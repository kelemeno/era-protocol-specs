import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.Rows

/-!
# Properties: the registry upgrade's proxy rows

Statements about `EraSpec.Contracts.ProxyUpgradeRowLib.Specs.Rows`.  Proofs are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.Rows`.

## What the library claims, and what is actually true

`ProxyUpgradeRowLib` states its semantics in one sentence — source-checked edges,
skip when already there, revert otherwise — and three consequences are claimed for
it across the subsystem: idempotence, replay safety, and that `applyRows` in an
early stage satisfies the `requireRowsApplied` gate in a later one.  The first two
hold as stated.  The third holds **only under two side conditions**, and both are
supplied elsewhere in the system rather than by the loop:

* `validateRows` must have run.  Without the duplicate check, `applyRows` can
  succeed and leave the gate failing — `DuplicateRowsBreakPostcondition`.
* No row may name a foreign `ProxyAdmin`.  Such a row is skipped and logged while
  the gate still demands it — `ForeignRowLeavesGateOpen`.

Both are by design and both are documented in the source.  Stating them as
theorems fixes which of them the gate depends on, so that a later refactor that
drops the duplicate check has to break a proof rather than a comment.

## Where the side conditions come from

Every applier builds its rows the same way — `toRows` then `validateRows` in the
constructor (`CoreRegistry`, `EcosystemUpgradeOperation`,
`RegistryBootstrapMigration`) — so validity is established once, immutably, before
any row is applied.  The foreign-admin condition is not established anywhere: it is
a property of the manifest, which is exactly why the second countermodel is worth
having.

## The gap the composition cannot close

`applyRows` and `requireRowsApplied` run in *different transactions*
(`applyOperation` then `completeOperation`).  `AppliedGatePasses` therefore carries
an explicit frame hypothesis: nothing moved the rows' proxies in between.  That is
not a theorem about this library — anything holding the relevant `ProxyAdmin` can
move a proxy — so it is stated as a hypothesis rather than quietly assumed.
-/

namespace Contracts.ProxyUpgrade

/-! ## The edge semantics -/

/-- **A ROW MOVES ONLY ITS OWN PROXY, AND ONLY ALONG ITS OWN EDGE.**  Whatever
happens to one row, every other proxy is untouched, and the row's proxy ends at
either where it started or at `implNew` — having started at `expectedOldImpl` in
the second case.  This is the precise form of "source-checked edge". -/
def Properties.OnlyTheNamedEdge : Prop :=
  ∀ (C : Config) (I J : Impl) (r : Row), ApplyRow C I r J →
    (∀ q, q ≠ r.proxy → J q = I q) ∧
    (J r.proxy = I r.proxy ∨ (I r.proxy = r.expectedOldImpl ∧ J r.proxy = r.implNew))

/-- **A STALE OBJECT CANNOT DOWNGRADE A MOVED PROXY.**  If a later upgrade has
already carried the proxy past both this row's source and its target, the row does
not apply at all: no state relates to any other, so the call reverts.

This is the replay-safety claim, and it is why the row carries `expectedOldImpl`
rather than just a target. -/
def Properties.StaleObjectCannotDowngrade : Prop :=
  ∀ (C : Config) (I : Impl) (r : Row), ¬ LeftToAdministrator C r →
    I r.proxy ≠ r.expectedOldImpl → I r.proxy ≠ r.implNew →
    ¬ ∃ J, ApplyRow C I r J

/-- **THE SAME, FOR A WHOLE OBJECT.**  A replayed object whose first row is stale
cannot be applied at all. -/
def Properties.StaleObjectReverts : Prop :=
  ∀ (C : Config) (I : Impl) (r : Row) (rs : List Row), ¬ LeftToAdministrator C r →
    I r.proxy ≠ r.expectedOldImpl → I r.proxy ≠ r.implNew →
    ¬ ∃ J, ApplyRows C I (r :: rs) J

/-- **APPLYING IS DETERMINISTIC.**  A run that succeeds reaches exactly one state, so
"the state after the upgrade" is well defined even though the model is a relation.
The three loop outcomes really are mutually exclusive. -/
def Properties.ApplyRowsDeterministic : Prop :=
  ∀ (C : Config) (I J K : Impl) (rows : List Row),
    ApplyRows C I rows J → ApplyRows C I rows K → J = K

/-! ## Idempotence -/

/-- **APPLYING TWICE IS APPLYING ONCE.**  A second run over the same rows succeeds —
it cannot revert — and changes nothing.  Every owned row takes the `liveImpl ==
newImpl` skip, every foreign row takes the skip it took before.

This is what makes a re-run of a governance stage safe, and what lets a row already
applied by someone else pass rather than block.  It needs `validateRows` too: see
`DuplicateRowsBreakIdempotence`. -/
def Properties.ApplyRowsIdempotent : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row),
    rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    ApplyRows C I rows J → ApplyRows C J rows J

/-! ## The post-state gate -/

/-- **UNTOUCHED PROXIES KEEP THEIR IMPLEMENTATION.**  If every row naming a proxy is
left to a foreign administrator — in particular, if no row names it at all — the
run does not move it. -/
def Properties.UnmovedProxiesFrame : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row), ApplyRows C I rows J →
    ∀ p, (∀ r ∈ rows, r.proxy = p → LeftToAdministrator C r) → J p = I p

/-- **A SUCCESSFUL APPLY SATISFIES THE GATE.**  With `validateRows` having run and no
row left to a foreign administrator, `applyRows` establishes exactly what
`requireRowsApplied` checks.

Note which hypothesis does the work: `distinctProxies`.  Without it a later row can
carry a proxy past an earlier row's target, and the gate then fails on the earlier
row even though every row applied successfully. -/
def Properties.ApplyRowsPostcondition : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row),
    rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    (∀ r ∈ rows, ¬ LeftToAdministrator C r) →
    ApplyRows C I rows J → RowsApplied J rows

/-- **THE TWO-STAGE COMPOSITION.**  `applyOperation` applies the rows in one
transaction and `completeOperation` checks them in another, so the claim that the
gate passes needs the intervening state to have left these proxies alone.  With
that, stage 2 cannot revert.

The frame hypothesis is the honest part: nothing in this library prevents a
`ProxyAdmin` owner from moving a proxy between the two stages, and the source says
as much — "a LATER upgrade legitimately moves proxies past `implNew`, after which
this reverts by design". -/
def Properties.AppliedGatePasses : Prop :=
  ∀ (C : Config) (I J K : Impl) (rows : List Row), ValidRows rows →
    (∀ r ∈ rows, ¬ LeftToAdministrator C r) →
    ApplyRows C I rows J → (∀ r ∈ rows, K r.proxy = J r.proxy) →
    RowsApplied K rows

/-! ## Order independence -/

/-- **THE ORDER OF ROWS DOES NOT MATTER.**  Rows arrive in an order fixed by a
contract enum, and the enum's order is an artefact of how the domain was written
down rather than anything the protocol chose.  Under `validateRows`, permuting them
either reaches the same state or is not a successful run at all — so no upgrade's
meaning depends on that artefact.

Stated as: whenever both orders succeed, they agree.  `DuplicateRowsBreakOrder`
shows the "both succeed" is needed — with duplicates, one order can revert while
the other does not. -/
def Properties.OrderIndependent : Prop :=
  ∀ (C : Config) (I J K : Impl) (rows rows' : List Row), rows.Perm rows' →
    rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    ApplyRows C I rows J → ApplyRows C I rows' K → J = K

/-! ## What is load-bearing -/

/-- **DUPLICATE ROWS BREAK THE GATE.**  Two rows on proxy `5` — `10 → 11` then
`11 → 12` — both apply, so `applyRows` succeeds; but the proxy ends at `12`, and the
first row demands `11`, so `requireRowsApplied` reverts.  A successful upgrade
would then be unable to complete.

`RegistryDuplicateProxyRow` is exactly what excludes this, which is why
`ApplyRowsPostcondition` takes `distinctProxies` as a hypothesis rather than a
remark. -/
def Properties.DuplicateRowsBreakPostcondition : Prop :=
  (∀ r ∈ [rowAB, rowBC], ¬ LeftToAdministrator cmConfig r)
    ∧ ApplyRows cmConfig cmImpl [rowAB, rowBC] cmFinal
    ∧ ¬ RowsApplied cmFinal [rowAB, rowBC]

/-- **DUPLICATE ROWS MAKE THE ORDER MATTER.**  The same two rows in the other order
do not apply at all: `11 → 12` sees the proxy at `10`, which is neither its source
nor its target, so the source check reverts.

One order succeeds, the other reverts — with duplicates, the enum's arbitrary order
decides whether the upgrade is executable. -/
def Properties.DuplicateRowsBreakOrder : Prop :=
  ApplyRows cmConfig cmImpl [rowAB, rowBC] cmFinal
    ∧ ¬ ∃ J, ApplyRows cmConfig cmImpl [rowBC, rowAB] J

/-- **DUPLICATE ROWS BREAK IDEMPOTENCE.**  Re-running the same pair on the state they
produced reverts: the proxy is at `12`, and the first row will accept only `11`
(its target) or `10` (its source).  So with duplicates a governance stage is not
merely wrong to re-run, it cannot be re-run — and the failure is the loud kind. -/
def Properties.DuplicateRowsBreakIdempotence : Prop :=
  ApplyRows cmConfig cmImpl [rowAB, rowBC] cmFinal
    ∧ ¬ ∃ J, ApplyRows cmConfig cmFinal [rowAB, rowBC] J

/-- **A FOREIGN-ADMIN ROW LEAVES THE GATE OPEN.**  The row names an admin the
applier does not own, so `applyRows` logs it and moves on and the whole call
succeeds — while `requireRowsApplied` still demands the proxy be at `implNew`, and
it is not.

So a manifest carrying such a row cannot complete its own upgrade unless that
administrator acts in between.  This is deliberate ("the applied-state check still
requires it"), and it is a liveness obligation on a party outside the system, which
is worth having as a theorem rather than a comment. -/
def Properties.ForeignRowLeavesGateOpen : Prop :=
  ValidRows [fgnRow]
    ∧ LeftToAdministrator fgnConfig fgnRow
    ∧ ApplyRows fgnConfig cmImpl [fgnRow] cmImpl
    ∧ ¬ RowsApplied cmImpl [fgnRow]

/-! ## The inventory -/

/-- **`toRows` KEEPS EXACTLY THE SLOTS MARKED FOR UPGRADE.**  A slot is a row iff its
`implNew` is set, and the order is preserved.  So an inventory growing by a member
that no upgrade touches changes nothing that any applier sees. -/
def Properties.ToRowsKeepsActiveSlots : Prop :=
  ∀ (slots : List Row) (r : Row),
    (r ∈ toRows slots ↔ r ∈ slots ∧ r.implNew ≠ 0) ∧ (toRows slots).Sublist slots

/-- **AN INERT SLOT'S PROXY IS NEVER UPGRADED.**  A slot with zero `implNew` becomes
no row, so — provided no *other* slot names the same proxy — applying the inventory
leaves that proxy exactly where it was.  "Not upgraded" means not upgraded. -/
def Properties.InertSlotNeverUpgraded : Prop :=
  ∀ (C : Config) (I J : Impl) (slots : List Row) (s : Row), s ∈ slots → s.implNew = 0 →
    (∀ t ∈ slots, t.proxy = s.proxy → t.implNew = 0) →
    ApplyRows C I (toRows slots) J → J s.proxy = I s.proxy

end Contracts.ProxyUpgrade
