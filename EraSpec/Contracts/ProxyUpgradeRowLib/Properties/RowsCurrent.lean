import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent

/-!
# Properties: the proxy rows at `e561b9cc2`

Statements about `EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent`. Proofs are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrent`. The same names as in
`Properties/Rows.lean` (the `612a71ccc` snapshot) are used where a result is re-established;
the folder README lists which ones changed status.

## What the in-call verification pass changed

At `612a71ccc` the post-state check (`requireRowsApplied`) ran in a later transaction and
held only for rows naming distinct proxies under an owned admin. At `e561b9cc2` it is the
last pass of `applyRows` itself, so a successful `applyRows` establishes it with no premise
(`ApplyRowsPostcondition`). Consequences:

* idempotence needs no distinct-proxies premise any more (`ApplyRowsIdempotent`);
* a pair of rows that carries a proxy past an earlier row's target now reverts instead of
  succeeding with the check failing (`DuplicateRowsNowRevert`, and in general
  `TwoTargetsForOneProxyRevert`);
* duplicate rows can still make the order decide whether the call reverts
  (`DuplicateRowsBreakOrder`), so `validateRows`' duplicate check is still load-bearing. It
  is not enough on its own: on valid rows, a reinitializer that reads another row's proxy
  can do the same (`ReinitReadBreaksOrder`, `Properties/RowsOrder.lean`).

## What the reinitializer can do

The model now gives `upgradeAndCall`'s `initializeUpgrade()` an effect. The verification
pass catches a reinitializer that moves a proxy of the row set
(`ReinitMovingOwnProxyIsCaught`), as the source says. It does not look at any other proxy
(`ReinitLeakIsNotCaught`), so the frame results take `ReinitFrames`: each reinitializer moves
at most its own proxy. Without it the final state can also depend on the order of the rows
(`ReinitMakesOrderMatter`).

## What the self-edge check adds

With `expectedOldImpl ≠ implNew` (`validateRows`, `:78-80`), a row's source state does not
already pass the verification, so a successful application from the source really moves
the proxy (`ValidSourceIsNotApplied`). A self-edge row passed the `612a71ccc` checks and
"applies" without moving anything (`SelfEdgeAppliesWithoutMoving`).
-/

namespace Contracts.ProxyUpgradeCurrent

/-! ## One row -/

/-- **A ROW MOVES ONLY ITS OWN PROXY, AND ONLY ALONG ITS OWN EDGE.** For a row without a
reinitializer effect, one iteration of the loop leaves every other proxy alone and leaves
the row's proxy where it was or moves it from `expectedOldImpl` to `implNew`. -/
def Properties.OnlyTheNamedEdge : Prop :=
  ∀ (C : Config) (I J : Impl) (r : Row), RowInert C r → ApplyRow C I r J →
    (∀ q, q ≠ r.proxy → J q = I q) ∧
    (J r.proxy = I r.proxy ∨ (I r.proxy = r.expectedOldImpl ∧ J r.proxy = r.implNew))

/-- **A STALE ROW DOES NOT APPLY.** If the proxy is at neither the row's source nor its
target, the loop iteration reverts. No premise: there is no foreign-admin skip any more. -/
def Properties.StaleObjectCannotDowngrade : Prop :=
  ∀ (C : Config) (I : Impl) (r : Row), I r.proxy ≠ r.expectedOldImpl → I r.proxy ≠ r.implNew →
    ¬ ∃ J, ApplyRow C I r J

/-- **THE SAME, FOR A WHOLE CALL.** `applyRows` whose first row is stale reverts. -/
def Properties.StaleObjectReverts : Prop :=
  ∀ (C : Config) (I : Impl) (r : Row) (rs : List Row),
    I r.proxy ≠ r.expectedOldImpl → I r.proxy ≠ r.implNew →
    ¬ ∃ J, ApplyRows C I (r :: rs) J

/-! ## A call -/

/-- **`applyRows` IS DETERMINISTIC.** -/
def Properties.ApplyRowsDeterministic : Prop :=
  ∀ (C : Config) (I J K : Impl) (rows : List Row),
    ApplyRows C I rows J → ApplyRows C I rows K → J = K

/-- **A SUCCESSFUL CALL ESTABLISHES THE VERIFICATION.** Every row's proxy ends at its
`implNew`. No premise: this is the second loop of `applyRows`. At `612a71ccc` the same
conclusion needed distinct proxies and no foreign-admin row. -/
def Properties.ApplyRowsPostcondition : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row), ApplyRows C I rows J → RowsApplied J rows

/-- **APPLYING TWICE IS APPLYING ONCE.** A second `applyRows` over the same rows, from the
state the first one left, succeeds and changes nothing. No distinct-proxies premise. -/
def Properties.ApplyRowsIdempotent : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row), ApplyRows C I rows J → ApplyRows C J rows J

/-- **A LATER READER SEES THE ROWS APPLIED IF NOTHING MOVED THEM.** The library no longer
has a separate `requireRowsApplied`. A reader in a later transaction sees every row applied
provided the rows' proxies have not moved since `applyRows` returned. The frame hypothesis
is not established by the library: the `ProxyAdmin`'s owner can move a proxy in between. -/
def Properties.AppliedGatePasses : Prop :=
  ∀ (C : Config) (I J K : Impl) (rows : List Row), ApplyRows C I rows J →
    (∀ r ∈ rows, K r.proxy = J r.proxy) → RowsApplied K rows

/-- **TWO TARGETS FOR ONE PROXY ALWAYS REVERT.** If two rows name the same proxy with
different `implNew`, no `applyRows` over them succeeds: the verification pass cannot meet
both. -/
def Properties.TwoTargetsForOneProxyRevert : Prop :=
  ∀ (C : Config) (I : Impl) (rows : List Row) (a b : Row), a ∈ rows → b ∈ rows →
    a.proxy = b.proxy → a.implNew ≠ b.implNew → ¬ ∃ J, ApplyRows C I rows J

/-- **AN APPLIER THAT DOES NOT OWN ITS ADMIN MOVES NOTHING.** Every row must then already be
applied: the upgrade reverts in `ProxyAdmin`'s `onlyOwner`. -/
def Properties.UnownedAdminMovesNothing : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row), C.adminOwner ≠ C.self →
    ApplyRows C I rows J → J = I

/-! ## Frames, under `ReinitFrames` -/

/-- **PROXIES NO ROW NAMES KEEP THEIR IMPLEMENTATION**, provided each reinitializer moves at
most its own proxy. -/
def Properties.UnmovedProxiesFrame : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row), ReinitFrames C → ApplyRows C I rows J →
    ∀ p, (∀ r ∈ rows, r.proxy ≠ p) → J p = I p

/-- **ACROSS A CALL, A PROXY MOVES ONLY ALONG A ROW'S EDGE.** For rows naming distinct
proxies and reinitializers that move at most their own proxy: after a successful
`applyRows`, every proxy is either where it was, or was at some row's `expectedOldImpl` and
is now at that row's `implNew`. This is replay safety for the whole call, including the
reinitializers. -/
def Properties.OnlyNamedEdgesAcrossCall : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row), rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    ReinitFrames C → ApplyRows C I rows J →
    ∀ p, J p = I p ∨ ∃ r ∈ rows, r.proxy = p ∧ I p = r.expectedOldImpl ∧ J p = r.implNew

/-- **IF TWO ORDERS OF THE ROWS BOTH SUCCEED, THEY END IN THE SAME STATE**, when
reinitializers move at most their own proxy. No distinct-proxies premise. Both successful
calls are premises: this does not say that one order succeeds when the other does, and on
valid rows it need not (`ReinitReadBreaksOrder`, `Properties/RowsOrder.lean`).
`DistinctRowsApplyInAnyOrder` there gives that under a stronger premise on the
reinitializers. -/
def Properties.OrderIndependent : Prop :=
  ∀ (C : Config) (I J K : Impl) (rows rows' : List Row), rows.Perm rows' → ReinitFrames C →
    ApplyRows C I rows J → ApplyRows C I rows' K → J = K

/-- **ON THE ROWS' OWN PROXIES THE ORDER NEVER MATTERS.** With no premise on the
reinitializers, two successful calls over permutations of the same rows agree on every
proxy a row names. -/
def Properties.OrderIndependentOnRowProxies : Prop :=
  ∀ (C : Config) (I J K : Impl) (rows rows' : List Row), rows.Perm rows' →
    ApplyRows C I rows J → ApplyRows C I rows' K → ∀ r ∈ rows, J r.proxy = K r.proxy

/-! ## The self-edge check -/

/-- **A VALID ROW'S SOURCE STATE IS NOT ALREADY APPLIED.** Under `validateRows` at
`e561b9cc2`, a state with a row's proxy at its `expectedOldImpl` fails the verification,
and any successful `applyRows` from it moves that proxy. -/
def Properties.ValidSourceIsNotApplied : Prop :=
  ∀ (C : Config) (I J : Impl) (rows : List Row) (r : Row), ValidRows rows → r ∈ rows →
    I r.proxy = r.expectedOldImpl → ¬ RowsApplied I rows ∧ (ApplyRows C I rows J → J r.proxy ≠ I r.proxy)

/-- **A SELF-EDGE PASSED THE OLD CHECKS AND APPLIES WITHOUT MOVING.** The row `5: 10 → 10`
passes `validateRows` as it was at `612a71ccc` and fails it at `e561b9cc2`. From the state
with proxy `5` at its source `10`, the verification already holds, and `applyRows` succeeds
and leaves the state unchanged. -/
def Properties.SelfEdgeAppliesWithoutMoving : Prop :=
  ValidRowsWithoutSelfEdgeCheck [rowSelf] ∧ ¬ ValidRows [rowSelf] ∧
    wImpl rowSelf.proxy = rowSelf.expectedOldImpl ∧ RowsApplied wImpl [rowSelf] ∧
    ApplyRows wConfig wImpl [rowSelf] wImpl

/-! ## Countermodels -/

/-- **DUPLICATE ROWS NOW REVERT.** The `612a71ccc` countermodel's pair, `5: 10 → 11` then
`5: 11 → 12`, each a valid row on its own: the first loop succeeds and leaves proxy `5` at
`12`, which fails the first row's verification, so `applyRows` reverts. At `612a71ccc` the
same call succeeded and left the later gate failing. -/
def Properties.DuplicateRowsNowRevert : Prop :=
  ValidRows [rowA] ∧ ValidRows [rowA2] ∧
    (∃ J, ApplyLoop wConfig wImpl [rowA, rowA2] J ∧ ¬ RowsApplied J [rowA, rowA2]) ∧
    ¬ ∃ J, ApplyRows wConfig wImpl [rowA, rowA2] J

/-- **DUPLICATE ROWS STILL MAKE THE ORDER MATTER.** `5: 10 → 11` and `5: 12 → 11`, each a
valid row on its own, name the same proxy and target. In one order `applyRows` succeeds;
in the other the second row sees `10`, neither its source nor its target, and reverts. -/
def Properties.DuplicateRowsBreakOrder : Prop :=
  ValidRows [rowA] ∧ ValidRows [rowA3] ∧ ¬ [rowA, rowA3].Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    (∃ J, ApplyRows wConfig wImpl [rowA, rowA3] J) ∧
    ¬ ∃ J, ApplyRows wConfig wImpl [rowA3, rowA] J

/-- **THE VERIFICATION CATCHES A REINITIALIZER THAT MOVES A ROW'S PROXY.** `rowB`'s
reinitializer moves its own proxy `6` back to `10` (so `ReinitFrames` holds). The first loop
succeeds; `applyRows` reverts. -/
def Properties.ReinitMovingOwnProxyIsCaught : Prop :=
  ReinitFrames wSelfMoving ∧ ValidRows [rowA, rowB] ∧
    (∃ J, ApplyLoop wSelfMoving wImpl [rowA, rowB] J) ∧
    ¬ ∃ J, ApplyRows wSelfMoving wImpl [rowA, rowB] J

/-- **THE VERIFICATION DOES NOT SEE OTHER PROXIES.** `rowB`'s reinitializer also moves proxy
`7`, which no row names (so `ReinitFrames` fails). `applyRows` succeeds and proxy `7` has
moved. So `UnmovedProxiesFrame` needs `ReinitFrames`. -/
def Properties.ReinitLeakIsNotCaught : Prop :=
  ¬ ReinitFrames wLeaky ∧ ValidRows [rowA, rowB] ∧
    ∃ J, ApplyRows wLeaky wImpl [rowA, rowB] J ∧ (∀ r ∈ [rowA, rowB], r.proxy ≠ 7) ∧ J 7 ≠ wImpl 7

/-- **A REINITIALIZER CAN MAKE THE ORDER MATTER.** `rowB`'s reinitializer writes proxy `7`
according to where proxy `5` is when it runs (so `ReinitFrames` fails). The rows are valid
and both orders succeed, and they end in different states. So `OrderIndependent` needs
`ReinitFrames`, and distinct proxies do not replace it. -/
def Properties.ReinitMakesOrderMatter : Prop :=
  ¬ ReinitFrames wOrderSensitive ∧ ValidRows [rowA, rowB] ∧
    ∃ J K, ApplyRows wOrderSensitive wImpl [rowA, rowB] J ∧
      ApplyRows wOrderSensitive wImpl [rowB, rowA] K ∧ J ≠ K

/-! ## The inventory and the transition -/

/-- **`toRows` KEEPS EXACTLY THE SLOTS MARKED FOR UPGRADE**, in order. -/
def Properties.ToRowsKeepsActiveSlots : Prop :=
  ∀ (slots : List Row) (r : Row),
    (r ∈ toRows slots ↔ r ∈ slots ∧ r.implNew ≠ 0) ∧ (toRows slots).Sublist slots

/-- **AN INERT SLOT'S PROXY IS NEVER UPGRADED**, if no other slot names it and the
reinitializers move at most their own proxy. -/
def Properties.InertSlotNeverUpgraded : Prop :=
  ∀ (C : Config) (I J : Impl) (slots : List Row) (s : Row), ReinitFrames C → s ∈ slots →
    s.implNew = 0 → (∀ t ∈ slots, t.proxy = s.proxy → t.implNew = 0) →
    ApplyRows C I (toRows slots) J → J s.proxy = I s.proxy

/-- **A TRANSITION OF THE OTHER DOMAIN IS REFUSED.** -/
def Properties.WrongDomainTransitionReverts : Prop :=
  ∀ (C : Config) (d : Domain) (T : Transition) (I : Impl), T.domain ≠ d →
    ¬ ∃ J, ApplyTransition C d T I J

/-! ## Witness -/

/-- **THE PREMISES ARE MET BY A REAL CALL.** Rows `5: 10 → 11` and `6: 10 → 12` (the latter
with an inert reinitializer) are valid, satisfy `ReinitFrames` and `RowInert`, and both
start at their source. `applyRows` succeeds in both orders and reaches one state that moves
both proxies and leaves proxy `7` alone; the same rows also apply as a CTM-domain
transition and are refused as a core-domain one. An applier that does not own its admin
succeeds on a row that is already applied. Row `5: 11 → 12` is stale in the starting state.
The inventory `[rowA, slotInert]` drops the inert slot for proxy `7`, applies, and leaves
proxy `7` alone. -/
def Properties.CurrentRowsWitness : Prop :=
  ValidRows [rowA, rowB] ∧ ReinitFrames wConfig ∧ (∀ r ∈ [rowA, rowB], RowInert wConfig r) ∧
    wImpl rowA.proxy = rowA.expectedOldImpl ∧ wImpl rowB.proxy = rowB.expectedOldImpl ∧
    (∃ J, ApplyRows wConfig wImpl [rowA, rowB] J ∧ ApplyRows wConfig wImpl [rowB, rowA] J ∧
      J 5 = 11 ∧ J 6 = 12 ∧ J 7 = wImpl 7 ∧
      ApplyTransition wConfig .ctm ⟨3, .ctm, [rowA, rowB]⟩ wImpl J) ∧
    wUnowned.adminOwner ≠ wUnowned.self ∧
    ApplyRows wUnowned (upd wImpl 5 11) [rowA] (upd wImpl 5 11) ∧
    wImpl rowA2.proxy ≠ rowA2.expectedOldImpl ∧ wImpl rowA2.proxy ≠ rowA2.implNew ∧
    (¬ ∃ J, ApplyTransition wConfig .core ⟨3, .ctm, [rowA, rowB]⟩ wImpl J) ∧
    toRows [rowA, slotInert] = [rowA] ∧
    ∃ J, ApplyRows wConfig wImpl (toRows [rowA, slotInert]) J ∧ J slotInert.proxy = wImpl slotInert.proxy

end Contracts.ProxyUpgradeCurrent
