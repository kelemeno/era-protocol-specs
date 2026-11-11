import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrentStrong

/-!
# Properties: when the `e561b9cc2` rows apply, and in which orders

Statements about `EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrentStrong`, which is the
`RowsCurrent` model plus `LocalSwap`, `RowApplies` and witness data. Proofs are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrentStrong`.

## What validation buys for executability

`OrderIndependent` (`Properties/RowsCurrent.lean`) compares two successful calls. Whether a
permutation of a successful call succeeds is a separate question.

* **Validation is not sufficient under `ReinitFrames`.** `ValidRowsOrderDecidesExecutability`
  gives valid rows and a reinitializer that writes only its own proxy (so `ReinitFrames`
  holds). The reinitializer reads another proxy, so one order applies and the other reverts
  at the verification pass. Its swap is not local.
* **It is sufficient for local swaps.** `ApplyRowsEnabledIff`: for rows naming distinct
  proxies whose swaps are local (`LocalSwap`), `applyRows` succeeds iff `requireRowCode`
  passes and every row applies on its own from the state the call starts from (`RowApplies`).
  The right-hand side does not mention the order, so a permutation of a successful call
  succeeds, and reaches the same state (`OrderIndependentExecutability`). The confirmed
  special case is rows without an effective reinitializer
  (`OrderIndependentExecutabilityInert`).
* **Distinct proxies are still needed.** `DuplicateRowsBreakOrder` (`Properties/RowsCurrent.lean`)
  has rows without reinitializers on one proxy, where one order applies and the other reverts.

`LocalSwap` is implied by `RowInert` (`LocalSwapOfInert`), and by a reinitializer that moves at
most its own proxy and whose result there does not depend on the other proxies
(`LocalSwapOfOwnProxyReinit`). `RowsCurrentStrongWitness` shows a local but not inert
reinitializer, valid rows applying in both orders under it, and a local swap that fails
`RowApplies`.
-/

namespace Contracts.ProxyUpgradeCurrent

/-! ## Local swaps -/

/-- **AN INERT ROW'S SWAP IS LOCAL**, with `implNew` as its fixed implementation. -/
def Properties.LocalSwapOfInert : Prop :=
  ∀ (C : Config) (r : Row), RowInert C r → LocalSwap C r

/-- **A REINITIALIZER THAT KEEPS TO ITS OWN PROXY GIVES A LOCAL SWAP.** If the row's
reinitializer moves at most the row's proxy, and what it leaves there depends on the mapping
only through the row's proxy, then the row's swap is local. This is `ReinitFrames` for this
row plus a bound on what the reinitializer reads. -/
def Properties.LocalSwapOfOwnProxyReinit : Prop :=
  ∀ (C : Config) (r : Row), (∀ (I : Impl) (q : Address), q ≠ r.proxy → C.reinit r I q = I q) →
    (∀ I I' : Impl, I r.proxy = I' r.proxy → C.reinit r I r.proxy = C.reinit r I' r.proxy) →
    LocalSwap C r

/-! ## When a call succeeds -/

/-- **ON DISTINCT PROXIES WITH LOCAL SWAPS, `applyRows` SUCCEEDS EXACTLY WHEN EACH ROW WOULD ON
ITS OWN.** For rows naming distinct proxies whose swaps are local, a call `applyRows` from `I`
succeeds iff `requireRowCode` passes and every row applies on its own from `I`: its proxy is
at `implNew`, or the applier owns `_admin`, the proxy is at `expectedOldImpl`, and its swap
leaves it at `implNew`. -/
def Properties.ApplyRowsEnabledIff : Prop :=
  ∀ (C : Config) (I : Impl) (rows : List Row), rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    (∀ r ∈ rows, LocalSwap C r) →
    ((∃ J, ApplyRows C I rows J) ↔ RowCode C rows ∧ ∀ r ∈ rows, RowApplies C I r)

/-! ## Order independence, executability included -/

/-- **A PERMUTATION OF A SUCCESSFUL CALL IS A SUCCESSFUL CALL TO THE SAME STATE**, for rows
naming distinct proxies whose swaps are local. If `applyRows` succeeds in one order, it
succeeds in every order and reaches the same state. `ValidRowsOrderDecidesExecutability`
shows that `ReinitFrames` cannot replace `LocalSwap`. `DuplicateRowsBreakOrder` shows that the
distinct-proxies premise is needed. -/
def Properties.OrderIndependentExecutability : Prop :=
  ∀ (C : Config) (I J : Impl) (rows rows' : List Row), rows.Perm rows' →
    rows.Pairwise (fun a b => a.proxy ≠ b.proxy) → (∀ r ∈ rows, LocalSwap C r) →
    ApplyRows C I rows J → ApplyRows C I rows' J

/-- **THE SAME, FOR INERT ROWS.** For rows naming distinct proxies, each without a reinitializer
or with an inert one, a permutation of a successful call is a successful call to the same
state. -/
def Properties.OrderIndependentExecutabilityInert : Prop :=
  ∀ (C : Config) (I J : Impl) (rows rows' : List Row), rows.Perm rows' →
    rows.Pairwise (fun a b => a.proxy ≠ b.proxy) → (∀ r ∈ rows, RowInert C r) →
    ApplyRows C I rows J → ApplyRows C I rows' J

/-! ## Countermodel -/

/-- **UNDER `ReinitFrames`, THE ORDER OF VALID ROWS CAN DECIDE WHETHER THE CALL REVERTS.**
`rowB`'s reinitializer writes only its own proxy `6`, so `ReinitFrames` holds. It writes `12`
if proxy `5` is at `11` and `10` otherwise, so its swap is not local. The rows `5: 10 → 11`
and `6: 10 → 12` are valid. In the order `[rowA, rowB]` the call succeeds. In the order
`[rowB, rowA]` the first loop succeeds, but proxy `6` ends at `10` and the verification pass
reverts. So the premises of `OrderIndependent` hold, one order succeeds, and its permutation
does not: validation and `ReinitFrames` together do not make executability
order-independent. -/
def Properties.ValidRowsOrderDecidesExecutability : Prop :=
  ReinitFrames wReadsOther ∧ ValidRows [rowA, rowB] ∧ ¬ LocalSwap wReadsOther rowB ∧
    (∃ J, ApplyRows wReadsOther wImpl [rowA, rowB] J) ∧
    (∃ J, ApplyLoop wReadsOther wImpl [rowB, rowA] J) ∧
    ¬ ∃ J, ApplyRows wReadsOther wImpl [rowB, rowA] J

/-! ## Witness -/

/-- **THE PREMISES ARE MET, BEYOND INERT ROWS.** Under `wLocalReinit`, `rowB`'s reinitializer
sets proxy `6` to `12` from any mapping. That reinitializer is not inert. It satisfies both
premises of `LocalSwapOfOwnProxyReinit`, and both rows' swaps are local. The rows `5: 10 → 11`
and `6: 10 → 12` are valid and pass `requireRowCode`, and each applies on its own from
`wImpl`. The call succeeds in both orders and reaches one state with proxy `5` at `11` and `6`
at `12`. The same rows under `wConfig` are inert and apply (the premises of
`OrderIndependentExecutabilityInert`). Under `wSelfMoving` (`rowB`'s reinitializer moves `6` back
to `10`) `rowB`'s swap is local but `rowB` does not apply on its own, so `ApplyRowsEnabledIff`
predicts the revert that `ReinitMovingOwnProxyIsCaught` shows. -/
def Properties.RowsCurrentStrongWitness : Prop :=
  ValidRows [rowA, rowB] ∧ ¬ RowInert wLocalReinit rowB ∧
    (∀ (I : Impl) (q : Address), q ≠ rowB.proxy → wLocalReinit.reinit rowB I q = I q) ∧
    (∀ I I' : Impl, I rowB.proxy = I' rowB.proxy →
      wLocalReinit.reinit rowB I rowB.proxy = wLocalReinit.reinit rowB I' rowB.proxy) ∧
    (∀ r ∈ [rowA, rowB], LocalSwap wLocalReinit r) ∧
    RowCode wLocalReinit [rowA, rowB] ∧ (∀ r ∈ [rowA, rowB], RowApplies wLocalReinit wImpl r) ∧
    (∃ J, ApplyRows wLocalReinit wImpl [rowA, rowB] J ∧
      ApplyRows wLocalReinit wImpl [rowB, rowA] J ∧ J 5 = 11 ∧ J 6 = 12) ∧
    (∀ r ∈ [rowA, rowB], RowInert wConfig r) ∧ (∃ J, ApplyRows wConfig wImpl [rowA, rowB] J) ∧
    LocalSwap wSelfMoving rowB ∧ ¬ RowApplies wSelfMoving wImpl rowB

end Contracts.ProxyUpgradeCurrent
