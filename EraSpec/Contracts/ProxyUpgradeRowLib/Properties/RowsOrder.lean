import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsOrder

/-!
# Properties: which row orders succeed (`e561b9cc2`)

Statements about `EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsOrder`, which is the
`RowsCurrent` model plus `ReinitReadsOwnProxy` and witness data. Proofs are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsOrder`.

## What `OrderIndependent` does and does not say

`OrderIndependent` (`Properties/RowsCurrent.lean`) assumes that `applyRows` succeeded over
both permutations and concludes that the two final states are equal. It does not say that if
one order succeeds, so does the other. That stronger claim, order-independent
*executability*, is what this file is about:

* `validateRows`' duplicate check is **necessary** for it: duplicate rows can make one order
  revert (`DuplicateRowsBreakOrder`, `Properties/RowsCurrent.lean`).
* It is **not sufficient**, even with `ReinitFrames`: on valid rows, a reinitializer that
  reads another row's proxy can make one order revert (`ReinitReadBreaksOrder`).
* Distinct proxies, `ReinitFrames` and `ReinitReadsOwnProxy` together **are sufficient**: a
  successful call succeeds in every order, and reaches the same state
  (`DistinctRowsApplyInAnyOrder`). Each premise is needed: `DuplicateRowsBreakOrder` under the
  witness configuration, which satisfies the other two (`RowsOrderWitness`), then
  `ReinitLeakBreaksOrder` and `ReinitReadBreaksOrder`.
-/

namespace Contracts.ProxyUpgradeCurrent

/-! ## Countermodels -/

/-- **ON VALID ROWS, THE ORDER CAN STILL DECIDE WHETHER THE CALL REVERTS.** Rows `5: 10 → 11`
(`rowA`) and `6: 10 → 12` (`rowB`, with a reinitializer) pass `validateRows` in either order.
`rowB`'s reinitializer writes only its own proxy, so `ReinitFrames` holds, but it reads proxy
`5`: if proxy `5` is already at `11` it leaves proxy `6` at `12`, and otherwise it moves proxy
`6` back to `10`. From the state with every proxy at `10`, `applyRows` over `rowA, rowB`
succeeds. Over `rowB, rowA` the verification finds proxy `6` at `10`, and the call reverts.
So `OrderIndependent`, which assumes both orders succeed, does not extend to "if one order
succeeds, so does the other" under `ValidRows` and `ReinitFrames`. -/
def Properties.ReinitReadBreaksOrder : Prop :=
  ReinitFrames wReadsOtherProxy ∧ ¬ ReinitReadsOwnProxy wReadsOtherProxy ∧
    ValidRows [rowA, rowB] ∧ ValidRows [rowB, rowA] ∧ [rowA, rowB].Perm [rowB, rowA] ∧
    (∃ J, ApplyRows wReadsOtherProxy wImpl [rowA, rowB] J) ∧
    ¬ ∃ K, ApplyRows wReadsOtherProxy wImpl [rowB, rowA] K

/-- **WITHOUT `ReinitFrames` THE ORDER CAN DECIDE IT TOO**, even if each reinitializer reads
only its own proxy. Rows `6: 10 → 12` (`rowB`, with a reinitializer) and `5: 11 → 12`
(`rowA2`) pass `validateRows` in either order. `rowB`'s reinitializer moves proxy `5` to
`11` (`wLeakNamed`), so `ReinitFrames` fails; where it leaves its own proxy `6` depends only
on proxy `6`. From the state with every proxy at `10`, `applyRows` over `rowB, rowA2`
succeeds (`ReinitLeakMovesNamedProxyOffEdge`). Over `rowA2, rowB` it reverts: `rowA2` finds
proxy `5` at `10`, neither its source nor its target. -/
def Properties.ReinitLeakBreaksOrder : Prop :=
  ¬ ReinitFrames wLeakNamed ∧ ReinitReadsOwnProxy wLeakNamed ∧
    ValidRows [rowB, rowA2] ∧ ValidRows [rowA2, rowB] ∧ [rowB, rowA2].Perm [rowA2, rowB] ∧
    (∃ J, ApplyRows wLeakNamed wImpl [rowB, rowA2] J) ∧
    ¬ ∃ K, ApplyRows wLeakNamed wImpl [rowA2, rowB] K

/-! ## Order-independent executability -/

/-- **ON DISTINCT ROWS, A SUCCESSFUL CALL SUCCEEDS IN EVERY ORDER**, if each reinitializer
moves at most its own proxy (`ReinitFrames`) and reads only its own proxy
(`ReinitReadsOwnProxy`). `applyRows` over any permutation of the rows then succeeds from the
same state and reaches the same state. Rows that pass `validateRows` name distinct proxies
(`ValidRows.distinctProxies`). Each premise is needed: `DuplicateRowsBreakOrder` (whose
configuration satisfies the other two, `RowsOrderWitness`), `ReinitLeakBreaksOrder` and
`ReinitReadBreaksOrder`. -/
def Properties.DistinctRowsApplyInAnyOrder : Prop :=
  ∀ (C : Config) (I J : Impl) (rows rows' : List Row), rows.Perm rows' →
    rows.Pairwise (fun a b => a.proxy ≠ b.proxy) → ReinitFrames C → ReinitReadsOwnProxy C →
    ApplyRows C I rows J → ApplyRows C I rows' J

/-! ## Witness -/

/-- **THE PREMISES OF `DistinctRowsApplyInAnyOrder` ARE MET BY A REAL CALL.** The witness
configuration's reinitializers change nothing, so they move and read at most their own
proxy. Rows `5: 10 → 11` and `6: 10 → 12` name distinct proxies; the second has a
reinitializer, which runs. `applyRows` over them succeeds from the state with every proxy at
`10`, and moves a proxy. The same configuration is the one of `DuplicateRowsBreakOrder`, so
that countermodel meets the two reinitializer premises. -/
def Properties.RowsOrderWitness : Prop :=
  ReinitFrames wConfig ∧ ReinitReadsOwnProxy wConfig ∧
    [rowA, rowB].Pairwise (fun a b => a.proxy ≠ b.proxy) ∧ [rowA, rowB].Perm [rowB, rowA] ∧
    rowB.callInitializeUpgrade = true ∧
    ∃ J, ApplyRows wConfig wImpl [rowA, rowB] J ∧ J ≠ wImpl

end Contracts.ProxyUpgradeCurrent
