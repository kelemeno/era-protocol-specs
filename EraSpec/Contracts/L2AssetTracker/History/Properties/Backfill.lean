import EraSpec.Contracts.L2AssetTracker.Specs.Accounting

/-!
# History: the tracker's base-token backfill at the pin `c67894b9`

**Record of an older commit, not a claim about `b17415d20`.**  At the pin `c67894b9` the tracker had
`backFillZKSyncOSBaseTokenV31MigrationData` (pin `L2AssetTracker.sol:120-140`),
`registerBaseTokenDuringUpgrade` (`:187-194`) and a backfill flag set by `initL2` (`:146-154`).  At
`b17415d20` all three are gone (the flag's slot is `__DEPRECATED_needBaseTokenTotalSupplyBackfill`,
`L2AssetTracker.sol:65`).  `Specs/Accounting.lean` keeps them as `Op.backfill`,
`Op.registerBaseDuringUpgrade` and `Op.initL2 need`; these statements are about those operations.

Proofs are in `EraSpec.Contracts.L2AssetTracker.History.Proofs.Backfill`.
-/

namespace Contracts.L2AssetTracker.History

/-- **THE BACKFILL WRITES ONLY THE BASE TOKEN'S SNAPSHOT, FROM ZERO.**  A successful backfill
found the base token registered with a saved zero snapshot and the flag set; it writes the
snapshot's amount, clears the flag, and changes nothing else. -/
def Properties.BackfillOnlyBaseFromZero : Prop :=
  ∀ (cfg : Config) (sys sys' : Sys) (amount : UInt256),
    exec cfg sys (.backfill amount) = some sys' →
      sys.st.isAssetRegistered sys.st.baseTokenAssetId = true ∧
      sys.st.totalPreV31TotalSupply sys.st.baseTokenAssetId = ⟨true, 0⟩ ∧
      sys.st.needBaseTokenTotalSupplyBackfill = true ∧
      sys'.st = { sys.st with
        totalPreV31TotalSupply := Function.update sys.st.totalPreV31TotalSupply
          sys.st.baseTokenAssetId ⟨true, amount⟩
        needBaseTokenTotalSupplyBackfill := false } ∧
      sys'.sl = sys.sl ∧ sys'.audit = sys.audit

/-- **AT MOST ONE BACKFILL.**  From a state satisfying `Inv`, after a successful backfill, no
backfill succeeds in any later state of the run. -/
def Properties.BackfillAtMostOnce : Prop :=
  ∀ (cfg : Config) (sys₀ sys₁ sys₂ : Sys) (amount amount' : UInt256),
    Inv cfg sys₀ → exec cfg sys₀ (.backfill amount) = some sys₁ → Reach cfg sys₁ sys₂ →
      exec cfg sys₂ (.backfill amount') = none

/-- **A RUN WITH A BACKFILL.**  From fresh storage satisfying `Inv`: `initL2` with the flag set,
the upgrade registration of the base token, reaching a state that satisfies `Inv`, then a
successful backfill of a nonzero amount. -/
def Properties.BackfillSatisfiable : Prop :=
  ∃ (cfg : Config) (sl : ChainId) (sys₁ sys₂ sys₃ : Sys) (amount : UInt256),
    Inv cfg (Sys.fresh sl) ∧ amount ≠ 0 ∧
    exec cfg (Sys.fresh sl) (.initL2 true) = some sys₁ ∧
    exec cfg sys₁ .registerBaseDuringUpgrade = some sys₂ ∧ Inv cfg sys₂ ∧
    exec cfg sys₂ (.backfill amount) = some sys₃

end Contracts.L2AssetTracker.History
