import EraSpec.Contracts.NativeTokenVaultBase.Properties.PreparationGuards

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

theorem wrong_router_rejected {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (h : r.caller ≠ s.config.router) :
    Properties.wrong_router_rejected (hooks := hooks) (s := s) (r := r) h := by
  simp [Properties.wrong_router_rejected, prepare, EntryAllowed, h]

theorem paused_preparation_rejected {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (h : s.paused = true) :
    Properties.paused_preparation_rejected (hooks := hooks) (s := s) (r := r) h := by
  simp [Properties.paused_preparation_rejected, prepare, EntryAllowed, h]

theorem zero_amount_rejected {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (h : r.data.amount = 0) :
    Properties.zero_amount_rejected (hooks := hooks) (s := s) (r := r) h := by
  simp [Properties.zero_amount_rejected, prepare, EntryAllowed, h]

theorem wrong_asset_rejected {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (hw : WellFormed s) (h : r.assetId ≠ s.config.assetId) :
    Properties.wrong_asset_rejected (hooks := hooks) (s := s) (r := r) hw h := by
  simp only [Properties.wrong_asset_rejected, prepare]
  have hnot : ¬ (InScope s r ∧ EntryAllowed s r) := by
    rintro ⟨hs, he⟩
    have hselected : selectedToken s r = s.config.tokenAddress := hs.2.2.2.2
    have hreverse : s.registry.assetForToken (selectedToken s r) = r.assetId :=
      he.2.2.2.2.1
    have hasset : s.config.assetId = r.assetId := by
      calc
        s.config.assetId = s.registry.assetForToken s.config.tokenAddress :=
          hw.2.2.2.2.symm
        _ = s.registry.assetForToken (selectedToken s r) :=
          congrArg s.registry.assetForToken hselected.symm
        _ = r.assetId := hreverse
    exact h hasset.symm
  simp [hnot]

end Contracts.NativeTokenVaultBase
