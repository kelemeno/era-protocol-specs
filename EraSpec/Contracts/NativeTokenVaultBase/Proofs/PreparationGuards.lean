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
  -- the reverse-map check reads `r.assetId` off the tracked token, whose id is the configured one
  have hnot : ¬ (InScope s r ∧ EntryAllowed s r) := fun ⟨hs, he⟩ =>
    h (he.2.2.2.2.1.symm.trans (by rw [hs.2.2.2.2]; exact hw.2.2.2.2))
  simp [Properties.wrong_asset_rejected, prepare, hnot]

end Contracts.NativeTokenVaultBase
