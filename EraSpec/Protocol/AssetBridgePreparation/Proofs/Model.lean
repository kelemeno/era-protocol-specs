import EraSpec.Protocol.AssetBridgePreparation.Properties.Model
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RepresentationPreparation

namespace AssetBridgePreparation

open Contracts
variable {Accounting : Type}

private theorem pending_append (pending : List Obligation) (next : Obligation) :
    pendingAmount (pending ++ [next]) = pendingAmount pending + next.data.amount.val := by
  simp only [pendingAmount, List.map_append, List.map_cons, List.map_nil,
    List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]

private theorem step_conservation {hooks : NativeTokenVaultBase.Hooks Accounting}
    {s t : Ledger Accounting} (hw : NativeTokenVaultBase.WellFormed s.vault)
    (h : Step hooks s t) :
    NativeTokenVaultBase.WellFormed t.vault ∧
    t.vault.token.totalSupply + pendingAmount t.pending =
      s.vault.token.totalSupply + pendingAmount s.pending ∧ t.vault.config = s.vault.config := by
  cases h with
  | prepare hp =>
    obtain ⟨hnext, hc, _hregistry, _hpaused, _hframe⟩ :=
      NativeTokenVaultBase.preparation_preserves_ledger hw hp
    have hsupply := (NativeTokenVaultBase.preparation_backed hw hp).2.2.1
    refine ⟨hnext, ?_, hc⟩
    dsimp only
    rw [pending_append]
    dsimp only [obligation] at *
    omega
  | spend ht =>
    obtain ⟨hnext, hsupply, hc⟩ := BridgedStandardERC20.transfer_preserves_ledger hw.1 ht
    refine ⟨⟨hnext, ?_, ?_, hw.2.2.2⟩, ?_, rfl⟩
    · exact (congrArg BridgedStandardERC20.Config.vault hc).trans hw.2.1
    · exact (congrArg BridgedStandardERC20.Config.assetId hc).trans hw.2.2.1
    · dsimp only
      rw [hsupply]

theorem reachable_conservation {hooks : NativeTokenVaultBase.Hooks Accounting}
    {s t : Ledger Accounting} (hw : NativeTokenVaultBase.WellFormed s.vault)
    (h : Reach hooks s t) : Properties.reachable_conservation hw h := by
  unfold Properties.reachable_conservation
  induction h with
  | refl => exact ⟨hw, rfl, rfl⟩
  | tail _hr hs ih =>
    obtain ⟨hnext, hsum, hc⟩ := step_conservation ih.1 hs
    exact ⟨hnext, hsum.trans ih.2.1, hc.trans ih.2.2⟩

theorem pending_backed_by_initial_supply {hooks : NativeTokenVaultBase.Hooks Accounting}
    {s t : Ledger Accounting} (hw : NativeTokenVaultBase.WellFormed s.vault)
    (he : s.pending = []) (h : Reach hooks s t) :
    Properties.pending_backed_by_initial_supply hw he h := by
  have hc := (reachable_conservation hw h).2.1
  rw [he] at hc
  simp only [pendingAmount, List.map_nil, List.sum_nil, Nat.add_zero] at hc
  unfold Properties.pending_backed_by_initial_supply
  unfold pendingAmount
  omega

theorem prepared_data_persists {hooks : NativeTokenVaultBase.Hooks Accounting}
    {s t : Ledger Accounting} (h : Reach hooks s t) : Properties.prepared_data_persists h := by
  unfold Properties.prepared_data_persists
  induction h with
  | refl => exact ⟨[], (List.append_nil _).symm⟩
  | tail _hr hs ih =>
    obtain ⟨later, he⟩ := ih
    cases hs with
    | prepare hp =>
      exact ⟨_, by rw [he, List.append_assoc]⟩
    | spend ht => exact ⟨later, he⟩

end AssetBridgePreparation
