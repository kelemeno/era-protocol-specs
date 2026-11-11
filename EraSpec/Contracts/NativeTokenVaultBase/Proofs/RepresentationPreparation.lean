import EraSpec.Contracts.NativeTokenVaultBase.Properties.RepresentationPreparation
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Model

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

private theorem prepare_view {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (h : prepare hooks s r = some out) :
    InScope s r ∧ EntryAllowed s r ∧ r.msgValue = 0 ∧
    ∃ accounted burned metadata,
      hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount =
        some accounted ∧
      BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount = some burned ∧
      burned.config.originToken ≠ 0 ∧ s.config.originChainId ≠ 0 ∧
      hooks.metadata burned s.config.originChainId = some metadata ∧
      out = ⟨{ s with token := burned, accounting := accounted }, mintData r burned metadata⟩ := by
  unfold prepare at h
  split at h
  · rename_i hg
    cases ha : hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount with
    | none => simp only [ha] at h
    | some accounted =>
      simp only [ha] at h
      split at h
      · rename_i hv
        cases hb : BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount with
        | none => simp only [hb] at h
        | some burned =>
          simp only [hb] at h
          split at h
          · rename_i ho
            cases hm : hooks.metadata burned s.config.originChainId with
            | none => simp only [hm] at h
            | some metadata =>
              simp only [hm] at h
              exact ⟨hg.1, hg.2, hv, accounted, burned, metadata, rfl, rfl,
                ho.1, ho.2, hm, (Option.some.inj h).symm⟩
          · cases h
      · cases h
  · cases h

theorem preparation_backed {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (hw : WellFormed s)
    (h : prepare hooks s r = some out) : Properties.preparation_backed hw h := by
  obtain ⟨_hs, he, _hv, accounted, burned, metadata, _ha, hb, _ho, _hc, _hm, rfl⟩ :=
    prepare_view h
  rcases BridgedStandardERC20.burn_exact hw.1 hb with ⟨_, _, hbal, hsupply, _, _⟩
  exact ⟨hb, hbal, hsupply, he.2.2.2.2.2⟩

theorem preparation_payload {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (hw : WellFormed s)
    (h : prepare hooks s r = some out) : Properties.preparation_payload hw h := by
  obtain ⟨_hs, _he, _hv, accounted, burned, metadata, _ha, hb, ho, _hc, hm, rfl⟩ :=
    prepare_view h
  rcases BridgedStandardERC20.burn_exact hw.1 hb with ⟨_, _, _, _, _, hconfig⟩
  exact ⟨rfl, rfl, congrArg BridgedStandardERC20.Config.originToken hconfig,
    rfl, ho, hm⟩

theorem preparation_accounting {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (h : prepare hooks s r = some out) :
    Properties.preparation_accounting h := by
  obtain ⟨_hs, _he, _hv, accounted, burned, metadata, ha, _hb, _ho, _hc, _hm, rfl⟩ :=
    prepare_view h
  exact ha

theorem preparation_asset_binding {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {out : Result Accounting} (hw : WellFormed s)
    (h : prepare hooks s r = some out) : Properties.preparation_asset_binding hw h := by
  obtain ⟨hs, he, _hv, accounted, burned, metadata, _ha, hb, _ho, _hc, _hm, rfl⟩ :=
    prepare_view h
  have hselected : selectedToken s r = s.config.tokenAddress := hs.2.2.2.2
  have hreverse := he.2.2.2.2.1
  rw [hselected, hw.2.2.2.2] at hreverse
  rcases BridgedStandardERC20.burn_exact hw.1 hb with ⟨_, _, _, _, _, hconfig⟩
  refine ⟨hreverse.symm, ?_, hselected⟩
  exact (congrArg BridgedStandardERC20.Config.assetId hconfig).trans
    (hw.2.2.1.trans hreverse)

theorem preparation_preserves_ledger {hooks : Hooks Accounting}
    {s : State Accounting} {r : Request} {out : Result Accounting}
    (hw : WellFormed s) (h : prepare hooks s r = some out) :
    Properties.preparation_preserves_ledger hw h := by
  obtain ⟨_hs, _he, _hv, accounted, burned, metadata, _ha, hb, _ho, _hc, _hm, rfl⟩ :=
    prepare_view h
  rcases BridgedStandardERC20.burn_exact hw.1 hb with ⟨_, _, _, _, hframe, hconfig⟩
  refine ⟨⟨BridgedStandardERC20.burn_preserves_ledger hw.1 hb, ?_, ?_, hw.2.2.2⟩,
    rfl, rfl, rfl, hframe⟩
  · exact (congrArg BridgedStandardERC20.Config.vault hconfig).trans hw.2.1
  · exact (congrArg BridgedStandardERC20.Config.assetId hconfig).trans hw.2.2.1

theorem preparation_preserves_ledger_invariant {hooks : Hooks Accounting}
    {s : State Accounting} {r : Request} {out : Result Accounting}
    (hl : LedgerInvariant s) (h : prepare hooks s r = some out) :
    Properties.preparation_preserves_ledger_invariant hl h := by
  obtain ⟨_hs, _he, _hv, accounted, burned, metadata, _ha, hb, _ho, _hc, _hm, rfl⟩ :=
    prepare_view h
  exact BridgedStandardERC20.burn_preserves_ledger hl hb

theorem preparation_preserves_representation {hooks : Hooks Accounting}
    {s : State Accounting} {r : Request} {out : Result Accounting}
    (hr : RepresentationConsistent s) (h : prepare hooks s r = some out) :
    Properties.preparation_preserves_representation hr h := by
  obtain ⟨_hs, _he, _hv, accounted, burned, metadata, _ha, hb, _ho, _hc, _hm, rfl⟩ :=
    prepare_view h
  have hconfig : burned.config = s.token.config := by
    unfold BridgedStandardERC20.burn at hb
    split at hb
    · rw [← Option.some.inj hb]
      rfl
    · cases hb
  refine ⟨?_, ?_, hr.2.2⟩
  · exact (congrArg BridgedStandardERC20.Config.vault hconfig).trans hr.1
  · exact (congrArg BridgedStandardERC20.Config.assetId hconfig).trans hr.2.1

theorem failed_preparation_atomic {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (h : prepare hooks s r = none) :
    Properties.failed_preparation_atomic h := by
  simp only [Properties.failed_preparation_atomic, transact, h]

theorem metadata_failure_atomic {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} (h : ∀ token, hooks.metadata token s.config.originChainId = none) :
    Properties.metadata_failure_atomic (r := r) h := by
  have hf : prepare hooks s r = none := by
    cases hp : prepare hooks s r with
    | none => rfl
    | some out =>
      obtain ⟨_hs, _he, _hv, accounted, burned, metadata, _ha, _hb, _ho, _hc, hm, _hout⟩ :=
        prepare_view hp
      rw [h burned] at hm
      cases hm
  exact failed_preparation_atomic hf

theorem accounting_failure_atomic {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request}
    (h : hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount = none) :
    Properties.accounting_failure_atomic h := by
  have hf : prepare hooks s r = none := by
    simp only [prepare, h]
    split <;> rfl
  exact failed_preparation_atomic hf

theorem preparation_enabled {hooks : Hooks Accounting} {s : State Accounting}
    {r : Request} {accounted : Accounting} {metadata : Bytes}
    (hw : WellFormed s) (hs : InScope s r) (he : EntryAllowed s r)
    (hv : r.msgValue = 0) (hd : r.depositor ≠ 0)
    (hb : r.data.amount.val ≤ s.token.balances r.depositor)
    (ho : s.token.config.originToken ≠ 0) (hc : s.config.originChainId ≠ 0)
    (ha : hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount =
      some accounted)
    (hm : hooks.metadata (BridgedStandardERC20.burnEffect s.token r.depositor r.data.amount)
      s.config.originChainId = some metadata) :
    Properties.preparation_enabled hw hs he hv hd hb ho hc ha hm := by
  have hg : BridgedStandardERC20.BurnAllowed s.token s.config.vault r.depositor r.data.amount :=
    ⟨by rw [hw.2.1]; exact hs.1, hw.2.1.symm, hd, hb⟩
  have hburn : BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount =
      some (BridgedStandardERC20.burnEffect s.token r.depositor r.data.amount) := if_pos hg
  have hentry : InScope s r ∧ EntryAllowed s r := ⟨hs, he⟩
  have horigin : (BridgedStandardERC20.burnEffect s.token r.depositor r.data.amount).config.originToken ≠ 0 ∧
      s.config.originChainId ≠ 0 := ⟨ho, hc⟩
  unfold Properties.preparation_enabled
  simp only [prepare, if_pos hentry, ha, if_pos hv, hburn, if_pos horigin, hm]
  exact ⟨_, rfl⟩

end Contracts.NativeTokenVaultBase
