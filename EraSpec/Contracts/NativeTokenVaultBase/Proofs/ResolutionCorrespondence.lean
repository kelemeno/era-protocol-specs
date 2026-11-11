import EraSpec.Contracts.NativeTokenVaultBase.Properties.ResolutionCorrespondence
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Resolution
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.ModelCorrespondence

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain Vault World NtvAssetId Valid)

theorem ResolutionIsForeignBridgeIn : Properties.ResolutionIsForeignBridgeIn := by
  intro Accounting rh s t c e thisChain W hc h
  have hcore : RegisteredBridged s c ∧ t.config = s.config ∧ t.registry = s.registry ∧
      t.token.config = s.token.config := by
    rcases h with h | h
    · obtain ⟨_, hs, _, _, _, _, _, htc, hcfg, hreg, _⟩ := BridgeMintExact _ rh s t c h
      exact ⟨hs, hcfg, hreg, htc⟩
    · obtain ⟨_, hs, _, _, _, _, _, htc, hcfg, hreg, _⟩ := RecoverExact _ rh s t c h
      exact ⟨hs, hcfg, hreg, htc⟩
  obtain ⟨hs, hcfg, hreg, htc⟩ := hcore
  have hasset : c.assetId = s.config.assetId := hs.2.1
  -- the call's asset is registered in the registry model: its token slot is the tracked token
  have hregistered : NativeTokenVault.Registered W.vault c.assetId := by
    show W.vault.token c.assetId ≠ 0
    rw [hc.registry.token, hs.2.2.2.1]
    exact fun h0 => hs.2.2.2.2 (widen_eq_zero.mp h0)
  -- and foreign: the registry model records the tracked asset's origin chain
  have hforeign : ¬ NativeTokenVault.Native thisChain W.vault c.assetId := by
    show ¬ W.vault.originChain c.assetId = thisChain
    have ho := (hc.tracked (hasset ▸ hregistered)).1
    rw [hasset, ho, hc.chain]
    exact hs.2.2.1
  have hvault : (NativeTokenVault.bridgeIn thisChain W c.chain c.assetId
      c.data.amount.val).vault = W.vault := by
    simp [NativeTokenVault.bridgeIn, ite_eq_right hforeign]
  refine ⟨NativeTokenVault.Step.bridgeIn ⟨hregistered, fun hn => absurd hn hforeign⟩, hforeign,
    hvault, ?_, ?_, ?_⟩
  · rw [hcfg]
    exact hc.chain
  · rw [hreg]
    exact hc.registry
  · rw [hcfg, htc]
    exact hc.tracked

namespace ResolutionCorrespondenceExample

/-- A hook with no accounting. -/
def unitHooks : ResolutionHooks Unit := ⟨fun a _ _ _ _ => some a⟩

/-- One unit to `12` from chain `4`, original caller `13`, for the witness state's asset
`2 + 1`, called by its router `1`. -/
def call : ResolutionCall := ⟨1, 0, 4, 2 + 1, ⟨13, 12, 7, 1, []⟩⟩

theorem call_entry : ResolveEntryAllowed witnessPrepState call := ⟨rfl, rfl, rfl⟩

theorem call_scope : RegisteredBridged witnessPrepState call :=
  ⟨by decide, rfl, by decide, witnessPrep_token, by decide⟩

theorem call_supply :
    witnessPrepState.token.totalSupply + call.data.amount.val < UInt256.size := by
  decide

theorem satisfiable : Properties.ResolutionCorrespondenceSatisfiable := by
  have hw : WellFormed witnessPrepState := ⟨witnessToken_ledger, witnessPrep_rc⟩
  obtain ⟨t, ht⟩ := BridgeMintEnabled Unit unitHooks witnessPrepState call () witnessPrep_rc
    call_entry call_scope (by decide) call_supply rfl
  obtain ⟨t', ht'⟩ := RecoverEnabled Unit unitHooks witnessPrepState call () witnessPrep_rc
    call_entry call_scope (by decide) call_supply rfl
  exact ⟨toyId, 1, ⟨witnessVault, NativeTokenVault.empty.audit⟩, unitHooks, witnessPrepState, t,
    call, witnessVault_valid, witnessPrep_corr, hw, ht, by rw [ht']; exact Option.some_ne_none _,
    by decide⟩

end ResolutionCorrespondenceExample

theorem ResolutionCorrespondenceSatisfiable : Properties.ResolutionCorrespondenceSatisfiable :=
  ResolutionCorrespondenceExample.satisfiable

end Contracts.NativeTokenVaultBase
