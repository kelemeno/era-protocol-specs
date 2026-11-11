import EraSpec.Contracts.NativeTokenVaultBase.Properties.Reinitialization
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RepresentationPreparation
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Reinitialization

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

private theorem reinit_token {s : State Accounting} {version : UInt8}
    {metadata : BridgedStandardERC20.Metadata} {beaconOwner : Option Address} {caller : Address}
    {getters : BridgedStandardERC20.Getters} {name symbol : BridgedStandardERC20.Text}
    {version' : UInt8} {t : BridgedStandardERC20.TokenStorage}
    (h : BridgedStandardERC20.reinitializeToken beaconOwner (trackedStorage s version metadata)
      caller getters name symbol version' = some t) : withTracked s t = s := by
  rw [BridgedStandardERC20.ReinitExactEffect _ _ _ _ _ _ _ _ h]
  rfl

/-- Once a preparation succeeded with the token's metadata at `m`, the same request with the
metadata at `m'` gives the same result with the bytes the metadata read returns on `m'`, or
fails exactly when that read fails. -/
private theorem prepare_other_metadata {hooks : MetaHooks Accounting} {s : State Accounting}
    {r : Request} {m m' : BridgedStandardERC20.Metadata} {out : Result Accounting}
    (h : prepare (hooks.toHooks m) s r = some out) :
    prepare (hooks.toHooks m') s r =
      (hooks.metadata m' out.state.token s.config.originChainId).map
        fun bytes => ⟨out.state, { out.data with metadata := bytes }⟩ := by
  unfold prepare at h ⊢
  split at h
  · rename_i hg
    rw [ite_eq_left hg]
    simp only [MetaHooks.toHooks] at h ⊢
    cases ha : hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount with
    | none => simp only [ha, reduceCtorEq] at h
    | some accounted =>
      simp only [ha] at h ⊢
      split at h
      · rename_i hv
        rw [ite_eq_left hv]
        cases hb : BridgedStandardERC20.burn s.token s.config.vault r.depositor r.data.amount with
        | none => simp only [hb, reduceCtorEq] at h
        | some burned =>
          simp only [hb] at h ⊢
          split at h
          · rename_i ho
            rw [ite_eq_left ho]
            cases hm : hooks.metadata m burned s.config.originChainId with
            | none => simp only [hm, reduceCtorEq] at h
            | some md =>
              simp only [hm] at h
              obtain rfl := (Option.some.inj h).symm
              cases hm' : hooks.metadata m' burned s.config.originChainId with
              | none => rfl
              | some bytes => rfl
          · cases h
      · cases h
  · cases h

theorem ReinitLeavesVaultStateUnchanged : Properties.ReinitLeavesVaultStateUnchanged := by
  intro Accounting s version metadata beaconOwner caller getters name symbol version' t h
  exact reinit_token h

theorem ReinitPreservesVaultInvariants : Properties.ReinitPreservesVaultInvariants := by
  intro Accounting s version metadata beaconOwner caller getters name symbol version' t h
  rw [reinit_token h]
  exact ⟨Iff.rfl, Iff.rfl, Iff.rfl⟩

theorem ReinitKeepsPreparationExceptMetadata :
    Properties.ReinitKeepsPreparationExceptMetadata := by
  intro Accounting hooks s version metadata beaconOwner caller getters name symbol version' t r
    out bytes h hp hb
  rw [reinit_token h, prepare_other_metadata hp, hb]
  rfl

theorem ReinitChangesOnlyPreparedMetadata : Properties.ReinitChangesOnlyPreparedMetadata := by
  intro Accounting hooks s version metadata beaconOwner caller getters name symbol version' t r
    out out' h hp hp'
  rw [reinit_token h, prepare_other_metadata hp] at hp'
  cases hm : hooks.metadata t.metadata out.state.token s.config.originChainId with
  | none => simp only [hm, Option.map_none, reduceCtorEq] at hp'
  | some bytes =>
    simp only [hm, Option.map_some, Option.some.injEq] at hp'
    subst hp'
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## Witness -/

private theorem wToken_mint :
    BridgedStandardERC20.mint (BridgedStandardERC20.empty ⟨1, 9, 5⟩) 1 4 10 = some wToken := by
  unfold BridgedStandardERC20.mint
  rw [ite_eq_left]
  · rfl
  · refine ⟨by decide, rfl, by decide, ?_⟩
    simp only [BridgedStandardERC20.empty]
    decide

private theorem wVault_wellFormed : WellFormed wVault := by
  have hw0 : BridgedStandardERC20.WellFormed (BridgedStandardERC20.empty ⟨1, 9, 5⟩) :=
    (BridgedStandardERC20.one_unit_roundtrip ⟨1, 9, 5⟩ 4 (by decide) (by decide)).1
  exact ⟨BridgedStandardERC20.mint_preserves_ledger hw0 wToken_mint, rfl, rfl, rfl, rfl⟩

theorem VaultReinitWitness : Properties.VaultReinitWitness := by
  have hw := wVault_wellFormed
  have hre : BridgedStandardERC20.ReinitAllowed (some 13) (trackedStorage wVault 1 wMetadata)
      13 2 := ⟨rfl, by decide, rfl⟩
  have hreinit : BridgedStandardERC20.reinitializeToken (some 13)
      (trackedStorage wVault 1 wMetadata) 13 ⟨false, false, false⟩ [0x42] [0x42] 2 =
      some ⟨wVault.token, 2, BridgedStandardERC20.reinitMetadata wMetadata ⟨false, false, false⟩
        [0x42] [0x42]⟩ := by
    unfold BridgedStandardERC20.reinitializeToken
    rw [ite_eq_left hre]
    rfl
  have hs : InScope wVault wRequest := by decide
  have he : EntryAllowed wVault wRequest := by decide
  have hb : wRequest.data.amount.val ≤ wVault.token.balances wRequest.depositor := by decide
  obtain ⟨out, hout⟩ := preparation_enabled (hooks := wHooks.toHooks wMetadata)
    (accounted := ()) (metadata := [0x41]) hw hs he rfl (by decide) hb (by decide) (by decide)
    rfl rfl
  have hmd : out.data.metadata = [0x41] := by
    have hm := (preparation_payload hw hout).2.2.2.2.2
    exact (Option.some.inj hm).symm
  refine ⟨_, out, _, hw, hreinit, hout,
    ReinitKeepsPreparationExceptMetadata wHooks wVault 1 wMetadata (some 13) 13
      ⟨false, false, false⟩ [0x42] [0x42] 2 _ wRequest out [0x42] hreinit hout rfl,
    hmd, rfl, rfl, rfl⟩

end Contracts.NativeTokenVaultBase
