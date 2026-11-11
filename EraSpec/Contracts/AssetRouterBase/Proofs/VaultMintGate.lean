import EraSpec.Contracts.AssetRouterBase.Properties.VaultMintGate
import EraSpec.Contracts.AssetRouterBase.Proofs.AllWriters
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistryAndEscrow

/-!
# Proofs: the router's vault-mint premise, discharged by the vault model

The vault's `idShape` equation is written only by `_setNewTokenStorage`, at the id it
writes, together with that id's origin.  Both registration paths pass an id that is the
encoding of the origin they record, so the equation is preserved with no hash premise.
-/

namespace Contracts.AssetRouter.AllWriters

/-- The hash-free field of the vault's `Valid`. -/
def VaultIdShape (e : Contracts.NativeTokenVault.NtvAssetId)
    (V : Contracts.NativeTokenVault.Vault) : Prop :=
  ∀ a, Contracts.NativeTokenVault.Registered V a → a = e (V.originChain a) (V.originToken a)

lemma vaultIdShape_of_fields {e : Contracts.NativeTokenVault.NtvAssetId}
    {V V' : Contracts.NativeTokenVault.Vault} (h1 : V'.token = V.token)
    (h2 : V'.originChain = V.originChain) (h3 : V'.originToken = V.originToken)
    (hV : VaultIdShape e V) : VaultIdShape e V' := by
  intro x hx
  have hx' : V.token x ≠ 0 := by rw [← h1]; exact hx
  rw [h2, h3]
  exact hV x hx'

lemma vaultIdShape_setNewTokenStorage {e : Contracts.NativeTokenVault.NtvAssetId}
    {V : Contracts.NativeTokenVault.Vault} {a : AssetId} {t ot : Address} {origin : Chain}
    (hV : VaultIdShape e V) (ha : a = e origin ot) :
    VaultIdShape e (Contracts.NativeTokenVault.setNewTokenStorage V a t ot origin) := by
  intro x hx
  by_cases hxa : x = a
  · subst hxa
    rw [Contracts.NativeTokenVault.sn_originChain_self,
      Contracts.NativeTokenVault.sn_originToken_self]
    exact ha
  · rw [Contracts.NativeTokenVault.sn_registered_of_ne V a t ot origin hxa] at hx
    rw [Contracts.NativeTokenVault.sn_originChain_of_ne V a t ot origin hxa,
      Contracts.NativeTokenVault.sn_originToken_of_ne V a t ot origin hxa]
    exact hV x hx

lemma vaultIdShape_step {e : Contracts.NativeTokenVault.NtvAssetId} {thisChain : Chain}
    {W X : Contracts.NativeTokenVault.World}
    (hs : Contracts.NativeTokenVault.Step e thisChain W X) (hW : VaultIdShape e W.vault) :
    VaultIdShape e X.vault := by
  cases hs with
  | registerNative _ => exact vaultIdShape_setNewTokenStorage hW rfl
  | registerBridged hg => exact vaultIdShape_setNewTokenStorage hW hg.idChecked
  | bridgeOut _ =>
    exact vaultIdShape_of_fields
      (by unfold Contracts.NativeTokenVault.bridgeOut; split_ifs <;> rfl)
      (by unfold Contracts.NativeTokenVault.bridgeOut; split_ifs <;> rfl)
      (by unfold Contracts.NativeTokenVault.bridgeOut; split_ifs <;> rfl) hW
  | bridgeIn _ =>
    exact vaultIdShape_of_fields
      (by unfold Contracts.NativeTokenVault.bridgeIn; split_ifs <;> rfl)
      (by unfold Contracts.NativeTokenVault.bridgeIn; split_ifs <;> rfl)
      (by unfold Contracts.NativeTokenVault.bridgeIn; split_ifs <;> rfl) hW
  | donate => exact hW

theorem vault_run_idShape {e : Contracts.NativeTokenVault.NtvAssetId} {thisChain : Chain}
    {W : Contracts.NativeTokenVault.World}
    (hr : Contracts.NativeTokenVault.Reach e thisChain Contracts.NativeTokenVault.empty W) :
    VaultIdShape e W.vault := by
  induction hr with
  | refl => intro a ha; exact absurd rfl ha
  | tail _ hs ih => exact vaultIdShape_step hs ih

theorem vault_model_mints_only_ntv_ids {e : Contracts.NativeTokenVault.NtvAssetId}
    {enc : AssetIdOf} {ntvAddr : Address} {thisChain : Chain}
    (hagree : EncodingsAgree e enc ntvAddr) {a : AssetId} (hm : VaultModelMints e thisChain a) :
    IsNtvId enc ntvAddr a := by
  obtain ⟨W, _, hr, hg⟩ := hm
  exact ⟨W.vault.originChain a, W.vault.originToken a,
    (vault_run_idShape hr a hg.registered).trans (hagree _ _)⟩

theorem vault_model_discharges_mint_premise {K : Cfg} {e : Contracts.NativeTokenVault.NtvAssetId}
    (hagree : EncodingsAgree e K.enc K.ntvAddr)
    (hsub : ∀ a, K.ntvMints a → VaultModelMints e K.thisChain a) : MintsOnlyNtvIds K :=
  fun a ha => vault_model_mints_only_ntv_ids hagree (hsub a ha)

/-! ## The witness: an L2 router whose vault is the vault model -/

/-- The vault's encoding: the router's `wEnc` at the vault sender `8`. -/
def wE : Contracts.NativeTokenVault.NtvAssetId := fun c t => wEnc c 8 t

/-- `wK2` with the vault model's mint gate. -/
def wKV : Cfg := { wK2 with ntvMints := VaultModelMints wE 2 }

/-- The vault, on chain `2`, deploys the representation `50` of token `0` from chain `1`:
id `wE 1 0 = 100`. -/
def wW1 : Contracts.NativeTokenVault.World :=
  { Contracts.NativeTokenVault.empty with
    vault := Contracts.NativeTokenVault.registerBridged
      Contracts.NativeTokenVault.empty.vault 100 50 0 1 }

lemma wW1_reach : Contracts.NativeTokenVault.Reach wE 2 Contracts.NativeTokenVault.empty wW1 :=
  .tail .refl (.registerBridged ⟨by decide, by decide, by decide, by decide, rfl, fun h => h rfl⟩)

lemma wKV_mints_100 : VaultModelMints wE 2 100 :=
  ⟨wW1, 0, wW1_reach, ⟨by decide, fun _ => Nat.zero_le _⟩⟩

theorem run_valid_fails_with_vault_model :
    ∃ (K : Cfg) (e : Contracts.NativeTokenVault.NtvAssetId) (a : AssetId) (R : Router),
      K.side = .l2 ∧ K.ntv ≠ 0 ∧ EncodingsAgree e K.enc K.ntvAddr ∧
      (∀ x, K.ntvMints x ↔ VaultModelMints e K.thisChain x) ∧ VaultModelMints e K.thisChain a ∧
      IsNtvId K.enc K.ntvAddr K.seedId ∧
      ARun K empty [.finalize a] R ∧ ¬ Valid R ∧ WeakValid K R :=
  ⟨wKV, wE, 100, pointAt empty 100 8, rfl, by decide, fun _ _ => rfl, fun _ => Iff.rfl,
    wKV_mints_100, isNtv_101,
    (ARun.nil).snoc (AStep.finalize rfl wKV_mints_100 (fun _ => by decide)),
    not_valid_pointAt (by decide) rfl, weakValid_pointAt_empty (K := wKV) isNtv_100⟩

end Contracts.AssetRouter.AllWriters

/-! ## Certificates -/

namespace Contracts.AssetRouter.AllWriters

theorem VaultRunIdShape : Properties.VaultRunIdShape :=
  fun _ _ _ hr => vault_run_idShape hr

theorem VaultModelMintsOnlyNtvIds : Properties.VaultModelMintsOnlyNtvIds :=
  fun _ _ _ _ hagree _ hm => vault_model_mints_only_ntv_ids hagree hm

theorem VaultModelDischargesMintPremise : Properties.VaultModelDischargesMintPremise :=
  fun _ _ hagree hsub => vault_model_discharges_mint_premise hagree hsub

theorem RunWeakValidWithVaultModel : Properties.RunWeakValidWithVaultModel :=
  fun K _ hagree hsub hseed _ _ hr hops =>
    run_weakValid (vault_model_discharges_mint_premise hagree hsub) hseed hr
      (empty_weakValid K) hops

theorem RunValidFailsWithVaultModel : Properties.RunValidFailsWithVaultModel :=
  run_valid_fails_with_vault_model

end Contracts.AssetRouter.AllWriters
