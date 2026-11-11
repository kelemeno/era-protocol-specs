import EraSpec.Contracts.AssetRouterBase.Specs.VaultMintGate

/-!
# Properties: the router's vault-mint premise, discharged by the vault model

Statements about `EraSpec.Contracts.AssetRouterBase.Specs.VaultMintGate`.  Proofs are in
`EraSpec.Contracts.AssetRouterBase.Proofs.VaultMintGate`.

* The vault model's `idShape` equation holds along every vault run, with no hash premise
  (`VaultRunIdShape`).  In `Contracts.NativeTokenVault` it is a field of `Valid`, whose
  other fields need a hash premise; this one does not.
* Hence the vault model mints only vault ids (`VaultModelMintsOnlyNtvIds`).  Any router
  whose vault-mint gate lies inside the vault model's satisfies `MintsOnlyNtvIds`
  (`VaultModelDischargesMintPremise`).
* `AllWriters.RunWeakValid` with that premise discharged (`RunWeakValidWithVaultModel`).
  The `AllWriters` countermodel to `RunValid` survives with the vault model as the vault
  (`RunValidFailsWithVaultModel`), which is also the witness that these premises are
  jointly satisfiable.
-/

namespace Contracts.AssetRouter.AllWriters

/-- **EVERY REGISTERED VAULT ID IS THE ENCODING OF ITS RECORDED ORIGIN, ALONG EVERY VAULT
RUN.**  No hash premise.  `_unsafeRegisterNativeToken` derives the id from this chain and
the token (`NTV/NativeTokenVaultBase.sol:516`).  `assetIdCheck` enforces the encoding on
the bridged path (:580).  Neither needs injectivity to keep the equation true. -/
def Properties.VaultRunIdShape : Prop :=
  ∀ (e : Contracts.NativeTokenVault.NtvAssetId) (thisChain : Chain)
    (W : Contracts.NativeTokenVault.World),
    Contracts.NativeTokenVault.Reach e thisChain Contracts.NativeTokenVault.empty W →
      ∀ a, Contracts.NativeTokenVault.Registered W.vault a →
        a = e (W.vault.originChain a) (W.vault.originToken a)

/-- **THE VAULT MODEL MINTS ONLY VAULT IDS.**  If the vault's encoding is the router's at
`L2_NATIVE_TOKEN_VAULT_ADDR`, every id at which the vault model admits an inbound
transfer is a vault id in the router's sense.  No hash premise. -/
def Properties.VaultModelMintsOnlyNtvIds : Prop :=
  ∀ (e : Contracts.NativeTokenVault.NtvAssetId) (enc : AssetIdOf) (ntvAddr : Address)
    (thisChain : Chain), EncodingsAgree e enc ntvAddr →
      ∀ a, VaultModelMints e thisChain a → IsNtvId enc ntvAddr a

/-- **THE ROUTER'S MINT PREMISE, DISCHARGED.**  A router configuration whose vault-mint
gate lies inside the vault model's, with agreeing encodings, satisfies
`MintsOnlyNtvIds`. -/
def Properties.VaultModelDischargesMintPremise : Prop :=
  ∀ (K : Cfg) (e : Contracts.NativeTokenVault.NtvAssetId), EncodingsAgree e K.enc K.ntvAddr →
    (∀ a, K.ntvMints a → VaultModelMints e K.thisChain a) → MintsOnlyNtvIds K

/-- **THE WEAKENED INVARIANT, WITH THE VAULT AS MODELLED.**  `AllWriters.RunWeakValid`, its
mint premise replaced by the vault model: along every run from fresh storage with no
counterpart write and no zero-tracker write, every live route has a nonzero tracker or
is a vault route.  The remaining premise is that the seeded id is a vault id. -/
def Properties.RunWeakValidWithVaultModel : Prop :=
  ∀ (K : Cfg) (e : Contracts.NativeTokenVault.NtvAssetId), EncodingsAgree e K.enc K.ntvAddr →
    (∀ a, K.ntvMints a → VaultModelMints e K.thisChain a) → IsNtvId K.enc K.ntvAddr K.seedId →
    ∀ (ops : List Op) (R : Router), ARun K empty ops R →
      (∀ op ∈ ops, ¬ op.IsCounterpart ∧ ¬ op.ZeroTracker) → WeakValid K R

/-- **`RunValid` STILL FAILS, WITH THE VAULT MODEL AS THE VAULT.**  An L2 router whose
vault-mint gate is exactly the vault model's, with agreeing encodings and a vault id
seeded.  One fallback deposit from fresh storage ends violating `Valid` and satisfying
`WeakValid`.  This also witnesses that the premises of `RunWeakValidWithVaultModel` and
`VaultModelMintsOnlyNtvIds` hold together with a nonempty mint gate. -/
def Properties.RunValidFailsWithVaultModel : Prop :=
  ∃ (K : Cfg) (e : Contracts.NativeTokenVault.NtvAssetId) (a : AssetId) (R : Router),
    K.side = .l2 ∧ K.ntv ≠ 0 ∧ EncodingsAgree e K.enc K.ntvAddr ∧
    (∀ x, K.ntvMints x ↔ VaultModelMints e K.thisChain x) ∧ VaultModelMints e K.thisChain a ∧
    IsNtvId K.enc K.ntvAddr K.seedId ∧
    ARun K empty [.finalize a] R ∧ ¬ Valid R ∧ WeakValid K R

end Contracts.AssetRouter.AllWriters
