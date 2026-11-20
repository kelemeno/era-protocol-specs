import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery
import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation

/-!
# Properties: the source burn's handler and the vault's refund of an unknown asset

Statements about the `b17415d20` parts of `EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery`:
`_burn`'s handler choice, the vault's refund `ntvRecover` (the refund of every asset other than an
L2's base token, see the Specs header) and the vault's registry runs.  Proofs are in
`EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery`.  The statements about the pin's
router refund and loop are History
(`EraSpec.Contracts.AssetRouterBase.History.Properties.AtomicRecovery`); the `b17415d20` refund
is `AtomicRecoveryAtHead`.

* The source burn uses the registered handler (`BurnUsesRegisteredHandler`).
* The vault's refund reverts on an asset it never registered whose id is not the NTV id of the
  pair in the data (`VaultRejectsUnknownAsset`); only the router reaches it
  (`VaultRefundOnlyByRouter`).
* A custom asset's id, hashed from a registrant other than the vault, is never such an id under
  injectivity on the two named triples (`CustomIdFailsAssetIdCheckOn`), and the vault never
  registers it along a logged registry run (`CustomIdUnknownAlongLoggedRunsOn`,
  `VaultStepLeavesAlone`).

No property takes a global hash premise: the `…On` premises are injectivity of `encodeAssetId` on
named triples.  These are supporting lemmas of `AtomicRecoveryAtHead`, not headlines.
-/

namespace Contracts.AssetRouter.AtomicRecovery

/-! ## The two sides of a transfer use different handlers -/

/-- **THE SOURCE BURN USES THE REGISTERED HANDLER.**  When the routing table names a handler
for the asset, `_burn` calls that handler's `bridgeBurn` (`AssetRouterBase.sol:312-330`). -/
def Properties.BurnUsesRegisteredHandler : Prop :=
  ∀ (cfg : Config) (R : Router) (a : AssetId), R.handler a ≠ 0 → burnHandler cfg R a = R.handler a

/-! ## An asset the vault does not know: the vault's refund reverts -/

/-- **THE VAULT REJECTS AN ASSET IT DOES NOT KNOW.**  No hash premise.  If the vault has no
token for `a` and `a` is not native, and `a` is not the NTV id of the pair decoded from the
data, `bridgeRecoverFailedTransfer` reverts — for every caller, value, chain, pause state and
every behaviour of the tracker, transfer, deploy and mint hooks. -/
def Properties.VaultRejectsUnknownAsset : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (caller : Address) (v : UInt256) (chainId : Chain) (a : AssetId) (m : Option MintData),
    VaultUnaware cfg w.vault a → FailsAssetIdCheck enc cfg a m →
      ntvRecover enc cfg hk w caller v chainId a m = none

/-- **A CUSTOM ASSET ID FAILS `assetIdCheck`**, with `encodeAssetId` injective on the two named
triples only: the custom id's preimage `(c₀, s, d)`, with `s` not the vault, and the NTV preimage
`(c, vault, originToken)` of the pair decoded from the data. -/
def Properties.CustomIdFailsAssetIdCheckOn : Prop :=
  ∀ (enc : AssetIdOf) (cfg : Config) (c₀ : Chain) (s : Address) (d : AssetData)
    (m : Option MintData), s ≠ cfg.ntv →
    (∀ md, m = some md → ∀ c, cfg.tokenOrigin md.metadata = some c →
      IdInjOn enc {(c₀, s, d), (c, cfg.ntv, NativeTokenVaultBase.widen md.originToken)}) →
      FailsAssetIdCheck enc cfg (enc c₀ s d) m

/-- **A REGISTRY STEP LEAVES OTHER IDS ALONE.**  A step of the registry model whose hashed pair
(if any) does not hash to `a` changes neither `tokenAddress[a]` nor `originChainId[a]`. -/
def Properties.VaultStepLeavesAlone : Prop :=
  ∀ (enc : AssetIdOf) (cfg : Config) (o : NativeTokenVault.Op) (W W' : NativeTokenVault.World)
    (a : AssetId),
    NativeTokenVault.StepOp (ntvId enc cfg) cfg.thisChain o W W' →
    (∀ p, o.pair cfg.thisChain = some p → ntvId enc cfg p.1 p.2 ≠ a) →
      LeavesAlone a W.vault W'.vault

/-- **THE VAULT NEVER REGISTERS A CUSTOM ID.**  At the end of every logged run of the registry
model from fresh storage, a custom id `enc c₀ s d` (`s` not the vault) is unknown to the vault,
given injectivity on the custom triple paired with each pair the run's log hashes. -/
def Properties.CustomIdUnknownAlongLoggedRunsOn : Prop :=
  ∀ (enc : AssetIdOf) (cfg : Config) (W : NativeTokenVault.World) (log : List NativeTokenVault.Op)
    (c₀ : Chain) (s : Address) (d : AssetData),
    cfg.thisChain ≠ 0 → s ≠ cfg.ntv →
    NativeTokenVault.ReachLog (ntvId enc cfg) cfg.thisChain NativeTokenVault.empty W log →
    (∀ p ∈ NativeTokenVault.registeredPairs cfg.thisChain log,
      IdInjOn enc {(c₀, s, d), (p.1, cfg.ntv, p.2)}) →
      VaultUnaware cfg W.vault (enc c₀ s d)

/-! ## Who reaches the vault's refund -/

/-- **ONLY THE ROUTER REACHES THE VAULT'S REFUND** (`onlyAssetRouter`,
`NativeTokenVaultBase.sol:104-107, 199`). -/
def Properties.VaultRefundOnlyByRouter : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (caller : Address) (v : UInt256) (chainId : Chain) (a : AssetId) (m : Option MintData),
    caller ≠ cfg.router → ntvRecover enc cfg hk w caller v chainId a m = none

/-! ## Refinement onto the canonical vault model -/

/-- **THE VAULT REFUND REFINES THE CANONICAL VAULT MODEL'S RECOVERY.**  On the registered bridged
branch of the canonical per-token model (`NativeTokenVaultBase.RegisteredBridged`), with the
registry entry of the call's asset the tracked token and origin chain, the router address and
this chain the per-token configuration's, and the canonical hooks as `vaultRefund`'s hooks
(`resolutionHooks`): `vaultRefund` on the call's caller, value, chain, asset and mint data is
`NativeTokenVaultBase.bridgeRecoverFailedTransfer` on the same call, for every call (the
guards agree too), leaving the registry unchanged.  No hash premise.  So the canonical model's
recovery results hold of this file's vault refund on that branch. -/
def Properties.VaultRefundRefinesResolution : Prop :=
  ∀ (Accounting : Type) (enc : AssetIdOf) (cfg : Config)
    (rh : NativeTokenVaultBase.ResolutionHooks Accounting)
    (s : NativeTokenVaultBase.State Accounting) (V : NativeTokenVault.Vault)
    (c : NativeTokenVaultBase.ResolutionCall),
    cfg.router = NativeTokenVaultBase.widen s.config.router →
    cfg.thisChain = s.config.chainId →
    V.originChain c.assetId = s.config.originChainId →
    V.token c.assetId = NativeTokenVaultBase.widen s.config.tokenAddress →
    NativeTokenVaultBase.RegisteredBridged s c →
      vaultRefund enc cfg (resolutionHooks rh) V s.paused s (NativeTokenVaultBase.widen c.caller)
          c.msgValue c.chain c.assetId (some c.data)
        = (NativeTokenVaultBase.bridgeRecoverFailedTransfer rh s c).map fun s' => (V, s')

end Contracts.AssetRouter.AtomicRecovery
