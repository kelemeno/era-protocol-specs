import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery
import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation

/-!
# Properties: what an atomic refund does with a bundle's asset-router calls

Statements about `EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery`.  Proofs are in
`EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery`.

The intended claim (`REVIEW.md`, the `L2AssetRouter` row: "only the manager invokes atomic
recovery; recovery restores the depositor rather than the remote recipient") holds for one kind
of bundle call and fails for two others.

* **Router-produced calls on assets the vault knows** are refunded to the burn's
  `originalCaller` — the depositor — for exactly the burned amount, and the remote receiver is
  ignored (`KnownBridgedAssetRefundsOriginalCaller`, `NativeAssetRefundsOriginalCaller`,
  `RefundIgnoresRemoteReceiver`, `PreparedBurnRefundsDepositor`).  These are results about the
  router's refund, which the manager runs only for a call that targets the router, as
  `routerCall` does.  The router produces such a call only for a destination other than L1.  For
  an L1 destination its call targets `L1_ASSET_ROUTER` (`L2AssetRouter.sol:336`) and these
  results do not apply: see `AtomicRecoveryFaithful`.
* **Calls on a custom-handler asset revert.**  The source burn went to the asset's own handler
  (`BurnUsesRegisteredHandler`), but the refund goes to the native token vault whatever the
  routing table says (`RecoveryCallsTheVault`, `RecoveryIgnoresHandler`), and the vault reverts
  on an asset it never registered whose id is not the NTV id of the pair in the data
  (`VaultRejectsUnknownAsset`, `UnknownAssetRecoveryReverts`).  A custom asset's id is hashed
  from a registrant other than the vault, so under injectivity on the two named triples it is
  never such an id (`CustomIdFailsAssetIdCheckOn`) and the vault never registers it
  (`CustomIdUnknownAlongLoggedRunsOn`).  Headline (a): `CustomHandlerDepositRefundReverts`.
  Because nothing catches the revert, one such call blocks the whole claim, including its
  vault-asset calls (`UnknownAssetOutcomeBlocksClaim`, `ClaimRevertsWithUnknownAssetCall`), in
  every registry state the model reaches (headline `CustomHandlerBundleNeverRefunded`) and after
  any steps that leave the asset's entry alone (`LegNeverRefunded`), and the only path to a vault
  refund is that claim (`RecoveryOnlyByManager`, `VaultRefundOnlyByRouter`).
  `CustomHandlerBundleIsStranded` is the concrete instance: an admitted two-call bundle whose
  vault-asset call alone is refundable.
* **Direct calls are refunded as if they were burns.**  The manager passes only a call's
  target and data, so the refund cannot tell a router-produced call from a direct call that
  names the router with self-written data (`RefundIgnoresCallSender`).  A direct call burns
  nothing at the source, yet its refund re-mints whatever amount, to whatever `originalCaller`,
  the data names (`DirectCallIsRefunded`, `DirectCallMintsUnbacked`); for an asset native to the
  chain, `NativeAssetRefundsOriginalCaller` with `RefundIgnoresCallSender` gives the same for the
  vault's escrow.

`ClaimSucceedsIffAccepted` ties the stateful refund loop to the outcome-list acceptance rule of
`AttackVectors.RecoveryLimits`, so its limits apply to this model unchanged.

Every property with premises has a satisfiability witness below.  No property takes a global
hash premise: the `…On` premises are injectivity of `encodeAssetId` on two named triples, and
the run premise is injectivity on the custom triple paired with each pair the run's own log
registers.
-/

namespace Contracts.AssetRouter.AtomicRecovery

open AttackVectors.RecoveryLimits (Outcome LegState ClaimAccepted)

/-! ## The two sides of a transfer use different handlers -/

/-- **THE SOURCE BURN USES THE REGISTERED HANDLER.**  When the routing table names a handler
for the asset, `_burn` calls that handler's `bridgeBurn` (`AssetRouterBase.sol:322-345`). -/
def Properties.BurnUsesRegisteredHandler : Prop :=
  ∀ (cfg : Config) (R : Router) (a : AssetId), R.handler a ≠ 0 → burnHandler cfg R a = R.handler a

/-! ## An asset the vault does not know: the refund reverts -/

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

/-! ## One such call blocks the whole bundle, permanently -/

/-- **ONLY THE ROUTER REACHES THE VAULT'S REFUND** (`onlyAssetRouter`,
`NativeTokenVaultBase.sol:107-110, 217`).  With `RecoveryOnlyByManager` and the single call site
in `_recoverBundle` (`AtomicFlowManager.sol:225`), a bundle call's burn is refunded only inside a
successful `claimRefund` of its whole bundle. -/
def Properties.VaultRefundOnlyByRouter : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (caller : Address) (v : UInt256) (chainId : Chain) (a : AssetId) (m : Option MintData),
    caller ≠ cfg.router → ntvRecover enc cfg hk w caller v chainId a m = none

end Contracts.AssetRouter.AtomicRecovery
