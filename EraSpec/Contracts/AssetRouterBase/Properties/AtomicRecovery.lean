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
  `RefundIgnoresRemoteReceiver`, `PreparedBurnRefundsDepositor`).
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

/-- **THE REFUND ALWAYS CALLS THE VAULT.**  For every `finalizeDeposit` call, the router's
`recoverAtomicCall` is exactly the vault's `bridgeRecoverFailedTransfer` on the call's own
`(destination chain, asset id, mint data)`, called by the router with zero value, followed by
`return true` (`L2AssetRouter.sol:293-295`). -/
def Properties.RecoveryCallsTheVault : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src : Chain) (a : AssetId) (m : Option MintData),
    recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a m)
      = (ntvRecover enc cfg hk w cfg.router 0 dest a m).map (fun w' => (w', true))

/-- **THE REFUND DOES NOT READ THE ROUTING TABLE.**  Replacing the router's maps by any `R`
changes neither the outcome nor the effect of `recoverAtomicCall`. -/
def Properties.RecoveryIgnoresHandler : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X) (R : Router)
    (caller : Address) (dest : Chain) (d : CallData),
    recoverAtomicCall enc cfg hk { w with router := R } caller dest d
      = (recoverAtomicCall enc cfg hk w caller dest d).map (fun p => ({ p.1 with router := R }, p.2))

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

/-- **…SO THE ROUTER'S REFUND REVERTS, RATHER THAN RETURNING `false`.**  The manager's call of
`recoverAtomicCall` on such a `finalizeDeposit` call reverts; its outcome is `reverts`, not
`declined` (`IAtomicRecoverable.sol:13-15` asks for `false`). -/
def Properties.UnknownAssetRecoveryReverts : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src : Chain) (a : AssetId) (m : Option MintData),
    VaultUnaware cfg w.vault a → FailsAssetIdCheck enc cfg a m →
      recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a m) = none
      ∧ outcomeOf (recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a m))
          = Outcome.reverts

/-- **A CUSTOM ASSET ID FAILS `assetIdCheck`**, with `encodeAssetId` injective on the two named
triples only: the custom id's preimage `(c₀, s, d)`, with `s` not the vault, and the NTV preimage
`(c, vault, originToken)` of the pair decoded from the data. -/
def Properties.CustomIdFailsAssetIdCheckOn : Prop :=
  ∀ (enc : AssetIdOf) (cfg : Config) (c₀ : Chain) (s : Address) (d : AssetData)
    (m : Option MintData), s ≠ cfg.ntv →
    (∀ md, m = some md → ∀ c, cfg.tokenOrigin md.metadata = some c →
      IdInjOn enc {(c₀, s, d), (c, cfg.ntv, NativeTokenVaultBase.widen md.originToken)}) →
      FailsAssetIdCheck enc cfg (enc c₀ s d) m

/-- **A CUSTOM-ASSET REFUND REVERTS, OR A PINNED COLLISION.**  No hash premise.  On an asset the
vault does not know, the refund reverts unless the custom id `enc c₀ s d` equals the NTV id of
the very pair decoded from the call's data. -/
def Properties.CustomAssetRecoveryRevertsOrCollision : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src c₀ : Chain) (s : Address) (d : AssetData) (m : Option MintData),
    VaultUnaware cfg w.vault (enc c₀ s d) →
      recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src (enc c₀ s d) m) = none
      ∨ ∃ md c, m = some md ∧ cfg.tokenOrigin md.metadata = some c
          ∧ enc c₀ s d = enc c cfg.ntv (NativeTokenVaultBase.widen md.originToken)

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

/-- **HEADLINE (a): A CUSTOM-HANDLER DEPOSIT IS BURNED BY ITS HANDLER AND ITS REFUND REVERTS.**
Asset `a = enc c₀ s d` was registered by `s`, not the vault, and the routing table points it at a
handler other than the vault.  The vault's registry is the end of any logged registry run, and
`encodeAssetId` is injective on the custom triple paired with each logged pair and with the pair
decoded from the call.  Then the source burn went to the custom handler, and the refund of the
call reverts. -/
def Properties.CustomHandlerDepositRefundReverts : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (log : List NativeTokenVault.Op) (audit : NativeTokenVault.Audit)
    (dest src c₀ : Chain) (s : Address) (d : AssetData) (m : Option MintData),
    cfg.thisChain ≠ 0 → s ≠ cfg.ntv →
    w.router.handler (enc c₀ s d) ≠ 0 → w.router.handler (enc c₀ s d) ≠ cfg.ntv →
    NativeTokenVault.ReachLog (ntvId enc cfg) cfg.thisChain NativeTokenVault.empty
      ⟨w.vault, audit⟩ log →
    (∀ p ∈ NativeTokenVault.registeredPairs cfg.thisChain log,
      IdInjOn enc {(c₀, s, d), (p.1, cfg.ntv, p.2)}) →
    (∀ md, m = some md → ∀ c, cfg.tokenOrigin md.metadata = some c →
      IdInjOn enc {(c₀, s, d), (c, cfg.ntv, NativeTokenVaultBase.widen md.originToken)}) →
      burnHandler cfg w.router (enc c₀ s d) ≠ cfg.ntv
      ∧ recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src (enc c₀ s d) m) = none

/-! ## One such call blocks the whole bundle, permanently -/

/-- **COMPOSED WITH `revert_anywhere_blocks`.**  Wherever in the bundle the unknown-asset call
sits, and whatever the other calls' outcomes, the claim is not accepted. -/
def Properties.UnknownAssetOutcomeBlocksClaim : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src : Chain) (a : AssetId) (m : Option MintData) (pre post : List Outcome),
    VaultUnaware cfg w.vault a → FailsAssetIdCheck enc cfg a m →
      ¬ ClaimAccepted
        (pre ++ outcomeOf (recoverAtomicCall enc cfg hk w cfg.manager dest
          (.finalizeDeposit src a m)) :: post)

/-- **THE REFUND LOOP, STATEFULLY.**  If the vault does not know `a`, the bundle has a router call
on `a`, every router call on `a` fails `assetIdCheck`, and the other targets leave `a`'s registry
entry alone, then `claimRefund` reverts — on the state the earlier calls actually leave, for any
leg state and any behaviour of the other targets. -/
def Properties.ClaimRevertsWithUnknownAssetCall : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (st : LegState) (calls : List Call) (a : AssetId),
    VaultUnaware cfg w.vault a → OthersLeaveAlone a other →
    HasRouterCallOn cfg a calls → RouterCallsOnFail enc cfg a calls →
      claimRefund (recoverCall enc cfg hk other dest) st w calls = none

/-- **A SUCCESSFUL REFUND OF ANOTHER ASSET LEAVES `a` ALONE.**  A `recoverAtomicCall` that returns,
on data that is not a `finalizeDeposit` on `a`, does not touch `a`'s registry entry. -/
def Properties.RefundOfOtherAssetLeavesAlone : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w w' : World X)
    (caller : Address) (dest : Chain) (d : CallData) (b : Bool) (a : AssetId),
    (∀ src m, d ≠ .finalizeDeposit src a m) →
    recoverAtomicCall enc cfg hk w caller dest d = some (w', b) →
      LeavesAlone a w.vault w'.vault

/-- **…AND SO DOES ANY OTHER LEG'S SUCCESSFUL CLAIM** whose bundle has no router call on `a`. -/
def Properties.OtherClaimLeavesAlone : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w w' : World X) (st st' : LegState) (calls : List Call) (a : AssetId),
    OthersLeaveAlone a other → ¬ HasRouterCallOn cfg a calls →
    claimRefund (recoverCall enc cfg hk other dest) st w calls = some (st', w') →
      LeavesAlone a w.vault w'.vault

/-- **THE LEG IS NEVER REFUNDED.**  In every world reachable by any number of steps that leave
`a`'s registry entry alone — registry steps hashing other ids (`VaultStepLeavesAlone`), other
legs' refunds (`OtherClaimLeavesAlone`), and any change to the router's maps, the pause flag or
the rest of the world — the claim still reverts, so the leg stays `Revertable` and none of the
bundle's calls, including its vault-asset calls, is ever refunded. -/
def Properties.LegNeverRefunded : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w w' : World X) (calls : List Call) (a : AssetId),
    VaultUnaware cfg w.vault a → OthersLeaveAlone a other →
    HasRouterCallOn cfg a calls → RouterCallsOnFail enc cfg a calls →
    Relation.ReflTransGen (fun u v : World X => LeavesAlone a u.vault v.vault) w w' →
      claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w' calls = none

/-- **HEADLINE (b): A BUNDLE WITH A CUSTOM-HANDLER DEPOSIT IS NEVER REFUNDED.**  In every world
whose vault registry is the end of a logged registry run from fresh storage — every registry
state the model reaches — the claim of any bundle containing a router call on a custom asset
`enc c₀ s d` (`s` not the vault) reverts.  Premises: `encodeAssetId` injective on the custom
triple paired with each logged pair and with the pair decoded from each of the bundle's router
calls on that asset, and other targets that leave its registry entry alone.  So the leg stays
`Revertable`, and none of its calls — vault-asset calls included — is ever refunded. -/
def Properties.CustomHandlerBundleNeverRefunded : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (log : List NativeTokenVault.Op) (audit : NativeTokenVault.Audit)
    (calls : List Call) (c₀ : Chain) (s : Address) (d : AssetData),
    cfg.thisChain ≠ 0 → s ≠ cfg.ntv →
    NativeTokenVault.ReachLog (ntvId enc cfg) cfg.thisChain NativeTokenVault.empty
      ⟨w.vault, audit⟩ log →
    (∀ p ∈ NativeTokenVault.registeredPairs cfg.thisChain log,
      IdInjOn enc {(c₀, s, d), (p.1, cfg.ntv, p.2)}) →
    OthersLeaveAlone (enc c₀ s d) other → HasRouterCallOn cfg (enc c₀ s d) calls →
    (∀ c ∈ calls, c.target = cfg.router → ∀ src m, c.data = .finalizeDeposit src (enc c₀ s d) m →
      ∀ md, m = some md → ∀ ch, cfg.tokenOrigin md.metadata = some ch →
        IdInjOn enc {(c₀, s, d), (ch, cfg.ntv, NativeTokenVaultBase.widen md.originToken)}) →
      claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w calls = none

/-- **ONLY THE MANAGER REACHES THE ROUTER'S REFUND** (`onlyAtomicFlowManager`,
`L2AssetRouter.sol:137-140, 284`). -/
def Properties.RecoveryOnlyByManager : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (caller : Address) (dest : Chain) (d : CallData),
    caller ≠ cfg.manager → recoverAtomicCall enc cfg hk w caller dest d = none

/-- **ONLY THE ROUTER REACHES THE VAULT'S REFUND** (`onlyAssetRouter`,
`NativeTokenVaultBase.sol:107-110, 217`).  With `RecoveryOnlyByManager` and the single call site
in `_recoverBundle` (`AtomicFlowManager.sol:225`), a bundle call's burn is refunded only inside a
successful `claimRefund` of its whole bundle. -/
def Properties.VaultRefundOnlyByRouter : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (caller : Address) (v : UInt256) (chainId : Chain) (a : AssetId) (m : Option MintData),
    caller ≠ cfg.router → ntvRecover enc cfg hk w caller v chainId a m = none

/-- **THE STATEFUL LOOP IS `RecoveryLimits`' ACCEPTANCE RULE.**  For any per-call behaviour, a
claim on a `Revertable` leg succeeds exactly when the outcomes the loop produces on the threaded
state satisfy `ClaimAccepted`: no call reverted and at least one recovered. -/
def Properties.ClaimSucceedsIffAccepted : Prop :=
  ∀ (X : Type) (step : World X → Call → Option (World X × Bool)) (w : World X) (calls : List Call),
    (claimRefund step LegState.Revertable w calls).isSome = true ↔ ClaimAccepted (outcomes step w calls)

/-! ## The positive side: router-produced calls on known assets refund the depositor -/

/-- **A KNOWN BRIDGED ASSET IS RE-MINTED TO `originalCaller`.**  For an asset the vault has a
token for and that is not native, unpaused, once the tracker hook returns: the refund is exactly
the token's `bridgeMint(originalCaller, amount)`, and returns `true` iff that mint does. -/
def Properties.KnownBridgedAssetRefundsOriginalCaller : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src : Chain) (a : AssetId) (md : MintData) (x₁ : X),
    w.paused = false → w.vault.originChain a ≠ cfg.thisChain → w.vault.token a ≠ 0 →
    hk.fromChain w.rest dest a md.amount = some x₁ →
      recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a (some md))
        = (hk.mint x₁ (w.vault.token a) md.originalCaller md.amount).map
            (fun x₂ => ({ w with rest := x₂ }, true))

/-- **A NATIVE ASSET IS UNLOCKED TO `originalCaller`.**  For an asset native to this chain: the
refund is exactly `_withdrawFunds(assetId, originalCaller, token, amount)`. -/
def Properties.NativeAssetRefundsOriginalCaller : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src : Chain) (a : AssetId) (md : MintData) (x₁ : X),
    w.paused = false → w.vault.originChain a = cfg.thisChain →
    hk.fromChain w.rest dest a md.amount = some x₁ →
      recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit src a (some md))
        = (hk.withdraw x₁ a md.originalCaller (w.vault.token a) md.amount).map
            (fun x₂ => ({ w with rest := x₂ }, true))

/-- **THE REMOTE RECEIVER IS IGNORED.**  Changing the mint data's `remoteReceiver` changes
nothing about the refund (`NativeTokenVaultBase.sol:219-230`). -/
def Properties.RefundIgnoresRemoteReceiver : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (caller : Address) (dest src : Chain) (a : AssetId) (md : MintData) (r : Addr160),
    recoverAtomicCall enc cfg hk w caller dest
        (.finalizeDeposit src a (some { md with remoteReceiver := r }))
      = recoverAtomicCall enc cfg hk w caller dest (.finalizeDeposit src a (some md))

/-- **HEADLINE (c): A BURN'S OWN BUNDLE CALL REFUNDS THE DEPOSITOR.**  The vault's preparation
(`bridgeBurn` on a registered representation token, `Contracts.NativeTokenVaultBase.prepare`)
returns mint data; the router's bundle call carrying it is refunded by re-minting exactly the
burned amount to the depositor `r.depositor`, not to the remote receiver — on a vault that knows
the asset, unpaused, once the tracker hook returns.  `routerCall` is the call the router really
produces only for a destination other than L1.  For an L1 destination the real call targets
`L1_ASSET_ROUTER` and its refund does not reach the router: see
`AtomicRecoveryFaithful.Properties.PreparedBurnRefundFailsToL1` and the case split
`AtomicRecoveryFaithful.Properties.PreparedBurnRefundByDestination`. -/
def Properties.PreparedBurnRefundsDepositor : Prop :=
  ∀ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc),
    NativeTokenVaultBase.WellFormed s → NativeTokenVaultBase.prepare prepHooks s r = some out →
    ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
      (other : Address → World X → Chain → CallData → Option (World X × Bool))
      (dest : Chain) (w : World X) (x₁ : X),
      w.paused = false → w.vault.originChain r.assetId ≠ cfg.thisChain →
      w.vault.token r.assetId ≠ 0 → hk.fromChain w.rest dest r.assetId r.data.amount = some x₁ →
        recoverCall enc cfg hk other dest w (routerCall cfg r.assetId out.data)
          = (hk.mint x₁ (w.vault.token r.assetId) r.depositor r.data.amount).map
              (fun x₂ => ({ w with rest := x₂ }, true))

/-! ## The refund cannot see where a call came from -/

/-- **THE REFUND IGNORES THE CALL'S SENDER AND VALUE.**  Two calls with the same target and data
are refunded identically, whoever sent them: a direct call that names the router with
router-shaped data is treated as a router-produced call. -/
def Properties.RefundIgnoresCallSender : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (c : Call) (sender : Address) (v : UInt256),
    recoverCall enc cfg hk other dest w { c with sender := sender, value := v }
      = recoverCall enc cfg hk other dest w c

/-- **A DIRECT CALL IS REFUNDED AS IF IT WERE A BURN.**  For an asset the vault knows (bridged,
unpaused, hooks returning), any account can put one direct call to the router into an atomic
bundle, with mint data of its choosing.  The bundle passes `_validateAtomicBundle`, and once the
leg is `Revertable` the claim succeeds by minting `md.amount` to `md.originalCaller` — although a
direct starter burns nothing at the source. -/
def Properties.DirectCallIsRefunded : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest src : Chain) (w : World X) (sender : Address) (a : AssetId) (md : MintData) (x₁ x₂ : X),
    w.paused = false → w.vault.originChain a ≠ cfg.thisChain → w.vault.token a ≠ 0 →
    hk.fromChain w.rest dest a md.amount = some x₁ →
    hk.mint x₁ (w.vault.token a) md.originalCaller md.amount = some x₂ →
      AtomicBundleValid [directCall cfg.router sender (.finalizeDeposit src a (some md))]
      ∧ claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w
          [directCall cfg.router sender (.finalizeDeposit src a (some md))]
        = some (LegState.Reverted, { w with rest := x₂ })

/-! ## Witnesses -/

/-- **`VaultRejectsUnknownAsset` FIRES AT THE CHECK.**  Its premises hold on a decodable call
whose every hook would succeed, so the revert is the vault's `assetIdCheck`, not a hook. -/
def Properties.VaultRejectsUnknownAssetSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X) (dest : Chain)
    (a : AssetId) (md : MintData) (c : Chain),
    VaultUnaware cfg w.vault a ∧ FailsAssetIdCheck enc cfg a (some md) ∧ w.paused = false
    ∧ cfg.tokenOrigin md.metadata = some c ∧ c ≠ cfg.thisChain
    ∧ (∀ x ch b amt, hk.fromChain x ch b amt ≠ none)
    ∧ (∀ x b ot ch, hk.deploy x b ot ch ≠ none)
    ∧ (∀ x tok rcv amt, hk.mint x tok rcv amt ≠ none)
    ∧ recoverAtomicCall enc cfg hk w cfg.manager dest (.finalizeDeposit 0 a (some md)) = none

/-- **THE HEADLINE'S PREMISES ARE JOINTLY SATISFIABLE**, on a vault that has registered an asset
and a decodable call whose hooks would all succeed. -/
def Properties.CustomHandlerDepositRefundRevertsSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (log : List NativeTokenVault.Op) (audit : NativeTokenVault.Audit)
    (c₀ : Chain) (s : Address) (d : AssetData) (md : MintData),
    cfg.thisChain ≠ 0 ∧ s ≠ cfg.ntv
    ∧ w.router.handler (enc c₀ s d) ≠ 0 ∧ w.router.handler (enc c₀ s d) ≠ cfg.ntv
    ∧ NativeTokenVault.ReachLog (ntvId enc cfg) cfg.thisChain NativeTokenVault.empty
        ⟨w.vault, audit⟩ log
    ∧ (NativeTokenVault.registeredPairs cfg.thisChain log).Nonempty
    ∧ (∀ p ∈ NativeTokenVault.registeredPairs cfg.thisChain log,
        IdInjOn enc {(c₀, s, d), (p.1, cfg.ntv, p.2)})
    ∧ (∀ c, cfg.tokenOrigin md.metadata = some c →
        IdInjOn enc {(c₀, s, d), (c, cfg.ntv, NativeTokenVaultBase.widen md.originToken)})
    ∧ (∃ c, cfg.tokenOrigin md.metadata = some c) ∧ w.paused = false
    ∧ (∀ x ch b amt, hk.fromChain x ch b amt ≠ none)
    ∧ (∀ x b ot ch, hk.deploy x b ot ch ≠ none)
    ∧ (∀ x tok rcv amt, hk.mint x tok rcv amt ≠ none)

/-- **THE FRAME LEMMAS' PREMISES ARE SATISFIABLE**, in one setting: a registry step hashing a
pair whose id is not `a` (`VaultStepLeavesAlone`), a successful refund of another asset
(`RefundOfOtherAssetLeavesAlone`), and another leg's successful claim with no router call on `a`
(`OtherClaimLeavesAlone`). -/
def Properties.FramePremisesSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (a : AssetId) (o : NativeTokenVault.Op)
    (W W' : NativeTokenVault.World) (d : CallData) (w' : World X) (b : Bool) (calls : List Call)
    (st' : LegState) (w'' : World X),
    (NativeTokenVault.StepOp (ntvId enc cfg) cfg.thisChain o W W'
      ∧ (∃ p, o.pair cfg.thisChain = some p)
      ∧ ∀ p, o.pair cfg.thisChain = some p → ntvId enc cfg p.1 p.2 ≠ a)
    ∧ ((∀ src m, d ≠ .finalizeDeposit src a m)
      ∧ recoverAtomicCall enc cfg hk w cfg.manager dest d = some (w', b))
    ∧ (OthersLeaveAlone a other ∧ ¬ HasRouterCallOn cfg a calls
      ∧ claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w calls
        = some (st', w''))

/-- **THE COLLISION DISJUNCT IS NEEDED.**  With an encoding under which a custom id equals the NTV
id of the pair in the data, the vault does not revert: it deploys and saves a bridged token for
the custom asset and mints to `originalCaller`. -/
def Properties.CollisionLetsVaultMintCustomAsset : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X) (dest src c₀ : Chain)
    (s : Address) (d : AssetData) (md : MintData),
    s ≠ cfg.ntv ∧ VaultUnaware cfg w.vault (enc c₀ s d)
    ∧ outcomeOf (recoverAtomicCall enc cfg hk w cfg.manager dest
        (.finalizeDeposit src (enc c₀ s d) (some md))) = Outcome.recovered

/-- **THE COLLISION DISJUNCT IS NOT A TAUTOLOGY.**  On a custom asset, decodable data whose pair
does not collide with the custom triple. -/
def Properties.CustomCollisionNotTautology : Prop :=
  ∃ (enc : AssetIdOf) (cfg : Config) (c₀ : Chain) (s : Address) (d : AssetData) (md : MintData)
    (c : Chain),
    s ≠ cfg.ntv ∧ cfg.tokenOrigin md.metadata = some c
    ∧ enc c₀ s d ≠ enc c cfg.ntv (NativeTokenVaultBase.widen md.originToken)

/-- **THE KNOWN-ASSET REFUND SUCCEEDS.**  The premises of `KnownBridgedAssetRefundsOriginalCaller`
hold with a mint that succeeds: the outcome is `recovered`. -/
def Properties.KnownAssetRefundSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src : Chain) (a : AssetId) (md : MintData) (x₁ : X),
    w.paused = false ∧ w.vault.originChain a ≠ cfg.thisChain ∧ w.vault.token a ≠ 0
    ∧ hk.fromChain w.rest dest a md.amount = some x₁
    ∧ outcomeOf (recoverAtomicCall enc cfg hk w cfg.manager dest
        (.finalizeDeposit src a (some md))) = Outcome.recovered

/-- **THE NATIVE-ASSET REFUND SUCCEEDS**, on the premises of `NativeAssetRefundsOriginalCaller`. -/
def Properties.NativeAssetRefundSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src : Chain) (a : AssetId) (md : MintData) (x₁ : X),
    w.paused = false ∧ w.vault.originChain a = cfg.thisChain
    ∧ hk.fromChain w.rest dest a md.amount = some x₁
    ∧ outcomeOf (recoverAtomicCall enc cfg hk w cfg.manager dest
        (.finalizeDeposit src a (some md))) = Outcome.recovered

/-- **`PreparedBurnRefundsDepositor`'S PREMISES ARE JOINTLY SATISFIABLE**, with a depositor who
is not the remote receiver and a refund that succeeds. -/
def Properties.PreparedBurnRefundSatisfiable : Prop :=
  ∃ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc)
    (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (x₁ : X),
    NativeTokenVaultBase.WellFormed s ∧ NativeTokenVaultBase.prepare prepHooks s r = some out
    ∧ r.depositor ≠ r.data.receiver
    ∧ w.paused = false ∧ w.vault.originChain r.assetId ≠ cfg.thisChain
    ∧ w.vault.token r.assetId ≠ 0 ∧ hk.fromChain w.rest dest r.assetId r.data.amount = some x₁
    ∧ outcomeOf (recoverCall enc cfg hk other dest w (routerCall cfg r.assetId out.data))
        = Outcome.recovered

/-- **THE STATEFUL BLOCKING PREMISES ARE JOINTLY SATISFIABLE**, on a two-call bundle whose other
call is a router call on a known asset that would be refunded on its own. -/
def Properties.ClaimRevertsWithUnknownAssetCallSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (calls : List Call) (a : AssetId),
    VaultUnaware cfg w.vault a ∧ OthersLeaveAlone a other
    ∧ HasRouterCallOn cfg a calls ∧ RouterCallsOnFail enc cfg a calls
    ∧ calls.length = 2
    ∧ (∃ c ∈ calls, (claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w [c]).isSome)

/-- **HEADLINE (b)'S PREMISES ARE JOINTLY SATISFIABLE**, on a vault that has registered an
asset, a bundle of a custom-asset call and a vault-asset call whose vault-asset call would be
refunded on its own, and other targets that return. -/
def Properties.CustomHandlerBundleNeverRefundedSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (log : List NativeTokenVault.Op) (audit : NativeTokenVault.Audit)
    (calls : List Call) (c₀ : Chain) (s : Address) (d : AssetData),
    cfg.thisChain ≠ 0 ∧ s ≠ cfg.ntv
    ∧ NativeTokenVault.ReachLog (ntvId enc cfg) cfg.thisChain NativeTokenVault.empty
        ⟨w.vault, audit⟩ log
    ∧ (NativeTokenVault.registeredPairs cfg.thisChain log).Nonempty
    ∧ (∀ p ∈ NativeTokenVault.registeredPairs cfg.thisChain log,
        IdInjOn enc {(c₀, s, d), (p.1, cfg.ntv, p.2)})
    ∧ OthersLeaveAlone (enc c₀ s d) other
    ∧ (∀ target u dest' d', ∃ r, other target u dest' d' = some r)
    ∧ HasRouterCallOn cfg (enc c₀ s d) calls
    ∧ (∀ c ∈ calls, c.target = cfg.router → ∀ src m,
        c.data = .finalizeDeposit src (enc c₀ s d) m →
        ∀ md, m = some md → ∀ ch, cfg.tokenOrigin md.metadata = some ch →
          IdInjOn enc {(c₀, s, d), (ch, cfg.ntv, NativeTokenVaultBase.widen md.originToken)})
    ∧ (∃ c ∈ calls,
        (claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w [c]).isSome)

/-- **HEADLINE (b), CONCRETE: AN ADMITTED BUNDLE IS STRANDED.**  One world and one atomic bundle
of two router-produced calls with zero value (so `_validateAtomicBundle` admits it): a deposit of
a custom-handler asset, burned by its handler, and a deposit of a vault asset, burned by the
vault.  The vault-asset call alone would be refunded, but the bundle's claim reverts in every
world reachable by steps that leave the custom asset's registry entry alone. -/
def Properties.CustomHandlerBundleIsStranded : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : Config) (hk : Hooks X)
    (other : Address → World X → Chain → CallData → Option (World X × Bool))
    (dest : Chain) (w : World X) (aCustom aVault : AssetId) (mdCustom mdVault : MintData),
    AtomicBundleValid [routerCall cfg aCustom mdCustom, routerCall cfg aVault mdVault]
    ∧ burnHandler cfg w.router aCustom ≠ cfg.ntv ∧ burnHandler cfg w.router aVault = cfg.ntv
    ∧ (claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w
        [routerCall cfg aVault mdVault]).isSome
    ∧ ∀ w', Relation.ReflTransGen (fun u v : World X => LeavesAlone aCustom u.vault v.vault) w w' →
        claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w'
          [routerCall cfg aCustom mdCustom, routerCall cfg aVault mdVault] = none

/-- **HEADLINE (c'), CONCRETE: A DIRECT CALL MINTS UNBACKED TOKENS.**  The rest of the world is
the bridged token's ledger.  A bundle of one direct call by `attacker` to the router — no
router-produced call, nothing burned — passes `_validateAtomicBundle`, and its claim raises the
attacker's balance from `0` to a positive amount. -/
def Properties.DirectCallMintsUnbacked : Prop :=
  ∃ (enc : AssetIdOf) (cfg : Config) (hk : Hooks (Addr160 → ℕ))
    (other : Address → World (Addr160 → ℕ) → Chain → CallData → Option (World (Addr160 → ℕ) × Bool))
    (dest src : Chain) (w : World (Addr160 → ℕ)) (attacker : Address) (a : AssetId)
    (md : MintData) (w' : World (Addr160 → ℕ)),
    attacker ≠ cfg.router ∧ AtomicBundleValid [directCall cfg.router attacker (.finalizeDeposit src a (some md))]
    ∧ claimRefund (recoverCall enc cfg hk other dest) LegState.Revertable w
        [directCall cfg.router attacker (.finalizeDeposit src a (some md))]
      = some (LegState.Reverted, w')
    ∧ w.rest md.originalCaller = 0 ∧ 0 < w'.rest md.originalCaller

end Contracts.AssetRouter.AtomicRecovery
