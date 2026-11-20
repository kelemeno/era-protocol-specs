import EraSpec.Core.Headline
import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecoveryAtHead
import EraSpec.Contracts.NativeTokenVaultBase.Specs.RepresentationPreparation

/-!
# Properties: atomic recovery at head — forged refunds and the custom-handler lock are gone

Statements about `EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecoveryAtHead` (era-contracts
`draft/v0.35.0` `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`).  Proofs are in
`EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecoveryAtHead`.

The pin model (`AtomicRecovery`, `c67894b9`) found that the refund always went to the vault and
that a direct call was refunded like a burn.  At head:

* **(a) The forged refund is gone.**  The manager dispatches on `InteropCall.from`, so a direct call
  never reaches `recoverAtomicCall`: its iteration is the vault's refund of the call's own value, in
  the bundle's destination base-token asset, to the call's own sender, or nothing when the value is
  zero (`DirectCallSkipsRouterRecovery`, `DirectCallDataIgnoredAtHead`, `CallTargetIgnoredAtHead`,
  `DirectValueLegRefundsItsSenderAtHead`; through the pin's vault refund when that asset is not this
  chain's base token, `CrossBaseValueLegRefundAtHead`, and through the base-token holder when it is,
  `SameBaseValueLegRefundAtHead`).  A bundle of zero-value direct calls is claimed as a no-op
  (headline `DirectBundleClaimIsNoOpAtHead`).  On the send side, for a sender other than the router,
  only indirect starters yield calls from the router (`RouterSenderIffIndirectAtHead`,
  `SentDirectCallNeverRecoveredAtHead`).  The pin's countermodel instance is rejected
  (`PinUnbackedMintRejectedAtHead`) and the pin's statement is false of the head
  (`DirectCallIsRefundedFailsAtHead`).
* **(b) The custom-handler lock is gone, while the handler is not rotated.**  The vault's own refund
  is the pin's except on this chain's base token (`VaultRecoverAtHeadIsPinRefundOffBaseToken`,
  `VaultRecoverAtHeadOnBaseToken`), so while the vault handles an asset a router call's head
  iteration is the pin's (`VaultRouterCallIsPinIterationAtHead`).  The refund reads the handler at
  claim time (`RecoveryReadsClaimTimeHandler`); the burn leaves its own handler registered
  (`BurnLeavesBurnHandler`); a run of the router-map writers that rotates nothing leaves it there
  (`NoRotationKeepsHandler`, logged-hash form `NoRotationKeepsHandlerLoggedOn`; conversely
  `HandlerMovesOnlyByRotation`).  So a router leg's refund is the burn handler's own refund, on the
  burn's own bytes (headline `RouterLegReachesBurnHandler`, logged form
  `RouterLegReachesBurnHandlerLoggedOn`).  The refund of a custom-handler deposit is that handler's
  refund, with no hash premise (`CustomHandlerRecoveredByItsHandler`); a vault burn's call re-mints
  the burned amount to its depositor while the vault is still its handler
  (`PreparedBurnRefundsDepositorAtHead`), in particular after any run of the writers that does not
  rotate the asset (`VaultBurnRefundsDepositorAfterRunAtHead`); the pin's stranded bundle is refunded
  (`PinStrandedBundleRefundedAtHead`); and the pin's `RecoveryCallsTheVault` and
  `RecoveryIgnoresHandler` are false of the head (`…FailsAtHead`).
* **(c) Rotation misroutes recovery** (upstream known issue 5).  Rotating to a handler that no-ops
  consumes the leg with nothing refunded (headline `RotationToNoOpHandlerStrandsBurn`); rotating to one
  that reverts blocks the claim until rotated back (`RotationToRevertingHandlerBlocksClaim`); a zeroed
  handler reverts (`ZeroedHandlerRecoveryReverts`).  On L2, along runs from fresh storage, only the L1
  counterpart, the initializer and the vault's own registration rotate a live route
  (`L2RotationOnlyByCounterpartSeedOrVault`).
* **(d) One failing recovery still blocks the whole bundle: the revert is still uncaught.**  The head
  acceptance rule is `RecoveryLimits.LoopCompletes` alone (`ClaimSucceedsIffLoopCompletesAtHead`):
  any revert blocks the claim (headline `RevertingCallBlocksClaimAtHead`, on the head loop
  `UnrecoverableHandlerBlocksBundleAtHead`, concrete `HandlerWithoutRecoveryStrandsBundleAtHead`), while
  a claim that recovers nothing consumes the leg (`NothingRecoveredStillConsumesLegAtHead`,
  `UnrecognisedRouterCallConsumedAtHead`, and against the pin `PinRejectsNothingRecoverableHeadAccepts`).
* **(e) An L1 destination is refused at claim time**, in every leg state, world and per-call
  behaviour (`L1DestinationClaimRevertsAtHead`).  The pin's stranded L1 leg
  (`AtomicRecoveryFaithful.AdmittedAtomicL1LegNeverRefunded`) needs an atomic bundle to L1, which
  `_sendBundle` rejects at head (`InteropCenter.sol:552-553`; the send is not modelled here).

No statement takes a global hash premise.  The only hash premises are in the two `…LoggedOn` forms:
injectivity of `encodeAssetId` on the burned asset's registration triple paired with each triple the
run between burn and claim hashes.  The configuration identifications of the Specs header (one
`L1_CHAIN_ID`, one `BASE_TOKEN_ASSET_ID`, `OPS-CONFIG`) are model boundaries, not premises.  Every
property with premises has a satisfiability witness below.

Scope.  These are statements about the claim side.  What was collected at send — the burn behind an
indirect starter (`AssetRouterBase._burn`), the value collected by `_ensureCorrectTotalValue` — enters
only as the premises a statement names (`burnRouter`, `burnHandler`, the prepared mint data); the
send-side collection of call value is not modelled.  The leg is taken as `Revertable`: how it got
there (`authorizeRefund` and its proofs) is the subject of the `InteropAtomicity` models.
-/

namespace Contracts.AssetRouter.AtomicRecoveryAtHead

open AttackVectors.RecoveryLimits (Outcome LegState LoopCompletes claimEnabled)

/-! ## (a) Direct calls never reach the router's refund -/

/-- **A DIRECT CALL NEVER REACHES THE ROUTER'S REFUND.**  For a call whose `InteropCall.from` is not
the router, the loop's iteration is the router's `bridgehubRecoverBaseToken` of the call's own value,
in the bundle's destination base-token asset, to the call's own sender, or nothing at all when the
value is zero (`AtomicFlowManager.sol:312-323`).  `recoverAtomicCall` is not called, and the call's
`data` does not occur on the right-hand side: whatever `finalizeDeposit` data a direct call carries, no
handler sees it. -/
def Properties.DirectCallSkipsRouterRecovery : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X) (c : HeadCall),
    c.sender ≠ cfg.router →
      recoverCallAtHead enc cfg hk code dest base w c
        = if c.value = 0 then some (w, false)
          else (bridgehubRecoverBaseTokenAtHead enc cfg hk w cfg.manager dest base c.sender
            c.value).map (fun w' => (w', true))

/-- **A DIRECT CALL'S TARGET AND DATA ARE IGNORED**, and so is every handler's code: replacing them
changes nothing about the call's iteration. -/
def Properties.DirectCallDataIgnoredAtHead : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code code' : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X) (c : HeadCall)
    (target : Address) (d : HeadCallData),
    c.sender ≠ cfg.router →
      recoverCallAtHead enc cfg hk code' dest base w { c with target := target, data := d }
        = recoverCallAtHead enc cfg hk code dest base w c

/-- **A DIRECT VALUE LEG REFUNDS ITS OWN VALUE TO ITS OWN SENDER.**  For a call not from the router
with value `v ≠ 0` and a destination other than L1, the iteration is exactly the vault's head
failed-transfer refund (`vaultRecoverAtHead`), called by the router with no value, of `v` of the
bundle's destination base-token asset, on the mint data `bridgehubRecoverBaseToken` rebuilds, whose
`originalCaller` is the call's sender (`baseRefundMint`).  The right-hand side reads no router map:
the refund goes to the vault whatever handler the asset has.  (At send, `_ensureCorrectTotalValue`,
`InteropCenter.sol:418-460`, collected the bundle's call values; the send is not modelled.)  The two
cases of the vault's refund are `CrossBaseValueLegRefundAtHead` and `SameBaseValueLegRefundAtHead`. -/
def Properties.DirectValueLegRefundsItsSenderAtHead : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X) (c : HeadCall),
    c.sender ≠ cfg.router → c.value ≠ 0 → dest ≠ cfg.l1Chain →
      recoverCallAtHead enc cfg hk code dest base w c
        = (vaultRecoverAtHead enc cfg hk w cfg.router 0 dest base
            (some (baseRefundMint c.sender c.value))).map (fun w' => (w', true))

/-- **…CROSS-BASE: THROUGH THE PIN'S VAULT REFUND.**  When the destination's base-token asset is not
this chain's base token, that refund is the pin model's `AtomicRecovery.ntvRecover` on the rebuilt
mint data, called by the router with no value: `ntvRecover` passes `v` and the mint data's
`originalCaller`, here the call's sender, to the vault's withdraw or mint hook (for a bridged asset it
has no token for, only after the asset-id check and a deployment). -/
def Properties.CrossBaseValueLegRefundAtHead : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X) (c : HeadCall),
    c.sender ≠ cfg.router → c.value ≠ 0 → dest ≠ cfg.l1Chain → base ≠ cfg.baseAsset →
      recoverCallAtHead enc cfg hk code dest base w c
        = (AtomicRecovery.ntvRecover enc cfg.toConfig hk.toHooks w cfg.router 0 dest base
            (some (baseRefundMint c.sender c.value))).map (fun w' => (w', true))

/-- **…SAME-BASE: THROUGH THE BASE-TOKEN HOLDER.**  When the destination's base-token asset is this
chain's base token, the vault is unpaused and does not record that asset as native to this chain, the
iteration is exactly `L2_BASE_TOKEN_HOLDER.recoverBaseToken(sender, v, dest)`
(`L2NativeTokenVault.sol:214-216`): the vault's registry is not written, and the tracker's
`_handleBridgeFromChain` and the token hooks play no part. -/
def Properties.SameBaseValueLegRefundAtHead : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (dest : Chain) (w : World X) (c : HeadCall),
    c.sender ≠ cfg.router → c.value ≠ 0 → dest ≠ cfg.l1Chain →
    w.paused = false → w.vault.originChain cfg.baseAsset ≠ cfg.thisChain →
      recoverCallAtHead enc cfg hk code dest cfg.baseAsset w c
        = (hk.recoverBase w.rest (narrow c.sender) c.value dest).map
            (fun x => ({ w with rest := x }, true))

/-- **NO CALL'S TARGET IS READ.**  For every call, router-produced or direct, replacing
`InteropCall.to` changes nothing about its iteration (`AtomicFlowManager.sol:302-324` reads `from`,
`value` and `data` only). -/
def Properties.CallTargetIgnoredAtHead : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X) (c : HeadCall)
    (target : Address),
    recoverCallAtHead enc cfg hk code dest base w { c with target := target }
      = recoverCallAtHead enc cfg hk code dest base w c

/-- **HEADLINE (a): A BUNDLE OF ZERO-VALUE DIRECT CALLS IS CLAIMED AS A NO-OP.**  For every world,
vault hooks and handler code: if no call of the bundle is from the router and none carries value, the
claim of a `Revertable` leg with a non-L1 destination succeeds, marks the leg `Reverted`, and leaves
the world exactly as it was — no mint and no unlock, whatever `finalizeDeposit` data the calls carry.
The pin's forged refund (`AtomicRecovery.History.DirectCallIsRefunded`, `DirectCallMintsUnbacked`) is a
bundle of this kind.

Premises: a non-L1 destination; no call of the bundle is from the router and none carries value.
No hash premise. Model boundary (`MODEL-ATOMIC-RECOVERY-HEAD`): call and mint data are typed (`SOL-ABI`); the
router's, manager's and tracker's `L1_CHAIN_ID` slots are one value and the vault's and tracker's
`BASE_TOKEN_ASSET_ID` slots another (`OPS-CONFIG`); the vault's hooks and the base-token holder
write only the rest of the world (`DEP-FRAME`); the code at every handler other than the vault
is arbitrary (`HandlerCode`); `nonReentrant`, events and the bundle decoding are omitted. -/
@[headline] def Properties.DirectBundleClaimIsNoOpAtHead : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (w : World X) (b : HeadBundle),
    b.destChain ≠ cfg.l1Chain → (∀ c ∈ b.calls, c.sender ≠ cfg.router ∧ c.value = 0) →
      claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w b
        = some (LegState.Reverted, w)

/-- **ONLY INDIRECT STARTERS PRODUCE CALLS FROM THE ROUTER.**  For a send by any account other than
the router, a processed call is from the router exactly when its starter was indirect, and then it is
the router-produced call carrying that starter's burn. -/
def Properties.RouterSenderIffIndirectAtHead : Prop :=
  ∀ (cfg : HeadConfig) (msgSender : Address) (st : HeadStarter), msgSender ≠ cfg.router →
    ((processCallStarterAtHead cfg msgSender st).sender = cfg.router
      ↔ ∃ a mintBytes, st = .indirect a mintBytes
          ∧ processCallStarterAtHead cfg msgSender st = routerCallAtHead cfg a mintBytes)

/-- **A SENT DIRECT CALL IS NEVER RECOVERED THROUGH THE ROUTER.**  For a send by any account other
than the router, the claim-time iteration of the call a direct starter produced is
`bridgehubRecoverBaseToken` of the starter's own value to that account, or nothing when the value is
zero — for every recipient and payload, the router and router-shaped `finalizeDeposit` data
included. -/
def Properties.SentDirectCallNeverRecoveredAtHead : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X) (msgSender : Address)
    (recipient : Address) (d : HeadCallData) (v : UInt256),
    msgSender ≠ cfg.router →
      recoverCallAtHead enc cfg hk code dest base w
          (processCallStarterAtHead cfg msgSender (.direct recipient d v))
        = if v = 0 then some (w, false)
          else (bridgehubRecoverBaseTokenAtHead enc cfg hk w cfg.manager dest base msgSender v).map
            (fun w' => (w', true))

/-- **THE PIN'S UNBACKED-MINT INSTANCE IS REJECTED AT HEAD.**  One world, one ledger, one attacker.
In the PIN model the claim of the attacker's direct call raises the balance of the `originalCaller`
named in the attacker-written data from `0` to a positive amount (the countermodel
`AtomicRecovery.History.DirectCallMintsUnbacked`).  In the HEAD model the claim of the same call — same
target, sender and zero value, `finalizeDeposit` bytes that decode to the same mint data — succeeds
and leaves the world as it was, so that balance stays `0`. -/
def Properties.PinUnbackedMintRejectedAtHead : Prop :=
  ∃ (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks (Addr160 → ℕ))
    (other : Address → World (Addr160 → ℕ) → Chain → AtomicRecovery.CallData →
      Option (World (Addr160 → ℕ) × Bool))
    (code : HandlerCode (Addr160 → ℕ)) (dest src : Chain) (base : AssetId)
    (w w' : World (Addr160 → ℕ)) (attacker : Address) (a : AssetId) (md : MintData) (data : Bytes),
    attacker ≠ cfg.router ∧ cfg.decodeMint data = some md ∧ dest ≠ cfg.l1Chain
    ∧ AtomicRecovery.claimRefund (AtomicRecovery.recoverCall enc cfg.toConfig hk.toHooks other dest)
        LegState.Revertable w
        [AtomicRecovery.directCall cfg.router attacker (.finalizeDeposit src a (some md))]
      = some (LegState.Reverted, w')
    ∧ w.rest md.originalCaller = 0 ∧ 0 < w'.rest md.originalCaller
    ∧ claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w
        ⟨dest, base, [directCallAtHead cfg.router attacker 0 (.finalizeDeposit src a data)]⟩
      = some (LegState.Reverted, w)

/-- **THE PIN'S `DirectCallIsRefunded` IS FALSE AT HEAD.**  Its head form — under the pin's premises,
a zero-value direct call to the router with `finalizeDeposit` data on a known bridged asset is
refunded by minting the data's amount to the data's `originalCaller` — does not hold of the head
model.  (A negative result: no witness.) -/
def Properties.DirectCallIsRefundedFailsAtHead : Prop :=
  ¬ ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
      (code : HandlerCode X) (dest src : Chain) (base : AssetId) (w : World X) (sender : Address)
      (a : AssetId) (data : Bytes) (md : MintData) (x₁ x₂ : X),
      sender ≠ cfg.router → dest ≠ cfg.l1Chain → cfg.decodeMint data = some md →
      w.paused = false → w.vault.originChain a ≠ cfg.thisChain → w.vault.token a ≠ 0 →
      hk.fromChain w.rest dest a md.amount = some x₁ →
      hk.mint x₁ (w.vault.token a) md.originalCaller md.amount = some x₂ →
        claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w
            ⟨dest, base, [directCallAtHead cfg.router sender 0 (.finalizeDeposit src a data)]⟩
          = some (LegState.Reverted, { w with rest := x₂ })

/-! ## (b) A router leg's refund reaches the handler that burned it -/

/-- **OFF THE CHAIN'S OWN BASE TOKEN, THE VAULT'S HEAD REFUND IS THE PIN'S.**  For every asset other
than this chain's `BASE_TOKEN_ASSET_ID` and every destination other than L1, the head vault's
`bridgeRecoverFailedTransfer` is the pin model's `AtomicRecovery.ntvRecover` on the pin hooks, for
every caller, value and mint data (decode failures included).  So every statement about
`ntvRecover` holds of the head refund of those assets to those destinations. -/
def Properties.VaultRecoverAtHeadIsPinRefundOffBaseToken : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X) (w : World X)
    (caller : Address) (v : UInt256) (chainId : Chain) (a : AssetId) (m : Option MintData),
    chainId ≠ cfg.l1Chain → a ≠ cfg.baseAsset →
      vaultRecoverAtHead enc cfg hk w caller v chainId a m
        = AtomicRecovery.ntvRecover enc cfg.toConfig hk.toHooks w caller v chainId a m

/-- **ON THE CHAIN'S OWN BASE TOKEN, THE VAULT'S HEAD REFUND IS THE BASE-TOKEN HOLDER'S.**  Called by
the router with no value, unpaused, for a destination other than L1: if the vault records the base
token as native to this chain the refund reverts (`BaseTokenNativeToThisChain`,
`L2AssetTracker.sol:182-184`); otherwise it is exactly `recoverBaseToken(originalCaller, amount,
chainId)`.  The registry is not written. -/
def Properties.VaultRecoverAtHeadOnBaseToken : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X) (w : World X)
    (chainId : Chain) (md : MintData),
    chainId ≠ cfg.l1Chain → w.paused = false →
      vaultRecoverAtHead enc cfg hk w cfg.router 0 chainId cfg.baseAsset (some md)
        = if w.vault.originChain cfg.baseAsset = cfg.thisChain then none
          else (hk.recoverBase w.rest md.originalCaller md.amount chainId).map
            (fun x => { w with rest := x })

/-- **WHILE THE VAULT HANDLES THE ASSET, A ROUTER CALL'S HEAD ITERATION IS THE PIN'S.**  For a
router-produced call on an asset other than this chain's base token, to a destination other than L1,
whose claim-time handler is the vault (at a nonzero address) and whose bytes the vault decodes to `md`:
the head iteration equals the pin model's iteration (`AtomicRecovery.recoverCall`, for every behaviour
`other` of non-router targets) on the pin's router call `AtomicRecovery.routerCall cfg a md`.  So the
pin model's results about that call (`KnownBridgedAssetRefundsOriginalCaller`,
`NativeAssetRefundsOriginalCaller`, `RefundIgnoresRemoteReceiver`) hold of it at head. -/
def Properties.VaultRouterCallIsPinIterationAtHead : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X) (code : HandlerCode X)
    (other : Address → World X → Chain → AtomicRecovery.CallData → Option (World X × Bool))
    (dest : Chain) (base : AssetId) (w : World X) (a : AssetId) (mintBytes : Bytes) (md : MintData),
    dest ≠ cfg.l1Chain → a ≠ cfg.baseAsset → cfg.ntv ≠ 0 → w.router.handler a = cfg.ntv →
    cfg.decodeMint mintBytes = some md →
      recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg a mintBytes)
        = AtomicRecovery.recoverCall enc cfg.toConfig hk.toHooks other dest w
            (AtomicRecovery.routerCall cfg.toConfig a md)

/-- **THE REFUND READS THE HANDLER AT CLAIM TIME.**  The manager's `recoverAtomicCall` on
`finalizeDeposit` data, for a non-L1 destination: an unset handler reverts
(`AssetHandlerDoesNotExist`), and otherwise the refund is exactly the claim-time handler's
`bridgeRecoverFailedTransfer` on the call's own destination, asset and bytes, then `return true`
(`L2AssetRouter.sol:299-302`). -/
def Properties.RecoveryReadsClaimTimeHandler : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (w : World X) (dest src : Chain) (a : AssetId) (data : Bytes),
    dest ≠ cfg.l1Chain →
      recoverAtomicCallAtHead enc cfg hk code w cfg.manager dest (.finalizeDeposit src a data)
        = if w.router.handler a = 0 then none
          else (handlerRecover enc cfg hk code (w.router.handler a) w dest a data).map
            (fun w' => (w', true))

/-- **THE BURN LEAVES ITS OWN HANDLER REGISTERED.**  After `_burn` of asset `a`, the handler at `a`
is the one `bridgeBurn` ran on (`AtomicRecovery.burnHandler`).  No premise. -/
def Properties.BurnLeavesBurnHandler : Prop :=
  ∀ (cfg : AtomicRecovery.Config) (R : Router) (a : AssetId),
    (burnRouter cfg R a).handler a = AtomicRecovery.burnHandler cfg R a

/-- **…AND THAT HANDLER IS SET,** whenever the vault's address is nonzero. -/
def Properties.BurnHandlerNonzero : Prop :=
  ∀ (cfg : AtomicRecovery.Config) (R : Router) (a : AssetId),
    cfg.ntv ≠ 0 → AtomicRecovery.burnHandler cfg R a ≠ 0

/-- **NO ROTATION, NO MOVE.**  Along any run of the router-map writers (`AllWriters.ARun`) from maps
whose handler at `a` is `h₀ ≠ 0`, if no call of the run rotates `a` away from `h₀` (`NoRotation`), the
handler at `a` is still `h₀` at the end.  No hash premise: `Rotates` is about the ids the calls
actually write. -/
def Properties.NoRotationKeepsHandler : Prop :=
  ∀ (K : AllWriters.Cfg) (R₁ R₂ : Router) (ops : List AllWriters.Op) (a : AssetId) (h₀ : Address),
    AllWriters.ARun K R₁ ops R₂ → R₁.handler a = h₀ → h₀ ≠ 0 → NoRotation K a h₀ ops →
      R₂.handler a = h₀

/-- **A LIVE HANDLER MOVES ONLY BY A ROTATION.**  Conversely: if one call of the writers changes the
handler of `a` from a nonzero value, that call rotates `a` away from it. -/
def Properties.HandlerMovesOnlyByRotation : Prop :=
  ∀ (K : AllWriters.Cfg) (op : AllWriters.Op) (R R' : Router) (a : AssetId),
    AllWriters.AStep K op R R' → R'.handler a ≠ R.handler a → R.handler a ≠ 0 →
      Rotates K a (R.handler a) op

/-- **NO ROTATION, UNDER LOGGED HASH PREMISES.**  Let the asset be `K.enc c₀ s₀ d₀`, its
registration triple `(c₀, s₀, d₀)`.  Along any run from maps whose handler at it is `h₀ ≠ 0`, the
handler is still `h₀` at the end, provided

* `encodeAssetId` is injective on that triple paired with each triple a call of the run hashes
  (`AllWriters.Op.triple`; at most one per call, `AllWriters.LoggedTriplesCardLe`);
* a registration hashing that very triple (its tracker's re-registration) writes `h₀`;
* a counterpart write naming the asset writes `h₀`;
* the seed, if the run has one and the seeded id is the asset, writes `h₀`. -/
def Properties.NoRotationKeepsHandlerLoggedOn : Prop :=
  ∀ (K : AllWriters.Cfg) (R₁ R₂ : Router) (ops : List AllWriters.Op) (c₀ : Chain) (s₀ : Address)
    (d₀ : AssetData) (h₀ : Address),
    AllWriters.ARun K R₁ ops R₂ → R₁.handler (K.enc c₀ s₀ d₀) = h₀ → h₀ ≠ 0 →
    (∀ op ∈ ops, ∀ p, op.triple K = some p → IdInjOn K.enc {(c₀, s₀, d₀), p}) →
    (∀ caller d h, AllWriters.Op.register caller d h ∈ ops →
      (K.thisChain, senderOf K.ntv K.ntvAddr caller, d) = (c₀, s₀, d₀) → h = h₀) →
    (∀ a' h, AllWriters.Op.counterpartSet a' h ∈ ops → a' = K.enc c₀ s₀ d₀ → h = h₀) →
    (AllWriters.Op.seed ∈ ops → K.seedId = K.enc c₀ s₀ d₀ → K.ntv = h₀) →
      R₂.handler (K.enc c₀ s₀ d₀) = h₀

/-- **HEADLINE (b): A ROUTER LEG'S REFUND REACHES THE HANDLER THAT BURNED IT, IF NOT ROTATED.**  The
burn of asset `a` ran in router maps `R`, on the handler `burnHandler cfg R a`, and its bundle call is
the router-produced `routerCallAtHead cfg a mintBytes`.  Between the burn and the claim the maps
evolve by any run of the writers, for any writers' configuration `K` (in particular this router's),
from `burnRouter cfg R a` to the claim-time maps, and no call of the run rotates `a` away from the
burn handler.  Then, for a non-L1 destination and a nonzero vault address, the claim's iteration on
that call is exactly the burn handler's `bridgeRecoverFailedTransfer` (`handlerRecover`) on the call's
destination, the asset and the burn's own bytes, followed by `return true`.

Premises: a non-L1 destination; a nonzero vault address; between burn and claim the router maps
evolve only by a run of the map writers (`AllWriters`) from the post-burn maps, with no call that
rotates `a` away from the burn handler.  No hash premise. Model boundary (`MODEL-ATOMIC-RECOVERY-HEAD`): call and mint data are typed (`SOL-ABI`); the
router's, manager's and tracker's `L1_CHAIN_ID` slots are one value and the vault's and tracker's
`BASE_TOKEN_ASSET_ID` slots another (`OPS-CONFIG`); the vault's hooks and the base-token holder
write only the rest of the world (`DEP-FRAME`); the code at every handler other than the vault
is arbitrary (`HandlerCode`); `nonReentrant`, events and the bundle decoding are omitted. -/
@[headline] def Properties.RouterLegReachesBurnHandler : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (K : AllWriters.Cfg) (R : Router) (ops : List AllWriters.Op)
    (w : World X) (dest : Chain) (base : AssetId) (a : AssetId) (mintBytes : Bytes),
    dest ≠ cfg.l1Chain → cfg.ntv ≠ 0 →
    AllWriters.ARun K (burnRouter cfg.toConfig R a) ops w.router →
    NoRotation K a (AtomicRecovery.burnHandler cfg.toConfig R a) ops →
      recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg a mintBytes)
        = (handlerRecover enc cfg hk code (AtomicRecovery.burnHandler cfg.toConfig R a) w dest a
            mintBytes).map (fun w' => (w', true))

/-- **HEADLINE (b), LOGGED FORM.**  The same conclusion for the asset `K.enc c₀ s₀ d₀`, with the
rotation premise replaced by the logged premises of `NoRotationKeepsHandlerLoggedOn` for the burn
handler: injectivity of `encodeAssetId` on the asset's triple paired with each triple the run hashes,
and no re-registration, counterpart write or seed that writes another handler at the asset. -/
def Properties.RouterLegReachesBurnHandlerLoggedOn : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (K : AllWriters.Cfg) (R : Router) (ops : List AllWriters.Op)
    (w : World X) (dest : Chain) (base : AssetId) (c₀ : Chain) (s₀ : Address) (d₀ : AssetData)
    (mintBytes : Bytes),
    dest ≠ cfg.l1Chain → cfg.ntv ≠ 0 →
    AllWriters.ARun K (burnRouter cfg.toConfig R (K.enc c₀ s₀ d₀)) ops w.router →
    (∀ op ∈ ops, ∀ p, op.triple K = some p → IdInjOn K.enc {(c₀, s₀, d₀), p}) →
    (∀ caller d h, AllWriters.Op.register caller d h ∈ ops →
      (K.thisChain, senderOf K.ntv K.ntvAddr caller, d) = (c₀, s₀, d₀) →
        h = AtomicRecovery.burnHandler cfg.toConfig R (K.enc c₀ s₀ d₀)) →
    (∀ a' h, AllWriters.Op.counterpartSet a' h ∈ ops → a' = K.enc c₀ s₀ d₀ →
      h = AtomicRecovery.burnHandler cfg.toConfig R (K.enc c₀ s₀ d₀)) →
    (AllWriters.Op.seed ∈ ops → K.seedId = K.enc c₀ s₀ d₀ →
      K.ntv = AtomicRecovery.burnHandler cfg.toConfig R (K.enc c₀ s₀ d₀)) →
      recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg (K.enc c₀ s₀ d₀) mintBytes)
        = (handlerRecover enc cfg hk code (AtomicRecovery.burnHandler cfg.toConfig R (K.enc c₀ s₀ d₀))
            w dest (K.enc c₀ s₀ d₀) mintBytes).map (fun w' => (w', true))

/-- **THE CUSTOM-HANDLER LOCK IS GONE: A CUSTOM-HANDLER DEPOSIT IS REFUNDED BY ITS HANDLER.**  No hash
premise.  When the claim-time handler of asset `a` is set and is not the vault, and its
`bridgeRecoverFailedTransfer` returns, the refund of a `finalizeDeposit` call on `a` returns `true` with
exactly that handler's effect: the vault and its `assetIdCheck` play no part.  (At the pin the same
call went to the vault, and reverted under the premises of
`AtomicRecovery.History.CustomHandlerDepositRefundReverts`.) -/
def Properties.CustomHandlerRecoveredByItsHandler : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (w w' : World X) (dest src : Chain) (a : AssetId) (data : Bytes),
    dest ≠ cfg.l1Chain → w.router.handler a ≠ 0 → w.router.handler a ≠ cfg.ntv →
    code (w.router.handler a) w dest a data = some w' →
      recoverAtomicCallAtHead enc cfg hk code w cfg.manager dest (.finalizeDeposit src a data)
        = some (w', true)

/-- **A VAULT BURN'S OWN CALL REFUNDS THE DEPOSITOR, WHILE THE VAULT IS STILL ITS HANDLER.**  The
vault's preparation (`bridgeBurn` on a registered representation token,
`NativeTokenVaultBase.prepare`) returns mint data `out.data`; the router call carries bytes the vault
decodes to it (the ABI round trip of `encodeBridgeMintData`, `SOL-ABI`); the claim-time handler of the
asset is the vault (not rotated); the destination is not L1; the asset is not this chain's base token
(whose burn and refund go through the base-token holder, not a representation token); in the refund
world the vault records the asset as bridged (not native to this chain) with a local token, is
unpaused, and the tracker hook returns.  Then the claim's iteration is the mint hook on that token,
to the request's depositor, of the request's amount, and returns `true` when the hook returns.  The
refund world is tied to the preparation only through these premises. -/
def Properties.PreparedBurnRefundsDepositorAtHead : Prop :=
  ∀ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc),
    NativeTokenVaultBase.WellFormed s → NativeTokenVaultBase.prepare prepHooks s r = some out →
    ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
      (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X) (mintBytes : Bytes)
      (x₁ : X),
      dest ≠ cfg.l1Chain → cfg.decodeMint mintBytes = some out.data →
      w.router.handler r.assetId = cfg.ntv → cfg.ntv ≠ 0 → r.assetId ≠ cfg.baseAsset →
      w.paused = false → w.vault.originChain r.assetId ≠ cfg.thisChain →
      w.vault.token r.assetId ≠ 0 → hk.fromChain w.rest dest r.assetId r.data.amount = some x₁ →
        recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg r.assetId mintBytes)
          = (hk.mint x₁ (w.vault.token r.assetId) r.depositor r.data.amount).map
              (fun x₂ => ({ w with rest := x₂ }, true))

/-- **HEADLINE (b) FOR A VAULT BURN: AFTER ANY RUN THAT DOES NOT ROTATE THE ASSET, THE DEPOSITOR IS
RE-MINTED.**  `PreparedBurnRefundsDepositorAtHead` with its premise on the claim-time handler derived
from the run: the burn ran in router maps `R` on the vault (`burnHandler cfg R a` is the vault), and
between the burn and the claim the maps evolve by a run of the writers, for any writers'
configuration `K`, from `burnRouter cfg R a` to the claim-time maps, with no call rotating the asset
away from the vault.  The other premises are `PreparedBurnRefundsDepositorAtHead`'s.  Then the claim's
iteration on the router call is the mint hook on the vault's token, to the request's depositor, of
the request's amount.

Premises: the burn is the vault's preparation from a `WellFormed` vault state; the bundle call's
bytes decode to the burn's mint data; a non-L1 destination; a nonzero vault address; the burn ran
on the vault; between burn and claim the maps evolve only by a run of the map writers with no call
rotating the asset away from the vault; the asset is not this chain's base token; the vault is not
paused, knows the asset as bridged with a nonzero local token, and its tracker hook returns.  No
hash premise. Model boundary (`MODEL-ATOMIC-RECOVERY-HEAD`): call and mint data are typed (`SOL-ABI`); the
router's, manager's and tracker's `L1_CHAIN_ID` slots are one value and the vault's and tracker's
`BASE_TOKEN_ASSET_ID` slots another (`OPS-CONFIG`); the vault's hooks and the base-token holder
write only the rest of the world (`DEP-FRAME`); the code at every handler other than the vault
is arbitrary (`HandlerCode`); `nonReentrant`, events and the bundle decoding are omitted. -/
@[headline] def Properties.VaultBurnRefundsDepositorAfterRunAtHead : Prop :=
  ∀ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc),
    NativeTokenVaultBase.WellFormed s → NativeTokenVaultBase.prepare prepHooks s r = some out →
    ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
      (code : HandlerCode X) (K : AllWriters.Cfg) (R : Router) (ops : List AllWriters.Op)
      (dest : Chain) (base : AssetId) (w : World X) (mintBytes : Bytes) (x₁ : X),
      dest ≠ cfg.l1Chain → cfg.decodeMint mintBytes = some out.data → cfg.ntv ≠ 0 →
      AtomicRecovery.burnHandler cfg.toConfig R r.assetId = cfg.ntv →
      AllWriters.ARun K (burnRouter cfg.toConfig R r.assetId) ops w.router →
      NoRotation K r.assetId cfg.ntv ops →
      r.assetId ≠ cfg.baseAsset → w.paused = false → w.vault.originChain r.assetId ≠ cfg.thisChain →
      w.vault.token r.assetId ≠ 0 → hk.fromChain w.rest dest r.assetId r.data.amount = some x₁ →
        recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg r.assetId mintBytes)
          = (hk.mint x₁ (w.vault.token r.assetId) r.depositor r.data.amount).map
              (fun x₂ => ({ w with rest := x₂ }, true))

/-- **THE PIN'S STRANDED BUNDLE IS REFUNDED AT HEAD.**  One world and one bundle of two
router-produced calls: a deposit of a custom-handler asset, burned by its handler, and a deposit of a
vault asset, burned by the vault.  In the PIN model the claim reverts (`AtomicRecovery`'s
`CustomHandlerBundleIsStranded` instance).  In the HEAD model, in the same world, the claim of the
bundle of the same two router-produced calls, with bytes that decode to the same mint data, succeeds
(for handler code under which the custom handler's refund returns).  (A custom handler that does not
implement the hook still blocks its bundle: `HandlerWithoutRecoveryStrandsBundleAtHead`.) -/
def Properties.PinStrandedBundleRefundedAtHead : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (other : Address → World X → Chain → AtomicRecovery.CallData → Option (World X × Bool))
    (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X)
    (aCustom aVault : AssetId) (mdCustom mdVault : MintData) (bCustom bVault : Bytes),
    cfg.decodeMint bCustom = some mdCustom ∧ cfg.decodeMint bVault = some mdVault
    ∧ AtomicRecovery.burnHandler cfg.toConfig w.router aCustom ≠ cfg.ntv
    ∧ AtomicRecovery.burnHandler cfg.toConfig w.router aVault = cfg.ntv
    ∧ AtomicRecovery.claimRefund (AtomicRecovery.recoverCall enc cfg.toConfig hk.toHooks other dest)
        LegState.Revertable w
        [AtomicRecovery.routerCall cfg.toConfig aCustom mdCustom,
          AtomicRecovery.routerCall cfg.toConfig aVault mdVault] = none
    ∧ (claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w
        ⟨dest, base, [routerCallAtHead cfg aCustom bCustom, routerCallAtHead cfg aVault bVault]⟩).isSome

/-- **THE PIN'S `RecoveryCallsTheVault` IS FALSE AT HEAD.**  Its head form — the manager's
`recoverAtomicCall` on any `finalizeDeposit` data is the vault's refund — fails.  (A negative result:
no witness.) -/
def Properties.RecoveryCallsTheVaultFailsAtHead : Prop :=
  ¬ ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
      (code : HandlerCode X) (w : World X) (dest src : Chain) (a : AssetId) (data : Bytes),
      dest ≠ cfg.l1Chain →
      recoverAtomicCallAtHead enc cfg hk code w cfg.manager dest (.finalizeDeposit src a data)
        = (vaultRecoverAtHead enc cfg hk w cfg.router 0 dest a
            (cfg.decodeMint data)).map (fun w' => (w', true))

/-- **…AND SO IS `RecoveryIgnoresHandler`.**  Replacing the router's maps can change the refund.  (A
negative result: no witness.) -/
def Properties.RecoveryIgnoresHandlerFailsAtHead : Prop :=
  ¬ ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
      (code : HandlerCode X) (w : World X) (R : Router) (dest : Chain) (d : HeadCallData),
      recoverAtomicCallAtHead enc cfg hk code { w with router := R } cfg.manager dest d
        = (recoverAtomicCallAtHead enc cfg hk code w cfg.manager dest d).map
            (fun p => ({ p.1 with router := R }, p.2))

/-! ## (c) Rotating the handler between burn and claim misroutes recovery -/

/-- **A ZEROED HANDLER MAKES THE REFUND REVERT.**  If the claim-time handler of the asset is unset —
for instance after the L2 counterpart's `setAssetHandlerAddress(_, a, 0)`, which the writers allow
(`ZeroedHandlerReachableByCounterpart`) — the router call's iteration reverts
(`AssetHandlerDoesNotExist`, `L2AssetRouter.sol:300`), for every destination (an L1 destination
reverts earlier, `:275`). -/
def Properties.ZeroedHandlerRecoveryReverts : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (w : World X) (dest : Chain) (base : AssetId) (a : AssetId)
    (mintBytes : Bytes),
    w.router.handler a = 0 →
      recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg a mintBytes) = none

/-- **HEADLINE (c): ROTATING TO A NO-OP HANDLER STRANDS THE BURN.**  A concrete L2 world, and one
bundle of one router-produced call on an asset whose burn handler is the vault.  Claimed in that
world, the leg becomes `Reverted` and the mint data's `originalCaller` is re-credited its (positive)
`amount`.  If instead one counterpart call `setAssetHandlerAddress` comes first
(`AllWriters.AStep … (.counterpartSet a h₁)`), re-pointing the asset at a handler whose
`bridgeRecoverFailedTransfer` returns without moving funds, the claim still succeeds and marks the
leg `Reverted`, which enables no second claim, and the world apart from the router's maps — the
`originalCaller`'s balance included — is unchanged (known issue 5,
`protocol-docs/atomicity/security.md:149-156`, "silently no-op (consuming the claim)"). -/
@[countermodel] def Properties.RotationToNoOpHandlerStrandsBurn : Prop :=
  ∃ (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks (Addr160 → ℕ))
    (code : HandlerCode (Addr160 → ℕ)) (K : AllWriters.Cfg) (w : World (Addr160 → ℕ))
    (R' : Router) (dest : Chain) (base : AssetId) (a : AssetId) (mintBytes : Bytes)
    (md : MintData) (h₁ : Address) (wRefunded : World (Addr160 → ℕ)),
    K.side = .l2 ∧ cfg.decodeMint mintBytes = some md
    ∧ AtomicRecovery.burnHandler cfg.toConfig w.router a = cfg.ntv ∧ h₁ ≠ cfg.ntv
    ∧ claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w
        ⟨dest, base, [routerCallAtHead cfg a mintBytes]⟩ = some (LegState.Reverted, wRefunded)
    ∧ wRefunded.rest md.originalCaller = w.rest md.originalCaller + md.amount.val
    ∧ 0 < md.amount.val
    ∧ AllWriters.AStep K (.counterpartSet a h₁) w.router R' ∧ R'.handler a = h₁
    ∧ claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable
        { w with router := R' } ⟨dest, base, [routerCallAtHead cfg a mintBytes]⟩
      = some (LegState.Reverted, { w with router := R' })
    ∧ ¬ claimEnabled LegState.Reverted

/-- **ROTATING TO A HANDLER WITHOUT RECOVERY BLOCKS THE CLAIM, UNTIL ROTATED BACK.**  The same setting
with a new handler whose `bridgeRecoverFailedTransfer` reverts.  After the rotation the claim reverts,
so the leg stays `Revertable`.  After a second counterpart call points the asset back at the vault,
the claim re-credits the mint data's `originalCaller` its (positive) `amount` ("blocking the refund
until rotated back", known issue 5). -/
@[countermodel] def Properties.RotationToRevertingHandlerBlocksClaim : Prop :=
  ∃ (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks (Addr160 → ℕ))
    (code : HandlerCode (Addr160 → ℕ)) (K : AllWriters.Cfg) (w : World (Addr160 → ℕ))
    (R' R'' : Router) (dest : Chain) (base : AssetId) (a : AssetId) (mintBytes : Bytes)
    (md : MintData) (h₁ : Address) (wRefunded : World (Addr160 → ℕ)),
    K.side = .l2 ∧ cfg.decodeMint mintBytes = some md
    ∧ AtomicRecovery.burnHandler cfg.toConfig w.router a = cfg.ntv ∧ h₁ ≠ cfg.ntv
    ∧ AllWriters.AStep K (.counterpartSet a h₁) w.router R'
    ∧ claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable
        { w with router := R' } ⟨dest, base, [routerCallAtHead cfg a mintBytes]⟩ = none
    ∧ AllWriters.AStep K (.counterpartSet a cfg.ntv) R' R''
    ∧ claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable
        { w with router := R'' } ⟨dest, base, [routerCallAtHead cfg a mintBytes]⟩
      = some (LegState.Reverted, wRefunded)
    ∧ wRefunded.rest md.originalCaller = w.rest md.originalCaller + md.amount.val
    ∧ 0 < md.amount.val

/-- **ON L2, A LIVE ROUTE IS ROTATED ONLY BY THE COUNTERPART, THE INITIALIZER OR THE VAULT.**  Along
every L2 run of the router-map writers from fresh storage, a call that changes the handler of `a` from
a nonzero value is the L1 counterpart's `setAssetHandlerAddress(_, a, _)`, the initializer's write at
`a`, or a `setAssetHandlerAddressThisChain` by the vault (which in the deployed vault names the vault
itself, `NativeTokenVaultBase.sol:495-498`).  No other account rotates a route: the guard
`msg.sender == assetDeploymentTracker[assetId]` (`AssetRouterBase.sol:73`) would let a custom
deployment tracker re-register its asset, but no L2 run records one
(`AllWriters.L2OnlyVaultRegisters`).  No hash premise.  The writers are modelled in `AllWriters`, at
`b17415d20` (see the Specs header). -/
def Properties.L2RotationOnlyByCounterpartSeedOrVault : Prop :=
  ∀ (K : AllWriters.Cfg), K.side = .l2 →
    ∀ (ops : List AllWriters.Op) (R R' : Router) (op : AllWriters.Op) (a : AssetId),
    AllWriters.ARun K empty ops R → AllWriters.AStep K op R R' →
    R.handler a ≠ 0 → R'.handler a ≠ R.handler a →
      (∃ h, op = .counterpartSet a h) ∨ (op = .seed ∧ K.seedId = a)
        ∨ ∃ d h, op = .register K.ntv d h

/-! ## (d) One failing recovery still blocks the whole bundle -/

/-- **THE HEAD ACCEPTANCE RULE: NO ATTEMPTED RECOVERY MAY REVERT, AND THAT IS ALL.**  For any
per-call behaviour, a claim on a `Revertable` leg succeeds exactly when the destination is not L1 and
the loop's outcomes on the threaded state contain no revert (`RecoveryLimits.LoopCompletes`).  The
pin's second condition, `recoveredCount ≠ 0` (`RecoveryLimits.ClaimAccepted`), is gone. -/
def Properties.ClaimSucceedsIffLoopCompletesAtHead : Prop :=
  ∀ (X : Type) (cfg : HeadConfig)
    (step : Chain → AssetId → World X → HeadCall → Option (World X × Bool)) (w : World X)
    (b : HeadBundle),
    (claimRefundAtHead cfg step LegState.Revertable w b).isSome = true
      ↔ b.destChain ≠ cfg.l1Chain
        ∧ LoopCompletes (outcomesAtHead (step b.destChain b.destBaseTokenAssetId) w b.calls)

/-- **HEADLINE (d): ONE REVERTING RECOVERY STILL BLOCKS THE WHOLE BUNDLE.**  The revert is still
uncaught.  For any per-call behaviour: if an invariant holds of the claim-time world and is kept by
every call of the bundle that returns, and some call of the bundle reverts in every world satisfying
it, the claim reverts, whatever the leg state.  So the leg stays `Revertable` and no call of the
bundle — those that would have been refunded included — is refunded.

Premises: an invariant of the claim-time world that every returning call of the bundle keeps, and
a call of the bundle that reverts in every world satisfying it.  No hash premise. Model boundary (`MODEL-ATOMIC-RECOVERY-HEAD`): call and mint data are typed (`SOL-ABI`); the
router's, manager's and tracker's `L1_CHAIN_ID` slots are one value and the vault's and tracker's
`BASE_TOKEN_ASSET_ID` slots another (`OPS-CONFIG`); the vault's hooks and the base-token holder
write only the rest of the world (`DEP-FRAME`); the code at every handler other than the vault
is arbitrary (`HandlerCode`); `nonReentrant`, events and the bundle decoding are omitted. -/
@[headline] def Properties.RevertingCallBlocksClaimAtHead : Prop :=
  ∀ (X : Type) (cfg : HeadConfig)
    (step : Chain → AssetId → World X → HeadCall → Option (World X × Bool)) (st : LegState)
    (w : World X) (b : HeadBundle) (Inv : World X → Prop) (Blocks : HeadCall → Prop),
    (∀ c ∈ b.calls, ∀ u u' x, Inv u →
      step b.destChain b.destBaseTokenAssetId u c = some (u', x) → Inv u') →
    (∀ c ∈ b.calls, Blocks c → ∀ u, Inv u → step b.destChain b.destBaseTokenAssetId u c = none) →
    (∃ c ∈ b.calls, Blocks c) → Inv w →
      claimRefundAtHead cfg step st w b = none

/-- **A ROUTER CALL WHOSE HANDLER CANNOT REFUND BLOCKS ITS BUNDLE.**  On the head loop.  Let the
claim-time handler of asset `a` be `h`; if `h` is set, let its refund of `a` revert whenever the table
points `a` at `h` (`RecoveryRevertsAt`: for a custom handler, code that does not implement
`bridgeRecoverFailedTransfer`, `IL2AssetHandler.sol:11-13`).  If the other handlers' code never
re-points `a`, the claim of every bundle with a router call on `a` reverts. -/
def Properties.UnrecoverableHandlerBlocksBundleAtHead : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (st : LegState) (w : World X) (b : HeadBundle) (a : AssetId)
    (h : Address),
    w.router.handler a = h → (h ≠ 0 → RecoveryRevertsAt enc cfg hk code h a) →
    CodeKeepsHandlerAt a code → HasRouterCallOnAtHead cfg a b.calls →
      claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) st w b = none

/-- **HEADLINE (d), CONCRETE: A BUNDLE STRANDED AT HEAD.**  One world and one bundle of two
router-produced calls: a deposit of a vault asset, whose call alone would be refunded, and a deposit
of a custom-handler asset whose handler does not implement `bridgeRecoverFailedTransfer`.  The claim
reverts in every world reachable by steps that keep the custom asset pointed at that handler. -/
def Properties.HandlerWithoutRecoveryStrandsBundleAtHead : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X)
    (aCustom aVault : AssetId) (bCustom bVault : Bytes),
    w.router.handler aCustom ≠ 0 ∧ w.router.handler aCustom ≠ cfg.ntv
    ∧ w.router.handler aVault = cfg.ntv
    ∧ (claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w
        ⟨dest, base, [routerCallAtHead cfg aVault bVault]⟩).isSome
    ∧ ∀ w', Relation.ReflTransGen
        (fun u v : World X => v.router.handler aCustom = u.router.handler aCustom) w w' →
        claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w'
          ⟨dest, base, [routerCallAtHead cfg aCustom bCustom, routerCallAtHead cfg aVault bVault]⟩
        = none

/-- **A CLAIM THAT RECOVERS NOTHING STILL CONSUMES THE LEG.**  For any per-call behaviour: if the loop
completes having reversed nothing, the claim succeeds and the leg becomes `Reverted`, which enables
no second claim (`AtomicFlowManager.sol:290-291`; per-bundle consumption, known issue 1,
`protocol-docs/atomicity/security.md:105-112`). -/
def Properties.NothingRecoveredStillConsumesLegAtHead : Prop :=
  ∀ (X : Type) (cfg : HeadConfig)
    (step : Chain → AssetId → World X → HeadCall → Option (World X × Bool)) (w w' : World X)
    (b : HeadBundle),
    b.destChain ≠ cfg.l1Chain →
    recoverBundleAtHead (step b.destChain b.destBaseTokenAssetId) w b.calls = some (w', 0) →
      claimRefundAtHead cfg step LegState.Revertable w b = some (LegState.Reverted, w')
      ∧ ¬ claimEnabled LegState.Reverted

/-- **A ROUTER CALL THE ROUTER DOES NOT RECOGNISE IS CONSUMED WITHOUT A REFUND.**  On the head loop, a
call from the router whose data is not a `finalizeDeposit` returns `false`
(`L2AssetRouter.sol:284-286`) and is skipped: a bundle of such calls and zero-value direct calls is
claimed as a no-op (the router's own note, `L2AssetRouter.sol:276-283`). -/
def Properties.UnrecognisedRouterCallConsumedAtHead : Prop :=
  ∀ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (w : World X) (b : HeadBundle),
    b.destChain ≠ cfg.l1Chain →
    (∀ c ∈ b.calls, (c.sender = cfg.router ∧ c.data = .other) ∨ (c.sender ≠ cfg.router ∧ c.value = 0)) →
      claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w b
        = some (LegState.Reverted, w)

/-- **THE PIN REJECTED A CLAIM THAT RECOVERS NOTHING; THE HEAD ACCEPTS IT.**  One world and one
single-call bundle, a zero-value direct call to the router whose data the router does not recognise:
at the pin its claim reverts (`ManagerNoRecoverableCalls`), at head it succeeds and changes nothing. -/
def Properties.PinRejectsNothingRecoverableHeadAccepts : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (other : Address → World X → Chain → AtomicRecovery.CallData → Option (World X × Bool))
    (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X) (sender : Address),
    sender ≠ cfg.router ∧ dest ≠ cfg.l1Chain
    ∧ AtomicRecovery.claimRefund (AtomicRecovery.recoverCall enc cfg.toConfig hk.toHooks other dest)
        LegState.Revertable w [AtomicRecovery.directCall cfg.router sender .other] = none
    ∧ claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w
        ⟨dest, base, [directCallAtHead cfg.router sender 0 .other]⟩ = some (LegState.Reverted, w)

/-! ## (e) An L1 destination is refused at claim time -/

/-- **AN L1 DESTINATION IS REFUSED AT CLAIM TIME.**  For any per-call behaviour, leg state and world,
the claim of a bundle whose destination is `L1_CHAIN_ID` reverts (`AtomicFlowManager.sol:299`,
`RecoverToL1NotSupported`) before any call is attempted.  At send, `_sendBundle` rejects an atomic
bundle to L1 (`InteropCenter.sol:552-553`); the send is not modelled here.

Premises: the bundle's destination is `L1_CHAIN_ID`.  No hash premise. Model boundary (`MODEL-ATOMIC-RECOVERY-HEAD`): call and mint data are typed (`SOL-ABI`); the
router's, manager's and tracker's `L1_CHAIN_ID` slots are one value and the vault's and tracker's
`BASE_TOKEN_ASSET_ID` slots another (`OPS-CONFIG`); the vault's hooks and the base-token holder
write only the rest of the world (`DEP-FRAME`); the code at every handler other than the vault
is arbitrary (`HandlerCode`); `nonReentrant`, events and the bundle decoding are omitted. -/
@[headline] def Properties.L1DestinationClaimRevertsAtHead : Prop :=
  ∀ (X : Type) (cfg : HeadConfig)
    (step : Chain → AssetId → World X → HeadCall → Option (World X × Bool)) (st : LegState)
    (w : World X) (b : HeadBundle),
    b.destChain = cfg.l1Chain → claimRefundAtHead cfg step st w b = none

/-! ## Witnesses -/

/-- **THE DIRECT-CALL PREMISES ARE SATISFIABLE, WHERE IT MATTERS.**  For `DirectCallSkipsRouterRecovery`,
`DirectCallDataIgnoredAtHead` and `SentDirectCallNeverRecoveredAtHead`: a direct zero-value call by a
non-router account to the router, carrying `finalizeDeposit` data on an asset whose handler is set,
for a non-L1 destination, such that the router's refund of that very data would return `true` — yet
the call's iteration declines. -/
def Properties.DirectCallPremisesSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X) (sender : Address)
    (src : Chain) (a : AssetId) (data : Bytes),
    sender ≠ cfg.router ∧ dest ≠ cfg.l1Chain ∧ w.router.handler a ≠ 0
    ∧ (∃ w', recoverAtomicCallAtHead enc cfg hk code w cfg.manager dest (.finalizeDeposit src a data)
        = some (w', true))
    ∧ recoverCallAtHead enc cfg hk code dest base w
        (directCallAtHead cfg.router sender 0 (.finalizeDeposit src a data)) = some (w, false)

/-- **`DirectValueLegRefundsItsSenderAtHead`'S AND `CrossBaseValueLegRefundAtHead`'S PREMISES ARE
SATISFIABLE**, on a destination base-token asset that is not this chain's base token, with a refund
that credits the sender exactly the call's value. -/
def Properties.DirectValueLegRefundSatisfiable : Prop :=
  ∃ (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks (Addr160 → ℕ))
    (code : HandlerCode (Addr160 → ℕ)) (dest : Chain) (base : AssetId) (w w' : World (Addr160 → ℕ))
    (c : HeadCall),
    c.sender ≠ cfg.router ∧ c.value ≠ 0 ∧ dest ≠ cfg.l1Chain ∧ base ≠ cfg.baseAsset
    ∧ recoverCallAtHead enc cfg hk code dest base w c = some (w', true)
    ∧ w'.rest (narrow c.sender) = w.rest (narrow c.sender) + c.value.val

/-- **`SameBaseValueLegRefundAtHead`'S AND `VaultRecoverAtHeadOnBaseToken`'S PREMISES ARE SATISFIABLE**,
with a base-token holder that credits the sender exactly the call's value, in a world where the pin
model's vault refund of the same asset would revert (the vault holds no token for it). -/
def Properties.SameBaseValueLegRefundSatisfiable : Prop :=
  ∃ (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks (Addr160 → ℕ))
    (code : HandlerCode (Addr160 → ℕ)) (dest : Chain) (w w' : World (Addr160 → ℕ)) (c : HeadCall),
    c.sender ≠ cfg.router ∧ c.value ≠ 0 ∧ dest ≠ cfg.l1Chain
    ∧ w.paused = false ∧ w.vault.originChain cfg.baseAsset ≠ cfg.thisChain
    ∧ recoverCallAtHead enc cfg hk code dest cfg.baseAsset w c = some (w', true)
    ∧ w'.rest (narrow c.sender) = w.rest (narrow c.sender) + c.value.val
    ∧ AtomicRecovery.ntvRecover enc cfg.toConfig hk.toHooks w cfg.router 0 dest cfg.baseAsset
        (some (baseRefundMint c.sender c.value)) = none

/-- **`VaultRecoverAtHeadIsPinRefundOffBaseToken`'S PREMISES ARE SATISFIABLE**, with a refund that
returns. -/
def Properties.VaultRecoverAtHeadOffBaseSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X) (w : World X)
    (caller : Address) (v : UInt256) (chainId : Chain) (a : AssetId) (m : Option MintData),
    chainId ≠ cfg.l1Chain ∧ a ≠ cfg.baseAsset
    ∧ (vaultRecoverAtHead enc cfg hk w caller v chainId a m).isSome

/-- **HEADLINE (a)'S PREMISES ARE SATISFIABLE**, on a nonempty bundle whose call names the router and
carries `finalizeDeposit` data. -/
@[witness] def Properties.DirectBundleClaimIsNoOpSatisfiable : Prop :=
  ∃ (cfg : HeadConfig) (b : HeadBundle) (src : Chain) (a : AssetId) (data : Bytes)
    (sender : Address),
    b.destChain ≠ cfg.l1Chain ∧ (∀ c ∈ b.calls, c.sender ≠ cfg.router ∧ c.value = 0)
    ∧ directCallAtHead cfg.router sender 0 (.finalizeDeposit src a data) ∈ b.calls

/-- **THE SEND-SIDE PREMISE IS SATISFIABLE**, with both a direct and an indirect starter: a sender
other than the router, whose indirect starter yields a call from the router and whose direct starter
does not. -/
def Properties.RouterSenderIffIndirectSatisfiable : Prop :=
  ∃ (cfg : HeadConfig) (msgSender : Address) (a : AssetId) (mintBytes : Bytes) (d : HeadCallData),
    msgSender ≠ cfg.router
    ∧ (processCallStarterAtHead cfg msgSender (.indirect a mintBytes)).sender = cfg.router
    ∧ (processCallStarterAtHead cfg msgSender (.direct cfg.router d 0)).sender ≠ cfg.router

/-- **`VaultRouterCallIsPinIterationAtHead`'S PREMISES ARE SATISFIABLE**, with an iteration that
returns `true`. -/
def Properties.VaultRouterCallIsPinIterationSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X) (code : HandlerCode X)
    (dest : Chain) (base : AssetId) (w w' : World X) (a : AssetId) (mintBytes : Bytes)
    (md : MintData),
    dest ≠ cfg.l1Chain ∧ a ≠ cfg.baseAsset ∧ cfg.ntv ≠ 0 ∧ w.router.handler a = cfg.ntv
    ∧ cfg.decodeMint mintBytes = some md
    ∧ recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg a mintBytes) = some (w', true)

/-- **THE ROUTING PREMISES ARE SATISFIABLE.**  For `RecoveryReadsClaimTimeHandler`,
`BurnHandlerNonzero` and `CustomHandlerRecoveredByItsHandler`: a non-L1 destination, a nonzero vault
address, and a custom handler, set and not the vault, whose refund returns — and then the router's
refund returns `true`. -/
def Properties.RoutingPremisesSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (w w' : World X) (dest src : Chain) (a : AssetId) (data : Bytes),
    dest ≠ cfg.l1Chain ∧ cfg.ntv ≠ 0 ∧ w.router.handler a ≠ 0 ∧ w.router.handler a ≠ cfg.ntv
    ∧ code (w.router.handler a) w dest a data = some w'
    ∧ recoverAtomicCallAtHead enc cfg hk code w cfg.manager dest (.finalizeDeposit src a data)
      = some (w', true)

/-- **`NoRotationKeepsHandler`'S PREMISES ARE SATISFIABLE**, on a nonempty run that does move some
other route. -/
def Properties.NoRotationKeepsHandlerSatisfiable : Prop :=
  ∃ (K : AllWriters.Cfg) (R₁ R₂ : Router) (ops : List AllWriters.Op) (a : AssetId) (h₀ : Address),
    AllWriters.ARun K R₁ ops R₂ ∧ R₁.handler a = h₀ ∧ h₀ ≠ 0 ∧ NoRotation K a h₀ ops
    ∧ ∃ x, R₂.handler x ≠ R₁.handler x

/-- **`HandlerMovesOnlyByRotation`'S PREMISES ARE SATISFIABLE**: a counterpart call moving a live
route. -/
def Properties.HandlerMovesOnlyByRotationSatisfiable : Prop :=
  ∃ (K : AllWriters.Cfg) (op : AllWriters.Op) (R R' : Router) (a : AssetId),
    AllWriters.AStep K op R R' ∧ R'.handler a ≠ R.handler a ∧ R.handler a ≠ 0

/-- **`NoRotationKeepsHandlerLoggedOn`'S PREMISES ARE SATISFIABLE**, on a nonempty run whose one call
is a registration hashing a triple other than the asset's, with `encodeAssetId` injective on that
pair, from maps that point the asset at a custom handler. -/
def Properties.NoRotationKeepsHandlerLoggedOnSatisfiable : Prop :=
  ∃ (K : AllWriters.Cfg) (R₁ R₂ : Router) (ops : List AllWriters.Op) (c₀ : Chain) (s₀ : Address)
    (d₀ : AssetData) (h₀ : Address),
    AllWriters.ARun K R₁ ops R₂ ∧ R₁.handler (K.enc c₀ s₀ d₀) = h₀ ∧ h₀ ≠ 0
    ∧ (∃ op ∈ ops, ∃ p, op.triple K = some p ∧ p ≠ (c₀, s₀, d₀))
    ∧ (∀ op ∈ ops, ∀ p, op.triple K = some p → IdInjOn K.enc {(c₀, s₀, d₀), p})
    ∧ (∀ caller d h, AllWriters.Op.register caller d h ∈ ops →
        (K.thisChain, senderOf K.ntv K.ntvAddr caller, d) = (c₀, s₀, d₀) → h = h₀)
    ∧ (∀ a' h, AllWriters.Op.counterpartSet a' h ∈ ops → a' = K.enc c₀ s₀ d₀ → h = h₀)
    ∧ (AllWriters.Op.seed ∈ ops → K.seedId = K.enc c₀ s₀ d₀ → K.ntv = h₀)

/-- **THE LOGGED PREMISES ARE SATISFIABLE**, for `RouterLegReachesBurnHandlerLoggedOn`: a run with a
registration hashing a triple other than the burned asset's, injectivity on that pair, a burned asset
whose burn handler is a custom handler, a non-L1 destination, and a recovery that returns. -/
def Properties.LoggedRoutingPremisesSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (K : AllWriters.Cfg) (R : Router) (ops : List AllWriters.Op)
    (w : World X) (dest : Chain) (base : AssetId) (c₀ : Chain) (s₀ : Address) (d₀ : AssetData)
    (mintBytes : Bytes),
    dest ≠ cfg.l1Chain ∧ cfg.ntv ≠ 0
    ∧ AllWriters.ARun K (burnRouter cfg.toConfig R (K.enc c₀ s₀ d₀)) ops w.router
    ∧ (∃ op ∈ ops, ∃ p, op.triple K = some p ∧ p ≠ (c₀, s₀, d₀))
    ∧ (∀ op ∈ ops, ∀ p, op.triple K = some p → IdInjOn K.enc {(c₀, s₀, d₀), p})
    ∧ (∀ caller d h, AllWriters.Op.register caller d h ∈ ops →
        (K.thisChain, senderOf K.ntv K.ntvAddr caller, d) = (c₀, s₀, d₀) →
          h = AtomicRecovery.burnHandler cfg.toConfig R (K.enc c₀ s₀ d₀))
    ∧ (∀ a' h, AllWriters.Op.counterpartSet a' h ∈ ops → a' = K.enc c₀ s₀ d₀ →
        h = AtomicRecovery.burnHandler cfg.toConfig R (K.enc c₀ s₀ d₀))
    ∧ (AllWriters.Op.seed ∈ ops → K.seedId = K.enc c₀ s₀ d₀ →
        K.ntv = AtomicRecovery.burnHandler cfg.toConfig R (K.enc c₀ s₀ d₀))
    ∧ AtomicRecovery.burnHandler cfg.toConfig R (K.enc c₀ s₀ d₀) ≠ cfg.ntv
    ∧ (recoverCallAtHead enc cfg hk code dest base w
        (routerCallAtHead cfg (K.enc c₀ s₀ d₀) mintBytes)).isSome

/-- **HEADLINE (b)'S PREMISES ARE SATISFIABLE**, on a nonempty run from the post-burn maps of a
custom-handler asset, with a refund that returns. -/
@[witness] def Properties.RouterLegReachesBurnHandlerSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (K : AllWriters.Cfg) (R : Router) (ops : List AllWriters.Op)
    (w : World X) (dest : Chain) (base : AssetId) (a : AssetId) (mintBytes : Bytes),
    dest ≠ cfg.l1Chain ∧ cfg.ntv ≠ 0
    ∧ AllWriters.ARun K (burnRouter cfg.toConfig R a) ops w.router ∧ ops ≠ []
    ∧ NoRotation K a (AtomicRecovery.burnHandler cfg.toConfig R a) ops
    ∧ AtomicRecovery.burnHandler cfg.toConfig R a ≠ cfg.ntv
    ∧ (recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg a mintBytes)).isSome

/-- **`PreparedBurnRefundsDepositorAtHead`'S PREMISES ARE JOINTLY SATISFIABLE**, with a depositor who
is not the remote receiver and a refund that returns. -/
def Properties.PreparedBurnRefundAtHeadSatisfiable : Prop :=
  ∃ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc)
    (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (dest : Chain) (base : AssetId) (w : World X) (mintBytes : Bytes)
    (x₁ : X),
    NativeTokenVaultBase.WellFormed s ∧ NativeTokenVaultBase.prepare prepHooks s r = some out
    ∧ r.depositor ≠ r.data.receiver
    ∧ dest ≠ cfg.l1Chain ∧ cfg.decodeMint mintBytes = some out.data
    ∧ w.router.handler r.assetId = cfg.ntv ∧ cfg.ntv ≠ 0 ∧ r.assetId ≠ cfg.baseAsset
    ∧ w.paused = false ∧ w.vault.originChain r.assetId ≠ cfg.thisChain
    ∧ w.vault.token r.assetId ≠ 0 ∧ hk.fromChain w.rest dest r.assetId r.data.amount = some x₁
    ∧ (recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg r.assetId mintBytes)).isSome

/-- **`VaultBurnRefundsDepositorAfterRunAtHead`'S PREMISES ARE JOINTLY SATISFIABLE**, on a nonempty
run between burn and claim that moves another asset's route, with a refund that returns. -/
@[witness] def Properties.VaultBurnRefundAfterRunSatisfiable : Prop :=
  ∃ (Acc : Type) (prepHooks : NativeTokenVaultBase.Hooks Acc) (s : NativeTokenVaultBase.State Acc)
    (r : NativeTokenVaultBase.Request) (out : NativeTokenVaultBase.Result Acc)
    (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (K : AllWriters.Cfg) (R : Router) (ops : List AllWriters.Op)
    (dest : Chain) (base : AssetId) (w : World X) (mintBytes : Bytes) (x₁ : X),
    NativeTokenVaultBase.WellFormed s ∧ NativeTokenVaultBase.prepare prepHooks s r = some out
    ∧ dest ≠ cfg.l1Chain ∧ cfg.decodeMint mintBytes = some out.data ∧ cfg.ntv ≠ 0
    ∧ AtomicRecovery.burnHandler cfg.toConfig R r.assetId = cfg.ntv
    ∧ AllWriters.ARun K (burnRouter cfg.toConfig R r.assetId) ops w.router ∧ ops ≠ []
    ∧ (∃ x, w.router.handler x ≠ R.handler x)
    ∧ NoRotation K r.assetId cfg.ntv ops
    ∧ r.assetId ≠ cfg.baseAsset ∧ w.paused = false ∧ w.vault.originChain r.assetId ≠ cfg.thisChain
    ∧ w.vault.token r.assetId ≠ 0 ∧ hk.fromChain w.rest dest r.assetId r.data.amount = some x₁
    ∧ (recoverCallAtHead enc cfg hk code dest base w (routerCallAtHead cfg r.assetId mintBytes)).isSome

/-- **`L2RotationOnlyByCounterpartSeedOrVault`'S PREMISES ARE SATISFIABLE**: an L2 run from fresh
storage reaching a live route, and a call that moves it. -/
def Properties.L2RotationSatisfiable : Prop :=
  ∃ (K : AllWriters.Cfg) (ops : List AllWriters.Op) (R R' : Router) (op : AllWriters.Op)
    (a : AssetId),
    K.side = .l2 ∧ AllWriters.ARun K empty ops R ∧ AllWriters.AStep K op R R'
    ∧ R.handler a ≠ 0 ∧ R'.handler a ≠ R.handler a

/-- **A ZEROED HANDLER IS REACHABLE BY A REAL WRITER.**  `ZeroedHandlerRecoveryReverts`'s premise: one
L2 counterpart call zeroes a live route. -/
def Properties.ZeroedHandlerReachableByCounterpart : Prop :=
  ∃ (K : AllWriters.Cfg) (R R' : Router) (a : AssetId),
    K.side = .l2 ∧ R.handler a ≠ 0 ∧ AllWriters.AStep K (.counterpartSet a 0) R R' ∧ R'.handler a = 0

/-- **HEADLINE (d)'S PREMISES ARE JOINTLY SATISFIABLE**, on a two-call bundle whose other call would be
refunded on its own. -/
@[witness] def Properties.RevertingCallBlocksClaimSatisfiable : Prop :=
  ∃ (X : Type) (cfg : HeadConfig)
    (step : Chain → AssetId → World X → HeadCall → Option (World X × Bool))
    (w : World X) (b : HeadBundle) (Inv : World X → Prop) (Blocks : HeadCall → Prop),
    (∀ c ∈ b.calls, ∀ u u' x, Inv u →
      step b.destChain b.destBaseTokenAssetId u c = some (u', x) → Inv u')
    ∧ (∀ c ∈ b.calls, Blocks c → ∀ u, Inv u → step b.destChain b.destBaseTokenAssetId u c = none)
    ∧ (∃ c ∈ b.calls, Blocks c) ∧ Inv w
    ∧ ∃ c ∈ b.calls, ¬ Blocks c
        ∧ (claimRefundAtHead cfg step LegState.Revertable w ⟨b.destChain, b.destBaseTokenAssetId, [c]⟩).isSome

/-- **`UnrecoverableHandlerBlocksBundleAtHead`'S PREMISES ARE JOINTLY SATISFIABLE**, with a set custom
handler and a bundle whose other call would be refunded on its own. -/
def Properties.UnrecoverableHandlerBlocksBundleSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (w : World X) (b : HeadBundle) (a : AssetId) (h : Address),
    w.router.handler a = h ∧ h ≠ 0 ∧ h ≠ cfg.ntv ∧ RecoveryRevertsAt enc cfg hk code h a
    ∧ CodeKeepsHandlerAt a code ∧ HasRouterCallOnAtHead cfg a b.calls
    ∧ ∃ c ∈ b.calls, (claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w
        ⟨b.destChain, b.destBaseTokenAssetId, [c]⟩).isSome

/-- **THE NOTHING-RECOVERED PREMISES ARE SATISFIABLE**, for `NothingRecoveredStillConsumesLegAtHead`
and `UnrecognisedRouterCallConsumedAtHead`: on the head loop, a nonempty bundle of an unrecognised
router call and a zero-value direct call completes with nothing reversed. -/
def Properties.NothingRecoveredSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (w : World X) (b : HeadBundle),
    b.destChain ≠ cfg.l1Chain ∧ b.calls ≠ []
    ∧ (∀ c ∈ b.calls, (c.sender = cfg.router ∧ c.data = .other) ∨ (c.sender ≠ cfg.router ∧ c.value = 0))
    ∧ (∃ c ∈ b.calls, c.sender = cfg.router)
    ∧ recoverBundleAtHead (recoverCallAtHead enc cfg hk code b.destChain b.destBaseTokenAssetId) w
        b.calls = some (w, 0)

/-- **`L1DestinationClaimRevertsAtHead`'S PREMISE IS SATISFIABLE, AND IT IS THE DESTINATION THAT
BLOCKS:** a `Revertable` leg whose bundle is one router-produced call: with the L1 destination the
claim reverts; with another destination the same call is refunded. -/
@[witness] def Properties.L1DestinationClaimRevertsSatisfiable : Prop :=
  ∃ (X : Type) (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X) (code : HandlerCode X)
    (w : World X) (base : AssetId) (a : AssetId) (mintBytes : Bytes) (dest : Chain),
    dest ≠ cfg.l1Chain
    ∧ claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w
        ⟨cfg.l1Chain, base, [routerCallAtHead cfg a mintBytes]⟩ = none
    ∧ (claimRefundAtHead cfg (recoverCallAtHead enc cfg hk code) LegState.Revertable w
        ⟨dest, base, [routerCallAtHead cfg a mintBytes]⟩).isSome

end Contracts.AssetRouter.AtomicRecoveryAtHead
