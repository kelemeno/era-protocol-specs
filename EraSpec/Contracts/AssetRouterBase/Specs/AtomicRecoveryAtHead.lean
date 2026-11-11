import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery
import EraSpec.Contracts.AssetRouterBase.Specs.AllWriters

/-!
# Model at head: atomic recovery dispatches on `InteropCall.from` and routes to the asset's handler

Source: era-contracts `main` at `3605e82dbdca5b60bd7bc6bde14ebb52a6b09b73` ("EVM-1825 docs(atomic-interop):
external developer docs for atomic interop (v33) (#2675)").  Paths are relative to
`l1-contracts/contracts/`.  Every function modelled here is the same at `draft/v0.35.0`
`d9f678900e1bc8286412b78f56d4a9f443983c29`, up to line shifts and the rename
`_nativeTokenVaultAddr` → `_getNativeTokenVaultAddr`; the v35 lines are given in brackets.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.AtomicRecoveryAtHead` and proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecoveryAtHead`.

The pin model `EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery` (`c67894b9`) is unchanged and
still describes the pin.  This file models the code that replaced its two halves upstream: the
handler-routed `recoverAtomicCall` (#2339) and the manager's dispatch on the call's local sender
(#2348), together with the removal of the `recovered == 0` rejection.

## The manager's loop (`atomic-interop/AtomicFlowManager.sol:289-322` [v35 `:292-325`])

    require(destChainId != L1_CHAIN_ID, RecoverToL1NotSupported());                       // :296
    bytes32 destBaseTokenAssetId = _bundle.destinationBaseTokenAssetId;
    for (uint256 i = 0; i < callsLen; ++i) {
        InteropCall memory c = _bundle.calls[i];
        if (c.from == L2_ASSET_ROUTER_ADDR) {                                                // :309
            IAtomicRecoverable(c.from).recoverAtomicCall(destChainId, c.data);              // result ignored
        }
        if (c.from != L2_ASSET_ROUTER_ADDR && c.value != 0) {                                // :313
            IAssetRouterShared(L2_ASSET_ROUTER_ADDR).bridgehubRecoverBaseToken(
                destChainId, destBaseTokenAssetId, c.from, c.value);
        }
    }

The pin dispatched on the call's *target* (`IAtomicRecoverable(c.to).recoverAtomicCall`) and
reverted when nothing recovered (`ManagerNoRecoverableCalls`).  At head the dispatch key is the
call's *sender*, the return value is ignored, and a claim that recovers nothing succeeds
(`:287-288`, "the state transition must not be blocked").  There is still no `try/catch`: a revert in
any attempted recovery rolls back the whole `claimRefund` (`protocol-docs/atomicity/recovery.md:58-68`).

`claimRefund` (`:247-262` [v35 `:250-265`]) requires the leg to be `Revertable` (`:251-254`), sets it
`Reverted` (`:257`), then runs `_recoverBundle` (`:259`).

## The router's refund (`bridge/asset-router/L2AssetRouter.sol:275-309` [v35 `:269-303`])

    function recoverAtomicCall(uint256 _destChainId, bytes calldata _callData)
        external onlyAtomicFlowManager nonReentrant returns (bool recovered) {
        require(_destChainId != L1_CHAIN_ID, RecoverToL1NotSupported());                  // :281
        if (_callData.length < 4 || bytes4(_callData[:4]) != AssetRouterBase.finalizeDeposit.selector) {
            return false;                                                                 // :290-292
        }
        (, bytes32 assetId, bytes memory mintData) = abi.decode(_callData[4:], (uint256, bytes32, bytes));
        address assetHandler = assetHandlerAddress[assetId];                              // :305
        require(assetHandler != address(0), AssetHandlerDoesNotExist(assetId));           // :306
        IL2AssetHandler(assetHandler).bridgeRecoverFailedTransfer(_destChainId, assetId, mintData);
        return true;
    }

The handler is read from the mutable routing table at CLAIM time.  The burn used the handler
registered at SEND time (`AssetRouterBase._burn`, `bridge/asset-router/AssetRouterBase.sol:303-331`).
Upstream accepts the gap as known issue 5 (`protocol-docs/atomicity/security.md:149-156`) and warns on
both writers (`L2AssetRouter.sol:196-203, 212-214`).

`bridgehubRecoverBaseToken` (`L2AssetRouter.sol:320-334` [v35 `:314-328`]) is manager-only, rejects an
L1 destination (`:326`), rebuilds the mint data `encodeBridgeMintData(_receiver, _receiver,
address(0), _amount, "")` (`:332`) and calls the vault's `bridgeRecoverFailedTransfer` (`:333`).

## The send side (`interop/InteropCenter.sol`)

`_processCallStarter` (`:767-824`) builds every bundle call:

* indirect starter: `from: recipientAddress` (`:812` [v35 `:820`]), the starter's recipient, which
  `_buildInteropBundle` pins to `L2_ASSET_ROUTER_ADDR` (`IndirectCallOnlyToAssetRouter`, `:664-667`),
  with `interopCallValue` forced to zero (`IndirectCallCannotCarryValue`, `:673-676`).  The data is
  what the router's `initiateIndirectCall` returned (`L2AssetRouter.sol:337-367`): through
  `_bridgehubDepositNonBaseTokenAsset` (`AssetRouterBase.sol:140-182`), `_burn` and `_requestToBridge`
  (`:340-356`) it is `finalizeDeposit(block.chainid, assetId, bridgeMintCalldata)`
  (`getDepositCalldata`, `:365-371`), `bridgeMintCalldata` being what the burn handler's `bridgeBurn`
  returned (`:324-330`), and `to` is `L2_ASSET_ROUTER_ADDR` (`:360-362`);
* direct starter: `from: msg.sender` (`:821` [v35 `:829`]), `to`, `data` and `value` as supplied.

So `from == L2_ASSET_ROUTER_ADDR` selects exactly the router-produced calls, provided the router
never itself calls `sendBundle`/`sendMessage` (the manager's comment, `AtomicFlowManager.sol:301-305`;
no contract under `bridge/` calls either at `3605e82`).  That proviso is the premise
`msgSender ≠ cfg.router` of the send-side statements.

## What is modelled, and what is not

* Bundle call data is typed (`SOL-ABI`), as in the pin model, except that the `finalizeDeposit`
  payload is now raw bytes: the handler, not the router, decodes it ("the mint data is in its own
  format", `L2AssetRouter.sol:297-299`).  The vault decodes it with `HeadConfig.decodeMint`.
* The vault's refund is the pin model's `AtomicRecovery.ntvRecover`.  `bridgeRecoverFailedTransfer`
  (`bridge/ntv/NativeTokenVaultBase.sol:193-213`) is unchanged at head; the new L2 override of
  `_disburseFailedTransfer` (`bridge/ntv/L2NativeTokenVault.sol:235-258`: the tracker's
  `assertRecoveryIsAccountingNeutral`, `bridge/asset-tracker/L2AssetTracker.sol:176-185`, and the
  base-token branch `L2_BASE_TOKEN_HOLDER.recoverBaseToken`) acts through the vault's external
  effects, which the pin model leaves as universally quantified hooks (`DEP-FRAME`).
* The code at every other address, as it answers `IL2AssetHandler.bridgeRecoverFailedTransfer`
  (`bridge/interfaces/IL2AssetHandler.sol:14-23`), is an arbitrary function `HandlerCode` of the
  world; it may write anything, router maps included.  Results that need it to leave something alone
  say so as a premise.
* Router-map writes between the burn and the claim are the steps of `AllWriters` (`AStep`, `ARun`).
  That model is at the pin; the writers of `assetHandlerAddress` are the same at head
  (`AssetRouterBase.sol:65-77, 267-283, 289-292`; `L2AssetRouter.sol:155-166, 204-210, 215-220`).
* One `L1_CHAIN_ID` serves the router (`L2AssetRouter.sol:51`) and the manager
  (`AtomicFlowManager.sol:64`): both are set by the upgrader to the L1 chain id (`OPS-CONFIG`).
* `nonReentrant`, events and the bundle-hash check of `claimRefund` (`:248-249`) are not modelled:
  the claim takes the decoded bundle.
-/

namespace Contracts.AssetRouter.AtomicRecoveryAtHead

open AttackVectors.RecoveryLimits (Outcome LegState)

/-- The 160-bit addresses of the vault's mint data (`AtomicRecovery.Addr160`). -/
abbrev Addr160 := AtomicRecovery.Addr160

/-- Decoded bridge-mint data (`AtomicRecovery.MintData`). -/
abbrev MintData := AtomicRecovery.MintData

/-- Opaque bytes. -/
abbrev Bytes := AtomicRecovery.Bytes

/-- What a refund reads and writes on the source chain (`AtomicRecovery.World`): the router's maps,
the vault's registry, the vault's pause flag and the rest of the world `X`. -/
abbrev World (X : Type) := AtomicRecovery.World X

/-! ## Configuration -/

/-- The pin model's fixed addresses and decoders, plus what the head code adds. -/
structure HeadConfig extends AtomicRecovery.Config where
  /-- `L1_CHAIN_ID` (`L2AssetRouter.sol:51`, `AtomicFlowManager.sol:64`). -/
  l1Chain : Chain
  /-- `DataEncoding.decodeBridgeMintData` on a `finalizeDeposit` call's inner bytes, as the vault
  runs it (`NativeTokenVaultBase.sol:199-200`); `none` when it reverts. -/
  decodeMint : Bytes → Option MintData

/-! ## Bundle calls -/

/-- The `data` of one bundle call, as the head `recoverAtomicCall` parses it
(`L2AssetRouter.sol:290-296`). -/
inductive HeadCallData where
  /-- The `finalizeDeposit` selector, and `abi.decode(_callData[4:], (uint256, bytes32, bytes))`
  succeeds.  `transferData` is the inner bytes, passed on undecoded. -/
  | finalizeDeposit (sourceChain : Chain) (assetId : AssetId) (transferData : Bytes)
  /-- The `finalizeDeposit` selector, but the outer `abi.decode` reverts. -/
  | malformedFinalizeDeposit
  /-- Shorter than four bytes, or any other selector. -/
  | other

/-- One `InteropCall` (`common/Messaging.sol:241-248`).  `version` and `shadowAccount` play no part in
recovery. -/
structure HeadCall where
  /-- `InteropCall.to`.  Recovery no longer reads it. -/
  target : Address
  /-- `InteropCall.from`: the router for a router-produced call, the sending account for a direct
  call (`InteropCenter.sol:812, 821`).  Recovery dispatches on it. -/
  sender : Address
  /-- `InteropCall.value`. -/
  value : UInt256
  /-- `InteropCall.data`. -/
  data : HeadCallData

/-- The fields of an `InteropBundle` (`common/Messaging.sol:269-277`) that recovery reads. -/
structure HeadBundle where
  /-- `destinationChainId`. -/
  destChain : Chain
  /-- `destinationBaseTokenAssetId`: the asset a direct call's value is refunded in. -/
  destBaseTokenAssetId : AssetId
  /-- `calls`, in order. -/
  calls : List HeadCall

/-- The bundle call an indirect starter produces (see the header): to and from the router, value
zero, data `finalizeDeposit(block.chainid, assetId, bridgeMintCalldata)` with `mintBytes` the bytes the
burn handler's `bridgeBurn` returned. -/
def routerCallAtHead (cfg : HeadConfig) (a : AssetId) (mintBytes : Bytes) : HeadCall :=
  ⟨cfg.router, cfg.router, 0, .finalizeDeposit cfg.thisChain a mintBytes⟩

/-- The bundle call a direct starter produces (`InteropCenter.sol:814-822`): `to`, `data` and `value`
as the sender supplied them, `from` the sender. -/
def directCallAtHead (target sender : Address) (value : UInt256) (data : HeadCallData) : HeadCall :=
  ⟨target, sender, value, data⟩

/-! ## The send side -/

/-- A call starter as `_processCallStarter` receives it, after `_buildInteropBundle`'s checks
(`InteropCenter.sol:644-686`). -/
inductive HeadStarter where
  /-- A direct starter: recipient, payload, `interopCallValue`. -/
  | direct (recipient : Address) (data : HeadCallData) (value : UInt256)
  /-- An indirect starter, pinned to the router (`:664-667`) with zero `interopCallValue`
  (`:673-676`): the router's `initiateIndirectCall` burned asset `assetId`, and the burn handler
  returned `mintBytes`. -/
  | indirect (assetId : AssetId) (mintBytes : Bytes)

/-- `_processCallStarter` (`InteropCenter.sol:767-824`) for a send by `msgSender`. -/
def processCallStarterAtHead (cfg : HeadConfig) (msgSender : Address) : HeadStarter → HeadCall
  | .direct recipient data value => directCallAtHead recipient msgSender value data
  | .indirect a mintBytes => routerCallAtHead cfg a mintBytes

/-- The router's maps right after `_burn` for asset `a` from maps `R`
(`AssetRouterBase.sol:312-321`).  An unset handler is registered as the vault by
`tryRegisterTokenFromBurnData` (`NativeTokenVaultBase.sol:321-335`), which registers through
`_unsafeRegisterNativeToken` → `setAssetHandlerAddressThisChain` (`:492-499`) and requires the id it
registered to be `a` (`:334`): handler and tracker of `a` become the vault.  A set handler is left as
it is.  So the handler at `a` afterwards is `AtomicRecovery.burnHandler`, the one `bridgeBurn` ran
on. -/
def burnRouter (cfg : AtomicRecovery.Config) (R : Router) (a : AssetId) : Router :=
  if R.handler a = 0 then ⟨upd R.handler a cfg.ntv, upd R.tracker a cfg.ntv⟩ else R

/-! ## The refund -/

variable {X : Type}

/-- The code at every address other than the vault, as it answers
`IL2AssetHandler(h).bridgeRecoverFailedTransfer(chainId, assetId, data)` called by the router:
`code h w chainId assetId data`, `none` a revert.  Arbitrary. -/
abbrev HandlerCode (X : Type) :=
  Address → World X → Chain → AssetId → Bytes → Option (World X)

/-- `IL2AssetHandler(h).bridgeRecoverFailedTransfer(chainId, assetId, data)` called by the router
with no value (`L2AssetRouter.sol:307`).  The vault runs the pin model's refund on the decoded mint
data; every other address runs `code`. -/
def handlerRecover (enc : AssetIdOf) (cfg : HeadConfig) (hk : AtomicRecovery.Hooks X)
    (code : HandlerCode X) (h : Address) (w : World X) (chainId : Chain) (a : AssetId)
    (data : Bytes) : Option (World X) :=
  if h = cfg.ntv then
    AtomicRecovery.ntvRecover enc cfg.toConfig hk w cfg.router 0 chainId a (cfg.decodeMint data)
  else code h w chainId a data

/-- `L2AssetRouter.recoverAtomicCall(destChainId, callData)` at head, called by `caller`
(`L2AssetRouter.sol:275-309`): `none` is a revert, `some (w', b)` returns `b`. -/
def recoverAtomicCallAtHead (enc : AssetIdOf) (cfg : HeadConfig) (hk : AtomicRecovery.Hooks X)
    (code : HandlerCode X) (w : World X) (caller : Address) (destChainId : Chain)
    (d : HeadCallData) : Option (World X × Bool) :=
  -- onlyAtomicFlowManager (`:278`, `:135-138`)
  if caller ≠ cfg.manager then none else
  -- require(_destChainId != L1_CHAIN_ID, RecoverToL1NotSupported()) (`:281`)
  if destChainId = cfg.l1Chain then none else
  match d with
  -- not a `finalizeDeposit`: `return false` (`:290-292`)
  | .other => some (w, false)
  -- the outer `abi.decode` reverts (`:296`)
  | .malformedFinalizeDeposit => none
  -- `assetHandlerAddress[assetId]`, nonzero, then its `bridgeRecoverFailedTransfer` (`:305-308`)
  | .finalizeDeposit _ a data =>
    if w.router.handler a = 0 then none else
    (handlerRecover enc cfg hk code (w.router.handler a) w destChainId a data).map
      fun w' => (w', true)

/-- A 256-bit word read as a 160-bit address: its low 160 bits.  Call senders are addresses
(`InteropCall.from`), carried as words in the router model; on every real address this inverts
`NativeTokenVaultBase.widen`. -/
def narrow (x : Address) : Addr160 := ⟨x.val % 2 ^ 160, Nat.mod_lt _ (by positivity)⟩

/-- The mint data `bridgehubRecoverBaseToken` builds, `encodeBridgeMintData(_receiver, _receiver,
address(0), _amount, "")` (`L2AssetRouter.sol:332`), as the vault decodes it (`SOL-ABI`). -/
def baseRefundMint (receiver : Address) (amount : UInt256) : MintData :=
  ⟨narrow receiver, narrow receiver, 0, amount, []⟩

/-- `L2AssetRouter.bridgehubRecoverBaseToken(chainId, assetId, receiver, amount)` called by `caller`
(`L2AssetRouter.sol:320-334`): manager-only (`:325`), no L1 destination (`:326`), then the vault's
`bridgeRecoverFailedTransfer` with the rebuilt mint data, called by the router with no value
(`:332-333`). -/
def bridgehubRecoverBaseTokenAtHead (enc : AssetIdOf) (cfg : HeadConfig)
    (hk : AtomicRecovery.Hooks X) (w : World X) (caller : Address) (chainId : Chain)
    (a : AssetId) (receiver : Address) (amount : UInt256) : Option (World X) :=
  if caller ≠ cfg.manager then none else
  if chainId = cfg.l1Chain then none else
  AtomicRecovery.ntvRecover enc cfg.toConfig hk w cfg.router 0 chainId a
    (some (baseRefundMint receiver amount))

/-! ## The manager's refund loop -/

/-- One iteration of `_recoverBundle`'s loop (`AtomicFlowManager.sol:300-320`), on the state the
earlier iterations left.  The two `if`s of the source are exclusive, so they are an `if … else if`.
The `Bool` says whether something was reversed; it is bookkeeping for the statements only, since the
manager ignores `recoverAtomicCall`'s return value (`:310-311`). -/
def recoverCallAtHead (enc : AssetIdOf) (cfg : HeadConfig) (hk : AtomicRecovery.Hooks X)
    (code : HandlerCode X) (destChainId : Chain) (destBase : AssetId) (w : World X)
    (c : HeadCall) : Option (World X × Bool) :=
  if c.sender = cfg.router then
    recoverAtomicCallAtHead enc cfg hk code w cfg.manager destChainId c.data
  else if c.value ≠ 0 then
    (bridgehubRecoverBaseTokenAtHead enc cfg hk w cfg.manager destChainId destBase c.sender
      c.value).map fun w' => (w', true)
  else some (w, false)

/-- `_recoverBundle`'s loop: the calls in order, each on the state the previous one left, no
`try/catch`; `some (w, n)` counts the calls whose iteration reversed something. -/
def recoverBundleAtHead (step : World X → HeadCall → Option (World X × Bool)) :
    World X → List HeadCall → Option (World X × ℕ)
  | w, [] => some (w, 0)
  | w, c :: cs =>
    match step w c with
    | none => none
    | some (w', b) =>
      match recoverBundleAtHead step w' cs with
      | none => none
      | some (w'', n) => some (w'', (if b then 1 else 0) + n)

/-- `AtomicFlowManager.claimRefund` at head for one leg with decoded bundle `b`
(`AtomicFlowManager.sol:247-262`): enabled only on a `Revertable` leg (`:251-254`), the leg set
`Reverted` (`:257`), then `_recoverBundle`: no L1 destination (`:296`) and the loop.  No
`recovered == 0` check.  `none` is a revert of the whole transaction, so the leg stays `Revertable`
and nothing the loop did persists.  `step dest base` is the per-call iteration for the bundle's
destination chain and destination base-token asset. -/
def claimRefundAtHead (cfg : HeadConfig)
    (step : Chain → AssetId → World X → HeadCall → Option (World X × Bool)) (s : LegState)
    (w : World X) (b : HeadBundle) : Option (LegState × World X) :=
  if s ≠ LegState.Revertable then none else
  if b.destChain = cfg.l1Chain then none else
  (recoverBundleAtHead (step b.destChain b.destBaseTokenAssetId) w b.calls).map
    fun p => (LegState.Reverted, p.1)

/-- The outcomes the loop produces, on the threaded state: it stops at the first revert.  A call
whose iteration reversed nothing (a declined router call, a zero-value direct call) is `declined`. -/
def outcomesAtHead (step : World X → HeadCall → Option (World X × Bool)) :
    World X → List HeadCall → List Outcome
  | _, [] => []
  | w, c :: cs =>
    match step w c with
    | none => [Outcome.reverts]
    | some (w', b) => (if b then Outcome.recovered else Outcome.declined) :: outcomesAtHead step w' cs

/-! ## Handler rotation between the burn and the claim -/

/-- Call `op` of the router-map writers (`AllWriters.Op`) writes a handler other than `h₀` at
asset `a`.  `register` (`setAssetHandlerAddressThisChain`), `counterpartSet`
(`setAssetHandlerAddress`) and `seed` (`initL2`) write a given handler at their target.  The
fallback of `_finalizeDeposit` writes only at an unset handler, and a tracker write moves no
handler, so neither ever rotates a live route. -/
def Rotates (K : AllWriters.Cfg) (a : AssetId) (h₀ : Address) : AllWriters.Op → Prop
  | .register caller d h => writtenId K.enc K.thisChain K.ntv K.ntvAddr caller d = a ∧ h ≠ h₀
  | .finalize _ => False
  | .seed => K.seedId = a ∧ K.ntv ≠ h₀
  | .counterpartSet a' h => a' = a ∧ h ≠ h₀
  | .setTracker _ _ => False

/-- No write between the burn and the claim rotates asset `a` away from `h₀`. -/
def NoRotation (K : AllWriters.Cfg) (a : AssetId) (h₀ : Address) (ops : List AllWriters.Op) :
    Prop :=
  ∀ op ∈ ops, ¬ Rotates K a h₀ op

/-! ## Frame predicates used by the statements -/

/-- The other handlers' code never re-points asset `a`. -/
def CodeKeepsHandlerAt (a : AssetId) (code : HandlerCode X) : Prop :=
  ∀ h w chainId b data w', code h w chainId b data = some w' → w'.router.handler a = w.router.handler a

/-- `h`'s refund of asset `a` reverts in every world whose routing table points `a` at `h`: for the
vault, an asset it rejects; for any other address, code that does not implement
`bridgeRecoverFailedTransfer` for `a` (`IL2AssetHandler.sol:11-13`). -/
def RecoveryRevertsAt (enc : AssetIdOf) (cfg : HeadConfig) (hk : AtomicRecovery.Hooks X)
    (code : HandlerCode X) (h : Address) (a : AssetId) : Prop :=
  ∀ w chainId data, w.router.handler a = h → handlerRecover enc cfg hk code h w chainId a data = none

/-- The bundle has a router-produced call on asset `a`: from the router, `finalizeDeposit` data on
`a`. -/
def HasRouterCallOnAtHead (cfg : HeadConfig) (a : AssetId) (calls : List HeadCall) : Prop :=
  ∃ c ∈ calls, c.sender = cfg.router ∧ ∃ src data, c.data = .finalizeDeposit src a data

end Contracts.AssetRouter.AtomicRecoveryAtHead
