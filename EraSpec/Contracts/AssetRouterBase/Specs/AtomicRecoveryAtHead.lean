import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery
import EraSpec.Contracts.AssetRouterBase.Specs.AllWriters

/-!
# Model at head: atomic recovery dispatches on `InteropCall.from` and routes to the asset's handler

Source: era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`.  Paths are
relative to `l1-contracts/contracts/`; `protocol-docs/` is at the repository root.  Every line cited
below is the same at the earlier v35 pin `d9f678900e1bc8286412b78f56d4a9f443983c29` (no cited file
changed between the two).  The modelled functions are also the same at `main`
`70096e2ea6eeb5373992e178064c4b26dcf6436a` (and at `3605e82db`, against which this topic was first
written; no cited file changed between those two), up to line shifts and renames
(`_nativeTokenVaultAddr` → `_getNativeTokenVaultAddr`, `_atomicFlowManagerAddr` →
`_getAtomicFlowManagerAddr`); the vault's token deployment differs (system `ContractDeployer` at
`main`, `CREATE2` at v35) but is the abstract `deploy` hook here.  Main lines of the central
functions: `AtomicFlowManager.sol` `claimRefund` `:247-262`, `_recoverBundle` `:289-322`;
`L2AssetRouter.sol` `recoverAtomicCall` `:275-309`, `bridgehubRecoverBaseToken` `:320-334`;
`L2NativeTokenVault.sol` `_disburseFailedTransfer` `:235-258`; `InteropCenter.sol`
`_processCallStarter` `:767-824`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.AtomicRecoveryAtHead` and proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecoveryAtHead`.

The pin model `EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery` (`c67894b9`) is unchanged and
still describes the pin.  This file models the code that replaced its two halves upstream: the
handler-routed `recoverAtomicCall` and the manager's dispatch on the call's local sender, together
with the removal of the `recovered == 0` rejection.

## The manager's loop (`atomic-interop/AtomicFlowManager.sol:292-325`)

    require(destChainId != L1_CHAIN_ID, RecoverToL1NotSupported());                       // :299
    bytes32 destBaseTokenAssetId = _bundle.destinationBaseTokenAssetId;
    for (uint256 i = 0; i < callsLen; ++i) {
        InteropCall memory c = _bundle.calls[i];
        if (c.from == L2_ASSET_ROUTER_ADDR) {                                                // :312
            IAtomicRecoverable(c.from).recoverAtomicCall(destChainId, c.data);              // result ignored
        }
        if (c.from != L2_ASSET_ROUTER_ADDR && c.value != 0) {                                // :316
            IAssetRouterShared(L2_ASSET_ROUTER_ADDR).bridgehubRecoverBaseToken(
                destChainId, destBaseTokenAssetId, c.from, c.value);
        }
    }

The pin dispatched on the call's *target* (`IAtomicRecoverable(c.to).recoverAtomicCall`) and
reverted when nothing recovered (`ManagerNoRecoverableCalls`).  At head the dispatch key is the
call's *sender*, the return value is ignored, and a claim that recovers nothing succeeds
(`:290-291`, "the state transition must not be blocked").  There is still no `try/catch`: a revert in
any attempted recovery rolls back the whole `claimRefund` (`protocol-docs/atomicity/recovery.md:59-69`).

`claimRefund` (`:250-265`) requires the leg to be `Revertable` (`:254-257`), sets it `Reverted`
(`:260`), then runs `_recoverBundle` (`:262`).

## The router's refund (`bridge/asset-router/L2AssetRouter.sol:269-303`)

    function recoverAtomicCall(uint256 _destChainId, bytes calldata _callData)
        external onlyAtomicFlowManager nonReentrant returns (bool recovered) {
        require(_destChainId != L1_CHAIN_ID, RecoverToL1NotSupported());                  // :275
        if (_callData.length < 4 || bytes4(_callData[:4]) != AssetRouterBase.finalizeDeposit.selector) {
            return false;                                                                 // :284-286
        }
        (, bytes32 assetId, bytes memory mintData) = abi.decode(_callData[4:], (uint256, bytes32, bytes));
        address assetHandler = assetHandlerAddress[assetId];                              // :299
        require(assetHandler != address(0), AssetHandlerDoesNotExist(assetId));           // :300
        IL2AssetHandler(assetHandler).bridgeRecoverFailedTransfer(_destChainId, assetId, mintData);
        return true;
    }

The handler is read from the mutable routing table at CLAIM time.  The burn used the handler
registered at SEND time (`AssetRouterBase._burn`, `bridge/asset-router/AssetRouterBase.sol:303-331`).
Upstream documents the gap as known issue 5 (`protocol-docs/atomicity/security.md:149-156`) and warns on
both writers (`L2AssetRouter.sol:190-197, 206-208`).

`bridgehubRecoverBaseToken` (`L2AssetRouter.sol:314-328`) is manager-only (`:319`), rejects an L1
destination (`:320`), rebuilds the mint data `encodeBridgeMintData(_receiver, _receiver, address(0),
_amount, "")` (`:326`) and calls the vault's `bridgeRecoverFailedTransfer` (`:327`), whatever handler
the asset has.

## The send side (`interop/InteropCenter.sol`)

`_processCallStarter` (`:776-832`) builds every bundle call:

* indirect starter: `from: recipientAddress` (`:820`), the starter's recipient, which
  `_buildInteropBundle` pins to `L2_ASSET_ROUTER_ADDR` (`IndirectCallOnlyToAssetRouter`, `:665-668`),
  with `interopCallValue` forced to zero (`IndirectCallCannotCarryValue`, `:674-677`).  The data is
  what the router's `initiateIndirectCall` returned (`L2AssetRouter.sol:331-361`): through
  `_bridgehubDepositNonBaseTokenAsset` (`AssetRouterBase.sol:140-183`), `_burn` and `_requestToBridge`
  (`:340-356`) it is `finalizeDeposit(block.chainid, assetId, bridgeMintCalldata)`
  (`getDepositCalldata`, `:365-371`), `bridgeMintCalldata` being what the burn handler's `bridgeBurn`
  returned (`:324-330`), and for a destination other than L1 its `to` is `L2_ASSET_ROUTER_ADDR`
  (`L2AssetRouter.sol:355`, `AssetRouterBase.sol:351, 360-362`);
* direct starter: `from: msg.sender` (`:829`), `to`, `data` and `value` as supplied (`:823-830`).

So `from == L2_ASSET_ROUTER_ADDR` selects exactly the router-produced calls, provided the router
never itself calls `sendBundle`/`sendMessage` (the manager's comment, `AtomicFlowManager.sol:304-306`;
no contract under `bridge/` calls either at `b17415d20`).  That proviso is the premise
`msgSender ≠ cfg.router` of the send-side statements.  An atomic bundle cannot be sent to L1
(`_sendBundle`, `InteropCenter.sol:552-553`, `AtomicBundleToL1NotSupported`); the send side beyond
`_processCallStarter` is not modelled.

## What is modelled, and what is not

* Bundle call data is typed (`SOL-ABI`), as in the pin model, except that the `finalizeDeposit`
  payload is now raw bytes: the handler, not the router, decodes it (the router's comment,
  `L2AssetRouter.sol:291-292`).  The vault decodes it with `HeadConfig.decodeMint`.
* The vault's refund is `vaultRecoverAtHead`.  `bridgeRecoverFailedTransfer`
  (`bridge/ntv/NativeTokenVaultBase.sol:195-214`) is the pin's, but on L2 it now runs the override of
  `_disburseFailedTransfer` (`bridge/ntv/L2NativeTokenVault.sol:204-227`), which the pin did not have:

      L2_ASSET_TRACKER.assertRecoveryIsAccountingNeutral(_assetId, _chainId);            // :213
      if (_assetId == BASE_TOKEN_ASSET_ID) {                                             // :214
          L2_BASE_TOKEN_HOLDER.recoverBaseToken(_receiver, _amount, _chainId);           // :215
          return;
      }
      super._disburseFailedTransfer(...);                                                // :218-226

  `assertRecoveryIsAccountingNeutral` (`bridge/asset-tracker/L2AssetTracker.sol:176-185`) is a view:
  it rejects an L1 destination (`:179`), and for the chain's own base token it rejects an asset the
  vault records as native to this chain (`:182-184`).  The base `_disburseFailedTransfer`
  (`NativeTokenVaultBase.sol:264-286`) has the pin's body; the pin's L2 override of
  `_ensureAndSaveTokenDeployed` is now the base function (`:515-529`, the same two steps); and
  `_withdrawFunds` and `_handleBridgeFromChain` (`L2NativeTokenVault.sol:196-199, 285-293`) are the
  pin's.  So for every asset other than this chain's `BASE_TOKEN_ASSET_ID` and every non-L1
  destination the refund is modelled by the pin model's `AtomicRecovery.ntvRecover`
  (`Properties.VaultRecoverAtHeadIsPinRefundOffBaseToken`), with the pin model's hooks and its
  boundaries (`MODEL-ATOMIC-RECOVERY`).  For the chain's own base token it is the base-token holder's
  `recoverBaseToken(receiver, amount, chainId)` (`l2-system/BaseTokenHolder.sol:79-87`), the new hook
  `HeadHooks.recoverBase`.  At send, `InteropCenter._ensureCorrectTotalValue` (`:418-460`) passes a
  bundle's call value to the base-token holder when the destination's base token is this chain's, and
  to the router's `bridgehubDepositBaseToken` otherwise; that is not modelled.
* The vault's other external effects are the pin model's universally quantified hooks
  (`AtomicRecovery.Hooks`, `DEP-FRAME`).  Their types, and that of `recoverBase`, confine their
  writes to the rest of the world: the code a token transfer or `recoverBase`'s native transfer may
  run at the receiver is assumed not to write the router's maps, the vault's registry or its pause
  flag (`DEP-FRAME`).
* The code at every other address, as it answers `IL2AssetHandler.bridgeRecoverFailedTransfer`
  (`bridge/interfaces/IL2AssetHandler.sol:14-23`), is an arbitrary function `HandlerCode` of the
  world; it may write anything, router maps included.  Results that need it to leave something alone
  say so as a premise.
* Router-map writes between the burn and the claim are the steps of `AllWriters` (`AStep`, `ARun`).
  That model is at the pin; the writers of `assetHandlerAddress` are the same at head
  (`AssetRouterBase.sol:65-77, 267-283, 289-292`; `L2AssetRouter.sol:154-163, 198-204, 209-214`), and
  no contract inherits either router.
* Configuration identified across contracts (`OPS-CONFIG`): one value `HeadConfig.l1Chain` stands
  for the `L1_CHAIN_ID` slots of the router (`L2AssetRouter.sol:51`), the manager
  (`AtomicFlowManager.sol:65`) and the asset tracker (`L2AssetTracker.sol:50`), and one value
  `HeadConfig.baseAsset` for the `BASE_TOKEN_ASSET_ID` slots of the vault
  (`L2NativeTokenVault.sol:53`) and the asset tracker (`L2AssetTracker.sol:52`).  Each is a separate
  storage slot, set by the complex upgrader.
* A router-produced call's `to` is modelled as the router's own address, its value for a non-L1
  destination; for an L1 destination `initiateIndirectCall` substitutes `L1_ASSET_ROUTER`
  (`L2AssetRouter.sol:355`), and recovery rejects those.  Recovery never reads `to`
  (`Properties.CallTargetIgnoredAtHead`).
* `nonReentrant`, events, and `claimRefund`'s bundle decode and hash lookup
  (`AtomicFlowManager.sol:251-252`) are not modelled: the claim takes the decoded bundle and the
  leg's state.  Other legs' states are not modelled.
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
  /-- `L1_CHAIN_ID`: one value for the router's (`L2AssetRouter.sol:51`), the manager's
  (`AtomicFlowManager.sol:65`) and the asset tracker's (`L2AssetTracker.sol:50`) slots
  (`OPS-CONFIG`). -/
  l1Chain : Chain
  /-- `BASE_TOKEN_ASSET_ID`, this chain's base token: one value for the vault's
  (`L2NativeTokenVault.sol:53`) and the asset tracker's (`L2AssetTracker.sol:52`) slots
  (`OPS-CONFIG`). -/
  baseAsset : AssetId
  /-- `DataEncoding.decodeBridgeMintData` on a `finalizeDeposit` call's inner bytes, as the vault
  runs it (`NativeTokenVaultBase.sol:201-202`); `none` when it reverts. -/
  decodeMint : Bytes → Option MintData

/-- The vault's external effects at head: the pin model's hooks, plus the base-token holder. -/
structure HeadHooks (X : Type) extends AtomicRecovery.Hooks X where
  /-- `L2_BASE_TOKEN_HOLDER.recoverBaseToken(to, amount, toChainId)` called by the vault
  (`l2-system/BaseTokenHolder.sol:79-87`): nothing for a zero amount, otherwise the tracker's
  `assertBaseTokenRecoveryIsAccountingNeutral(toChainId)` and a native transfer of `amount` to `to`.
  It may revert (`none`), for instance when `to` rejects the transfer.  Its type confines writes to
  `X` (`DEP-FRAME`). -/
  recoverBase : X → Addr160 → UInt256 → Chain → Option X

/-! ## Bundle calls -/

/-- The `data` of one bundle call, as the head `recoverAtomicCall` parses it
(`L2AssetRouter.sol:284-290`). -/
inductive HeadCallData where
  /-- The `finalizeDeposit` selector, and `abi.decode(_callData[4:], (uint256, bytes32, bytes))`
  succeeds.  `transferData` is the inner bytes, passed on undecoded. -/
  | finalizeDeposit (sourceChain : Chain) (assetId : AssetId) (transferData : Bytes)
  /-- The `finalizeDeposit` selector, but the outer `abi.decode` reverts. -/
  | malformedFinalizeDeposit
  /-- Shorter than four bytes, or any other selector. -/
  | other

/-- One `InteropCall` (`common/Messaging.sol:240-247`).  `version` and `shadowAccount` play no part in
recovery. -/
structure HeadCall where
  /-- `InteropCall.to`.  Recovery does not read it. -/
  target : Address
  /-- `InteropCall.from`: the router for a router-produced call, the sending account for a direct
  call (`InteropCenter.sol:820, 829`).  Recovery dispatches on it. -/
  sender : Address
  /-- `InteropCall.value`. -/
  value : UInt256
  /-- `InteropCall.data`. -/
  data : HeadCallData

/-- The fields of an `InteropBundle` (`common/Messaging.sol:268-276`) that recovery reads. -/
structure HeadBundle where
  /-- `destinationChainId`. -/
  destChain : Chain
  /-- `destinationBaseTokenAssetId`: the asset a direct call's value is refunded in. -/
  destBaseTokenAssetId : AssetId
  /-- `calls`, in order. -/
  calls : List HeadCall

/-- The bundle call an indirect starter produces for a non-L1 destination (see the header): to and
from the router, value zero, data `finalizeDeposit(block.chainid, assetId, bridgeMintCalldata)` with
`mintBytes` the bytes the burn handler's `bridgeBurn` returned. -/
def routerCallAtHead (cfg : HeadConfig) (a : AssetId) (mintBytes : Bytes) : HeadCall :=
  ⟨cfg.router, cfg.router, 0, .finalizeDeposit cfg.thisChain a mintBytes⟩

/-- The bundle call a direct starter produces (`InteropCenter.sol:823-830`): `to`, `data` and `value`
as the sender supplied them, `from` the sender. -/
def directCallAtHead (target sender : Address) (value : UInt256) (data : HeadCallData) : HeadCall :=
  ⟨target, sender, value, data⟩

/-! ## The send side -/

/-- A call starter as `_processCallStarter` receives it, after `_buildInteropBundle`'s checks
(`InteropCenter.sol:645-678`). -/
inductive HeadStarter where
  /-- A direct starter: recipient, payload, `interopCallValue`. -/
  | direct (recipient : Address) (data : HeadCallData) (value : UInt256)
  /-- An indirect starter, pinned to the router (`:665-668`) with zero `interopCallValue`
  (`:674-677`): the router's `initiateIndirectCall` burned asset `assetId`, and the burn handler
  returned `mintBytes`. -/
  | indirect (assetId : AssetId) (mintBytes : Bytes)

/-- `_processCallStarter` (`InteropCenter.sol:776-832`) for a send by `msgSender`, to a destination
other than L1. -/
def processCallStarterAtHead (cfg : HeadConfig) (msgSender : Address) : HeadStarter → HeadCall
  | .direct recipient data value => directCallAtHead recipient msgSender value data
  | .indirect a mintBytes => routerCallAtHead cfg a mintBytes

/-- The router's maps right after `_burn` for asset `a` from maps `R`
(`AssetRouterBase.sol:312-321`).  An unset handler is registered as the vault by
`tryRegisterTokenFromBurnData` (`NativeTokenVaultBase.sol:321-335`), which registers through
`_unsafeRegisterNativeToken` → `setAssetHandlerAddressThisChain` (`:492-499`) and requires the id it
registered to be `a` (`:334`): handler and tracker of `a` become the vault.  (The vault's
`encodeNTVAssetId(block.chainid, token)` and the router's `encodeAssetId(block.chainid,
bytes32(token), L2_NATIVE_TOKEN_VAULT_ADDR)` hash the same words, `common/libraries/DataEncoding.sol:125-152`.)
A set handler is left as it is.  So the handler at `a` afterwards is `AtomicRecovery.burnHandler`, the
one `bridgeBurn` ran on. -/
def burnRouter (cfg : AtomicRecovery.Config) (R : Router) (a : AssetId) : Router :=
  if R.handler a = 0 then ⟨upd R.handler a cfg.ntv, upd R.tracker a cfg.ntv⟩ else R

/-! ## The refund -/

variable {X : Type}

/-- The code at every address other than the vault, as it answers
`IL2AssetHandler(h).bridgeRecoverFailedTransfer(chainId, assetId, data)` called by the router:
`code h w chainId assetId data`, `none` a revert.  Arbitrary. -/
abbrev HandlerCode (X : Type) :=
  Address → World X → Chain → AssetId → Bytes → Option (World X)

/-- `L2NativeTokenVault.bridgeRecoverFailedTransfer(chainId, assetId, data)` at head, called by
`caller` with `msgValue`, on already decoded mint data (`none`: `decodeBridgeMintData` reverts).  The
base function's guards and decode (`NativeTokenVaultBase.sol:195-203`), then the L2 override of
`_disburseFailedTransfer` (`L2NativeTokenVault.sol:204-227`): the tracker's
`assertRecoveryIsAccountingNeutral`, the base-token branch, and otherwise the base function, modelled
by the pin model's `AtomicRecovery.ntvRecover` (which re-runs the same guards and decode, see the
header).  `none` is a revert.  It reads the vault's registry, the pause flag and the rest of the
world; the router's maps are neither read nor written. -/
def vaultRecoverAtHead (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X) (w : World X)
    (caller : Address) (msgValue : UInt256) (chainId : Chain) (a : AssetId)
    (m : Option MintData) : Option (World X) :=
  -- requireZeroValue(msg.value) onlyAssetRouter whenNotPaused (`NativeTokenVaultBase.sol:199`)
  if msgValue ≠ 0 ∨ caller ≠ cfg.router ∨ w.paused = true then none else
  -- decodeBridgeMintData (`:201-202`)
  match m with
  | none => none
  | some md =>
    -- assertRecoveryIsAccountingNeutral: no L1 destination (`L2AssetTracker.sol:179`)
    if chainId = cfg.l1Chain then none else
    if a = cfg.baseAsset then
      -- …and the base token must not be native to this chain (`L2AssetTracker.sol:182-184`)
      if w.vault.originChain a = cfg.thisChain then none else
      -- L2_BASE_TOKEN_HOLDER.recoverBaseToken(_receiver, _amount, _chainId); return (`L2NativeTokenVault.sol:214-217`)
      (hk.recoverBase w.rest md.originalCaller md.amount chainId).map fun x => { w with rest := x }
    -- super._disburseFailedTransfer (`L2NativeTokenVault.sol:218-226`)
    else AtomicRecovery.ntvRecover enc cfg.toConfig hk.toHooks w caller msgValue chainId a (some md)

/-- `IL2AssetHandler(h).bridgeRecoverFailedTransfer(chainId, assetId, data)` called by the router
with no value (`L2AssetRouter.sol:301`).  The vault runs its head refund on the decoded mint data;
every other address runs `code`. -/
def handlerRecover (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (h : Address) (w : World X) (chainId : Chain) (a : AssetId)
    (data : Bytes) : Option (World X) :=
  if h = cfg.ntv then
    vaultRecoverAtHead enc cfg hk w cfg.router 0 chainId a (cfg.decodeMint data)
  else code h w chainId a data

/-- `L2AssetRouter.recoverAtomicCall(destChainId, callData)` at head, called by `caller`
(`L2AssetRouter.sol:269-303`): `none` is a revert, `some (w', b)` returns `b`. -/
def recoverAtomicCallAtHead (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (w : World X) (caller : Address) (destChainId : Chain)
    (d : HeadCallData) : Option (World X × Bool) :=
  -- onlyAtomicFlowManager (`:272`, `:135-138`)
  if caller ≠ cfg.manager then none else
  -- require(_destChainId != L1_CHAIN_ID, RecoverToL1NotSupported()) (`:275`)
  if destChainId = cfg.l1Chain then none else
  match d with
  -- not a `finalizeDeposit`: `return false` (`:284-286`)
  | .other => some (w, false)
  -- the outer `abi.decode` reverts (`:290`)
  | .malformedFinalizeDeposit => none
  -- `assetHandlerAddress[assetId]`, nonzero, then its `bridgeRecoverFailedTransfer` (`:299-302`)
  | .finalizeDeposit _ a data =>
    if w.router.handler a = 0 then none else
    (handlerRecover enc cfg hk code (w.router.handler a) w destChainId a data).map
      fun w' => (w', true)

/-- A 256-bit word read as a 160-bit address: its low 160 bits.  Call senders are addresses
(`InteropCall.from`), carried as words in the router model; on every real address this inverts
`NativeTokenVaultBase.widen`. -/
def narrow (x : Address) : Addr160 := ⟨x.val % 2 ^ 160, Nat.mod_lt _ (by positivity)⟩

/-- The mint data `bridgehubRecoverBaseToken` builds, `encodeBridgeMintData(_receiver, _receiver,
address(0), _amount, "")` (`L2AssetRouter.sol:326`), as the vault decodes it (`SOL-ABI`). -/
def baseRefundMint (receiver : Address) (amount : UInt256) : MintData :=
  ⟨narrow receiver, narrow receiver, 0, amount, []⟩

/-- `L2AssetRouter.bridgehubRecoverBaseToken(chainId, assetId, receiver, amount)` called by `caller`
(`L2AssetRouter.sol:314-328`): manager-only (`:319`), no L1 destination (`:320`), then the vault's
`bridgeRecoverFailedTransfer` with the rebuilt mint data, called by the router with no value
(`:326-327`).  The routing table is not read. -/
def bridgehubRecoverBaseTokenAtHead (enc : AssetIdOf) (cfg : HeadConfig)
    (hk : HeadHooks X) (w : World X) (caller : Address) (chainId : Chain)
    (a : AssetId) (receiver : Address) (amount : UInt256) : Option (World X) :=
  if caller ≠ cfg.manager then none else
  if chainId = cfg.l1Chain then none else
  vaultRecoverAtHead enc cfg hk w cfg.router 0 chainId a (some (baseRefundMint receiver amount))

/-! ## The manager's refund loop -/

/-- One iteration of `_recoverBundle`'s loop (`AtomicFlowManager.sol:302-324`), on the state the
earlier iterations left.  The two `if`s of the source are exclusive, so they are an `if … else if`.
The `Bool` says whether something was reversed; it is bookkeeping for the statements only, since the
manager ignores `recoverAtomicCall`'s return value (`:313-314`). -/
def recoverCallAtHead (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
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
(`AtomicFlowManager.sol:250-265`): enabled only on a `Revertable` leg (`:254-257`), the leg set
`Reverted` (`:260`), then `_recoverBundle`: no L1 destination (`:299`) and the loop.  No
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
handler, so neither rotates a nonzero `h₀` (the statements take `h₀ ≠ 0`). -/
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
def RecoveryRevertsAt (enc : AssetIdOf) (cfg : HeadConfig) (hk : HeadHooks X)
    (code : HandlerCode X) (h : Address) (a : AssetId) : Prop :=
  ∀ w chainId data, w.router.handler a = h → handlerRecover enc cfg hk code h w chainId a data = none

/-- The bundle has a router-produced call on asset `a`: from the router, `finalizeDeposit` data on
`a`. -/
def HasRouterCallOnAtHead (cfg : HeadConfig) (a : AssetId) (calls : List HeadCall) : Prop :=
  ∃ c ∈ calls, c.sender = cfg.router ∧ ∃ src data, c.data = .finalizeDeposit src a data

end Contracts.AssetRouter.AtomicRecoveryAtHead
