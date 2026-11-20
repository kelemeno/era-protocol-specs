import EraSpec.Contracts.InteropCenter.History.Specs.Dispatch
import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryTargets
import EraSpec.Contracts.InteropHandlerBase.Specs.BundleStatusMachine

/-!
# Model: where an atomic leg's calls point, and what happens to an atomic leg sent to L1

**History: the record of the old interop pin `c67894b9`, not a claim about `b17415d20`.** The
`b17415d20` send model is `Specs/Send.lean` (namespace `Contracts.InteropCenter.Send`).

Source: the pinned era-contracts tree (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`),
`l1-contracts/contracts/`:

* `interop/InteropCenter.sol` (a bare `:N` is a line of this file);
* `bridge/asset-router/L2AssetRouter.sol`, `bridge/asset-router/AssetRouterBase.sol`;
* `atomic-interop/AtomicFlowManager.sol`, `atomic-interop/IAtomicRecoverable.sol`;
* `interop/interop-handler/InteropHandlerBase.sol`, `L1InteropHandler.sol`, `L2InteropHandler.sol`;
* `interop/IERC7786Attributes.sol`.

Two checks are read from another tree, `e561b9cc2` (the snapshot of `feat/upgrade-simplification`
that the upgrade models pin, not a successor of the pin), cited as `UPG/…`. The current heads
(`draft/v0.35.0` `b17415d20`, `main` `70096e2ea`) have the same two checks.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropCenter.History.Properties.AtomicRouting` and are proved in
`EraSpec.Contracts.InteropCenter.History.Proofs.AtomicRouting`.

## The code

The two send entry points hand `_sendBundle` (:464-586) different `AtomicSend` values:

    // sendMessage (:213-259)
    _ensureL2ToL2(recipientChainId);                                                 // :220
    (callAttributes, bundleAttributes) = parseAttributes(attributes,
        AttributeParsingRestrictions.CallAndBundleAttributes);                       // :222-225
    ... one call starter ...                                                         // :235-240
    _sendBundle(..., _atomicSend: AtomicSend({flowId: 0, lowNullifierIndex: 0, deadline: 0,
        isAtomic: false}));                                                          // :247-253

    // sendBundle (:262-327)
    _ensureValidDestination(destinationChainId, _callStarters.length);               // :275
    ...
    AtomicSend memory atomicSend = _parseAtomicSend(_bundleAttributes);              // :318
    _sendBundle(..., _atomicSend: atomicSend);                                       // :320-326

`parseAttributes` accepts the `atomicBundle` attribute, at most once, under
`CallAndBundleAttributes` and `OnlyBundleAttributes` (:843-854). So `sendMessage` accepts it and
passes `isAtomic: false` whatever it carried (:252); this is the source finding recorded in this
folder's README. `_parseAtomicSend` (:874-883) sets `isAtomic = true` exactly when the attribute is
present. `IERC7786Attributes.sol:26-28` says of the attribute: "When present, the InteropCenter does
not publish the bundle to L1; instead it appends the bundle's commit value to the interop IMT via
the AtomicFlowManager". At `UPG`, `sendMessage` passes `parseAtomicSend(attributes)` instead
(`UPG/interop/InteropCenter.sol:229-231`).

Destinations (:378-396): a bundle starts on an L2 and never targets its own chain; `sendMessage`
never targets L1; a `sendBundle` to L1 has one call. Inside `_sendBundle`, an L1-destined call must
be an indirect, zero-value call through the L2 asset router (:520-538). No check at the pin
compares the `atomicBundle` attribute with an L1 destination; `UPG/interop/InteropCenter.sol:550-551`
has `require(_destinationChainId != L1_CHAIN_ID, AtomicBundleToL1NotSupported())` for an atomic
send.

The indirect call through the router (:714-740) asks `L2AssetRouter.initiateIndirectCall`
(`L2AssetRouter.sol:299-342`), which burns the asset (`_bridgehubDeposit`) and returns

    address destinationAssetRouter = _chainId == L1_CHAIN_ID ? address(L1_ASSET_ROUTER) : request.l2Contract;
    interopCallStarter = InteropCallStarter({to: InteroperableAddress.formatEvmV1(destinationAssetRouter),
        data: request.l2Calldata, callAttributes: attributes});                     // L2AssetRouter.sol:336-341

with `request.l2Contract = _l2AssetRouterAddress(_chainId) = L2_ASSET_ROUTER_ADDR` and
`request.l2Calldata = getDepositCalldata(...) = abi.encodeCall(finalizeDeposit, (block.chainid,
assetId, bridgeMintCalldata))` (`AssetRouterBase.sol:361-376, 378-384`). The center records
`to = actualCallRecipient`, `from = the router` (:732-740).

`_dispatchBundle` (:639-659) appends an atomic bundle to the manager and publishes any other one
(`_sendBundleToL1`, :622-627). The handler entry point for an atomic bundle,
`executeAtomicBundle`, exists only in `L2InteropHandler.sol:49` ("L2->L2 only", :39); the L1 handler
(`L1InteropHandler.sol:30-94`) has the shared entry points `executeBundle`, `verifyBundle` and
`unbundleBundle` (`InteropHandlerBase.sol:86-231`). `grep -rn executeAtomicBundle` over the pinned
tree finds no other definition.

The refund (`AtomicFlowManager.sol:165-180, 219-230`) calls `IAtomicRecoverable(c.to)` on the
**source** chain: for an L1-destined leg that is the L1 asset router's address, on the L2
(`EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryTargets`).

## The inventory the L1 results rest on (checked against the pinned tree)

* L1 credits a withdrawal only through `L1AssetRouter.finalizeDeposit`, which is `onlySelf`
  (`bridge/asset-router/L1AssetRouter.sol:288-295`) and reached from `receiveMessage`, which only
  the configured L1 interop handler may call (`AssetRouterBase.sol:215-220`,
  `L1AssetRouter.sol:274-276`). `bridge/L1Nullifier.sol` has no finalization entry point.
* The L1 handler runs a bundle's calls only from `executeBundle` and `unbundleBundle`. A bundle
  leaves `Unreceived` only through `_verifyBundle` (from `verifyBundle` or a fresh `executeBundle`),
  which needs an inclusion proof of `BUNDLE_IDENTIFIER ++ bytes` sent by `L2_INTEROP_CENTER_ADDR`
  (`InteropHandlerBase.sol:296-316`): `unbundleBundle` needs `Verified` or `Unbundled`
  (`InteropHandlerBase.sol:195`). The handler's `receiveMessage` (`InteropHandlerBase.sol:334-362`)
  reaches only these three functions.
* `grep -rn 'sendToL1('` over the pinned `l1-contracts/contracts` finds one bundle publisher,
  `_sendBundleToL1` (:626); the other callers are the settlement-layer relay (`Committer.sol:419,
  540`) and DA (`RelayedSLDAValidator.sol:42`), and `L2ContractHelper.sendMessageToL1` has no
  caller outside `dev-contracts`.

## What is modelled

* **One source chain** (`Env.P`, the `Params` of `Specs/Dispatch.lean`): its center, its manager and
  the ghost dispatch log, exactly as `Dispatch`'s `State`, plus a ghost log of the entry point and
  the `atomicBundle` attribute of every dispatch (`Send`).
* **Sending** (`SysStep.send`) has `Dispatch`'s guards (salt, formation, `_validateAtomicBundle`,
  `append`'s `Unset` check) and in addition the destination and L1-withdrawal checks above, and
  the router's returned call starter (`RouterReturns`). Two switches (`Guards`) add the two `UPG`
  checks above; the pin has neither. The rest of `UPG` is not modelled. Fees, `msg.value`, pause,
  attribute parsing beyond the `atomicBundle` attribute, the indirect value equality (:723-729) and
  the Bridgehub registration check (:495-496) only reject, and are omitted. The asset id and mint
  data the router's burn produces are free.
* **One `L1_CHAIN_ID`.** `Env.l1ChainId` is the center's slot and also the router's own
  `L1_CHAIN_ID`, a separate slot (`L2AssetRouter.sol:44`, written by `updateL2`, :187); their
  agreement is `OPS-CONFIG`. `AssetRouterBase/Specs/AtomicRecoveryFaithful.lean` keeps them apart.
* **Refunds.** `authorize` moves a `Committed` leg `h` of flow `f` to `Revertable`, for any `h`
  among the flow's legs, as the loop at `AtomicFlowManager.sol:155-161` does, when some leg of the
  flow is missing: declared on this chain and not appended here (so its commit value is not in this
  chain's tree, `AttackVectors.LocalHonesty`), or declared elsewhere and absent there
  (`Env.absentElsewhere`, other chains being outside the model). The deadline and the proof bytes
  are not modelled, and `Env.flowLegs` takes a flow id to one leg list, so flow-id collisions are
  left out. Only the witnesses read the `authorize` guard; no universally quantified result does.
  `claim` is `AtomicFlowManager.claimRefund` on bytes `x`, with the recovery loop of
  `RecoveryTargets` over the decoded bundle's calls, on the code map `Env.code` and the call
  semantics `Env.sem` (premise `VmCall` where a result needs it); recovery acts on the world `W`.
  A recovery target that re-enters the center or the manager is treated as in `Dispatch`: the
  claim's write precedes the loop (`AtomicFlowManager.sol:175`). `env` changes the world
  arbitrarily (other transactions).
* **Destinations.** Each destination chain has `InteropHandlerBase.bundleStatus` and a ghost log of
  the bytes `_verifyBundle` accepted (`Handler`). `verify` and `executeFresh` need the message to be
  included from the bundle's source chain (`Env.included`, the inclusion-proof verdict) and the
  bundle's destination to be this chain; `executeVerified` and `unbundle` need no proof;
  `executeAtomic` exists only where the handler has `executeAtomicBundle` (`atomicEntry`), behind
  the abstract flow gate `Env.finalized`. Execution-address and unbundler permissions, versions,
  pause and the base-token asset id check only reject, and are omitted. A handler call nested
  through `receiveMessage` is a later step.
* **No hash or encoding premise is built in.** `Env.P.keccak`, `Env.P.enc` and `Env.dec` are
  abstract; results needing more take the run-local premise `DecodesRunBundles` (which also makes
  the encoder injective on the run's bundles, `Dispatch`'s `EncInjOn`) and return pinned
  collisions otherwise. `CenterPublishesOnlyPublicDispatches` is the named publication premise
  (`PROTO-EVIDENCE`): the only `sendToL1` of a bundle message is `_sendBundleToL1` (:622-627),
  called only in `_dispatchBundle`'s non-atomic branch (:657), and inclusion proofs are sound.
* **Token balances are not modelled.** The burn is the dispatch of a router call; its resolutions
  are execution on the destination (`finalizeDeposit` there) and a successful `claimRefund` on the
  source. The results speak of handler statuses and leg states, not of balances.
-/

namespace Contracts.InteropCenter.History.AtomicRouting

open Contracts.AtomicFlowManager (LegState AppendGuard AuthorizeGuard ClaimGuard)
open Contracts.AtomicFlowManager.RecoveryTargets (Code CallSem recoverStep claimRefund)
open AttackVectors.BundleStatusMachine (Status)

/-! ## Entry points and the `atomicBundle` attribute -/

/-- The two public send entry points. -/
inductive EntryPoint
  /-- `sendMessage(recipient, payload, attributes)` (:213-259). -/
  | sendMessage
  /-- `sendBundle(destinationChainId, callStarters, bundleAttributes)` (:262-327). -/
  | sendBundle
deriving DecidableEq

/-- The decoded `atomicBundle(bytes32 flowId, uint64 deadline, uint256 lowNullifierIndex)` attribute
(`IERC7786Attributes.sol:26-34`). -/
structure AtomicAttr where
  flowId : Word
  deadline : ℕ
  lowNullifierIndex : ℕ
deriving DecidableEq

/-- One successful send, as the ghost log records it. -/
structure Send where
  /-- The entry point the caller used. -/
  entry : EntryPoint
  /-- The `atomicBundle` attribute, if the caller passed it. `parseAttributes` accepts it at most
  once (:844), under both entry points' restrictions (:845-849). At the pin `sendMessage` never
  decodes its fields (:851-854); `attr` records what the caller passed. -/
  attr : Option AtomicAttr
  /-- What `_sendBundle` dispatched: sender, parsed starters, bundle, `AtomicSend`. -/
  dispatch : Dispatch

/-- The destination chain: `destinationChainId: _destinationChainId` (:501). -/
def Send.dest (s : Send) : Word := s.dispatch.bundle.destinationChainId

/-! ## The environment -/

/-- The deployment constants of the source chain and the oracles the destinations consult. -/
structure Env (W : Type) where
  /-- The source chain's `block.chainid`, center address, `abi.encode(InteropBundle)` and keccak. -/
  P : Params
  /-- `L1_CHAIN_ID` (:90, set by `initL2`, :199). The model also reads it as the router's own
  `L1_CHAIN_ID` (`L2AssetRouter.sol:44`, written by `updateL2`, :187), a separate slot; that the
  two agree is `OPS-CONFIG`. -/
  l1ChainId : Word
  /-- `L2_ASSET_ROUTER_ADDR` (`common/l2-helpers/L2ContractAddresses.sol:94`), a constant: the
  router's address on every L2, which the center compares starters with (:531) and the router
  returns for an L2 destination (`AssetRouterBase.sol:365, 374-376`). -/
  l2Router : Address
  /-- The router's `L1_ASSET_ROUTER` (`L2AssetRouter.sol:54`): an L1 address. -/
  l1Router : Address
  /-- `getDepositCalldata(_, assetId, assetData)` = `abi.encodeCall(finalizeDeposit, (block.chainid,
  assetId, assetData))` (`AssetRouterBase.sol:378-384`), as a function of the chain id. -/
  depositCalldata : Word → Word → List UInt8 → List UInt8
  /-- `abi.decode(_, (InteropBundle))` (`AtomicFlowManager.sol:166`, `InteropHandlerBase.sol:247`). -/
  dec : List UInt8 → Bundle
  /-- What is deployed at each address of the source chain. -/
  code : Address → Code W (List UInt8)
  /-- How `IAtomicRecoverable(c.to).recoverAtomicCall` resolves (`AtomicFlowManager.sol:225`). -/
  sem : CallSem W (List UInt8)
  /-- `included c x`: an inclusion proof verifies for the message `BUNDLE_IDENTIFIER ++ x` sent by
  `L2_INTEROP_CENTER_ADDR` on chain `c` (`InteropHandlerBase.sol:302-310`). -/
  included : Word → List UInt8 → Prop
  /-- `finalized c h`: `requireFlowFinalized(h, _)` passes on chain `c` (`L2InteropHandler.sol:83`). -/
  finalized : Word → Word → Prop
  /-- The legs `_checkFlowId` binds to a flow id: bundle hash and declared source chain
  (`AtomicFlowManager.sol:247-259`). A function, so one leg list per flow id: flow-id collisions
  are left out. Only `authorize` reads it. -/
  flowLegs : Word → List (Word × Word)
  /-- `absentElsewhere f h`: leg `h` of flow `f`, declared on another chain, is provably absent
  from that chain's tree after the deadline. -/
  absentElsewhere : Word → Word → Prop

variable {W : Type}

/-- The destination kind. -/
inductive DestKind
  | L1
  | L2
deriving DecidableEq

/-- A destination chain is L1 iff it is `L1_CHAIN_ID`. -/
def destKind (E : Env W) (c : Word) : DestKind := if c = E.l1ChainId then .L1 else .L2

/-- Whether the destination's handler has `executeAtomicBundle`: `L2InteropHandler.sol:49` does,
`L1InteropHandler.sol:30-94` does not. -/
def atomicEntry : DestKind → Bool
  | .L1 => false
  | .L2 => true

/-! ## Sending -/

/-- **WHAT THE ROUTER RETURNS.** The call the center records for an indirect starter through the
L2 asset router (`L2AssetRouter.sol:336-341`, `InteropCenter.sol:732-740`): `to` is the L1 asset
router for an L1 destination and `L2_ASSET_ROUTER_ADDR` otherwise, and `data` is
`finalizeDeposit(block.chainid, assetId, mintData)` for some asset id and mint data (those of the
router's burn, which is not modelled). -/
def RouterReturns (E : Env W) (dest : Word) (c : InteropCall) : Prop :=
  c.target = (if dest = E.l1ChainId then E.l1Router else E.l2Router) ∧
    ∃ (assetId : Word) (mintData : List UInt8), c.data = E.depositCalldata E.P.chainId assetId mintData

/-- The two checks of the other tree (`e561b9cc2`) that decide where the `atomicBundle` attribute
goes. The pin has neither. -/
structure Guards where
  /-- `_sendBundle`, under both entry points: an atomic bundle must not go to L1
  (`UPG/interop/InteropCenter.sol:550-551`). -/
  atomicNotToL1 : Bool
  /-- `sendMessage` passes the parsed `atomicBundle` attribute on
  (`UPG/interop/InteropCenter.sol:229-231`) instead of the empty `AtomicSend` (:252). -/
  messageHonoursAtomic : Bool

/-- The pinned code. -/
def pin : Guards := ⟨false, false⟩

/-- The pinned code with both checks of the other tree. -/
def upgradeTree : Guards := ⟨true, true⟩

/-- The `AtomicSend` each entry point passes to `_sendBundle`. `sendBundle`: the one
`_parseAtomicSend` decodes (:874-883), atomic iff the attribute is present. `sendMessage`: the
empty one at the pin (:252); the parsed one where `sendMessage` honours the attribute. -/
def atomicSendOf (K : Guards) : EntryPoint → Option AtomicAttr → AtomicSend
  | .sendMessage, none => ⟨0, 0, 0, false⟩
  | .sendMessage, some a =>
    bif K.messageHonoursAtomic then ⟨a.flowId, a.lowNullifierIndex, a.deadline, true⟩
    else ⟨0, 0, 0, false⟩
  | .sendBundle, none => ⟨0, 0, 0, false⟩
  | .sendBundle, some a => ⟨a.flowId, a.lowNullifierIndex, a.deadline, true⟩

/-- **THE STATE-INDEPENDENT PART OF A SUCCESSFUL SEND.** -/
structure SendShape (K : Guards) (E : Env W) (s : Send) : Prop where
  /-- The `AtomicSend` reaching `_dispatchBundle` (:252, :318). -/
  atomicSend : s.dispatch.atomicSend = atomicSendOf K s.entry s.attr
  /-- Bundles start on an L2 (:380, :392). -/
  sourceNotL1 : E.P.chainId ≠ E.l1ChainId
  /-- …and never target this chain (:381, :395). -/
  notSelf : s.dest ≠ E.P.chainId
  /-- `sendMessage` never targets L1 (:220, :392). -/
  messageNotToL1 : s.entry = .sendMessage → s.dest ≠ E.l1ChainId
  /-- `sendMessage` sends one call (:235-240). -/
  messageOneCall : s.entry = .sendMessage → s.dispatch.starters.length = 1
  /-- An L1-destined bundle has one call (:382-384). -/
  l1OneCall : s.dest = E.l1ChainId → s.dispatch.starters.length = 1
  /-- …which is an indirect, zero-value call through the L2 asset router (:520-538). -/
  l1Withdrawal : s.dest = E.l1ChainId → ∀ cs ∈ s.dispatch.starters,
    cs.callAttributes.indirectCall = true ∧ cs.target = E.l2Router ∧
      cs.callAttributes.interopCallValue = 0
  /-- The bundle `_sendBundle` built (:498-546), as in `Dispatch`. -/
  formed : FormedBy E.P s.dispatch
  /-- A call through the L2 asset router is what the router returned. -/
  routed : List.Forall₂ (fun cs c => cs.callAttributes.indirectCall = true → cs.target = E.l2Router →
    RouterReturns E s.dest c) s.dispatch.starters s.dispatch.bundle.calls
  /-- `_validateAtomicBundle` (:649), in the atomic branch. -/
  validated : s.dispatch.isAtomic = true → Validated s.dispatch.bundle
  /-- The other tree's check that an atomic bundle does not go to L1, when `K` has it. -/
  atomicNotToL1 : K.atomicNotToL1 = true → s.dispatch.isAtomic = true → s.dest ≠ E.l1ChainId

/-- **A SUCCESSFUL SEND** from source state `S`: its shape, the salt check (:479-482) and, in the
atomic branch, `append`'s `Unset` check (`AtomicFlowManager.sol:93`). -/
structure SendOk (K : Guards) (E : Env W) (S : State) (s : Send) : Prop where
  shape : SendShape K E s
  salt : S.saltUsed s.dispatch.sender s.dispatch.salt = false
  append : s.dispatch.isAtomic = true →
    AppendGuard S.manager s.dispatch.atomicSend.flowId (bundleHash E.P s.dispatch.bundle)

/-! ## Destinations -/

/-- One destination chain's handler: `bundleStatus` (`InteropHandlerBase.sol:54`) and a ghost log of
the bytes `_verifyBundle` accepted. -/
structure Handler where
  status : Word → Status
  verified : List (List UInt8)

/-- Fresh storage. -/
def Handler.init : Handler := ⟨fun _ => .Unreceived, []⟩

/-- `bundleStatus[h] = s`. -/
def setStatus (st : Word → Status) (h : Word) (s : Status) : Word → Status :=
  fun h' => if h' = h then s else st h'

/-- The hash `_getBundleData` and `claimRefund` compute for bytes `x`:
`encodeInteropBundleHash(abi.decode(x).sourceChainId, x)` (`InteropHandlerBase.sol:247-249`,
`AtomicFlowManager.sol:166-167`). -/
def handlerHash (E : Env W) (x : List UInt8) : Word := E.P.keccak (claimPreimage E.dec x)

/-- One handler transaction on destination chain `c`. -/
inductive HandlerStep (E : Env W) (c : Word) : Handler → Handler → Prop
  /-- `verifyBundle(x, proof)` (`InteropHandlerBase.sol:150-161`). -/
  | verify {H : Handler} (x : List UInt8) :
      E.included (E.dec x).sourceChainId x → (E.dec x).destinationChainId = c →
      H.status (handlerHash E x) = .Unreceived →
      HandlerStep E c H ⟨setStatus H.status (handlerHash E x) .Verified, H.verified ++ [x]⟩
  /-- `executeBundle(x, proof)` on a fresh bundle: `_verifyBundle`, then `FullyExecuted`
  (`InteropHandlerBase.sol:86-147`). -/
  | executeFresh {H : Handler} (x : List UInt8) :
      E.included (E.dec x).sourceChainId x → (E.dec x).destinationChainId = c →
      H.status (handlerHash E x) = .Unreceived →
      HandlerStep E c H ⟨setStatus H.status (handlerHash E x) .FullyExecuted, H.verified ++ [x]⟩
  /-- `executeBundle` on a verified bundle: no proof (:123). -/
  | executeVerified {H : Handler} (x : List UInt8) :
      H.status (handlerHash E x) = .Verified →
      HandlerStep E c H ⟨setStatus H.status (handlerHash E x) .FullyExecuted, H.verified⟩
  /-- `unbundleBundle(x, statuses)` (`InteropHandlerBase.sol:164-231`). -/
  | unbundle {H : Handler} (x : List UInt8) :
      H.status (handlerHash E x) = .Verified ∨ H.status (handlerHash E x) = .Unbundled →
      HandlerStep E c H ⟨setStatus H.status (handlerHash E x) .Unbundled, H.verified⟩
  /-- `executeAtomicBundle(x, finality)` (`L2InteropHandler.sol:49-100`), where it exists. -/
  | executeAtomic {H : Handler} (x : List UInt8) :
      atomicEntry (destKind E c) = true → E.finalized c (handlerHash E x) →
      (E.dec x).destinationChainId = c → H.status (handlerHash E x) = .Unreceived →
      HandlerStep E c H ⟨setStatus H.status (handlerHash E x) .FullyExecuted, H.verified⟩

/-! ## The system -/

/-- The source chain, its world, and every destination's handler. -/
structure Sys (W : Type) where
  /-- The source chain's salts, manager and dispatch log (`Specs/Dispatch.lean`). -/
  src : State
  /-- Ghost: the entry point and attribute of every dispatch, oldest first. -/
  sends : List Send
  /-- What recovery calls read and write on the source chain. -/
  world : W
  /-- Ghost: every successful `claimRefund(f, x)`, oldest first. -/
  claims : List (Word × List UInt8)
  /-- Each destination chain's handler. -/
  dst : Word → Handler

/-- Fresh storage everywhere, with world `w₀`. -/
def sysInit (w₀ : W) : Sys W := ⟨init, [], w₀, [], fun _ => Handler.init⟩

/-- The recovery loop `claimRefund(_, x)` runs: the decoded bundle's calls, its destination chain
(`AtomicFlowManager.sol:220`), on the source chain's code. -/
def refundStep (E : Env W) (x : List UInt8) : W → InteropCall → Option (W × Bool) :=
  recoverStep E.sem E.code InteropCall.target InteropCall.data (E.dec x).destinationChainId

/-- One transaction. -/
inductive SysStep (K : Guards) (E : Env W) : Sys W → Sys W → Prop
  /-- `sendMessage` or `sendBundle`, through `_sendBundle` and `_dispatchBundle`. -/
  | send {S : Sys W} (s : Send) : SendOk K E S.src s →
      SysStep K E S { S with src := S.src.afterSend E.P s.dispatch, sends := S.sends ++ [s] }
  /-- `authorizeRefund` marking the committed leg `h` of flow `f` (`AtomicFlowManager.sol:134-162`;
  the loop at :155-161 marks every committed leg of the flow, one step each here), when a leg of
  the flow is missing. -/
  | authorize {S : Sys W} (f h : Word) :
      AuthorizeGuard S.src.manager f h → h ∈ (E.flowLegs f).map Prod.fst →
      (∃ p ∈ E.flowLegs f, (p.2 = E.P.chainId ∧ S.src.manager.legState f p.1 = .Unset) ∨
        (p.2 ≠ E.P.chainId ∧ E.absentElsewhere f p.1)) →
      SysStep K E S { S with src := { S.src with manager := S.src.manager.set f h .Revertable } }
  /-- `claimRefund(f, x)` (`AtomicFlowManager.sol:165-180`), when the whole transaction succeeds. -/
  | claim {S : Sys W} (f : Word) (x : List UInt8) (w' : W) :
      claimRefund (refundStep E x) (S.src.manager.legState f (handlerHash E x)) S.world
        (E.dec x).calls = some (.Reverted, w') →
      SysStep K E S { S with
        src := { S.src with manager := S.src.manager.set f (handlerHash E x) .Reverted },
        world := w', claims := S.claims ++ [(f, x)] }
  /-- A transaction on destination chain `c`'s handler. -/
  | handler {S : Sys W} (c : Word) (H : Handler) : HandlerStep E c (S.dst c) H →
      SysStep K E S { S with dst := fun c' => if c' = c then H else S.dst c' }
  /-- Any other transaction on the source chain: it changes the world. -/
  | env {S : Sys W} (w' : W) : SysStep K E S { S with world := w' }

/-- Reachability. -/
inductive SysReach (K : Guards) (E : Env W) : Sys W → Sys W → Prop
  | refl {S : Sys W} : SysReach K E S S
  | tail {S T U : Sys W} : SysReach K E S T → SysStep K E T U → SysReach K E S U

/-! ## Named premises -/

/-- **THE CENTER PUBLISHES ONLY PUBLIC DISPATCHES** (a named premise, `PROTO-EVIDENCE`). Every
message from this chain's center that a destination can prove included is the bytes of a public
dispatch of the run. -/
def CenterPublishesOnlyPublicDispatches (E : Env W) (S : Sys W) : Prop :=
  ∀ x, E.included E.P.chainId x → ∃ d ∈ S.src.log, d.isAtomic = false ∧ E.P.enc d.bundle = x

/-- **THE DECODER INVERTS THE ENCODER ON THE RUN'S BUNDLES** (`SOL-ABI`, a named premise). -/
def DecodesRunBundles (E : Env W) (S : Sys W) : Prop :=
  ∀ d ∈ S.src.log, E.dec (E.P.enc d.bundle) = d.bundle

/-! ## Witness data

The source chain is `Dispatch`'s honest witness chain `wParams` (chain `324`, toy keccak reading
the last word, so a bundle's hash is its user salt). L1 is chain `1`, the destination L2 is chain
`325`. The router is at `9`, the L1 router at `26`, a destination application at `5`. -/

/-- The bundle `sender` forms on `wParams` with salt `s` and calls `cs`, to `dest`. -/
def arBundle (dest : Word) (sender : Address) (s : Word) (cs : List InteropCall) : Bundle :=
  ⟨wParams.chainId, dest, 1, wParams.keccak (saltPreimage sender s), cs, wAttrs s⟩

/-- An indirect starter through the router `9`, with zero value. -/
def arRouterStarter : CallStarter := ⟨9, [], ⟨0, 0, true⟩⟩

/-- A direct starter to the application `5`, with zero value. -/
def arAppStarter : CallStarter := ⟨5, [], ⟨0, 0, false⟩⟩

/-- The call the router returns for a burn to L1: to the L1 router `26`, from the router `9`. -/
def arL1Call : InteropCall := ⟨26, 9, 0, [7]⟩

/-- The call the router returns for a burn to an L2: to the router `9`, from the router `9`. -/
def arL2Call : InteropCall := ⟨9, 9, 0, [7]⟩

/-- A direct call from `sender` to the application `5`. -/
def arAppCall (sender : Address) : InteropCall := ⟨5, sender, 0, []⟩

/-- `sW`: a public withdrawal to L1 (`sendBundle`, no attribute), by `2`, salt `2`. -/
def arSW : Send := ⟨.sendBundle, none,
  ⟨2, [arRouterStarter], arBundle 1 2 2 [arL1Call], ⟨0, 0, 0, false⟩⟩⟩

/-- `sL`: an **atomic withdrawal to L1** (`sendBundle` with the attribute of flow `7`), by `1`,
salt `1`. -/
def arSL : Send := ⟨.sendBundle, some ⟨7, 100, 0⟩,
  ⟨1, [arRouterStarter], arBundle 1 1 1 [arL1Call], ⟨7, 0, 100, true⟩⟩⟩

/-- `s1`: `sendMessage` with the attribute of flow `9`, a direct call to the application on
chain `325`, by `1`, salt `3`: published, not appended. -/
def arS1 : Send := ⟨.sendMessage, some ⟨9, 100, 0⟩,
  ⟨1, [arAppStarter], arBundle 325 1 3 [arAppCall 1], ⟨0, 0, 0, false⟩⟩⟩

/-- `s2`: the other leg of flow `9`, an atomic router deposit to chain `325`, by `1`, salt `4`. -/
def arS2 : Send := ⟨.sendBundle, some ⟨9, 100, 0⟩,
  ⟨1, [arRouterStarter], arBundle 325 1 4 [arL2Call], ⟨9, 0, 100, true⟩⟩⟩

/-- `sG`: an atomic leg of flow `8` to chain `325`: a router deposit, then a direct call to the
application, by `1`, salt `5`. -/
def arSG : Send := ⟨.sendBundle, some ⟨8, 100, 0⟩,
  ⟨1, [arRouterStarter, arAppStarter], arBundle 325 1 5 [arL2Call, arAppCall 1], ⟨8, 0, 100, true⟩⟩⟩

/-- `sM`: `sendMessage` without the attribute, a direct call to the application on chain `325`, by
`2`, salt `6`. -/
def arSM : Send := ⟨.sendMessage, none,
  ⟨2, [arAppStarter], arBundle 325 2 6 [arAppCall 2], ⟨0, 0, 0, false⟩⟩⟩

/-- `sMA`: `sendMessage` with the attribute of flow `10`, a direct call to the application on chain
`325`, by `2`, salt `7`, as `upgradeTree` sends it: appended, not published. -/
def arSMA : Send := ⟨.sendMessage, some ⟨10, 100, 0⟩,
  ⟨2, [arAppStarter], arBundle 325 2 7 [arAppCall 2], ⟨10, 0, 100, true⟩⟩⟩

/-- A decoder that inverts `wParams.enc` on the witness bundles: it reads the user salt (the last
word). -/
def arDec (x : List UInt8) : Bundle :=
  if lastWord x = 1 then arSL.dispatch.bundle
  else if lastWord x = 2 then arSW.dispatch.bundle
  else if lastWord x = 3 then arS1.dispatch.bundle
  else if lastWord x = 4 then arS2.dispatch.bundle
  else if lastWord x = 5 then arSG.dispatch.bundle
  else arSM.dispatch.bundle

/-- The witness code map: the router at `9` answers `true`; nothing is deployed at the L1 router's
address `26` or at the application's address `5` on the source chain. -/
def arCode : Address → Code Unit (List UInt8) :=
  fun a => if a = 9 then .recoverer Contracts.AtomicFlowManager.RecoveryTargets.trueNoOp else .none

/-- The witness flows: `7 = {1, 99}`, `9 = {3, 4}`, `8 = {5, 98}`, every leg declared on `324`. -/
def arFlowLegs (f : Word) : List (Word × Word) :=
  if f = 7 then [(1, 324), (99, 324)]
  else if f = 9 then [(3, 324), (4, 324)]
  else if f = 8 then [(5, 324), (98, 324)] else []

/-- The witness environment. The destinations can prove included exactly the bytes of the two
public bundles `sW` and `s1`. -/
def arEnv : Env Unit where
  P := wParams
  l1ChainId := 1
  l2Router := 9
  l1Router := 26
  depositCalldata := fun _ _ _ => [7]
  dec := arDec
  code := arCode
  sem := Contracts.AtomicFlowManager.RecoveryTargets.vmCall
  included := fun c x => c = 324 ∧
    (x = wParams.enc arSW.dispatch.bundle ∨ x = wParams.enc arS1.dispatch.bundle)
  finalized := fun _ _ => False
  flowLegs := arFlowLegs
  absentElsewhere := fun _ _ => False

end Contracts.InteropCenter.History.AtomicRouting
