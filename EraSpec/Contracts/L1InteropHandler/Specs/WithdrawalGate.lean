import Mathlib.Tactic
import EraSpec.Core.Word
import EraSpec.Contracts.InteropHandlerBase.Specs.Reentrancy

/-!
# Model: `L1InteropHandler` at v0.35 head — the gate in front of L1 withdrawal finalization

Source: era-contracts branch `draft/v0.35.0` at head `b17415d20`. Paths are relative to
`l1-contracts/contracts/`. In this header `L1` is `interop/interop-handler/L1InteropHandler.sol`
and `IHB` is `interop/interop-handler/InteropHandlerBase.sol`; every line number is at `b17415d20`.
At main `70096e2ea` both files differ only in three getter names (`_executeBundleSelector`,
`_verifyBundleSelector`, `_expectedDestinationBaseTokenAssetId`) and, for the two selector getters,
their mutability (`pure` to `view`, `L1:117`, `:122` at main), so the model also describes main.
The pin model of the shared status machine is `InteropHandlerBase/Specs/Reentrancy.lean`
(`c67894b9`); this file reuses its replay state and its unbundle loop, and is a new model beside it.

**This file is definitions only.** The results are in
`EraSpec.Contracts.L1InteropHandler.Properties.WithdrawalGate` and are proved in
`EraSpec.Contracts.L1InteropHandler.Proofs.WithdrawalGate`.

## The code

    executeBundle(bytes _bundle, MessageInclusionProof _proof)                       // L1:81-98
      (bundle, bundleHash, status) = _getBundleData(_bundle)                          // L1:82
        require(_bundle.length != 0); abi.decode; require(version == 1)              // IHB:228-230
        bundleHash = keccak256(_bundle); status = bundleStatus[bundleHash]           // IHB:231-232
      require(bundle.calls.length == 1, MultiCallToL1NotSupported)                    // L1:85
      _validateExecutable: _ensureNotPaused, _requireExecutionAllowed,
                           require(status == Unreceived || status == Verified)        // L1:88; IHB:292-300
      if (status != Verified) _verifyBundle(_bundle, bundle, _proof, bundleHash, status) // L1:92-95
      _markFullyExecutedAndRun(bundleHash, bundle)                                    // L1:97
        bundleStatus = FullyExecuted; callStatus[i] = Executed for all i              // IHB:326-331
        _executeCalls(_executeAllCalls: true)                                         // IHB:333-339

    verifyBundle(bytes _bundle, MessageInclusionProof _proof)                        // L1:103-110
      _getBundleData; _verifyBundle(...)                                              // no pause gate

    _verifyBundle                                                                     // L1:203-224
      _validateVerifiable: _validateBundleDestinationContext(h, bundle, _proof.chainId)
                           require(status == Unreceived)                             // L1:211; IHB:306-314
        require(bundle.sourceChainId == _proof.chainId)                               // IHB:395-398
        require(bundle.destinationChainId == block.chainid)                           // IHB:400-403
        require(bundle.destinationBaseTokenAssetId ==
                DataEncoding.encodeNTVAssetId(block.chainid, ETH_TOKEN_ADDRESS))     // IHB:405-409; L1:181-183
      require(_proof.message.sender == L2_INTEROP_CENTER_ADDR)                        // L1:213-216
      _proof.message.data = bytes.concat(BUNDLE_IDENTIFIER, _bundle)                 // L1:219
      require(_proveInclusion(_proof))                                                // L1:221; :227-236
      _markVerified: bundleStatus = Verified                                          // L1:223; IHB:317-320

    unbundleBundle(bytes _bundle, CallStatus[] _providedCallStatus)                  // IHB:113-175
      _ensureNotPaused()                                                              // IHB:114
      _getBundleData; parse unbundlerAddress; permission gate                         // IHB:116-132
      require(calls.length == _providedCallStatus.length)                             // IHB:134-137
      require(status == Verified || status == Unbundled)                              // IHB:139
      bundleStatus = Unbundled; per-call status loop                                  // IHB:147-164
      _executeCalls(_executeAllCalls: false, _providedCallStatus)                     // IHB:166-172

    _executeCalls, per call i that runs                                               // IHB:350-383
      require(call.version == 1); require(!call.shadowAccount)                       // IHB:366, :369
      _handleCallValue(value): require(value == 0)                                    // IHB:371; L1:175-177
      target = _interopCallTarget(to): require(to == L1_ASSET_ROUTER); L1_ASSET_ROUTER // IHB:374; L1:189-192
      selector = target.receiveMessage{value}(keccak256(abi.encodePacked(h, i)),
                   formatEvmV1(sourceChainId, call.from), call.data)                  // IHB:374-380
      require(selector == receiveMessage.selector)                                    // IHB:381

Administration: `initialize(_owner)` (L1:59-62: `reentrancyGuardInitializer initializer`,
`require(_owner != 0)`, `_transferOwnership(_owner)`), `pause`/`unpause` (L1:65-72, `onlyOwner`,
OpenZeppelin `_pause`/`_unpause` with `whenNotPaused`/`whenPaused`), and the inherited
`Ownable2StepUpgradeable` functions `transferOwnership` (`onlyOwner`, writes `_pendingOwner`),
`acceptOwnership` (`_pendingOwner == msg.sender`) and `renounceOwnership` (`onlyOwner`), all from
OpenZeppelin contracts-upgradeable `release-v4.9` (`.gitmodules`; the submodule is cited by function).

## The inventory the model rests on (checked against `b17415d20`)

* `bundleStatus` (IHB:55) has three writers: `_markVerified` (IHB:318, `Verified`),
  `_markFullyExecutedAndRun` (IHB:326, `FullyExecuted`) and `unbundleBundle` (IHB:147, `Unbundled`).
  `callStatus` (IHB:58) has three: IHB:330, :155 and :160. None writes `Unreceived`.
* `_paused` is written only by OpenZeppelin's `_pause`/`_unpause`, called only from `pause`/`unpause`
  (L1:65-72). `initialize` does not call `__Pausable_init`, so a fresh proxy starts unpaused.
* `_owner` is written only through `_transferOwnership`: by `initialize` (L1:61), `acceptOwnership`
  and `renounceOwnership`. `_pendingOwner` by `transferOwnership` and by `_transferOwnership`'s
  `delete`.
* The reentrancy-guard slot (`common/ReentrancyGuard.sol:31`) is written by
  `reentrancyGuardInitializer` (`:43-63`), which reverts unless the slot was zero. The handler uses it
  only in `initialize` (and in the implementation's constructor, L1:50, on the implementation's own
  storage); no handler function is `nonReentrant`.
* The handler makes three kinds of external call: the static `MESSAGE_ROOT.proveL2MessageInclusionShared`
  (L1:227-236, `internal view`), the delivered call's `receiveMessage` (IHB:374-380), and the self-calls
  `this.executeBundle`/`this.verifyBundle`/`this.unbundleBundle` of the `receiveMessage` rescue path
  (L1:148, :159; IHB:432). `receiveMessage` requires `msg.sender == address(this)` (IHB:194).

## Modelling choices

* **Bytes, decoding and hashing are abstract** (`Codec`): `abi.decode(_bundle, (InteropBundle))`
  together with the empty-bytes check (`decode`, `none` is a revert), `abi.encode(InteropBundle)`
  (`enc`, used only by the composed results), `keccak256` (`keccak`) and
  `DataEncoding.encodeNTVAssetId(chainId, ETH_TOKEN_ADDRESS)` (`ethAssetId`). No hash or encoding
  premise is taken by the model; results that need one state it.
* **The inclusion oracle is an input.** `_proveInclusion` is a static call whose answer depends on the
  `MessageRoot`'s state at the time. Each `executeBundle`/`verifyBundle` call carries the oracle's
  verdict `incl` on the substituted query: `proveL2MessageInclusionShared(_proof.chainId,
  _proof.l1BatchNumber, _proof.l2MessageIndex, {txNumberInBatch, sender, BUNDLE_IDENTIFIER ++ _bundle},
  _proof.proof)`. A passing `_verifyBundle` commits a `Verification` record; "the oracle accepted the
  query" means exactly that such a record is in the committed log. What the oracle's acceptance says
  about the source chain is the premise `InclusionSoundOn` of the composed results (`PROTO-EVIDENCE`).
* **Re-entry, as in the pin model.** A delivered call's target is a finite tree of re-entrant calls of
  the handler's entry points (`Callee`), each failure caught or propagated, run with a fuel budget; a
  reverted frame returns `none` and leaves nothing (`VM-REVERT` as modelled). The target is pinned to
  `L1_ASSET_ROUTER`, whose `receiveMessage` (`bridge/asset-router/AssetRouterBase.sol:213-251`) ends in
  `finalizeDeposit` and can reach arbitrary code (a withdrawal's receiver); the tree stands for all of
  that. Entry points other than the target's `receiveMessage` cannot re-enter (inventory above).
* **Callers are inputs.** Every entry call carries `msg.sender`. The `receiveMessage` rescue path is not a
  separate entry: it ends in one of the three entry points with `msg.sender == address(this)`, so it is
  the same entry with `caller = self`. On L1 a frame with `msg.sender == address(this)` exists only if the
  handler calls itself, and its only call target is `L1_ASSET_ROUTER`; the model lets any frame take any
  caller, which only adds runs.
* **The permission gates are kept** (`ExecutionAllowed`, `UnbundleAllowed`), with ERC-7930 attributes as
  parsed values (`AddrAttr`): `parseEvmV1` reverts on empty or malformed bytes (`vendor/
  draft-InteroperableAddress.sol:159-163`), except that an empty `executionAddress` means
  permissionless (IHB:240-242).
* **Ghost effects.** The committed log records each passing `_verifyBundle` (`Effect.verified`, with the
  submitted bytes, the decoded bundle and the proof), each delivered call (`Effect.delivered`, with the
  route, the bytes it was decoded from, its index, target, value, ERC-7786 sender and payload, and the
  pause flag at the moment of the call), each `BundleExecuted`, and the administrative writes. The
  `receiveId` `keccak256(abi.encodePacked(bundleHash, i))` is a function of the recorded hash and index;
  `L1_ASSET_ROUTER` ignores it (`AssetRouterBase.sol:214`).
* **Reject-only details omitted**: the returned-selector check (IHB:381, folded into the target's
  failure), event emissions, and OpenZeppelin's `initializer` flag next to the guard slot (in fresh proxy
  storage both are clear, and the guard slot alone already rejects a second `initialize`). `address(0)`
  is never a real `msg.sender`; the model allows it, which only adds runs. Proxy upgrades of the handler
  are `OPS-CONFIG`. The handler is new in this release and the upgrade deploys its proxy
  (`protocol-docs/chain-lifecycle.md:186-188`), so results "from fresh storage" start from `init`.
* **The only finalization path.** At `b17415d20` `L1Nullifier` has no withdrawal-finalization entry
  point; `L1AssetRouter.receiveMessage` accepts only `l1InteropHandler` as caller
  (`bridge/asset-router/AssetRouterBase.sol:218`, `L1AssetRouter.sol:258-260`), a one-shot owner setting
  (`L1AssetRouter.sol:126-130`). That the router's handler is this proxy is configuration.
-/

namespace Contracts.L1WithdrawalGate

open AttackVectors.BundleStatusMachine (Status CallStatus)

/-! ## Words, addresses, bytes -/

/-- `bytes32` and `uint256` words. -/
abbrev Word := UInt256

/-- An `address`: 20 bytes. -/
abbrev Address := Fin (256 ^ 20)

/-- A `bytes` value. -/
abbrev Bytes := List UInt8

/-- `bytes32(uint256(uint160(a)))`: an address as a log key (`common/libraries/MessageHashing.sol:34`). -/
def padAddr (a : Address) : Word := ⟨a.val, lt_trans a.isLt (by norm_num [UInt256.size])⟩

/-! ## Constants (`common/Messaging.sol:5-7`, `common/l2-helpers/L2ContractAddresses.sol`) -/

/-- `BUNDLE_IDENTIFIER = 0x01` (`Messaging.sol:5`). -/
def bundleIdentifier : UInt8 := 0x01

/-- `INTEROP_BUNDLE_VERSION = 0x01` (`Messaging.sol:6`). -/
def interopBundleVersion : ℕ := 1

/-- `INTEROP_CALL_VERSION = 0x01` (`Messaging.sol:7`). -/
def interopCallVersion : ℕ := 1

/-- `L2_INTEROP_CENTER_ADDR = BUILT_IN_CONTRACTS_OFFSET + 0x0d` (`L2ContractAddresses.sol:118`). -/
def l2InteropCenterAddr : Address := 0x1000d

/-- `L2_TO_L1_MESSENGER_SYSTEM_CONTRACT_ADDR = SYSTEM_CONTRACTS_OFFSET + 0x08`
(`L2ContractAddresses.sol:56`): the sender of every L2→L1 message log on L1's side
(`MessageHashing.sol:33`). -/
def l2ToL1MessengerAddr : Address := 0x8008

/-! ## The message types -/

/-- An ERC-7930 address attribute as `InteroperableAddress.parseEvmV1` reads it. -/
inductive AddrAttr
  /-- Zero-length bytes. -/
  | empty
  /-- Parses to `(chainId, addr)`; chain id `0` is the chain-agnostic form. -/
  | evm (chainId : ℕ) (addr : Address)
  /-- Non-empty bytes that do not parse: `parseEvmV1` reverts. -/
  | malformed
deriving DecidableEq

/-- `InteropCall` (`Messaging.sol:240-247`). -/
structure Call where
  /-- `bytes1 version`. -/
  version : ℕ
  /-- `bool shadowAccount` (reserved). -/
  shadowAccount : Bool
  /-- `to`. -/
  target : Address
  /-- `from`. -/
  fromAddr : Address
  /-- `value`. -/
  value : ℕ
  /-- `data`. -/
  data : Bytes
deriving DecidableEq

/-- `BundleAttributes` (`Messaging.sol:224-229`). -/
structure Attributes where
  executionAddress : AddrAttr
  unbundlerAddress : AddrAttr
  useFixedFee : Bool
  salt : Word
deriving DecidableEq

/-- `InteropBundle` (`Messaging.sol:268-276`). -/
structure Bundle where
  /-- `bytes1 version`. -/
  version : ℕ
  sourceChainId : ℕ
  destinationChainId : ℕ
  destinationBaseTokenAssetId : Word
  interopBundleSalt : Word
  calls : List Call
  bundleAttributes : Attributes
deriving DecidableEq

/-- `L2Message` (`Messaging.sol:41-45`). -/
structure L2Message where
  txNumberInBatch : ℕ
  sender : Address
  data : Bytes
deriving DecidableEq

/-- `MessageInclusionProof` (`Messaging.sol:296-302`). -/
structure InclusionProof where
  chainId : ℕ
  l1BatchNumber : ℕ
  l2MessageIndex : ℕ
  message : L2Message
  proof : List Word
deriving DecidableEq

/-- `L2Log` (`Messaging.sol:27-34`). -/
structure L2Log where
  l2ShardId : ℕ
  isService : Bool
  txNumberInBatch : ℕ
  sender : Address
  key : Word
  value : Word
deriving DecidableEq

/-! ## Deployment constants and abstract functions -/

/-- The functions the gate and its source chains compose, shared by all chains. -/
structure Codec where
  /-- `abi.encode(InteropBundle)` (the source center, `interop/InteropCenter.sol:735`). -/
  enc : Bundle → Bytes
  /-- `require(_bundle.length != 0)` and `abi.decode(_bundle, (InteropBundle))` (IHB:228-229); `none`
  is a revert. -/
  decode : Bytes → Option Bundle
  /-- `keccak256`. -/
  keccak : Bytes → Word
  /-- `DataEncoding.encodeNTVAssetId(chainId, ETH_TOKEN_ADDRESS)`. -/
  ethAssetId : ℕ → Word

/-- `_l2MessageToLog(message)` (`common/libraries/MessageHashing.sol:27-37`): the log whose leaf hash
`proveL2MessageInclusionShared` proves (`common/MessageVerification.sol:17-32`, `:85-108`). -/
def msgToLog (C : Codec) (m : L2Message) : L2Log :=
  ⟨0, true, m.txNumberInBatch, l2ToL1MessengerAddr, padAddr m.sender, C.keccak m.data⟩

/-- One deployment of the L1 handler. -/
structure Params where
  codec : Codec
  /-- `block.chainid` on L1. -/
  l1ChainId : ℕ
  /-- `address(this)`, the handler's proxy. -/
  self : Address
  /-- `L1_ASSET_ROUTER` (L1:43, immutable; the constructor requires it nonzero, L1:52). -/
  router : Address

/-- The destination base-token asset id the handler expects (L1:181-183). -/
def Params.expectedBaseAsset (P : Params) : Word := P.codec.ethAssetId P.l1ChainId

/-! ## State -/

/-- The handler's storage. -/
structure State where
  /-- `bundleStatus` and `callStatus` (IHB:55, :58), as in the pin model. -/
  replay : Contracts.InteropHandler.State
  /-- OpenZeppelin `PausableUpgradeable._paused`. -/
  paused : Bool
  /-- OpenZeppelin `OwnableUpgradeable._owner`. -/
  owner : Address
  /-- OpenZeppelin `Ownable2StepUpgradeable._pendingOwner`. -/
  pendingOwner : Address
  /-- The reentrancy-guard slot is nonzero (`common/ReentrancyGuard.sol:31`, written by
  `reentrancyGuardInitializer`). -/
  guardSet : Bool

/-- Fresh proxy storage: everything zero. -/
def init : State := ⟨Contracts.InteropHandler.init, false, 0, 0, false⟩

/-! ## Entry points -/

/-- The administrative entry points; none makes an external call. -/
inductive AdminOp
  /-- `initialize(_owner)` (L1:59-62). -/
  | initialize (newOwner : Address)
  /-- `pause()` (L1:65-67). -/
  | pause
  /-- `unpause()` (L1:70-72). -/
  | unpause
  /-- `Ownable2StepUpgradeable.transferOwnership(newOwner)`. -/
  | transferOwnership (newOwner : Address)
  /-- `Ownable2StepUpgradeable.acceptOwnership()`. -/
  | acceptOwnership
  /-- `OwnableUpgradeable.renounceOwnership()`. -/
  | renounceOwnership
deriving DecidableEq

/-- A call of one of the handler's entry points, at top level or re-entrantly, with its `msg.sender`. -/
inductive Entry
  /-- `executeBundle(_bundle, _proof)` (L1:81-98); `incl` is `_proveInclusion`'s verdict on the
  substituted query, consulted only for an `Unreceived` bundle. -/
  | executeBundle (caller : Address) (bundle : Bytes) (proof : InclusionProof) (incl : Bool)
  /-- `verifyBundle(_bundle, _proof)` (L1:103-110). -/
  | verifyBundle (caller : Address) (bundle : Bytes) (proof : InclusionProof) (incl : Bool)
  /-- `unbundleBundle(_bundle, _providedCallStatus)` (IHB:113-175). -/
  | unbundleBundle (caller : Address) (bundle : Bytes) (req : List CallStatus)
  /-- An administrative function. -/
  | admin (caller : Address) (op : AdminOp)

/-- What the target of one delivered call does, from its `receiveMessage` until it returns (the pin
model's `Callee`, over this handler's entry points). -/
inductive Callee
  /-- Returns the expected selector. -/
  | returns
  /-- Reverts, or returns another selector. -/
  | reverts
  /-- Calls entry point `e`; `inner` are the targets of the calls that frame delivers. If that frame
  reverts, the target catches the failure (`caught`) or reverts; then it goes on as `next`. -/
  | calls (e : Entry) (inner : List Callee) (caught : Bool) (next : Callee)

/-- Which entry point's call loop delivered a call. -/
inductive Route
  /-- `executeBundle`'s `_markFullyExecutedAndRun` (IHB:333-339). -/
  | execute
  /-- `unbundleBundle`'s `_executeCalls` (IHB:166-172). -/
  | unbundle
deriving DecidableEq

/-! ## The committed log -/

/-- A passing `_verifyBundle`: the submitted bytes, the bundle decoded from them, the submitted proof. -/
structure Verification where
  bytes : Bytes
  bundle : Bundle
  proof : InclusionProof
deriving DecidableEq

/-- The message `_proveInclusion` asked about: the submitted message with its data replaced by
`BUNDLE_IDENTIFIER ++ _bundle` (L1:219). -/
def Verification.query (v : Verification) : L2Message :=
  { v.proof.message with data := bundleIdentifier :: v.bytes }

/-- One call reaching its target's `receiveMessage` (IHB:374-380). -/
structure Delivery where
  route : Route
  /-- The bytes the delivering frame decoded. -/
  bytes : Bytes
  /-- `bundleHash = keccak256(_bundle)` (IHB:231). -/
  hash : Word
  /-- The call index `i`; the `receiveId` is `keccak256(abi.encodePacked(hash, i))` (IHB:377). -/
  index : ℕ
  /-- The called contract, `_interopCallTarget(call.to)` (IHB:374). -/
  target : Address
  /-- `msg.value` of the call. -/
  value : ℕ
  /-- The ERC-7786 sender `formatEvmV1(sourceChainId, call.from)` (IHB:378), as its two parts. -/
  senderChain : ℕ
  senderAddr : Address
  /-- `call.data` (IHB:379). -/
  payload : Bytes
  /-- `_paused` at the moment of the call. -/
  pausedNow : Bool
deriving DecidableEq

/-- A committed event of the handler. -/
inductive Effect
  /-- A passing `_verifyBundle` (`BundleVerified`, IHB:319). -/
  | verified (v : Verification)
  /-- A delivered call. -/
  | delivered (d : Delivery)
  /-- `BundleExecuted(bundleHash)` (IHB:341). -/
  | executed (h : Word)
  /-- `_paused` written to `value` by `caller` (`pause`/`unpause`). -/
  | pauseSet (caller : Address) (value : Bool)
  /-- `_owner` written to `newOwner` (`_transferOwnership`). -/
  | ownerSet (newOwner : Address)
  /-- `_pendingOwner` written to `newPending` by `transferOwnership`. -/
  | pendingSet (newPending : Address)
  /-- `initialize` ran, called by `caller`. -/
  | initialized (caller : Address)
deriving DecidableEq

/-! ## The checks -/

/-- `_validateBundleDestinationContext(h, b, proofChainId)` (IHB:390-410). -/
def ContextOk (P : Params) (b : Bundle) (proofChainId : ℕ) : Prop :=
  b.sourceChainId = proofChainId ∧ b.destinationChainId = P.l1ChainId ∧
    b.destinationBaseTokenAssetId = P.expectedBaseAsset

instance (P : Params) (b : Bundle) (c : ℕ) : Decidable (ContextOk P b c) := by
  unfold ContextOk; infer_instance

/-- `_verifyBundle` (L1:203-224) passes on a bundle whose status is `st`: the destination context
against `_proof.chainId` and `st == Unreceived` (L1:211), the message sender (L1:213-216), and the
oracle's verdict on the substituted query (L1:219-221). -/
def VerifyOk (P : Params) (st : Status) (b : Bundle) (pf : InclusionProof) (incl : Bool) : Prop :=
  ContextOk P b pf.chainId ∧ st = .Unreceived ∧ pf.message.sender = l2InteropCenterAddr ∧ incl = true

instance (P : Params) (st : Status) (b : Bundle) (pf : InclusionProof) (incl : Bool) :
    Decidable (VerifyOk P st b pf incl) := by
  unfold VerifyOk; infer_instance

/-- `_requireExecutionAllowed` (IHB:239-255) for `msg.sender = caller`. -/
def ExecutionAllowed (P : Params) (caller : Address) (b : Bundle) : Prop :=
  match b.bundleAttributes.executionAddress with
  | .empty => True
  | .evm cid a => caller = P.self ∨ ((cid = P.l1ChainId ∨ cid = 0) ∧ a = caller)
  | .malformed => False

instance (P : Params) (caller : Address) (b : Bundle) : Decidable (ExecutionAllowed P caller b) := by
  unfold ExecutionAllowed; split <;> infer_instance

/-- `unbundleBundle`'s parse and permission gate (IHB:118-132) for `msg.sender = caller`. -/
def UnbundleAllowed (P : Params) (caller : Address) (b : Bundle) : Prop :=
  match b.bundleAttributes.unbundlerAddress with
  | .evm cid a => caller = P.self ∨ ((cid = P.l1ChainId ∨ cid = 0) ∧ a = caller)
  | _ => False

instance (P : Params) (caller : Address) (b : Bundle) : Decidable (UnbundleAllowed P caller b) := by
  unfold UnbundleAllowed; split <;> infer_instance

/-- The checks `_executeCalls` makes on a call before calling its target: the call version (IHB:366),
no shadow account (IHB:369), `_handleCallValue` (L1:175-177) and `_interopCallTarget` (L1:189-192). -/
def CallChecks (P : Params) (c : Call) : Prop :=
  c.version = interopCallVersion ∧ c.shadowAccount = false ∧ c.value = 0 ∧ c.target = P.router

instance (P : Params) (c : Call) : Decidable (CallChecks P c) := by
  unfold CallChecks; infer_instance

/-- `executeBundle`'s checks before its writes (L1:82-95): the bundle version, the single-call rule,
`_validateExecutable` (pause, permission, `Unreceived` or `Verified`), and `_verifyBundle` when the
bundle is not yet `Verified`. -/
def ExecuteOk (P : Params) (s : State) (caller : Address) (B : Bytes) (b : Bundle)
    (pf : InclusionProof) (incl : Bool) : Prop :=
  b.version = interopBundleVersion ∧ b.calls.length = 1 ∧ s.paused = false ∧
    ExecutionAllowed P caller b ∧
    (s.replay.bundle (P.codec.keccak B) = .Unreceived ∨
      s.replay.bundle (P.codec.keccak B) = .Verified) ∧
    (s.replay.bundle (P.codec.keccak B) = .Unreceived →
      VerifyOk P (s.replay.bundle (P.codec.keccak B)) b pf incl)

instance (P : Params) (s : State) (caller : Address) (B : Bytes) (b : Bundle) (pf : InclusionProof)
    (incl : Bool) : Decidable (ExecuteOk P s caller B b pf incl) := by
  unfold ExecuteOk; infer_instance

/-- `unbundleBundle`'s checks before its writes, after the pause gate (IHB:116-139). -/
def UnbundleOk (P : Params) (s : State) (caller : Address) (B : Bytes) (b : Bundle)
    (req : List CallStatus) : Prop :=
  b.version = interopBundleVersion ∧ UnbundleAllowed P caller b ∧ req.length = b.calls.length ∧
    (s.replay.bundle (P.codec.keccak B) = .Verified ∨
      s.replay.bundle (P.codec.keccak B) = .Unbundled)

instance (P : Params) (s : State) (caller : Address) (B : Bytes) (b : Bundle)
    (req : List CallStatus) : Decidable (UnbundleOk P s caller B b req) := by
  unfold UnbundleOk; infer_instance

/-! ## The semantics -/

/-- The administrative functions: the state after a successful call and its log, or `none`. -/
def adminStep (caller : Address) : AdminOp → State → Option (State × List Effect)
  | .initialize o, s =>
      if s.guardSet = false ∧ o ≠ 0 then
        some ({ s with guardSet := true, owner := o, pendingOwner := 0 },
          [.initialized caller, .ownerSet o])
      else none
  | .pause, s =>
      if caller = s.owner ∧ s.paused = false then
        some ({ s with paused := true }, [.pauseSet caller true])
      else none
  | .unpause, s =>
      if caller = s.owner ∧ s.paused = true then
        some ({ s with paused := false }, [.pauseSet caller false])
      else none
  | .transferOwnership o, s =>
      if caller = s.owner then some ({ s with pendingOwner := o }, [.pendingSet o]) else none
  | .acceptOwnership, s =>
      if caller = s.pendingOwner then
        some ({ s with owner := caller, pendingOwner := 0 }, [.ownerSet caller])
      else none
  | .renounceOwnership, s =>
      if caller = s.owner then
        some ({ s with owner := 0, pendingOwner := 0 }, [.ownerSet 0])
      else none

/-- What runs: an entry point, a call loop, or one delivered call's target. -/
inductive Frame
  /-- Entry point `e`; `callees` are the targets of the calls it delivers, in order. -/
  | entry (e : Entry) (callees : List Callee)
  /-- `_executeCalls` of the bundle decoded from `bytes`, delivering calls `is` on `route`. -/
  | calls (bytes : Bytes) (b : Bundle) (route : Route) (is : List ℕ) (callees : List Callee)
  /-- One delivered call's target. -/
  | target (c : Callee)

/-- The replay writes `executeBundle` makes before its calls: `_markVerified` for an `Unreceived`
bundle (L1:223, inside `_verifyBundle`), then `bundleStatus = FullyExecuted` and every call
`Executed` (IHB:326-331). These are the pin model's `verifyIfUnreceived` and `beforeCalls`. -/
def executeWrites (h : Word) (n : ℕ) (r : Contracts.InteropHandler.State) :
    Contracts.InteropHandler.State :=
  Contracts.InteropHandler.beforeCalls .deployed ⟨h, n⟩ (r.verifyIfUnreceived h)

/-- **The semantics.** `exec P n f s` runs frame `f` from `s` with budget `n`: the state and the
committed log it leaves, or `none` if it reverts. -/
def exec (P : Params) : ℕ → Frame → State → Option (State × List Effect)
  | 0, _, _ => none
  | n + 1, .entry (.executeBundle caller B pf incl) cs, s =>
      match P.codec.decode B with
      | none => none
      | some b =>
          if ExecuteOk P s caller B b pf incl then
            match exec P n (.calls B b .execute (List.range b.calls.length) cs)
                { s with replay := executeWrites (P.codec.keccak B) b.calls.length s.replay } with
            | some (s₂, l) =>
                some (s₂, (if s.replay.bundle (P.codec.keccak B) = .Unreceived then
                    [Effect.verified ⟨B, b, pf⟩] else []) ++ l ++ [.executed (P.codec.keccak B)])
            | none => none
          else none
  | _ + 1, .entry (.verifyBundle _ B pf incl) _, s =>
      match P.codec.decode B with
      | none => none
      | some b =>
          if b.version = interopBundleVersion ∧
              VerifyOk P (s.replay.bundle (P.codec.keccak B)) b pf incl then
            some ({ s with replay := s.replay.setBundle (P.codec.keccak B) .Verified },
              [.verified ⟨B, b, pf⟩])
          else none
  | n + 1, .entry (.unbundleBundle caller B req) cs, s =>
      if s.paused = true then none
      else
        match P.codec.decode B with
        | none => none
        | some b =>
            if UnbundleOk P s caller B b req then
              match Contracts.InteropHandler.markCalls true (P.codec.keccak B) 0 req
                  (s.replay.setBundle (P.codec.keccak B) .Unbundled) with
              | some r₁ =>
                  exec P n (.calls B b .unbundle (Contracts.InteropHandler.toExecute 0 req) cs)
                    { s with replay := r₁ }
              | none => none
            else none
  | _ + 1, .entry (.admin caller op) _, s => adminStep caller op s
  | _ + 1, .calls _ _ _ [] _, s => some (s, [])
  | n + 1, .calls B b r (i :: is) cs, s =>
      match b.calls[i]? with
      | none => none
      | some c =>
          if CallChecks P c then
            match exec P n (.target (cs.headD .returns)) s with
            | some (s₁, l₁) =>
                match exec P n (.calls B b r is cs.tail) s₁ with
                | some (s₂, l₂) =>
                    some (s₂, .delivered ⟨r, B, P.codec.keccak B, i, P.router, c.value,
                      b.sourceChainId, c.fromAddr, c.data, s.paused⟩ :: (l₁ ++ l₂))
                | none => none
            | none => none
          else none
  | _ + 1, .target .returns, s => some (s, [])
  | _ + 1, .target .reverts, _ => none
  | n + 1, .target (.calls e inner caught next), s =>
      match exec P n (.entry e inner) s with
      | some (s₁, l₁) =>
          match exec P n (.target next) s₁ with
          | some (s₂, l₂) => some (s₂, l₁ ++ l₂)
          | none => none
      | none => if caught then exec P n (.target next) s else none

/-- The commit rule: a transaction that reverts leaves the state and the log as they were. -/
def commit (s : State) : Option (State × List Effect) → State × List Effect
  | some r => r
  | none => (s, [])

/-- A submitted transaction: a budget, an entry point and the targets of the calls it delivers. -/
structure Tx where
  fuel : ℕ
  entry : Entry
  callees : List Callee

/-- One transaction. -/
def submit (P : Params) (s : State) (t : Tx) : State × List Effect :=
  commit s (exec P t.fuel (.entry t.entry t.callees) s)

/-- A sequence of transactions: the final state and the committed log, in order. -/
def submitAll (P : Params) : State → List Tx → State × List Effect
  | s, [] => (s, [])
  | s, t :: ts =>
      ((submitAll P (submit P s t).1 ts).1,
        (submit P s t).2 ++ (submitAll P (submit P s t).1 ts).2)

/-! ## Reading the log -/

/-- The verifications in a log, in order. -/
def verifications : List Effect → List Verification
  | [] => []
  | .verified v :: l => v :: verifications l
  | _ :: l => verifications l

/-- The deliveries in a log, in order. -/
def deliveries : List Effect → List Delivery
  | [] => []
  | .delivered d :: l => d :: deliveries l
  | _ :: l => deliveries l

/-- The pause values written in a log, in order. -/
def pauseWrites : List Effect → List Bool
  | [] => []
  | .pauseSet _ v :: l => v :: pauseWrites l
  | _ :: l => pauseWrites l

/-- The owners written in a log, in order (`_transferOwnership`, called by `initialize`,
`acceptOwnership` and `renounceOwnership`). -/
def ownerWrites : List Effect → List Address
  | [] => []
  | .ownerSet o :: l => o :: ownerWrites l
  | _ :: l => ownerWrites l

/-- The number of `initialize` calls in a log. -/
def initCount : List Effect → ℕ
  | [] => 0
  | .initialized _ :: l => initCount l + 1
  | _ :: l => initCount l

/-- A log entry as the pin model's `Effect`: deliveries and completions; the rest has no pin
counterpart. -/
def Effect.toPin : Effect → Option Contracts.InteropHandler.Effect
  | .delivered d => some (.delivered d.hash d.index)
  | .executed h => some (.executed h)
  | _ => none

/-- What a committed delivery satisfies by the code alone: it is call `index` of the bundle its
bytes decode to, and that call passed `_executeCalls`' checks; the target is `L1_ASSET_ROUTER` and the
value zero; the ERC-7786 sender and payload are the call's; a call delivered by `executeBundle` belongs
to a one-call bundle; and a call of a one-call bundle is call `0`, delivered while the handler was not
paused. -/
def DeliveryWellFormed (P : Params) (d : Delivery) : Prop :=
  d.hash = P.codec.keccak d.bytes ∧ d.target = P.router ∧ d.value = 0 ∧
    ∃ b c, P.codec.decode d.bytes = some b ∧ b.version = interopBundleVersion ∧
      b.calls[d.index]? = some c ∧ CallChecks P c ∧
      d.senderChain = b.sourceChainId ∧ d.senderAddr = c.fromAddr ∧ d.payload = c.data ∧
      (d.route = .execute → b.calls.length = 1) ∧
      (b.calls.length = 1 → d.index = 0 ∧ d.pausedNow = false)

/-- What a committed verification satisfies by the code alone: its bytes decode to its bundle, of
version 1, whose destination context matches the proof's chain, L1 and L1's ETH asset id, and the
proven message was sent by `L2_INTEROP_CENTER_ADDR` with data `BUNDLE_IDENTIFIER ++ bytes`. -/
def VerificationWellFormed (P : Params) (v : Verification) : Prop :=
  P.codec.decode v.bytes = some v.bundle ∧ v.bundle.version = interopBundleVersion ∧
    ContextOk P v.bundle v.proof.chainId ∧ v.query.sender = l2InteropCenterAddr ∧
    v.query.data = bundleIdentifier :: v.bytes

/-- Bundle `b` has a call at index `i`, with `from = a` and `data = p`. -/
def CallHas (b : Bundle) (i : ℕ) (a : Address) (p : Bytes) : Prop :=
  match b.calls[i]? with
  | some c => a = c.fromAddr ∧ p = c.data
  | none => False

instance (b : Bundle) (i : ℕ) (a : Address) (p : Bytes) : Decidable (CallHas b i a p) := by
  unfold CallHas; split <;> infer_instance

/-- The provenance of a delivered call through one verification of the same bytes: the proven
message was sent by the center with data `BUNDLE_IDENTIFIER ++ bytes`, from the chain the bundle names
as its source and the delivery names as its sender's chain; the bundle is for L1 with L1's ETH asset;
the sender and payload are those of the bundle's call at the delivered index. -/
def ProvenBy (P : Params) (v : Verification) (d : Delivery) : Prop :=
  v.bytes = d.bytes ∧ v.query.sender = l2InteropCenterAddr ∧
    v.query.data = bundleIdentifier :: d.bytes ∧
    d.senderChain = v.proof.chainId ∧ v.bundle.sourceChainId = v.proof.chainId ∧
    v.bundle.destinationChainId = P.l1ChainId ∧
    v.bundle.destinationBaseTokenAssetId = P.expectedBaseAsset ∧
    CallHas v.bundle d.index d.senderAddr d.payload

instance (P : Params) (v : Verification) (d : Delivery) : Decidable (ProvenBy P v d) := by
  unfold ProvenBy; infer_instance

/-- Two named byte strings of the run collide under `keccak256`. -/
def KeccakClash (C : Codec) (x y : Bytes) : Prop := x ≠ y ∧ C.keccak x = C.keccak y

instance (C : Codec) (x y : Bytes) : Decidable (KeccakClash C x y) := by
  unfold KeccakClash; infer_instance

/-! ## Witness data

Chain `270` withdraws to L1 (chain id `1`). `wOne` is a one-call withdrawal, `wTwo` a two-call bundle
naming `0xBEEF` as its unbundler, `wOther` a one-call bundle from chain `999`. They are the bytes
`[1]`, `[2]` and `[3]`. -/

/-- The witness L1 asset router. -/
def wRouter : Address := 0xA5

/-- The witness unbundler. -/
def wUnbundler : Address := 0xBEEF

/-- The witness owner. -/
def wOwner : Address := 0x0A

/-- Some caller with no role. -/
def wAnyone : Address := 0xE0A

/-- A zero-value call to the router, with payload `p`. -/
def wCall (p : UInt8) : Call := ⟨1, false, wRouter, 0x10003, 0, [p]⟩

/-- A bundle from `src` with the given calls, naming `wUnbundler` on L1 as its unbundler. -/
def wBundle (src : ℕ) (calls : List Call) : Bundle :=
  ⟨1, src, 1, 1001, 0, calls, ⟨.empty, .evm 1 wUnbundler, false, 0⟩⟩

/-- One call. -/
def wOne : Bundle := wBundle 270 [wCall 7]

/-- Two calls. -/
def wTwo : Bundle := wBundle 270 [wCall 7, wCall 8]

/-- One call, from chain `999`. -/
def wOther : Bundle := wBundle 999 [wCall 9]

/-- A toy `keccak256`, injective on short byte strings. -/
def wKeccak (x : Bytes) : Word := (x.foldl (fun acc y => acc * 257 + y.toNat + 1) 0 : ℕ)

/-- The witness codec. -/
def wCodec : Codec where
  enc b := if b = wOne then [1] else if b = wTwo then [2] else if b = wOther then [3] else []
  decode x := if x = [1] then some wOne else if x = [2] then some wTwo
    else if x = [3] then some wOther else none
  keccak := wKeccak
  ethAssetId c := (c + 1000 : ℕ)

/-- The witness codec with a collision: `[3]` hashes like `[1]`. -/
def wClashCodec : Codec := { wCodec with keccak := fun x => if x = [3] then wKeccak [1] else wKeccak x }

/-- The witness deployment. -/
def wParams : Params := ⟨wCodec, 1, 0xC0DE, wRouter⟩

/-- The witness deployment with the colliding codec. -/
def wClashParams : Params := ⟨wClashCodec, 1, 0xC0DE, wRouter⟩

/-- An inclusion proof of a message of chain `270` sent by the center. -/
def wProof : InclusionProof := ⟨270, 5, 0, ⟨0, l2InteropCenterAddr, [0x99]⟩, []⟩

/-- `executeBundle` of `[1]` with an accepted proof; its call's target returns. -/
def wExecOne : Tx := ⟨4, .executeBundle wAnyone [1] wProof true, [.returns]⟩

/-- `verifyBundle` of the bytes `x` with an accepted proof. -/
def wVerify (x : Bytes) : Tx := ⟨1, .verifyBundle wAnyone x wProof true, []⟩

/-- `executeBundle` of `[2]` with an accepted proof. -/
def wExecTwo : Tx := ⟨4, .executeBundle wAnyone [2] wProof true, [.returns, .returns]⟩

/-- `unbundleBundle` of `[2]` by its unbundler, executing both calls; both targets return. -/
def wUnbundleTwo : Tx := ⟨5, .unbundleBundle wUnbundler [2] [.Executed, .Executed], [.returns, .returns]⟩

/-- `initialize(o)` called by `caller`. -/
def wInit (caller o : Address) : Tx := ⟨1, .admin caller (.initialize o), []⟩

/-- An administrative call by the owner. -/
def wAdmin (op : AdminOp) : Tx := ⟨1, .admin wOwner op, []⟩

/-- An administrative call by `caller`. -/
def wAdminBy (caller : Address) (op : AdminOp) : Tx := ⟨1, .admin caller op, []⟩

/-- `wOwner` initializes and pauses, then hands ownership to `wUnbundler`, which accepts it; then
`unpause` by `wOwner`, then `unpause` by `wUnbundler`. -/
def wHandoverRun : List Tx :=
  [wInit wOwner wOwner, wAdmin .pause, wAdmin (.transferOwnership wUnbundler),
    wAdminBy wUnbundler .acceptOwnership, wAdmin .unpause, wAdminBy wUnbundler .unpause]

/-- Unbundling `[2]` after the unbundler became the owner: call 0's target calls `pause()` as the
owner, call 1's target returns. -/
def wUnbundlePausing : Tx :=
  ⟨5, .unbundleBundle wUnbundler [2] [.Executed, .Executed],
    [.calls (.admin wUnbundler .pause) [] false .returns, .returns]⟩

/-- `executeBundle` of `[3]` by anyone, with no accepted proof. -/
def wExecOther : Tx := ⟨4, .executeBundle wAnyone [3] wProof false, [.returns]⟩

/-- `unbundleBundle` of `[1]` by its unbundler, executing call 0, whose target re-enters
`unbundleBundle` with the same request and then `executeBundle` of `[1]`, catching each failure if
`caught`, and returns. -/
def wUnbundleReentering (caught : Bool) : Tx :=
  ⟨8, .unbundleBundle wUnbundler [1] [.Executed],
    [.calls (.unbundleBundle wUnbundler [1] [.Executed]) [.returns] caught
      (.calls (.executeBundle wAnyone [1] wProof true) [.returns] caught .returns)]⟩

end Contracts.L1WithdrawalGate
