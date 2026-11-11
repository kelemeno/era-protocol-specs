import Mathlib.Tactic
import EraSpec.Core.Word
import EraSpec.Contracts.AtomicFlowManager.Specs.Model
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashEncoding

/-!
# Model: `InteropCenter` — sender salts, the atomic-value check, and the only `append`

Source: `l1-contracts/contracts/interop/InteropCenter.sol` in the pinned era-contracts tree
(`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), together with `atomic-interop/AtomicFlowManager.sol`,
`common/Messaging.sol` and `interop/IInteropCenter.sol` from the same tree. A bare `:N` is a line
of `InteropCenter.sol`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropCenter.Properties.Dispatch` and are proved in
`EraSpec.Contracts.InteropCenter.Proofs.Dispatch`.

## The code

Both public send entry points, `sendMessage` (:213-259) and `sendBundle` (:262-327), end in
`_sendBundle` (:464-586), which ends in `_dispatchBundle` (:639-659):

    // _sendBundle
    require(!isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt],
            InteropBundleSaltAlreadyUsed(msg.sender, _bundleAttributes.salt));      // :479-482
    isInteropBundleSaltUsed[msg.sender][_bundleAttributes.salt] = true;              // :483
    InteropBundle memory bundle = InteropBundle({
        sourceChainId: block.chainid,                                                // :500
        interopBundleSalt: keccak256(abi.encodePacked(msg.sender, _bundleAttributes.salt)), // :507
        calls: new InteropCall[](_callStarters.length),
        bundleAttributes: _bundleAttributes, ... });                                 // :498-510
    for (uint256 i = 0; i < callStartersLength; ++i) {
        ...
        InteropCall memory interopCall = _processCallStarter(_callStarters[i], _destinationChainId, msg.sender); // :539
        bundle.calls[i] = interopCall;                                               // :540
        totalBurnedCallsValue += _callStarters[i].callAttributes.interopCallValue;   // :541
        ...
    }
    ...                                                                              // fees, :548-567
    (bundleHash, msgHash) = _dispatchBundle(bundle, _atomicSend);                    // :574

    // _dispatchBundle
    bytes memory interopBundleBytes = abi.encode(_bundle);                           // :643
    bundleHash = InteropDataEncoding.encodeInteropBundleHash(block.chainid, interopBundleBytes); // :644
    if (_atomicSend.isAtomic) {
        _validateAtomicBundle(_bundle);                                              // :649
        IAtomicFlowManager(L2_ATOMIC_FLOW_MANAGER_ADDR).append({_flowId: _atomicSend.flowId,
            _bundleHash: bundleHash, ...});                                          // :650-655
    } else {
        msgHash = _sendBundleToL1(interopBundleBytes, _bundle.calls.length);         // :657
    }

    // _validateAtomicBundle (:670-677)
    for (...) { if (_bundle.calls[i].value != 0) revert AtomicBundleCallCarriesValue(i, ...); }

    // AtomicFlowManager.append (AtomicFlowManager.sol:87-102), `onlyInteropCenter` (:76-79):
    if (_state[_flowId][_bundleHash] != LegState.Unset) revert ManagerLegAlreadyCommitted(...); // :93
    _state[_flowId][_bundleHash] = LegState.Committed;                               // :95

`_processCallStarter` (:701-751) sets the call's `value` to the starter's `interopCallValue` in both
branches (:738, :747). A direct call copies the starter's recipient and data and has
`from = msg.sender` (:742-749). An indirect call asks the starter's recipient, an arbitrary
`IL2CrossChainSender`, for the actual recipient and calldata (:714-716, :732) and has
`from = that recipient` (:739); the indirect sender's own `interopCallValue` is only checked equal
(:723-729).

## The inventory the model rests on (checked against the pinned tree)

* `isInteropBundleSaltUsed` (:129) has one writer, :483, which writes `true`. Nothing clears it.
* `append` has one call site in `l1-contracts/contracts`, :650 (`grep -rn '\.append(' contracts/`).
  `_dispatchBundle` has one call site, :574, and `_sendBundle` has two, :247 (`sendMessage`, which
  always passes `isAtomic: false`, :252) and :320 (`sendBundle`, whose `AtomicSend` comes from
  `_parseAtomicSend`, :318, :874-883). No contract in the tree inherits `InteropCenter`.
* The manager's leg state `_state` (AtomicFlowManager.sol:53) has three writers: `append` (:95,
  `Unset → Committed`), `authorizeRefund` (:158-159, `Committed → Revertable`) and `claimRefund`
  (:170, :175, `Revertable → Reverted`). Its `initL2` (:69-74) writes only `L1_CHAIN_ID`.
* `msg.sender` equals the center only while the center's own code makes the call, so a direct
  transaction to `append` from any other account reverts at `onlyInteropCenter`.

## Modelling choices

* **One chain.** `Params` fixes `block.chainid`, the center's address, and the two functions
  `_dispatchBundle` composes: `abi.encode(InteropBundle)` (`Params.enc`, abstract — the ABI encoder of
  the nested struct is not transcribed) and `keccak256` (`Params.keccak`, abstract). The model
  itself takes **no hash or encoding premise**; the results that need one state it, in run-local
  form.
* **A revert is the absence of a step.** A successful `_sendBundle` is one `Step.send`: it marks
  the salt, and in the atomic branch commits the leg; a failing one changes nothing (`VM-REVERT`).
* **A send is one step.** `sendMessage` and `sendBundle` are `nonReentrant` (:217, :266), sharing
  the guard with `claimProtocolFees` and `claimZKFees` (:949, :965), so the external
  `initiateIndirectCall` (:714) cannot start a second dispatch inside the first, and it cannot call
  `append` as the center. `authorizeRefund` and `claimRefund` are permissionless and may run inside
  that call; they only move legs that are already not `Unset`, so running them before the send
  instead gives the same guards and the same final state. A send nested in `claimRefund`'s
  recovery calls (the manager has no reentrancy guard) runs after the claim's write (:175), which is
  the step sequence claim, then send.
* **Checks that only reject, and read nothing the model tracks, are omitted**: `whenNotPaused`, the
  destination checks (:378-396, :492-497), the L1-destination restrictions (:520-538), the fee and
  `msg.value` checks (:407-456, :548-557), the indirect value equality (:723-729), attribute
  parsing (:776-868), the commitment-tree insertion inside `append` (AtomicFlowManager.sol:97-99),
  and every proof check of `authorizeRefund` / `claimRefund` (so the model's `authorize` may move
  any `Committed` leg). Omitting a rejecting check only adds runs, so every safety result holds a
  fortiori. The witnesses send to a chain other than the source with a nonzero destination
  base-token asset id; their byte fields (calldata, execution and unbundler addresses) are
  placeholders, which no result reads.
* **The three checks the results depend on are switches** (`Checks`): the salt check (:479-482),
  `_validateAtomicBundle` (:649) and `onlyInteropCenter` (AtomicFlowManager.sol:76-79, :92). The
  deployed code has all three (`deployed`); each countermodel turns exactly one off.
* **The indirect sender is arbitrary code.** The recipient and calldata it returns are free
  (`FormsCall`); only the fields the center itself writes are pinned.
* **A ghost log** records every successful dispatch, oldest first. It is not storage; it is what
  lets the results name *which* dispatch a committed leg or a bundle hash came from.
* **Omitted state and fields.** Fee balances, the ZK token cache, the pause flag, events,
  `__DEPRECATED_interopBundleNonce` (:96, never read or written), the constant `version` fields
  (:499, :734, :743) and the reserved `shadowAccount` (always `false`). Center and manager upgrades
  that could rewrite storage are `OPS-CONFIG`.
* **`sendMessage` and the `atomicBundle` attribute.** `sendMessage` parses its attributes with
  `CallAndBundleAttributes` (:222-225), which accepts the `atomicBundle` attribute (:843-854), and
  then passes `isAtomic: false` (:252) regardless. Such a bundle is published to L1. The model's
  `send` takes the `AtomicSend` that reaches `_dispatchBundle`, so this is a non-atomic dispatch.
-/

namespace Contracts.InteropCenter

open AttackVectors.BundleHashEncoding (toBytesBE fromBytesBE abiEncode)
open Contracts.AtomicFlowManager (Manager LegState AppendGuard AuthorizeGuard ClaimGuard)

/-! ## Words, addresses and the bundle -/

/-- `bytes32` and `uint256` words: salts, hashes, chain ids, asset ids, flow ids. -/
abbrev Word := UInt256

/-- An `address`: 20 bytes. -/
abbrev Address := Fin (256 ^ 20)

/-- `InteropCall` (`common/Messaging.sol:257-264`), without the constant `version` and the
reserved `shadowAccount`. -/
structure InteropCall where
  /-- `to`: the contract called on the destination. -/
  target : Address
  /-- `from`: the original sender, or the indirect sender contract for an indirect call. -/
  fromAddr : Address
  /-- `value`: base token sent with the call on the destination. -/
  value : ℕ
  /-- `data`: the calldata. -/
  data : List UInt8
deriving DecidableEq

/-- `BundleAttributes` (`Messaging.sol:241-246`). -/
structure BundleAttributes where
  executionAddress : List UInt8
  unbundlerAddress : List UInt8
  useFixedFee : Bool
  /-- The user-provided salt, from the `interopBundleSalt` attribute (:855-863); `0` if absent. -/
  salt : Word
deriving DecidableEq

/-- `InteropBundle` (`Messaging.sol:288-296`), without the constant `version`. -/
structure Bundle where
  sourceChainId : Word
  destinationChainId : Word
  destinationBaseTokenAssetId : Word
  /-- `keccak256(abi.encodePacked(sender, salt))` (:507). -/
  interopBundleSalt : Word
  calls : List InteropCall
  /-- The bundle carries the attributes, user salt included (:509). -/
  bundleAttributes : BundleAttributes
deriving DecidableEq

/-- `CallAttributes` (`Messaging.sol:217-221`). -/
structure CallAttributes where
  interopCallValue : ℕ
  indirectCallMessageValue : ℕ
  indirectCall : Bool
deriving DecidableEq

/-- `InteropCallStarterInternal` (`Messaging.sol:208-212`): a parsed call starter. -/
structure CallStarter where
  /-- `to`: the recipient, or the indirect sender for an indirect call. -/
  target : Address
  data : List UInt8
  callAttributes : CallAttributes
deriving DecidableEq

/-- `IInteropCenter.AtomicSend` (`IInteropCenter.sol:16-21`): the out-of-band atomic metadata. It
is not part of the bundle, so the bundle hash does not depend on the flow id (:634-638). -/
structure AtomicSend where
  flowId : Word
  lowNullifierIndex : ℕ
  deadline : ℕ
  isAtomic : Bool
deriving DecidableEq

/-! ## What `_dispatchBundle` hashes -/

/-- The deployment constants of one chain, and the two functions `_dispatchBundle` composes. -/
structure Params where
  /-- `block.chainid`. -/
  chainId : Word
  /-- `L2_INTEROP_CENTER_ADDR`, the only caller `append` accepts (`interopCenter()`,
  AtomicFlowManager.sol:193-195). -/
  center : Address
  /-- `abi.encode(InteropBundle)` (:643). -/
  enc : Bundle → List UInt8
  /-- `keccak256`. -/
  keccak : List UInt8 → Word

/-- `abi.encodePacked(msg.sender, _bundleAttributes.salt)` (:507): 20 address bytes, then the 32
salt bytes. -/
def saltPreimage (sender : Address) (salt : Word) : List UInt8 :=
  toBytesBE 20 sender.val ++ toBytesBE 32 salt.val

/-- `abi.encode(block.chainid, abi.encode(bundle))`: what `encodeInteropBundleHash` (:644,
`InteropDataEncoding.sol:11-13`) hashes. `abiEncode` is the byte model of
`abi.encode(uint256, bytes)` from `InteropDataEncoding/Specs/BundleHashEncoding.lean`. -/
def bundlePreimage (P : Params) (b : Bundle) : List UInt8 :=
  abiEncode P.chainId.val (P.enc b)

/-- The bundle hash (:644). -/
def bundleHash (P : Params) (b : Bundle) : Word :=
  P.keccak (bundlePreimage P b)

/-- `_validateAtomicBundle(b)` (:670-677) does not revert: no call carries native value. -/
def Validated (b : Bundle) : Prop := ∀ c ∈ b.calls, c.value = 0

instance (b : Bundle) : Decidable (Validated b) := by
  unfold Validated; infer_instance

/-- `_totalBurnedCallsValue` (:513, :541): the base token `_ensureCorrectTotalValue` burns through
the `BaseTokenHolder` (:429-434) or deposits through `bridgehubDepositBaseToken` (:440-447) when it
is nonzero. -/
def totalBurnedCallsValue (starters : List CallStarter) : ℕ :=
  (starters.map fun cs => cs.callAttributes.interopCallValue).sum

/-! ## Forming the bundle -/

/-- `_processCallStarter(cs, _, sender)` (:701-751) may return `c`. -/
structure FormsCall (sender : Address) (cs : CallStarter) (c : InteropCall) : Prop where
  /-- Both branches: `value: _callStarter.callAttributes.interopCallValue` (:738, :747). -/
  value : c.value = cs.callAttributes.interopCallValue
  /-- Indirect: `from: recipientAddress` (:739); recipient and data are what the indirect sender
  returned (:714-716, :732), so free. -/
  indirect : cs.callAttributes.indirectCall = true → c.fromAddr = cs.target
  /-- Direct: the starter's recipient and data, `from: _sender` (:742-749). -/
  direct : cs.callAttributes.indirectCall = false →
    c.target = cs.target ∧ c.data = cs.data ∧ c.fromAddr = sender

/-- One successful `_sendBundle`, as the ghost log records it. -/
structure Dispatch where
  /-- `msg.sender` of `sendBundle` / `sendMessage`. -/
  sender : Address
  /-- The parsed call starters. -/
  starters : List CallStarter
  /-- The bundle `_sendBundle` built and `_dispatchBundle` hashed. -/
  bundle : Bundle
  /-- The `AtomicSend` passed to `_dispatchBundle`. -/
  atomicSend : AtomicSend
deriving DecidableEq

/-- The user salt, `_bundleAttributes.salt`. -/
def Dispatch.salt (d : Dispatch) : Word := d.bundle.bundleAttributes.salt

/-- The key `isInteropBundleSaltUsed` is indexed by (:480, :483). -/
def Dispatch.key (d : Dispatch) : Address × Word := (d.sender, d.salt)

/-- Whether `_dispatchBundle` took the atomic branch (:646). -/
abbrev Dispatch.isAtomic (d : Dispatch) : Bool := d.atomicSend.isAtomic

/-- `d.bundle` is the bundle `_sendBundle` builds for `d.sender` from `d.starters` (:498-546).
The destination, its base-token asset id and the attributes are inputs, so they are free. -/
structure FormedBy (P : Params) (d : Dispatch) : Prop where
  /-- `sourceChainId: block.chainid` (:500). -/
  source : d.bundle.sourceChainId = P.chainId
  /-- `interopBundleSalt: keccak256(abi.encodePacked(msg.sender, _bundleAttributes.salt))` (:507). -/
  salt : d.bundle.interopBundleSalt = P.keccak (saltPreimage d.sender d.salt)
  /-- `bundle.calls[i] = _processCallStarter(_callStarters[i], _, msg.sender)` (:539-540). -/
  calls : List.Forall₂ (FormsCall d.sender) d.starters d.bundle.calls

/-! ## State and steps -/

/-- One chain's center and flow manager. -/
structure State where
  /-- `isInteropBundleSaltUsed[user][salt]` (:129). -/
  saltUsed : Address → Word → Bool
  /-- The manager's `_state[flowId][bundleHash]` (AtomicFlowManager.sol:53). -/
  manager : Manager
  /-- Ghost: every successful dispatch, oldest first. -/
  log : List Dispatch

/-- Fresh storage: no salt used, every leg `Unset`, nothing dispatched. -/
def init : State := ⟨fun _ _ => false, Contracts.AtomicFlowManager.empty, []⟩

/-- `isInteropBundleSaltUsed[a][s] = true` (:483). -/
def markSalt (u : Address → Word → Bool) (a : Address) (s : Word) : Address → Word → Bool :=
  fun a' s' => if a' = a ∧ s' = s then true else u a' s'

/-- The state after a successful `_sendBundle` of `d`: the salt is marked; in the atomic branch the
leg `(flowId, bundleHash)` is `Committed` (AtomicFlowManager.sol:95); the log records `d`. -/
def State.afterSend (P : Params) (S : State) (d : Dispatch) : State where
  saltUsed := markSalt S.saltUsed d.sender d.salt
  manager := if d.isAtomic then S.manager.set d.atomicSend.flowId (bundleHash P d.bundle) .Committed
    else S.manager
  log := S.log ++ [d]

/-- Which of the three checks the code performs. The deployed code performs all three. -/
structure Checks where
  /-- `require(!isInteropBundleSaltUsed[msg.sender][salt])` (:479-482). -/
  saltCheck : Bool
  /-- `_validateAtomicBundle(_bundle)` before `append` (:649). -/
  atomicValueCheck : Bool
  /-- `onlyInteropCenter` on `append` (AtomicFlowManager.sol:76-79, :92). -/
  onlyInteropCenter : Bool

/-- The deployed code. -/
def deployed : Checks := ⟨true, true, true⟩

/-- The deployed code without the salt check. -/
def withoutSaltCheck : Checks := ⟨false, true, true⟩

/-- The deployed code without `_validateAtomicBundle`. -/
def withoutValueCheck : Checks := ⟨true, false, true⟩

/-- The deployed code without `onlyInteropCenter` on `append`. -/
def withoutOnlyInteropCenter : Checks := ⟨true, true, false⟩

/-- One transaction that changes the modelled state. -/
inductive Step (K : Checks) (P : Params) : State → State → Prop
  /-- `sendBundle` / `sendMessage` by `d.sender`, through `_sendBundle` and `_dispatchBundle`. -/
  | send {S : State} (d : Dispatch) :
      (K.saltCheck = true → S.saltUsed d.sender d.salt = false) →
      FormedBy P d →
      (d.isAtomic = true → K.atomicValueCheck = true → Validated d.bundle) →
      (d.isAtomic = true → AppendGuard S.manager d.atomicSend.flowId (bundleHash P d.bundle)) →
      Step K P S (S.afterSend P d)
  /-- `authorizeRefund` marking one of the flow's legs (AtomicFlowManager.sol:158-159). Its proof
  checks are omitted. -/
  | authorize {S : State} (f h : Word) :
      AuthorizeGuard S.manager f h →
      Step K P S { S with manager := S.manager.set f h .Revertable }
  /-- `claimRefund` (AtomicFlowManager.sol:170, :175). The recovery calls are external. -/
  | claim {S : State} (f h : Word) :
      ClaimGuard S.manager f h →
      Step K P S { S with manager := S.manager.set f h .Reverted }
  /-- A transaction calling `append` directly, from any account other than the center: the
  center's code calls `append` only at :650, inside `send`. -/
  | foreignAppend {S : State} (caller : Address) (f h : Word) :
      caller ≠ P.center →
      (K.onlyInteropCenter = true → caller = P.center) →
      AppendGuard S.manager f h →
      Step K P S { S with manager := S.manager.set f h .Committed }

/-- Reachability. -/
inductive Reach (K : Checks) (P : Params) : State → State → Prop
  | refl {S : State} : Reach K P S S
  | tail {S T U : State} : Reach K P S T → Step K P T U → Reach K P S U

/-! ## Derived notions -/

/-- `b` is a bundle the center appended: the bundle of an atomic dispatch in the log. -/
def AppendedOn (S : State) (b : Bundle) : Prop :=
  ∃ d ∈ S.log, d.isAtomic = true ∧ d.bundle = b

/-- The bytes `claimRefund(_flowId, x)` hashes for the bytes `x` it is given
(AtomicFlowManager.sol:166-167): it decodes `x` and hashes `abi.encode(bundle.sourceChainId, x)`,
with the decoded bundle's own source chain rather than `block.chainid`. `dec` is `abi.decode`. -/
def claimPreimage (dec : List UInt8 → Bundle) (x : List UInt8) : List UInt8 :=
  abiEncode (dec x).sourceChainId.val x

/-- **A PINNED SALT COLLISION.** keccak collides on exactly the `abi.encodePacked(sender, salt)`
preimages of the two given dispatches: they differ, and hash equal. -/
def SaltClash (P : Params) (d d' : Dispatch) : Prop :=
  saltPreimage d.sender d.salt ≠ saltPreimage d'.sender d'.salt ∧
    P.keccak (saltPreimage d.sender d.salt) = P.keccak (saltPreimage d'.sender d'.salt)

/-- **THE ONLY WAY TWO DISPATCHES SHARE A BUNDLE.** Two different senders used the same salt, and
keccak collides on their two packed preimages. -/
def CrossSenderSaltClash (P : Params) (d d' : Dispatch) : Prop :=
  d.salt = d'.salt ∧ d.sender ≠ d'.sender ∧ SaltClash P d d'

/-- **A PINNED BUNDLE-HASH COLLISION.** keccak collides on exactly the two bundle-hash preimages
`abi.encode(block.chainid, abi.encode(b))` of the two given bundles. -/
def BundleHashClash (P : Params) (b b' : Bundle) : Prop :=
  bundlePreimage P b ≠ bundlePreimage P b' ∧ bundleHash P b = bundleHash P b'

/-- **A PINNED COLLISION OF THE WHOLE BUNDLE HASH.** Two different bundles, one bundle hash. It
covers an ambiguity of the encoder and a keccak collision alike, and names the two bundles. -/
def BundleClash (P : Params) (b b' : Bundle) : Prop :=
  b ≠ b' ∧ bundleHash P b = bundleHash P b'

/-- keccak is injective on the explicit finite list `L` of preimages. -/
def KeccakInjOn (k : List UInt8 → Word) (L : List (List UInt8)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, k x = k y → x = y

/-- The encoder separates the bundles of the explicit finite list `L`. `abi.encode` of a value is
decodable (`claimRefund` decodes these very bytes, AtomicFlowManager.sol:166), so it separates any
two bundles; the results ask it only of the bundles a run dispatched (`SOL-ABI`). -/
def EncInjOn (enc : Bundle → List UInt8) (L : List Bundle) : Prop :=
  ∀ b ∈ L, ∀ b' ∈ L, enc b = enc b' → b = b'

/-- The salt preimages a run hashed, one per dispatch. -/
def saltPreimages (log : List Dispatch) : List (List UInt8) :=
  log.map fun d => saltPreimage d.sender d.salt

/-- The bundle-hash preimages a run hashed, one per dispatch. -/
def bundlePreimages (P : Params) (log : List Dispatch) : List (List UInt8) :=
  log.map fun d => bundlePreimage P d.bundle

/-! ## Witness data

A toy keccak that reads the last 32 bytes as a word, and a toy encoder that writes the bundle's two
salt words. Together they separate every preimage the witness runs hash. -/

/-- The last 32 bytes of `l`, as a word. -/
def lastWord (l : List UInt8) : Word := Fin.ofNat _ (fromBytesBE l)

/-- The two salt words of the bundle. -/
def saltWordsEncoder (b : Bundle) : List UInt8 :=
  toBytesBE 32 b.interopBundleSalt.val ++ toBytesBE 32 b.bundleAttributes.salt.val

/-- The honest witness chain: chain `324`, center `0x8010`. -/
def wParams : Params := ⟨324, 0x8010, saltWordsEncoder, lastWord⟩

/-- The colliding witness chain: as `wParams`, but keccak is constant. -/
def collidingParams : Params := ⟨324, 0x8010, saltWordsEncoder, fun _ => 0⟩

/-- Bundle attributes with the given salt. The unbundler is a nonempty placeholder: `sendBundle`
would put a formatted ERC-7930 address there (:314-316), and no result reads it. -/
def wAttrs (s : Word) : BundleAttributes := ⟨[], [1], false, s⟩

/-- A direct call starter to contract `5` with base-token value `v`. -/
def wDirect (v : ℕ) : CallStarter := ⟨5, [], ⟨v, 0, false⟩⟩

/-- An indirect call starter through the indirect sender `9` (say, the asset router). -/
def wIndirect : CallStarter := ⟨9, [], ⟨0, 0, true⟩⟩

/-- The bundle `sender` forms on chain `P` with salt `s` and the calls `cs`, to chain `325`. -/
def wBundle (P : Params) (sender : Address) (s : Word) (cs : List InteropCall) : Bundle :=
  ⟨P.chainId, 325, 1, P.keccak (saltPreimage sender s), cs, wAttrs s⟩

/-- Sender `1`, salt `1`: an atomic leg of flow `7` with one direct zero-value call. -/
def wD1 : Dispatch :=
  ⟨1, [wDirect 0], wBundle wParams 1 1 [⟨5, 1, 0, []⟩], ⟨7, 0, 100, true⟩⟩

/-- Sender `2`, salt `2`: a public bundle with one direct call carrying value `9`. -/
def wD2 : Dispatch :=
  ⟨2, [wDirect 9], wBundle wParams 2 2 [⟨5, 2, 9, []⟩], ⟨0, 0, 0, false⟩⟩

/-- A decoder for the honest run: it inverts `saltWordsEncoder` on the two bundles the run
dispatches. -/
def wDec (x : List UInt8) : Bundle :=
  if x = saltWordsEncoder wD2.bundle then wD2.bundle else wD1.bundle

/-- The honest run's states: dispatch `wD1`, dispatch `wD2`, authorize `wD1`'s leg. -/
def wS1 : State := init.afterSend wParams wD1
def wS2 : State := wS1.afterSend wParams wD2
def wS3 : State :=
  { wS2 with manager := wS2.manager.set 7 (bundleHash wParams wD1.bundle) .Revertable }

end Contracts.InteropCenter
