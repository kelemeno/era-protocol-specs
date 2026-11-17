import Mathlib.Tactic
import EraSpec.Contracts.InteropCenter.Specs.Dispatch

/-!
# Model: `InteropCenter` send path at head — every L2→L2 send is atomic

Source: era-contracts **main `3605e82dbdca5b60bd7bc6bde14ebb52a6b09b73`**,
`l1-contracts/contracts/interop/InteropCenter.sol` (a bare `:N` is a line of that file), with
`interop/InteropAttributeParser.sol`, `interop/IERC7786Attributes.sol`, `interop/IInteropCenter.sol`,
`interop/InteropDataEncoding.sol`, `atomic-interop/AtomicFlowManager.sol`,
`atomic-interop/IAtomicInterop.sol` and `common/Messaging.sol` from the same commit. The pin model of
the same path is `Specs/Dispatch.lean` (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`); it is unchanged.

**This file is definitions only.** The results are in
`EraSpec.Contracts.InteropCenter.Properties.SendAtHead` and are proved in
`EraSpec.Contracts.InteropCenter.Proofs.SendAtHead`.

## What changed since the pin (a1d5c34d4 #2280, 8935a573e #2348, #2312, #2339)

* **`sendMessage` parses the `atomicBundle` attribute.** At the pin it parsed its attributes under
  `CallAndBundleAttributes`, which accepts `atomicBundle`, and then passed a constant non-atomic
  `AtomicSend` (pin :246-252): the round-5 finding O1-1. At head:

      (CallAttributes memory callAttributes, BundleAttributes memory bundleAttributes) = parseAttributes(
          attributes, AttributeParsingRestrictions.CallAndBundleAttributes);                     // :206-209
      ...
      AtomicSend memory atomicSend = _parser().parseAtomicSend(attributes);                      // :230

* **Every L2→L2 send is atomic.** `_sendBundle` begins with

      if (_atomicSend.isAtomic) {
          require(_destinationChainId != L1_CHAIN_ID, AtomicBundleToL1NotSupported());           // :552
      } else {
          require(_destinationChainId == L1_CHAIN_ID, NonAtomicSendUnsupported());               // :554
      }

  and `sendMessage` only sends L2→L2 (`_ensureL2ToL2`, :204, :396-402).
* **`_dispatchBundle` branches on the destination** (:721-741): an L1 destination publishes
  `bytes.concat(BUNDLE_IDENTIFIER, abi.encode(_bundle))` to L1 (:727-731); any other destination calls
  `append(bundleHash, lowNullifierIndex, flowPreimage)` (:736-740). Public L2→L2 interop is gone.
* **`_validateAtomicBundle` is gone.** Native-value legs are allowed and are refunded on timeout by
  `AtomicFlowManager._recoverBundle` (NatSpec :707-709). Instead, indirect call starters must target
  the asset router (`IndirectCallOnlyToAssetRouter`, :664-667) and carry no `interopCallValue`
  (`IndirectCallCannotCarryValue`, :673-676); an L1 destination takes one indirect zero-value call to
  the asset router (:645-657, and :259-261 for the count).
* **The bundle hash has no outer chain id**: `keccak256(abi.encode(bundle))` (:689-691,
  `InteropDataEncoding.sol:14-16`); `claimRefund` hashes the bytes it is given the same way
  (AtomicFlowManager.sol:249). The source chain is the bundle's own `sourceChainId` field (:633).
* **`append` takes the flow preimage** (AtomicFlowManager.sol:103-172): it recomputes
  `flowId = keccak256(abi.encode(preimage))` (:108, :364) and requires the bundle hash to be one of the
  flow's legs (:129-139), declared with this chain as its source (:140-146).

`IERC7786Attributes.sol:27-31` now reads: "Marks a bundle as an atomic interop leg (bundle-level
attribute): the InteropCenter appends the bundle's commit value to the interop IMT instead of
publishing it to L1. ... the AtomicFlowManager recomputes `flowId` and requires this bundle's hash to
be one of its legs, else the send reverts."

## The inventory the model rests on (checked against main)

* `isInteropBundleSaltUsed` (:125) has one writer, :565, which writes `true`.
* `append` has one call site, :736, in `_dispatchBundle`; `_dispatchBundle` has one call site, :601,
  in `_sendBundle`; `_sendBundle` has two, :232 (`sendMessage`) and :271 (`sendBundle`). No contract
  inherits `InteropCenter`. `previewBundleHash`/`previewMessageHash` (:281-332) build a bundle and
  always revert (:350), so they are no step.
* `L2_TO_L1_MESSENGER_SYSTEM_CONTRACT.sendToL1` is called by the center only at :729.
* The manager's `_state` (AtomicFlowManager.sol:60) has three writers: `append` (:165,
  `Unset → Committed`), `authorizeRefund` (:241, `Committed → Revertable`), `claimRefund` (:257,
  `Revertable → Reverted`).

## Modelling choices

* **One chain**, as in the pin model. `Params` fixes `block.chainid`, `L1_CHAIN_ID`, the center and
  asset-router addresses, and the abstract functions the path composes: `abi.encode(InteropBundle)`,
  `abi.encode(AtomicFlowPreimage)`, `keccak256`, `InteroperableAddress.formatEvmV1`. The center's
  `L1_CHAIN_ID` (:95) and the manager's (AtomicFlowManager.sol:64) are one parameter: both are set at
  genesis to the L1 chain id. The model takes **no hash or encoding premise**.
* **Attributes are decoded values.** An `Attribute` is one of the seven supported selectors
  (InteropAttributeParser.sol:143-154) with its decoded payload, or an unsupported selector.
  `parseAttributes` is transcribed exactly: an unsupported selector, a repeated attribute, or one
  that the restriction mask forbids reverts (:41-51); the payload decoding writes the fields of
  :55-77. Malformed payloads (`AttributesDecoder` reverts) and malformed ERC-7930 addresses are
  reject-only and omitted. The pin's `parseAttributes` (pin :776-868) accepts and decodes exactly
  the same lists (`pinAllowed`, `MaskTableIsPinTable`).
* **A revert is the absence of a step; a send is one step** (`nonReentrant`, :198, :249), as in the
  pin model. Indirect calls now reach only the asset router (:664-667).
* **Reject-only checks that read nothing the model tracks are omitted**: `whenNotPaused` (main only;
  draft/v0.35.0 has no pause), the ERC-7930 format checks (:250, :364-391, :487, :802-805), the
  destination's base-token lookup and v0.35's `isPeerAllowed` (:694-698), fees and `msg.value`
  (:415-457, :578-583), the indirect value equality (:784-794), and in `append` the version, leg cap,
  sortedness and length checks (AtomicFlowManager.sol:346-363), the settlement-layer check (:109),
  the expired-flow gate (:119-124), the other legs' registration (:151-159) and the tree insert
  (:167-169). `append`'s leg-membership and source-chain checks (:129-146) are kept: they are what
  the `atomicBundle` NatSpec promises. Omitting a rejecting check only adds runs.
* **Six checks are switches** (`Checks`): `sendMessage`'s `parseAtomicSend` (:230; the pin passed a
  constant), `_ensureL2ToL2` (:204), the atomicity gate (:551-555), the salt check (:561-564), the
  indirect-call restrictions (:658-677), and `onlyInteropCenter` (AtomicFlowManager.sol:87-92,
  :107). The deployed code has all six (`deployed`); each countermodel turns one off.
* **The asset router's returned recipient and calldata are free** (`FormsCall`, unchanged from the
  pin: :806-822 set `value` from the starter, `from` to the starter's target for an indirect call
  and to `msg.sender` for a direct one).
* **A ghost log** records every successful dispatch, with its entry point and raw attribute lists.
  `l1Messages` is the real messenger traffic of the center.
* **Omitted**: fee state, the ZK-token cache, events, the per-call `MessageSent` ids, the constant
  `version` fields and the reserved `shadowAccount`, `__DEPRECATED_interopBundleNonce` (:99), and
  draft/v0.35.0's `INTEROP_FEE_UNITS_SLOT` counter. Upgrades are `OPS-CONFIG`.

On draft/v0.35.0 (`d9f678900e1bc8286412b78f56d4a9f443983c29`) this path differs only by reject-only
checks (no `whenNotPaused`, plus `isPeerAllowed` in `_getDestinationBaseTokenAssetId`) and the
fee-unit counter. The cited `InteropCenter.sol` lines move: `sendMessage` :197-245 and `sendBundle`
:248-281 (`parseAtomicSend` :233, :272), `_ensureL2ToL2` :399-405; the gate :552-556, the salt check
:562-566, `_buildInteropBundle` :621-687, `_hashBundle` :690-692; `_dispatchBundle` :727-750
(publish :735, `append` :742); `_processCallStarter` :776-832. `InteropAttributeParser.sol` and
`IERC7786Attributes.sol` are byte-identical, and `AtomicFlowManager.append` is unchanged (the v0.35
`_checkLegSourceAllowed` is in `requireFlowFinalized` and `authorizeRefund` only). So the model also
describes v0.35.0.
-/

namespace Contracts.InteropCenter.SendAtHead

open Contracts.AtomicFlowManager (Manager LegState AuthorizeGuard ClaimGuard)
open AttackVectors.BundleHashEncoding (toBytesBE)

/-! ## Flow preimages and the out-of-band atomic metadata -/

/-- `AtomicFlowPreimage` (`atomic-interop/IAtomicInterop.sol:50-56`). -/
structure FlowPreimage where
  /-- `bytes1 version` (must be `ATOMIC_FLOW_PREIMAGE_VERSION`, checked in `append`, omitted). -/
  version : ℕ
  /-- `uint64 deadline`. -/
  deadline : ℕ
  settlementLayerChainId : Word
  /-- Every leg's bundle hash. -/
  legBundleHashes : List Word
  /-- Each leg's source chain, aligned with `legBundleHashes`. -/
  legSourceChainIds : List Word
deriving DecidableEq

/-- `IInteropCenter.AtomicSend` at head (`interop/IInteropCenter.sol:18-22`): the send-side metadata
parsed from the `atomicBundle` attribute, kept out of the bundle so that the bundle hash does not
depend on the flow (:714-718). -/
structure AtomicSend where
  flowPreimage : FlowPreimage
  lowNullifierIndex : ℕ
  isAtomic : Bool
deriving DecidableEq

/-- The zero `AtomicSend` (a fresh memory struct): what `parseAtomicSend` returns when no
`atomicBundle` attribute is present. The pin's `sendMessage` constant (pin :252) is the same zero
struct in the pin's layout. -/
def AtomicSend.empty : AtomicSend := ⟨⟨0, 0, 0, [], []⟩, 0, false⟩

/-! ## ERC-7786 attributes -/

/-- A decoded ERC-7786 attribute. The seven supported selectors are those of
`_getERC7786AttributeSelectors` (InteropAttributeParser.sol:143-154), in that order; `unsupported`
is any other selector. The payload is the decoded value (`AttributesDecoder`). -/
inductive Attribute
  /-- `interopCallValue(uint256)`. -/
  | interopCallValue (value : ℕ)
  /-- `indirectCall(uint256 _indirectCallMessageValue)`. -/
  | indirectCall (messageValue : ℕ)
  /-- `executionAddress(bytes)`. -/
  | executionAddress (addr : List UInt8)
  /-- `unbundlerAddress(bytes)`. -/
  | unbundlerAddress (addr : List UInt8)
  /-- `useFixedFee(bool)`. -/
  | useFixedFee (useFixed : Bool)
  /-- `atomicBundle(AtomicFlowPreimage, uint256 _lowNullifierIndex)` (IERC7786Attributes.sol:33). -/
  | atomicBundle (flowPreimage : FlowPreimage) (lowNullifierIndex : ℕ)
  /-- `interopBundleSalt(bytes32)`. -/
  | interopBundleSalt (salt : Word)
  /-- Any other selector. -/
  | unsupported (selector : ℕ)
deriving DecidableEq

/-- `_attributeIndex(selector)` (InteropAttributeParser.sol:112-122): the attribute's position in the
supported list; `none` is the `UnsupportedAttribute` revert (:121). -/
def Attribute.index : Attribute → Option ℕ
  | .interopCallValue _ => some 0
  | .indirectCall _ => some 1
  | .executionAddress _ => some 2
  | .unbundlerAddress _ => some 3
  | .useFixedFee _ => some 4
  | .atomicBundle _ _ => some 5
  | .interopBundleSalt _ => some 6
  | .unsupported _ => none

/-- Whether the attribute is `atomicBundle`: `bytes4(_attributes[i]) == atomicBundle.selector`
(InteropAttributeParser.sol:87). -/
def Attribute.isAtomicBundle : Attribute → Bool
  | .atomicBundle _ _ => true
  | _ => false

/-- The list carries an `atomicBundle` attribute. -/
def HasAtomicBundle (attrs : List Attribute) : Prop :=
  ∃ pre lni, Attribute.atomicBundle pre lni ∈ attrs

/-- `IInteropCenter.AttributeParsingRestrictions` (`interop/IInteropCenter.sol:61-66`). -/
inductive Restriction
  | onlyInteropCallValue
  | onlyCallAttributes
  | onlyBundleAttributes
  | callAndBundleAttributes
deriving DecidableEq

/-- `uint8(_restriction)`. -/
def Restriction.toNat : Restriction → ℕ
  | .onlyInteropCallValue => 0
  | .onlyCallAttributes => 1
  | .onlyBundleAttributes => 2
  | .callAndBundleAttributes => 3

/-- `_getAttributeRestrictionMasks()` (InteropAttributeParser.sol:128-139): bit `b` of entry `i` is
set iff attribute `i` is allowed under restriction `b`. -/
def restrictionMask : ℕ → ℕ
  | 0 => 11
  | 1 => 10
  | 2 => 12
  | 3 => 12
  | 4 => 12
  | 5 => 12
  | 6 => 12
  | _ => 0

/-- `(allowedRestrictions[idx] >> uint8(_restriction)) & 1 == 1` (InteropAttributeParser.sol:47-50). -/
def allowedUnder (idx : ℕ) (r : Restriction) : Bool :=
  (restrictionMask idx >>> r.toNat) &&& 1 == 1

/-- The pin's table, written out as the explicit `_restriction == …` disjunctions of pin
`InteropCenter.sol:791-863` (one branch per selector, same order). -/
def pinAllowed : ℕ → Restriction → Bool
  | 0, r => r == .onlyInteropCallValue || r == .onlyCallAttributes || r == .callAndBundleAttributes
  | 1, r => r == .onlyCallAttributes || r == .callAndBundleAttributes
  | _, r => r == .onlyBundleAttributes || r == .callAndBundleAttributes

/-- `CallAttributes` with every field zero: the fresh memory struct `parseAttributes` returns
(`indirectCall` defaults to `false`, InteropAttributeParser.sol:31-32). -/
def noCallAttributes : CallAttributes := ⟨0, 0, false⟩

/-- `BundleAttributes` with every field zero. -/
def noBundleAttributes : BundleAttributes := ⟨[], [], false, 0⟩

/-- The fields one attribute writes (InteropAttributeParser.sol:55-77). `atomicBundle` writes
nothing: its payload is parsed separately by `parseAtomicSend` and kept out of the bundle (:68-73). -/
def Attribute.apply : Attribute → CallAttributes × BundleAttributes → CallAttributes × BundleAttributes
  | .interopCallValue v, (ca, ba) => ({ ca with interopCallValue := v }, ba)
  | .indirectCall m, (ca, ba) => ({ ca with indirectCall := true, indirectCallMessageValue := m }, ba)
  | .executionAddress a, (ca, ba) => (ca, { ba with executionAddress := a })
  | .unbundlerAddress a, (ca, ba) => (ca, { ba with unbundlerAddress := a })
  | .useFixedFee b, (ca, ba) => (ca, { ba with useFixedFee := b })
  | .atomicBundle _ _, x => x
  | .interopBundleSalt s, (ca, ba) => (ca, { ba with salt := s })
  | .unsupported _, x => x

/-- The loop of `parseAttributes` (InteropAttributeParser.sol:40-78), from the set `used` of indices
seen so far (`attributeUsed`, :38) and the fields written so far. `none` is a revert:
`UnsupportedAttribute` (:44, :121), `AttributeAlreadySet` (:46), `AttributeViolatesRestriction`
(:47-50). -/
def parseFrom (r : Restriction) :
    List ℕ → CallAttributes × BundleAttributes → List Attribute →
      Option (CallAttributes × BundleAttributes)
  | _, x, [] => some x
  | used, x, a :: rest =>
    match a.index with
    | none => none
    | some i =>
      if i ∈ used then none
      else if allowedUnder i r then parseFrom r (i :: used) (a.apply x) rest
      else none

/-- `parseAttributes(_attributes, _restriction)` (InteropAttributeParser.sol:27-79; forwarded by
`InteropCenter.parseAttributes`, :851-858). -/
def parseAttributes (attrs : List Attribute) (r : Restriction) :
    Option (CallAttributes × BundleAttributes) :=
  parseFrom r [] (noCallAttributes, noBundleAttributes) attrs

/-- `parseAtomicSend(_attributes)` (InteropAttributeParser.sol:82-96): the payload of the first
`atomicBundle` attribute, with `isAtomic = true` (:87-93); the zero struct if there is none. -/
def parseAtomicSend : List Attribute → AtomicSend
  | [] => AtomicSend.empty
  | .atomicBundle pre lni :: _ => ⟨pre, lni, true⟩
  | _ :: rest => parseAtomicSend rest

/-! ## What the send path hashes and publishes -/

/-- The deployment constants of one chain and the abstract functions the send path composes. -/
structure Params where
  /-- `block.chainid`. -/
  chainId : Word
  /-- `L1_CHAIN_ID` of the center (:95) and of the manager (AtomicFlowManager.sol:64). -/
  l1ChainId : Word
  /-- `L2_INTEROP_CENTER_ADDR`, the only caller `append` accepts (AtomicFlowManager.sol:87-92). -/
  center : Address
  /-- `L2_ASSET_ROUTER_ADDR`. -/
  assetRouter : Address
  /-- `abi.encode(InteropBundle)` (:690, :729). -/
  enc : Bundle → List UInt8
  /-- `abi.encode(AtomicFlowPreimage)` (AtomicFlowManager.sol:364). -/
  encFlow : FlowPreimage → List UInt8
  /-- `keccak256`. -/
  keccak : List UInt8 → Word
  /-- `InteroperableAddress.formatEvmV1(chainId, addr)`: the default unbundler (:215, :520). -/
  formatEvmV1 : Word → Address → List UInt8

/-- The bundle hash: `_hashBundle(b) = encodeInteropBundleHash(abi.encode(b)) = keccak256(abi.encode(b))`
(:689-691, `InteropDataEncoding.sol:14-16`). There is no outer chain id any more. -/
def bundleHash (P : Params) (b : Bundle) : Word :=
  P.keccak (P.enc b)

/-- `flowId = keccak256(abi.encode(_preimage))`, which `append` recomputes from the preimage
(AtomicFlowManager.sol:108, :364). -/
def flowIdOf (P : Params) (pre : FlowPreimage) : Word :=
  P.keccak (P.encFlow pre)

/-- The message a published bundle sends to L1: `bytes.concat(BUNDLE_IDENTIFIER, abi.encode(_bundle))`
(:729), with `BUNDLE_IDENTIFIER = 0x01` (`common/Messaging.sol:5`). -/
def l1Message (P : Params) (b : Bundle) : List UInt8 :=
  1 :: P.enc b

/-- The unbundler default: an empty `unbundlerAddress` becomes `formatEvmV1(block.chainid,
msg.sender)` (:214-216 in `sendMessage`, :519-521 in `_parseBundleInputs`). -/
def withDefaultUnbundler (P : Params) (sender : Address) (ba : BundleAttributes) :
    BundleAttributes :=
  if ba.unbundlerAddress = [] then { ba with unbundlerAddress := P.formatEvmV1 P.chainId sender }
  else ba

/-! ## One dispatch -/

/-- The two public entry points that reach `_sendBundle`. -/
inductive Entry
  /-- `sendMessage(recipient, payload, attributes)` (:194-242). -/
  | sendMessage
  /-- `sendBundle(destination, callStarters, bundleAttributes)` (:245-278). -/
  | sendBundle
deriving DecidableEq

/-- One successful send, as the ghost log records it. -/
structure Dispatch where
  entry : Entry
  /-- `msg.sender` of the entry point. -/
  sender : Address
  /-- The attribute list `parseAtomicSend` reads: `attributes` of `sendMessage` (:230), the bundle
  attributes of `sendBundle` (:269). -/
  attrs : List Attribute
  /-- The raw per-call attribute lists: `originalCallAttributes[0] = attributes` for `sendMessage`
  (:225-226); each starter's `callAttributes` for `sendBundle` (:498-504). -/
  callAttrs : List (List Attribute)
  /-- The parsed call starters (`InteropCallStarterInternal`). -/
  starters : List CallStarter
  /-- The bundle `_buildInteropBundle` built and `_dispatchBundle` hashed. -/
  bundle : Bundle
  /-- The `AtomicSend` passed to `_sendBundle`. -/
  atomicSend : AtomicSend
deriving DecidableEq

/-- The user salt, `_bundleAttributes.salt`. -/
def Dispatch.salt (d : Dispatch) : Word := d.bundle.bundleAttributes.salt

/-- The key `isInteropBundleSaltUsed` is indexed by (:562, :565). -/
def Dispatch.key (d : Dispatch) : Address × Word := (d.sender, d.salt)

/-- `_dispatchBundle` took the L2 branch (:733-740): the leg was appended, nothing published. -/
def Dispatch.appends (P : Params) (d : Dispatch) : Prop :=
  d.bundle.destinationChainId ≠ P.l1ChainId

instance (P : Params) (d : Dispatch) : Decidable (d.appends P) := by
  unfold Dispatch.appends; infer_instance

/-- The leg an appended dispatch commits: `(flowId(preimage), bundleHash)`. -/
def legOf (P : Params) (d : Dispatch) : Word × Word :=
  (flowIdOf P d.atomicSend.flowPreimage, bundleHash P d.bundle)

/-- `d.bundle` is the bundle `_buildInteropBundle` builds for `d.sender` (:631-640, :678-679). The
destination and its base-token asset id are inputs. -/
structure FormedBy (P : Params) (d : Dispatch) : Prop where
  /-- `sourceChainId: block.chainid` (:633). -/
  source : d.bundle.sourceChainId = P.chainId
  /-- `interopBundleSalt: keccak256(abi.encodePacked(msg.sender, _bundleAttributes.salt))` (:637). -/
  salt : d.bundle.interopBundleSalt = P.keccak (saltPreimage d.sender d.salt)
  /-- `bundle.calls[i] = _processCallStarter(_callStarters[i], _)` (:678-679, :767-824), whose
  `from` is the starter's target (the asset router) for an indirect call and `msg.sender` for a
  direct one. -/
  calls : List.Forall₂ (FormsCall d.sender) d.starters d.bundle.calls

/-! ## The checks -/

/-- Which of the six checks the code performs. The deployed code performs all six. -/
structure Checks where
  /-- `sendMessage` passes `parseAtomicSend(attributes)` (:230). Off: the pin's constant non-atomic
  `AtomicSend` (pin :246-252). -/
  sendMessageParsesAtomic : Bool
  /-- `_ensureL2ToL2(recipientChainId)` in `sendMessage` (:204, :396-402). -/
  l2ToL2Check : Bool
  /-- `_sendBundle`'s atomicity/destination gate (:551-555). -/
  atomicityGate : Bool
  /-- `require(!isInteropBundleSaltUsed[msg.sender][salt])` (:561-564). -/
  saltCheck : Bool
  /-- `IndirectCallOnlyToAssetRouter` (:664-667) and `IndirectCallCannotCarryValue` (:673-676). -/
  indirectRestriction : Bool
  /-- `onlyInteropCenter` on `append` (AtomicFlowManager.sol:87-92, :107). -/
  onlyInteropCenter : Bool

/-- The deployed code at main. -/
def deployed : Checks := ⟨true, true, true, true, true, true⟩

/-- The deployed code with the pin's `sendMessage` constant in place of `parseAtomicSend`. -/
def withPinSendMessage : Checks := ⟨false, true, true, true, true, true⟩

/-- The deployed code without `_ensureL2ToL2` in `sendMessage`. -/
def withoutL2ToL2Check : Checks := ⟨true, false, true, true, true, true⟩

/-- The deployed code without the atomicity gate of `_sendBundle`. -/
def withoutAtomicityGate : Checks := ⟨true, true, false, true, true, true⟩

/-- The deployed code without the salt check. -/
def withoutSaltCheck : Checks := ⟨true, true, true, false, true, true⟩

/-- The deployed code without the two indirect-call restrictions. -/
def withoutIndirectRestriction : Checks := ⟨true, true, true, true, false, true⟩

/-- The deployed code without `onlyInteropCenter` on `append`. -/
def withoutOnlyInteropCenter : Checks := ⟨true, true, true, true, true, false⟩

/-- What `sendMessage` checks and computes before `_sendBundle` (:194-230). -/
structure SendMessageChecks (K : Checks) (P : Params) (d : Dispatch) : Prop where
  /-- `_ensureL2ToL2(recipientChainId)` (:204, :396-402): not on L1, not to L1, not to itself. -/
  l2ToL2 : K.l2ToL2Check = true →
    P.l1ChainId ≠ P.chainId ∧ d.bundle.destinationChainId ≠ P.l1ChainId ∧
      d.bundle.destinationChainId ≠ P.chainId
  /-- One call starter: the nonzero recipient (:202), the payload, and the call attributes parsed
  from `attributes` under `CallAndBundleAttributes` (:206-209, :218-223); the bundle attributes are
  the parsed ones with the default unbundler (:214-216). -/
  parsed : ∃ (recipient : Address) (payload : List UInt8) (ca : CallAttributes)
      (ba : BundleAttributes),
    recipient ≠ 0 ∧ parseAttributes d.attrs .callAndBundleAttributes = some (ca, ba) ∧
      d.starters = [⟨recipient, payload, ca⟩] ∧
      d.bundle.bundleAttributes = withDefaultUnbundler P d.sender ba
  /-- `originalCallAttributes[0] = attributes` (:225-226). -/
  callAttrs : d.callAttrs = [d.attrs]
  /-- `atomicSend = _parser().parseAtomicSend(attributes)` (:230). -/
  atomic : d.atomicSend = if K.sendMessageParsesAtomic then parseAtomicSend d.attrs
    else AtomicSend.empty

/-- What `sendBundle` checks and computes before `_sendBundle` (:245-269). -/
structure SendBundleChecks (P : Params) (d : Dispatch) : Prop where
  /-- `CannotInitiateInteropOnL1` (:257). -/
  notOnL1 : P.l1ChainId ≠ P.chainId
  /-- `InteropToSelfNotSupported` (:258). -/
  notToSelf : d.bundle.destinationChainId ≠ P.chainId
  /-- `MultiCallToL1NotSupported` (:259-261). -/
  toL1Single : d.bundle.destinationChainId = P.l1ChainId → d.starters.length = 1
  /-- `_parseBundleInputs` (:486-510): each starter's recipient is nonzero (:495) and its call
  attributes are its raw attribute list parsed under `OnlyCallAttributes` (:501-504). -/
  calls : List.Forall₂
    (fun (l : List Attribute) (cs : CallStarter) =>
      cs.target ≠ 0 ∧ ∃ ba, parseAttributes l .onlyCallAttributes = some (cs.callAttributes, ba))
    d.callAttrs d.starters
  /-- The bundle attributes parsed under `OnlyBundleAttributes` (:513), with the default unbundler
  (:519-521). -/
  bundleAttrs : ∃ (ca : CallAttributes) (ba : BundleAttributes),
    parseAttributes d.attrs .onlyBundleAttributes = some (ca, ba) ∧
      d.bundle.bundleAttributes = withDefaultUnbundler P d.sender ba
  /-- `atomicSend = _parser().parseAtomicSend(_bundleAttributes)` (:269). -/
  atomic : d.atomicSend = parseAtomicSend d.attrs

/-- `_buildInteropBundle`'s per-starter checks (:644-677). -/
structure StarterChecks (K : Checks) (P : Params) (dest : Word) (cs : CallStarter) : Prop where
  /-- An L1 destination takes only an indirect, zero-value call to the asset router:
  `DirectCallToL1NotSupported`, `InteropCallToL1NotToAssetRouter`, `NonZeroValueToL1NotSupported`
  (:645-657). -/
  toL1 : dest = P.l1ChainId →
    cs.callAttributes.indirectCall = true ∧ cs.target = P.assetRouter ∧
      cs.callAttributes.interopCallValue = 0
  /-- Indirect calls target the asset router (:664-667) and carry no `interopCallValue`
  (:673-676). -/
  indirect : K.indirectRestriction = true → cs.callAttributes.indirectCall = true →
    cs.target = P.assetRouter ∧ cs.callAttributes.interopCallValue = 0

/-- `append`'s checks on the flow preimage that the model keeps (AtomicFlowManager.sol:126-146): the
bundle hash is one of the flow's legs, and the first such leg declares this chain as its source. -/
structure FlowAccepts (P : Params) (a : AtomicSend) (h : Word) : Prop where
  /-- `ManagerCommittedBundleNotInFlow` (:129-139). -/
  isLeg : h ∈ a.flowPreimage.legBundleHashes
  /-- `ManagerCommittedLegSourceChainMismatch` (:140-146), at the index the loop of :131-136 finds. -/
  sourceIsThisChain :
    a.flowPreimage.legSourceChainIds[a.flowPreimage.legBundleHashes.idxOf h]? = some P.chainId

/-- The checks of one send that read no storage. -/
structure SendShape (K : Checks) (P : Params) (d : Dispatch) : Prop where
  /-- The `sendMessage` entry (:194-230). -/
  message : d.entry = .sendMessage → SendMessageChecks K P d
  /-- The `sendBundle` entry (:245-269). -/
  bundleEntry : d.entry = .sendBundle → SendBundleChecks P d
  /-- `AtomicBundleToL1NotSupported` (:551-552). -/
  atomicNotToL1 : K.atomicityGate = true → d.atomicSend.isAtomic = true →
    d.bundle.destinationChainId ≠ P.l1ChainId
  /-- `NonAtomicSendUnsupported` (:553-554). -/
  nonAtomicToL1 : K.atomicityGate = true → d.atomicSend.isAtomic = false →
    d.bundle.destinationChainId = P.l1ChainId
  /-- The bundle `_buildInteropBundle` builds (:620-686). -/
  formed : FormedBy P d
  /-- Its per-starter checks (:644-677). -/
  starterChecks : ∀ cs ∈ d.starters, StarterChecks K P d.bundle.destinationChainId cs
  /-- In the L2 branch, `append`'s flow checks (:736-740 → AtomicFlowManager.sol:126-146). -/
  flow : d.appends P → FlowAccepts P d.atomicSend (bundleHash P d.bundle)

/-! ## State and steps -/

/-- One chain's center, flow manager, and the center's L2→L1 messages. -/
structure State where
  /-- `isInteropBundleSaltUsed[user][salt]` (:125). -/
  saltUsed : Address → Word → Bool
  /-- The manager's `_state[flowId][bundleHash]` (AtomicFlowManager.sol:60). -/
  manager : Manager
  /-- The messages the center sent through `L2_TO_L1_MESSENGER_SYSTEM_CONTRACT.sendToL1` (:729),
  oldest first. -/
  l1Messages : List (List UInt8)
  /-- Ghost: every successful dispatch, oldest first. -/
  log : List Dispatch

/-- Fresh storage: no salt used, every leg `Unset`, nothing sent to L1, nothing dispatched. -/
def init : State := ⟨fun _ _ => false, Contracts.AtomicFlowManager.empty, [], []⟩

/-- The state after a successful `_sendBundle` of `d`: the salt is marked (:565); an L1 destination
publishes `l1Message` (:727-731); any other commits the leg `legOf P d` (:736-740,
AtomicFlowManager.sol:165); the log records `d`. -/
def State.afterSend (P : Params) (S : State) (d : Dispatch) : State where
  saltUsed := markSalt S.saltUsed d.sender d.salt
  manager := if d.bundle.destinationChainId = P.l1ChainId then S.manager
    else S.manager.set (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) .Committed
  l1Messages := if d.bundle.destinationChainId = P.l1ChainId then S.l1Messages ++ [l1Message P d.bundle]
    else S.l1Messages
  log := S.log ++ [d]

/-- One transaction that changes the modelled state. -/
inductive Step (K : Checks) (P : Params) : State → State → Prop
  /-- `sendMessage` or `sendBundle` by `d.sender`, through `_sendBundle` and `_dispatchBundle`. -/
  | send {S : State} (d : Dispatch) :
      SendShape K P d →
      (K.saltCheck = true → S.saltUsed d.sender d.salt = false) →
      (d.appends P →
        S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) = .Unset) →
      Step K P S (S.afterSend P d)
  /-- `authorizeRefund` marking one of the flow's legs (AtomicFlowManager.sol:236-243). Its proof
  checks are omitted. -/
  | authorize {S : State} (f h : Word) :
      AuthorizeGuard S.manager f h →
      Step K P S { S with manager := S.manager.set f h .Revertable }
  /-- `claimRefund` (AtomicFlowManager.sol:251-257). The recovery calls go to the asset router. -/
  | claim {S : State} (f h : Word) :
      ClaimGuard S.manager f h →
      Step K P S { S with manager := S.manager.set f h .Reverted }
  /-- A transaction calling `append` directly from an account other than the center. -/
  | foreignAppend {S : State} (caller : Address) (a : AtomicSend) (h : Word) :
      caller ≠ P.center →
      (K.onlyInteropCenter = true → caller = P.center) →
      FlowAccepts P a h →
      S.manager.legState (flowIdOf P a.flowPreimage) h = .Unset →
      Step K P S { S with manager := S.manager.set (flowIdOf P a.flowPreimage) h .Committed }

/-- Reachability. -/
inductive Reach (K : Checks) (P : Params) : State → State → Prop
  | refl {S : State} : Reach K P S S
  | tail {S T U : State} : Reach K P S T → Step K P T U → Reach K P S U

/-! ## What the head guarantees about a bundle's calls, and what recovery does with them -/

/-- What the head's send path guarantees about the calls of a dispatched bundle, in place of the
pin's `_validateAtomicBundle` (`∀ c, c.value = 0`). -/
structure CallsChecked (P : Params) (d : Dispatch) : Prop where
  /-- A call carrying base-token value is a direct call of the sender: `from: msg.sender` (:821). -/
  valueFromSender : ∀ c ∈ d.bundle.calls, c.value ≠ 0 → c.fromAddr = d.sender
  /-- Every other call is an indirect call through the asset router (`from: recipientAddress`,
  :812, pinned to the router by :664-667) carrying no value (:673-676). -/
  othersFromRouter : ∀ c ∈ d.bundle.calls, c.fromAddr ≠ d.sender →
    c.fromAddr = P.assetRouter ∧ c.value = 0

/-- The base-token refunds `_recoverBundle` makes for a bundle (AtomicFlowManager.sol:313-320): one
`bridgehubRecoverBaseToken(dest, destBaseTokenAssetId, c.from, c.value)` per call whose `from` is not
the asset router and whose value is nonzero, as `(recipient, amount)`. -/
def baseTokenRefunds (P : Params) (b : Bundle) : List (Address × ℕ) :=
  (b.calls.filter fun c => decide (c.fromAddr ≠ P.assetRouter) && decide (c.value ≠ 0)).map
    fun c => (c.fromAddr, c.value)

/-- **A PINNED KECCAK COLLISION** on two named byte strings: they differ and hash equal. -/
def KeccakClash (P : Params) (x y : List UInt8) : Prop :=
  x ≠ y ∧ P.keccak x = P.keccak y

/-- A pinned collision on the two dispatches' `abi.encodePacked(sender, salt)` preimages (:637). -/
def SaltClash (P : Params) (d d' : Dispatch) : Prop :=
  KeccakClash P (saltPreimage d.sender d.salt) (saltPreimage d'.sender d'.salt)

/-- **THE ONLY WAY TWO DISPATCHES SHARE A BUNDLE.** Two different senders used the same salt, and
keccak collides on their packed preimages. -/
def CrossSenderSaltClash (P : Params) (d d' : Dispatch) : Prop :=
  d.salt = d'.salt ∧ d.sender ≠ d'.sender ∧ SaltClash P d d'

/-- A pinned collision on two bundles' bundle-hash preimages, which at head are the encodings
`abi.encode(bundle)` themselves. -/
def BundleHashClash (P : Params) (b b' : Bundle) : Prop :=
  KeccakClash P (P.enc b) (P.enc b')

/-- The salt preimages a run hashed, one per dispatch. -/
def saltPreimages (log : List Dispatch) : List (List UInt8) :=
  log.map fun d => saltPreimage d.sender d.salt

/-- The bundle-hash preimages a run hashed, one per dispatch: the encodings. -/
def bundleEncodings (P : Params) (log : List Dispatch) : List (List UInt8) :=
  log.map fun d => P.enc d.bundle

/-! ## The pin's `sendMessage`, for comparison -/

/-- The `AtomicSend` the pin's `sendMessage` passed to `_sendBundle`, in the pin's layout
(`Contracts.InteropCenter.AtomicSend`): `AtomicSend({flowId: bytes32(0), lowNullifierIndex: 0,
deadline: 0, isAtomic: false})` (pin `InteropCenter.sol:246-252`), whatever the attributes. -/
def pinSendMessageAtomicSend (_attrs : List Attribute) : Contracts.InteropCenter.AtomicSend :=
  ⟨0, 0, 0, false⟩

/-! ## Witness data

The toy keccak and bundle encoder of the pin model (`lastWord`, `saltWordsEncoder`), so a bundle's
hash is its user salt; the flow encoder writes the deadline, so a flow id is its deadline. The asset
router is address `9`, the indirect sender of the pin witnesses; L1 is chain `1`. -/

/-- The flow encoder of the witnesses: the deadline as one word. -/
def deadlineEncoder (pre : FlowPreimage) : List UInt8 := toBytesBE 32 pre.deadline

/-- The honest witness chain: chain `324`, L1 `1`, center `0x8010`, asset router `9`. -/
def headParams : Params :=
  ⟨324, 1, 0x8010, 9, saltWordsEncoder, deadlineEncoder, lastWord, fun _ _ => [1]⟩

/-- A one-leg flow on chain `324` with deadline `t` whose only leg is `h`. -/
def oneLegFlow (t : ℕ) (h : Word) : FlowPreimage := ⟨1, t, 1, [h], [324]⟩

/-- Sender `1`'s `sendMessage` attributes: the flow of deadline `7` whose leg is the bundle of salt
`1`, and the salt `1`. -/
def headMsgAttrs : List Attribute :=
  [.atomicBundle (oneLegFlow 7 1) 0, .interopBundleSalt 1]

/-- Sender `1`'s `sendMessage` to contract `5` on chain `325`, with an empty payload. -/
def headMsg : Dispatch :=
  ⟨.sendMessage, 1, headMsgAttrs, [headMsgAttrs], [⟨5, [], noCallAttributes⟩],
    ⟨324, 325, 1, lastWord (saltPreimage 1 1), [⟨5, 1, 0, []⟩], wAttrs 1⟩,
    ⟨oneLegFlow 7 1, 0, true⟩⟩

/-- Sender `2`'s `sendBundle` bundle attributes: the flow of deadline `8` whose leg is the bundle of
salt `2`, and the salt `2`. -/
def headValueAttrs : List Attribute :=
  [.atomicBundle (oneLegFlow 8 2) 0, .interopBundleSalt 2]

/-- Sender `2`'s `sendBundle` to chain `325`: one direct call to contract `5` carrying base-token
value `9`. Committed at head; the pin's `_validateAtomicBundle` would have rejected it. -/
def headValueLeg : Dispatch :=
  ⟨.sendBundle, 2, headValueAttrs, [[.interopCallValue 9]], [⟨5, [], ⟨9, 0, false⟩⟩],
    ⟨324, 325, 1, lastWord (saltPreimage 2 2), [⟨5, 2, 9, []⟩], wAttrs 2⟩,
    ⟨oneLegFlow 8 2, 0, true⟩⟩

/-- Sender `3`'s `sendBundle` to L1 without `atomicBundle`: one indirect zero-value call to the asset
router (a withdrawal), published to L1. -/
def headWithdrawal : Dispatch :=
  ⟨.sendBundle, 3, [.interopBundleSalt 3], [[.indirectCall 0]], [⟨9, [], ⟨0, 0, true⟩⟩],
    ⟨324, 1, 1, lastWord (saltPreimage 3 3), [⟨5, 9, 0, []⟩], wAttrs 3⟩,
    AtomicSend.empty⟩

/-- The honest run's states: the atomic `sendMessage`, the value leg, the withdrawal, and the
authorization of the `sendMessage` leg. -/
def headS1 : State := init.afterSend headParams headMsg
def headS2 : State := headS1.afterSend headParams headValueLeg
def headS3 : State := headS2.afterSend headParams headWithdrawal
def headS4 : State :=
  { headS3 with manager := headS3.manager.set 7 1 .Revertable }

/-- A decoder for the honest run: it inverts `saltWordsEncoder` on the run's three bundles. -/
def headDec (x : List UInt8) : Bundle :=
  if x = saltWordsEncoder headValueLeg.bundle then headValueLeg.bundle
  else if x = saltWordsEncoder headWithdrawal.bundle then headWithdrawal.bundle
  else headMsg.bundle

end Contracts.InteropCenter.SendAtHead
