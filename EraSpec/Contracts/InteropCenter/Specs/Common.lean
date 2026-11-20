import Mathlib.Tactic
import EraSpec.Core.Word
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashEncoding

/-!
# Model vocabulary: `InteropCenter` words, bundles, call starters and the call-forming relation

Source: era-contracts `draft/v0.35.0` head `b17415d20`: `l1-contracts/contracts/common/Messaging.sol`
(the structs) and `interop/InteropCenter.sol` (a bare `:N` is a line of that file). The send model
(`Specs/SendAtHead.lean`) and the fee model (`Specs/FeeState.lean`) of this folder build on these
definitions, and so does the `c67894b9` record under `History/`.

**This file is definitions only.** It declares no state and no step.

The structures omit the constant `version` fields (`INTEROP_CALL_VERSION`,
`INTEROP_BUNDLE_VERSION`) and the reserved `shadowAccount` (always `false`, :816, :825).
-/

namespace Contracts.InteropCenter

open AttackVectors.BundleHashEncoding (toBytesBE fromBytesBE)

/-! ## Words, addresses and the bundle -/

/-- `bytes32` and `uint256` words: salts, hashes, chain ids, asset ids, flow ids. -/
abbrev Word := UInt256

/-- An `address`: 20 bytes. -/
abbrev Address := Fin (256 ^ 20)

/-- `InteropCall` (`common/Messaging.sol:240-247`), without the constant `version` and the
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

/-- `BundleAttributes` (`Messaging.sol:224-229`). -/
structure BundleAttributes where
  executionAddress : List UInt8
  unbundlerAddress : List UInt8
  useFixedFee : Bool
  /-- The user-provided salt, from the `interopBundleSalt` attribute; `0` if absent. -/
  salt : Word
deriving DecidableEq

/-- `InteropBundle` (`Messaging.sol:268-276`), without the constant `version`. -/
structure Bundle where
  sourceChainId : Word
  destinationChainId : Word
  destinationBaseTokenAssetId : Word
  /-- `keccak256(abi.encodePacked(msg.sender, _bundleAttributes.salt))` (:638). -/
  interopBundleSalt : Word
  calls : List InteropCall
  /-- The bundle carries the attributes, user salt included. -/
  bundleAttributes : BundleAttributes
deriving DecidableEq

/-- `CallAttributes` (`Messaging.sol:210-214`). -/
structure CallAttributes where
  interopCallValue : ℕ
  indirectCallMessageValue : ℕ
  indirectCall : Bool
deriving DecidableEq

/-- `InteropCallStarterInternal` (`Messaging.sol:199-203`): a parsed call starter. -/
structure CallStarter where
  /-- `to`: the recipient, or the indirect sender for an indirect call. -/
  target : Address
  data : List UInt8
  callAttributes : CallAttributes
deriving DecidableEq

/-! ## Byte strings the center hashes -/

/-- `abi.encodePacked(msg.sender, _bundleAttributes.salt)` (:638): 20 address bytes, then the 32
salt bytes. -/
def saltPreimage (sender : Address) (salt : Word) : List UInt8 :=
  toBytesBE 20 sender.val ++ toBytesBE 32 salt.val

/-- No call of the bundle carries native value. At `b17415d20` this is not checked by the center
for atomic bundles (the `c67894b9` `_validateAtomicBundle` that checked it is gone); the send model
uses it to state that difference. -/
def Validated (b : Bundle) : Prop := ∀ c ∈ b.calls, c.value = 0

instance (b : Bundle) : Decidable (Validated b) := by
  unfold Validated; infer_instance

/-- `totalBurnedCallsValue` (:681): the sum of the starters' `interopCallValue`, which
`_ensureCorrectTotalValue` burns through the `BaseTokenHolder` (:436-439) or deposits (:445-450)
when it is nonzero. -/
def totalBurnedCallsValue (starters : List CallStarter) : ℕ :=
  (starters.map fun cs => cs.callAttributes.interopCallValue).sum

/-! ## Forming a call -/

/-- `_processCallStarter(cs, _)` (:776-832), called by `sender`, may return `c`. -/
structure FormsCall (sender : Address) (cs : CallStarter) (c : InteropCall) : Prop where
  /-- Both branches: `value: _callStarter.callAttributes.interopCallValue` (:819, :828). -/
  value : c.value = cs.callAttributes.interopCallValue
  /-- Indirect: `from: recipientAddress` (:820); recipient and data are what the indirect sender
  returned (:788-790, :812-818), so free. -/
  indirect : cs.callAttributes.indirectCall = true → c.fromAddr = cs.target
  /-- Direct: the starter's recipient and data, `from: msg.sender` (:822-830). -/
  direct : cs.callAttributes.indirectCall = false →
    c.target = cs.target ∧ c.data = cs.data ∧ c.fromAddr = sender

/-- `isInteropBundleSaltUsed[a][s] = true` (:566; the mapping is :128). -/
def markSalt (u : Address → Word → Bool) (a : Address) (s : Word) : Address → Word → Bool :=
  fun a' s' => if a' = a ∧ s' = s then true else u a' s'

/-! ## Run-local hash and encoder premises -/

/-- keccak is injective on the explicit finite list `L` of preimages. -/
def KeccakInjOn (k : List UInt8 → Word) (L : List (List UInt8)) : Prop :=
  ∀ x ∈ L, ∀ y ∈ L, k x = k y → x = y

/-- The encoder separates the bundles of the explicit finite list `L`. `abi.encode` of a value is
decodable (`claimRefund` decodes these very bytes, `AtomicFlowManager.sol:251`), so it separates
any two bundles; the results ask it only of the bundles a run dispatched (`SOL-ABI`). -/
def EncInjOn (enc : Bundle → List UInt8) (L : List Bundle) : Prop :=
  ∀ b ∈ L, ∀ b' ∈ L, enc b = enc b' → b = b'

/-! ## Witness data

A toy keccak that reads the last 32 bytes as a word, a toy encoder that writes the bundle's two
salt words, and call starters used by the witnesses. -/

/-- The last 32 bytes of `l`, as a word. -/
def lastWord (l : List UInt8) : Word := Fin.ofNat _ (fromBytesBE l)

/-- The two salt words of the bundle. -/
def saltWordsEncoder (b : Bundle) : List UInt8 :=
  toBytesBE 32 b.interopBundleSalt.val ++ toBytesBE 32 b.bundleAttributes.salt.val

/-- Bundle attributes with the given salt. The unbundler is a nonempty placeholder: `sendBundle`
puts a formatted ERC-7930 address there, and no result reads it. -/
def wAttrs (s : Word) : BundleAttributes := ⟨[], [1], false, s⟩

/-- A direct call starter to contract `5` with base-token value `v`. -/
def wDirect (v : ℕ) : CallStarter := ⟨5, [], ⟨v, 0, false⟩⟩

/-- An indirect call starter through the indirect sender `9` (say, the asset router). -/
def wIndirect : CallStarter := ⟨9, [], ⟨0, 0, true⟩⟩

end Contracts.InteropCenter
