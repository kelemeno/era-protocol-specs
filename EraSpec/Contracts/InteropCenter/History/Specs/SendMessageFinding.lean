import EraSpec.Contracts.InteropCenter.Specs.Send
import EraSpec.Contracts.InteropCenter.History.Specs.Dispatch

/-!
# History: the `c67894b9` `sendMessage` finding, compared with the `b17415d20` parser

**History is the record of an older commit, not a claim about `b17415d20`.**

At the old interop pin `c67894b9`, `sendMessage` parsed its attributes under
`CallAndBundleAttributes`, which accepts `atomicBundle`, and then passed a constant non-atomic
`AtomicSend` (pin `InteropCenter.sol:246-252`), so a bundle carrying the attribute was published
instead of appended (the round-5 source finding on `sendMessage`, REVIEW.md, "Round 5 source
findings"). This file transcribes the pin's `parseAttributes` (pin `InteropCenter.sol:776-868`) on
the decoded attribute lists of the `b17415d20` send model (`Specs/Send.lean`), and the pin's
`sendMessage` constant in the pin model's layout (`History/Specs/Dispatch.lean`). The pin's
`atomicBundle` payload had a different layout (`flowId`, `deadline`, `lowNullifierIndex`; pin
:878-879), and neither parser decodes it, so a list is compared up to that payload. The pin's
branches write the same fields as the `b17415d20` `Attribute.apply` (pin :800, :809-810, :819,
:829, :841-842, :863; nothing for `atomicBundle`, pin :843-854).

The `b17415d20` behaviour is stated in `Properties/Send.lean` (`SendMessageAlwaysAtomic`,
`AtomicBundleAttributeMeansAppended`). The results are in
`EraSpec.Contracts.InteropCenter.History.Properties.SendMessageFinding`.
-/

namespace Contracts.InteropCenter.Send.History

/-- The pin's table, written out as the explicit `_restriction == …` disjunctions of pin
`InteropCenter.sol:791-863` (one branch per selector, same order): `interopCallValue` under
`OnlyInteropCallValue`, `OnlyCallAttributes` or `CallAndBundleAttributes` (pin :794-796);
`indirectCall` under `OnlyCallAttributes` or `CallAndBundleAttributes` (pin :804-805); the five
bundle attributes under `OnlyBundleAttributes` or `CallAndBundleAttributes` (pin :814-815, :824-825,
:834-835, :846-847, :858-859). -/
def pinAllowed : ℕ → Restriction → Bool
  | 0, r => r == .onlyInteropCallValue || r == .onlyCallAttributes || r == .callAndBundleAttributes
  | 1, r => r == .onlyCallAttributes || r == .callAndBundleAttributes
  | _, r => r == .onlyBundleAttributes || r == .callAndBundleAttributes

/-- The loop of the pin's `parseAttributes` (pin `InteropCenter.sol:788-867`): per attribute, the
selector's branch (an unsupported selector reverts `UnsupportedAttribute`, pin :864-866), then
`require(!attributeUsed[k], AttributeAlreadySet)`, then the explicit restriction disjunction
(`pinAllowed`, `AttributeViolatesRestriction`), then `attributeUsed[k] = true` and the field writes.
The selector-to-branch mapping is the head's `Attribute.index`. -/
def pinParseFrom (r : Restriction) :
    List ℕ → CallAttributes × BundleAttributes → List Attribute →
      Option (CallAttributes × BundleAttributes)
  | _, x, [] => some x
  | used, x, a :: rest =>
    match a.index with
    | none => none
    | some i =>
      if i ∈ used then none
      else if pinAllowed i r then pinParseFrom r (i :: used) (a.apply x) rest
      else none

/-- The pin's `parseAttributes(_attributes, _restriction)` (pin `InteropCenter.sol:776-868`), from
the zero structs (`indirectCall = false`, pin :781). -/
def pinParseAttributes (attrs : List Attribute) (r : Restriction) :
    Option (CallAttributes × BundleAttributes) :=
  pinParseFrom r [] (noCallAttributes, noBundleAttributes) attrs

/-! ## The pin's `sendMessage` -/

/-- The `AtomicSend` the pin's `sendMessage` passed to `_sendBundle`, in the pin's layout
(`Contracts.InteropCenter.History.AtomicSend`): `AtomicSend({flowId: bytes32(0), lowNullifierIndex: 0,
deadline: 0, isAtomic: false})` (pin `InteropCenter.sol:246-252`), whatever the attributes. -/
def pinSendMessageAtomicSend (_attrs : List Attribute) : Contracts.InteropCenter.History.AtomicSend :=
  ⟨0, 0, 0, false⟩

end Contracts.InteropCenter.Send.History
