import EraSpec.Contracts.InteropCenter.History.Specs.SendMessageFinding
import EraSpec.Contracts.InteropCenter.Properties.Send

/-!
# History properties: the `c67894b9` `sendMessage` finding and its fix

**History is the record of an older commit, not a claim about `b17415d20`.** Statements about
`EraSpec.Contracts.InteropCenter.History.Specs.SendMessageFinding`; proofs are in
`EraSpec.Contracts.InteropCenter.History.Proofs.SendMessageFinding`.

The pin's parser and the `b17415d20` parser agree on every decoded list (`PinParserIsHeadParser`;
the tables, `MaskTableIsPinTable`). The pin's parser accepts `atomicBundle` under `sendMessage`'s
restriction, while the pin's `sendMessage` sent non-atomically (`PinSendMessageDroppedAtomicBundle`).
At `b17415d20` every `sendMessage` step with such a list is atomic and commits its leg
(`PinFindingRejectedAtHead`; "head" here is `b17415d20`). `SendAtHeadStepWitness` is the step
witness of the send model as it stood before this split, with the conjuncts that mention the pin;
`Contracts.InteropCenter.Send.Properties.SendStepWitness` is its `b17415d20` part.
-/

namespace Contracts.InteropCenter.Send.History

/-- **THE HEAD'S MASK TABLE IS THE PIN'S RESTRICTION TABLE.** For each of the seven attributes and
each restriction, `(mask >> r) & 1 == 1` (InteropAttributeParser.sol:47-50, :128-139) agrees with
`pinAllowed`, the pin's explicit `_restriction == …` disjunctions (pin `InteropCenter.sol:791-863`). -/
def Properties.MaskTableIsPinTable : Prop :=
  ∀ i < 7, ∀ r : Restriction, allowedUnder i r = pinAllowed i r

/-- **THE PIN'S AND THE HEAD'S `parseAttributes` AGREE.** On every decoded attribute list and under
every restriction, the transcribed pin parser (`pinParseAttributes`, pin `InteropCenter.sol:776-868`)
and the head's (`parseAttributes`, InteropAttributeParser.sol:27-79) both revert or both return the
same fields. Lists are compared up to the `atomicBundle` payload, whose layout changed and which
neither parser decodes. -/
def Properties.PinParserIsHeadParser : Prop :=
  ∀ (attrs : List Attribute) (r : Restriction), pinParseAttributes attrs r = parseAttributes attrs r

/-- **THE PIN'S `sendMessage` FINDING, AT THE ATTRIBUTE LEVEL.** Some attribute list carrying
`atomicBundle` is accepted by the pin's parser under `CallAndBundleAttributes`, the restriction the
pin's `sendMessage` parsed under (pin :222-225). For every such list, the `AtomicSend` the pin's
`sendMessage` passed is the constant non-atomic one (pin :246-252), and in the pin model a send with
that `AtomicSend` leaves the manager unchanged (`Contracts.InteropCenter.History.State.afterSend`; at the pin
the bundle was published instead, pin :657). -/
def Properties.PinSendMessageDroppedAtomicBundle : Prop :=
  (∃ attrs, HasAtomicBundle attrs ∧ pinParseAttributes attrs .callAndBundleAttributes ≠ none) ∧
  ∀ attrs, HasAtomicBundle attrs → pinParseAttributes attrs .callAndBundleAttributes ≠ none →
    (pinSendMessageAtomicSend attrs).isAtomic = false ∧
    ∀ (P : Contracts.InteropCenter.History.Params) (S : Contracts.InteropCenter.History.State)
      (d : Contracts.InteropCenter.History.Dispatch), d.atomicSend = pinSendMessageAtomicSend attrs →
      (S.afterSend P d).manager = S.manager

/-- **THE PIN'S FINDING IS REJECTED AT HEAD.** For every attribute list carrying `atomicBundle` that
the pin's parser accepts under `CallAndBundleAttributes` — the lists whose attribute the pin's
`sendMessage` dropped — head's `parseAtomicSend` is atomic, and every step of the deployed code that
dispatches a `sendMessage` with this list uses that `AtomicSend`, leaves its leg `Committed` and
sends nothing to L1. -/
def Properties.PinFindingRejectedAtHead : Prop :=
  ∀ attrs, HasAtomicBundle attrs → pinParseAttributes attrs .callAndBundleAttributes ≠ none →
    (parseAtomicSend attrs).isAtomic = true ∧
    ∀ (P : Params) (S S' : State) (d : Dispatch), Step deployed P S S' → S'.log = S.log ++ [d] →
      d.entry = .sendMessage → d.attrs = attrs →
      d.atomicSend = parseAtomicSend attrs ∧
        S'.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle)
          = .Committed ∧
        S'.l1Messages = S.l1Messages

/-- **THE PER-STEP PREMISES ARE SATISFIABLE, ON THE SAME RUN.** The first step dispatches the
`sendMessage`, whose list carries `atomicBundle` and is accepted by the pin's parser
(`SendMessageAlwaysAtomic`, the attribute branch of `AtomicBundleAttributeMeansAppended`,
`PinFindingRejectedAtHead`, and `OnlyADispatchCommitsALeg`: its leg leaves `Unset`); the second
starts with the first sender's salt used (`UsedSaltHasNoDispatch`, `SaltFlagsNeverCleared`); the
third dispatches the withdrawal, a `sendBundle` without the attribute and non-atomic (the other
branch, `CallLevelAtomicBundleReverts`, `NonAtomicL2SendRevertsInAppend`), and is also a step of
`withPinSendMessage` (`PinConstantMakesSendMessageUnusable`). A `sendMessage` dispatch without the
attribute exists (`SendMessageWithoutAttributeReverts`), and the pin model's public witness dispatch
`Contracts.InteropCenter.History.wD2` carries the pin's `sendMessage` constant (the dispatch premise of
`PinSendMessageDroppedAtomicBundle`). -/
def Properties.SendAtHeadStepWitness : Prop :=
  Step deployed headParams init headS1 ∧ headS1.log = init.log ++ [headMsg] ∧
    headMsg.entry = .sendMessage ∧ HasAtomicBundle headMsg.attrs ∧
    pinParseAttributes headMsg.attrs .callAndBundleAttributes ≠ none ∧
    init.manager.legState 7 1 = .Unset ∧ headS1.manager.legState 7 1 ≠ .Unset ∧
    headS1.saltUsed headMsg.sender headMsg.salt = true ∧ Step deployed headParams headS1 headS2 ∧
    Step deployed headParams headS2 headS3 ∧ headS3.log = headS2.log ++ [headWithdrawal] ∧
    headWithdrawal.entry = .sendBundle ∧ ¬ HasAtomicBundle headWithdrawal.attrs ∧
    headWithdrawal.atomicSend.isAtomic = false ∧
    Step withPinSendMessage headParams headS2 headS3 ∧
    (∃ d : Dispatch, d.entry = .sendMessage ∧ ¬ HasAtomicBundle d.attrs) ∧
    Contracts.InteropCenter.History.wD2.atomicSend = pinSendMessageAtomicSend headMsg.attrs

end Contracts.InteropCenter.Send.History
