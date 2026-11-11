import EraSpec.Contracts.InteropCenter.Specs.SendAtHead
import EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimits

/-!
# Properties: the head send path (main `3605e82`) — `sendMessage` is atomic, the NatSpec is true

Statements about `EraSpec.Contracts.InteropCenter.Specs.SendAtHead`. Proofs are in
`EraSpec.Contracts.InteropCenter.Proofs.SendAtHead`. Every run starts from fresh storage (`init`)
on one chain; `deployed` is main's code with all six of its checks. No result takes a global hash or
encoding premise: the hash premises are run-local (`EncInjOn`, `KeccakInjOn` on the run's own
inputs) or a collision pinned to two named byte strings.

## 1. The round-5 finding O1-1 is gone

At the pin, `sendMessage` parsed `atomicBundle` (the parser accepts it under
`CallAndBundleAttributes`) and then dispatched non-atomically, publishing the bundle to L1
(`PinSendMessageDroppedAtomicBundle`, now formal at the attribute level; the pin's parser table is
the head's mask table, `MaskTableIsPinTable`). At head, `parseAtomicSend` returns exactly the
attribute's payload (`ParseAtomicSendIsTheAttribute`), and the same attribute lists make every
`sendMessage` atomic (`PinFindingRejectedAtHead`).

## 2. `sendMessage` is always atomic

Every successful `sendMessage` carries `atomicBundle`, sends to an L2, commits its leg and publishes
nothing (`SendMessageAlwaysAtomic`; along runs `SendMessagesAreAtomicAlongRuns`); without the
attribute it reverts (`SendMessageWithoutAttributeReverts`). This rests on `_ensureL2ToL2`
(`WithoutL2ToL2CheckSendMessagePublishes`) and on `parseAtomicSend`: with the pin's constant in its
place the head's gate makes `sendMessage` unusable (`PinConstantMakesSendMessageUnusable`).

## 3. The `atomicBundle` NatSpec (IERC7786Attributes.sol:27-33) is true

For both entry points, a successful send whose bundle-level attributes carry `atomicBundle` is
appended, at the leg `(keccak(abi.encode(preimage)), bundleHash)`, with the bundle hash one of the
flow's legs declared from this chain, and publishes nothing; one without it is an L1 withdrawal that
appends nothing (`AtomicBundleAttributeMeansAppended`). The attribute is bundle-level: at call level
it reverts (`CallLevelAtomicBundleReverts`, `AtomicBundleIsABundleAttribute`). Along runs, appended,
atomic and attribute-carrying coincide (`EveryL2SendIsAtomic`), and every L1 message is a zero-value
router withdrawal (`PublishedMessagesAreL1Dispatches`, `PublishedMessagesAreWithdrawals`).
`NonAtomicSendUnsupported` is defense in depth: whatever the checks, `append` rejects a non-atomic
L2 send (`NonAtomicL2SendRevertsInAppend`). `AtomicBundleToL1NotSupported` is load-bearing for the
NatSpec (`WithoutAtomicityGateAttributeBundleIsPublished`).

## 4. O1's validation results, restated at head

* **(a) Salts**: unchanged (`SaltFlagRecordsDispatches`, `SaltFlagsNeverCleared`,
  `UsedSaltHasNoDispatch`, `EachSaltDispatchesOnce`; countermodel
  `WithoutSaltCheckABundleRepeats`).
* **(b) The value check is gone, so O1's (b) is false at head**: a value-carrying leg is committed
  by the deployed code (`ValueLegCommitsAtHead`; O1's `Validated` fails on it). Its repaired form:
  every committed leg is an atomic dispatch of this chain whose value-carrying calls are the
  sender's own direct calls and whose other calls are zero-value router calls
  (`CommittedLegsAreCheckedDispatches`, per step `OnlyADispatchCommitsALeg`, funnel `SolePath`,
  `ValidationUnbypassableDischarged`), so `_recoverBundle`'s base-token refunds go to the payer and
  add up to what the send burned (`AtomicValueIsRefundedToPayer`), unless the payer is the asset
  router itself (`RouterSenderValueIsNotRefunded`); the indirect-call restriction is load-bearing
  (`WithoutIndirectRestrictionRefundMissesPayer`). The bytes `claimRefund` hashes are a logged
  atomic dispatch's, or keccak collides on two named strings
  (`ClaimedBundleIsDispatchedOrCollision`; the disjunct is needed,
  `CollisionLetsForeignBytesMatchACommittedLeg`). Legs: `AppendedLegsStayCommitted`,
  `EachLegAppendedOnce`, `WithoutOnlyInteropCenterUnbackedLegCommits`, `BurnedTotalIsCallValues`.
* **(c) Distinct dispatches**: `DistinctDispatchesDistinctBundles` (no hash premise),
  `DistinctDispatchesDistinctBundleHashes`, `LoggedRunBundleHashesUnique` with the head's preimage
  `abi.encode(bundle)`; firing `SaltClashLetsTwoSendersShareABundle`. `AtomicBytesNeverPublished`
  is now stronger than at the pin: no salt-clash disjunct, any checks.

## Non-vacuity

`SendAtHeadWitness` is a deployed run (an atomic `sendMessage`, an atomic value leg, an L1
withdrawal, one authorization) meeting every premise of the run-level headlines, with every clash
false on it. `SendAtHeadStepWitness` meets the per-step premises, and `SendAtHeadClaimWitness` those
of `ClaimedBundleIsDispatchedOrCollision`. The run-local premises `EncInjOn` and `KeccakInjOn` are
the pin model's, satisfiable for every list (`Contracts.InteropCenter.EncInjOnSatisfiable`,
`Contracts.InteropCenter.KeccakInjOnSatisfiable`).
-/

namespace Contracts.InteropCenter.SendAtHead

open Contracts.AtomicFlowManager (LegState)

/-! ## The attribute parser -/

/-- **`parseAtomicSend` IS THE ATTRIBUTE.** It reports atomic iff the list carries `atomicBundle`;
then it returns that attribute's own preimage and index, and otherwise the zero `AtomicSend`. -/
def Properties.ParseAtomicSendIsTheAttribute : Prop :=
  ∀ attrs : List Attribute,
    ((parseAtomicSend attrs).isAtomic = true ↔ HasAtomicBundle attrs) ∧
    (HasAtomicBundle attrs → ∃ pre lni, Attribute.atomicBundle pre lni ∈ attrs ∧
      parseAtomicSend attrs = ⟨pre, lni, true⟩) ∧
    (¬ HasAtomicBundle attrs → parseAtomicSend attrs = AtomicSend.empty)

/-- **`atomicBundle` IS A BUNDLE-LEVEL ATTRIBUTE.** `parseAttributes` rejects every list carrying it
under `OnlyCallAttributes` (the per-call restriction of `sendBundle`, :501-504) and under
`OnlyInteropCallValue`; it accepts the attribute alone under `OnlyBundleAttributes` (`sendBundle`'s
bundle attributes, :513) and `CallAndBundleAttributes` (`sendMessage`, :206-209), writing no field. -/
def Properties.AtomicBundleIsABundleAttribute : Prop :=
  (∀ attrs, HasAtomicBundle attrs →
    parseAttributes attrs .onlyCallAttributes = none ∧
      parseAttributes attrs .onlyInteropCallValue = none) ∧
  ∀ (pre : FlowPreimage) (lni : ℕ),
    parseAttributes [.atomicBundle pre lni] .onlyBundleAttributes
        = some (noCallAttributes, noBundleAttributes) ∧
      parseAttributes [.atomicBundle pre lni] .callAndBundleAttributes
        = some (noCallAttributes, noBundleAttributes)

/-- **THE HEAD'S MASK TABLE IS THE PIN'S RESTRICTION TABLE.** For each of the seven attributes and
each restriction, `(mask >> r) & 1 == 1` (InteropAttributeParser.sol:47-50, :128-139) agrees with the
pin's explicit `_restriction == …` disjunctions (pin `InteropCenter.sol:791-863`). So the pin's and
the head's `parseAttributes` accept the same lists. -/
def Properties.MaskTableIsPinTable : Prop :=
  ∀ i < 7, ∀ r : Restriction, allowedUnder i r = pinAllowed i r

/-! ## 1. O1-1: the pin dropped the attribute, the head honours it -/

/-- **O1-1 AT THE PIN, AT THE ATTRIBUTE LEVEL.** Some attribute list carrying `atomicBundle` is
accepted under `CallAndBundleAttributes`, the restriction the pin's `sendMessage` parsed under (pin
:222-225; same table, `MaskTableIsPinTable`). For every such list the pin's `sendMessage` passed a
non-atomic `AtomicSend` (pin :246-252), and in the pin model a send with that `AtomicSend` appends
nothing: `Contracts.InteropCenter.State.afterSend` leaves the manager as it was (the bundle was
published, pin :657). -/
def Properties.PinSendMessageDroppedAtomicBundle : Prop :=
  (∃ attrs, HasAtomicBundle attrs ∧ parseAttributes attrs .callAndBundleAttributes ≠ none) ∧
  ∀ attrs, HasAtomicBundle attrs → parseAttributes attrs .callAndBundleAttributes ≠ none →
    (pinSendMessageAtomicSend attrs).isAtomic = false ∧
    ∀ (P : Contracts.InteropCenter.Params) (S : Contracts.InteropCenter.State)
      (d : Contracts.InteropCenter.Dispatch), d.atomicSend = pinSendMessageAtomicSend attrs →
      (S.afterSend P d).manager = S.manager

/-- **THE PIN'S O1-1 INSTANCE IS REJECTED AT HEAD.** For every attribute list carrying `atomicBundle`
that the parser accepts under `CallAndBundleAttributes` — the lists for which the pin's
`sendMessage` dropped the attribute — head's `parseAtomicSend` is atomic, and every step of the
deployed code that dispatches a `sendMessage` with these attributes uses that `AtomicSend`, commits
its leg and sends nothing to L1. -/
def Properties.PinFindingRejectedAtHead : Prop :=
  ∀ attrs, HasAtomicBundle attrs → parseAttributes attrs .callAndBundleAttributes ≠ none →
    (parseAtomicSend attrs).isAtomic = true ∧
    ∀ (P : Params) (S S' : State) (d : Dispatch), Step deployed P S S' → S'.log = S.log ++ [d] →
      d.entry = .sendMessage → d.attrs = attrs →
      d.atomicSend = parseAtomicSend attrs ∧
        S'.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle)
          = .Committed ∧
        S'.l1Messages = S.l1Messages

/-! ## 2. `sendMessage` is always atomic -/

/-- **HEADLINE: EVERY SUCCESSFUL `sendMessage` IS ATOMIC.** A step of the deployed code that
dispatches a `sendMessage` used an attribute list carrying `atomicBundle`, passed that attribute's
`AtomicSend` (atomic), sent to an L2, moved its leg `(flowId(preimage), bundleHash)` from `Unset` to
`Committed`, and sent nothing to L1. -/
def Properties.SendMessageAlwaysAtomic : Prop :=
  ∀ (P : Params) (S S' : State) (d : Dispatch), Step deployed P S S' → S'.log = S.log ++ [d] →
    d.entry = .sendMessage →
      HasAtomicBundle d.attrs ∧ d.atomicSend = parseAtomicSend d.attrs ∧
      d.atomicSend.isAtomic = true ∧ d.appends P ∧
      S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) = .Unset ∧
      S'.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle)
        = .Committed ∧
      S'.l1Messages = S.l1Messages

/-- **A `sendMessage` WITHOUT `atomicBundle` REVERTS.** No step of the deployed code dispatches it
(`NonAtomicSendUnsupported`, :554, against `_ensureL2ToL2`, :204). -/
def Properties.SendMessageWithoutAttributeReverts : Prop :=
  ∀ (P : Params) (S S' : State) (d : Dispatch), d.entry = .sendMessage →
    ¬ HasAtomicBundle d.attrs → Step deployed P S S' → S'.log ≠ S.log ++ [d]

/-- **ALONG ANY RUN, EVERY `sendMessage` IS AN APPENDED ATOMIC LEG.** Every logged `sendMessage`
dispatch of a deployed run carries `atomicBundle`, is atomic, took the L2 branch, and its leg is not
`Unset`. -/
def Properties.SendMessagesAreAtomicAlongRuns : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ d ∈ S.log, d.entry = .sendMessage →
      HasAtomicBundle d.attrs ∧ d.atomicSend.isAtomic = true ∧ d.appends P ∧
        S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) ≠ .Unset

/-- **`parseAtomicSend` IS WHAT KEEPS `sendMessage` LIVE.** With the pin's constant non-atomic
`AtomicSend` in place of `parseAtomicSend` (pin :246-252) and the head's other checks, no step
dispatches a `sendMessage` at all: the gate (:554) wants L1, `_ensureL2ToL2` (:204) forbids it. -/
def Properties.PinConstantMakesSendMessageUnusable : Prop :=
  ∀ (P : Params) (S S' : State) (d : Dispatch), Step withPinSendMessage P S S' →
    S'.log = S.log ++ [d] → d.entry ≠ .sendMessage

/-- **WITHOUT `_ensureL2ToL2`, A `sendMessage` IS PUBLISHED.** A run of the code without :204 in
which a `sendMessage` without `atomicBundle` (an indirect zero-value call to the asset router, to
L1) is dispatched non-atomically and published to L1. -/
def Properties.WithoutL2ToL2CheckSendMessagePublishes : Prop :=
  ∃ (P : Params) (S : State), Reach withoutL2ToL2Check P init S ∧
    ∃ d ∈ S.log, d.entry = .sendMessage ∧ ¬ HasAtomicBundle d.attrs ∧
      d.atomicSend.isAtomic = false ∧ S.l1Messages = [l1Message P d.bundle]

/-! ## 3. The `atomicBundle` NatSpec -/

/-- **HEADLINE: THE `atomicBundle` NATSPEC IS TRUE** (IERC7786Attributes.sol:27-33), for both entry
points. If a step of the deployed code dispatches `d` and `d`'s bundle-level attributes carry
`atomicBundle`, the center "appends the bundle's commit value ... instead of publishing it to L1":
`d` is atomic with that attribute's `AtomicSend`, sends to an L2, its bundle hash is one of the
flow's legs declared from this chain ("requires this bundle's hash to be one of its legs"), its leg
`(keccak(abi.encode(preimage)), bundleHash)` moves from `Unset` to `Committed` and nothing else
changes in the manager, and nothing is sent to L1. Otherwise `d` is an L1 withdrawal: the zero
`AtomicSend`, destination L1, the manager unchanged, and `BUNDLE_IDENTIFIER ++ abi.encode(bundle)`
sent to L1. -/
def Properties.AtomicBundleAttributeMeansAppended : Prop :=
  ∀ (P : Params) (S S' : State) (d : Dispatch), Step deployed P S S' → S'.log = S.log ++ [d] →
    (HasAtomicBundle d.attrs →
      d.atomicSend = parseAtomicSend d.attrs ∧ d.atomicSend.isAtomic = true ∧ d.appends P ∧
      FlowAccepts P d.atomicSend (bundleHash P d.bundle) ∧
      S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) = .Unset ∧
      S'.manager =
        S.manager.set (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) .Committed ∧
      S'.l1Messages = S.l1Messages) ∧
    (¬ HasAtomicBundle d.attrs →
      d.atomicSend = AtomicSend.empty ∧ d.bundle.destinationChainId = P.l1ChainId ∧
      S'.manager = S.manager ∧ S'.l1Messages = S.l1Messages ++ [l1Message P d.bundle])

/-- **A CALL-LEVEL `atomicBundle` REVERTS.** Whatever the checks, no step dispatches a `sendBundle`
one of whose per-call attribute lists carries `atomicBundle` (`OnlyCallAttributes` forbids it). -/
def Properties.CallLevelAtomicBundleReverts : Prop :=
  ∀ (K : Checks) (P : Params) (S S' : State) (d : Dispatch), Step K P S S' →
    S'.log = S.log ++ [d] → d.entry = .sendBundle → ∀ l ∈ d.callAttrs, ¬ HasAtomicBundle l

/-- **ALONG ANY RUN, APPENDED = ATOMIC = CARRIES `atomicBundle`.** For every logged dispatch of a
deployed run, `_dispatchBundle` took the L2 branch iff the send was atomic, iff its attributes carry
`atomicBundle`. -/
def Properties.EveryL2SendIsAtomic : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S → ∀ d ∈ S.log,
    (d.appends P ↔ d.atomicSend.isAtomic = true) ∧
      (d.atomicSend.isAtomic = true ↔ HasAtomicBundle d.attrs)

/-- **`NonAtomicSendUnsupported` IS DEFENSE IN DEPTH.** Whatever the checks, a step that dispatches a
non-atomic `d` sends it to L1: its `AtomicSend` is the zero struct, whose flow has no leg, so
`append` would revert (AtomicFlowManager.sol:137-139; in the code `_validateAndComputeFlowId`
already rejects the zero version, :347-349). -/
def Properties.NonAtomicL2SendRevertsInAppend : Prop :=
  ∀ (K : Checks) (P : Params) (S S' : State) (d : Dispatch), Step K P S S' →
    S'.log = S.log ++ [d] → d.atomicSend.isAtomic = false → d.bundle.destinationChainId = P.l1ChainId

/-- **WITHOUT `AtomicBundleToL1NotSupported`, THE NATSPEC FAILS.** A run of the code without the
gate (:551-555) in which a `sendBundle` carrying `atomicBundle`, atomic, to L1 is published to L1 and
nothing is appended: `_dispatchBundle` branches on the destination (:727). -/
def Properties.WithoutAtomicityGateAttributeBundleIsPublished : Prop :=
  ∃ (P : Params) (S : State), Reach withoutAtomicityGate P init S ∧
    ∃ d ∈ S.log, HasAtomicBundle d.attrs ∧ d.atomicSend.isAtomic = true ∧
      S.l1Messages = [l1Message P d.bundle] ∧ ∀ f h, S.manager.legState f h = .Unset

/-- **THE CENTER'S L1 MESSAGES ARE EXACTLY ITS L1 DISPATCHES.** Along any run, with or without the
checks, the messages sent to L1 are `BUNDLE_IDENTIFIER ++ abi.encode(bundle)` of the logged
dispatches whose destination is L1, in order. -/
def Properties.PublishedMessagesAreL1Dispatches : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    S.l1Messages = (S.log.filter fun d => decide (d.bundle.destinationChainId = P.l1ChainId)).map
      fun d => l1Message P d.bundle

/-- **EVERY PUBLISHED DISPATCH IS A ZERO-VALUE ROUTER WITHDRAWAL.** Along any deployed run, a logged
dispatch to L1 is a `sendBundle` without `atomicBundle` and with the zero `AtomicSend`, of one call,
from the asset router and carrying no value, so it burns no base token. Public L2→L2 interop is gone. -/
def Properties.PublishedMessagesAreWithdrawals : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ d ∈ S.log, d.bundle.destinationChainId = P.l1ChainId →
      d.entry = .sendBundle ∧ ¬ HasAtomicBundle d.attrs ∧ d.atomicSend = AtomicSend.empty ∧
      d.bundle.calls.length = 1 ∧ (∀ c ∈ d.bundle.calls, c.fromAddr = P.assetRouter ∧ c.value = 0) ∧
      totalBurnedCallsValue d.starters = 0

/-! ## 4(a). Sender salts, as at the pin -/

/-- **THE SALT FLAG RECORDS EXACTLY THE DISPATCHED KEYS** (any checks). -/
def Properties.SaltFlagRecordsDispatches : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ∀ (a : Address) (s : Word), S.saltUsed a s = true ↔ ∃ d ∈ S.log, d.sender = a ∧ d.salt = s

/-- **A SET SALT FLAG STAYS SET** (any checks). -/
def Properties.SaltFlagsNeverCleared : Prop :=
  ∀ (K : Checks) (P : Params) (S S' : State), Step K P S S' →
    ∀ (a : Address) (s : Word), S.saltUsed a s = true → S'.saltUsed a s = true

/-- **A USED SALT HAS NO FURTHER DISPATCH** (:561-564). -/
def Properties.UsedSaltHasNoDispatch : Prop :=
  ∀ (P : Params) (S S' : State) (d : Dispatch), S.saltUsed d.sender d.salt = true →
    Step deployed P S S' → S'.log ≠ S.log ++ [d]

/-- **EACH `(sender, salt)` DISPATCHES AT MOST ONE BUNDLE.** -/
def Properties.EachSaltDispatchesOnce : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S → (S.log.map Dispatch.key).Nodup

/-- **WITHOUT THE SALT CHECK, ONE BUNDLE IS DISPATCHED TWICE**, so one bundle hash, with no
collision. -/
def Properties.WithoutSaltCheckABundleRepeats : Prop :=
  ∃ (P : Params) (S : State), Reach withoutSaltCheck P init S ∧
    ∃ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j ∧
      S.log[i].bundle = S.log[j].bundle ∧
      bundleHash P S.log[i].bundle = bundleHash P S.log[j].bundle

/-! ## 4(b). Validation at head -/

/-- **O1'S (b) IS FALSE AT HEAD: A VALUE-CARRYING LEG IS COMMITTED.** A run of the deployed head code
commits an atomic leg whose bundle has a call carrying native value, and whose send burned base
token. So the conclusion `Validated` of the pin's
`Contracts.InteropCenter.Properties.CommittedLegsAreValidatedDispatches` (and of
`AtomicDispatchesCarryNoValue`) fails on it, and so does the pin's `AtomicDispatchBurnsNothing`.
The pin's countermodel `WithoutValueCheckValueLegCommits` is deployed behaviour at head. -/
def Properties.ValueLegCommitsAtHead : Prop :=
  ∃ (P : Params) (S : State), Reach deployed P init S ∧
    ∃ d ∈ S.log, d.atomicSend.isAtomic = true ∧ ¬ Contracts.InteropCenter.Validated d.bundle ∧
      totalBurnedCallsValue d.starters ≠ 0 ∧
      S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) = .Committed

/-- **HEADLINE (b) AT HEAD: EVERY COMMITTED LEG IS A CHECKED ATOMIC DISPATCH OF THIS CHAIN.** Along
any deployed run, every leg `(f, h)` that is not `Unset` was committed by a logged dispatch that is
atomic, carries `atomicBundle`, took the L2 branch, has flow id `f = keccak(abi.encode(preimage))`
and bundle hash `h`, whose preimage lists `h` with this chain as its source, built with
`sourceChainId = block.chainid`, and whose calls are `CallsChecked`: value only on the sender's own
direct calls, every other call a zero-value router call. -/
def Properties.CommittedLegsAreCheckedDispatches : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ (f h : Word), S.manager.legState f h ≠ .Unset →
      ∃ d ∈ S.log, d.atomicSend.isAtomic = true ∧ HasAtomicBundle d.attrs ∧ d.appends P ∧
        flowIdOf P d.atomicSend.flowPreimage = f ∧ bundleHash P d.bundle = h ∧
        FlowAccepts P d.atomicSend h ∧ d.bundle.sourceChainId = P.chainId ∧ CallsChecked P d

/-- **ONLY A DISPATCH COMMITS A LEG.** One step of the deployed code moves a leg out of `Unset` only
by logging an atomic, appended, checked dispatch with that flow id and bundle hash. -/
def Properties.OnlyADispatchCommitsALeg : Prop :=
  ∀ (P : Params) (S S' : State), Step deployed P S S' →
    ∀ (f h : Word), S.manager.legState f h = .Unset → S'.manager.legState f h ≠ .Unset →
      ∃ d, S'.log = S.log ++ [d] ∧ d.atomicSend.isAtomic = true ∧ d.appends P ∧
        flowIdOf P d.atomicSend.flowPreimage = f ∧ bundleHash P d.bundle = h ∧ CallsChecked P d

/-- **THE BURNED TOTAL IS THE CALLS' VALUES** (any checks; :680 and :811, :820). -/
def Properties.BurnedTotalIsCallValues : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ∀ d ∈ S.log, totalBurnedCallsValue d.starters = (d.bundle.calls.map InteropCall.value).sum

/-- **THE VALUE OF A LEG IS REFUNDED TO ITS PAYER.** Along any deployed run, for every logged
dispatch whose sender is not the asset router, the base-token refunds `_recoverBundle` would make
(AtomicFlowManager.sol:313-320) all go to the sender — who paid `msg.value` or the destination base
token (:429-449) — and add up to the burned total `totalBurnedCallsValue`. -/
def Properties.AtomicValueIsRefundedToPayer : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ d ∈ S.log, d.sender ≠ P.assetRouter →
      (∀ r ∈ baseTokenRefunds P d.bundle, r.1 = d.sender) ∧
        ((baseTokenRefunds P d.bundle).map Prod.snd).sum = totalBurnedCallsValue d.starters

/-- **THE ROUTER-SENDER PREMISE IS NEEDED.** A deployed run in which the asset router itself sends an
atomic direct call carrying value: the value is burned, but `_recoverBundle` takes the call for a
router call (`from == L2_ASSET_ROUTER_ADDR`, AtomicFlowManager.sol:309) and refunds no base token.
The source assumes the router never does this (AtomicFlowManager.sol:301-305). -/
def Properties.RouterSenderValueIsNotRefunded : Prop :=
  ∃ (P : Params) (S : State), Reach deployed P init S ∧
    ∃ d ∈ S.log, d.sender = P.assetRouter ∧ d.atomicSend.isAtomic = true ∧
      totalBurnedCallsValue d.starters ≠ 0 ∧ baseTokenRefunds P d.bundle = []

/-- **WITHOUT THE INDIRECT-CALL RESTRICTION, A REFUND MISSES THE PAYER.** A run of the code without
:658-677 in which an atomic indirect call through a non-router sender carries value: its base-token
refund goes to that indirect sender, not to the payer (the reason given at :668-672). -/
def Properties.WithoutIndirectRestrictionRefundMissesPayer : Prop :=
  ∃ (P : Params) (S : State), Reach withoutIndirectRestriction P init S ∧
    ∃ d ∈ S.log, d.atomicSend.isAtomic = true ∧ d.sender ≠ P.assetRouter ∧
      ∃ r ∈ baseTokenRefunds P d.bundle, r.1 ≠ d.sender

/-- **THE FUNNEL, DERIVED.** Along any deployed run, every appended dispatch is `CallsChecked`: the
premise `sole_path` of `AttackVectors.RecoveryLimits.Properties.validation_unbypassable`, for the
head's validation. -/
def Properties.SolePath : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ d, (d ∈ S.log ∧ d.appends P) → CallsChecked P d

/-- **`validation_unbypassable` AT HEAD, WITH ITS PREMISE DISCHARGED.** The abstract funnel statement
instantiated with `CallsChecked` and the appended dispatches, with a proved `sole_path` (the formal
instantiation; the content is `CommittedLegsAreCheckedDispatches`). -/
def Properties.ValidationUnbypassableDischarged : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∃ sole_path : (∀ d, (d ∈ S.log ∧ d.appends P) → CallsChecked P d),
      ∀ (d : Dispatch) (h : d ∈ S.log ∧ d.appends P),
        AttackVectors.RecoveryLimits.Properties.validation_unbypassable
          (CallsChecked P) (fun d => d ∈ S.log ∧ d.appends P) sole_path h

/-- **THE BUNDLE `claimRefund` RECOVERS IS A LOGGED ATOMIC DISPATCH'S, OR KECCAK COLLIDES.** Along any
deployed run whose decoder inverts the encoder on the run's bundles (`SOL-ABI`): if `claimRefund(f, x)`
finds the leg `(f, keccak(x))` not `Unset` (AtomicFlowManager.sol:249-251), then some logged atomic,
appended, checked dispatch has flow id `f`, and either `x` is that dispatch's `abi.encode(bundle)` —
so `_recoverBundle` reverses exactly that bundle, whose destination is not L1 (:296) — or keccak
collides on `x` and that encoding. Any bytes `x`. -/
def Properties.ClaimedBundleIsDispatchedOrCollision : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    (∀ d ∈ S.log, dec (P.enc d.bundle) = d.bundle) →
    ∀ (f : Word) (x : List UInt8), S.manager.legState f (P.keccak x) ≠ .Unset →
      ∃ d ∈ S.log, d.atomicSend.isAtomic = true ∧ d.appends P ∧ CallsChecked P d ∧
        flowIdOf P d.atomicSend.flowPreimage = f ∧
        ((x = P.enc d.bundle ∧ dec x = d.bundle) ∨ KeccakClash P x (P.enc d.bundle))

/-- **ANY BUNDLE WHOSE HASH IS A COMMITTED LEG IS THE LOGGED ONE, OR CLASHES WITH IT.** The coarser
companion of `ClaimedBundleIsDispatchedOrCollision`: along any deployed run, if the leg
`(f, bundleHash b)` of some bundle `b` is not `Unset`, then some logged atomic, appended, checked
dispatch has flow id `f`, and `b` is its bundle, or `b` and its bundle are two different bundles with
one bundle hash. -/
def Properties.PresentedBundleIsDispatchedOrClash : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ (f : Word) (b : Bundle), S.manager.legState f (bundleHash P b) ≠ .Unset →
      ∃ d ∈ S.log, d.atomicSend.isAtomic = true ∧ d.appends P ∧ CallsChecked P d ∧
        flowIdOf P d.atomicSend.flowPreimage = f ∧
        (b = d.bundle ∨ (b ≠ d.bundle ∧ bundleHash P b = bundleHash P d.bundle))

/-- **THE COLLISION DISJUNCT IS NEEDED.** Under a colliding keccak, a deployed run with a committed
leg `(f, keccak(x))` for bytes `x` that encode no logged bundle. -/
def Properties.CollisionLetsForeignBytesMatchACommittedLeg : Prop :=
  ∃ (P : Params) (S : State) (f : Word) (x : List UInt8), Reach deployed P init S ∧
    S.manager.legState f (P.keccak x) ≠ .Unset ∧ ∀ d ∈ S.log, x ≠ P.enc d.bundle

/-- **AN APPENDED LEG NEVER RETURNS TO `Unset`** (any checks). -/
def Properties.AppendedLegsStayCommitted : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ∀ d ∈ S.log, d.appends P →
      S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) ≠ .Unset

/-- **EACH LEG IS APPENDED AT MOST ONCE** (any checks): the legs of a run's appended dispatches are
pairwise distinct (AtomicFlowManager.sol:161-163). -/
def Properties.EachLegAppendedOnce : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ((S.log.filter fun d => decide (d.appends P)).map (legOf P)).Nodup

/-- **WITHOUT `onlyInteropCenter`, A LEG BACKED BY NO DISPATCH IS COMMITTED.** -/
def Properties.WithoutOnlyInteropCenterUnbackedLegCommits : Prop :=
  ∃ (P : Params) (S : State) (f h : Word), Reach withoutOnlyInteropCenter P init S ∧
    S.log = [] ∧ S.manager.legState f h = .Committed

/-! ## 4(c). Distinct dispatches -/

/-- **(c), BUNDLES.** Along any deployed run, two dispatches at different positions carry different
bundles, unless two different senders used the same salt and keccak collides on their packed
preimages. No hash premise. -/
def Properties.DistinctDispatchesDistinctBundles : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j →
      S.log[i].bundle ≠ S.log[j].bundle ∨ CrossSenderSaltClash P S.log[i] S.log[j]

/-- **(c), BUNDLE HASHES.** If the encoder separates the run's bundles, two dispatches' bundle hashes
differ, or the cross-sender salt clash, or keccak collides on their two encodings — the head's
bundle-hash preimages. -/
def Properties.DistinctDispatchesDistinctBundleHashes : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    ∀ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j →
      bundleHash P S.log[i].bundle ≠ bundleHash P S.log[j].bundle ∨
        CrossSenderSaltClash P S.log[i] S.log[j] ∨
        BundleHashClash P S.log[i].bundle S.log[j].bundle

/-- **(c), RUN-LOCAL: EVERY BUNDLE HASH OF A RUN IS UNIQUE**, if the encoder separates the run's
bundles and keccak is injective on the run's salt preimages and on its bundle encodings. -/
def Properties.LoggedRunBundleHashesUnique : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    KeccakInjOn P.keccak (saltPreimages S.log) →
    KeccakInjOn P.keccak (bundleEncodings P S.log) →
    (S.log.map fun d => bundleHash P d.bundle).Nodup

/-- **AN APPENDED BUNDLE IS NEVER PUBLISHED TO L1.** Along any run, with or without the checks, if
the encoder separates the run's bundles, no appended dispatch's `BUNDLE_IDENTIFIER ++
abi.encode(bundle)` is among the center's L1 messages. At the pin this needed a salt-clash disjunct
(`Contracts.InteropCenter.Properties.AtomicBytesNeverPublished`); at head the published bundles go
to L1 and the appended ones do not. -/
def Properties.AtomicBytesNeverPublished : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    ∀ d ∈ S.log, d.appends P → l1Message P d.bundle ∉ S.l1Messages

/-- **THE (c) CLASH DISJUNCT FIRES.** Under a colliding keccak, a deployed run in which two different
senders with the same salt dispatch one identical bundle (two router withdrawals). -/
def Properties.SaltClashLetsTwoSendersShareABundle : Prop :=
  ∃ (P : Params) (S : State), Reach deployed P init S ∧
    ∃ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j ∧
      S.log[i].bundle = S.log[j].bundle ∧ CrossSenderSaltClash P S.log[i] S.log[j]

/-! ## Non-vacuity -/

/-- **THE RUN-LEVEL PREMISES HOLD ON A NONTRIVIAL DEPLOYED RUN, AND THE CLASHES ARE FALSE ON IT.** On
the witness chain: sender `1`'s atomic `sendMessage` (leg authorized, so `Revertable`), sender `2`'s
atomic `sendBundle` whose direct call carries value `9` (committed; not `Validated` in the pin's
sense; refunded to sender `2`), and sender `3`'s L1 withdrawal without `atomicBundle` (published).
The encoder separates the bundles, keccak is injective on the run's salt preimages and encodings,
and no salt or bundle-hash clash holds between the two atomic dispatches. -/
def Properties.SendAtHeadWitness : Prop :=
  Reach deployed headParams init headS4 ∧ headS4.log = [headMsg, headValueLeg, headWithdrawal] ∧
    EncInjOn headParams.enc (headS4.log.map Dispatch.bundle) ∧
    KeccakInjOn headParams.keccak (saltPreimages headS4.log) ∧
    KeccakInjOn headParams.keccak (bundleEncodings headParams headS4.log) ∧
    headMsg.entry = .sendMessage ∧ HasAtomicBundle headMsg.attrs ∧
    headS4.manager.legState (flowIdOf headParams headMsg.atomicSend.flowPreimage)
      (bundleHash headParams headMsg.bundle) = .Revertable ∧
    headValueLeg.atomicSend.isAtomic = true ∧ ¬ Contracts.InteropCenter.Validated headValueLeg.bundle ∧
    headS4.manager.legState (flowIdOf headParams headValueLeg.atomicSend.flowPreimage)
      (bundleHash headParams headValueLeg.bundle) = .Committed ∧
    baseTokenRefunds headParams headValueLeg.bundle = [(headValueLeg.sender, 9)] ∧
    ¬ HasAtomicBundle headWithdrawal.attrs ∧
    headS4.l1Messages = [l1Message headParams headWithdrawal.bundle] ∧
    ¬ SaltClash headParams headMsg headValueLeg ∧
    ¬ BundleHashClash headParams headMsg.bundle headValueLeg.bundle

/-- **THE PER-STEP PREMISES ARE SATISFIABLE, ON THE SAME RUN.** The first step dispatches the
`sendMessage` (`SendMessageAlwaysAtomic`, the attribute branch of
`AtomicBundleAttributeMeansAppended`, `PinFindingRejectedAtHead`, and `OnlyADispatchCommitsALeg`:
its leg leaves `Unset`); the second starts with the first sender's salt used
(`UsedSaltHasNoDispatch`); the third dispatches the withdrawal, a `sendBundle` without the attribute
and non-atomic (the other branch, `CallLevelAtomicBundleReverts`,
`NonAtomicL2SendRevertsInAppend`), and is also a step of `withPinSendMessage`
(`PinConstantMakesSendMessageUnusable`). A `sendMessage` dispatch without the attribute exists
(`SendMessageWithoutAttributeReverts`). -/
def Properties.SendAtHeadStepWitness : Prop :=
  Step deployed headParams init headS1 ∧ headS1.log = init.log ++ [headMsg] ∧
    headMsg.entry = .sendMessage ∧ HasAtomicBundle headMsg.attrs ∧
    parseAttributes headMsg.attrs .callAndBundleAttributes ≠ none ∧
    init.manager.legState 7 1 = .Unset ∧ headS1.manager.legState 7 1 ≠ .Unset ∧
    headS1.saltUsed headMsg.sender headMsg.salt = true ∧ Step deployed headParams headS1 headS2 ∧
    Step deployed headParams headS2 headS3 ∧ headS3.log = headS2.log ++ [headWithdrawal] ∧
    headWithdrawal.entry = .sendBundle ∧ ¬ HasAtomicBundle headWithdrawal.attrs ∧
    headWithdrawal.atomicSend.isAtomic = false ∧
    Step withPinSendMessage headParams headS2 headS3 ∧
    ∃ d : Dispatch, d.entry = .sendMessage ∧ ¬ HasAtomicBundle d.attrs

/-- **`ClaimedBundleIsDispatchedOrCollision`'S PREMISES HOLD, AND ITS FIRST DISJUNCT.** On the honest
run, `headDec` inverts the encoder on the run's bundles, and `claimRefund(7, x)` with `x` the
`sendMessage` bundle's encoding finds its leg `Revertable`; `x` decodes to that bundle. -/
def Properties.SendAtHeadClaimWitness : Prop :=
  (∀ d ∈ headS4.log, headDec (headParams.enc d.bundle) = d.bundle) ∧
    headS4.manager.legState 7 (headParams.keccak (headParams.enc headMsg.bundle)) = .Revertable ∧
    headDec (headParams.enc headMsg.bundle) = headMsg.bundle

end Contracts.InteropCenter.SendAtHead
