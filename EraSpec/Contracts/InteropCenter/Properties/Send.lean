import EraSpec.Contracts.InteropCenter.Specs.Send
import EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimits
import EraSpec.Core.Headline

/-!
# Properties: the send path at `draft/v0.35.0` (`b17415d20`)

Statements about `EraSpec.Contracts.InteropCenter.Specs.Send`. Proofs are in
`EraSpec.Contracts.InteropCenter.Proofs.Send`. Every run starts from fresh storage (`init`)
on one chain; `deployed` is the `b17415d20` code with all six of its switchable checks. "Head" in
statement names (`ValueLegCommitsAtHead`, …) means `b17415d20`, as opposed to the `c67894b9` record
under `History/`. No result takes a
global hash or encoding premise: the hash premises are run-local (`EncInjOn`, `KeccakInjOn` on the
run's own inputs) or a collision pinned to two named byte strings or bundles. "Committed" below is
the manager's leg state; the commitment-tree insert that follows it in `append` is not modelled.

## 1. The attribute parser

`parseAtomicSend` returns exactly the attribute's payload (`ParseAtomicSendIsTheAttribute`), and
`atomicBundle` is a bundle-level attribute (`AtomicBundleIsABundleAttribute`). The `c67894b9`
`sendMessage` dropped the attribute; that record, and the agreement of the old parser with this
one, are `History/Properties/SendMessageFinding.lean`.

## 2. `sendMessage` is always atomic

Every successful `sendMessage` carries `atomicBundle`, sends to a chain other than L1, commits its
leg and sends nothing to L1 (`SendMessageAlwaysAtomic`; along runs
`SendMessagesAreAtomicAlongRuns`); without the attribute no step dispatches it
(`SendMessageWithoutAttributeReverts`). This rests on `_ensureL2ToL2`
(`WithoutL2ToL2CheckSendMessagePublishes`) and on `parseAtomicSend`: with the `c67894b9` constant non-atomic
`AtomicSend` in its place the gate leaves `sendMessage` no step at all (`PinConstantMakesSendMessageUnusable`).

## 3. The `atomicBundle` NatSpec (IERC7786Attributes.sol:27-31), in the model

For both entry points, a successful send whose `parseAtomicSend` list carries `atomicBundle` commits
the leg `(keccak(abi.encode(preimage)), bundleHash)`, with the bundle hash one of the flow's legs
declared from this chain, and sends nothing to L1; one without it goes to L1, is sent to L1 and
leaves the manager unchanged (`AtomicBundleAttributeMeansAppended`). The attribute is bundle-level:
in the attribute list of a `sendBundle` call starter the send has no step
(`CallLevelAtomicBundleReverts`, `AtomicBundleIsABundleAttribute`). Along runs, appended, atomic and
attribute-carrying coincide (`EveryL2SendIsAtomic`), and the L1 messages are exactly the L1
dispatches (`PublishedMessagesAreL1Dispatches`), each a `sendBundle` of one zero-value call whose
`from` is the asset router (`PublishedMessagesAreWithdrawals`).
`NonAtomicSendUnsupported` is defense in depth: whatever the checks, a non-atomic send that has a step
goes to L1, because `append` rejects its empty flow (`NonAtomicL2SendRevertsInAppend`).
`AtomicBundleToL1NotSupported` is load-bearing for the NatSpec
(`WithoutAtomicityGateAttributeBundleIsPublished`).

## 4. The `c67894b9` record's (`History/Dispatch`) results, restated at `b17415d20`

* **(a) Salts**: unchanged (`SaltFlagRecordsDispatches`, `SaltFlagsNeverCleared`,
  `UsedSaltHasNoDispatch`, `EachSaltDispatchesOnce`; countermodel
  `WithoutSaltCheckABundleRepeats`).
* **(b) The value check is gone, so the record's (b) is false at `b17415d20`**: a value-carrying leg
  is committed by the deployed code (`ValueLegCommitsAtHead`; `Validated` fails on it). Its
  repaired form: every committed leg comes from an atomic dispatch of this chain whose value-carrying
  calls have the sender as `from` and whose other calls are zero-value calls from the asset router
  (`CommittedLegsAreCheckedDispatches`, per step `OnlyADispatchCommitsALeg`, funnel `SolePath`,
  `ValidationUnbypassableDischarged`). So the base-token refunds `_recoverBundle` would make for a
  logged bundle go to its sender and add up to its `totalBurnedCallsValue`
  (`AtomicValueIsRefundedToPayer`), unless the sender is the asset router itself
  (`RouterSenderValueIsNotRefunded`); the indirect-call restriction is load-bearing
  (`WithoutIndirectRestrictionRefundMissesPayer`). The bytes `claimRefund` hashes are a logged atomic
  dispatch's encoding, or keccak collides on two named strings
  (`ClaimedBundleIsDispatchedOrCollision`; the disjunct is needed,
  `CollisionLetsForeignBytesMatchACommittedLeg`); for bundles, `PresentedBundleIsDispatchedOrClash`
  (`CollisionLetsAForeignBundleMatchACommittedLeg`). Legs: `AppendedLegsStayCommitted`,
  `EachLegAppendedOnce`, `WithoutOnlyInteropCenterUnbackedLegCommits`, `BurnedTotalIsCallValues`.
* **(c) Distinct dispatches**: `DistinctDispatchesDistinctBundles` (no hash premise),
  `DistinctDispatchesDistinctBundleHashes`, `LoggedRunBundleHashesUnique` with the bundle-hash preimage
  `abi.encode(bundle)`; firing `SaltClashLetsTwoSendersShareABundle` and
  `BundleHashClashFiresAlone`. `AtomicBytesNeverPublished` is stronger than in the record: no
  salt-clash disjunct, any checks.
* **(d) One flow per bundle hash** (not stated in the record; the flow is passed outside the
  bundle, :720-724): two legs that are not `Unset` and share a bundle hash share the flow id, or two
  logged dispatches clash (`BundleHashCommittedUnderOneFlowOrClash`; run-local
  `BundleHashCommittedUnderOneFlow`). Without the salt check one bundle is committed under two flows
  while every run-local hash premise holds (`WithoutSaltCheckABundleJoinsTwoFlows`); the clash
  disjunct fires (`BundleHashCollisionJoinsTwoFlows`).

## Non-vacuity

`SendWitness` is a deployed run (an atomic `sendMessage`, an atomic value leg, an L1
withdrawal, one authorization) meeting every premise of the run-level statements, with the clashes
false on its two atomic dispatches. `SendStepWitness` meets the per-step premises, and
`SendClaimWitness` those of `ClaimedBundleIsDispatchedOrCollision`.
`BundleHashCollisionJoinsTwoFlows` meets every premise of `BundleHashCommittedUnderOneFlowOrClash`
with two different flow ids; on a deployed run that meets the premises of
`BundleHashCommittedUnderOneFlow` the two legs can only be one leg (that is the result), as on
`SendWitness`. The run-local premises
`EncInjOn` and `KeccakInjOn` (`Specs/Common.lean`) are satisfiable: `EncInjOn` for every list of bundles
(`Contracts.InteropCenter.EncInjOnSatisfiable`), `KeccakInjOn` for every list of byte strings no
longer than the word space (`Contracts.InteropCenter.KeccakInjOnSatisfiable`).
-/

namespace Contracts.InteropCenter.Send

open Contracts.AtomicFlowManager (LegState)

/-! ## The attribute parser -/

/-- **`parseAtomicSend` IS THE ATTRIBUTE.** It reports atomic iff the list carries `atomicBundle`;
then it returns the preimage and `lowNullifierIndex` of an `atomicBundle` attribute of the list (the
first; a list `parseAttributes` accepts has at most one), and otherwise the zero `AtomicSend`. -/
def Properties.ParseAtomicSendIsTheAttribute : Prop :=
  ∀ attrs : List Attribute,
    ((parseAtomicSend attrs).isAtomic = true ↔ HasAtomicBundle attrs) ∧
    (HasAtomicBundle attrs → ∃ pre lni, Attribute.atomicBundle pre lni ∈ attrs ∧
      parseAtomicSend attrs = ⟨pre, lni, true⟩) ∧
    (¬ HasAtomicBundle attrs → parseAtomicSend attrs = AtomicSend.empty)

/-- **`atomicBundle` IS A BUNDLE-LEVEL ATTRIBUTE.** `parseAttributes` rejects every list carrying it
under `OnlyCallAttributes` (the per-call restriction of `sendBundle`, :503-506) and under
`OnlyInteropCallValue`; it accepts the attribute alone under `OnlyBundleAttributes` (`sendBundle`'s
bundle attributes, :514) and `CallAndBundleAttributes` (`sendMessage`, :209-212), writing no field. -/
def Properties.AtomicBundleIsABundleAttribute : Prop :=
  (∀ attrs, HasAtomicBundle attrs →
    parseAttributes attrs .onlyCallAttributes = none ∧
      parseAttributes attrs .onlyInteropCallValue = none) ∧
  ∀ (pre : FlowPreimage) (lni : ℕ),
    parseAttributes [.atomicBundle pre lni] .onlyBundleAttributes
        = some (noCallAttributes, noBundleAttributes) ∧
      parseAttributes [.atomicBundle pre lni] .callAndBundleAttributes
        = some (noCallAttributes, noBundleAttributes)

/-! ## 2. `sendMessage` is always atomic -/

/-- **HEADLINE: EVERY SUCCESSFUL `sendMessage` IS ATOMIC.** A step of the deployed code that
dispatches a `sendMessage` used an attribute list carrying `atomicBundle`, passed that list's
`parseAtomicSend` (atomic), sent to a chain other than L1, moved its leg
`(flowId(preimage), bundleHash)` from `Unset` to `Committed`, and sent nothing to L1. -/
@[headline] def Properties.SendMessageAlwaysAtomic : Prop :=
  ∀ (P : Params) (S S' : State) (d : Dispatch), Step deployed P S S' → S'.log = S.log ++ [d] →
    d.entry = .sendMessage →
      HasAtomicBundle d.attrs ∧ d.atomicSend = parseAtomicSend d.attrs ∧
      d.atomicSend.isAtomic = true ∧ d.appends P ∧
      S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) = .Unset ∧
      S'.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle)
        = .Committed ∧
      S'.l1Messages = S.l1Messages

/-- **A `sendMessage` WITHOUT `atomicBundle` HAS NO STEP.** No step of the deployed code dispatches
it (`NonAtomicSendUnsupported`, :555, against `_ensureL2ToL2`, :207). -/
def Properties.SendMessageWithoutAttributeReverts : Prop :=
  ∀ (P : Params) (S S' : State) (d : Dispatch), d.entry = .sendMessage →
    ¬ HasAtomicBundle d.attrs → Step deployed P S S' → S'.log ≠ S.log ++ [d]

/-- **ALONG ANY RUN, EVERY `sendMessage` IS AN APPENDED ATOMIC LEG.** Every logged `sendMessage`
dispatch of a deployed run carries `atomicBundle`, is atomic, took the branch that is not L1's, and
its leg is not `Unset`. -/
def Properties.SendMessagesAreAtomicAlongRuns : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ d ∈ S.log, d.entry = .sendMessage →
      HasAtomicBundle d.attrs ∧ d.atomicSend.isAtomic = true ∧ d.appends P ∧
        S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) ≠ .Unset

/-- **`parseAtomicSend` IS WHAT KEEPS `sendMessage` LIVE.** With the `c67894b9` constant non-atomic
`AtomicSend` in place of `parseAtomicSend` (pin :246-252) and the other checks, no step
dispatches a `sendMessage` at all: the gate (:555) wants L1, `_ensureL2ToL2` (:207) forbids it. -/
@[countermodel] def Properties.PinConstantMakesSendMessageUnusable : Prop :=
  ∀ (P : Params) (S S' : State) (d : Dispatch), Step withPinSendMessage P S S' →
    S'.log = S.log ++ [d] → d.entry ≠ .sendMessage

/-- **WITHOUT `_ensureL2ToL2`, A `sendMessage` IS PUBLISHED.** A run of the code without :207 in
which a `sendMessage` without `atomicBundle` goes to L1, non-atomically, and is the run's only L1
message. (In the witness it is an indirect zero-value call to the asset router.) -/
@[countermodel] def Properties.WithoutL2ToL2CheckSendMessagePublishes : Prop :=
  ∃ (P : Params) (S : State), Reach withoutL2ToL2Check P init S ∧
    ∃ d ∈ S.log, d.entry = .sendMessage ∧ ¬ HasAtomicBundle d.attrs ∧
      d.atomicSend.isAtomic = false ∧ d.bundle.destinationChainId = P.l1ChainId ∧
      S.l1Messages = [l1Message P d.bundle]

/-! ## 3. The `atomicBundle` NatSpec -/

/-- **HEADLINE: THE `atomicBundle` NATSPEC (IERC7786Attributes.sol:27-31), IN THE MODEL.** For both
entry points: if a step of the deployed code dispatches `d` and the list `parseAtomicSend` reads
(`d.attrs`) carries `atomicBundle`, then `d`'s `AtomicSend` is that list's `parseAtomicSend`
(atomic), its destination is not L1, its bundle hash is one of the flow's legs and the first matching
leg declares this chain as its source ("requires this bundle's hash to be one of its legs"), its leg
`(keccak(abi.encode(preimage)), bundleHash)` moves from `Unset` to `Committed` with no other change
to the manager, and nothing is sent to L1. That is the model's form of "appends the bundle's commit
value to the interop IMT instead of publishing it to L1": the tree insert after the write
(AtomicFlowManager.sol:168-170) is not modelled. Otherwise `d` has the zero `AtomicSend` and
destination L1, the manager is unchanged, and `BUNDLE_IDENTIFIER ++ abi.encode(bundle)` is sent to
L1. -/
@[headline] def Properties.AtomicBundleAttributeMeansAppended : Prop :=
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

/-- **A CALL-LEVEL `atomicBundle` HAS NO STEP.** Whatever the checks, no step dispatches a
`sendBundle` one of whose per-call attribute lists carries `atomicBundle` (`OnlyCallAttributes`
forbids it). -/
def Properties.CallLevelAtomicBundleReverts : Prop :=
  ∀ (K : Checks) (P : Params) (S S' : State) (d : Dispatch), Step K P S S' →
    S'.log = S.log ++ [d] → d.entry = .sendBundle → ∀ l ∈ d.callAttrs, ¬ HasAtomicBundle l

/-- **ALONG ANY RUN, APPENDED = ATOMIC = CARRIES `atomicBundle`.** For every logged dispatch of a
run of the deployed code from fresh storage (`init`), `_dispatchBundle` took the branch that is not L1's iff the send was atomic, iff its
`parseAtomicSend` list carries `atomicBundle`. -/
@[headline] def Properties.EveryL2SendIsAtomic : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S → ∀ d ∈ S.log,
    (d.appends P ↔ d.atomicSend.isAtomic = true) ∧
      (d.atomicSend.isAtomic = true ↔ HasAtomicBundle d.attrs)

/-- **`NonAtomicSendUnsupported` IS DEFENSE IN DEPTH.** Whatever the checks, a step that dispatches a
non-atomic `d` sends it to L1: its `AtomicSend` is the zero struct, whose flow has no leg, so
`append` would revert (AtomicFlowManager.sol:138-140; in the code `_validateAndComputeFlowId`
already rejects the zero version, :361-363, as `ATOMIC_FLOW_PREIMAGE_VERSION` is `0x01`,
`IAtomicInterop.sol:91`). -/
def Properties.NonAtomicL2SendRevertsInAppend : Prop :=
  ∀ (K : Checks) (P : Params) (S S' : State) (d : Dispatch), Step K P S S' →
    S'.log = S.log ++ [d] → d.atomicSend.isAtomic = false → d.bundle.destinationChainId = P.l1ChainId

/-- **WITHOUT `AtomicBundleToL1NotSupported`, THE NATSPEC FAILS.** A run of the code without the
gate (:552-556) in which a `sendBundle` carrying `atomicBundle`, atomic, goes to L1, is the run's
only L1 message, and no leg is committed: `_dispatchBundle` branches on the destination (:733). -/
@[countermodel] def Properties.WithoutAtomicityGateAttributeBundleIsPublished : Prop :=
  ∃ (P : Params) (S : State), Reach withoutAtomicityGate P init S ∧
    ∃ d ∈ S.log, d.entry = .sendBundle ∧ HasAtomicBundle d.attrs ∧ d.atomicSend.isAtomic = true ∧
      d.bundle.destinationChainId = P.l1ChainId ∧
      S.l1Messages = [l1Message P d.bundle] ∧ ∀ f h, S.manager.legState f h = .Unset

/-- **THE CENTER'S L1 MESSAGES ARE EXACTLY ITS L1 DISPATCHES.** Along any run, with or without the
checks, the messages sent to L1 are `BUNDLE_IDENTIFIER ++ abi.encode(bundle)` of the logged
dispatches whose destination is L1, in order. -/
def Properties.PublishedMessagesAreL1Dispatches : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    S.l1Messages = (S.log.filter fun d => decide (d.bundle.destinationChainId = P.l1ChainId)).map
      fun d => l1Message P d.bundle

/-- **EVERY DISPATCH TO L1 IS A ONE-CALL ROUTER WITHDRAWAL WITH NO CALL VALUE.** Along any run of the deployed
code from fresh storage (`init`), a logged dispatch to L1 is a `sendBundle` without `atomicBundle` and with the zero `AtomicSend`,
of one call, whose `from` is the asset router and whose value is zero, and its
`totalBurnedCallsValue` is zero, so `_ensureCorrectTotalValue` burns or deposits no call value
(:436-452). The source-side value the router receives for an indirect call
(`indirectCallMessageValue`, :788-790) is not modelled. -/
@[headline] def Properties.PublishedMessagesAreWithdrawals : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ d ∈ S.log, d.bundle.destinationChainId = P.l1ChainId →
      d.entry = .sendBundle ∧ ¬ HasAtomicBundle d.attrs ∧ d.atomicSend = AtomicSend.empty ∧
      d.bundle.calls.length = 1 ∧ (∀ c ∈ d.bundle.calls, c.fromAddr = P.assetRouter ∧ c.value = 0) ∧
      totalBurnedCallsValue d.starters = 0

/-! ## 4(a). Sender salts, as in the `c67894b9` record -/

/-- **THE SALT FLAG RECORDS EXACTLY THE DISPATCHED KEYS** (any checks). -/
def Properties.SaltFlagRecordsDispatches : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ∀ (a : Address) (s : Word), S.saltUsed a s = true ↔ ∃ d ∈ S.log, d.sender = a ∧ d.salt = s

/-- **A SET SALT FLAG STAYS SET** (any checks). -/
def Properties.SaltFlagsNeverCleared : Prop :=
  ∀ (K : Checks) (P : Params) (S S' : State), Step K P S S' →
    ∀ (a : Address) (s : Word), S.saltUsed a s = true → S'.saltUsed a s = true

/-- **A USED SALT HAS NO FURTHER DISPATCH** (:562-565). -/
def Properties.UsedSaltHasNoDispatch : Prop :=
  ∀ (P : Params) (S S' : State) (d : Dispatch), S.saltUsed d.sender d.salt = true →
    Step deployed P S S' → S'.log ≠ S.log ++ [d]

/-- **EACH `(sender, salt)` DISPATCHES AT MOST ONE BUNDLE.** Along any run of the deployed code from fresh storage (`init`), the keys of the
logged dispatches are pairwise distinct. -/
@[headline] def Properties.EachSaltDispatchesOnce : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S → (S.log.map Dispatch.key).Nodup

/-- **WITHOUT THE SALT CHECK, ONE BUNDLE IS DISPATCHED TWICE**, so one bundle hash, with no
collision. -/
@[countermodel] def Properties.WithoutSaltCheckABundleRepeats : Prop :=
  ∃ (P : Params) (S : State), Reach withoutSaltCheck P init S ∧
    ∃ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j ∧
      S.log[i].bundle = S.log[j].bundle ∧
      bundleHash P S.log[i].bundle = bundleHash P S.log[j].bundle

/-! ## 4(b). Validation at `b17415d20` -/

/-- **THE PIN'S (b) IS FALSE AT HEAD: A VALUE-CARRYING LEG IS COMMITTED.** A run of the deployed head
code commits an atomic leg whose bundle has a call carrying native value, and whose
`totalBurnedCallsValue` (the call value `_ensureCorrectTotalValue` burns or deposits, :436-452) is
nonzero. The conclusion `Validated` of the `c67894b9` record's
`Contracts.InteropCenter.History.Properties.CommittedLegsAreValidatedDispatches` (and of
`AtomicDispatchesCarryNoValue`) fails on it, and so does the `c67894b9` record's `AtomicDispatchBurnsNothing`. -/
@[countermodel] def Properties.ValueLegCommitsAtHead : Prop :=
  ∃ (P : Params) (S : State), Reach deployed P init S ∧
    ∃ d ∈ S.log, d.atomicSend.isAtomic = true ∧ ¬ Contracts.InteropCenter.Validated d.bundle ∧
      totalBurnedCallsValue d.starters ≠ 0 ∧
      S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) = .Committed

/-- **HEADLINE (b) AT HEAD: EVERY COMMITTED LEG IS A CHECKED ATOMIC DISPATCH OF THIS CHAIN.** Along
any run of the deployed code from fresh storage (`init`), for every leg `(f, h)` that is not `Unset` some logged dispatch is atomic, carries
`atomicBundle`, took the branch that is not L1's, has flow id `f = keccak(abi.encode(preimage))` and
bundle hash `h`, lists `h` in its preimage with this chain as that leg's source, was built with
`sourceChainId = block.chainid`, and has `CallsChecked` calls: a value-carrying call has the sender
as `from`, and every call whose `from` is not the sender is a zero-value call from the asset router. -/
@[headline] def Properties.CommittedLegsAreCheckedDispatches : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ (f h : Word), S.manager.legState f h ≠ .Unset →
      ∃ d ∈ S.log, d.atomicSend.isAtomic = true ∧ HasAtomicBundle d.attrs ∧ d.appends P ∧
        flowIdOf P d.atomicSend.flowPreimage = f ∧ bundleHash P d.bundle = h ∧
        FlowAccepts P d.atomicSend h ∧ d.bundle.sourceChainId = P.chainId ∧ CallsChecked P d

/-- **ONLY A DISPATCH COMMITS A LEG.** One step of the deployed code moves a leg out of `Unset` only
by logging an atomic, appended dispatch with that flow id and bundle hash and `CallsChecked` calls. -/
def Properties.OnlyADispatchCommitsALeg : Prop :=
  ∀ (P : Params) (S S' : State), Step deployed P S S' →
    ∀ (f h : Word), S.manager.legState f h = .Unset → S'.manager.legState f h ≠ .Unset →
      ∃ d, S'.log = S.log ++ [d] ∧ d.atomicSend.isAtomic = true ∧ d.appends P ∧
        flowIdOf P d.atomicSend.flowPreimage = f ∧ bundleHash P d.bundle = h ∧ CallsChecked P d

/-- **THE BURNED TOTAL IS THE CALLS' VALUES** (any checks; :681 and :819, :828). -/
def Properties.BurnedTotalIsCallValues : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ∀ d ∈ S.log, totalBurnedCallsValue d.starters = (d.bundle.calls.map InteropCall.value).sum

/-- **THE BASE-TOKEN REFUNDS OF A LEG GO TO ITS SENDER AND ADD UP TO ITS CALL VALUE.** Along any
run of the deployed code from fresh storage (`init`), for every logged dispatch whose sender is not the asset router, the base-token refunds
`_recoverBundle` would make for its bundle (`baseTokenRefunds`, AtomicFlowManager.sol:316-323) all go
to the sender and add up to `totalBurnedCallsValue`. In the code the sender is the payer of that
total (`msg.value`, or the destination base token through `bridgehubDepositBaseToken`, :432-452); the
payment is not modelled. -/
@[headline] def Properties.AtomicValueIsRefundedToPayer : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ d ∈ S.log, d.sender ≠ P.assetRouter →
      (∀ r ∈ baseTokenRefunds P d.bundle, r.1 = d.sender) ∧
        ((baseTokenRefunds P d.bundle).map Prod.snd).sum = totalBurnedCallsValue d.starters

/-- **THE ROUTER-SENDER PREMISE IS NEEDED.** A deployed run in which the asset router itself is the
sender of an atomic dispatch with nonzero `totalBurnedCallsValue` whose bundle gets no base-token
refund: `_recoverBundle` treats every call `from == L2_ASSET_ROUTER_ADDR` as a router call
(AtomicFlowManager.sol:312-316). The source comment there assumes the router never initiates a
direct send (AtomicFlowManager.sol:304-308). -/
@[countermodel] def Properties.RouterSenderValueIsNotRefunded : Prop :=
  ∃ (P : Params) (S : State), Reach deployed P init S ∧
    ∃ d ∈ S.log, d.sender = P.assetRouter ∧ d.atomicSend.isAtomic = true ∧
      totalBurnedCallsValue d.starters ≠ 0 ∧ baseTokenRefunds P d.bundle = []

/-- **WITHOUT THE INDIRECT-CALL RESTRICTION, A REFUND MISSES THE SENDER.** A run of the code without
:659-678 with an atomic dispatch, whose sender is not the asset router, one of whose base-token
refunds goes to an address other than the sender. (In the witness: an indirect call through contract
`8` carrying value, refunded to `8`, the reason given at :669-673.) -/
@[countermodel] def Properties.WithoutIndirectRestrictionRefundMissesPayer : Prop :=
  ∃ (P : Params) (S : State), Reach withoutIndirectRestriction P init S ∧
    ∃ d ∈ S.log, d.atomicSend.isAtomic = true ∧ d.sender ≠ P.assetRouter ∧
      ∃ r ∈ baseTokenRefunds P d.bundle, r.1 ≠ d.sender

/-- **THE FUNNEL, DERIVED.** Along any run of the deployed code from fresh storage (`init`), every appended dispatch is `CallsChecked`: the
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

/-- **THE BYTES `claimRefund` HASHES ARE A LOGGED ATOMIC DISPATCH'S, OR KECCAK COLLIDES.** Along any
run of the deployed code from fresh storage (`init`) whose decoder inverts the encoder on the run's bundles (`SOL-ABI`): if the leg
`(f, keccak(x))` that `claimRefund(f, x)` reads (AtomicFlowManager.sol:252-254) is not `Unset`, then
some logged atomic, appended, `CallsChecked` dispatch has flow id `f`, and either `x` is that
dispatch's `abi.encode(bundle)` and decodes to its bundle — the bundle `_recoverBundle` is then given,
whose destination is not the center's `L1_CHAIN_ID` — or keccak collides on `x` and that encoding.
Any bytes `x`. -/
@[headline] def Properties.ClaimedBundleIsDispatchedOrCollision : Prop :=
  ∀ (P : Params) (dec : List UInt8 → Bundle) (S : State), Reach deployed P init S →
    (∀ d ∈ S.log, dec (P.enc d.bundle) = d.bundle) →
    ∀ (f : Word) (x : List UInt8), S.manager.legState f (P.keccak x) ≠ .Unset →
      ∃ d ∈ S.log, d.atomicSend.isAtomic = true ∧ d.appends P ∧ CallsChecked P d ∧
        flowIdOf P d.atomicSend.flowPreimage = f ∧
        ((x = P.enc d.bundle ∧ dec x = d.bundle) ∨ KeccakClash P x (P.enc d.bundle))

/-- **ANY BUNDLE WHOSE HASH IS A COMMITTED LEG IS THE LOGGED ONE, OR CLASHES WITH IT.** The coarser
companion of `ClaimedBundleIsDispatchedOrCollision`: along any deployed run, if the leg
`(f, bundleHash b)` of some bundle `b` is not `Unset`, then some logged atomic, appended,
`CallsChecked` dispatch has flow id `f`, and `b` is its bundle, or `b` and its bundle are two
different bundles with one bundle hash. -/
def Properties.PresentedBundleIsDispatchedOrClash : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ (f : Word) (b : Bundle), S.manager.legState f (bundleHash P b) ≠ .Unset →
      ∃ d ∈ S.log, d.atomicSend.isAtomic = true ∧ d.appends P ∧ CallsChecked P d ∧
        flowIdOf P d.atomicSend.flowPreimage = f ∧
        (b = d.bundle ∨ (b ≠ d.bundle ∧ bundleHash P b = bundleHash P d.bundle))

/-- **THE COLLISION DISJUNCT IS NEEDED (BYTES).** Under a colliding keccak, a deployed run with a
leg `(f, keccak(x))` that is not `Unset`, for bytes `x` that are no logged bundle's encoding. -/
@[countermodel] def Properties.CollisionLetsForeignBytesMatchACommittedLeg : Prop :=
  ∃ (P : Params) (S : State) (f : Word) (x : List UInt8), Reach deployed P init S ∧
    S.manager.legState f (P.keccak x) ≠ .Unset ∧ ∀ d ∈ S.log, x ≠ P.enc d.bundle

/-- **THE CLASH DISJUNCT IS NEEDED (BUNDLES).** Under a colliding keccak, a deployed run with a leg
`(f, bundleHash b)` that is not `Unset`, for a bundle `b` that is no logged dispatch's bundle. -/
@[countermodel] def Properties.CollisionLetsAForeignBundleMatchACommittedLeg : Prop :=
  ∃ (P : Params) (S : State) (f : Word) (b : Bundle), Reach deployed P init S ∧
    S.manager.legState f (bundleHash P b) ≠ .Unset ∧ ∀ d ∈ S.log, b ≠ d.bundle

/-- **AN APPENDED LEG NEVER RETURNS TO `Unset`** (any checks). -/
def Properties.AppendedLegsStayCommitted : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ∀ d ∈ S.log, d.appends P →
      S.manager.legState (flowIdOf P d.atomicSend.flowPreimage) (bundleHash P d.bundle) ≠ .Unset

/-- **EACH LEG IS APPENDED AT MOST ONCE** (any checks): along any run from fresh storage (`init`), the legs of the run's appended dispatches are
pairwise distinct (AtomicFlowManager.sol:162-164). -/
@[headline] def Properties.EachLegAppendedOnce : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    ((S.log.filter fun d => decide (d.appends P)).map (legOf P)).Nodup

/-- **WITHOUT `onlyInteropCenter`, A LEG BACKED BY NO DISPATCH IS COMMITTED.** A run of the code
without AtomicFlowManager.sol:88-93 that dispatches nothing yet ends with a `Committed` leg. -/
@[countermodel] def Properties.WithoutOnlyInteropCenterUnbackedLegCommits : Prop :=
  ∃ (P : Params) (S : State) (f h : Word), Reach withoutOnlyInteropCenter P init S ∧
    S.log = [] ∧ S.manager.legState f h = .Committed

/-! ## 4(c). Distinct dispatches -/

/-- **(c), BUNDLES.** Along any run of the deployed code from fresh storage (`init`), two dispatches at different positions carry different
bundles, unless two different senders used the same salt and keccak collides on their packed
preimages. No hash premise. -/
@[headline] def Properties.DistinctDispatchesDistinctBundles : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    ∀ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j →
      S.log[i].bundle ≠ S.log[j].bundle ∨ CrossSenderSaltClash P S.log[i] S.log[j]

/-- **(c), BUNDLE HASHES.** If the encoder separates the run's bundles, two dispatches' bundle hashes
differ, or the cross-sender salt clash, or keccak collides on their two encodings — the
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

/-- **AN APPENDED BUNDLE IS NEVER PUBLISHED TO L1.** Along any run from fresh storage (`init`), with or without the checks,
if the encoder separates the run's bundles, no appended dispatch's `BUNDLE_IDENTIFIER ++
abi.encode(bundle)` is among the center's L1 messages. In the `c67894b9` record the deployed form needed a
cross-sender salt-clash disjunct (`Contracts.InteropCenter.History.Properties.AtomicBytesNeverPublished`);
at `b17415d20` `_dispatchBundle` publishes exactly the bundles whose destination is L1 and appends the
others. -/
@[headline] def Properties.AtomicBytesNeverPublished : Prop :=
  ∀ (K : Checks) (P : Params) (S : State), Reach K P init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    ∀ d ∈ S.log, d.appends P → l1Message P d.bundle ∉ S.l1Messages

/-- **THE (c) SALT-CLASH DISJUNCT FIRES.** Under a colliding keccak, a deployed run in which two
different senders with the same salt dispatch one identical bundle. (In the witness: two router
withdrawals.) -/
@[countermodel] def Properties.SaltClashLetsTwoSendersShareABundle : Prop :=
  ∃ (P : Params) (S : State), Reach deployed P init S ∧
    ∃ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j ∧
      S.log[i].bundle = S.log[j].bundle ∧ CrossSenderSaltClash P S.log[i] S.log[j]

/-- **THE (c) BUNDLE-HASH-CLASH DISJUNCT FIRES ALONE.** Under a colliding keccak, a deployed run whose
encoder separates its bundles, with two dispatches whose bundle hashes are equal, which are no
cross-sender salt clash, and whose encodings keccak collides on: the third disjunct of
`DistinctDispatchesDistinctBundleHashes` is the only one that holds. -/
@[countermodel] def Properties.BundleHashClashFiresAlone : Prop :=
  ∃ (P : Params) (S : State), Reach deployed P init S ∧ EncInjOn P.enc (S.log.map Dispatch.bundle) ∧
    ∃ (i j : ℕ) (hi : i < S.log.length) (hj : j < S.log.length), i ≠ j ∧
      bundleHash P S.log[i].bundle = bundleHash P S.log[j].bundle ∧
      ¬ CrossSenderSaltClash P S.log[i] S.log[j] ∧
      BundleHashClash P S.log[i].bundle S.log[j].bundle

/-! ## 4(d). One flow per bundle hash -/

/-- **EACH BUNDLE HASH IS COMMITTED UNDER ONE FLOW ID, OR A LOGGED CLASH.** Along any run of the deployed code from fresh storage (`init`)
whose encoder separates its bundles: if two legs `(f, h)` and `(f', h)` with one bundle hash are not
`Unset`, then `f = f'`, or two logged dispatches with flow ids `f` and `f'` and bundle hash `h` are a
cross-sender salt clash or keccak collides on their two encodings. The flow is not part of the
bundle (:720-724), so it is the salt check that keeps a bundle out of a second flow
(`WithoutSaltCheckABundleJoinsTwoFlows`). -/
@[headline] def Properties.BundleHashCommittedUnderOneFlowOrClash : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    ∀ (f f' h : Word), S.manager.legState f h ≠ .Unset → S.manager.legState f' h ≠ .Unset →
      f = f' ∨ ∃ d ∈ S.log, ∃ d' ∈ S.log, flowIdOf P d.atomicSend.flowPreimage = f ∧
        flowIdOf P d'.atomicSend.flowPreimage = f' ∧ bundleHash P d.bundle = h ∧
        bundleHash P d'.bundle = h ∧
        (CrossSenderSaltClash P d d' ∨ BundleHashClash P d.bundle d'.bundle)

/-- **RUN-LOCAL: EACH BUNDLE HASH IS COMMITTED UNDER ONE FLOW ID.** As above, if moreover keccak is
injective on the run's salt preimages and on its bundle encodings: two legs that are not `Unset` and
share a bundle hash share the flow id. -/
def Properties.BundleHashCommittedUnderOneFlow : Prop :=
  ∀ (P : Params) (S : State), Reach deployed P init S →
    EncInjOn P.enc (S.log.map Dispatch.bundle) →
    KeccakInjOn P.keccak (saltPreimages S.log) →
    KeccakInjOn P.keccak (bundleEncodings P S.log) →
    ∀ (f f' h : Word), S.manager.legState f h ≠ .Unset → S.manager.legState f' h ≠ .Unset → f = f'

/-- **WITHOUT THE SALT CHECK, ONE BUNDLE IS COMMITTED UNDER TWO FLOWS.** A run of the code without
:562-565 whose encoder separates its bundles and whose keccak is injective on its salt preimages and
bundle encodings, with two `Committed` legs that share a bundle hash and have different flow ids.
(In the witness one sender dispatches one bundle twice, with two flow preimages that both list its
hash. So the salt-preimage list and the encoding list each hold one value twice, and injectivity
on them holds trivially: what the countermodel shows is that the salt check, not hashing, keeps
a bundle out of a second flow.) -/
@[countermodel] def Properties.WithoutSaltCheckABundleJoinsTwoFlows : Prop :=
  ∃ (P : Params) (S : State), Reach withoutSaltCheck P init S ∧
    EncInjOn P.enc (S.log.map Dispatch.bundle) ∧ KeccakInjOn P.keccak (saltPreimages S.log) ∧
    KeccakInjOn P.keccak (bundleEncodings P S.log) ∧
    ∃ (f f' h : Word), f ≠ f' ∧ S.manager.legState f h = .Committed ∧
      S.manager.legState f' h = .Committed

/-- **THE CLASH DISJUNCT FIRES.** A deployed run, under a keccak that collides on bundle encodings,
whose encoder separates its bundles, with two `Committed` legs that share a bundle hash and have
different flow ids. -/
@[countermodel] def Properties.BundleHashCollisionJoinsTwoFlows : Prop :=
  ∃ (P : Params) (S : State), Reach deployed P init S ∧ EncInjOn P.enc (S.log.map Dispatch.bundle) ∧
    ∃ (f f' h : Word), f ≠ f' ∧ S.manager.legState f h = .Committed ∧
      S.manager.legState f' h = .Committed

/-! ## Non-vacuity -/

/-- **THE RUN-LEVEL PREMISES HOLD ON A NONTRIVIAL DEPLOYED RUN, AND THE CLASHES ARE FALSE ON IT.** On
the witness chain: sender `1`'s atomic `sendMessage` (leg authorized, so `Revertable`), sender `2`'s
atomic `sendBundle` whose direct call carries value `9` (committed; not `Validated` in the `c67894b9` record's
sense; its one base-token refund would go to sender `2`), and sender `3`'s L1 withdrawal without
`atomicBundle` (published). The encoder separates the bundles, keccak is injective on the run's salt
preimages and encodings, and no salt or bundle-hash clash holds between the two atomic dispatches. -/
@[witness] def Properties.SendWitness : Prop :=
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
`sendMessage`, whose list carries `atomicBundle` and is accepted by `parseAttributes` under
`CallAndBundleAttributes` (`SendMessageAlwaysAtomic`, the attribute branch of
`AtomicBundleAttributeMeansAppended`, and `OnlyADispatchCommitsALeg`: its leg leaves `Unset`); the second
starts with the first sender's salt used (`UsedSaltHasNoDispatch`, `SaltFlagsNeverCleared`); the
third dispatches the withdrawal, a `sendBundle` without the attribute and non-atomic (the other
branch, `CallLevelAtomicBundleReverts`, `NonAtomicL2SendRevertsInAppend`), and is also a step of
`withPinSendMessage` (`PinConstantMakesSendMessageUnusable`). A `sendMessage` dispatch without the
attribute exists (`SendMessageWithoutAttributeReverts`). -/
@[witness] def Properties.SendStepWitness : Prop :=
  Step deployed headParams init headS1 ∧ headS1.log = init.log ++ [headMsg] ∧
    headMsg.entry = .sendMessage ∧ HasAtomicBundle headMsg.attrs ∧
    parseAttributes headMsg.attrs .callAndBundleAttributes ≠ none ∧
    init.manager.legState 7 1 = .Unset ∧ headS1.manager.legState 7 1 ≠ .Unset ∧
    headS1.saltUsed headMsg.sender headMsg.salt = true ∧ Step deployed headParams headS1 headS2 ∧
    Step deployed headParams headS2 headS3 ∧ headS3.log = headS2.log ++ [headWithdrawal] ∧
    headWithdrawal.entry = .sendBundle ∧ ¬ HasAtomicBundle headWithdrawal.attrs ∧
    headWithdrawal.atomicSend.isAtomic = false ∧
    Step withPinSendMessage headParams headS2 headS3 ∧
    (∃ d : Dispatch, d.entry = .sendMessage ∧ ¬ HasAtomicBundle d.attrs)

/-- **`ClaimedBundleIsDispatchedOrCollision`'S PREMISES HOLD, WITH ITS FIRST DISJUNCT.** On the
honest run, `headDec` inverts the encoder on the run's bundles, and the leg `claimRefund(7, x)` reads,
for `x` the `sendMessage` bundle's encoding, is `Revertable`; `x` decodes to that bundle. -/
@[witness] def Properties.SendClaimWitness : Prop :=
  (∀ d ∈ headS4.log, headDec (headParams.enc d.bundle) = d.bundle) ∧
    headS4.manager.legState 7 (headParams.keccak (headParams.enc headMsg.bundle)) = .Revertable ∧
    headDec (headParams.enc headMsg.bundle) = headMsg.bundle

end Contracts.InteropCenter.Send
