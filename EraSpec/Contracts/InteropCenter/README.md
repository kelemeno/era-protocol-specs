# InteropCenter

Source: `contracts/interop/InteropCenter.sol` in the pinned era-contracts tree, with
`contracts/atomic-interop/AtomicFlowManager.sol` for the leg state that `append` writes.
Topics `SendAtHead`, `FeeState` and `FeeReentry` are pinned to later era-contracts commits
instead, as their table rows and sections say.
Only the send path is modelled: the salt mapping `isInteropBundleSaltUsed`, bundle
formation in `_sendBundle`, `_validateAtomicBundle`, and `_dispatchBundle` →
`AtomicFlowManager.append`. Topic `AtomicRouting` adds the send entry points' handling of
the `atomicBundle` attribute, the refund loop and the destination handlers' bundle status.
`ClaimBinding` adds no state or step: it names what one
`AtomicFlowManager.claimRefund` computes from the bytes it is given, on the same runs.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Dispatch | [Specs/Dispatch.lean](Specs/Dispatch.lean) | [Properties/Dispatch.lean](Properties/Dispatch.lean) | [Proofs/Dispatch.lean](Proofs/Dispatch.lean) |
| SendAtHead (main `3605e82` = `70096e2ea`; `draft/v0.35.0` `b17415d20`) | [Specs/SendAtHead.lean](Specs/SendAtHead.lean) | [Properties/SendAtHead.lean](Properties/SendAtHead.lean) | [Proofs/SendAtHead.lean](Proofs/SendAtHead.lean) |
| AtomicRouting | [Specs/AtomicRouting.lean](Specs/AtomicRouting.lean) | [Properties/AtomicRouting.lean](Properties/AtomicRouting.lean) | [Proofs/AtomicRouting.lean](Proofs/AtomicRouting.lean) |
| ClaimBinding | [Specs/ClaimBinding.lean](Specs/ClaimBinding.lean) | [Properties/ClaimBinding.lean](Properties/ClaimBinding.lean) | [Proofs/ClaimBinding.lean](Proofs/ClaimBinding.lean) |
| FeeState (`b17415d20`) | [Specs/FeeState.lean](Specs/FeeState.lean) | [Properties/FeeState.lean](Properties/FeeState.lean) | [Proofs/FeeState.lean](Proofs/FeeState.lean) |
| FeeReentry (`b17415d20`) | [Specs/FeeReentry.lean](Specs/FeeReentry.lean) | [Properties/FeeReentry.lean](Properties/FeeReentry.lean) | [Proofs/FeeReentry.lean](Proofs/FeeReentry.lean) |

Namespace `Contracts.InteropCenter`. Statements are `Contracts.InteropCenter.Properties.*`;
each certificate has the same name without the `Properties` segment.

- **Salts do not replay.** Along any run of the deployed code from fresh storage, the
  `(sender, salt)` keys of all dispatches are pairwise distinct (`EachSaltDispatchesOnce`;
  no hash premise). The flag records exactly the dispatched keys and is never cleared
  (`SaltFlagRecordsDispatches`, `SaltFlagsNeverCleared`). Without the check the same
  bundle, and so the same bundle hash, is dispatched twice with no hash collision
  (`WithoutSaltCheckABundleRepeats`).
- **Committed legs carry no native value.** Every manager leg that is not `Unset` was
  committed by a logged atomic dispatch of this chain with that flow id and bundle hash,
  whose bundle passed `_validateAtomicBundle` (`CommittedLegsAreValidatedDispatches`; per
  step `OnlyADispatchCommitsALeg`; no hash premise). The model includes a foreign
  direct-`append` step, so the result depends on `onlyInteropCenter` rather than assuming
  it. Both checks are load-bearing (`WithoutValueCheckValueLegCommits`,
  `WithoutOnlyInteropCenterUnbackedLegCommits`). An atomic dispatch burns no base token
  (`AtomicDispatchBurnsNothing`), and each leg is appended at most once
  (`EachLegAppendedOnce`).
  - `AtomicFlowManager`'s `validation_unbypassable` takes the funnel `sole_path` as a
    premise. `SolePath` proves it for the center's appended bundles, and
    `ValidationUnbypassableDischarged` instantiates the statement; both are close to the
    send step's guard, and the content is in `CommittedLegsAreValidatedDispatches`.
  - Following `claimRefund`'s own hash of the bytes it is given, the bundle it decodes
    and recovers carries no value, or keccak collides on two named preimages
    (`ClaimedBundleValidatedOrCollision`, under the decoder round trip on the run's
    bundles; `PresentedBundleValidatedOrClash` is the coarser form).
- **Distinct dispatches, distinct bundles.** Two dispatches carry different bundles unless
  two different senders used the same salt and keccak collides on their packed preimages
  (`DistinctDispatchesDistinctBundles`; no hash premise). With an encoder that separates
  the run's bundles (`EncInjOn`), their bundle-hash preimages differ
  (`DistinctDispatchesDistinctPreimages`), and their hashes differ or keccak collides on
  those preimages (`DistinctDispatchesDistinctBundleHashes`). Under keccak injectivity on
  the run's own preimages, every bundle hash of a run is unique
  (`LoggedRunBundleHashesUnique`). An atomic dispatch's bytes are never a public
  dispatch's bytes on this chain, except under the same salt clash
  (`AtomicBytesNeverPublished`).

Witnesses: `DispatchWitness`, `StepWitness`, `ClaimWitness`, `EncInjOnSatisfiable`,
`KeccakInjOnSatisfiable`. The clash disjuncts fire in
`SaltClashLetsTwoSendersShareABundle` (indirect calls) and
`CollisionLetsAValueBundleMatchACommittedLeg`.

Model boundaries: one chain, with a ghost log of dispatches. `abi.encode(InteropBundle)`
and keccak are abstract; encoder, decoder and keccak premises are run-local, never global.
A revert is the absence of a step, and a send is one step (`nonReentrant`). The indirect
sender's returned recipient and calldata are free. Reject-only checks are omitted (pause,
destinations, fees and `msg.value`, attribute parsing, the tree insert inside `append`,
the proof checks of `authorizeRefund`/`claimRefund`); omitting them only adds runs. The
three checks the results depend on are switches (`Checks`). Not modelled: fee balances
and claims, asset-router/NTV preparation behind indirect calls, other chains, upgrades
(`OPS-CONFIG`), events. The tree side of `append` is `../../Protocol/InteropAtomicity/`
topic `OncePerLeg`.

- **A claimed bundle is a dispatched bundle (`ClaimBinding`).** `claimRefund(f, x)` hashes
  `abi.encode(bundle.sourceChainId, x)` with `bundle = abi.decode(x)`, the bytes as given.
  Along any run of the deployed code whose decoder inverts the encoder on the run's own
  bundles (`SOL-ABI`), if that leg is not `Unset`, then `x` is the canonical
  `abi.encode(bundle)` of an atomic dispatch of flow `f` in the log and decodes to its
  bundle, or keccak collides on the claim's preimage and the center's preimage for a logged
  atomic dispatch of `f` (`ClaimedBundleIsDispatchedOrCollision`; it uses only
  `onlyInteropCenter`, `ClaimBindingIndependentOfSaltAndValueChecks`). With keccak
  injective on the claim's preimage and the run's bundle-hash preimages, there is no
  disjunct (`ClaimedBundleIsDispatchedOn`). It implies O1's
  `ClaimedBundleValidatedOrCollision` (`ClaimedBundleIsDispatchedImpliesValidated`).
  - Up to the same collision: the decoded source chain is `block.chainid`
    (`ClaimSourceChainIsThisChainOrCollision`); the calls `_recoverBundle` makes (target,
    data, destination chain) are the dispatched bundle's, and the decoded calls are related
    to the dispatch's own starters by `FormsCall` and carry no value
    (`RecoveredCallsAreDispatchedCalls`).
  - The dispatch is unique (`ClaimIdentifiesOneDispatch`, with or without the checks).
    Two successful claims on one run recover two different bundles, unless a claim
    collision or O1 (c)'s cross-sender salt clash (`EachBundleRecoveredAtMostOnce`); with
    keccak injective on the instance's own preimages, always
    (`EachBundleRecoveredAtMostOnceOn`).
  - The canonical bytes always reach the committed leg (`CanonicalBytesReadTheirLeg`);
    any other bytes, such as a re-encoding with a trailing byte, read an `Unset` leg, or
    the collision holds (`NonCanonicalBytesNeverClaim`, `ReencodedBundleNeverClaims`).
  - The headline needs its collision disjunct, the round trip and `onlyInteropCenter`
    (`CollisionLetsAClaimRecoverUndispatchedCalls`,
    `WithoutRoundTripClaimRecoversUndispatchedCalls`,
    `WithoutOnlyInteropCenterClaimRecoversUndispatchedCalls`).
    `EachBundleRecoveredAtMostOnce` needs each of its three break disjuncts
    (`SaltClashLetsOneBundleBeRecoveredTwice`, `ClaimCollisionLetsOneBundleBeRecoveredTwice`),
    the salt check, the round trip and `onlyInteropCenter`
    (`WithoutSaltCheckOneBundleRecoveredTwice`, `WithoutRoundTripOneBundleRecoveredTwice`,
    `WithoutOnlyInteropCenterOneBundleRecoveredTwice`). Both matches of
    `ClaimIdentifiesOneDispatch` are needed (`ClaimIdentifiesOneDispatchNeedsBothMatches`);
    the flow match only because the statement takes no hash premise: that countermodel's
    second run uses O1 (c)'s cross-sender salt clash under a constant keccak.
  - The head form of the headline is `SendAtHead`'s
    `ClaimedBundleIsDispatchedOrCollision` (namespace `Contracts.InteropCenter.SendAtHead`).
  - Witnesses: `ClaimBindingWitness`, `ClaimBindingWithoutValueCheckWitness`,
    `ClaimBindingWithoutSaltCheckWitness`, `ClaimBindingNonCanonicalWitness`,
    `ClaimBindingTwoClaimsWitness`.
  - Pinned at `c67894b9`, like `Dispatch`. At the current heads `claimRefund` hashes
    `keccak256(_bundle)`, `_recoverBundle` dispatches differently, and `_validateAtomicBundle`
    is gone; `Specs/ClaimBinding.lean` lists the differences.

Source findings, reported to the maintainer of this repo, not yet confirmed upstream:
- `sendMessage` parses its attributes with `CallAndBundleAttributes` (:222-225), under
  which `parseAttributes` accepts `atomicBundle` (:843-854), and then hard-codes
  `isAtomic: false` (:246-252). Such a bundle is published to L1 (:657) and never
  appended to the `AtomicFlowManager`. If it is listed as a leg of a flow, the flow can
  never finalize and the other legs become refundable, while this leg stays executable
  through the ordinary path. Both verifiers classified it as a bug, low severity.
- The same behaviour contradicts `interop/IERC7786Attributes.sol:26-30` (the attribute
  appends the bundle to the IMT instead of publishing it). Both verifiers classified it as
  wrong documentation, low severity.

Neither is formalized at the attribute-parsing level in `Dispatch`; in that model such a
bundle is a public dispatch. Topics `AtomicRouting` (at the pin) and `SendAtHead` (at head)
model the attribute: see below.

## SendAtHead: the send path at head

Pinned at era-contracts main `3605e82`; nothing under `l1-contracts/contracts` changed up to
the current main `70096e2ea`. The Specs header maps every cited line to the current
`draft/v0.35.0` head `b17415d20`, where this path differs only by reject-only checks (no pause,
`isPeerAllowed`) and an unmodelled fee-unit counter. Namespace
`Contracts.InteropCenter.SendAtHead`; statements are `Contracts.InteropCenter.SendAtHead.Properties.*`.
The namespace reuses many of the parent's names for the head model, among them `State`,
`Dispatch`, `Params`, `AtomicSend`, `Step`, `Reach`, `init`, `Dispatch.key`, `bundleHash` and
`Inv`, and eighteen of its headline names (for example `EachSaltDispatchesOnce`, `SolePath`,
`AtomicBytesNeverPublished`, `EachLegAppendedOnce`), so refer to them by qualified name when
comparing pin and head results.

At head every L2→L2 send is atomic: `_sendBundle` sends an atomic bundle only to a chain other
than L1 and a non-atomic one only to L1, `_dispatchBundle` publishes exactly the L1 sends and
calls `append` for the others, `_validateAtomicBundle` is gone, and `append` takes the flow
preimage and checks that the bundle is one of its legs. The model adds the ERC-7786 attribute
parser (on decoded attributes), both entry points, the center's L1 messages, and `append`'s
leg-membership and source-chain checks; six checks are switches.

- **The pin's `sendMessage` finding, at the attribute level, and its fix.** The pin's parser
  accepts `atomicBundle` under `sendMessage`'s restriction while the pin's `sendMessage` sends
  non-atomically (`PinSendMessageDroppedAtomicBundle`, on a transcription of the pin's parser that
  agrees with the head's on every decoded list: `PinParserIsHeadParser`). Their content is that
  the pin's parser accepts a list carrying `atomicBundle` and that the two attribute tables are
  equal (`MaskTableIsPinTable`); the pin's `sendMessage` send is a constant with
  `isAtomic = false`. At head every successful
  `sendMessage` carries `atomicBundle`, is atomic, commits its leg and sends nothing to L1
  (`SendMessageAlwaysAtomic`, `PinFindingRejectedAtHead`, `SendMessagesAreAtomicAlongRuns`).
  `_ensureL2ToL2` and `parseAtomicSend` are both load-bearing
  (`WithoutL2ToL2CheckSendMessagePublishes`, `PinConstantMakesSendMessageUnusable`).
- **The `atomicBundle` NatSpec holds in the model** for both entry points
  (`AtomicBundleAttributeMeansAppended`): with the attribute, the leg
  `(keccak(abi.encode(preimage)), bundleHash)` moves from `Unset` to `Committed`, the bundle hash
  is one of the flow's legs declared from this chain, and nothing goes to L1; without it, the send
  goes to L1. The commitment-tree insert is not modelled. The attribute is bundle-level
  (`CallLevelAtomicBundleReverts`). Along runs, appended, atomic and attribute-carrying coincide,
  so no atomic send goes to L1 (`EveryL2SendIsAtomic`), and the L1 messages are exactly the L1
  sends, each a one-call router withdrawal with no call value (`PublishedMessagesAreL1Dispatches`,
  `PublishedMessagesAreWithdrawals`). The gate's atomic half is load-bearing
  (`WithoutAtomicityGateAttributeBundleIsPublished`); its non-atomic half is defense in depth
  behind `append` (`NonAtomicL2SendRevertsInAppend`).
- **Value legs.** The pin's "committed legs carry no value" is false at head
  (`ValueLegCommitsAtHead`). What holds, with no hash premise: every committed leg comes from an
  atomic dispatch of this chain whose value-carrying calls have the sender as `from` and whose
  other calls are zero-value calls from the asset router (`CommittedLegsAreCheckedDispatches`,
  `OnlyADispatchCommitsALeg`). So the base-token refunds `_recoverBundle` would make for a logged
  bundle go to its sender and add up to its call value (`AtomicValueIsRefundedToPayer`), when the
  sender is not the asset router (`RouterSenderValueIsNotRefunded`; the source comment at
  `AtomicFlowManager.sol:301-305` assumes the router never itself initiates a direct send). The
  indirect-call restriction is
  load-bearing (`WithoutIndirectRestrictionRefundMissesPayer`). The bytes `claimRefund` hashes are a
  logged atomic dispatch's encoding, or keccak collides on two named strings
  (`ClaimedBundleIsDispatchedOrCollision`; for bundles `PresentedBundleIsDispatchedOrClash`; both
  disjuncts fire).
- **Salts, legs and distinct dispatches** as at the pin, with the head's bundle-hash preimage
  `abi.encode(bundle)`: `EachSaltDispatchesOnce`, `EachLegAppendedOnce`,
  `DistinctDispatchesDistinctBundles`, `DistinctDispatchesDistinctBundleHashes`,
  `LoggedRunBundleHashesUnique`. An appended bundle is never published to L1, with no clash
  disjunct and whatever the checks (`AtomicBytesNeverPublished`).
- **One flow per bundle hash.** The flow preimage travels outside the bundle, so the bundle hash
  does not name its flow. Two legs that are not `Unset` and share a bundle hash share the flow id,
  or two logged dispatches clash (`BundleHashCommittedUnderOneFlowOrClash`; under run-local
  injectivity `BundleHashCommittedUnderOneFlow`). The salt check is what ensures it: without it one
  bundle is committed under two flows while the run-local hash premises hold
  (`WithoutSaltCheckABundleJoinsTwoFlows`). The clash disjunct fires
  (`BundleHashCollisionJoinsTwoFlows`).

Witnesses: `SendAtHeadWitness`, `SendAtHeadStepWitness`, `SendAtHeadClaimWitness`. The clash and
collision disjuncts fire in `SaltClashLetsTwoSendersShareABundle`, `BundleHashClashFiresAlone`,
`CollisionLetsForeignBytesMatchACommittedLeg`, `CollisionLetsAForeignBundleMatchACommittedLeg` and
`BundleHashCollisionJoinsTwoFlows`. Countermodels: `WithoutSaltCheckABundleRepeats`,
`WithoutOnlyInteropCenterUnbackedLegCommits` and those above.

Model boundaries: as for `Dispatch`, one chain with a ghost log, abstract `abi.encode` and keccak
with run-local premises only, a revert as the absence of a step and a send as one step. Unlike
`Dispatch`, attribute parsing and the destination checks are modelled; attributes are decoded
values (malformed payloads and ERC-7930 addresses only reject). The manager's own `L1_CHAIN_ID` is
read only by omitted checks. `authorizeRefund` moves one leg per step, without its proof checks,
and `claimRefund` does not run `_recoverBundle`. `baseTokenRefunds` transcribes `_recoverBundle`'s
base-token branch for a logged bundle; the router's `recoverAtomicCall` is not modelled, and neither
is the payment of call value, fees, or the router's `indirectCallMessageValue`.

## AtomicRouting

Namespace `Contracts.InteropCenter.AtomicRouting` (`c67894b9`). It composes this chain's
center and manager (`Dispatch`'s state), a ghost log of each send's entry point and
`atomicBundle` attribute, the source chain's code map and world for the refund loop
(`AtomicFlowManager` topic `RecoveryTargets`), and every destination's `bundleStatus`.
`pin` is the pinned code; `upgradeTree` adds the two checks of `e561b9cc2` (also at the
current heads) that decide where the attribute goes: `sendMessage` passes the attribute on,
and an atomic send must not go to L1.

- **Routing.** A logged send is atomic exactly when it carried the attribute and came
  through `sendBundle`, or through `sendMessage` where `sendMessage` honours it
  (`AttributeRoutingByEntryPoint`; no hash premise). The `sendMessage` finding above is
  `SendMessageAtomicMisrouted`: a pinned run in which a `sendMessage` carrying a flow's
  attribute is executed at its destination through `executeBundle` while the flow's other
  leg is refunded on the source.
- **An atomic leg to L1 at the pin** (the case recorded in `../AssetRouterBase/README.md`).
  Its one call targets the router's `L1_ASSET_ROUTER` (`AtomicL1BundleCarriesL1RouterTarget`).
  L1's `bundleStatus` of the leg stays `Unreceived` (`AtomicToL1NeverExecuted`), every claim
  of its bytes reverts when no recoverer is deployed at that address on the L2
  (`AtomicToL1ClaimReverts`), and together the leg is neither received on L1 nor `Reverted`
  in any reachable state (`AtomicToL1Stranded`), each up to a pinned keccak collision on
  logged preimages or `CrossSenderSaltClash`. Premises: `VmCall`, no recoverer at the L1
  router's address on the L2, the publication premise `CenterPublishesOnlyPublicDispatches`
  (`PROTO-EVIDENCE`) and the run-local decoding premise `DecodesRunBundles` (`SOL-ABI`).
  Both environment premises are needed: with an inclusion verdict that accepts the leg's
  bytes L1 executes it (`AtomicToL1StrandedNeedsPublicationPremise`), and with code at the
  L1 router's address that returns `true` the leg is claimed and `Reverted`
  (`AtomicToL1StrandedNeedsNoRecoverer`), with no collision in either run.
- **Targets on the source chain.** A router call in a send to an L2 targets
  `L2_ASSET_ROUTER_ADDR`, the source chain's own router (`IndirectL2RouterLegsReachSourceRouter`).
  An atomic leg with a call whose target has no recoverer on the source chain is not
  `Reverted`, up to a pinned collision with a logged claim (`NonRecovererLegNeverRefunded`).
- **The other tree's checks.** Under `upgradeTree` every send is atomic exactly when it
  carried the attribute, and no atomic send goes to L1 (`AttributeHonouredOrRejected`,
  `GuardKeepsAtomicLegsOffL1`); at the pin both fail (`PinBreaksAttributeHonoured`).

Witnesses: `AtomicToL1StrandedWitness` (every premise of the L1 results, the leg
`Revertable`, a public withdrawal executed on L1, every collision disjunct false),
`NonRecovererLegNeverRefundedWitness`, `IndirectL2RouterLegsReachSourceRouterWitness`,
`AttributeRoutingByEntryPointWitness`, `AttributeHonouredOrRejectedWitness` (whose run also
meets the premises of `GuardKeepsAtomicLegsOffL1`). Model boundaries: `MODEL-ATOMIC-ROUTING`
in `../../../ASSUMPTIONS.md`. In particular one `L1_CHAIN_ID` serves the center and the
router, `authorize` abstracts the absence proof and is read only by the witnesses, token
balances are not modelled, and that L1 credits a withdrawal only by executing or unbundling
its bundle is argued from source in the Specs header.

## Fee state at draft/v0.35.0 (`b17415d20`)

Topics `FeeState` (namespace `Contracts.InteropCenter.FeeState`) and `FeeReentry` (namespace
`Contracts.InteropCenter.FeeState.Reentry`) model the center's balances, fee ledgers, fee
parameters and the `INTEROP_FEE_UNITS_SLOT` counter at the draft/v0.35.0 head, with every entry
point, a direct `AtomicFlowManager.append` attempt and forced inflows (`MODEL-FEE-STATE`,
`MODEL-FEE-REENTRY`).

- **Backing.** With the `msg.value` equalities (:433-434, :442-443) the native balance is exactly
  the accrued protocol fees plus the forced value (`NativeBalanceIsFeesPlusForced`,
  `ProtocolFeesBacked`); under the standard-token premise the ZK fees are backed by the cached ZK
  token's balance (`ZkFeesBacked`); no transaction shrinks either excess (`BackingNeverShrinks`).
  Without the equalities a withdrawal's forwarded value comes out of a coinbase's accrued fees
  (`WithoutValueCheckFeesFundAWithdrawal`); a token that credits less breaks the ZK backing
  (`NonStandardZkTokenUnbacked`).
- **Nested calls.** With the equalities, the backing survives arbitrary calls nested in the
  forwards, deposits and claim receivers, provided either `claimProtocolFees` writes before it pays
  (the deployed order) or the claims hold the lock (`NestedBackingNeverShrinks`,
  `NestedProtocolFeesBacked`, `NestedZkFeesBacked`); so the claims' `nonReentrant` is not what keeps
  the fees backed. With neither, a re-entering receiver is paid twice
  (`NoLockNoWriteFirstDrainsFees`). A `FeeState` transaction is exactly the corresponding call with
  no nested calls (`FlatIsNestedWithoutCalls`).
- **One send, one claim.** A send adds exactly its protocol fee, credited to the coinbase alone,
  and on the fixed-fee path exactly `ZK_INTEROP_FEE * calls` to the ZK balance and the coinbase's
  ZK entry (`SendAccruesExactProtocolFee`, `SendAccruesExactZkFee`); its payments are the forwards
  to the asset router (`Σ indirectCallMessageValue`) and one burn (same base token;
  the holder's `burnAndStartBridging` by construction, the burn's recipient not being a modelled
  field) or one value-free deposit request (different base token) of exactly the direct calls'
  value (`SendPaymentsExact`). A claim pays exactly the claimant's entry and zeroes it
  (`ClaimProtocolFeesExact`, `ClaimZkFeesExact`).
- **Writers.** `interopProtocolFee` only by the bootloader; the `initL2` fields only by the
  upgrader's single `initL2`, which precedes every send and claim; `zkToken` only from unset;
  `_paused` never; the owner has no power over the fee state (`ProtocolFeeSetOnlyByBootloader`,
  `InitFieldsOnlyByInitL2`, `InitL2AtMostOnceAndFirst`, `ZkTokenSetOnce`, `PausedNeverWritten`,
  `OwnerHasNoFeePower`).
- **Fee units.** Each transaction moves the counter by exactly its L2→L2 call count
  (`FeeUnitsDeltaExact`); with `onlyInteropCenter` every IMT leaf is appended in a step that adds
  its bundle's call count, and along any run the counter grows by the L2→L2 sends' call count
  (`EveryLeafCounted`, `FeeUnitsAreL2Calls`). A zero-call bundle appends a leaf and adds nothing
  (`ZeroCallBundleAddsLeafNoUnits`, as `protocol-docs/interop-fee.md:9-10` says); without the
  `append` gate a leaf with calls is uncounted (`WithoutOnlyInteropCenterUncountedLeaf`). The slot
  is separate from the fixed slots (`FeeUnitsSlotSeparate`).

Witnesses: `FeeStateWitness`, `SendWitness`, `ClaimWitness`, `WriterWitness`, `OwnershipWitness`,
`NestedClaimInsideSendWitness` (write-first disjunct), `PayFirstClaimLockNestedWitness` (claims'
lock disjunct).

Model boundaries: one chain; ERC-7930 and attribute parsing, destination and peer checks, the salt
check, `append`'s own checks, the token side of deposits and the ZK allowance, and overflow of the
fee products are omitted (reject-only). The counter is its own field; that no mapping slot equals
`INTEROP_FEE_UNITS_SLOT` is a keccak premise not stated. main `70096e2ea` differs: it has
`pause()`/`unpause()` (`onlyOwner`), `whenNotPaused` on the sends, and no fee-unit counter.
