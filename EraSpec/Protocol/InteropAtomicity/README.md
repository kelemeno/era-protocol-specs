# Interop atomicity across chains and batches

Sources: `contracts/atomic-interop/AtomicFlowManager.sol` (`requireFlowFinalized`,
`_checkFlowId`, `authorizeRefund`, `claimRefund`),
`contracts/atomic-interop/libraries/AtomicInteropProof.sol`
(`verifyTimeoutAbsence`, `_verifyLastBatchInRoot`, `_authenticateRoot`),
`contracts/interop/L2MessageVerification.sol` and
`contracts/interop/L2InteropRootStorage.sol` in the pinned era-contracts tree.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Atomicity | [Specs/Atomicity.lean](Specs/Atomicity.lean) | [Properties/Atomicity.lean](Properties/Atomicity.lean) | [Proofs/Atomicity.lean](Proofs/Atomicity.lean) |
| Timeout | [Specs/Timeout.lean](Specs/Timeout.lean) | [Properties/Timeout.lean](Properties/Timeout.lean) | [Proofs/Timeout.lean](Proofs/Timeout.lean) |
| Refund | [Specs/Refund.lean](Specs/Refund.lean) | [Properties/Refund.lean](Properties/Refund.lean) | [Proofs/Refund.lean](Proofs/Refund.lean) |
| RefundStrong | [Specs/RefundStrong.lean](Specs/RefundStrong.lean) | [Properties/RefundStrong.lean](Properties/RefundStrong.lean) | [Proofs/RefundStrong.lean](Proofs/RefundStrong.lean) |
| SourceHeight | [Specs/SourceHeight.lean](Specs/SourceHeight.lean) | [Properties/SourceHeight.lean](Properties/SourceHeight.lean) | [Proofs/SourceHeight.lean](Proofs/SourceHeight.lean) |
| FlowBinding | [Specs/FlowBinding.lean](Specs/FlowBinding.lean) | [Properties/FlowBinding.lean](Properties/FlowBinding.lean) | [Proofs/FlowBinding.lean](Proofs/FlowBinding.lean) |
| OncePerLeg | [Specs/OncePerLeg.lean](Specs/OncePerLeg.lean) | [Properties/OncePerLeg.lean](Properties/OncePerLeg.lean) | [Proofs/OncePerLeg.lean](Proofs/OncePerLeg.lean) |
| RootImport | [Specs/RootImport.lean](Specs/RootImport.lean) | [Properties/RootImport.lean](Properties/RootImport.lean) | [Proofs/RootImport.lean](Proofs/RootImport.lean) |
| Pause | [Specs/Pause.lean](Specs/Pause.lean) | [Properties/Pause.lean](Properties/Pause.lean) | [Proofs/Pause.lean](Proofs/Pause.lean) |
| SharedCommitment | [Specs/SharedCommitment.lean](Specs/SharedCommitment.lean) | [Properties/SharedCommitment.lean](Properties/SharedCommitment.lean) | [Proofs/SharedCommitment.lean](Proofs/SharedCommitment.lean) |
| Operational | [Specs/Operational.lean](Specs/Operational.lean) | [Properties/Operational.lean](Properties/Operational.lean) | [Proofs/Operational.lean](Proofs/Operational.lean) |
| RefundFaithful | [Specs/RefundFaithful.lean](Specs/RefundFaithful.lean) | [Properties/RefundFaithful.lean](Properties/RefundFaithful.lean) | [Proofs/RefundFaithful.lean](Proofs/RefundFaithful.lean) |
| BatchPosition | [Specs/BatchPosition.lean](Specs/BatchPosition.lean) | [Properties/BatchPosition.lean](Properties/BatchPosition.lean) | [Proofs/BatchPosition.lean](Proofs/BatchPosition.lean) |
| LegSourceFilterAtV35 | [Specs/LegSourceFilterAtV35.lean](Specs/LegSourceFilterAtV35.lean) | [Properties/LegSourceFilterAtV35.lean](Properties/LegSourceFilterAtV35.lean) | [Proofs/LegSourceFilterAtV35.lean](Proofs/LegSourceFilterAtV35.lean) |
| FlowBindingAtHead (`3605e82`) | [Specs/FlowBindingAtHead.lean](Specs/FlowBindingAtHead.lean) | [Properties/FlowBindingAtHead.lean](Properties/FlowBindingAtHead.lean) | [Proofs/FlowBindingAtHead.lean](Proofs/FlowBindingAtHead.lean) |
| OncePerLegAtHead (`main` `70096e2`, `draft/v0.35.0` `b17415d`) | [Specs/OncePerLegAtHead.lean](Specs/OncePerLegAtHead.lean) | [Properties/OncePerLegAtHead.lean](Properties/OncePerLegAtHead.lean) | [Proofs/OncePerLegAtHead.lean](Proofs/OncePerLegAtHead.lean) |
| SettlementRoots | [Specs/SettlementRoots.lean](Specs/SettlementRoots.lean) | [Properties/SettlementRoots.lean](Properties/SettlementRoots.lean) | [Proofs/SettlementRoots.lean](Proofs/SettlementRoots.lean) |
| DispatchLiveness | [Specs/DispatchLiveness.lean](Specs/DispatchLiveness.lean) | [Properties/DispatchLiveness.lean](Properties/DispatchLiveness.lean) | [Proofs/DispatchLiveness.lean](Proofs/DispatchLiveness.lean) |
| ExecutionLiveness | [Specs/ExecutionLiveness.lean](Specs/ExecutionLiveness.lean) | [Properties/ExecutionLiveness.lean](Properties/ExecutionLiveness.lean) | [Proofs/ExecutionLiveness.lean](Proofs/ExecutionLiveness.lean) |

Read them in that order; each builds on earlier ones (`FlowBinding` and `OncePerLeg` on
`Refund`, `RootImport` on `Atomicity`, `Timeout`, `SourceHeight` and `FlowBinding`;
`Pause` on `FlowBinding` and `OncePerLeg`, `SharedCommitment` on `OncePerLeg`,
`Operational` on `OncePerLeg`, `FlowBinding` and `SourceHeight`, `RefundFaithful` on
`Refund` and `Timeout`, `BatchPosition` on `Timeout` and `Refund`, `LegSourceFilterAtV35` on
`FlowBinding` and `OncePerLeg`, `FlowBindingAtHead` on `FlowBinding`, `OncePerLeg` and
`AtomicFlowManager` `FlowCanonicalAtHead`, `OncePerLegAtHead` on `OncePerLeg` and
`L2InteropCommitmentTree` `HintSearchAtHead`, `SettlementRoots` on `Refund`, `Operational`
and the `MessageRoot` and `L2InteropRootStorage` contract models, `DispatchLiveness` on
`OncePerLeg` and `../../Contracts/InteropCenter/`, and `ExecutionLiveness` on `Refund`,
`RootImport` (its witness history) and the handler topics of
`../../Contracts/InteropHandlerBase/`).
The exception is `RefundStrong`, which also takes `AggregatesBefore` from the later
`Operational` topic ([Specs/Operational.lean](Specs/Operational.lean)).
Every topic models the pinned tree except `LegSourceFilterAtV35`, which adds the receive
filter of `draft/v0.35.0` (`b17415d20`) to the `FlowBinding` and `OncePerLeg` models, and
`FlowBindingAtHead` and `OncePerLegAtHead`, which model later era-contracts heads (see their
sections below).

`SourceHeight` derives `Wf.capacity` instead of assuming it: a system built from
per-chain runs that carry `FullMerkle._height` (`systemOfRuns`, `RunsWf`) is `Wf`
(`WfOfRuns`), its heights are the source's (`RunsHeightsFromSource`), and every `Wf`
system with source heights is so built (`WfSourceHeightsFromRuns`).
`NoneOrAllOrBreakPinnedFromRuns` is the pinned partial-atomicity result over such
systems. `PaddedSystemFromRuns` / `MixedSystemFromRuns` show the countermodel systems'
heights are the ones the source computes. The batch-root tree's `capacity` field in
`Specs/Timeout.lean` is a different tree and is not covered.

> **Caveat.** Most results here take a premise proved unsatisfiable:
> `HashAssumptions` (`HashAssumptionsUnsatisfiable`), `FlowHashInj`
> (`FlowHashInjUnsatisfiable`), `CommitValueInj` (`CommitValueInjUnsatisfiable`) or
> a global pair-injective `hinj` (`not_nodeInj`). Those results, including every
> headline (`NoneOrAll`, `ExecutedExcludesAnyRefund`, `FlowIdCheckPinsLegList`,
> `ExecutedObligationNeverRefunded`, `TimeoutMeansMissedDeadline`) and the
> countermodels `FullGateBlocksMixedOutcome` and `WithoutDaCommittedLegIsStuck`, are
> vacuous as stated; the full list is in `ASSUMPTIONS.md`. What stands: the
> countermodels `SelfOnlyGateAdmitsMixedOutcome`, `SubsetFlowPassesUncheckedGate`
> and `StaleRootRefundsDeliveredLeg` (they never needed a hash premise and no longer
> take one), the pinned `CrossFlowIdClashIsPinnedCollision`, and the premise-free
> structural results. `CrossFlowRefundYieldsCollision` and
> `SharedCommitmentYieldsCollision` take no premise but end in an unpinned "some
> collision exists", which is always true (`UnpinnedCollisionsAlwaysExist`).
> `SharedCommitmentYieldsCollision` has a run-level restatement with content in
> `SharedCommitment`.
> `ExecutedImpliesRealFlowFinalizable` now has a logged-clash form
> (`ExecutedImpliesRealFlowFinalizableOrLoggedClash`, `FlowBinding`), and
> `CommitmentPinsLegOn`'s premise is discharged on a run's own append log
> (`RunRefutesLoggedCommitClash`, `CommitmentPinsLoggedLeg`, `OncePerLeg`).
> `FlowIdCheckPinsLegList` and `SubsetFlowRejectedByCheck` have no restatement of their
> own with protocol content (`ASSUMPTIONS.md`); the flow-id check's content is the
> `FlowBinding` result.
> Every headline now has a repaired `…OrBreak` form with no hash premise: the
> property holds, or a break is located on a named submitted proof (a leg's gate
> proof, the refund's absence proof, the last-batch path on the END branch, or a
> logged call's flow-id preimage). Each has a witness where every break is false and
> one where a forged padding proof is located. See `ASSUMPTIONS.md` ("Repaired forms
> that stand").

- **Atomicity.** The gate requires an inclusion proof for every leg. If any leg of a
  flow executes, every leg is finalizable and no leg can be refunded on either
  timeout branch (`NoneOrAll`, `ExecutedExcludesAnyRefund`). "Finalizable" here
  (`FlowFinalizableBy`) is the IMT half only: a presentable IMT proof accepted against
  the true END root. Whether a given destination can pass its gate is `RootImport`. The flow-id
  recomputation is meant to pin the leg list (`FlowIdCheckPinsLegList`, vacuous via
  `FlowHashInj`). Countermodels: a
  self-only gate admits a mixed outcome, a subset flow passes a gate without the
  id check, and without data availability a committed leg is stuck.
- **Timeout.** The "last batch that settled by the deadline" fact is derived from
  the three comparisons and the last-batch proof (`IsLastOnTimeDerived`,
  `TimeoutMeansMissedDeadline`), under the settlement layer's `Aggregates`
  invariant. `StaleRootRefundsDeliveredLeg` shows that invariant is load-bearing,
  so real-path claims inherit it. The last-batch proof is modelled with the walk's
  length taken to be the chain tree's height and the batch an occupied leaf, which the
  deployed verifier does not check (`LastLeafFaithful`), and chain-tree leaf `i` is read
  as batch `i` (first pushed batch 0 and `PROTO-CONTIGUOUS-PUSH`): see the Correction
  notes in `Specs/Timeout.lean` (`LastBatchAccepted`, `RootBacking`). The halted-chain
  END branch is composed into the reference bridge in `../../Examples/BurnMintBridge/`
  (topic `EndBranch`). `BatchPosition` is the END branch without the leaf-`i`-is-batch-`i`
  reading.
- **BatchPosition** (namespace `Contracts.BatchPosition`). The END branch with the
  chain-tree leaf position and the batch number kept apart. `Timeout`'s `RootBacking` reads
  leaf `i` as batch `i`, which needs first pushed batch 0 and `PROTO-CONTIGUOUS-PUSH`;
  `AttackVectors.LastBatchInRootOffset` keeps the two apart by taking `B = batchAt f p` as a
  premise. Here the batch number is read from the submitted leaf preimage
  `(batchRoot, N, timestamp)`, which `batchLeafHash` binds, so no contiguity is assumed.
  `ChainTreeStep` models `MessageRootBase`'s numbering and push writers at `c67894b9`
  (record only, record and push, migrate, seed genesis); on every reachable tree batch
  numbers strictly increase (`ReachableSlotNumbersIncrease`). A genesis-seeded ZKsync OS
  chain (by round 7's trace, every atomic-interop source chain at the pin) is
  identity-numbered until a Gateway round trip; after one, no first-batch offset makes its
  tree contiguous, and any
  three-leaf `RootBacking` reads the root's last batch as `2` (`RoundTripBreaksContiguity`). Chains
  registered at a nonzero batch or without a genesis leaf are never identity-numbered
  (`TreePositionBelowBatchNumber`, `CurrentCompositionCannotRepresentOnboardingAt100`); at
  the pin their L1 trees are not an atomic-interop source's (EraVM chains get no atomic
  built-ins, and round 7 traces every source chain to `createNewChain`). On the identity
  numbering the old backing is the new one (`IdentityNumberedBackingIsOldBacking`, premises
  instantiated by `IdentityNumberedBackingWitness`; `IdentityNumberingNeedsGenesis`).
  With no hash premise, an accepted last-batch proof makes the submitted preimage the tree's
  last entry, so `N = R.upTo c` and the compared timestamp is the leaf's, or a
  `PositionedEndBreak` is located on the submission: a `PinnedBreak`, a `PathCollision`, or a
  `LeafPreimageClash` between the stored entry and the submitted preimage
  (`PositionedLastBatchIdentifiesLastEntryPinned`, `PositionedEndBranchImpliesVerifiedPinned`).
  Its `AggregatesBefore` premise has the same body as `Contracts.InteropOperational.AggregatesBefore`,
  which `SettlementRoots` discharges for MessageRoot-clocked systems
  (`HistoricalRootAggregatesBefore`).
  Headlines: `PositionedTimeoutMeansMissedDeadlineOrBreak`,
  `PositionedTimeoutExcludesFinalityOrBreak`, `PushLogTimeoutMeansMissedDeadlineOrBreak`
  (premises about the batches actually pushed), and the counterparts of `Refund`'s repaired
  accepted-gate results, `PositionedTimeoutAuthorizesPinned` and
  `PositionedExecutedExcludesRefundOrBreak` (no leg of an executed flow passes the positioned
  gate, or a break is located). The `…On` forms collapse the break under injectivity restricted to this
  tree's pairs, the submitted path and the entries plus the submitted preimage
  (`NoPositionedEndBreakOn`). The settlement-layer premise is the strict `AggregatesBefore`
  (`AggregatesImpliesBefore`, `AggregatesBeforeIsWeaker`), derived from the push log
  (`AggregatesBeforeFromPushLog`) under the explicit `GapsAfterRootLate` for batches after the
  root's last entry that never reached this layer. Witnesses on the round-trip tree, every
  break false: `RoundTripTimeoutWitness` (a leg committed after the deadline; it also
  instantiates the finality and authorization forms) and
  `RoundTripExecutedExcludesRefundWitness` (an executed leg; the last-batch check passes at
  the last entry and the gate fails). Others: `OnboardedTimeoutWitness` (every starting
  batch), `OnboardedAt100Composes`, `EraVmNoGenesisComposes`, `MigrationGapInsideTreeWitness`,
  `PositionedConclusionNotAlways`. Countermodels: `BatchNumberForgeryLocatesLeafClash` (a leaf
  hash that does not bind the batch number refunds a delivered leg; the located break is the
  `LeafPreimageClash`) and `MigrationGapIsLoadBearing` (the model's composition needs
  `GapsAfterRootLate`).
  Not modelled: the link from the submitted batch root to the IMT the absence check runs
  against, the shared tree and the import of the root. As in `Timeout`, the walk's length is
  the tree's height and the mask an occupied position (`LastLeafFaithful`);
  `MaskBoundGivesOccupiedRange` relates the occupied range to the mask bound the contract
  checks. Open: `Operational` and the `BurnMintBridge` `EndBranch` topic still take
  `RootBacking`, so they cover the identity numbering only; their positioned restatements are
  not written.
- **Refund.** One outcome per obligation over every interleaving of every chain's
  manager calls (`ExecutedObligationNeverRefunded`). A cross-flow refund yields a
  collision of the flow-id hash on the two flows' own preimages
  (`CrossFlowIdClashIsPinnedCollision`).
- **RefundStrong** (namespace `Contracts.Refund`). Completeness of the refund side, with
  no hash premise. It builds on `Refund` and `Timeout`, and takes one definition,
  `AggregatesBefore`, from [Specs/Operational.lean](Specs/Operational.lean), which itself
  builds on `SourceHeight`, `FlowBinding` and `OncePerLeg`. Two gates are in play, and
  each result names its own.
  - *The loose gate* `LegRefundableBy` resolves against no root and may cite any batch of
    the fixed history; `ReachLog` uses it. On a well-formed history it accepts a break-free
    proof for a leg with nonzero commit value exactly when the leg missed its deadline and
    the history has a batch of its chain after the deadline
    (`RefundableIffMissedDeadline`); the honest low-leaf proof at the first late batch does
    it and is presentable under data availability
    (`MissedDeadlineRefundableByHonestProof`). Neither result is about
    `verifyTimeoutAbsence`, which can cite only a batch inside an imported root.
  - *The gate as the contract runs it* is `LegRefundableAcceptedBy` with the submitted
    batch inside the imported root (`N ≤ R.upTo`; `_authenticateRoot` requires it on both
    branches). From any imported root created after the deadline, a leg that missed its
    deadline has an accepted, break-free submission inside that root, with no aggregation
    premise (`AcceptedGateCompleteFromAnyPostDeadlineRoot`). The source's case split is in
    the statement of `AcceptedGateCompleteByHonestProofs`: if the root's last batch of the
    chain is late, the honest BEGIN proof at the first late batch, which lies inside the
    root; otherwise the honest END proofs at the root's last batch (alone:
    `EndBranchAcceptsHonestProofs`). There both IMT proofs are presentable under data
    availability. With the strict `AggregatesBefore` a break-free submission inside the root
    exists exactly when the leg missed its deadline (`AcceptedGateIffMissedDeadline`). As in
    `Timeout`, the END branch's last-batch check is `LastBatchAccepted`, stronger than the
    deployed one (`LastLeafFaithful`), "inside the root" reads leaf position as batch number
    (`PROTO-CONTIGUOUS-PUSH`), and the BEGIN tree of batch `n + 1` is the END tree of batch
    `n` by definition (`PROTO-BATCH-SNAPSHOT`). The witnesses of these gate-as-run results
    use a chain that has committed a value, so the tree the absence proof is checked against
    is not the empty `setup`.
  - *In the fixed-history model*, at every manager state, each still `Committed` leg of a
    checked flow with a stranded leg can be authorized by a verified call on a break-free
    proof and then claimed (`StrandedFlowCommittedLegRefundable`). This is enabledness in a
    model that admits more refunds than the contract (the loose gate with no root, no
    pause, `claimRefund` as its leg-state guard, no prover access), so it is not a liveness
    claim about the contracts. The statement against a recorded root is
    `OpTimedOutLegIsRefundable` (`Operational`); `PausedVaultKeepsLegRevertable` (`Pause`)
    and `LegNeverRefunded` (`AssetRouterBase`, topic `AtomicRecovery`) show claims that do
    not go through.
  - *At run level*, an obligation is past `Committed` exactly when a logged call marked it
    (`RefundedIffLoggedMark`), and a `RefundBreak` implies a refund
    (`RefundBreakImpliesRefunded`). `CrossFlowRefundYieldsLoggedPinnedClash` is a corollary
    of `RefundNeedsLoggedAuthorize` and `CrossFlowIdClashIsPinnedCollision`: a refund under
    a checked flow's id that no logged call made for that flow was made by a logged call
    whose flow clashes with it. The flow itself need not occur in the run. Its witness is a
    refund that does cross flows: under a constant flow hash, a leg delivered through a
    truncated flow is refunded on the full flow's timeout.
  - `ExecutedObligationLiveAndUnmarkableUnderSealedHash` exhibits, under a toy hash pair
    (`sealedNodeHash`, `sealedLeafHash`, not a model of keccak), an executed obligation
    that is appended and `Committed`, with a logged flow-id clash in the run, that no
    verified `authorizeRefund` call can mark. The flow-id check and the timeout gate do
    that together; the cross-flow witness shows the timeout gate alone does not.
- **FlowBinding** (namespace `Contracts.FlowBinding`). `RunLog` is `ReachLog` plus a
  logged `requireFlowFinalized` step, so the log holds every call that runs
  `_checkFlowId`. With no hash premise, every logged flow claiming an executed flow's id
  is all finalizable, or the execution's gate proof carries a break on the first stranded
  leg, or the two logged flows clash on the flow-id hash
  (`ExecutedImpliesRealFlowFinalizableOrLoggedClash`; per leg
  `ExecutedImpliesRealFlowLegFinalizableOrLoggedClash`).
  `LoggedExecutionExcludesLoggedRefundOrBreak` is delivered-xor-refunded at call level.
  Given the premises the clash disjunct is equivalent to the two flows differing; the gain
  is that both flows come from the run's own log. `SubsetFlowAttackLandsInLoggedClash`,
  `ForgedSiblingProofLandsInPinnedBreak` and `PaddingRefundLandsInAbsenceBreak` each fire
  one disjunct alone; on `ExecutedImpliesRealFlowFinalizableOrLoggedClashWitness` there is
  no break and no clash.
  `RunLogAuthCallsReachLog` and `ReachLogEmbedsInRunLog` carry every `Refund` result over.
- **OncePerLeg** (namespace `Contracts.AppendPath`). One chain's manager and commitment
  tree in one state, so one `append` is one step of both (`Steps`), and every chain at
  once with `Refund`'s verified `authorizeRefund` (`SysSteps`). With no hash premise and
  no premise on the commit value, on every run from genesis: each obligation is appended
  at most once, occupies exactly one index of its chain's tree, and two appended
  obligations on one chain with one commit value are equal (`OncePerLeg`,
  `SystemOncePerLeg`). A commit-value clash can only block a later leg's `append`, never
  create a second key (`AppendBlockedOnlyByClash`, `ClashBlocksFreshLeg`); without
  `IMTValueAlreadyExists` one value sits at two indices
  (`WithoutDedupClashOccupiesTwoIndices`). On reachable states the manager's
  `ManagerLegAlreadyCommitted` check is implied by the tree's
  (`TreeGateImpliesManagerGate`); the two disagree exactly on a logged clash
  (`GatesDisagreeOnlyOnLoggedClash`). The system's managers are a `ReachLog` run
  (`SystemProjectsToReachLog`), so the refund milestones hold with trees attached
  (`SystemExecutedObligationNeverRefundedOrBreak`, `SystemRefundedWasAppendedOnce`).
  Witnesses: `OncePerLegWitness`, `NoSecondAppendWitness`, `SystemWitness`. Obligations on
  different chains may clash harmlessly; that `bundleHash` embeds `block.chainid` is not
  modelled.
- **FlowBindingAtHead** (namespace `Contracts.FlowBindingAtHead`, source `main` `3605e82`;
  `main` at `70096e2` changes no contract since). At the pin `append` took an opaque
  `flowId`; at `3605e82` it takes the preimage, recomputes the id, and requires the bundle
  to be a leg declared on `block.chainid` (`AtomicFlowManager.sol:103-172`). `RunAtHead`
  interleaves every chain's head `append` (manager and tree in one step, with every check
  in source order), `requireFlowFinalized`, `authorizeRefund`, `claimRefund` and the tree's
  `initL2`, and logs every call that takes a preimage. Unlike the pin's `ReachLog`,
  `authorizeRefund` marks the leg in the manager of the chain that runs the call, as the
  code does. No result takes a global injectivity premise; the `…On` forms take
  injectivity on the run's own logged preimages.
  - The flow a leg was committed under is now on the log: every leg that is not `Unset`
    was committed by exactly one logged `append`, whose preimage hashes to its id, passes
    `_checkFlowId`, and declares the leg on the committing chain
    (`CommittedLegHasLoggedPreimage`, `UnsetIffNotAppended`, `LoggedCallsPassedTheirChecks`).
  - The declared source chain is the committing chain, or two logged preimages clash
    (`DeclaredSourceIsCommittingChainOrLoggedClash`,
    `SameKeyAppendedOnTwoChainsIsLoggedClash`, `AuthorizeMarksDeclaredLegOrLoggedClash`,
    `KeyIsDeclaredOnItsChainOrLoggedClash`). `SystemOncePerLegAtHead` is
    `SystemOncePerLeg` without its "on one chain" premise.
  - The `FlowBinding` headlines now range over the committed-under flow instead of a flow
    some later call presented (`ExecutedImpliesCommittedFlowFinalizableOrLoggedClash`, per
    leg `ExecutedImpliesCommittedLegFinalizableOrLoggedClash`,
    `LoggedExecutionExcludesLoggedRefundOrBreakAtHead`,
    `ExecutionFreezesItsFlowOrLoggedBreakAtHead`, `RefundedLegWasAuthorizedOnItsChain`).
    With the preimage hash injective on the run's logged preimages the clash disjuncts go
    (`DeclaredSourceIsCommittingChainOn`, `ExecutedImpliesCommittedFlowFinalizableOn`;
    `NoLoggedClashIffInjOn` ties that premise to `LoggedPreimageClash`).
  - Each chain of a head run is a pin `Steps` run (`RunAtHeadProjectsToChainRuns`), so the
    one-chain `OncePerLeg` results hold at head (`OncePerLegAtHead`). The unbounded low-leaf
    walk lands where a pin insert lands (`HeadInsertLandsWherePinInsertLands`) but accepts
    hints the five-hop walk rejects (`HeadWalkAcceptsHintPinRejects`). A checked head flow
    is a checked pin flow for the induced hash (`HeadCheckIsPinCheck`,
    `PinClashIsPreimageClash`, `PinLegIffDeclares`).
  - What the pin allowed and head rejects. In the pin's own model, a leg committed under an
    id that no refund authorization's flow lists it under stays `Committed`
    (`PinUnboundLegIsStrandedLogged`; `PinUnboundLegIsStranded` is the form over every
    checked flow; `PinUnboundLegWitness` meets both forms' premises on a run that refunds a
    sibling). At head `append` rejects a leg its preimage does not declare on the calling
    chain (`AppendRejectsUndeclaredLeg`, `PinUnboundLegRejectedAtHead`), and in the model a
    committed leg can always be marked `Revertable` through the flow it was committed
    under, given a verified timeout of one of its legs (`CommittedLegRefundableOnTimeout`).
    That last result is enabledness of the modelled checks only: the root-authentication
    and imported-root checks of `verifyTimeoutAbsence` are omitted.
  - `draft/v0.35.0` (`b17415d20`; `d9f6789` has the same text in these files): `append`,
    `_validateAndComputeFlowId` and `IndexedMerkleTree.insert` are unchanged, and
    `requireFlowFinalized` and `authorizeRefund` add the reject-only
    `_checkLegSourceAllowed` (`AtomicFlowManager.sol:338-344` at that commit), modelled in
    `RunAtV35`. Its runs project to `RunAtHead` runs between the same states
    (`RunAtV35ProjectsToRunAtHead`), so every result above holds there;
    `CommittedLegRefundableOnTimeoutAtV35` is the enabledness result with the extra
    premise that the timed-out leg's chain passes that check on the refunding chain.
  - Witnesses: `FlowBindingAtHeadWitness` (an honest run using every call, no clash, no
    break, and the headline's same-id premise load-bearing),
    `SubsetFlowAttackAtHeadLandsInLoggedClash` (only the clash disjunct holds),
    `SameKeyOnTwoChainsWitness`, `PinUnboundLegWitness`, `PinUnboundLegRejectedAtHeadWitness`,
    `AppendRejectsUndeclaredLegWitness`, `CommittedLegRefundableOnTimeoutWitness`,
    `RunAtV35Witness`, `CommittedLegRefundableOnTimeoutAtV35Witness` (the timed-out leg on
    another chain, admitted through `isPeerAllowed`).
  - Not covered: `_recoverBundle`, callers, the proof count, upgrades, events, and the
    manager's `initL2` (every chain's `L1_CHAIN_ID` is the one parameter `l1`). The gate
    and timeout evidence is still checked against the fixed history `S`, through the pin's
    `LegFinalizedBy`/`LegRefundableBy`, not against the live trees.
- **OncePerLegAtHead** (namespace `Contracts.AppendPath`, `main` `70096e2` and
  `draft/v0.35.0` `b17415d`). `StepsAtHead` and `SysStepsAtHead` are `Steps` and `SysSteps`
  with the tree's unbounded walk (`L2InteropCommitmentTree` topic `HintSearchAtHead`). The
  checks the head adds to `append` and `authorizeRefund` (on `draft/v0.35.0` also
  `_checkLegSourceAllowed`) only revert and are not modelled (`MODEL-APPEND-PATH-HEAD`).
  From genesis the head's runs reach exactly the pin's states and logs
  (`StepsAtHeadIffSteps`, `SysStepsAtHeadIffSysSteps`), so the headlines hold at head
  (`OncePerLegAtHead`, `NoSecondAppendAtHead`, `SystemOncePerLegAtHead`,
  `SystemExecutedObligationNeverRefundedOrBreakAtHead` and the rest). New: on every reachable
  state an `append` passes the guard and the tree's checks exactly when its commit value is
  nonzero and not a key and the hint is an occupied index below it (`AppendAtHeadEnabledIff`),
  and the pin's stale-hint revert passes at head
  (`StaleHintAppendRevertsAtPinSucceedsAtHead`). Witnesses: `OncePerLegAtHeadWitness`,
  `RefundedLegAtHeadWitness`, `NoSecondAppendAtHeadWitness` (stale-hint appends),
  `ClashBlocksFreshLegAtHead`, `SystemWitnessAtHead`.

- **RootImport** (namespace `Contracts.RootImport`). The gate as a destination runs it:
  `_authenticateRoot` must authenticate the IMT root through a multi-hop settlement
  proof ending at a settlement-layer root that destination has itself imported
  (`interopRoots`, bootloader-only imports), and final-node proofs are rejected. Source
  DA does not supply the import. `FlowFinalizableAt` is finalizability on a named
  destination; `FlowFinalizableBy` is its IMT half (`FinalizableAtImpliesBy`) and the two
  coincide on a ready destination with settlement data available
  (`SettlementDataAvailable`, `ReadyFinalizableAtIffBy`). The none-or-all results are
  restated per destination with two new world premises, `ImportAvailable` and
  `SettlementDataAvailable` (`PROTO-ROOT-IMPORT` in `ASSUMPTIONS.md`), and no hash premise
  (`NoneOrAllAtOrBreak`, `NoneOrAllAtOrBreakPinned`,
  `ExecutedAtImpliesAllFinalizableAtOrBreak` for an execution on one destination and
  finalizability on another, `…FromRuns`, the logged-clash form).
  `ImportAvailableOfPostDeadlineImport` discharges import availability from one
  post-deadline import plus `Aggregates`. Countermodel `WithoutImportFlowSitsHalfExecuted`:
  every leg committed on time and all data available, `FlowFinalizableBy` holds, one
  destination executes a leg, another can execute none, and no leg is refundable without a
  located `AbsenceBreak` on the refund's absence proof (what blocks the refunds is the legs'
  on-time commitment, not the missing import); `ImportAloneRestoresFinalizability` shows
  the single import is all that is missing, and `WithoutImportCrossDestinationFails` is the
  negation of `ExecutedAtImpliesAllFinalizableAtOrBreak` without the import premise
  (`WithoutImportLoggedFormFails` likewise for the logged-clash form).
  `StaleImportFlowSitsHalfExecuted` is the variant in which the stuck destination has
  imported a genuine root that does not cover the legs' batch, and
  `WithoutCoverageCrossDestinationFails` shows that the coverage half of the import premise
  is load-bearing, not only the import.
  Source chains are assumed to settle directly on the flow's settlement layer
  (`L2MessageVerification` allows one recursion level); Gateway-settled sources are out
  of scope.
  `WithoutSettlementDataLegIsStuck` shows the settlement-proof premise is needed too.
  Aggregation paths inside a settlement proof are idealized as the honest ones; the import
  transitions themselves are not modelled (a snapshot `World`, `ImportsGrow`).

- **Pause** (namespace `Contracts.InteropPause`). Each chain gets the `paused()` flags of
  its L2 `InteropCenter`, `L2AssetRouter` and `NativeTokenVault`, the owner's `pause` and
  `unpause` steps, and a pause gate on each step of `RunLog` (`PRun`) and of the
  tree-attached `SysSteps` (`PSysSteps`). Which pausable contract a bundle's send,
  execution and refund reach is the parameter `Profile`, fixed for the run; every result
  quantifies over profiles. The L2 interop handler has no pause gate (its
  `_ensureNotPaused` is a no-op on L2), and the manager has none. No hash premise.
  - Pause only removes steps. A paused run is a `RunLog` with the same checked calls, its
    authorizations are a `ReachLog`, and a paused `PSysSteps` run is a `SysSteps` run with
    the same logs (`PausedRunIsRunLog`, `PausedRunAuthCallsReachLog`,
    `PausedSystemIsSystemRun`; with every flag clear the converses hold,
    `RunLogIsUnpausedRun`, `SystemRunIsUnpausedSystemRun`). So the `…OrBreak` results hold
    verbatim over paused runs: `ExecutedObligationNeverRefundedOrBreakUnderPause`,
    `OneExecutionFreezesTheFlowOrBreakUnderPause`, `NoneOrAllOrBreakUnderPause` and its
    pinned form, `LoggedExecutionExcludesLoggedRefundOrBreakUnderPause`,
    `ExecutedImpliesRealFlowFinalizableOrLoggedClashUnderPause`, `SystemOncePerLegUnderPause`,
    `SystemExecutedObligationNeverRefundedOrBreakUnderPause`.
  - A paused destination vault (`PausedDestinationLeavesFlowStuck`). Take a checked flow
    whose legs were all committed by on-time batches, and a paused run from fresh managers
    to a state where the destination vault of one leg is paused, that leg minting through
    it. Then that leg cannot execute; no obligation of the flow is refunded unless a logged
    call that marked it carries a `CommittedRefundBreak` (a flow-id clash, or an
    `AbsenceBreak` on the call's own absence proof); and no timeout evidence for a leg of the
    flow passes without an `AbsenceBreak`. The first part is the gate's definition; the
    refund parts do not use the pause (`CommittedOnTimeNeverRefundedOrBreak`,
    `CommittedOnTimeExcludesRefundOrBreak`). In a continuation that never unpauses that
    vault, the leg is not executed and the same refund exclusion holds, also after a sibling
    leg executed on another destination (`PermanentDestinationPauseStrandsLeg`,
    `DestinationPauseStrandsSiblingWitness`); ending that state rests on the vault's owner
    (`OPS-CONFIG`).
  - Unpausing restores enabledness. At the end of any paused run, under `Wf` and
    `DataAvailable`, for a checked, committed-on-time flow, an extension by unpauses of that
    vault only (at most one, by `unpause`'s `whenPaused` guard) followed by the leg's
    execution on presentable evidence is a run (`UnpauseRestoresExecution`;
    `UnpausedGateIsTheGate`). The gate has no clock, so a long pause delays the execution
    but cannot expire it. The execution is `ExecutedViaBy`, the IMT half; the destination's
    root import is `RootImport`'s. `PRun`'s execute step, like `RunLog`'s, has no
    bundle-status check, so this is enabledness at the gate.
  - A paused source vault keeps a `Revertable` leg whose bundle has a router call
    `Revertable` and unclaimed for as long as it stays paused
    (`PausedVaultKeepsLegRevertable`); an unpause followed by the claim is then a run that
    leaves the leg `Reverted` (`UnpauseReEnablesClaim`). That the concrete claim succeeds
    is `AssetRouterBase` `PausedRecovery`.
  - Frames: `PauseGatesReadOnlyTheirOwnFlags`, `PausedDestinationStaysPausedAlongRuns`,
    `PausedCenterStaysPausedAlongRuns` (a paused center logs no `append` on its chain). That a
    source pause lasting past the deadline makes the timeout genuine is not a theorem here:
    the history is fixed and not tied to the run's appends.

  Witnesses: `PauseRunWitness`, `PausedDestinationStuckWitness`, `PausedVaultClaimWitness`,
  `DestinationPauseStrandsSiblingWitness`, `PausedCenterWitness`, `PausedSystemWitness`,
  and `LoggedExecutionExcludesLoggedRefundOrBreakUnderPauseWitness` (the padding run: the
  absence break is located). In `PauseRunWitness` and `PausedDestinationStuckWitness` the
  refund-break disjuncts are false because the one logged authorization marks another
  flow's obligation.

- **SharedCommitment** (namespace `Contracts.SharedCommitment`). Restates
  `SharedCommitmentYieldsCollision`, whose collision disjunct is unpinned and whose pinned
  form `CommitmentPinsLegOrCollision` is excluded middle, as statements the run decides. No
  hash premise and no premise on the commit value.
  - On a run. Two distinct obligations with one nonzero commit value can both be appended
    in one `SysSteps` run iff they are on different chains
    (`SharedCommitmentCoexistsIffCrossChain`). A list is the `append` log of some run of
    chain `c` iff its entries are on `c`, have nonzero commit values, appear once and have
    no `CommitClash` among them (`ChainLogIffAppendable`; every chain at once,
    `SystemLogIffAppendablePerChain`), and every duplicate-free list on one chain is a run's
    log under some clash-free commit value (`HonestCommitValueRealizesChainLog`).
    `SharedCommitmentPinnedToRun` is the backlog sketch's shape: two obligations drawn from
    a run's append and authorize logs with one commit value are equal, or on different
    chains (the same leg there, or a `CommitClash` on exactly those two). Once the commit
    values are equal that inner disjunction is excluded middle; the content is that on one
    chain only equality is possible. The managers alone admit a same-chain clash; the
    tree's `IMTValueAlreadyExists` check is what refutes it
    (`SharedCommitmentManagersAloneAdmitSameChainClash`).
  - At the gate, under the premise `HistoryFromRuns` (each batch-end tree of the fixed
    history is a tree its chain's run reaches; `MODEL-HISTORY-FROM-RUNS`). A leg that passes
    the inclusion check was appended on its declared chain by that batch, or has a
    `CommitClash` with an obligation in that chain's log, or has commit value `0`, or its
    proof carries an `InclusionBreak` (`GateLegWasAppendedOrClash`; flow form
    `ExecutedFlowLegsWereAppendedOrClash`; for a history cut from one `SysSteps` run,
    `SystemHistoryIsHistoryFromRuns`, `ExecutedFlowLegsWereAppendedInSystemOrClash`). Each
    exception fires alone on a never-appended leg
    (`SharedCommitmentClashLetsUnappendedLegExecute`,
    `SharedCommitmentZeroLetsUnappendedLegExecute`,
    `SharedCommitmentForgedProofLetsUnappendedLegExecute`); `SharedCommitmentGateWitness`
    and `SystemHistoryWitness` meet the premises with all three false.
  - At the timeout check, under `HistoryFromRuns`. If an absence proof passes, no
    obligation appended behind the root the check used shares the missing leg's commit
    value, or the proof carries an `AbsenceBreak`; there is no clash or zero exception
    (`TimeoutAbsenceExcludesSharedCommitmentOrBreak`, witness `TimeoutAbsenceWitness`). In
    `SharedCommitmentClashBlocksTimeout` a never-appended leg whose value clashes with an
    appended one executes, and every absence proof that passes for it carries an
    `AbsenceBreak`; it does not show that such a proof exists.
  - The same `(flowId, bundleHash)` can be appended on two chains in the model, because
    `bundleHash` embedding `block.chainid` is not modelled
    (`SharedCommitmentSameLegTwoChainsWitness`).

- **Operational** (namespace `Contracts.InteropOperational`). One global interleaving of
  every chain's `append` (with the tree insert), `authorizeRefund` (one leg per step, on the
  leg's declared chain), `claimRefund` and `initL2`; every destination's
  `executeAtomicBundle` (the gate only; it writes no destination state); and the
  settlement layer's batch end, in-order settlement at a non-decreasing clock, and root
  recording. An execution may cite only settled batches; `authorizeRefund` resolves against
  a recorded root and cites a settled batch. Every result is for every run from
  `opGenesis` and every node hash, leaf hash, padding constant, commit value and flow hash;
  none takes a hash, `Wf` or `Aggregates` premise. Boundaries: `MODEL-INTEROP-OPERATIONAL`.
  - Projection. The history the end state determines is `Wf`, with heights `fmHeight` of
    the leaf count by construction (`OpRunHistoryWf`). Every recorded root aggregates every
    batch settled strictly before it (`OpRunRootsAggregateBefore`), and that strict form is
    what the END branch needs (`IsLastOnTimeDerivedBefore`). The non-strict `Aggregates`
    can fail for a root recorded before a same-timestamp settlement
    (`OpRootMayMissSameTimeBatch`), so fixed-history results that take `Aggregates` do not
    apply verbatim; their content is re-proved (`OpRefundedLegMissedDeadlineOrBreak`,
    `OpRefundStaysDeserved`). Settled batches and recorded roots never change
    (`OpRunSettledHistoryIsFinal`), and every logged call cites settled batches
    (`OpLoggedEvidenceIsSettled`).
  - Embedding. A run's steps are a `SysSteps`, a `RunLog` and a `ReachLog` run over that
    history (`OpRunEmbedsInSysSteps`, `OpRunEmbedsInRunLog`, `OpRunEmbedsInReachLog`), and
    a prefix's calls stay valid against every later history (`OpPrefixEmbedsInLaterHistory`).
  - Transfer: `OpExecutedObligationNeverRefundedOrBreak`,
    `OpOneExecutionFreezesTheFlowOrBreak`, `OpRefundImpliesOwnFlowTimeoutOrLoggedClash`,
    `OpExecutedImpliesAllFinalizableOrBreak`, `OpSiblingFinalizableNowOrBreak`,
    `OpNoneOrAllOrBreakPinned`, `OpLoggedExecutionExcludesLoggedRefundOrBreak`,
    `OpExecutedImpliesRealFlowFinalizableOrLoggedClash`, `OpSystemOncePerLeg`,
    `OpRefundedWasAppendedOnce`, with `DataAvailable` where the original takes it. The
    projected history gives a batch that has not settled the live tree and the time `now`,
    so an existential conclusion over it ("finalizable", `RefundAuthorized`) may be met at
    such a batch, which can still settle late. `OpSiblingFinalizableNowOrBreak` is the
    reading on the settled batch the execution cited.
  - Escrow. For every logged execution and every leg of its flow: the leg's obligation was
    appended on its declared chain and is still `Committed` there, or a `CommitClash` with an
    obligation appended there, a zero commit value, an `InclusionBreak` on the execution's
    proof for that leg, or a `RefundBreak` holds (`OpExecutedLegWasAppendedOrBreak`,
    `OpExecutedLegEscrowedAndNotRefundedOrBreak`). The model has no burn: reading "appended"
    as "escrowed" rests on the center calling `append` in the source burn's transaction,
    argued from source. Over a fixed history an execution of a never-appended leg passes
    with no break (`FixedHistoryAdmitsUnescrowedExecution`).
  - Liveness as enabledness. Once a root created after the deadline is recorded, a checked
    flow with nonzero commit values can be executed now on every leg, or some leg makes
    every `Committed` leg refundable now on the BEGIN or (for a halted chain) END branch
    (`OpFinalizedFlowIsExecutable`, `OpTimedOutLegIsRefundable`,
    `OpFlowFateDecidedAfterRoot`), and the on-time settled batches never change again
    (`OpOnTimeBatchesFinalAfterRoot`). The exhibited evidence is the honest proof
    (`PROTO-DA`); the model imports every recorded root on every chain at once, and the
    omitted reject-only checks (pause, replay guard, sortedness) can still reject the call.
    Nobody is assumed to send it (`OPS-PROGRESS`).
  - `_verifyLastBatchInRoot` is modelled by its conclusion `N = R.upTo c`; the path forms
    (`RootBacking`, `LastBatchAccepted`) are not transferred.

  Witnesses: `OpHonestRunWitness` (two segments with nonempty logs, an execution and a
  refund of another flow; every break and clash disjunct false, and every recorded root
  meets even the non-strict `Aggregates`), `OpPaddingRefundLocatesAbsenceBreak` (with the
  pin's padding constant an executed, appended leg is refunded on a forged END-branch
  absence proof; the located break is that proof's `paddingHit`), `OpLivenessWitness`, and
  the countermodels `OpRootMayMissSameTimeBatch` and `FixedHistoryAdmitsUnescrowedExecution`.

- **RefundFaithful** (namespace `Contracts.RefundFaithful`, `c67894b9`; builds on `Refund`
  and `Timeout`). `authorizeRefund` as it runs: each writing iteration of its loop writes the
  CALLING chain's slot (`AtomicFlowManager.sol:155-161`), whatever chain the flow declares
  for that bundle, and the END branch is `_verifyLastBatchInRoot` with the batch-leaf path's
  length and position the prover's (`DeployedEndBranch`, over `LastLeafFaithful`'s
  `LastBatchPathAccepted`) instead of `IsLastOnTime`. `DeployedRun` is `Refund.ReachLog`
  with that step. With no hash premise and no premise on the roots, every slot carrying an
  executed flow's id, on every chain, stays at `Committed` or below, or a logged iteration
  that wrote it carries a `DeployedRefundBreak`: a flow-id clash, a break on the gate's or
  the timeout's IMT proof, a `LastLeafAnyLengthBreak` on the batch-leaf path, or a root
  stale for the missing leg's chain (`DeployedExecutedFlowFrozenOrBreak` and its per-leg
  forms; `DeployedExecutedFlowFrozenOrBreakUnderHonestRoots` drops the stale case under
  `Aggregates`). `MisdeclaredLegRefundedOnlyInDeployedModel` (a leg committed off its
  declared chain reaches `Revertable` there) and `StaleRootEndRefundOfDeliveredLegIsDeployed`
  are deployed runs that no `ReachLog` run matches. These forms locate a refund of an
  executed flow's slot and do not exclude it at `c67894b9`: the pinned padding gives the
  `AbsenceBreak` case with a `paddingHit` and no collision, also under aggregating roots
  (`DeployedPaddingRefundLocatesAbsenceBreak`). Witnesses:
  `DeployedExecutedFlowFrozenOrBreakWitness`, `DeployedRefundOwnTimeoutWitness`. At the
  current heads `append` binds the committed bundle to the committing chain; that is argued
  from source in the Specs docstring, not modelled.

- **LegSourceFilterAtV35** (namespace `Contracts.LegSourceFilterAtV35`; source
  `draft/v0.35.0` at `b17415d20`, not the pin; every Solidity file it cites is the same at
  `d9f678900`, where it was first written). v35 adds `_checkLegSourceAllowed` to the flow
  manager (`AtomicFlowManager.sol:338-344`): `requireFlowFinalized` runs it on every leg's
  source, on the bundle's destination, and `authorizeRefund` on the missing leg's source, on
  the refunding chain. It reads `L2Bridgehub.isPeerAllowed`, which `allowInteropPeer` sets and
  `deregisterChainForInterop` deletes. The model is `FlowBinding`'s `RunLog` and
  `OncePerLeg`'s `SysSteps` with every chain's allow-list in the state, the filter on the gate
  and authorize steps, and two admin steps enabled at every moment (`RunAtV35`,
  `SysStepsAtV35`). The tree, the proof checks and the manager are the pin's models, checked
  against true batch roots with no settlement-layer import, so this isolates the filter; the
  rest of the v35 diff is not modelled (the spec header lists it). No result takes a hash
  premise.
  - *Safety survives.* The filter only rejects: a v35 run is a pin run once the
    allow-lists are forgotten (`RunAtV35ProjectsToRunLog`, `SysStepsAtV35ProjectsToSysSteps`),
    and every pin run is a v35 run under full mutual allowance
    (`RunLogIsRunAtV35UnderFullAllowance`, `SysStepsIsSysStepsAtV35UnderFullAllowance`).
    The pin's `…OrBreak` exclusion results hold over v35 runs with the same located breaks
    (`ExecutedExcludesAnyRefundOrBreakAtV35`, `ExecutedObligationNeverRefundedOrBreakAtV35`,
    `OneExecutionFreezesTheFlowOrBreakAtV35`, `SystemOncePerLegAtV35`,
    `SystemExecutedObligationNeverRefundedOrBreakAtV35`, `NoneOrAllOrBreakAtV35`,
    `ExecutedImpliesRealFlowFinalizableOrLoggedClashAtV35`). What the filter adds: a logged
    execution and a logged refund of one flow id need a broken proof about the refund's
    missing leg, accepted by a chain that allowed that leg's source when it accepted it, or a
    flow-id clash between the two logged flows
    (`LoggedGateExcludesLoggedRefundOrAllowedBreakAtV35`).
    `ForgedSiblingExecutionNeedsAllowedForgerAtV35` and
    `ForeignForgedRefundNeedsAllowedForgerAtV35` replay two pin forgeries under the filter,
    the second on the pin's padding constant, which v35 no longer uses.
  - *Liveness does not.* One deregistration after commit strands a committed leg. In a
    complete swap the destination of one leg drops that leg's source: that leg passes the gate
    there for no presented flow and no evidence, while its sibling has executed, and every
    `authorizeRefund` call that presents the swap's flow id and passes carries a located break
    (`SwapStrandedByDeregistrationAtV35`). In an incomplete swap the committed leg's chain
    drops the missing leg's source: no refund passes there without a located break, though
    the honest call passes every check the pin runs, and no gate passes without a located
    break (`IncompleteSwapRefundStrandedByDeregistrationAtV35`). `StrandedIffAtV35` says
    exactly which legs are stranded in this model, for flows that pass `_checkFlowId`, have
    nonzero commit values and whose late legs' chains settle past the deadline
    (`StrandedIffAtV35Witness`: both cases occur, and neither under full allowance). The
    pin's `FlowFinalizableBy` has no destination, so it still holds of the stranded complete
    swap. Upstream documents this as the known limitation K1, "stuck flows"
    (`protocol-docs/interop-gating.md:256-266` at `b17415d20`); these results state it
    exactly in this model and are not a new finding. A chain without the settlement-layer
    import can be stuck for another reason (`RootImport`), which this topic does not combine
    with the filter.
  - *Re-allowing restores progress.* Both checks are monotone in the allow-lists
    (`GateMonotoneInPeersAtV35`, `RefundMonotoneInPeersAtV35`); one `allowPeer` step
    lets through a gate call with pin-valid evidence whose destination allows every other
    leg source (`ReallowRestoresGateAtV35`, `ReallowRestoresGateAtV35Witness`) and an
    `authorizeRefund` call that passes the pin's checks for a still-`Committed` leg
    (`ReallowRestoresRefundAtV35`), and until then the dropped source stays blocked on that
    chain (`BlockedUntilReallowedAtV35`). Who may take that step, and whether its service
    transaction lands, is outside the model (`MODEL-LEG-SOURCE-FILTER`, `OPS-CONFIG`).
  - Witnesses: `SafetyAtV35Witness`, `SystemAtV35Witness`, `StrandedIffAtV35Witness`,
    `CompleteFlowGateOpenIffSourcesAllowedAtV35Witness`, `RefundEvidenceCompleteAtV35Witness`
    (its filter premise is needed), `MonotoneInPeersAtV35Witness`,
    `ReallowRestoresGateAtV35Witness`, `ReallowAtV35Witness`.
  - Open: the filter on the operational model (`Operational`) and together with the
    settlement-layer import (`RootImport`), the handler's `Verified` status as state,
    `append`'s registration check, and the L1 side (`ChainRegistrationSender`).

- **SettlementRoots** (namespace `Contracts.SettlementRoots`). The roots the timeout gate
  resolves against, from the settlement layer's `MessageRootBase` (`../../Contracts/MessageRoot/`)
  and the destination's `L2InteropRootStorage` (`../../Contracts/L2InteropRootStorage/`). Every
  fixed-history timeout and refund headline holds with `Aggregates` weakened to the strict
  `Contracts.InteropOperational.AggregatesBefore` (the `…Before` forms; run level
  `ExecutedObligationNeverRefundedOrBreakAt`, over `ReachLogAt`, whose refunds are verified
  against roots). For a system whose batches are a MessageRoot run's pushed positions, clocked by
  their `l1Timestamp` (`ClockedBy`), every historical root of the run, as it stood at any point,
  satisfies the strict form (`HistoricalRootAggregatesBefore`), the clock gives `Wf.timeOrdered`
  (`WfFromMessageRoot`), and the headlines hold with no aggregation and no `timeOrdered` premise
  (the `…FromMessageRoot` forms). An L2 whose imports all passed the Executor's dependency-root
  check holds only historical roots, so the root the timeout read accepts is one of them
  (`ImportedRootsAreHistorical`, `ImportedTimeoutRootAggregatesBefore`). What remains: the trees
  (`WfTrees`) read as the commitment trees at the end of each pushed batch, with the BEGIN branch
  across a record-only or migration gap still needing `PROTO-BATCH-SNAPSHOT` and contiguous
  pushes; the root's content is a ghost count, not tied to what a Merkle proof against the root
  value shows. Witnesses: `SettlementRootsEndBranchWitness` (an END-branch timeout against a root
  read mid-block, where `Aggregates` fails), `SettlementRootsAcceptedWitness`,
  `SettlementRootsRefundRunWitness`, `SettlementRootsImportWitness`. Related models: `BatchPosition`
  takes `AggregatesBefore` as a premise (by definition the same condition as
  `Contracts.InteropOperational.AggregatesBefore`), which `HistoricalRootAggregatesBefore`
  discharges for MessageRoot-clocked systems; `../../Contracts/ChainBatchRootTree/` topic `GenesisSeed`
  (`b17415d20`) models `MessageRootBase`'s per-chain numbering slice, and
  `../../Contracts/AtomicFlowManager/` topic `RefundClosesAppend` (`b17415d20`) models
  `L2InteropRootStorage` with `latestInteropRootTimestamp`.

- **DispatchLiveness** (namespace `Contracts.DispatchLiveness`, pin `c67894b9`). One chain's send
  path: the center's salt flags and dispatch log (`InteropCenter`, topic `Dispatch`) composed with
  `OncePerLeg`'s manager and tree, so an atomic `_sendBundle` is one step with the dispatch's own
  hint (`Step`, `MODEL-SEND-PATH` in `ASSUMPTIONS.md`); its runs are runs of both
  (`DispatchRunProjectsToCenter`, `DispatchRunProjectsToAppendPath`). With no hash premise, an
  atomic dispatch with an unused salt, a formed and validated bundle, a nonzero commit value and the
  exact hint (the occupied leaf with the largest value below the commit value,
  `ExactHintIsLargestBelow`) has a step, or a `DispatchClash` pinned to the run's own log holds
  (`HonestDispatchEnabledOrClash`), also when the hint was exact at an earlier state of the run with
  at most five appends in between (`StaleHintDispatchEnabledOrClash`); no hint works iff such a
  clash holds (`AtomicDispatchBlockedIffClash`). The hint search, counted: the search succeeds iff its fuel
  covers `hopsNeeded` (`SearchSucceedsIffHopsWithinFuel`), so at the pin a hint works iff it is at
  most five hops away (`HintWithinFiveHopsSucceeds`), an exact hint still works after five later
  inserts (`StaleExactHintSurvivesFiveInserts`), and for every fuel some honest tree has an occupied
  hint that needs one hop more (`HopsNeededUnbounded`). "Enabled" is relative to the modelled checks.
  At the current heads the walk is unbounded and `append` checks more (Specs header).
- **ExecutionLiveness** (namespace `Contracts.ExecutionLiveness`, pin `c67894b9`). On the handler
  model of `InteropHandlerBase` topic `Reentrancy`. Outside `Verified`, without a valid proof,
  `executeBundle`, `verifyBundle` and `unbundleBundle` revert (`PublicRoutesRevertOutsideVerified`).
  Under the same no-proof condition only a call that passed the flow gate commits an effect of the
  hash (`NeverPublishedBundleNeedsTheFlowGate`, topic `BundleStatusMachineFaithful`), and an atomic
  leg's hash meets that condition up to two named clashes (`AtomicLegStaysAtomicAtDestinationOrClash`,
  topic `BundleStatusMachineStrong`). If every attempt on the leg meets a target that always
  reverts, whether or not the attempt passes the flow gate, the leg stays `Unreceived` and none of
  its calls is delivered (`AtomicLegWithRevertingCallNeverExecutes`; from a source run, up to the
  same two clashes, `…OrClash`); for a leg of a flow that passed the gate,
  `FinalizedRevertingLegNeitherDeliveredNorRefunded` adds `Refund`'s
  `OneExecutionFreezesTheFlowOrBreak`, a separate model linked by the leg's bundle hash. A bundle
  with a valid proof can instead be verified and unbundled with that call cancelled
  (`PublicBundleEscapesViaUnbundle`). The execution permission, which the handler model omits, is
  stated on topic `SelfCallAuthorityFaithful`'s gate model, not composed with `exec`: at the pin a
  call passes `executeAtomicBundle`'s gate for an `executionAddress` `(ch, a)` only as a direct call
  from `a`, with `ch` this chain or `0` (`ExecutorGatedLegNeedsExecutor`); for any other `ch` none
  passes it, while `receiveMessage` relays `executeBundle` for `(ch, a)`
  (`ForeignChainExecutorHasNoAtomicRoute`). Enabledness: `UnbundleEnabled`,
  `AtomicRouteStaysEnabled`. At `e561b9cc2` and the current heads the L2 handler has
  `verifyAtomicBundle` and a `receiveMessage` route into `executeAtomicBundle` (Specs header).

The other topics' tree side is a fixed multi-chain, multi-batch history, and steps may cite
evidence from anywhere in it. That admits more refunds and executions than an
operational model, so excluding both is the stronger claim, and a result that says a
refund or an execution can happen is the weaker one (`RefundStrong`'s
`StrandedFlowCommittedLegRefundable` is of that kind). The operational model is the
`Operational` topic ([Specs/Operational.lean](Specs/Operational.lean), namespace
`Contracts.InteropOperational`): the run produces the history, a call cites only settled
batches, `authorizeRefund` resolves against a recorded root, and every run projects to
a fixed history over which the `…OrBreak` headlines hold. `OncePerLeg`'s `SysSteps`,
`Pause` and the `SharedCommitment` gate results are still stated over a fixed history.
Liveness is proved there as
enabledness only (`OpFinalizedFlowIsExecutable`, `OpTimedOutLegIsRefundable`,
`OpFlowFateDecidedAfterRoot`): nobody is assumed to send the call, and checks the model
omits can still reject it (for an execution, among others, that the destination has
imported a root holding the cited batches: `RootImport`). Still open: eventual liveness
(every committed obligation eventually executes or refunds); `DispatchLiveness` and
`ExecutionLiveness` state when the send and execution routes are enabled at the pin, and a
case in which a leg of a finalized flow is neither delivered nor refunded. Source-side
obligations are O7–O9 in `../../Refinement.lean`.

These modules keep the namespaces they had on the `claude/proof-attempt-4f3778`
line (`Contracts.Atomicity`, `Contracts.Timeout`, `Contracts.Refund`).
