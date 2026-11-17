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
| SourceHeight | [Specs/SourceHeight.lean](Specs/SourceHeight.lean) | [Properties/SourceHeight.lean](Properties/SourceHeight.lean) | [Proofs/SourceHeight.lean](Proofs/SourceHeight.lean) |
| FlowBinding | [Specs/FlowBinding.lean](Specs/FlowBinding.lean) | [Properties/FlowBinding.lean](Properties/FlowBinding.lean) | [Proofs/FlowBinding.lean](Proofs/FlowBinding.lean) |
| OncePerLeg | [Specs/OncePerLeg.lean](Specs/OncePerLeg.lean) | [Properties/OncePerLeg.lean](Properties/OncePerLeg.lean) | [Proofs/OncePerLeg.lean](Proofs/OncePerLeg.lean) |
| RootImport | [Specs/RootImport.lean](Specs/RootImport.lean) | [Properties/RootImport.lean](Properties/RootImport.lean) | [Proofs/RootImport.lean](Proofs/RootImport.lean) |
| BatchPosition | [Specs/BatchPosition.lean](Specs/BatchPosition.lean) | [Properties/BatchPosition.lean](Properties/BatchPosition.lean) | [Proofs/BatchPosition.lean](Proofs/BatchPosition.lean) |

Read them in that order; each builds on earlier ones (`FlowBinding` and `OncePerLeg` on
`Refund`, `RootImport` on `Atomicity`, `Timeout`, `SourceHeight` and `FlowBinding`,
`BatchPosition` on `Timeout`).

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
  tree contiguous, and a
  `RootBacking` of it misreads the root's last batch (`RoundTripBreaksContiguity`). Chains
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

The tree side is a fixed multi-chain, multi-batch history, and steps may cite
evidence from anywhere in it. That admits more refunds and executions than an
operational model, so excluding both is the stronger claim. An operational model
(or a projection theorem from one) is open; `OncePerLeg`'s `SysSteps` still checks
timeout evidence against that fixed history. Also open: liveness (every committed
obligation eventually executes or refunds). Source-side obligations are O7–O9 in
`../../Refinement.lean`.

These modules keep the namespaces they had on the `claude/proof-attempt-4f3778`
line (`Contracts.Atomicity`, `Contracts.Timeout`, `Contracts.Refund`).
