# Interop atomicity across chains and batches

Sources: `contracts/atomic-interop/AtomicFlowManager.sol` (`requireFlowFinalized`,
`_checkFlowId`, `authorizeRefund`, `claimRefund`) and
`contracts/atomic-interop/libraries/AtomicInteropProof.sol`
(`verifyTimeoutAbsence`, `_verifyLastBatchInRoot`) in the pinned era-contracts tree.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Atomicity | [Specs/Atomicity.lean](Specs/Atomicity.lean) | [Properties/Atomicity.lean](Properties/Atomicity.lean) | [Proofs/Atomicity.lean](Proofs/Atomicity.lean) |
| Timeout | [Specs/Timeout.lean](Specs/Timeout.lean) | [Properties/Timeout.lean](Properties/Timeout.lean) | [Proofs/Timeout.lean](Proofs/Timeout.lean) |
| Refund | [Specs/Refund.lean](Specs/Refund.lean) | [Properties/Refund.lean](Properties/Refund.lean) | [Proofs/Refund.lean](Proofs/Refund.lean) |
| SourceHeight | [Specs/SourceHeight.lean](Specs/SourceHeight.lean) | [Properties/SourceHeight.lean](Properties/SourceHeight.lean) | [Proofs/SourceHeight.lean](Proofs/SourceHeight.lean) |
| FlowBinding | [Specs/FlowBinding.lean](Specs/FlowBinding.lean) | [Properties/FlowBinding.lean](Properties/FlowBinding.lean) | [Proofs/FlowBinding.lean](Proofs/FlowBinding.lean) |
| OncePerLeg | [Specs/OncePerLeg.lean](Specs/OncePerLeg.lean) | [Properties/OncePerLeg.lean](Properties/OncePerLeg.lean) | [Proofs/OncePerLeg.lean](Proofs/OncePerLeg.lean) |
| BatchPosition | [Specs/BatchPosition.lean](Specs/BatchPosition.lean) | [Properties/BatchPosition.lean](Properties/BatchPosition.lean) | [Proofs/BatchPosition.lean](Proofs/BatchPosition.lean) |

Read them in that order; each builds on earlier ones (`FlowBinding` and `OncePerLeg` on
`Refund`, `BatchPosition` on `Timeout`).

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
  timeout branch (`NoneOrAll`, `ExecutedExcludesAnyRefund`). The flow-id
  recomputation is meant to pin the leg list (`FlowIdCheckPinsLegList`, vacuous via
  `FlowHashInj`). Countermodels: a
  self-only gate admits a mixed outcome, a subset flow passes a gate without the
  id check, and without data availability a committed leg is stuck.
- **Timeout.** The "last batch that settled by the deadline" fact is derived from
  the three comparisons and the last-batch proof (`IsLastOnTimeDerived`,
  `TimeoutMeansMissedDeadline`), under the settlement layer's `Aggregates`
  invariant. `StaleRootRefundsDeliveredLeg` shows that invariant is load-bearing,
  so real-path claims inherit it. The halted-chain END branch is composed into the
  reference bridge in `../../Examples/BurnMintBridge/` (topic `EndBranch`).
  `Timeout`'s `RootBacking` reads "leaf `i` of the chain tree is batch `i`" and uses one
  `N` as Merkle position and batch number. That holds only on the identity numbering;
  `BatchPosition` is the END branch without it.
- **BatchPosition** (namespace `Contracts.BatchPosition`). The settlement layer's chain
  tree starts empty at whatever batch the chain is registered at and appends at the next
  position (`MessageRootBase._addNewChain`, `_pushChainBatchRoot`), so position and batch
  number differ for an EraVM chain, a chain onboarded at a nonzero batch, a chain that
  recorded batches through the v31 entry point, and a chain that migrated. `ChainTreeStep`
  models the four writers; on every reachable tree batch numbers strictly increase
  (`ReachableSlotNumbersIncrease`) and, without a genesis leaf, position `i` holds a batch
  above `s + i` (`TreePositionBelowBatchNumber`). The old backing cannot represent a chain
  onboarded at batch 100 (`CurrentCompositionCannotRepresentOnboardingAt100`); it is the
  new one exactly on the identity numbering, which only a seeded ZKsync OS chain registered
  at 0 reaches (`IdentityNumberedBackingIsOldBacking`, `IdentityNumberingNeedsGenesis`).
  The END branch takes the mask `pos` and the leaf preimage `(batchRoot, N, timestamp)`
  separately. With no hash premise, an accepted last-batch proof makes the submitted
  preimage the tree's last entry, so `N = R.upTo c` and the compared timestamp is the
  leaf's, or a `PositionedEndBreak` is located on the submission: a `PinnedBreak`, a
  `PathCollision`, or a `LeafPreimageClash` between the stored entry and the submitted
  preimage (`PositionedLastBatchIdentifiesLastEntryPinned`,
  `PositionedEndBranchImpliesVerifiedPinned`). Headlines:
  `PositionedTimeoutMeansMissedDeadlineOrBreak`,
  `PositionedTimeoutExcludesFinalityOrBreak`, and
  `PushLogTimeoutMeansMissedDeadlineOrBreak`, whose premises are about the batches
  actually pushed. The `…On` forms collapse the break under injectivity restricted to
  this tree's pairs, the submitted path and the entries plus the submitted preimage
  (`NoPositionedEndBreakOn`). `PositionedAcceptedImpliesRefundablePinned` lands in
  `Contracts.Atomicity.LegRefundableBy`, so results stated over that predicate apply.
  The settlement-layer premise is the strict `AggregatesBefore`
  (`AggregatesImpliesBefore`, `AggregatesBeforeIsWeaker`), derived from the push log
  (`AggregatesBeforeFromPushLog`) under the explicit `GapsAfterRootLate` for batches never
  pushed to this layer. Witnesses: `OnboardedTimeoutWitness` (every starting batch, all
  breaks false), `OnboardedAt100Composes`, `EraVmNoGenesisComposes`,
  `MigrationGapInsideTreeWitness`, `PositionedConclusionNotAlways`. Countermodels:
  `BatchNumberForgeryLocatesLeafClash` (a leaf hash that does not bind the batch number
  refunds a delivered leg, and the located break is the `LeafPreimageClash`),
  `MigrationGapIsLoadBearing`.
  Not modelled: the link from the submitted batch root to the IMT the absence check
  runs against, the prover-chosen path length, the shared tree and the import of the
  root. The gate takes the occupied-range form of the mask check;
  `MaskBoundGivesOccupiedRange` relates it to the bound the contract checks.
  Open: `Refund`'s accepted-gate results (`AcceptedTimeoutAuthorizesOrBreak` and the
  others over `LegRefundableAcceptedBy`), `Operational`, and the `BurnMintBridge`
  `EndBranch` topic still take `RootBacking`, so they cover the identity numbering only.
  Their positioned restatements are not written.
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

The tree side is a fixed multi-chain, multi-batch history, and steps may cite
evidence from anywhere in it. That admits more refunds and executions than an
operational model, so excluding both is the stronger claim. An operational model
(or a projection theorem from one) is open; `OncePerLeg`'s `SysSteps` still checks
timeout evidence against that fixed history. Also open: liveness (every committed
obligation eventually executes or refunds). Source-side obligations are O7–O9 in
`../../Refinement.lean`.

These modules keep the namespaces they had on the `claude/proof-attempt-4f3778`
line (`Contracts.Atomicity`, `Contracts.Timeout`, `Contracts.Refund`).
