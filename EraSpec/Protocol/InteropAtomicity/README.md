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
| LegSourceFilterAtV35 | [Specs/LegSourceFilterAtV35.lean](Specs/LegSourceFilterAtV35.lean) | [Properties/LegSourceFilterAtV35.lean](Properties/LegSourceFilterAtV35.lean) | [Proofs/LegSourceFilterAtV35.lean](Proofs/LegSourceFilterAtV35.lean) |

Read them in that order; each builds on earlier ones (`FlowBinding` and `OncePerLeg` on
`Refund`, `RootImport` on `Atomicity`, `Timeout`, `SourceHeight` and `FlowBinding`,
`LegSourceFilterAtV35` on `FlowBinding` and `OncePerLeg`). `LegSourceFilterAtV35` is the one
topic not at the pin: it adds the receive filter of `draft/v0.35.0` (`b17415d20`) to the
`FlowBinding` and `OncePerLeg` models.

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
  (topic `EndBranch`).
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

The tree side is a fixed multi-chain, multi-batch history, and steps may cite
evidence from anywhere in it. That admits more refunds and executions than an
operational model, so excluding both is the stronger claim. An operational model
(or a projection theorem from one) is open; `OncePerLeg`'s `SysSteps` still checks
timeout evidence against that fixed history. Also open: liveness (every committed
obligation eventually executes or refunds). Source-side obligations are O7–O9 in
`../../Refinement.lean`.

These modules keep the namespaces they had on the `claude/proof-attempt-4f3778`
line (`Contracts.Atomicity`, `Contracts.Timeout`, `Contracts.Refund`).
