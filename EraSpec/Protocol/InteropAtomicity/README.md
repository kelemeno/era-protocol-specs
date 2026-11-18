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

Read them in that order; each builds on earlier ones (`FlowBinding` and `OncePerLeg` on
`Refund`, `RootImport` on `Atomicity`, `Timeout`, `SourceHeight` and `FlowBinding`;
`Pause` on `FlowBinding` and `OncePerLeg`, `SharedCommitment` on `OncePerLeg`, and
`Operational` on `OncePerLeg`, `FlowBinding` and `SourceHeight`).
The exception is `RefundStrong`, which also takes `AggregatesBefore` from the later
`Operational` topic ([Specs/Operational.lean](Specs/Operational.lean)).

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
  (topic `EndBranch`).
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
(every committed obligation eventually executes or refunds). Source-side obligations are
O7–O9 in `../../Refinement.lean`.

These modules keep the namespaces they had on the `claude/proof-attempt-4f3778`
line (`Contracts.Atomicity`, `Contracts.Timeout`, `Contracts.Refund`).
