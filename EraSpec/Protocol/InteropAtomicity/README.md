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
| FlowBindingAtHead (`3605e82`) | [Specs/FlowBindingAtHead.lean](Specs/FlowBindingAtHead.lean) | [Properties/FlowBindingAtHead.lean](Properties/FlowBindingAtHead.lean) | [Proofs/FlowBindingAtHead.lean](Proofs/FlowBindingAtHead.lean) |

Read them in that order; each builds on earlier ones (`FlowBinding` and `OncePerLeg` on
`Refund`, `RootImport` on `Atomicity`, `Timeout`, `SourceHeight` and `FlowBinding`;
`FlowBindingAtHead` on `FlowBinding`, `OncePerLeg` and `AtomicFlowManager`
`FlowCanonicalAtHead`). Every topic models the pinned tree except `FlowBindingAtHead`,
which models a later era-contracts head (see its section below).

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
