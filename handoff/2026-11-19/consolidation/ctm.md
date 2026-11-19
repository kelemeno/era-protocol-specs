# Consolidation unit `ctm`: ChainTypeManager unification

Branch `consol9/ctm`, from `claude/proof-round-9` (`35d2eb9`). It merges the three re-pin slices
(`consol9/ctm-a`, `-b`, `-c`; notes in `ctm-a.md`, `ctm-b.md`, `ctm-c.md`), applies the Specs
changes they deferred, and does HANDOFF step 2 (one model) and the README part of step 3 for
`EraSpec/Contracts/ChainTypeManager/`. Renames: `../renames/ctm.json` (the slices' own files are
empty).

## Deferred logic differences, and what was done

| Slice note | Difference at `b17415d20` | Done |
|---|---|---|
| ctm-a 1 | `Admin._executeDiamondCut` ends with the second-proof-system check; `GenesisWriters.AppStorage` lacked the field | `AppStorage.secondProofSystemRequired` and `Env.multiProofOf` added; `adminGenesisUpgrade` is now `executeDiamondCut` (cut, then the check). `DiamondInitInstallsTheRelease` gained the conjunct "requirement off" (stronger). All proofs repaired. |
| ctm-a 2 | `CTMRelease` constructor refuses more | No change needed (`validate()` unchanged); noted below as a shared-predicate candidate. |
| ctm-b 1 | `applyInfrastructureUpgrade` delegatecalls the transition's engine | `XStep` is kept as the default-engine projection (other folders import it); `ExecutorEngineAtV35.V35Step` is the executor model and the base results are restated over it (below). |
| ctm-b 2, ctm-c | `forward` requires code at a target with calldata | Reject-only; documented by the slices. |
| ctm-b 3, ctm-c | the gate on the transition path | `ChainRouting.Step` is kept gate-free (imported by `SecondProofSystem`, `Diamond`); `ProofGateAtV35`/`UpgradeTimingAtV35` are the gated models and the base results are restated over them (below). |
| ctm-b, ctm-c | names saying `E561` | Renamed to `Ungated` (six properties, `../renames/ctm.json`); docstrings saying "the `e561b9cc2` step" now say "the gate-free step". |
| ctm-c | `DefaultUpgrade` NatSpec binds a transition to its departing release | Doc only; `ChainRouting.Step.transition` already models the guard that way. |

## One model per layer

The folder now reads as one stack of models, each pinned at `b17415d20`, linked by proved
refinements (README, *How the models fit together*). Each gate-free or default-engine layer stays,
as the projection the `b17415d20` layer is defined over; other folders import `ChainRouting`,
`Enabledness`, `UpgradeTiming`, `VersionRegistry`, `DiamondStorage` and `LiveRouting`. No model was
deleted, so no property was moved or dropped. The base results are restated over the `b17415d20`
models, derived through the refinement lemmas, under the same names:

| Base topic | Restated over the `b17415d20` model |
|---|---|
| `ChainRouting` | `ProofGateAtV35`: `ChainsRunTheirVersionsRelease`, `FreshChainsRunTheirVersionsRelease` (already there); new `StepPreservesSysInvariant`, `TransitionStartsAndLandsOnRelease` (adds the installed verifier), `DriftBlocksTransition`. Not restated: the invariant constructors (`FreshSystemSatisfiesInvariant`, `BootstrapSystemSatisfiesInvariant`, about `Sys` only, apply unchanged), `UnguardedCutKeepsForeignSelectors` (about `applyDerived` only), and the two countermodels (gate-free runs are gated runs without the requirement, `UngatedRunsAreRunsWithoutTheRequirement`). |
| `ChainLocal` | `ChainRunsItsVersionsRelease` (already there); new `StepsElsewhereKeepChainOk`, `NonCutWriteLandsOnRelease`, `NewChainRunsItsVersionsRelease`, `RepairCutRestoresChainOk`, `OnlyRepairCutsLandOnARelease`, `RepairEnablesTransition` (plus the gate premise), `RepeatedSelectorBlocksTheEdge`, `LastWriteDecidesTheRouting`. Not restated: the migration ones (below), `GlobalPremiseImpliesChainLocal` (about label lists only). |
| `ChainMigration` | Not restated: `Sys35` has no migration out. Migration is disabled at `b17415d20` (`CHAIN_MIGRATIONS_ENABLED = false`), so these results describe runs production does not take. |
| `Enabledness` | `TransitionEnabledIff`, `UpgradesStayEnabled`, `ValidatedRunsKeepEverythingEnabled` (already there, with the gate); new `NewChainEnabledIff` (no extra condition), `BootstrapResetEnabledIff` (plus the gate), `ChainsStayOnWfReleases`, `BehindChainsCanCatchUp` (plus the gate on the edge's and the bootstrap's verifier). Not restated: `TransitionEnabled`/`NewChainEnabled` (implied by the iff forms), `StartingStatesMeetLivenessPremises` (about `Sys` only). |
| `ExecutorForward` | `ExecutorEngineAtV35` (already there): `TameEngineRunPreservesSysInv`, `TameEngineRunKeepsChainsOnTheirRelease`, `ReviewedLegsMoveProxiesOnlyAlongRows`, and the countermodels showing the old premises no longer suffice. `ForwardOfCtmCallsIsARun` is about `forward`, unchanged at `b17415d20` (`V35Step.other`). |
| `ChainLocalExecutor` | new `ExecutorEngineAtV35.ChainRunsItsVersionsReleaseAcrossEngineRuns`. |
| `ExecutorUpgradeChain` | new `ExecutorEngineAtV35.MisreportingSlotStaysFrozen`. The step-level results are about `upgradeChain`, unchanged at `b17415d20`. Not restated: `GenuineReplacementsKeepUpgradeChainLive` (its premise names the run's forwarded replacements, which the engine runs hide; follow-up). |
| `UpgradeTiming` | `UpgradeTimingAtV35`: `TimedRunKeepsChainsOnTheirRelease`, `ExecutorPathIgnoresNotifier`, `UpgradeChainEnabledIffTimed`, `NotAtAnyTime` (already there); new `UpgradeIsATransition`, `ManifestTimestampGates`, `EveryPathNeedsExecutedBatches`, `EveryPathNeedsTheSettlementLayerAhead`, `OtherCallersNeedTheNotifier`, `NotifierWrittenOnlyByItsChainAdmin`, `CtmPathIsADiamondCallByTheCtm`, `ExecutorPathIsACtmCallByTheExecutor`, `AdminAndCtmSkipTheNotifier`, `UpgradeStaysEnabledLater`. `ValidEdgeHasNoDeadTime` and `DeadlineOverrideOpensDeadTime` are about the CTM only and apply unchanged. |
| `UpgradeTimingStrong` | new `UpgradeTimingAtV35.ValidatedTimedRunsHaveNoDeadTime` (plus the gate premise). |
| `PendingL2UpgradeAtV35` | new `PendingRunIsAGatedRunWithoutTheRequirement`: without the requirement, every run of it is a run of the gated timed system. A pending model with the gate is a follow-up. |

## Duplication left inside this folder (follow-ups)

- `DuplicateSelectorScan` and `DuplicateSelectorCheck` transcribe the same
  `_requireNoDuplicateSelectors` (ctm-a). Now bridged: `ScanIsTheDuplicateCheck` proves the two
  accept the same routings for 4-byte selectors, so their results compose. Keeping one
  transcription is left: `DuplicateSelectorCheck`'s is imported by `Enabledness`'s users,
  `DuplicateSelectorScan`'s by `LiveRouting`'s.
- `EdgeChecks` (`CommittedEdgeExecutable`) and `L2Tables` (`L2Derivation`) model `L2PlanLib.build`
  twice, and `requireValidEdge` is re-stated in `L2Derivation.ValidEdge` and
  `PendingL2UpgradeAtV35.ValidEdge` (ctm-c). Bridged for the edge check:
  `EdgeChecks.RequireValidEdgeIsL2TablesValidEdge` proves `L2Tables.ValidEdge` is exactly
  `requireValidEdge` returning. Still open: the two plan builders, and
  `PendingL2UpgradeAtV35.ValidEdge`, an abstraction (version increase, valid schedule, no L2 side on
  a patch) with its own `minorOf` that does not truncate to `uint32`.
- `PendingL2UpgradeAtV35.BatchAux` and `UpgradeTxNonces.NonceDiamond` model the same pending pair
  (ctm-c).
- `GenesisWriters` transcribes `Diamond.sol` independently of `DiamondStorage`; a refinement lemma
  (`applyFacetCuts` without `isFrozen` equals `DiamondStorage.diamondCut`) would let it reuse it
  (ctm-a). `GenesisWriters.ReleaseWf`, `Enabledness.ReleaseWf` and `LiveRouting.ReleaseValid`/`RowsWf`
  could share one release-wellformedness predicate.

## Cross-contract duplication, for a later bridge unit

Not touched here: the upgrade-stack unit is consolidating those folders now.

- `ProxyUpgradeExecutorBase/{DomainHoldersV35, CoreLegV35, EngineLegV35}` model the executor's
  infrastructure leg independently of `ExecutorEngineAtV35`; `ExecutorOwnerCallsV35` models the
  executor's owner calls over `VersionRegistry`, independently of `ExecutorForward`'s `FStep`.
- `SecondProofSystem/UpgradeGateV35` adds the same gate to `UpgradeTiming.TimedStep` with its own
  `GateState`/`GSys`/`GStep`, independently of `ProofGateAtV35.ProofState` and
  `UpgradeTimingAtV35.TimedStep35`; `SecondProofSystem/FlagAuthorityV35` and `MigrationV35` re-model
  the flag's writers.
- `ProxyUpgradeExecutorBase/NotifierBindingV35` re-models the notifier binding that
  `UpgradeTiming.swapNotifier` abstracts (linked by `AgreesAt`).
- `Diamond/DiamondProxy` reuses `DiamondStorage` and `LiveRouting` and adds `isFrozen` and the
  fallback; `GenesisWriters.proxyCall` re-models that fallback.
- `AdminFacet.State` overlaps `GenesisWriters.AppStorage`'s slice of `ZKChainStorage`.
- The SemVer helpers of `EdgeChecks` duplicate the unmerged `Contracts.SemVer` (`cov2/encodings`).

## Headline tags

`EraSpec/Core/Headline.lean` had not landed on `claude/proof-round-9` when this unit finished, so no
tag is in the Lean files. The README's *Headline guarantees* list is the intended `@[headline]`
set. The full intended tagging (35 headlines, 64 countermodels, every `…Witness` def plus
`CommittedSlotWitnessMeetsHeadline` and `NoDeadTimeAcrossPatchWithPendingTx` as witnesses) is in the
table below, to be applied with `attribute [headline] Properties.X` lines once the infra unit lands.

| Topic | `@[headline]` | `@[countermodel]` | `@[witness]` |
|---|---|---|---|
| ChainLocal | - | `ChainLocalPremiseNotNecessary`, `RepairNeedsUniqueSelectors`, `RepairStepIgnoresLiveRouting` | `ChainLocalWitness` |
| ChainLocalExecutor | - | `CtmSwapBreaksChainLocal` | `ExecutorChainLocalWitness` |
| ChainMigration | - | - | `MigrationRoundTripWitness` |
| ChainRouting | - | `BreakGlassSelectorSurvivesWithoutGuard`, `MissingSelectorBricksTransition` | `ChainRoutingWitness`, `BootstrapResetWitness` |
| CommittedEdgeExecutable | `CommittedSlotEdgePassesChainChecks` | `NonGenuineSlotEdgeRevertsOnChain`, `UnbuiltPlanBreaksEmptinessAgreement`, `SupplierSwapClearsPublication`, `PubdataLimitThresholdIsExact`, `CalldataBoundIsExact` | `ConstructedEdgeWitness`, `CommittedSlotWitness`, `SupplierWitness`, `CommittedSlotWitnessMeetsHeadline` |
| DiamondStorage | - | `EmptyAddBreaksOk` | `DiamondCutWitness` |
| DuplicateSelectorCheck | `ReleaseWfIsTheDuplicateCheck` | - | `DuplicateCheckWitness` |
| DuplicateSelectorScan | - | - | `DuplicateScanWitness` |
| Enabledness | - | `DuplicateSelectorBricksEdge`, `DepartingDuplicateBlocksTransition` | `EnablednessWitness`, `CatchUpWitness` |
| EngineGettersFaithful | - | `ForeignCutsBreakTheHeadline`, `ForeignTargetBreaksTheHeadline` | `EngineGettersWitness` |
| ExecutorEngineAtV35 | `ExecutorChecksAfterAnyEngine`, `TameEngineRunKeepsChainsOnTheirRelease`, `ReviewedRunKeepsChainsOnTheirRelease`, `DefaultEngineRunKeepsChainsOnTheirRelease`, `ChainRunsItsVersionsReleaseAcrossEngineRuns` | `TameRunsNoLongerPreserveSysInv`, `TameRunsNoLongerKeepChainsOnTheirRelease`, `FixedEntrypointsNoLongerMoveOnlyAlongRows`, `CuttingEngineBreaksTheHeadline`, `CtmSwappingEngineBreaksSysInv`, `ProxyMovingEngineMovesAnUnnamedProxy`, `DirectEngineSkipsTheSourceCheck`, `BeforeHookDefeatsTheSourceCheck` | `ReviewedRunWitness`, `DefaultEngineRunWitness`, `EveryForwardIsAnEngineLegWitness` |
| ExecutorForward | - | `ForwardDowngradesAProxy`, `ForwardCtmSwapBreaksInvariants` | `ExecutorWitness` |
| ExecutorRowsUnvalidated | - | - | `ExecutorAnyRowsWitness` |
| ExecutorUpgradeChain | - | `NonGenuineReplacementBricksUpgradeChain` | `ExecutorUpgradeChainWitness`, `MisreportingSlotWitness` |
| GenesisWriters | `CodeRunsKeepChainsOnTheirRelease` | `ForeignDiamondInitBreaksGenesis`, `ForeignGenesisUpgradeBreaksGenesis`, `SelectorlessRowRevertsCreation` | `GenesisWritersWitness`, `CodeRunWitness` |
| L2Convergence | `ChainsOnOneVersionRunOneL2` | `ShellsDoNotConverge`, `UnexecutedL2TxLeavesTheOldRow`, `NonGenuinePlanLeavesTheOldRow`, `StaleGenesisImageSplitsAVersion`, `LegacyCommitMovesTheFrozenRow` | `L2ConvergenceWitness`, `BootstrapConvergenceWitness`, `FrozenRowAlongRunsWitness` |
| L2Derivation | `TransitionDeploysExactlyTheChangedRows` | `EmptyRowClashSplitsTheComparisons`, `AppendedEmptyRowKeepsAnL1OnlyEdge` | `FrozenRowWitness`, `L2DerivationWitness` |
| LegacyCrossingFaithful | - | `ChainSideCrossingBreaksTameHeadline` | `LegacyCatchUpWitness` |
| LiveRouting | `CountCheckIffExactRouting`, `ChainsRunTheirVersionsReleaseCounted` | `EmptySelectorRowFoolsCountCheck`, `RepeatedRowFoolsCountCheck`, `CorruptStorageFoolsCountCheck`, `EmptySelectorRowCarriesDriftAcrossEdge` | `CountCheckWitness`, `CountedRoutingWitness`, `CountedBootstrapResetWitness`, `CountedDriftWitness` |
| MutableSelectors | - | `MutableSelectorsSplitRouting`, `MutableSelectorsBlockNextEdge`, `StaleCutsSplitRouting`, `MutableSelectorsLeaveDepartingFacetRouted` | `StableSelectorsWitness`, `StableSelectorsOnWitness`, `InstallsReadDifferentAnswersWitness` |
| PendingL2UpgradeAtV35 | `PendingTxBlocksEveryUpgrade`, `NoDeadTimeWithoutPendingTx` | `NoDeadTimeNeedsItsPendingTxPremise`, `LateUpgradeLandsInDeadTime` | `ExpiredPendingChainWitness`, `NoDeadTimeWithoutPendingTxWitness`, `NoDeadTimeAcrossPatchWithPendingTx` |
| ProofGateAtV35 | `ChainsRunTheirVersionsRelease`, `FreshChainsRunTheirVersionsRelease`, `ChainRunsItsVersionsRelease`, `DriftBlocksTransition`, `TransitionEnabledIff`, `ValidatedRunsKeepEverythingEnabled`, `RequiringChainsKeepAMultiProofVerifier`, `RequirementIsPermanentWithoutBreakGlass` | `GateStrandsRequiringChain`, `BreakGlassClearsTheRequirement`, `MaskPremiseNeeded`, `RequirementDoesNotPinTheCurrentProofMode` | `ProofGateWitness`, `RequiringChainCanCrossWitness`, `RequirementLifecycleWitness`, `PerChainHeadlineAtV35Witness`, `UngatedRunLiftWitness` |
| UpgradeTiming | - | `NotAtAnyTime`, `UpgradeChainIsNotTimeIndependent`, `ReplacementMovesTheTimeGate`, `DeadlineOverrideOpensDeadTime`, `EachGateIsLoadBearing` | `UpgradeTimingWitness` |
| UpgradeTimingAtV35 | `UpgradeChainEnabledIffTimed`, `ExecutorPathIgnoresNotifier`, `ManifestTimestampGates`, `EveryPathNeedsExecutedBatches`, `EveryPathNeedsTheSettlementLayerAhead`, `ProofGateBindsEveryPath`, `OtherCallersNeedTheNotifier`, `ValidatedTimedRunsHaveNoDeadTime` | `NotAtAnyTime`, `OwnerCannotUpgradeARequiringChainToAPlonkRelease` | `UpgradeTimingAtV35Witness`, `TimedRequirementWritersWitness`, `UnflaggedUpgradeWitness` |
| UpgradeTimingStrong | - | `ValidScheduleAloneLeavesDeadTime`, `NoDeadTimeNeedsItsOtherPremises` | `ReplacementDeadlineWitness`, `NoDeadTimeWitness` |
| UpgradeTxNonces | `UpgradeTxNoncesStrictlyIncrease` | `LaggingReturnRepeatsNonce`, `ReturnAheadSkipsAnL2Upgrade` | `ExactLandingWitness`, `UpgradeTxNoncesWitness` |
| VersionRegistry | `CurrentReleaseIsVersionsRelease`, `VersionsIncreaseAlongRuns`, `CommitWritesEachSlotOnce`, `TransitionsChain` | `NonGenuineReplacementBreaksSlotVersion` | `VersionRegistryWitness` |
