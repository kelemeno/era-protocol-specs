# Consolidation step 1: ChainTypeManager slice `ctm-c`

Topics: `UpgradeTiming`, `UpgradeTimingStrong`, `UpgradeTimingAtV35`, `PendingL2UpgradeAtV35`,
`CommittedEdgeExecutable`, `UpgradeTxNonces`, `L2Derivation`, `L2Convergence` (Specs, Properties
and Proofs of each, under `EraSpec/Contracts/ChainTypeManager/`).

Target: era-contracts `draft/v0.35.0` head `b17415d20`. No Properties def was removed or renamed,
and no statement changed (`renames/ctm-c.json` is empty). Only docstrings changed. Nothing in
another slice's files, the CTM README or outside `ChainTypeManager/` was edited.

## How the citations were checked

* For the two topics written at `e561b9cc2`, every cited file was diffed from `ccf00623c` (the
  squash-merge of the `e561b9cc2` registry code into `draft/v0.35.0`) to `b17415d20`. Every
  `file:line` was moved by a line map of that diff, then re-read at `b17415d20`: the first and
  last cited lines of every range were printed, and every code quote with a `// :n` comment was
  matched against the source text at those lines.
* For the six topics already pinned at `b17415d20`, every `file:line` was re-read the same way at
  `b17415d20`.

## Per topic

### `UpgradeTiming`

* **Pin before:** `e561b9cc2` (`feat/upgrade-simplification`). **Now:** `b17415d20`. The header
  states the re-pin and what changed.
* **Citations:** about 90 `file:line` moved, in Specs, Properties and Proofs. The Solidity bodies
  it models are unchanged between `ccf00623c` and `b17415d20`. Several fixes needed manual care:
  `_upgradeFromCommittedObject` in `DefaultUpgrade.sol` is now `:65-84` (`:66`, `:74`); the
  previous-upgrade-finalized check is now `BaseZkSyncUpgrade.sol:259-268` (it was an unmapped
  `245-254`).
* **Logic differences at `b17415d20`:** these are all reject-only checks, now listed under
  "Omitted reject-only checks":
  * `Admin._executeDiamondCut` (`Admin.sol:117-128`, check at `:121-126`) refuses a chain that
    requires its second proof system unless its verifier is in multi-proof mode.
  * `BaseZkSyncUpgrade._setVerifier` (`:143-148`) makes the same check.
  * `UpgradeExecutorBase.forward` requires code at the target of a call with calldata
    (`:42-44`). A forwarded `upgradeChainFromVersion` targets the CTM, so the check never
    rejects it.
  * `CTMUpgradeExecutor` now derives from `ProxyUpgradeExecutorBase`. `owner()` is unchanged.
  * `upgradeEngine` was renamed `chainUpgradeEngine`.

  No Specs definition needed a change. **Consequence:** `UpgradeTiming`'s enabledness and
  existence results (`UpgradeChainEnabledIffTimed`, `UpgradeStaysEnabledLater`,
  `EachGateIsLoadBearing`, `ValidEdgeHasNoDeadTime`) are about the gate-free model. At
  `b17415d20` they are exact only for chains that do not require their second proof system,
  which `UpgradeTimingAtV35.UnflaggedChainsUpgradeAsAtE561` proves. Its safety results carry over
  to v35 through `UpgradeTimingAtV35.TimedRunIsATimedRun`.
* **Model types:**
  * `TransitionSchedule`, `TimedConfig` (over `ExecutorForward.XConfig`), `ValidSchedule`;
  * `DiamondAux` (admin, validators, batch counters, settlement-layer version);
  * `TimedSys`, which is `ChainRouting.Sys` plus `DiamondAux` per chain plus the notifier
    schedule;
  * `UpgradePath`, `TimedLabel`, `DiamondUpgrade`, `TimedStep`, `TimedRun`;
  * `versionDeadline` and `ProtocolVersionActive`.
* **Imports:** `Specs/ExecutorForward` (another slice), and through it `ChainRouting` and
  `VersionRegistry`.
* **Imported by:**
  * in CTM: `UpgradeTimingStrong`, `UpgradeTimingAtV35`, and `PendingL2UpgradeAtV35`
    (transitively);
  * outside CTM: `ProxyUpgradeExecutorBase/{Specs,Proofs}/NotifierBindingV35.lean` and
    `SecondProofSystem/{Specs,Proofs}/UpgradeGateV35.lean`.
* **Duplicates and re-models:**
  * `UpgradeTimingAtV35` is this model plus the proof gate. The refinement lemmas already exist.
  * `SecondProofSystem/UpgradeGateV35` also adds a proof gate to `TimedStep`, with its own
    `GateState`/`GSys`/`GStep`. It re-models what `UpgradeTimingAtV35` does over
    `ProofGateAtV35.ProofState`.
  * `PendingL2UpgradeAtV35.BatchAux` and `UpgradeTxNonces.NonceDiamond` re-model the batch
    counters of `DiamondAux`, which `setAux` here leaves arbitrary.
  * `ProxyUpgradeExecutorBase/NotifierBindingV35` re-models the notifier binding that
    `swapNotifier` abstracts. It is linked to this model by `AgreesAt`.
* **Recommendation:** make `UpgradeTimingAtV35` the v35 timed topic and the home of the
  headlines. Keep `UpgradeTiming` as its gate-free abstraction, which the refinement lemmas
  already connect. Do not move it to History: it is now pinned at `b17415d20`. Restate
  `SecondProofSystem/UpgradeGateV35` over `TimedStep35`, or prove a refinement between `GStep`
  and `TimedStep35`, so that only one proof-state representation remains.

### `UpgradeTimingStrong`

* **Pin before:** `e561b9cc2`. **Now:** `b17415d20`. Citations moved. The cited code is
  unchanged apart from `CTMTransition.validate()` naming `chainUpgradeEngine`; it still only
  checks code presence. In the "same-deadline check" section, three bare `:n` references to
  `ChainTypeManager.sol` were remapped by hand: `:438`, `:483-489`, `:480`.
* **Logic differences:** none.
* **Model types:** label predicates over `UpgradeTiming`: `Op/Label/TimedLabel.CommitsValidSchedule`,
  `Op/Label/TimedLabel.KeepsDeadline`, `TimedLabel.InstallsWf` (over `Enabledness.Label.InstallsWf`),
  `SlotSchedulesValid` and `ChainDeadTime`. It adds no state.
* **Imports:** `UpgradeTiming` and `Enabledness` (another slice).
* **Imported by:** `PendingL2UpgradeAtV35`. Nothing outside CTM imports it.
* **Duplicates and re-models:** `PendingL2UpgradeAtV35.PChainDeadTime` re-states `ChainDeadTime`
  with real batch steps in place of `setAux`. `PendingRunIsATimedRun` is the refinement between
  them.
* **Recommendation:** keep it as a refinement layer.
  * The headline `ValidatedTimedRunsHaveNoDeadTime` is about the gate-free model with arbitrary
    `setAux`. `PendingL2UpgradeAtV35` shows it needs further premises once the pending L2
    transaction and real batch steps are modelled (`ExpiredPendingChainStaysInDeadTime`,
    `NoDeadTimeWithoutPendingTx`).
  * Either take the headline from `PendingL2UpgradeAtV35` (`NoDeadTimeWithoutPendingTx`), or
    tag `ValidatedTimedRunsHaveNoDeadTime` as a model-relative result.
  * Consider restating both over `TimedStep35`, so that the proof gate is included.

### `UpgradeTimingAtV35`

* **Pin:** `b17415d20`, unchanged. Citations re-read at `b17415d20`.
  * The `ICTMUpgradeExecutor` NatSpec range is corrected to `:47-54`. It had been `:47-56`,
    which included two `@param` lines.
  * The header and the Properties docstrings now say that `UpgradeTiming` is pinned at
    `b17415d20` and lists the proof-system checks among its omitted checks. The "was" line
    numbers remain the `ccf00623c` ones.
* **Logic differences:** none.
* **Model types:** `TimedSys35` (`TimedSys` plus `ProofGateAtV35.ProofState` per chain),
  `TimedProofEffect`, `TimedLabel35`, `TimedStep35`, `TimedRun35` and `TimedGateHolds`.
* **Imports:** `UpgradeTiming`, and `ProofGateAtV35` (another slice).
* **Imported by:** only `EraSpec.lean`.
* **Duplicates and re-models:** see `UpgradeTiming` above, and `SecondProofSystem/UpgradeGateV35`.
* **Recommendation:**
  * Make this the v35 topic, through unification or refinement.
  * Three property names still say `E561`: `TimedStepIsTheE561StepPlusTheGate`,
    `E561TimedRunsAreRunsWithoutTheRequirement` and `UnflaggedChainsUpgradeAsAtE561`. They now
    mean "the gate-free `UpgradeTiming` step". Rename them in the unification unit, for example
    to `…Ungated…`, with renames entries. I left them, because renaming is outside step 1.

### `PendingL2UpgradeAtV35`

* **Pin:** `b17415d20`, unchanged.
* **Citations:** re-read. All matched except one: the storage mapping `protocolVersionDeadlines`
  was cited at the getter's lines and is now cited at `ChainTypeManager.sol:97`, read at `:546`.
  The header no longer says that `UpgradeTiming` is at `e561b9cc2`.
* **Logic differences:** none. It already lists the two second-proof checks as omitted.
* **Model types:**
  * `PendingConfig`, `ValidEdge` (schedule, version increase, and no L2 side on a patch), `BatchAux`;
  * `PendingSys`, which is `TimedSys` plus `BatchAux` per chain plus the CTM's deadline
    overrides;
  * `PLabel`, `L2Gate`, `l2After`, `BaseEffect`, `PStep`, `PRun`, `PChainDeadTime`,
    `PendingBlock`, `PendingUnbatched`;
  * `minorOf` and `PatchOnly`.
* **Imports:** `UpgradeTimingStrong`, and through it `UpgradeTiming`, `Enabledness`,
  `ChainRouting` and `VersionRegistry`.
* **Imported by:** only `EraSpec.lean`.
* **Duplicates and re-models:**
  * **With `UpgradeTxNonces`:** both model the pending pair `(l2SystemContractsUpgradeTxHash,
    l2SystemContractsUpgradeBatchNumber)` under commit, execute, revert and migration, with
    separate state types (`BatchAux` vs `NonceDiamond`).
  * **Version shape:** `minorOf`, `PatchOnly` and `ValidEdge` duplicate `EdgeChecks.minorOf` and
    `requireValidEdge` (`CommittedEdgeExecutable`) and `L2Tables.minorOf` and `ValidEdge`
    (`L2Derivation`).
  * **Base model:** it sits on `UpgradeTimingStrong`, not on `UpgradeTimingAtV35`.
* **Recommendation:** unify.
  * Keep one per-chain pending-upgrade state, `BatchAux` over the timed system. Restate
    `UpgradeTxNonces` over it, or prove a simulation from `PStep` to `NonceStep` on the shared
    fields.
  * Make `EdgeChecks.requireValidEdge` the one transcription of the version shape, with the
    other two `ValidEdge`s as lemmas over it.
  * Rebase onto `TimedStep35` when the timed topics are unified.

### `CommittedEdgeExecutable`

* **Pin:** `b17415d20`, unchanged.
* **Citations:** re-read. All quotes match. The composition section had four end lines off by a
  few lines, now corrected: `replaceUpgradeTransition` `:424-443`, `_requireSameDeparture`
  `:472-478`, `_requireOnwardDestination` `:498-518`, `_setCurrentRelease` `:300-318`. Added a
  note that `_setVerifier`, outside the modelled storage part, also has the second-proof check
  (`:143-148`).
* **Logic differences:** none.
* **Model types:**
  * Config constants; SemVer helpers `edgeUnpackSemVer`, `unpackChecked`, `majorOf`, `minorOf`,
    `VersionWf`, `EdgeVersionShape`; `requireValidEdge`;
  * L2 plan types: `ContractUpgradeType`, `Deployment`, `AuthoredL2Plan`, `L2UpgradePlan`,
    `L2Tx`, `PlanEnv`, `unsafeDeployment`, `planBuild`, `buildL2UpgradeTxFromPlan`;
  * edge construction: `EdgeObject`, `Constructed`;
  * chain side: `ChainUpgradeState`, `setNewProtocolVersion`, `setL2SystemContractUpgrade`,
    `upgradeStoragePart`, the gas formula;
  * supplier: `Supplier`, `SupplierStep`/`SupplierRun`, `requirePublished`;
  * `EdgeWorld`.
* **Imports:** `VersionRegistry` (another slice).
* **Imported by:** `UpgradeTxNonces`.
* **Duplicates and re-models:**
  * `planBuild`/`L2UpgradePlan`/`Deployment` duplicate `L2Tables.buildPlan`/`L2Plan`/`Deployment`
    (`L2Derivation`). Both model `L2PlanLib.build`.
  * The SemVer helpers duplicate the unmerged `Contracts.SemVer` (`cov2/encodings`).
  * `requireValidEdge` is re-modelled in `L2Derivation.ValidEdge`, in
    `PendingL2UpgradeAtV35.ValidEdge`, and in part in `UpgradeTiming.ValidSchedule`.
* **Recommendation:** unify the two L2-plan models into one. `EdgeChecks` is the fuller
  transcription; `L2Tables` adds the table derivation that feeds `planBuild`'s `_derived`. Keep
  one `requireValidEdge`.

### `UpgradeTxNonces`

* **Pin:** `b17415d20`, unchanged.
* **Citations:** re-read; all match.
* **Logic differences:** none.
* **Model types:** `setNewProtocolVersionGenesis`, `genesisStoragePart`, `NonceDiamond`,
  `NonceMigration`, `NonceSys`, `NonceLabel`, `NonceStep`/`NonceRunWith`/`NonceRun`, `NonceInv`,
  `ActiveVersion`, `MintLandsNotBehind`/`MintLandsExactly` and `TxHashCollision`.
* **Imports:** `CommittedEdgeExecutable`.
* **Imported by:** only `EraSpec.lean`.
* **Duplicates and re-models:** see `PendingL2UpgradeAtV35`. It has its own one-chain history
  model with migration copies, and is not composed with the CTM's runs or with
  `UpgradeTiming`/`PendingL2UpgradeAtV35`.
* **Recommendation:** refinement lemma onto the unified pending-upgrade state; otherwise keep it
  separate. Its migration-copy part (`NonceMigration`) has no counterpart elsewhere.

### `L2Derivation`

* **Pin:** `b17415d20`, unchanged.
* **Citations:** re-read; all match. The pre-fix comparison at `4e073f09b` (parent of the OZ fix
  `9775be946`) was checked at `4e073f09b`: `CTMTransition.sol:128-135` there.
* **Logic differences:** none.
* **Model types:**
  * byte and address types: `Bytes`, `L2Addr`, `KeccakClash`;
  * `fixedAddress`, `rowAt`, `changedL2Rows`, `ProxyDeployment`, `deriveL2DeploymentsFromTable`;
  * plan types: `Deployment`, `L2Plan`, `AuthoredL2`, `buildPlan`, `hasL2Side`;
  * version shape: `minorOf`, `majorOf`, `ValidEdge`;
  * releases: `GenesisParams`, `ReleaseL2`, `l2TableChanged`, `L2StateKept`;
  * `L2StateKeptPreFix` and `ctmTransitionL2PreFix` (`4e073f09b`);
  * `EdgeInput`, `derivedPlan`, `ctmTransitionL2`, `bootstrapPlanL2`, `ReleaseL2Accepted`.
* **Imports:** only Mathlib.
* **Imported by:** `L2Convergence`.
* **Duplicates and re-models:** see `CommittedEdgeExecutable`.
* **Recommendation:**
  * Unify the plan types with `EdgeChecks`.
  * The `…PreFix` definitions, and the statement that compares against them
    (`AppendedEmptyRowKeepsAnL1OnlyEdge`, which states the `b17415d20` behaviour together with
    the refusal at `4e073f09b`), are the record of the OZ L-01 fix. Keep them as a countermodel
    of the fixed behaviour, or split off the `4e073f09b` half into History. That half cannot be
    dropped without weakening the statement.

### `L2Convergence`

* **Pin:** `b17415d20`, unchanged.
* **Citations:** re-read; all match.
* **Logic differences:** none.
* **Model types:** `L2State`, `applyProxy`/`applyProxies`/`applyPlan`, `fullInstall`, `L2World`
  (over `VersionRegistry.World`), `L2Chain`, `L2Sys`, `L2Label`, `L2Step`, `L2Run`, `L2Genuine`,
  `RunsReleaseL2`, `GenesisImageHolds`, `L2Inv`, `CrossClash`, `freshL2Sys` and `bootstrapL2Sys`.
* **Imports:** `ChainRouting` (only `ChainId`) and `L2Derivation`. It uses `VersionRegistry`'s
  `CTM`/`CStep`.
* **Imported by:** only `EraSpec.lean`.
* **Duplicates and re-models:** its crossing step re-models a chain's upgrade (version
  `old → new` at the committed slot) without routing, timing or the pending transaction. It is
  not connected to `ChainRouting.Step.transition` or `UpgradeTiming.TimedStep`.
* **Recommendation:** keep it separate; its L2 ghost state is unique. Add a refinement lemma
  mapping `L2Step.cross` to `ChainRouting`'s transition, so that its run-level headline
  (`ChainsOnOneVersionRunOneL2`) composes with the timed topics.

## Logic differences that need another slice

None needs a Specs change in another slice's topic. Notes for the unification unit:

* `DefaultUpgrade.upgradeFromTransition`'s NatSpec at `b17415d20` says the transition is bound to
  its departing release's routing (`requireReleaseRouting`), not to a CTM. `UpgradeTiming` reads
  that through `ChainRouting.Step.transition`, which belongs to another slice.
* `UpgradeTiming`'s `TimedStep.ctm` covers "the executor's `forward`" of the CTM call. The new
  `forward` code check is reject-only and never fires for that call. `ExecutorForward`, in
  another slice, owns the `forward` model.

## Headline tags

Not added. The infra unit's `EraSpec/Core/Headline.lean` was not on `claude/proof-round-9` when
this slice finished, and step 1 excludes headlines. Candidates:

* `UpgradeTimingAtV35.ProofGateBindsEveryPath`
* `UpgradeTimingAtV35.UpgradeChainEnabledIffTimed`
* `UpgradeTimingAtV35.TimedRunsKeepAMultiProofVerifier`
* `PendingL2UpgradeAtV35.NoDeadTimeWithoutPendingTx`
* `PendingL2UpgradeAtV35.PendingTxBlocksEveryUpgrade`
* `CommittedEdgeExecutable.CommittedSlotEdgePassesChainChecks`
* `UpgradeTxNonces.UpgradeTxNoncesStrictlyIncrease`
* `L2Derivation.TransitionDeploysExactlyTheChangedRows`
* `L2Convergence.ChainsOnOneVersionRunOneL2`

Countermodels: `NotAtAnyTime`, `OwnerCannotUpgradeARequiringChainToAPlonkRelease`,
`ExpiredPendingChainStaysInDeadTime`, `LaggingReturnRepeatsNonce`, `ShellsDoNotConverge` and
the `…Witness` defs.
