# ChainTypeManager

Source: `l1-contracts/contracts/state-transition/ChainTypeManager.sol` and the
registry-driven upgrade objects and engines it drives
(`l1-contracts/contracts/upgrades/registry/`, `upgrades/DefaultUpgrade.sol`,
`upgrades/BootstrapUpgrade.sol`, the chain's `Admin` facet and `DiamondInit`).

That code is **not** in the pinned era-contracts tree. It lives on branch
`feat/upgrade-simplification` of the zksync-era `contracts` repository, and this model
was written against commit **`e561b9cc2`** (2026-10-19). **The branch moves**: every
`file:line` quoted in the specs is at that commit, and the results describe that commit,
not the current branch. Re-check the source before relying on them.
`../ProxyUpgradeRowLib/` models the row library at an older snapshot (`Rows`) and at this
commit (`RowsCurrent`, and `RowsUnvalidated` for rows no `validateRows` has checked); the
`ExecutorForward` topic below uses `RowsCurrent`, and `ExecutorRowsUnvalidated` uses
`RowsUnvalidated`.

One topic is at a different commit: `ExecutorEngineAtV35` models
`applyInfrastructureUpgrade` at branch `draft/v0.35.0`, commit **`d9f6789`** (2026-11-06),
where #2654 (`95b5c469d`) replaced the executor's own `applyTransition` by a delegatecall
into the engine the transition names. Every other entry point it uses is `ExecutorForward`'s,
whose bodies are unchanged at `d9f6789`; nothing else in this folder has been re-read there.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those
exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| VersionRegistry | [Specs/VersionRegistry.lean](Specs/VersionRegistry.lean) | [Properties/VersionRegistry.lean](Properties/VersionRegistry.lean) | [Proofs/VersionRegistry.lean](Proofs/VersionRegistry.lean) |
| ChainRouting | [Specs/ChainRouting.lean](Specs/ChainRouting.lean) | [Properties/ChainRouting.lean](Properties/ChainRouting.lean) | [Proofs/ChainRouting.lean](Proofs/ChainRouting.lean) |
| ChainMigration | [Specs/ChainMigration.lean](Specs/ChainMigration.lean) | [Properties/ChainMigration.lean](Properties/ChainMigration.lean) | [Proofs/ChainMigration.lean](Proofs/ChainMigration.lean) |
| ChainLocal | [Specs/ChainLocal.lean](Specs/ChainLocal.lean) | [Properties/ChainLocal.lean](Properties/ChainLocal.lean) | [Proofs/ChainLocal.lean](Proofs/ChainLocal.lean) |
| ExecutorForward | [Specs/ExecutorForward.lean](Specs/ExecutorForward.lean) | [Properties/ExecutorForward.lean](Properties/ExecutorForward.lean) | [Proofs/ExecutorForward.lean](Proofs/ExecutorForward.lean) |
| ExecutorEngineAtV35 (`d9f6789`) | [Specs/ExecutorEngineAtV35.lean](Specs/ExecutorEngineAtV35.lean) | [Properties/ExecutorEngineAtV35.lean](Properties/ExecutorEngineAtV35.lean) | [Proofs/ExecutorEngineAtV35.lean](Proofs/ExecutorEngineAtV35.lean) |
| ExecutorRowsUnvalidated | (uses [Specs/ExecutorForward.lean](Specs/ExecutorForward.lean)) | [Properties/ExecutorRowsUnvalidated.lean](Properties/ExecutorRowsUnvalidated.lean) | [Proofs/ExecutorRowsUnvalidated.lean](Proofs/ExecutorRowsUnvalidated.lean) |
| ExecutorUpgradeChain | [Specs/ExecutorUpgradeChain.lean](Specs/ExecutorUpgradeChain.lean) | [Properties/ExecutorUpgradeChain.lean](Properties/ExecutorUpgradeChain.lean) | [Proofs/ExecutorUpgradeChain.lean](Proofs/ExecutorUpgradeChain.lean) |
| ChainLocalExecutor | [Specs/ChainLocalExecutor.lean](Specs/ChainLocalExecutor.lean) | [Properties/ChainLocalExecutor.lean](Properties/ChainLocalExecutor.lean) | [Proofs/ChainLocalExecutor.lean](Proofs/ChainLocalExecutor.lean) |
| UpgradeTiming | [Specs/UpgradeTiming.lean](Specs/UpgradeTiming.lean) | [Properties/UpgradeTiming.lean](Properties/UpgradeTiming.lean) | [Proofs/UpgradeTiming.lean](Proofs/UpgradeTiming.lean) |
| UpgradeTimingStrong | [Specs/UpgradeTimingStrong.lean](Specs/UpgradeTimingStrong.lean) | [Properties/UpgradeTimingStrong.lean](Properties/UpgradeTimingStrong.lean) | [Proofs/UpgradeTimingStrong.lean](Proofs/UpgradeTimingStrong.lean) |
| Enabledness | [Specs/Enabledness.lean](Specs/Enabledness.lean) | [Properties/Enabledness.lean](Properties/Enabledness.lean) | [Proofs/Enabledness.lean](Proofs/Enabledness.lean) |
| DuplicateSelectorCheck | [Specs/DuplicateSelectorCheck.lean](Specs/DuplicateSelectorCheck.lean) | [Properties/DuplicateSelectorCheck.lean](Properties/DuplicateSelectorCheck.lean) | [Proofs/DuplicateSelectorCheck.lean](Proofs/DuplicateSelectorCheck.lean) |
| DiamondStorage | [Specs/DiamondStorage.lean](Specs/DiamondStorage.lean) | [Properties/DiamondStorage.lean](Properties/DiamondStorage.lean) | [Proofs/DiamondStorage.lean](Proofs/DiamondStorage.lean) |
| LiveRouting | [Specs/LiveRouting.lean](Specs/LiveRouting.lean) | [Properties/LiveRouting.lean](Properties/LiveRouting.lean) | [Proofs/LiveRouting.lean](Proofs/LiveRouting.lean) |
| DuplicateSelectorScan | [Specs/DuplicateSelectorScan.lean](Specs/DuplicateSelectorScan.lean) | [Properties/DuplicateSelectorScan.lean](Properties/DuplicateSelectorScan.lean) | [Proofs/DuplicateSelectorScan.lean](Proofs/DuplicateSelectorScan.lean) |
| GenesisWriters | [Specs/GenesisWriters.lean](Specs/GenesisWriters.lean) | [Properties/GenesisWriters.lean](Properties/GenesisWriters.lean) | [Proofs/GenesisWriters.lean](Proofs/GenesisWriters.lean) |

Namespace: `Contracts.ChainTypeManager`. Statements are
`Contracts.ChainTypeManager.Properties.*`; each certificate has the same name without
the `Properties` segment. `GenesisWriters` uses the sub-namespace
`Contracts.ChainTypeManager.GenesisWriters` (statements
`Contracts.ChainTypeManager.GenesisWriters.Properties.*`), and `ExecutorEngineAtV35` uses
`Contracts.ChainTypeManager.ExecutorEngineAtV35` likewise.

The topics after `ChainMigration` extend the first four:

- one chain at a time, and the break-glass repair: `ChainLocal`, `ChainLocalExecutor`;
- the executor's entry points: `ExecutorRowsUnvalidated`, `ExecutorUpgradeChain`, and
  `UpgradeTiming` (callers and block time);
- the executor's infrastructure leg at `d9f6789`: `ExecutorEngineAtV35`;
- liveness: `Enabledness`, `DuplicateSelectorCheck`;
- the routing guard by its code: `DiamondStorage`, `LiveRouting`, `DuplicateSelectorScan`;
- chain creation by its code: `GenesisWriters`.

Each section below says how its model relates to the one it extends. None is composed
with another unless its section says so.

## What to check

**VersionRegistry** (the CTM's `protocolVersion`, `currentRelease`, `upgradeTransition`):

- The current release is the release of the current version
  (`CurrentReleaseIsVersionsRelease`).
- The version never decreases and every edge raises it (`VersionStrictlyIncreasesOnEdges`,
  `VersionsIncreaseAlongRuns`).
- Each slot `upgradeTransition[v]` is written by at most one commit, which finds it empty
  (`CommitWritesEachSlotOnce`, `CommitWritesOnlyEmptySlots`). The slot is **not**
  write-once: `replaceUpgradeTransition` rewrites it by design and is the only other
  writer (`OnlyCommitOrReplaceWritesSlots`; the witness fires a replacement).
- Committed transitions chain: slot `v` departs from `R_v` and lands on `R_w`, and slot
  `w` departs from that `R_w` (`TransitionsChain`), through replacements too.
- The replacement path does not check that the replacement reports
  `oldProtocolVersion() == v`. That holds for genuine `CTMTransition` objects
  (`SlotsDepartFromTheirVersion`) and fails for an object that does not derive its
  versions from its releases (`NonGenuineReplacementBreaksSlotVersion`). What such a slot
  does to the executor's `upgradeChain` and to later replacements is in
  `ExecutorUpgradeChain`.

**ChainRouting** (every chain on the CTM):

- Headline: without a break-glass cut, every chain at a version `v` with a release `R_v`
  routes exactly `R_v` (`ChainsRunTheirVersionsRelease`; on a fresh CTM every chain has
  one, `FreshChainsRunTheirVersionsRelease`). Induction over genesis, migration in, the
  bootstrap reset and transitions.
- Break-glass drift cannot cross a version edge. The guard in
  `DefaultUpgrade.upgradeFromTransition` blocks the transition (`DriftBlocksTransition`).
  Every transition that runs starts on `R_v` and lands on `R_w`
  (`TransitionStartsAndLandsOnRelease`).
- The guard is load-bearing. Without it, a break-glass selector survives the transition
  (`UnguardedCutKeepsForeignSelectors`, `BreakGlassSelectorSurvivesWithoutGuard`).
  A missing selector bricks the next transition when the two releases route that
  selector differently (`MissingSelectorBricksTransition`); for an edge whose releases
  route identically it does not.

**ChainMigration** (chains leaving and coming back; extends ChainRouting):

- A chain that comes back to a settlement layer where its diamond is still registered reuses
  that diamond. `ChainAssetHandlerBase.bridgeMint` skips `ChainTypeManager.forwardedBridgeMint`
  when `contractAlreadyDeployed` (`ChainAssetHandlerBase.sol:397-417`). The return requires
  only that the diamond's version equals the CTM's (`Migrator.sol:225-229`).
- No migration step writes a diamond (`MigrationLeavesRoutingAlone`). Only a transition, the
  bootstrap reset or a break-glass cut of that chain changes a registered chain's version or
  routing (`OnlyUpgradesAndCutsWriteADiamond`).
- The headline survives migration (`ChainsRunTheirVersionsReleaseAcrossMigration`;
  `MigrationRoundTripWitness`).
- Drift is kept: a break-glass routing leaves and comes back unchanged, while a fresh arrival
  of the same chain would get the release (`DriftSurvivesMigrationRoundTrip`). Once the CTM
  commits the next edge, the returned chain can neither upgrade nor leave
  (`DriftedReturnerIsStuck`) until the CTM owner's repair cut restores its routing
  (`RepairUnsticksDriftedReturner`, topic `ChainLocal`; in the model, and in the source while
  the drifted diamond still routes `executeUpgrade`).

**ChainLocal** (one chain at a time; reuses the `ChainRouting` and `ChainMigration` steps
unchanged):

- **Per-chain headline.** If the last step writing chain `id` is not a break-glass cut, chain
  `id` runs its version's release (`ChainRunsItsVersionsRelease`). Across migration:
  `ChainRunsItsVersionsReleaseAcrossMigration`, through `MigrationRunIsARoutingRun`. A chain
  created during the run ends at a version that has a release
  (`NewChainRunsItsVersionsRelease`).
- **Why it holds.** Steps that do not write `id`, other chains' break-glass cuts included, keep
  it consistent, with no invariant needed (`StepsElsewhereKeepChainOk`). A write that is not a
  cut lands the chain on a release whatever it routed before (`NonCutWriteLandsOnRelease`).
- **Against the global headline.** It contains it (`GlobalPremiseImpliesChainLocal`). It is
  strictly more general and its premise is load-bearing (`ChainLocalWitness`: in a run with
  cuts of two chains, the chain whose last write is a transition runs its release, the other
  does not). The premise is sufficient, not necessary (`ChainLocalPremiseNotNecessary`): a cut
  can put a chain ahead of its CTM, and the CTM can later catch up to it.
- **Repair.** `repairCut` is the break-glass cut to `v` with exactly `R_v`'s routing, the
  "last step of such a recovery" of `DefaultUpgrade.sol:33-36`.
  - In the model it has a step for every registered chain, and every such step restores the
    chain (`RepairCutRestoresChainOk`). The existence half is enabledness in the model only:
    the model's break-glass step has no routing precondition, while in the source
    `executeUpgrade` enters the drifted diamond through its own dispatch
    (`DiamondProxy.sol:32-36`). `RepairStepIgnoresLiveRouting` exhibits the gap: a chain that
    routes nothing still has the repair step.
  - It is the only cut right after which a chain is on its release
    (`OnlyRepairCutsLandOnARelease`). Run level: `LastWriteDecidesTheRouting`.
  - After a repair the committed edge is enabled in the model (`RepairEnablesTransition`),
    given unique selectors in both releases. That premise cannot be dropped for an edge that
    changes the routing (`RepeatedSelectorBlocksTheEdge`, `RepairNeedsUniqueSelectors`).
  - `RepairUnsticksDriftedReturner`: after the repair, the chain of `DriftedReturnerIsStuck`
    upgrades and leaves.

**ExecutorForward** (the `CTMUpgradeExecutor` that owns the CTM and its `ProxyAdmin`,
including `UpgradeExecutorBase.forward`, `governance/UpgradeExecutorBase.sol:32-46`):

- A `forward` of calls to the CTM relates exactly the states a `ChainRouting` run relates
  and moves no proxy (`ForwardOfCtmCallsIsARun`). The CTM's checks are in the CTM, so every
  run result above applies to such forwards, under its own premises. The break-glass
  `executeUpgrade` is reachable only through `forward`.
- **Survives** along executor runs whose transactions are `Tame` (no infrastructure row
  names the CTM proxy; no forwarded break-glass cut or CTM code swap), with reinitializers
  that move at most their own proxy: `SysInv`, hence `CtmInv` and everything derived from
  it (`TransitionsChain`, `CurrentReleaseIsVersionsRelease`), the version never decreasing,
  and the routing headline (`TameRunPreservesSysInv`, `TameRunKeepsChainsOnTheirRelease`).
  The fixed entry points move a CTM-domain proxy only along a row's edge
  (`FixedEntrypointsMoveProxiesOnlyAlongRows`, for rows naming distinct proxies). This holds
  for any transition object `applyInfrastructureUpgrade` is handed, genuine or not:
  `FixedEntrypointsMoveProxiesOnlyAlongRowsAnyRows` (topic `ExecutorRowsUnvalidated`) keeps
  only `ReinitFrames`. `ExecutorAnyRowsWitness` applies an object whose rows name a proxy
  twice.
- **Does not survive**: replay safety of proxy rows. A tame `forward` of
  `CTM_PROXY_ADMIN.upgrade` moves a proxy back from `11` to `10`, which no row allows
  (`ForwardDowngradesAProxy`). **Nor** do the CTM's invariants once its code is swapped:
  one forwarded `upgradeAndCall` on the CTM proxy takes an invariant system with a chain at
  version 2 to a CTM at version 1, so the version decreased and `SysInv` fails
  (`ForwardCtmSwapBreaksInvariants`). In the model an infrastructure transition whose rows
  move the CTM proxy has the same effect; `Tame` excludes both.
- `ExecutorWitness` is a tame run that uses every entry point, including a `forward` that
  replaces a committed transition and upgrades a proxy.

**ExecutorEngineAtV35** (`applyInfrastructureUpgrade` at `draft/v0.35.0`, `d9f6789`:
`CTMUpgradeExecutor.sol:64-72` and `ProxyUpgradeExecutorBase.sol:48-98`, which delegatecall
`executeUpgrade` on the engine the transition's manifest names; over `ExecutorForward`, whose
other steps it reuses unchanged):

- **What the executor checks, whatever the engine.** After a successful leg every row's proxy
  is at its `implNew`, the executor's `owner` and `pendingOwner` are unchanged, and the domain
  holders are unchanged or the logged pair (before, after) is a collision of the hash the
  executor compares (`ExecutorChecksAfterAnyEngine`; the hash is an arbitrary function, no
  keccak property is assumed). Nothing else: an engine that only makes the calls `calls`
  succeeds exactly when `forward(calls)` does and the rows end applied
  (`EveryForwardIsAnEngineLeg`).
- **So `ExecutorForward`'s premise no longer suffices.** With "no row names the CTM proxy" as
  the only condition on an infrastructure step, the run invariants fail at `d9f6789` even for
  genuine `ProxyUpgradeTransition` objects (`TameRunsNoLongerPreserveSysInv`,
  `TameRunsNoLongerKeepChainsOnTheirRelease`, `FixedEntrypointsNoLongerMoveOnlyAlongRows`).
- **With `DefaultProxyUpgradeEngine` nothing changes.** The leg is `ExecutorForward`'s
  infrastructure step of the same object, and conversely given the checks #2654 added (the
  executor owns its `ProxyAdmin`, the engine has code, the inventory has the domain's length)
  (`DefaultEngineLegIsAnInfraStep`, `InfraStepIsADefaultEngineLeg`). The routing headline
  holds across runs whose transitions pin it (`DefaultEngineRunKeepsChainsOnTheirRelease`).
- **What must be established about any other engine** is stated as two premises; the executor
  checks neither.
  - `EngineIsTame` (every leg is a run of tame `e561b9cc2` transactions: no break-glass cut,
    the CTM proxy not moved) gives `SysInv`, the version never decreasing, the CTM proxy
    unmoved and the routing headline (`TameEngineRunIsATameExecutorRun`,
    `TameEngineRunPreservesSysInv`, `TameEngineRunKeepsChainsOnTheirRelease`).
  - `EngineReviewed` (the engine runs `DefaultProxyUpgradeEngine`'s core on the manifest's
    rows, and its two hooks make only CTM calls that are not break-glass cuts) makes the leg a
    `forward`, the `e561b9cc2` infrastructure step and a `forward`
    (`ReviewedLegIsAnExecutorRun`). For rows that do not name the CTM proxy it implies
    `EngineIsTame` (`ReviewedEngineIsTame`, `ReviewedRunKeepsChainsOnTheirRelease`,
    `DefaultEngineIsReviewed`). It also gives what the NatSpec calls source-checked swaps: a
    proxy moves only along a row's edge, for any rows
    (`ReviewedLegsMoveProxiesOnlyAlongRows`), and a stale object reverts
    (`ReviewedEngineRefusesStaleRows`, for rows naming distinct proxies).
- **Countermodels**, each with a genuine object whose rows do not name the CTM proxy and with
  every executor check passing (storage and holders unchanged):
  `CuttingEngineBreaksTheHeadline` (an `_afterSwaps` break-glass cut; not tame),
  `CtmSwappingEngineBreaksSysInv` (an `_afterSwaps` `upgradeAndCall` on the CTM proxy; not
  tame), `ProxyMovingEngineMovesAnUnnamedProxy` (tame, not reviewed),
  `DirectEngineSkipsTheSourceCheck` (an engine without `applyRows` replays a stale object the
  default engine refuses; tame, not reviewed), `BeforeHookDefeatsTheSourceCheck` (a
  `_beforeSwaps` hook puts a row's proxy on its `expectedOldImpl`; tame, not reviewed).
- `ReviewedRunWitness` meets every premise in one run: a default-engine leg, a chain created,
  a commit, an `upgradeChain`, then a leg whose reviewed subclass replaces the committed
  transition in `_afterSwaps`.
- **Read against the NatSpec** (`ICTMUpgradeExecutor.sol:33-34`, unchanged since `e561b9cc2`:
  "Applies a CTM-domain transition's source-checked implementation swaps through the bound CTM
  `ProxyAdmin`, and verifies every row at its `implNew` before returning"): the second half
  holds for every engine; the first half describes `DefaultProxyUpgradeEngine`, not the
  executor. The contract's own NatSpec (`ProxyUpgradeExecutorBase.sol:32-38`) and
  `docs/registry-driven-upgrades.md:449-453` say the engine has the executor's authority; the
  results above make that precise. This reading has had one pass, not the two-verifier check
  of the list under "Source findings".
- Not proved here: anything about the Core domain's executor, which shares
  `_applyProxyUpgradeTransition`; what an engine's calls do to ownership (the holders and the
  executor's owner are ghosts the witness engines never change, so the two ownership
  post-checks are stated but never reject in a witness); that a release's actual engine subclass meets
  `EngineReviewed`.

**ExecutorUpgradeChain** (the executor's `upgradeChain(t, id)` with its
`t.oldProtocolVersion()` lookup, `CTMUpgradeExecutor.sol:87-102`; refines `ExecutorForward`'s
bare transition step and adds the chain admin's direct `Admin.upgradeChainFromVersion`):

- **Safety is unaffected.** A successful `upgradeChain(t, id)` is `ExecutorForward`'s step: `t`
  is the slot at the chain's version, and the chain lands on `t.newProtocolVersion()`
  (`UpgradeChainRunsTheCommittedEdge`). Refined runs are executor runs
  (`RefinedRunIsAnExecutorRun`), and every executor run is a refined run whose crossings are
  `forward`s of the CTM call (`ExecutorRunsNeedNoUpgradeChain`), so both reach the same
  states. The routing headline holds whatever replacements report
  (`RefinedTameRunKeepsChainsOnTheirRelease`).
- **Liveness depends on what the slot's transition reports.** `upgradeChain` is enabled exactly
  when the chain can cross and the slot's transition reports the chain's version
  (`UpgradeChainEnabledIff`). With reporting slots it is exactly the transition step
  (`ReportingSlotsMakeUpgradeChainTheTransition`). Forwarded replacements that report their
  departing release's version keep this along tame runs
  (`GenuineReplacementsKeepUpgradeChainLive`).
- **A misreporting slot is frozen.** No commit and no replacement ever rewrites it, because
  `replaceUpgradeTransition` also finds its slot through `oldProtocolVersion()`
  (`MisreportingSlotIsFrozen`). So `upgradeChain` stays dead at that version along tame runs
  (`MisreportingSlotStaysFrozen`).
- **Countermodel** `NonGenuineReplacementBricksUpgradeChain`: a tame `forward` replacing `300`
  by `500` (which reports `7`) bricks `upgradeChain` for chain `0` at version 1 for good. The
  chain admin's direct call and a forwarded CTM call still take the chain to release `200`
  with `SysInv` intact.
- Witnesses: `ExecutorUpgradeChainWitness` (a genuine replacement `400`; the replaced `300`
  stops working at once and `upgradeChain(400, 0)` works), `MisreportingSlotWitness`
  (`replace(500, _)` reverts and a later commit leaves the slot alone).

**ChainLocalExecutor** (`ChainLocal` over `ExecutorForward`):

- An executor run whose transactions keep the CTM's code is a routing run of its routing steps
  (`ExecutorRunIsARoutingRun`; needs `ReinitFrames`).
- The per-chain headline holds across such runs, forwarded break-glass cuts included
  (`ChainRunsItsVersionsReleaseAcrossExecutorRuns`). Tame runs meet its premises
  (`TamePremiseImpliesChainLocal`).
- `ExecutorChainLocalWitness`: a forward drifts two chains, a forwarded repair follows, then
  `upgradeChain`; all three steps are enabled in the model only. `CtmSwapBreaksChainLocal`:
  the CTM-code premise is load-bearing.

**UpgradeTiming** (who may upgrade a chain across a registry transition, and when). It extends
`ChainRouting`'s transition and `ExecutorForward`'s `upgradeChain` with the caller, the block
time, the `ServerNotifier` schedule, all-batches-executed and the settlement-layer order.

- Three entry points: the diamond's `Admin.upgradeChainFromVersion` (the chain's admin, its CTM
  or its validators); the CTM's `upgradeChainFromVersion` (the CTM's owner; a `forward` of it
  is this path); the executor's `upgradeChain` (the executor's owner or the chain's admin).
  The executor's call is a CTM call by the executor, which is a diamond call by the CTM
  (`ExecutorPathIsACtmCallByTheExecutor`, `CtmPathIsADiamondCallByTheCtm`).
- `ICTMUpgradeExecutor.sol:53-54` holds. Whether the executor's call succeeds, and what it
  does, does not depend on the notifier (`ExecutorPathIgnoresNotifier`). The same holds for a
  direct call by the admin or the CTM (`AdminAndCtmSkipTheNotifier`). Any other caller is a
  validator and needs the chain's notifier entry set and reached
  (`OtherCallersNeedTheNotifier`). Only the chain's admin writes that entry, unless the whole
  notifier is replaced (`NotifierWrittenOnlyByItsChainAdmin`).
- `ICTMUpgradeExecutor.sol:48-49` ("the OWNER may upgrade any chain at any time", and the same
  for the chain's admin) is false:
  - the manifest's `upgradeTimestamp` is checked in the engine, so it gates every path and
    caller (`ManifestTimestampGates`);
  - at time 9 nobody can upgrade across an edge whose timestamp is 10; at time 10 the owner
    and the admin both can (`NotAtAnyTime`), so "possible at some time implies possible at any
    time" fails for both (`UpgradeChainIsNotTimeIndependent`);
  - every path also needs every committed batch executed and the settlement layer at the
    target version (`EveryPathNeedsExecutedBatches`, `EveryPathNeedsTheSettlementLayerAhead`);
  - the gate is read from whatever the slot holds, so a replacement can close an open gate
    again (`ReplacementMovesTheTimeGate`);
  - what the owner can do at any time is a break-glass cut (`executeUpgrade` through
    `forward`), which here is the untimed `arbitraryCut`.
- The repaired statement is `UpgradeChainEnabledIffTimed`: exactly when `upgradeChain`
  succeeds, with no notifier condition; its last conjunct is `ChainRouting`'s transition step,
  which `TransitionEnabledIff` characterizes. Once enabled, the call stays enabled as time
  passes (`UpgradeStaysEnabledLater`). In the source these conditions are necessary, not
  sufficient: further reject-only checks are omitted.
- The extension is conservative. Every timed upgrade is a `ChainRouting` transition and every
  timed run a `ChainRouting` run, so the routing headline holds along timed runs
  (`UpgradeIsATransition`, `TimedRunIsARun`, `TimedRunKeepsChainsOnTheirRelease`). An executor
  upgrade is `ExecutorForward`'s `upgradeChain` step (`TimedUpgradeChainIsAnXStep`).
  `UpgradeTiming` and `ExecutorUpgradeChain` refine that step separately and are not composed;
  `UpgradeChainEnabledIffTimed` and `UpgradeChainEnabledIff` are different statements.
- Deadline. On the deadline getter, for any CTM state: if the slot's schedule passed
  `requireValidEdge` and there is no override, at every instant the departing version is active
  or the manifest's time gate is open (`ValidEdgeHasNoDeadTime`). The time gate is only one gate
  of an upgrade. An owner override can close both (`DeadlineOverrideOpensDeadTime`).
- Deadline along runs (`UpgradeTimingStrong`). Every reachable slot has a valid schedule when
  every committed and replacement transition passed `requireValidEdge`
  (`ReachableSlotsHaveValidSchedules`). Along a timed run from `SysInv` with no break-glass cut,
  validated installs and valid schedules, a chain at a version with a committed edge, no
  override, every batch executed and its settlement layer at the target is never in dead time:
  at every instant its version is active, or its admin and the CTM's owner can both upgrade it
  (`ValidatedTimedRunsHaveNoDeadTime`). A valid schedule alone does not suffice: with the
  settlement layer behind or a batch unexecuted, a reachable chain is in dead time
  (`ValidScheduleAloneLeavesDeadTime`); an override, an invalid schedule and a break-glass cut
  each open dead time too (`NoDeadTimeNeedsItsOtherPremises`). If replacements keep the
  deadline (`_requireSameDeadline`, which the model's replacement step omits), a committed
  version's deadline never moves (`SameDeadlineReplacementsFixTheDeadline`); without it, it can
  (`ReplacementDeadlineWitness`). `NoDeadTimeWitness` meets every premise of the headline.
- Witnesses: `EachGateIsLoadBearing` shows each gate deciding a concrete step both ways.
  `UpgradeTimingWitness` is a run from a fresh CTM that upgrades three chains, one per entry
  point.

**Enabledness** (when a chain can upgrade, be deployed, or cross the bootstrap edge; the
liveness side of `ChainRouting`):

- A positive result means no check the model keeps blocks the step. The omitted reject-only
  checks are further premises of any source-level claim (listed in `Specs/Enabledness.lean`).
  Negative results transfer to the source.
- One step. A chain that is `ChainOk`, with an edge committed at its version and both releases
  listing each selector once, can cross the edge and lands on the arriving release
  (`TransitionEnabled`); nothing is assumed about other chains. Exactly when: a transition
  exists iff the edge is committed, the chain routes its version's release, and the releases
  route identically or both list each selector once (`TransitionEnabledIff`). A free id can be
  deployed, by genesis or migration in, iff the current release lists each selector once
  (`NewChainEnabled`, `NewChainEnabledIff`). The bootstrap reset exists iff the bootstrap cut is
  recorded and its genesis release lists each selector once (`BootstrapResetEnabledIff`).
- `validate()`'s duplicate check is a liveness guard. A release that lists a selector twice
  bricks its edge and the CTM's new chains (`DuplicateSelectorBricksEdge`); in the model this
  needs no break-glass cut, because the model omits `validate()`. `SysInv` alone does not make
  the departing release well-formed (`DepartingDuplicateBlocksTransition`).
- Along runs without a break-glass cut: every chain stays on a well-formed release
  (`ChainsStayOnWfReleases`); upgrades stay enabled, needing only the arriving release's check
  (`UpgradesStayEnabled`); with validated installs every committed edge can be crossed and
  every free id deployed (`ValidatedRunsKeepEverythingEnabled`); every chain behind its CTM can
  take its transition or the bootstrap reset, unless it sits behind an opaque legacy cut
  (`BehindChainsCanCatchUp`). Every starting state meets the premises
  (`StartingStatesMeetLivenessPremises`).
- These are about `ChainRouting.Step`, whose guard is the semantic one. `LiveRouting` proves
  the counting guard equal to it on consistent storage, but that a `Step` transition has a
  `DStep` counterpart (the converse of `CountedStepRefinesStep`) is not stated.
- Witnesses: `EnablednessWitness`, `CatchUpWitness`.

**DuplicateSelectorCheck** (`CTMRelease._requireNoDuplicateSelectors`, the open-addressing set
inside `validate()`):

- The check returns iff no selector repeats across a release's facets
  (`DuplicateCheckIsExact`). Any table with more slots than selectors would do
  (`DuplicateCheckExactForAnyLargerTable`), so the `2 * total + 1` sizing is for probe length.
  `ReleaseWf` is exactly this check (`ReleaseWfIsTheDuplicateCheck`).
- `DuplicateCheckWitness` exercises probing past occupied slots. `DuplicateSelectorScan`
  proves the same function exact separately, over `LiveRouting`'s rows.

**DiamondStorage** (`state-transition/libraries/Diamond.sol`: the diamond's own storage and
every writer):

- `DiamondOk` is stated position by position: each entry of `facets` and of
  `facetToSelectors[f].selectors` points back at its index; each routed selector or listed
  facet sits at its recorded index; address 0 lists nothing. In plain terms
  (`DiamondOkMeans`): no facet is listed twice; a facet is listed iff it has selectors; no
  selector is listed twice; `x ∈ facetToSelectors[f]` iff the proxy routes `x` to `f`.
- A fresh diamond satisfies it (`FreshStorageOk`). Every action keeps it, including the
  swap-and-pop in `_removeOneFunction`/`_removeFacet` (`AddFunctionsPreservesOk`,
  `RemoveFunctionsPreservesOk`, `ReplaceFunctionsPreservesOk`, `DiamondCutPreservesOk`).
- On the routing the proxy implements, `Add` is `ChainRouting.addAll` and `Remove` is
  `removeAll`, with no invariant needed (`AddFunctionsRoutes`, `RemoveFunctionsRoutes`,
  `ReplaceFunctionsRoutes`).
- The `NoFunctionsForDiamondCut` check is load-bearing (`EmptyAddBreaksOk`).
- `DiamondCutWitness` runs all three actions through both swap-and-pop branches.

**LiveRouting** (`requireReleaseRouting` by its code, and the routing system rebuilt on diamond
storage):

- Headline: on `DiamondOk` storage, and for rows whose selector lists are nonempty and
  duplicate-free (`RowsWf`, what `validate()` checks), the counting check passes iff the proxy
  routes exactly the release (`CountCheckIffExactRouting`; `CountCheckWitness`). Distinct facet
  rows follow from the premises (`ValidRowsHaveDistinctFacets`).
- Each premise is needed. A selector-less row (`EmptySelectorRowFoolsCountCheck`), a repeated
  row (`RepeatedRowFoolsCountCheck`) or inconsistent storage (`CorruptStorageFoolsCountCheck`)
  each lets a diamond that routes an extra selector pass. With a selector-less row on both
  sides of an edge, drift crosses the edge under the counting check, while the semantic guard
  refuses (`EmptySelectorRowCarriesDriftAcrossEdge`).
- `DStep` is `ChainRouting.Step` with the cuts executed by `Diamond.sol`'s code and the guard
  replaced by `CountCheck`; installing a release requires `validate()`. Every step refines
  `ChainRouting.Step` (`CountedStepRefinesStep`); the invariant `DSysInv` is kept
  (`CountedStepPreservesInvariant`) and runs refine runs (`CountedRunRefinesRun`); the headline
  is re-derived with the on-chain check passing against `R_v`
  (`ChainsRunTheirVersionsReleaseCounted`, `FreshChainsRunTheirVersionsReleaseCounted`); the
  starting states satisfy the invariant (`FreshCountedSystemSatisfiesInvariant`,
  `BootstrapCountedSystemSatisfiesInvariant`); drift cannot cross an edge
  (`CountedDriftBlocksTransition`).
- Witnesses: `CountedRoutingWitness`, `CountedBootstrapResetWitness` (exercises
  `removeAllCuts`), `CountedDriftWitness`.

**DuplicateSelectorScan** (`CTMRelease._requireNoDuplicateSelectors`, over `LiveRouting`'s
rows):

- The scan reverts iff a selector repeats, for 4-byte selectors (`DuplicateScanIffNodup`). So
  `validate()`'s facet checks as coded are `RowsWf` (`ValidateRowsIffRowsWf`), and the counting
  check is exact for every release that passed them (`CountCheckExactAfterValidate`).
- `DuplicateScanWitness` covers a home-slot collision and both duplicate shapes.

**GenesisWriters** (the code that writes a new chain's diamond: `DiamondInit`,
`Admin.genesisUpgrade` and `L1GenesisUpgrade`; `state-transition/chain-deps/DiamondInit.sol:52-150`,
`facets/Admin.sol:566-578`, `upgrades/L1GenesisUpgrade.sol:31-53`):

- **DiamondInit.** Its only diamond write is `newChainInstallations(currentRelease)`. It sets
  `s.protocolVersion = ctm.protocolVersion()` and `s.chainTypeManager = msg.sender`
  (`DiamondInitWrites`). On a new proxy the routing is exactly the release's flattened rows
  (`DiamondInitInstallsTheRelease`), resting on `Add` cuts being `ChainRouting`'s `addAll`
  (`AddCutsRefineAddAll`). It cannot run twice (`DiamondInitCannotRerun`).
- **Genesis upgrade.** The cut `Admin.genesisUpgrade` builds has no facet cuts
  (`GenesisUpgradeCutIsEmpty`). `L1GenesisUpgrade` writes no `Diamond.DiamondStorage` slot and
  writes the version back to its own value; its only write is `l2SystemContractsUpgradeTxHash`
  (`GenesisUpgradeWritesNoDiamondStorage`).
- **The genesis label is a theorem.** A code-level creation is a `Step.genesis` or
  `Step.migrateIn` (`CodeCreationIsAStep`). On a validated, genuine release creation succeeds
  (`ValidatedReleaseCreatesChains`, `ValidatedReleaseMigratesChainsIn`), and the code-level
  step and the model's step coincide (`GenesisStepIsExact`, `MigrateInStepIsExact`,
  `CodeStepIsExact`). The headline holds along runs whose creations are code-level
  (`CodeRunIsARun`, `CodeRunsKeepChainsOnTheirRelease`).
- **Load-bearing.** Genuine release members (`ForeignDiamondInitBreaksGenesis`,
  `ForeignGenesisUpgradeBreaksGenesis`), and `validate()`'s nonempty-rows check: without it the
  flattened step admits a release the code refuses (`SelectorlessRowRevertsCreation`).
- Witnesses: `GenesisWritersWitness`, `CodeRunWitness`.

Witnesses: `VersionRegistryWitness`, `ChainRoutingWitness`, `BootstrapResetWitness` and
`MigrationRoundTripWitness` are concrete runs that meet the premises. Each later topic lists
its own above.

Related folders: `../RegistryBootstrapMigration/` (who holds the CTM's authority across the
bootstrap, and what a `forward` does to it, same commit) and `../EcosystemUpgradeExecutor/`
(the staged coordinator and its timer, at the earlier commit `afa407085`; deleted by
`e561b9cc2`).

## Model boundaries

- A revert is the absence of a step. Checks that only reject and read nothing the model
  tracks are omitted. That only adds runs, so the safety results hold a fortiori.
- Release and transition objects are their getters. They are fixed functions of the
  address, because the objects are write-once.
- `relAt` is a ghost map: the release installed when the CTM reached each version.
- In `ChainRouting` and every topic built on it except `LiveRouting` and
  `DuplicateSelectorScan`, the guard `requireReleaseRouting` is modelled by its documented
  meaning ("exactly `_release`'s routing"). `LiveRouting` models it by its code over
  `DiamondStorage` and proves the two agree under `DiamondOk` and `RowsWf`; its count-checked
  system refines `ChainRouting`. Its boundaries:
  - `selectors()` is a fixed function of the facet address. `validate()` runs at install
    time, while the check re-reads `selectors()`.
  - The keccak comparison in the `deriveFacetCuts` shortcut is modelled as list equality.
  - A break-glass init may leave inconsistent diamond storage (`CountedDriftBlocksTransition`
    takes `DiamondOk` explicitly).
  - Pre-registry diamonds are assumed consistent at the bootstrap (a premise of
    `BootstrapCountedSystemSatisfiesInvariant`).
  - `ChainMigration` and `ExecutorForward` steps are not lifted to `DStep`.
- The upgrade engine named by a transition is assumed to run `DefaultUpgrade`'s logic.
  A transition's cuts are assumed to be `CTMTransition`'s derived cuts.
- In `ExecutorForward`, a CTM code swap (forwarded, or by an infrastructure row naming the
  CTM proxy) leaves the CTM's version state arbitrary; ownership transfers through
  `forward` (modelled for the authority state in `../RegistryBootstrapMigration/`, topic
  `Forward`), CTM owner functions that touch no modelled state, and calls to other targets
  are not modelled; the `ProxyAdmin`'s owner is fixed configuration.
- In `ExecutorEngineAtV35` (`d9f6789`), an engine is an arbitrary relation on the model
  state, so every engine is covered, but only its effect on `ExecutorForward`'s state (the
  CTM, its chains, the CTM domain's implementations) and on three ghosts is represented:
  the executor's `owner()`/`pendingOwner()` and the seven values `_domainHolders` hashes.
  No other step changes the ghosts, the `ProxyAdmin`'s owner the row library reads stays
  fixed configuration, and the hash is an arbitrary function. The witness engines are
  sequences of `ExecutorForward`'s forwarded calls around the row library's `applyRows`;
  engine calls that touch no modelled state (the ServerNotifier's setters, events) are
  no-ops, and `_checkPostconditions` and `onlyOwner` only reject and are omitted. `HookRun`
  admits any CTM call that is not a break-glass cut, as `forward`'s `FCall.sys` does.
- In `ExecutorUpgradeChain`, the three ways to cross an edge (`upgradeChain`, the chain
  admin's direct call, a forwarded CTM call) differ only before `Admin.upgradeChainFromVersion`.
  They run the same engine, so the omitted timing checks do not separate them, and neither
  the admin nor the CTM faces the `ServerNotifier` gate (`AdminAndCtmSkipTheNotifier`). The
  caller check of `upgradeChain` only rejects.
- **The diamond's dispatch (`DiamondProxy.sol:32-36`) is not modelled.** A call into a chain
  reverts unless the live routing sends its selector to a facet, with a route not marked
  freezable while the diamond is frozen. This check reads the routing, so it is not one of
  the checks that "read nothing the model tracks"; omitting it still only adds runs. Two
  enabledness facts depend on it:
  - the repair needs the drifted diamond still to route `executeUpgrade` to code that
    performs the cut (`RepairStepIgnoresLiveRouting`);
  - a transition needs the departing release to route `upgradeChainFromVersion`. The Admin
    facet of a release built by the deployment script does, non-freezable
    (`l1-contracts/deploy-scripts/ctm/DeployCTMUtils.s.sol:103`).
- Outside `UpgradeTiming`, callers and timing are not modelled, nor are deadlines or the
  all-batches-executed check. `UpgradeTiming` adds, for registry transitions only, callers,
  the block time, the manifest's `upgradeTimestamp`, the `ServerNotifier` gate,
  all-batches-executed and the settlement-layer order. Within it:
  - every chain's `s.chainTypeManager` is identified with the CTM (`DiamondInit.sol:91` is its
    only writer at this commit);
  - each diamond's admin, validators, batch counters and settlement layer are rewritten
    arbitrarily by `setAux`;
  - the notifier can be replaced wholesale, and its own CTM pointer is assumed to be this CTM;
  - the two owners are fixed configuration;
  - block times along a run are unordered;
  - the verifier, L2-upgrade-transaction, previous-upgrade-finalized and semver checks remain
    omitted;
  - the bootstrap crossing and break-glass cuts remain untimed;
  - stored deadline overrides are a parameter of the deadline results, not state;
  - it is not composed with `ChainMigration` or with `ExecutorForward`'s full run.
- So the positive enabledness results (`Enabledness`, `RepairEnablesTransition`,
  `ExecutorUpgradeChain`'s liveness results, the witnesses that cross an edge) are relative to
  the model: they rule out only reverts of the checks the model keeps, the guard and the
  derived cuts. Each omitted check on a path (callers, the two timestamp gates, executed
  batches, settlement-layer order, previous-upgrade finalization, the dispatch, and the rest
  listed in `Specs/Enabledness.lean`) is a further premise of a source-level claim. The one
  omitted check the model's own steps depend on is `CTMRelease.validate()`'s duplicate-selector
  check, stated as `ReleaseWf` / `Op.InstallsWf` where needed and proved to be
  `_requireNoDuplicateSelectors` (`ReleaseWfIsTheDuplicateCheck`). The label `migrateIn id`
  carries no version; the model's migration in carries the CTM's version. Only enabled steps
  are claimed, not eventual progress.
- In `GenesisWriters`:
  - a release's members are assumed to be the code they are named for (`GenuineRelease`): its
    `diamondInit()`, its genesis upgrade, and the facets that route the creation path's entry
    points;
  - `Diamond.DiamondStorage`, the reentrancy lock and `ZKChainStorage` are assumed to be
    disjoint storage regions, and only the `ZKChainStorage` fields the path reads are kept;
  - reject-only checks are omitted (callers, `onlyL1`, zero checks, SafeCast, semver checks),
    so exactness is relative to a model that accepts at least what the code accepts. In the
    code, `createNewChain` is L1-only and a fresh `forwardedBridgeMint` reverts on L1;
  - transitions, the bootstrap reset and break-glass cuts still use `ChainRouting`'s
    flattened steps.

## Source findings

Reported to the maintainer of this repo, not yet confirmed upstream. Each was checked by two
independent verifiers; only findings both upheld are listed, with the classification both
gave (and the severity, where they agreed). Paths are under `l1-contracts/contracts/` at
`e561b9cc2` unless they start at the repository root.

- *natspec-or-doc-wrong, info.* `upgrades/registry/libraries/LiveRoutingReader.sol:34-37`
  names unique rows and selectors as the precondition of `requireReleaseRouting`'s counting
  argument. It also needs every row to list at least one selector
  (`EmptySelectorRowFoolsCountCheck`, `EmptySelectorRowCarriesDriftAcrossEdge`). `validate()`
  refuses empty lists (`CTMRelease.sol:121-123`), so releases that passed it are covered
  (`CountCheckExactAfterValidate`).
- *natspec-or-doc-wrong.* The same argument assumes consistent diamond storage. A break-glass
  `executeUpgrade` whose init writes diamond storage directly can leave an orphan
  `selectorToFacet` entry that passes the guard (`CorruptStorageFoolsCountCheck`). Only the CTM
  owner can do this; a recovery made of facet cuts keeps storage consistent
  (`DiamondCutPreservesOk`).
- *natspec-or-doc-wrong.* `upgrades/registry/executors/ICTMUpgradeExecutor.sol:48-49` ("at any
  time"): refuted by `NotAtAnyTime`, `UpgradeChainIsNotTimeIndependent`,
  `EveryPathNeedsExecutedBatches`, `EveryPathNeedsTheSettlementLayerAhead`.
- *repo-doc-stale, info.* The same wording is in `docs/registry-driven-upgrades.md:658-659` and
  `protocol-docs/system/contracts/chain_management/upgrade_process.md:40-41`.
- *natspec-or-doc-wrong, info.* `ICTMUpgradeExecutor.sol:53-54` is true but easy to misread:
  the gate it skips is the per-chain `ServerNotifier` schedule, while the manifest's gate of
  the same name, `upgradeTimestamp`, is not skipped (`ExecutorPathIgnoresNotifier`,
  `ManifestTimestampGates`).
- *real-bug, low.* `ChainTypeManager.replaceUpgradeTransition` (`ChainTypeManager.sol:429-448`)
  does not check that the replacement's `oldProtocolVersion()` equals the slot it writes
  (`NonGenuineReplacementBreaksSlotVersion`). It needs governance to approve a non-genuine
  object.
- *real-bug, low.* Such a slot can never be replaced again, because the replacement is looked
  up at the version it reports (`MisreportingSlotIsFrozen`); only a CTM code swap fixes it.
- *natspec-or-doc-wrong, low.* `protocol-docs/ecosystem-upgrade-coordination.md:171` ("can be
  repaired without moving the CTM") does not hold for such a slot.
