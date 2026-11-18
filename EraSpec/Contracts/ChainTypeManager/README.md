# ChainTypeManager

Source: `l1-contracts/contracts/state-transition/ChainTypeManager.sol` and the
registry-driven upgrade objects and engines it drives
(`l1-contracts/contracts/upgrades/registry/`, `upgrades/DefaultUpgrade.sol`,
`upgrades/BootstrapUpgrade.sol`, the chain's `Admin` facet and `DiamondInit`).

That code is **not** in the pinned era-contracts tree. It lives on branch
`feat/upgrade-simplification` of the zksync-era `contracts` repository, and this model
was written against commit **`e561b9cc2`** (2026-10-19). **The branch moves**: every
`file:line` quoted in the specs is at that commit, and the results describe that commit,
not the current branch. Re-check the source before relying on them. One topic is the exception:
`MutableSelectors` cites branch `draft/v0.35.0` of era-contracts at commit `b17415d20`, and its
Specs header says where the code it reuses from the other topics sits there.
`../ProxyUpgradeRowLib/` models the row library at an older snapshot (`Rows`) and at this
commit (`RowsCurrent`, and `RowsUnvalidated` for rows no `validateRows` has checked); the
`ExecutorForward` topic below uses `RowsCurrent`, and `ExecutorRowsUnvalidated` uses
`RowsUnvalidated`.

One topic is at a different commit: `ExecutorEngineAtV35` models
`applyInfrastructureUpgrade` at branch `draft/v0.35.0`, commit **`b17415d20`** (2026-11-16),
where #2654 (`95b5c469d`) replaced the executor's own `applyTransition` by a delegatecall
into the engine the transition names. It was first written at `d9f6789` (2026-11-06) and
re-read at `b17415d20`; its Specs header lists what changed in between. Every other entry
point it uses is `ExecutorForward`'s; their bodies at `b17415d20` do what `ExecutorForward`
models (`forward` gained a code check that never rejects a modelled call). Nothing else in
this folder has been re-read there.

Two topics, `ProofGateAtV35` and `UpgradeTimingAtV35`, describe branch `draft/v0.35.0` of
`matter-labs/era-contracts` at commit **`b17415d20`** instead (first written against `d9f6789`,
re-read at `b17415d20`). That branch took this registry code by the squash-merge `ccf00623c`;
their specs list what changed on the modelled paths since then.

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
| ExecutorEngineAtV35 (`b17415d20`) | [Specs/ExecutorEngineAtV35.lean](Specs/ExecutorEngineAtV35.lean) | [Properties/ExecutorEngineAtV35.lean](Properties/ExecutorEngineAtV35.lean) | [Proofs/ExecutorEngineAtV35.lean](Proofs/ExecutorEngineAtV35.lean) |
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
| EngineGettersFaithful | [Specs/EngineGettersFaithful.lean](Specs/EngineGettersFaithful.lean) | [Properties/EngineGettersFaithful.lean](Properties/EngineGettersFaithful.lean) | [Proofs/EngineGettersFaithful.lean](Proofs/EngineGettersFaithful.lean) |
| LegacyCrossingFaithful | [Specs/LegacyCrossingFaithful.lean](Specs/LegacyCrossingFaithful.lean) | [Properties/LegacyCrossingFaithful.lean](Properties/LegacyCrossingFaithful.lean) | [Proofs/LegacyCrossingFaithful.lean](Proofs/LegacyCrossingFaithful.lean) |
| L2Derivation (pin `b17415d20`) | [Specs/L2Derivation.lean](Specs/L2Derivation.lean) | [Properties/L2Derivation.lean](Properties/L2Derivation.lean) | [Proofs/L2Derivation.lean](Proofs/L2Derivation.lean) |
| L2Convergence (pin `b17415d20`) | [Specs/L2Convergence.lean](Specs/L2Convergence.lean) | [Properties/L2Convergence.lean](Properties/L2Convergence.lean) | [Proofs/L2Convergence.lean](Proofs/L2Convergence.lean) |
| MutableSelectors | [Specs/MutableSelectors.lean](Specs/MutableSelectors.lean) | [Properties/MutableSelectors.lean](Properties/MutableSelectors.lean) | [Proofs/MutableSelectors.lean](Proofs/MutableSelectors.lean) |
| CommittedEdgeExecutable | [Specs/CommittedEdgeExecutable.lean](Specs/CommittedEdgeExecutable.lean) | [Properties/CommittedEdgeExecutable.lean](Properties/CommittedEdgeExecutable.lean) | [Proofs/CommittedEdgeExecutable.lean](Proofs/CommittedEdgeExecutable.lean) |
| UpgradeTxNonces | [Specs/UpgradeTxNonces.lean](Specs/UpgradeTxNonces.lean) | [Properties/UpgradeTxNonces.lean](Properties/UpgradeTxNonces.lean) | [Proofs/UpgradeTxNonces.lean](Proofs/UpgradeTxNonces.lean) |
| ProofGateAtV35 | [Specs/ProofGateAtV35.lean](Specs/ProofGateAtV35.lean) | [Properties/ProofGateAtV35.lean](Properties/ProofGateAtV35.lean) | [Proofs/ProofGateAtV35.lean](Proofs/ProofGateAtV35.lean) |
| UpgradeTimingAtV35 | [Specs/UpgradeTimingAtV35.lean](Specs/UpgradeTimingAtV35.lean) | [Properties/UpgradeTimingAtV35.lean](Properties/UpgradeTimingAtV35.lean) | [Proofs/UpgradeTimingAtV35.lean](Proofs/UpgradeTimingAtV35.lean) |

Namespace: `Contracts.ChainTypeManager`. Statements are
`Contracts.ChainTypeManager.Properties.*`; each certificate has the same name without
the `Properties` segment. `GenesisWriters` uses the sub-namespace
`Contracts.ChainTypeManager.GenesisWriters` (statements
`Contracts.ChainTypeManager.GenesisWriters.Properties.*`); likewise `EngineGettersFaithful`
uses `Contracts.ChainTypeManager.EngineGetters`, `LegacyCrossingFaithful` uses
`Contracts.ChainTypeManager.LegacyCrossing`, `MutableSelectors` uses
`Contracts.ChainTypeManager.MutableSelectors`, and `ExecutorEngineAtV35` uses
`Contracts.ChainTypeManager.ExecutorEngineAtV35`.
`L2Derivation` and `L2Convergence` share the sub-namespace `Contracts.ChainTypeManager.L2Tables`.
`CommittedEdgeExecutable` and `UpgradeTxNonces`
share `Contracts.ChainTypeManager.EdgeChecks`; unlike the rest of this folder they are written
against `draft/v0.35.0` commit `b17415d20`. `ProofGateAtV35` and `UpgradeTimingAtV35` use
`Contracts.ChainTypeManager.ProofGateAtV35` and `Contracts.ChainTypeManager.UpgradeTimingAtV35`;
a statement there named like an `e561b9cc2` one is that statement over the v35 system.

The topics after `ChainMigration` extend the first four:

- one chain at a time, and the break-glass repair: `ChainLocal`, `ChainLocalExecutor`;
- the executor's entry points: `ExecutorRowsUnvalidated`, `ExecutorUpgradeChain`, and
  `UpgradeTiming` (callers and block time);
- the executor's infrastructure leg at `b17415d20`: `ExecutorEngineAtV35`;
- liveness: `Enabledness`, `DuplicateSelectorCheck`;
- the routing guard by its code: `DiamondStorage`, `LiveRouting`, `DuplicateSelectorScan`;
- chain creation by its code: `GenesisWriters`.
- faithfulness repairs of the executor topics: `EngineGettersFaithful` (the engine's own
  getters), `LegacyCrossingFaithful` (pre-v35 chains crossing opaque legacy edges themselves);
- the facets' self-descriptions: `MutableSelectors` (`selectors()` answers that change, over
  `LiveRouting`).
- the chain-side checks a committed edge must pass, and the L2 upgrade transaction's nonce, at
  `b17415d20`: `CommittedEdgeExecutable` (composed with `VersionRegistry`'s CTM runs),
  `UpgradeTxNonces`.
- the second-proof-system gate at `draft/v0.35.0` (`b17415d20`): `ProofGateAtV35` (over
  `ChainRouting`) and `UpgradeTimingAtV35` (over `UpgradeTiming`).

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

**ExecutorEngineAtV35** (`applyInfrastructureUpgrade` at `draft/v0.35.0`, `b17415d20`:
`CTMUpgradeExecutor.sol:64-72` and `ProxyUpgradeExecutorBase.sol:51-104`, which delegatecall
`executeUpgrade` on the engine the transition's manifest names; over `ExecutorForward`, whose
other steps it reuses unchanged):

- **What the executor checks, whatever the engine.** Before the leg, that the CTM's `admin()` is
  not the `ProxyAdmin`; after it, every row's proxy at its `implNew`, the executor's `owner` and
  `pendingOwner` unchanged, and the domain holders unchanged or the logged pair (before, after)
  a collision of the hash the executor compares (`ExecutorChecksAfterAnyEngine`; the hash is an
  arbitrary function, no keccak property is assumed). The pre-check and each of the three
  post-checks reject some witness leg whose engine code succeeds
  (`CtmAdminPrecheckRefusesTheLeg`, `OwnershipCheckRefusesAnEngineNomination`,
  `HoldersCheckRefusesAnEngineNomination`, `RowsCheckRefusesAHookThatMovesARowProxy`), and the
  collision case is reachable when the hash does not separate the pair
  (`HoldersCollisionCaseIsReachable`). Nothing else: an engine that only
  makes the calls `calls` succeeds exactly when `forward(calls)` does and the rows end applied
  (`EveryForwardIsAnEngineLeg`, witness `EveryForwardIsAnEngineLegWitness`).
- **So `ExecutorForward`'s premise no longer suffices.** With "no row names the CTM proxy" as
  the only condition on an infrastructure step, the run invariants fail at `b17415d20` even for
  genuine `ProxyUpgradeTransition` objects (`TameRunsNoLongerPreserveSysInv`,
  `TameRunsNoLongerKeepChainsOnTheirRelease`, `FixedEntrypointsNoLongerMoveOnlyAlongRows`).
- **With `DefaultProxyUpgradeEngine` nothing changes.** The leg is `ExecutorForward`'s
  infrastructure step of the same object, and conversely given the checks the executor and
  engine now make (the executor owns its `ProxyAdmin`, the engine has code, the CTM's `admin()`
  is not the `ProxyAdmin`, the inventory has the domain's length)
  (`DefaultEngineLegIsAnInfraStep`, `InfraStepIsADefaultEngineLeg`). The routing headline
  holds across runs whose transitions pin it (`DefaultEngineRunKeepsChainsOnTheirRelease`,
  witness `DefaultEngineRunWitness`).
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
    `DefaultEngineIsReviewed`). It also gives the row library's source check at the executor:
    a proxy moves only along a row's edge, for any rows
    (`ReviewedLegsMoveProxiesOnlyAlongRows`), and a stale object reverts
    (`ReviewedEngineRefusesStaleRows`, for rows naming distinct proxies).
- **Countermodels**, each with a genuine object whose rows do not name the CTM proxy and with
  every executor check passing (ownership and holders unchanged):
  `CuttingEngineBreaksTheHeadline` (an `_afterSwaps` break-glass cut; not tame),
  `CtmSwappingEngineBreaksSysInv` (an `_afterSwaps` `upgradeAndCall` on the CTM proxy; not
  tame), `ProxyMovingEngineMovesAnUnnamedProxy` (tame, not reviewed),
  `DirectEngineSkipsTheSourceCheck` (an engine without `applyRows` replays a stale object the
  default engine refuses; tame, not reviewed), `BeforeHookDefeatsTheSourceCheck` (a
  `_beforeSwaps` hook puts a row's proxy on its `expectedOldImpl`; tame, not reviewed). The
  source documents this boundary: the engine runs with the executor's authority, and what it
  does beyond the executor's checks rests on its review (`ProxyUpgradeExecutorBase.sol:34-41`,
  `IProxyUpgradeEngine.sol:16-21`, `docs/registry-driven-upgrades.md:473-478`).
- `ReviewedRunWitness` meets every premise of the positive results in one run: a
  default-engine leg, a chain created, a commit, an `upgradeChain`, then a leg whose reviewed
  subclass replaces the committed transition in `_afterSwaps`.
- Not proved here: anything about the Core domain's executor, which shares
  `_applyProxyUpgradeTransition`; what a real engine's calls do to ownership and to the holders
  (only two witness engines write those ghosts, and no other step changes them); that a
  release's actual engine subclass meets `EngineReviewed`.

**ExecutorUpgradeChain** (the executor's `upgradeChain(t, id)` with its
`t.oldProtocolVersion()` lookup, `CTMUpgradeExecutor.sol:87-102`; refines `ExecutorForward`'s
bare transition step and adds the chain admin's direct `Admin.upgradeChainFromVersion`):

- **Safety is unaffected.** A successful `upgradeChain(t, id)` is `ExecutorForward`'s step: `t`
  is the slot at the chain's version, and the chain lands on `t.newProtocolVersion()`
  (`UpgradeChainRunsTheCommittedEdge`). Refined runs are executor runs
  (`RefinedRunIsAnExecutorRun`), and every executor run is a refined run whose crossings are
  `forward`s of the CTM call (`ExecutorRunsNeedNoUpgradeChain`), so both reach the same
  states. The routing headline holds whatever replacements report
  as `oldProtocolVersion()` (`RefinedTameRunKeepsChainsOnTheirRelease`). The model runs every
  object's derived cuts and lands on its `newProtocolVersion()`; for the getters only the
  engine reads, see `EngineGettersFaithful`.
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

**EngineGettersFaithful** (the getters `DefaultUpgrade.upgradeFromTransition` reads and the CTM
never checks: `facetCuts()` and `upgradeTarget()`, `upgrades/DefaultUpgrade.sol:30-44, 66-67`;
refines the transition step of `ExecutorUpgradeChain`):

- The derived cut list, applied action by action with `Diamond.sol`'s semantics, is
  `ChainRouting`'s `applyDerived` (`DerivedCutsAreApplyDerived`). With every committed slot
  holding an object whose two getters are what a `CTMTransition` returns (`SlotsDerived`), a
  refined step is exactly a `ChainRouting` step (`DerivedEngineStepIsAStep`), and a refined run
  that commits or installs only such objects is an `ExecutorUpgradeChain` run
  (`DerivedEngineRunIsAUpgradeChainRun`).
- **The headline with the premise explicit**: `DerivedEngineTameRunKeepsChainsOnTheirRelease`.
  No premise on what replacements report as `oldProtocolVersion()`.
- **Load-bearing.** `replaceUpgradeTransition` checks neither getter
  (`ChainTypeManager.sol:429-457`). A replacement `400` that passes every check the model keeps
  (`World.Genuine`) but adds one selector to its cuts leaves chain `0` at version 2 routing
  more than release `200` after a tame run (`ForeignCutsBreakTheHeadline`); one whose
  `upgradeTarget()` lands on 3 instead of 2 puts the chain ahead of its CTM, and after a tame
  commit to 3 the chain does not route release `250` (`ForeignTargetBreaksTheHeadline`). Both
  need the owner to commit or install a non-`CTMTransition` object.
- Witness: `EngineGettersWitness`.

**LegacyCrossingFaithful** (a pre-v35 chain's admin or validator calling the cut-taking
`Admin.upgradeChainFromVersion(_, old, cut)` on the chain's own diamond, `c67894b9`
`state-transition/chain-deps/facets/Admin.sol:494-525`, against the hash the CTM still serves,
`ChainTypeManager.sol:876-878` at `e561b9cc2`):

- A crossing writes exactly what `Step.arbitraryCut` writes (`CrossIsABreakGlassStep`), and keeps
  `SysInv` iff it lands its chain consistent with the CTM (`CrossKeepsSysInvIff`).
- **The source reading of the tame headlines is false**
  (`ChainSideCrossingBreaksTameHeadline`). A tame `forward` of `setUpgradeDiamondCut(cut, 0)`
  re-commits the bootstrap edge with an opaque cut; pre-registry chain `5` crosses it on its own
  diamond and ends at version 1 not routing release `100`. `SysInv` fails, and no tame
  `ExecutorForward` or `ExecutorUpgradeChain` run reaches that state. So
  `TameRunPreservesSysInv`, `TameRunKeepsChainsOnTheirRelease`,
  `RefinedTameRunKeepsChainsOnTheirRelease` and `TamePremiseImpliesChainLocal` hold of their
  models but not of "every run whose executor transactions are tame" once such chains act.
- **What survives.** Counting crossings as break-glass, the old conclusions stand
  (`CrossFreeRunsAreUpgradeChainRuns`, `TameRefinedRunKeepsChainsOnTheirRelease`). With every
  crossing landing consistently (a property of the opaque cut the owner committed), `SysInv`
  and the headline hold (`LandingRunPreservesSysInv`). With no premise on crossings, per chain:
  `CrossRunIsARoutingRun`, `ChainRunsItsVersionsReleaseAcrossCrossings`, and
  `ExecTamePremiseImpliesChainLocal` for every chain no crossing names. The slot results are
  unaffected (`MisreportingSlotStaysFrozenAcrossCrossings`,
  `GenuineReplacementsKeepUpgradeChainLiveAcrossCrossings`).
- Dispatch is not modelled: the step exists for every chain at an opaque edge, while in the
  source only chains still routing a v31-v34 `Admin` facet can take it. That only adds runs; the
  countermodel and witness use pre-registry chains of the bootstrap states.
- Witness: `LegacyCatchUpWitness` (a lagging pre-registry chain catches up with no owner action).

**L2Derivation** and **L2Convergence** (the L2 implementation tables; era-contracts
`draft/v0.35.0` at **`b17415d20`**, a newer pin than the topics above; `MODEL-L2-TABLES`). The
L2 analogue of `ChainRouting`: what L2 code a registry transition installs and whether chains on
one version run the same L2 code.

- **The derivation, pure** (`L2Derivation`; `CTMTransition.sol:50-143, 173-185`,
  `TransitionDerivationLib.sol:95-169`, `L2PlanLib.sol:47-82`, `L2InventoryLib.sol:48-113`). A
  successful construction deploys exactly the target table's new or changed rows (by keccak),
  each at its member's fixed address with the target shell, at distinct addresses
  (`TransitionDeploysExactlyTheChangedRows`). It has an L2 side iff it names a delegate; a changed
  row, an extra or a composer each force one (`HasL2SideIffDelegate`). A patch edge has none
  (`PatchEdgeHasNoL2Side`). An edge without one stores the empty plan and keeps the L2
  description: tables equal member by member with padding, shell and blob equal, each up to a
  named keccak clash, genesis parameters equal (`L1OnlyEdgeKeepsTheL2Description`).
- **The two table comparisons** (`changedL2Rows`, `_l2TableChanged`). "No row changed" implies
  `_l2TableChanged` is false with no hash premise; the converse holds up to an appended row
  that hashes like the empty row (`TableComparisonsAgree`), and such a clash splits them, so
  `releaseDiff()` can report an unchanged table for an edge that deploys a row
  (`EmptyRowClashSplitsTheComparisons`). OpenZeppelin L-01: there is an L1-only patch edge onto
  a table that only gained an empty row which reverts at `4e073f09b`, before the fix `9775be946`,
  for every injective table hash, and succeeds at `b17415d20` for every hash
  (`AppendedEmptyRowKeepsAnL1OnlyEdge`).
- **Boundaries.** A nonempty row never becomes empty (`NonemptyRowStaysNonempty`). A row at a
  member with no fixed address (members 14-19) can pass `CTMRelease`'s table checks
  (`FrozenRowWitness`) but can be neither added nor changed by a transition
  (`NoFixedAddressRowCannotChange`); once in a
  departing release it is frozen (`NoFixedAddressRowIsFrozen`), and no bootstrap plan onto such a
  release can be built (`BootstrapOntoNoFixedAddressRowReverts`); `FrozenRowWitness` shows all of
  it on one 27-row release. The deploy tooling fills only fixed-address members
  (`l1-contracts/deploy-scripts/upgrade/SystemContractsProcessing.s.sol:184-206`).
- **Convergence** (`L2Convergence`). Each chain gets a ghost L2 state: per address, the system
  proxy's shell and implementation row. A crossing of an L2-genuine transition with its L2
  transaction executed writes exactly the new or changed rows (`CrossingWritesExactlyTheChangedRows`).
  Headline: along runs from `L2Inv` (fresh or bootstrap starting states,
  `FreshL2SysSatisfiesInvariant`, `BootstrapL2SysSatisfiesInvariant`) with no break-glass step,
  every L2 upgrade transaction executed, every crossed transition L2-genuine and the genesis
  images of the releases the CTM records holding their tables, every chain at a version with a
  release runs that release's implementation at every member with a fixed address and a
  nonempty row, or a crossed transition's two releases have a member whose rows clash under the
  hash (`ChainsRunTheirVersionsL2Rows`); so two chains on one version agree there, however they
  got there (`ChainsOnOneVersionRunOneL2`). Replacements, skips included, are covered:
  `L2ConvergenceWitness` brings three chains onto one version by two crossings, by a skip
  replacement and by genesis; `BootstrapConvergenceWitness` takes a pre-registry chain across
  the bootstrap edge and a transition, and reads its result off the headline.
- **What does not converge, and what is needed.** The proxy shell does not converge
  (`ShellsDoNotConverge`; `TransitionDerivationLib.sol:91-94`). An unexecuted L2 transaction
  and a plan `CTMTransition` did not derive each leave a chain on its old implementation with an
  injective hash (`UnexecutedL2TxLeavesTheOldRow`, `NonGenuinePlanLeavesTheOldRow`); the CTM
  checks only that the plan's bytecodes are published (`ChainTypeManager.sol:449-452`). A
  genesis image that does not hold its release's table splits a version between a chain that
  crossed to it and one created there (`StaleGenesisImageSplitsAVersion`); nothing on L1
  checks the image.
- **Rows along CTM runs.** With no legacy commit and L2-genuine commits, nonempty rows of the
  current release stay nonempty and a row without a fixed address keeps its hash
  (`NonemptyRowsStayNonemptyAlongRegistryRuns`, `NoFixedAddressRowFrozenAlongRegistryRuns`;
  `FrozenRowAlongRunsWitness`); the legacy `setNewVersionUpgrade` can still replace it
  (`LegacyCommitMovesTheFrozenRow`).
- Model boundaries: the CTM steps are `VersionRegistry`'s, re-checked at `b17415d20`; the
  authored delegate, extras and delegatecall are assumed to write no member's proxy; a new
  chain's L2 state is its release's genesis image, checked only off chain
  (`protocol-ops/src/upgrade_verification/registry/genesis.rs:311-371`); routing, callers,
  timing and migration are not modelled; the factory-dependency cap is omitted.

**MutableSelectors** (each facet's `selectors()` answer as state; extends `LiveRouting`; cites
`draft/v0.35.0` at `b17415d20`):

- A release stores facet rows, not selectors (`upgrades/registry/RegistryTypes.sol:20-23`). Four
  readers ask the facets when they run: `validate()`, the derivation in `CTMTransition`'s
  constructor (whose cuts are stored and applied as they are by `DefaultUpgrade`), the
  installation at genesis, migration in and the bootstrap, and the guard. `World.relRows` and
  `DWorld.selectors` fix every answer for a run. Here each answer is state, changed by a step of
  its own (`setSelectors`), and each transition's cuts are what it stored when it was built.
- **With stable answers** (`StableSelectors`: no answer changes, and every transition was built
  under the starting answers) a run is a `LiveRouting` run and conversely
  (`StableRunIsACountedRun`, `CountedRunIsAStableRun`), and the headline holds
  (`ChainsRunTheirVersionsReleaseStable`, `FreshChainsRunTheirVersionsReleaseStable`,
  `StableRunIsARoutingRun`). Only the transitions a run can cross need to have been built under
  those answers (`StableSelectorsOn`; `StableOnRunIsACountedRun`,
  `ChainsRunTheirVersionsReleaseStableOn`, `StableSelectorsIsStableOn`).
- **The installing paths read answers from different times.** A crossing lands on the arriving
  release as the facets answered when the transition was built (`CrossingInstallsTheBuildAnswers`);
  a new chain gets the current release as they answer now (`CreationInstallsTheAnswersNow`); the
  guard reads the answers now (`CrossingNeedsTheAnswersNow`). On consistent storage, with the
  departing release's rows well-formed now and its facets answering as when the transition was
  built, a crossing lands on the arriving release as built, whatever the arriving release's
  facets answer (`UnchangedDepartingAnswersLandOnRelease`).
- **Load-bearing**, with genuine objects and every release passing `validate()`'s facet checks
  before and after the change:
  - one change of the arriving release's facet splits release `200`'s routing between a chain
    that crossed and one created afterwards, a state no `ChainRouting` or `LiveRouting` world
    reaches from an invariant state without a break-glass cut (`MutableSelectorsSplitRouting`);
    the next edge then refuses the chain that crossed (`MutableSelectorsBlockNextEdge`);
  - the same split happens with no change during the run when a transition was built under
    other answers (`StaleCutsSplitRouting`);
  - one change of the departing release's facet leaves that facet routed after a crossing: the
    chain is at version 2 and routes selector `5` to release `100`'s facet, a state no
    `LiveRouting` run of these objects reaches from an invariant state without a break-glass
    cut, under any fixed answers (`MutableSelectorsLeaveDepartingFacetRouted`). Before the
    crossing every condition of `UnchangedDepartingAnswersLandOnRelease` but the last holds.
- Witnesses: `StableSelectorsWitness`, `StableSelectorsOnWitness`,
  `InstallsReadDifferentAnswersWitness`.

**CommittedEdgeExecutable** (pin `b17415d20`: the commit-time checks of a registry edge,
`VersionEdgeLib.requireValidEdge` and `L2PlanLib.build`/`requirePublished`, against the chain-side
`BaseZkSyncUpgrade._setNewProtocolVersion`/`_setL2SystemContractUpgrade` and the transaction
`CTMUpgradeComposer.buildL2UpgradeTxFromPlan` composes; `upgrades/registry/libraries/VersionEdgeLib.sol:35-91`,
`L2PlanLib.sol:47-97`, `upgrades/BaseZkSyncUpgrade.sol:162-272`):

- **The two copies agree.** Both version checks reduce to `EdgeVersionShape`: construction
  passes exactly when the versions have that shape, the schedule is valid and a patch has no L2
  side; a chain's version step passes exactly when its version and the target have that shape
  and, for a minor change on the settlement layer, nothing is pending
  (`EdgeShapeIsTheChainVersionCheck`). For a plan `build` returned, the composer's empty
  transaction test is the constructor's `hasL2Side`, with no hash premise
  (`ComposerEmptinessIsHasL2Side`). A constructed edge's composed transaction has the upgrade
  type, nonce `minor(new)`, at most 64 factory dependencies and the canonical envelope
  (`ConstructedEdgeChainFacts`).
- **Headline.** `ConstructedEdgePassesChainChecks`: a constructed edge passes both chain-side
  steps on a chain at its departure on its settlement layer, with nothing pending if the minor
  changes, `priorityTxMaxPubdata` at least `90_000`, and composed calldata within
  `UpgradeCalldataFits`. Off the settlement layer only the version step runs, and it passes
  whatever is pending (`ConstructedEdgePassesOffLayerVersionStep`).
  `CommittedSlotEdgePassesChainChecks` composes this with `VersionRegistry`'s CTM runs, whose
  commit and replace steps were re-read at `b17415d20`: whatever a run with genuine replacements
  leaves in slot `v` passes on a chain at `v`. `PublishedFactoryDepsStayPublished`: what the
  commit's `requirePublished` checked stays published while the supplier's code stays.
- **The premises are needed, at their exact thresholds.** `PubdataLimitThresholdIsExact`
  (`89_999` reverts, `90_000` passes); `CalldataBoundIsExact` (composer answers of `1_799_375`
  and `1_799_376` bytes; no commit-time check bounds the composed calldata);
  `NonGenuineSlotEdgeRevertsOnChain` (a replacement reporting another departure leaves a slot
  on which every chain at its version reverts); `UnbuiltPlanBreaksEmptinessAgreement`
  (without `build`'s shape checks a patch edge passes construction and reverts on chains);
  `SupplierSwapClearsPublication` (a supplier proxy upgrade can clear a checked publication).
- Not covered: `_upgrade`'s time gate, its settlement-layer order check and the verifier
  installation (which also reads the chain's `secondProofSystemRequired`), `requireReleaseRouting`
  and the derived cuts (see `LiveRouting`), what the composer returns or whether its call
  reverts, and the transaction's execution on L2.
- Witnesses: `ConstructedEdgeWitness` (an L2-carrying minor edge, and a patch edge over a pending
  upgrade), `CommittedSlotWitness`, `SupplierWitness`.

**UpgradeTxNonces** (pin `b17415d20`: one chain's pending L2 upgrade transaction,
`l2SystemContractsUpgradeTxHash` and its batch number, across genesis, crossings on and off the
settlement layer, commit, execute, revert and migration copies, with a ghost log of the
transactions written to the hash):

- **Per step.** A crossing never overwrites a nonzero pending hash, a patch crossing leaves the
  pending upgrade alone, and a crossing that writes found nothing pending and wrote nonce
  `minor(new) > minor(old)` (`CrossingKeepsANonzeroPendingHash`,
  `PatchCrossingKeepsThePendingUpgrade`, `WritingCrossingRaisesTheMinor`).
- **Headline.** `UpgradeTxNoncesStrictlyIncrease`: from a chain before `createNewChain`
  (`NonceInitSatisfiesInvariant`), along every run whose migrations onto an existing diamond land
  at a version no lower than the one they left (`MintLandsNotBehind`), the log only grows and its
  nonces strictly increase. Logged hashes are distinct up to a `TxHashCollision` on two logged
  transactions with different nonces (`LoggedUpgradeTxHashesDistinctOrCollide`). No hash premise.
- **Needed.** `LaggingReturnRepeatsNonce`: a migration back onto a diamond behind the version the
  chain left with writes nonce `30` twice, with the same transaction. A destination deployed for
  the migration starts at the version handed over; for an existing destination nothing on chain
  relates the two CTMs' versions.
- **Increasing nonces do not rule out a skipped transaction.** `ReturnAheadSkipsAnL2Upgrade`:
  under `MintLandsNotBehind`, a diamond that crossed `0.29.0 → 0.30.0` off its settlement layer,
  where nothing is written, becomes live through a migration back, and the L2 side of that
  constructed edge is never written. With exact landings (`MintLandsExactly`) only a genesis or a
  crossing on the settlement layer moves the chain's live version
  (`ExactLandingRunsKeepTheActiveVersion`).
- Every migration step of this model reverts at `b17415d20` (`CHAIN_MIGRATIONS_ENABLED = false`,
  `common/Config.sol:320`); the model omits that check. Not modelled: break-glass cuts and
  upgrade engines older than `b17415d20`.
- Witnesses: `UpgradeTxNoncesWitness` (every kind of step; nonces 29, 30, 31),
  `ExactLandingWitness`.

**ProofGateAtV35** (`ChainRouting` with each diamond's `secondProofSystemRequired`, `verifier` and
`disabledProofSystems`, at `b17415d20`; the checks #2628 added to `Admin._executeDiamondCut` and
`BaseZkSyncUpgrade._setVerifier`, `state-transition/chain-deps/facets/Admin.sol:117-128`,
`upgrades/BaseZkSyncUpgrade.sol:133-153`, and the two writers `permanentlyRequireSecondProofSystem`
and `setProofSystemStatus`):

- A v35 step is the `e561b9cc2` step plus one condition: a transition or bootstrap crossing of a
  chain that requires its second proof system needs the arriving release's verifier to report
  multi-proof mode for mask `0` (`StepIsTheE561StepPlusTheGate`). The routing image of a v35 run
  is a `ChainRouting` run (`RunIsARun`), so the routing headline holds at v35
  (`ChainsRunTheirVersionsRelease`, `FreshChainsRunTheirVersionsRelease`,
  `ChainRunsItsVersionsRelease`). From fields with the requirement off everywhere, every
  `ChainRouting` run is the image of a v35 run in which no chain requires it
  (`E561RunsAreRunsWithoutTheRequirement`).
- Liveness gets that one premise (`TransitionEnabledIff`, `UpgradesStayEnabled`,
  `ValidatedRunsKeepEverythingEnabled`), and it cannot be dropped: in `GateStrandsRequiringChain`
  the CTM commits an edge to a release with a PLONK-only verifier, and a chain that requires its
  second proof system has no transition while a chain that does not crosses.
  `protocol-docs/interop-gating.md:43-48` at `b17415d20` describes such an edge and leaves its
  prevention to off-chain package verification. A break-glass cut that clears the requirement
  lets the chain cross (`BreakGlassClearsTheRequirement`).
- From `ProofInv`, along every v35 run, break-glass cuts included, a registered chain that
  requires its second proof system has a verifier in multi-proof mode for mask `0`
  (`RequiringChainsKeepAMultiProofVerifier`), given `DisablingNeverEnablesMultiProof`, which
  `MultiProofVerifier` and `ZKsyncOSVerifier` meet and which is needed (`MaskPremiseNeeded`).
  That is not the chain's current mode: with ZiSK switched off (in the source, by the Bridgehub
  owner) the chain is not in multi-proof mode (`RequirementDoesNotPinTheCurrentProofMode`).
- The requirement is changed only by the chain's `permanentlyRequireSecondProofSystem`, which
  sets it, and by a break-glass cut of the chain, which may set or clear it
  (`RequirementWriters`); without such a cut it stays set
  (`RequirementIsPermanentWithoutBreakGlass`). Both are about the in-tree engines.
- Witnesses: `ProofGateWitness`, `RequiringChainCanCrossWitness` (the enabledness premises with the
  gate in force), `RequirementLifecycleWitness`, `PerChainHeadlineAtV35Witness` (a run with
  break-glass cuts), `E561RunLiftWitness`.

**UpgradeTimingAtV35** (`UpgradeTiming` with the same fields and writers, and the caller of
`permanentlyRequireSecondProofSystem`: the chain's admin, on its settlement layer):

- A v35 timed step is the `e561b9cc2` timed step plus the gate of its routing step
  (`TimedStepIsTheE561StepPlusTheGate`). For a chain that does not require its second proof system
  an upgrade succeeds at v35 exactly when it does in `UpgradeTiming`
  (`UnflaggedChainsUpgradeAsAtE561`). Every `UpgradeTiming` run is the image of a v35 run
  (`E561TimedRunsAreRunsWithoutTheRequirement`), and the timed image of every v35 run is an
  `UpgradeTiming` run (`TimedRunIsATimedRun`), so `UpgradeTiming`'s necessary conditions still
  bind and its routing headline holds (`TimedRunKeepsChainsOnTheirRelease`).
- The `upgradeChain` NatSpec is unchanged at `b17415d20`. `ICTMUpgradeExecutor.sol:53-54` still
  holds (`ExecutorPathIgnoresNotifier`). `:48-49` is still false (`NotAtAnyTime`, for every proof
  world), and fails through the gate too, which binds every path, caller and time
  (`ProofGateBindsEveryPath`; `OwnerCannotUpgradeARequiringChainToAPlonkRelease`: every condition
  of `UpgradeTiming`'s repaired statement holds for the owner, and no upgrade exists). The
  repaired statement is `UpgradeChainEnabledIffTimed`, `UpgradeTiming`'s eight conditions plus the
  gate; exact for the model, necessary but not sufficient in the source.
- Along timed runs: `TimedRunIsAProofGateRun`, `TimedRunsKeepAMultiProofVerifier`; the
  requirement is set by the chain's admin on its settlement layer, and otherwise changed only by a
  break-glass cut of the chain (`TimedRequirementWriters`), and stays set without one
  (`TimedRequirementIsPermanentWithoutBreakGlass`).
- Witnesses: `UpgradeTimingAtV35Witness` (a chain that requires its second proof system upgraded
  through `upgradeChain` by its admin), `TimedRequirementWritersWitness` (the admin sets the
  requirement, the chain's validator cannot), `UnflaggedUpgradeWitness`.

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
    time, while the check re-reads `selectors()`. `MutableSelectors` drops this assumption.
  - The keccak comparison in the `deriveFacetCuts` shortcut is modelled as list equality.
  - A break-glass init may leave inconsistent diamond storage (`CountedDriftBlocksTransition`
    takes `DiamondOk` explicitly).
  - Pre-registry diamonds are assumed consistent at the bootstrap (a premise of
    `BootstrapCountedSystemSatisfiesInvariant`).
  - `ChainMigration` and `ExecutorForward` steps are not lifted to `DStep`.
- The upgrade engine named by a transition is assumed to run `DefaultUpgrade`'s logic.
  A transition's cuts are assumed to be `CTMTransition`'s derived cuts.
  `EngineGettersFaithful` makes the second assumption (and that `upgradeTarget()` lands on
  `newProtocolVersion()`) an explicit premise, `EngineDerived`, and shows it is load-bearing.
- Outside `LegacyCrossingFaithful`, a pre-v35 chain's own call of the cut-taking
  `upgradeChainFromVersion` is not an executor transaction of any topic: `ExecutorForward`
  reaches the routing label `arbitraryCut` only through a forwarded CTM call, which `Tame`
  excludes. `LegacyCrossingFaithful` adds it and says which executor headlines survive.
- In `ExecutorForward`, a CTM code swap (forwarded, or by an infrastructure row naming the
  CTM proxy) leaves the CTM's version state arbitrary; ownership transfers through
  `forward` (modelled for the authority state in `../RegistryBootstrapMigration/`, topic
  `Forward`), CTM owner functions that touch no modelled state, and calls to other targets
  are not modelled; the `ProxyAdmin`'s owner is fixed configuration.
- In `ExecutorEngineAtV35` (`b17415d20`), an engine is an arbitrary relation on the model
  state, so every engine is covered, but only its effect on `ExecutorForward`'s state (the
  CTM, its chains, the CTM domain's implementations) and on three ghosts is represented:
  the executor's `owner()`/`pendingOwner()` and the ten values `_domainHolders` reads.
  No other step changes the ghosts, the `ProxyAdmin`'s owner the row library reads stays
  fixed configuration, and the hash is an arbitrary function. The witness engines are
  sequences of `ExecutorForward`'s forwarded calls around the row library's `applyRows`, two of
  them also writing a ghost; engine calls that touch no modelled state (the ServerNotifier's setters, events) are
  no-ops, and `_checkPostconditions`, `onlyOwner` and `_domainHolders` reverting for a
  ServerNotifier the `ProxyAdmin` no longer administers only reject and are omitted. `HookRun`
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
- In `MutableSelectors`:
  - in a given state every reader gets the same answer; a facet that answers by caller, or
    otherwise differently to two reads in one state, is not modelled;
  - who can change an answer is not modelled: `setSelectors` stands for any change to the state
    a facet's code reads. Every facet in the tree declares `selectors()` `pure` with a hard-coded
    list; the readers call it through a `STATICCALL`;
  - a transition's construction is not a step: the answers it was built under are a parameter
    (`MutWorld.FrozenUnder`, `MutWorld.GenuineUnder`);
  - everything else is as in `LiveRouting`.
- In `ProofGateAtV35` and `UpgradeTimingAtV35` (`b17415d20`):
  - `getProofMode(m)` is a fixed function of the verifier and the mask, and a release's
    `verifier()` a fixed function of the release;
  - `setProofSystemStatus` is an arbitrary write of the mask; its caller rule
    (`Admin.sol:417-420`) and the zero check on a release's verifier are omitted. Callers of
    `permanentlyRequireSecondProofSystem` are modelled only in `UpgradeTimingAtV35`;
  - every break-glass cut makes the final check of the v35 `Admin` facet. A chain's own
    crossing of an opaque legacy edge runs its pre-v35 facet, which makes none; the two differ
    only for a diamond that requires its second proof system and routes a pre-v35 `Admin`
    facet;
  - the fields belong to a diamond: migration in deploys a diamond with fresh fields, and the
    results are about the diamonds registered on the one modelled CTM. `ChainMigration` and
    `ExecutorForward` steps are not lifted to v35.

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
