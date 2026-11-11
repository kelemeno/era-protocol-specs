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
`../ProxyUpgradeRowLib/` models an older snapshot of the same branch and is not updated
here.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those
exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| VersionRegistry | [Specs/VersionRegistry.lean](Specs/VersionRegistry.lean) | [Properties/VersionRegistry.lean](Properties/VersionRegistry.lean) | [Proofs/VersionRegistry.lean](Proofs/VersionRegistry.lean) |
| ChainRouting | [Specs/ChainRouting.lean](Specs/ChainRouting.lean) | [Properties/ChainRouting.lean](Properties/ChainRouting.lean) | [Proofs/ChainRouting.lean](Proofs/ChainRouting.lean) |
| ChainMigration | [Specs/ChainMigration.lean](Specs/ChainMigration.lean) | [Properties/ChainMigration.lean](Properties/ChainMigration.lean) | [Proofs/ChainMigration.lean](Proofs/ChainMigration.lean) |

Namespace: `Contracts.ChainTypeManager`. Statements are
`Contracts.ChainTypeManager.Properties.*`; each certificate has the same name without
the `Properties` segment.

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
  versions from its releases (`NonGenuineReplacementBreaksSlotVersion`).

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
  (`DriftedReturnerIsStuck`).

Witnesses: `VersionRegistryWitness`, `ChainRoutingWitness`, `BootstrapResetWitness` and
`MigrationRoundTripWitness` are concrete runs that meet the premises.

Related folders: `../RegistryBootstrapMigration/` (who holds the CTM's authority across the
bootstrap, same commit) and `../EcosystemUpgradeExecutor/` (the staged coordinator and its
timer, at the earlier commit `afa407085`; deleted by `e561b9cc2`).

## Model boundaries

- A revert is the absence of a step. Checks that only reject and read nothing the model
  tracks are omitted. That only adds runs, so the safety results hold a fortiori.
- Release and transition objects are their getters. They are fixed functions of the
  address, because the objects are write-once.
- `relAt` is a ghost map: the release installed when the CTM reached each version.
- The guard `requireReleaseRouting` is modelled by its documented meaning ("exactly
  `_release`'s routing"). Its counting implementation is not re-proved.
- The upgrade engine named by a transition is assumed to run `DefaultUpgrade`'s logic.
  A transition's cuts are assumed to be `CTMTransition`'s derived cuts.
- Callers and timing are not modelled. Upgrade timestamps, deadlines and the
  all-batches-executed check are not modelled either.
