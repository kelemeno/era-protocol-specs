# ChainTypeManager

Source: era-contracts branch `draft/v0.35.0`, commit **`b17415d20`**. Paths are under
`l1-contracts/contracts/`. The folder models `state-transition/ChainTypeManager.sol`, the
registry-driven upgrade objects and engines it drives (`upgrades/registry/`,
`upgrades/DefaultUpgrade.sol`, `upgrades/BootstrapUpgrade.sol`), the `CTMUpgradeExecutor` that owns
it, and the parts of a chain's diamond those touch (the `Admin` facet's upgrade entry points,
`DiamondInit`, `Diamond.sol`). One topic also reads older code: `LegacyCrossingFaithful` reads the
pre-v35 chain-side `Admin` facet at `c67894b9`, which a chain that has not crossed to v35 still
runs.

Namespace `Contracts.ChainTypeManager`. A statement `….Properties.X` is proved by the theorem `….X`.
Several topics use a sub-namespace (`ProofGateAtV35`, `UpgradeTimingAtV35`, `ExecutorEngineAtV35`,
`PendingL2UpgradeAtV35`, `GenesisWriters`, `EngineGetters`, `LegacyCrossing`, `MutableSelectors`,
`EdgeChecks`, `L2Tables`); each Specs header names it.

## Headline guarantees

Each item is a Lean statement about `b17415d20` behaviour. "In the model" means that reverts of the
checks the model omits are not ruled out (see *Model boundaries*): an existence result is then a
necessary condition at the source, while a safety result holds a fortiori.

**The CTM's version registry** (`VersionRegistry`, over every run of the CTM's writers):

1. `CurrentReleaseIsVersionsRelease`: from a state satisfying the CTM invariant, `currentRelease` is
   never zero and its `protocolVersion()` is the CTM's `protocolVersion`.
2. `VersionsIncreaseAlongRuns`: no premise. The CTM's version never decreases, and strictly
   increases if the run commits an edge (registry or legacy commit).
3. `CommitWritesEachSlotOnce`: no premise. Each slot `upgradeTransition[v]` is committed at most
   once in any run (`replaceUpgradeTransition` is the only other writer).
4. `TransitionsChain`: in every state satisfying the CTM invariant, the transition in slot `v`
   departs from version `v`'s release and lands on a later version `w`, not ahead of the CTM, on
   `w`'s release; slot `w`, if filled, departs from exactly that release.

**Every chain runs its version's release** (`ProofGateAtV35`: the routing system with the
second-proof-system gate):

5. `ChainsRunTheirVersionsRelease`: premises: the start state satisfies the system invariant (the
   CTM invariant, and every chain is not ahead of the CTM and routes its version's release), and
   the run has no break-glass cut (the CTM owner's `executeUpgrade`). Then every chain at a version
   `v` for which the CTM has a release `R_v` routes exactly `R_v`, and `R_v` is a release of
   version `v`. `FreshChainsRunTheirVersionsRelease` is the same from a freshly initialized CTM,
   with no invariant premise.
6. `ChainRunsItsVersionsRelease`: per chain, with weaker premises: the CTM invariant holds at the
   start, chain `id` is consistent at the start, and the last step of the run that writes chain
   `id` is not a break-glass cut (cuts of other chains are allowed). Then chain `id` is not ahead
   of the CTM and routes its version's release, if the CTM has one.
7. `DriftBlocksTransition`: under the CTM invariant, a chain whose routing is not exactly its
   version's release cannot cross the committed edge (the guard `requireReleaseRouting` of
   `DefaultUpgrade.upgradeFromTransition`).
8. `TransitionEnabledIff` (in the model): under the CTM invariant, a registered chain can cross
   iff an edge is committed at its version, it routes its version's release, the edge's two
   releases route identically or both pass the duplicate-selector check, and, if the chain requires
   its second proof system, the arriving release's verifier reports multi-proof mode.
   `ValidatedRunsKeepEverythingEnabled` (in the model): after a run with no break-glass cut, from
   an invariant state whose recorded releases pass the duplicate check, in which every installed
   release passes it, every chain with a committed edge can cross it (given the same verifier
   condition if it requires its second proof system) and every free chain id can be created.

**The second-proof-system requirement** (`ProofGateAtV35`, #2628):

9. `RequiringChainsKeepAMultiProofVerifier`: premises: no verifier enters multi-proof mode by
   having proof systems disabled (`DisablingNeverEnablesMultiProof`; `MultiProofVerifier` and
   `ZKsyncOSVerifier` meet it), and at the start every chain that requires its second proof system
   has a verifier in multi-proof mode. Then along every run, break-glass cuts included, every chain
   that requires its second proof system has a verifier that reports multi-proof mode for the empty
   mask.
10. `RequirementIsPermanentWithoutBreakGlass`: no other premise. Along a run with no break-glass cut
    of chain `id`, a chain that requires its second proof system still requires it at the end.

**Who may upgrade a chain, and when** (`UpgradeTimingAtV35`: the timed system with the gate):

11. `UpgradeChainEnabledIffTimed` (in the model): `CTMUpgradeExecutor.upgradeChain(t, id)` by
    `caller` at block time `τ` succeeds iff: the caller is the executor's owner or the chain's
    admin; `t` is committed at its old version; the executor owns the CTM; the chain is at `t`'s
    old version; `τ` is at least the manifest's `upgradeTimestamp`; every committed batch is
    executed; the settlement layer, if any, is at least at `t`'s new version; the routing step
    exists; and, if the chain requires its second proof system, `t`'s new release's verifier
    reports multi-proof mode. The `ServerNotifier` schedule plays no part
    (`ExecutorPathIgnoresNotifier`).
12. `ManifestTimestampGates`, `EveryPathNeedsExecutedBatches`,
    `EveryPathNeedsTheSettlementLayerAhead`, `ProofGateBindsEveryPath`: no premise. Every upgrade of
    a chain, by any path, caller and block time, happens at or after the manifest's
    `upgradeTimestamp`, with every committed batch executed and the settlement layer (if any) at
    least at the edge's target; for a chain that requires its second proof system it installs the
    arriving release's verifier, which reports multi-proof mode.
13. `OtherCallersNeedTheNotifier`: no premise. A direct `upgradeChainFromVersion` by anyone other
    than the chain's admin and the CTM is by one of the chain's validators, at or after a nonzero
    time its `ServerNotifier` holds for the version.
14. `ValidatedTimedRunsHaveNoDeadTime` (in the model): premises: the run starts from an invariant
    state whose recorded releases pass the duplicate check and whose committed slots have valid
    schedules (a nonzero deadline not before the upgrade time); it has no break-glass cut, installs
    only releases that pass the duplicate check and commits only valid schedules. At its end take a
    chain with a committed edge, no stored deadline override, every committed batch executed, the
    settlement layer (if any) at least at the edge's target, and, if it requires its second proof
    system, a multi-proof arriving verifier. Then at every block time the chain's version is still
    active or both the admin's direct upgrade and the CTM owner's upgrade succeed.
15. `PendingL2UpgradeAtV35.PendingTxBlocksEveryUpgrade`: no premise beyond the situation: a chain
    on its settlement layer with a pending L2 upgrade transaction or a recorded upgrade batch, whose
    next edge changes the minor version, cannot be upgraded by any path, caller or time.
    `NoDeadTimeWithoutPendingTx` is item 14 for the model with the pending transaction (without the
    gate), with two more premises: nothing is pending or the edge is a patch, and a patch edge has
    no L2 side.

**The executor's infrastructure leg** (`ExecutorEngineAtV35`: `applyInfrastructureUpgrade` through
the engine the transition names, #2654):

16. `ExecutorChecksAfterAnyEngine`: no premise. Whatever the engine, after a successful leg the
    transition object and its engine have code, the object is of the CTM domain with an inventory
    of that domain's length, the CTM's `admin()` was not the `ProxyAdmin`, every row's proxy is at
    its new implementation, the executor's owner and pending owner are unchanged, and the domain
    holders are unchanged up to a collision of the hash the check compares.
17. `TameEngineRunKeepsChainsOnTheirRelease`: premises: each reinitializer moves at most its own
    proxy (`ReinitFrames`); the start state satisfies the system invariant; every transaction is
    tame (no forwarded break-glass cut or CTM swap, no infrastructure row naming the CTM proxy); and
    every infrastructure transition pins a tame engine (`EngineIsTame`: its effect is that of tame
    executor transactions; governance must check this, the executor does not). Then every chain
    routes its version's release, as in item 5. `ReviewedRunKeepsChainsOnTheirRelease` and
    `DefaultEngineRunKeepsChainsOnTheirRelease` replace `EngineIsTame` by the reviewable
    `EngineReviewed` and by "the engine is `DefaultProxyUpgradeEngine`";
    `ChainRunsItsVersionsReleaseAcrossEngineRuns` is the per-chain form (item 6).

**Chain creation and the routing guard, by their code**:

18. `GenesisWriters.CodeRunsKeepChainsOnTheirRelease`: premises: address zero has no code; every
    release the CTM records is genuine (its `diamondInit()`, genesis upgrade and facets are the code
    they are named for); the start state satisfies the system invariant; and the run has no
    break-glass cut, with chain creation run as the `DiamondInit` and `L1GenesisUpgrade` code. Then
    every chain routes its version's release.
19. `LiveRouting.CountCheckIffExactRouting`: premises: the diamond's storage is consistent
    (`DiamondOk`), every row of the release lists at least one selector, and no selector appears
    twice across the rows. Then `requireReleaseRouting`'s counting check passes iff the proxy
    routes exactly the release. `ChainsRunTheirVersionsReleaseCounted` is item 5 with the guard by
    its code.
20. `DuplicateSelectorCheck.ReleaseWfIsTheDuplicateCheck`: premise: the model's flattened routing
    of a release lists the facets' `selectors()` in row order. Then the model's `ReleaseWf` holds iff
    `CTMRelease._requireNoDuplicateSelectors` returns.

**Edges, the L2 upgrade transaction and the L2 side**:

21. `CommittedEdgeExecutable.CommittedSlotEdgePassesChainChecks`: premises: a CTM run from an
    invariant state whose slots report their own version, in which every replacement reports its
    departing release's version; at the end slot `v` holds a transition built by `CTMTransition`'s
    constructor, whose getters report that construction. Then on a chain at `v` on its settlement
    layer, with nothing pending if the minor version changes, `priorityTxMaxPubdata` at least
    `90_000` and composed calldata within the bound, the storage part of `_upgrade` succeeds and
    lands the chain on the edge's target.
22. `UpgradeTxNonces.UpgradeTxNoncesStrictlyIncrease`: premises: the chain starts in a state
    satisfying `NonceInv` (for example before `createNewChain`), and every migration onto an existing
    diamond lands at a version not behind the one the chain left with (`MintLandsNotBehind`). Then
    the L2 upgrade transactions the chain writes form an append-only log with strictly increasing
    nonces.
23. `L2Derivation.TransitionDeploysExactlyTheChangedRows`: no premise beyond a successful
    `CTMTransition` construction. Its plan deploys a system proxy exactly for each fixed-address row
    that is new or changed, at pairwise distinct addresses.
24. `L2Convergence.ChainsOnOneVersionRunOneL2`: premises: an invariant start state, no break-glass
    cut, every L2 upgrade transaction executed, every crossed transition derived by the
    constructor, and every recorded release's genesis image holding its table. Then two chains on
    the same version run the same implementation at every fixed address with a nonempty row,
    however each got there, unless the run crosses a transition with a row hash clash.

Countermodels show that a premise above is needed or that a stronger reading fails; witnesses show
that the premises can hold together. Each Properties header lists them.

## How the models fit together

Each row is one model. Every "restated from" link is a proved refinement or simulation, and the
results of the lower layer are restated over the upper one, mostly under the same names (each
Properties header lists them).

| Layer | Model (topic) | Restated from |
|---|---|---|
| CTM version state | `VersionRegistry` (`CTM`, `CStep`) | |
| Routing of every chain | `ProofGateAtV35` (`Sys35`, `Step35`) | `ChainRouting`, `ChainLocal`, `Enabledness` (`StepIsTheUngatedStepPlusTheGate`, `RunIsARun`) |
| Executor | `ExecutorEngineAtV35` (`V35Step`) | `ExecutorForward`, `ChainLocalExecutor`, `ExecutorUpgradeChain` (`DefaultEngineLegIsAnInfraStep`, `TameEngineRunIsATameExecutorRun`) |
| Callers and time | `UpgradeTimingAtV35` (`TimedStep35`) | `UpgradeTiming`, `UpgradeTimingStrong`, `ProofGateAtV35` (`TimedStepIsTheUngatedStepPlusTheGate`, `TimedRunIsAProofGateRun`) |
| Pending L2 upgrade | `PendingL2UpgradeAtV35` (`PStep`) | `UpgradeTiming` (`PendingRunIsATimedRun`); `UpgradeTimingAtV35` without the requirement (`PendingRunIsAGatedRunWithoutTheRequirement`) |
| Guard and storage by code | `DiamondStorage`, `LiveRouting` (`DStep`), `DuplicateSelectorScan`, `MutableSelectors` | `ChainRouting` (`CountedRunRefinesRun`, `StableRunIsACountedRun`) |
| Creation by code | `GenesisWriters` (`CodeStep`) | `ChainRouting` (`CodeStepIsExact`) |
| Executor entry points, faithfully | `ExecutorUpgradeChain` (`UStep`), `EngineGettersFaithful`, `LegacyCrossingFaithful`, `ExecutorRowsUnvalidated` | `ExecutorForward` |
| Edge checks and L2 tables | `CommittedEdgeExecutable`, `UpgradeTxNonces`, `L2Derivation`, `L2Convergence` | `VersionRegistry` |
| The duplicate-selector check | `DuplicateSelectorCheck` | `Enabledness` |

The `b17415d20` models are defined over gate-free layers that stay as their projections:
`ChainRouting` (with `ChainLocal`, `ChainMigration`, `Enabledness`), `ExecutorForward` (with its
default engine, and `ChainLocalExecutor`) and `UpgradeTiming` (with `UpgradeTimingStrong`). Other
folders import them. They describe `b17415d20` exactly for chains that do not require their second
proof system (`UngatedRunsAreRunsWithoutTheRequirement`, `UnflaggedChainsUpgradeAsUngated`) and for
infrastructure legs that pin `DefaultProxyUpgradeEngine`. `ChainMigration` has no gated
counterpart: chain migration is disabled at `b17415d20` (`CHAIN_MIGRATIONS_ENABLED = false`,
`common/Config.sol:320`), so it describes runs the production source does not take.

Every topic has `Specs/<Topic>.lean`, `Properties/<Topic>.lean` and `Proofs/<Topic>.lean`
(`ExecutorRowsUnvalidated` reuses `ExecutorForward`'s Specs). Each Specs header quotes the code it
transcribes, with its lines.

## Model boundaries

- A revert is the absence of a step. Checks that only reject and read nothing the model tracks are
  omitted. That only adds runs, so safety results hold a fortiori and existence results are "in
  the model". The Specs headers list the omitted checks; `Specs/Enabledness.lean` lists those on
  the transition path.
- Release and transition objects are their getters, fixed functions of the address (the objects
  are write-once). `relAt` is a ghost map: the release installed when the CTM reached each version.
- Outside `LiveRouting`, `DuplicateSelectorScan` and `MutableSelectors`, the guard
  `requireReleaseRouting` is modelled by its documented meaning; `LiveRouting` proves the two agree
  for consistent storage and well-formed rows. `selectors()` is a fixed function of the facet,
  except in `MutableSelectors`.
- The chain-side engine a transition names runs `DefaultUpgrade`/`BootstrapUpgrade`, and a
  transition's cuts are its derived cuts; `EngineGettersFaithful` makes both explicit premises and
  shows they are needed. The executor's infrastructure engine is arbitrary in
  `ExecutorEngineAtV35`.
- The diamond's dispatch (`DiamondProxy.sol:32-36`) is not modelled. A repair needs the drifted
  diamond still to route `executeUpgrade` (`RepairStepIgnoresLiveRouting`), and a transition needs
  the departing release to route `upgradeChainFromVersion`.
- Callers, block time, deadlines and the executed-batches check are modelled only in the timed
  layers. There each diamond's admin, validators, batch counters and settlement layer are written
  by `setAux` (by their real writers in `PendingL2UpgradeAtV35`), the two owners are fixed, and
  block times along a run are unordered.
- `getProofMode` is a fixed function of the verifier and the mask, `setProofSystemStatus` is an
  arbitrary write of the mask, and every break-glass cut makes the v35 `Admin` facet's final check.
- `GenesisWriters` assumes releases are genuine (`GenuineRelease`) and the diamond's storage
  regions disjoint. It models `Admin._executeDiamondCut`'s second-proof-system check.
- The assumption register rows for this folder are the `MODEL-CTM-*` rows of
  [`ASSUMPTIONS.md`](../../../ASSUMPTIONS.md).

## Source findings

Reported to the maintainer of this repo, not yet confirmed upstream. Each was checked by two
independent verifiers; only findings both upheld are listed, with the classification both gave.
Paths are at `b17415d20`.

- *natspec-or-doc-wrong, info.* `upgrades/registry/libraries/LiveRoutingReader.sol:34-37` names
  unique rows and selectors as the precondition of `requireReleaseRouting`'s counting argument. It
  also needs every row to list at least one selector (`EmptySelectorRowFoolsCountCheck`,
  `EmptySelectorRowCarriesDriftAcrossEdge`). `validate()` refuses empty lists
  (`CTMRelease.sol:134-136`), so releases that passed it are covered
  (`CountCheckExactAfterValidate`).
- *natspec-or-doc-wrong.* The same argument assumes consistent diamond storage. A break-glass
  `executeUpgrade` whose init writes diamond storage directly can leave an orphan
  `selectorToFacet` entry that passes the guard (`CorruptStorageFoolsCountCheck`). Only the CTM
  owner can do this; a recovery made of facet cuts keeps storage consistent
  (`DiamondCutPreservesOk`).
- *natspec-or-doc-wrong.* `upgrades/registry/executors/ICTMUpgradeExecutor.sol:48-49` ("at any
  time"): refuted by `NotAtAnyTime`, `UpgradeChainIsNotTimeIndependent`,
  `EveryPathNeedsExecutedBatches`, `EveryPathNeedsTheSettlementLayerAhead`.
- *repo-doc-stale, info.* The same wording is in `docs/registry-driven-upgrades.md:762-764` and
  `protocol-docs/system/contracts/chain_management/upgrade_process.md:40-41` (repository root).
- *natspec-or-doc-wrong, info.* `ICTMUpgradeExecutor.sol:53-54` is true but easy to misread: the
  gate it skips is the per-chain `ServerNotifier` schedule, while the manifest's `upgradeTimestamp`
  is not skipped (`ExecutorPathIgnoresNotifier`, `ManifestTimestampGates`).
- *real-bug, low.* `ChainTypeManager.replaceUpgradeTransition` (`ChainTypeManager.sol:424-443`)
  does not check that the replacement's `oldProtocolVersion()` equals the slot it writes
  (`NonGenuineReplacementBreaksSlotVersion`). It needs governance to approve a non-genuine object.
- *real-bug, low.* Such a slot can never be replaced again, because the replacement is looked up
  at the version it reports (`MisreportingSlotIsFrozen`); only a CTM code swap fixes it.
- *natspec-or-doc-wrong, low.* `protocol-docs/ecosystem-upgrade-coordination.md:180` ("can be
  repaired without moving the CTM") does not hold for such a slot.
