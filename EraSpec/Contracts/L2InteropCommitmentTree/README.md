# L2InteropCommitmentTree

Source: `contracts/atomic-interop/L2InteropCommitmentTree.sol`, using
`contracts/common/libraries/IndexedMerkleTree.sol` in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| Reaches | [Specs/Reaches.lean](Specs/Reaches.lean) | [Properties/Reaches.lean](Properties/Reaches.lean) | [Proofs/Reaches.lean](Proofs/Reaches.lean) |
| HintSearch | [Specs/HintSearch.lean](Specs/HintSearch.lean) | [Properties/HintSearch.lean](Properties/HintSearch.lean) | [Proofs/HintSearch.lean](Proofs/HintSearch.lean) |
| TreeRoot | [Specs/TreeRoot.lean](Specs/TreeRoot.lean) | [Properties/TreeRoot.lean](Properties/TreeRoot.lean) | [Proofs/TreeRoot.lean](Proofs/TreeRoot.lean) |
| RunHeight | [Specs/RunHeight.lean](Specs/RunHeight.lean) | [Properties/RunHeight.lean](Properties/RunHeight.lean) | [Proofs/RunHeight.lean](Proofs/RunHeight.lean) |
| CachedRoot | [Specs/CachedRoot.lean](Specs/CachedRoot.lean) | [Properties/CachedRoot.lean](Properties/CachedRoot.lean) | [Proofs/CachedRoot.lean](Proofs/CachedRoot.lean) |
| PublishedRootCommits | [Specs/PublishedRootCommits.lean](Specs/PublishedRootCommits.lean) | [Properties/PublishedRootCommits.lean](Properties/PublishedRootCommits.lean) | [Proofs/PublishedRootCommits.lean](Proofs/PublishedRootCommits.lean) |
| CommitmentTreeAtV35 (`draft/v0.35.0` `b17415d20`) | [Specs/CommitmentTreeAtV35.lean](Specs/CommitmentTreeAtV35.lean) | [Properties/CommitmentTreeAtV35.lean](Properties/CommitmentTreeAtV35.lean) | [Proofs/CommitmentTreeAtV35.lean](Proofs/CommitmentTreeAtV35.lean) |
| InitOnce | [Specs/InitOnce.lean](Specs/InitOnce.lean) | [Properties/InitOnce.lean](Properties/InitOnce.lean) | [Proofs/InitOnce.lean](Proofs/InitOnce.lean) |

The library's abstract list/order theory, insertion-guard countermodels, and
reset/sentinel properties live under `../IndexedMerkleTree/`. The wrapper model
projects into `../IndexedMerkleTree/Specs/Model.lean`; that shared use does not make the
library specification a Core module.

`Reaches` is the batch-sized step (any number of guarded inserts) and shows the
key set only grows. `HintSearch` proves the contract's insert flow yields
`InsertGuard`, that `leafCount` hops always suffice, and that the deployed
constant fuel can make an honest insert revert (a liveness caveat).
`TreeRoot` adds the root over the list state and the two verifiers as they
consume an attacker's proof: complete (no hash premise), sound under `HashAssumptions`, and a
countermodel on a real run showing `padNotLeaf` is load-bearing and **false at
the pinned commit** (the setup pads with `hashLeaf({0,0,0})`). The soundness
results take `HashAssumptions`, which `HashAssumptionsUnsatisfiable` shows no hash
meets, so they are vacuous as stated; the padding countermodels take no such
premise and stand.

The repaired forms (`ProofsExclusiveOrBreak` and the other `…OrBreak` results) take
no hash premise: the property holds, or a `TreeRootBreak` is located on the submitted
path (wrong length, a path collision, a leaf-hash collision with the opened leaf, or a
padding/domain hit). `HonestProofNoBreak` shows the break is not a tautology.

`HonestInsertRevertsAtDeployedFuel` shows the revert at the deployed
`MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5`: on an honest seven-leaf run, an insert from a valid
but distant hint reverts although a correct low leaf exists.

`RunHeight` carries `FullMerkle`'s `(_leafNumber, _height)` next to the list state, moved
by `../FullMerkle/Specs/CapacityInvariant.lean`'s `push` once in `setup` and once per
`insert`, as the source does. Along every run from `setup`, `_height` is
`fmHeight leafCount` and `leafCount ≤ 2 ^ _height` (`HReachesCapacity`, `HRunCapacity`),
so the capacity premises of `TreeRoot` are discharged at the run's own height:
`RootAfterUpdateLeafOwnHeight`, `RootAfterInsertOwnHeight`, and the headlines
`ProofsExclusiveOrBreakAtOwnHeight` / `RunRootsExclusiveOrBreakAtOwnHeight` (exclusivity
or a located break, plus break-free honest inclusion and non-inclusion proofs). The
model adds no constraint on the list run (`HRunProjects`, `RunLiftsToHRun`).
`PaddingForgeryAtOwnHeight` shows the padding forgery is live at the height the source
itself computes for `threeLeafTree`. `Wf.capacity` in `Protocol/InteropAtomicity` is
derived in that folder's `SourceHeight`.

`CachedRoot` carries the whole `FullMerkle` storage, moved by the transcribed library
calls (`../FullMerkle/` topic `CachedNodes`) where `IndexedMerkleTree.setup`/`insert` make
them. Along every run, `IndexedMerkleTree.root()` is `HState.root` at the run's own height
(`CReachesRootIsPublished`, `CRunRootIsPublished`). A guarded insert never reverts inside
`FullMerkle`, and it returns that root and the `RootAfterInsertOwnHeight` walk
(`CInsertReturnsPublishedRoot`, `CInsertReturnsTheWalk`). No `RunHeight` state or run is
lost (`HReachesLifts`, `HRunLiftsToCRun`). `ContractProofsAtStoredRoot` restates
`ProofsExclusiveOrBreakAtOwnHeight` against the stored root, with the honest proofs being
the contract's own `merklePath` outputs. `CThreeLeafWitness`: the padding forgery is
accepted against the stored root, while `merklePath(3)` reverts. Still assumed: that
compiled code executes the transcription (O7).

`PublishedRootCommits` (its Specs module only imports `RunHeight` and
`../Merkle/Specs/RootForgeryPinned.lean`) states FullMerkle's `capacity_ok_root_commits`
(vacuous: global pair-injectivity) at the run's own `_height`, with no hash premise;
capacity comes from `HReachesCapacity`.
- On every reached state, and at every step of every run, a list of `leafCount` hashes
  with the published root is the leaf-hash list, or a `TreeCollision` is located on a
  named index's path (`PublishedRootCommitsOrCollision`, `RunRootsCommitOrCollision`).
- A list of any length within `2 ^ _height` with the published root is the leaf-hash
  list, a `PaddingHit`, or a located collision (`PublishedRootCommitsAnyLengthOrBreak`,
  `RunRootsCommitAnyLengthOrBreak`).
- `PublishedRootPaddingHitFires`: for every hash, appending the padding constant to a
  reached state's leaf list keeps the published root, so the root does not commit
  `leafCount`. `PublishedRootForgeryIsLocated` fires the collision case alone.

`InitOnce` models both non-view entry points, `initL2` and `insert(value, hint)`, with
their callers (`onlyUpgrader`, `appender()`; `TxStepCallerIsRole`), from the predeploy's
all-zero storage. No hash premise.
- On the predeploy, `initL2` writes exactly `setup` (`InitL2OnPredeploy`). On an
  initialized tree it reverts for every caller (`InitL2RevertsOnceInitialized`). At most
  one `initL2` succeeds per run, and none after initialization (`InitL2AtMostOnce`,
  `NoInitL2OnceInitialized`, `NoRunFromSetupReinitializes`).
- Runs are append-only in values from any start (`TxRunAppendOnly`, `TxRunKeysMono`,
  `ResetHistoryUnreachable`); `insert` rewrites the low leaf's links by design.
- A run from the predeploy is a predeploy prefix, one `initL2` that yields `setup`, then
  a `Run` (`PredeployRunShape`). Its initialized states are Valid and reached from
  `hSetup` (`PredeployRunStates`, `PredeployRunReclaimableIffAbsent`). `RunLiftsToTxRun`
  and `TxRunFromValidIsRun` make the existing `Run` model exactly the post-init part.
- With `_nodes[0]` as a ghost of the source's writes, it equals `leafHashes` along runs
  from the predeploy (`StoredLeavesAreLeafHashes`), so exclusivity-or-break holds at the
  stored leaf fold (`PredeployStoredRootExclusiveOrBreak`; `StoredRootWitness`).
- With `IMTAlreadyInitialized` deleted, a second `initL2` after a delivery makes the
  delivered value reclaimable while present (`GuardlessReinitBreaksExclusivity`), and
  the stored fold accepts honest inclusion and non-inclusion proofs of it under every hash
  (`GuardlessReinitForgesAbsenceAtStoredRoot`). No key is ever erased
  (`GuardlessRunsKeepKeys`, `GuardlessResetHistoryUnreachable`): the guard protects the
  sentinel link, not the key set, unlike the key-erasure narrative in the header of
  `../IndexedMerkleTree/Specs/ResetAndZero.lean`.
- Out of model: proxy upgrades by the complex upgrader, who owns the
  `SystemContractProxyAdmin` (`OPS-CONFIG`).

Source finding, reported to the maintainer of this repo, not yet confirmed upstream: the
tree pads empty slots with `hashLeaf({0,0,0})` (`IndexedMerkleTree.sol:47-48`), against
`FullMerkle.sol:25-26`'s warning, and `verifyNonInclusion`
(`IndexedMerkleTree.sol:153-171`) bounds the low-leaf index only by `2^pathLength`
(`Merkle.sol:133-140`), not by the leaf count. So the padding forgery is accepted against
the root the contract stores (`CThreeLeafWitness`, `PublishedRootPaddingHitFires`,
`PaddingCollisionRefundsDeliveredLeg`). Both verifiers classified it as a bug, high
severity.

Root authentication and hash assumptions have separate proofs under `../Merkle/`
and `../FullMerkle/`. Caller checks are modelled in `InitOnce`; their source
correspondence, compiled search, and dispatcher-to-model correspondence remain
implementation obligations in `../../Refinement.lean`.

`CommitmentTreeAtV35` models the tree contract at era-contracts `draft/v0.35.0` (`b17415d20`;
the tree code is the same at `main` `70096e2`) as one machine: `InitOnce`'s two entry points
with their callers, from the predeploy's all-zero storage, acting on `CachedRoot`'s whole
`FullMerkle` storage. `insert`'s low-leaf walk is unbounded (`b8cc61203`), read as "some number
of hops exits at the written index" (`WalkExitsAtV35`), and `setup` pads with a parameter `zE`
(`IMT_EMPTY_LEAF_HASH` at v35, item F-04 of `78e14b3bc`). Gas and the leaf hook report are not
modelled. No hash premise.
- On the predeploy's storage only the upgrader's `initL2()` succeeds, and it leaves storage
  caching `hashLeaf({0,0,0})` padded with `zE` (`CInitL2AtV35OnPredeploy`); with the pin's
  constant it is `cSetup` (`CInitL2AtV35AtPinPaddingIsCSetup`).
- A run from there has no successful transaction, or exactly one successful `initL2()` with
  nothing before it, and from there on it is a `CachedRoot.CRun` (`CTxRunAtV35Shape`; with the
  pin's constant a `CRun` from `cSetup`, `CTxRunAtV35AtPinPaddingIsCRunFromCSetup`). Each
  successful insert writes at the index where `InsertGuard` holds and returns the root that
  `root()` then reads (`CTxRunAtV35InsertIsGuardedCInsert`).
- Headline, `CTxRunAtV35StoredRootIsPublished`: at every step of every run the storage is the
  predeploy's, or it caches the leaf hashes padded with `zE`, the list state is reached from
  `setup` and valid, and `root()` is the fold at the source's own `_height`. Against that root
  the contract's own `merklePath` outputs are accepted with no located break, and an accepted
  inclusion and non-inclusion proof of one value locate a `TreeRootBreak`
  (`CTxRunAtV35ContractProofsAtStoredRoot`). A path accepted at an index at or beyond the leaf
  count locates `hashLeaf(ℓ) = zE`, a node-hash collision on the path, or a wrong length
  (`CTxRunAtV35EmptySlotLocatesPadding`).
- Witnesses: `StaleHintCRunWitnessAtV35` (for every hash and padding constant, a run whose last
  insert exits six hops from its hint, which the pin's five-hop search refuses) and
  `PaddingForgeryAtV35Witness` (with the pin's constant as `zE`, the pin's padding forgery is
  accepted against the stored root of that run, and its located break is exactly `paddingHit`).
- Not covered: keccak at the byte level (whether `hashLeaf(ℓ) = IMT_EMPTY_LEAF_HASH` has a
  solution), gas, and that the leaf hook does not write the tree's storage.
