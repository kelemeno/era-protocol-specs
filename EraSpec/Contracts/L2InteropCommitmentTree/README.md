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
| InitOnce | [Specs/InitOnce.lean](Specs/InitOnce.lean) | [Properties/InitOnce.lean](Properties/InitOnce.lean) | [Proofs/InitOnce.lean](Proofs/InitOnce.lean) |
| PaddingAtHead (`main` `3605e82`) | [Specs/PaddingAtHead.lean](Specs/PaddingAtHead.lean) | [Properties/PaddingAtHead.lean](Properties/PaddingAtHead.lean) | [Proofs/PaddingAtHead.lean](Proofs/PaddingAtHead.lean) |
| HintSearchAtHead (`main` `70096e2`, `draft/v0.35.0` `b17415d`) | [Specs/HintSearchAtHead.lean](Specs/HintSearchAtHead.lean) | [Properties/HintSearchAtHead.lean](Properties/HintSearchAtHead.lean) | [Proofs/HintSearchAtHead.lean](Proofs/HintSearchAtHead.lean) |

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

`PaddingAtHead` models the tree at era-contracts `main` (`3605e82`), where `setup` pads
with `IMT_EMPTY_LEAF_HASH = keccak256("zkSync:IndexedMerkleTree:emptyLeaf")` and no longer
with `hashLeaf({0,0,0})` (item F-04 of commit `78e14b3bc`). Every other topic in this folder
models the pin `c67894b9`. The cited files are byte-identical at the current `main`
(`70096e2`); on draft/v0.35.0 (`d9f6789` and its current head `b17415d20`) the three library
files and the constant are the same, and `L2InteropCommitmentTree.sol` differs only in its
error imports. No property takes a hash premise; `keccak` is an arbitrary function
`List UInt8 → UInt256`, applied to the byte strings the source hashes.
- The model changes one argument of the pin's: `cSetupPad h hl ze` is `setup` with padding
  `ze`, and `CachedRoot`'s `cSetup`/`CReaches` are the instance `ze = hashLeaf({0,0,0})`
  (`PinSetupIsPadAtZeroLeafHash`). For every padding constant the storage caches the leaf
  hashes and `root()` is the published root (`CSetupPadCaches`,
  `CReachesPadRootIsPublished`, `CRunPadReaches`), and the reached list states and heights
  are `RunHeight`'s (`CReachesPadViewsAreHReaches`). `insert` is the same `cInsert`; the
  low-leaf search is unbounded at `main` (#2349), so `HintSearch`'s deployed-fuel caveat
  (`HonestInsertRevertsAtDeployedFuel`) describes the pin only.
- Headline, `NonInclusionAtHeadIsAbsentOrKeccakCollision`: on every reached state, against
  the root the contract stores, an accepted `verifyNonInclusion` means the value is absent,
  or a `KeccakBreakAtHead`: keccak collides on two different byte strings that the
  submitted proof names. The cases are a presented leaf's `abi.encode` (96 bytes) against
  the tag (34 bytes) at a padding slot, against a different stored leaf's `abi.encode` at
  an occupied slot, a node pair (64 bytes) at a named step of the path, or a wrong length
  (`LengthKeccakBreak`). `InclusionAtHeadIsPresentOrKeccakCollision` and
  `ProofsExclusiveAtHeadOrKeccakCollision` are the same for `verifyInclusion` and for a
  pair of proofs.
- The tag is the literal's UTF-8 encoding, and the preimages are separated by length and
  determine what is hashed (`ImtEmptyLeafTagIsTheLiteral`, `ImtPreimagesDomainSeparated`,
  `ImtPreimagesDetermineTheirInputs`).
- `KeccakBreakAtHead` implies `TreeRootBreak` at `main`'s hashes
  (`KeccakBreakAtHeadIsTreeRootBreak`), and for leaves whose `nextIndex` fits a `uint256`
  every `TreeRootBreak` there is one of the named keccak collisions
  (`TreeRootBreakAtHeadIsKeccakCollision`; `PathCollisionAtHeadIffKeccak`,
  `HeightBreakAtHeadIffKeccak`, `PaddingHitAtHeadIffEmptyLeafCollision`). The bound is
  needed, since the model's `nextIndex` is a natural number
  (`TreeRootBreakAtHeadNeedsNextIndexBound`). At the pin the padding case held for the zero
  leaf with no collision (`PaddingHitAtPinNeedsNoCollision`).
- Against the round-7 padding-forgery notes. `HashAssumptions`' `padNotLeaf`, false at the
  pin for every hash, is at `main` the statement that no leaf's `abi.encode` collides with
  the tag under keccak; it is satisfiable, while `HashAssumptions` as a whole stays
  unsatisfiable (`PadNotLeafAtHeadIsKeccakNonCollision`). Over contract runs at `main`, an
  accepted absence proof at a snapshot meeting `StaleSnapshot`'s abstract deadline pin
  excludes on-time delivery, or carries a `KeccakBreakAtHead`, with no premise on the
  presented leaf (`StaleWitnessAtHeadNotRedeemableOrKeccakCollision`, the `main` counterpart
  of `StaleSnapshotFaithful`'s `StaleWitnessNotRedeemableOrCollision`;
  `StaleWitnessAtHeadSatisfiable`). For every keccak that collides on `abi.encode(0,0,0)`
  and the tag, the pin's padding reclaim of a delivered value is accepted on such a run at
  `main`, and its located break is exactly the `emptyLeaf` case
  (`PaddingReclaimAtHeadLocatesEmptyLeafCollision`).
- The pin's forged proof at `main` (`PinForgeryAtHeadNeedsKeccakCollision`; the same leaf,
  index and sibling words as at the pin, `PinForgeryProofSameAtPinAndHead`): on the
  three-leaf run it is accepted exactly when keccak collides on `abi.encode(0,0,0)` and the
  tag, or on a node pair at one of its two steps. `PinForgeryAcceptedAtPinRejectedAtHead`
  gives one toy hash for which the same proof against the same tree is accepted with the
  pin's padding and rejected with `main`'s.
- Each of the four cases of `KeccakBreakAtHead` is, alone, the located break of an accepted
  forged proof on a reached state (`KeccakBreakAtHeadExactly`, `KeccakBreakAtHeadIffSomeCase`):
  `emptyLeaf` (`PinForgeryAtHeadFiresOnCollision`) and `leaf` (`LeafCollisionAtHeadFires`)
  for every keccak with the named collision, `node` (`NodeCollisionAtHeadFires`) and
  `length` (`OutOfRangeIndexAtHeadWitness`) on toy keccaks. So no case can be dropped.
- `calculateRootMemory` still does not bound the index by the leaf count. At `main` the
  tree's own siblings of an empty slot authenticate `IMT_EMPTY_LEAF_HASH`, and presenting a
  leaf there takes a collision (`OutOfRangeIndexAtHead`,
  `HonestSiblingsAcceptEntryOrPathCollision`, `OutOfRangeIndexAtHeadWitness`).
- Anti-vacuity: `PaddingAtHeadThreeLeafRun`, `NonInclusionAtHeadWitness`,
  `ContractProofsAtStoredRootAtHead` (the contract's own `merklePath` outputs are accepted
  with no break), `HonestProofNoKeccakBreakAtHead`, `PaddingAtHeadBreakPremisesSatisfiable`,
  `StaleWitnessAtHeadSatisfiable`.
- Not covered: the firing witnesses show the disjuncts are needed in the statement, not that
  keccak256 collides. `PathAccepts` omits the `_pathLength >= 256` revert, so the model
  accepts more proofs than the source. The wrapper's `_reportLeaf` hook is taken not to
  call back into the tree. That the pin's bounded search and `main`'s unbounded one reach
  the same states is argued from `SearchYieldsGuard`, not stated as a theorem. The
  stale-snapshot result uses the abstract pin `D < t (j+1)`, not `main`'s timeout branches.
  `InitOnce`'s `initL2`/caller model and `Protocol/InteropAtomicity` are still at
  `c67894b9`; only the break disjunct of their results is translated to `main`'s hashes,
  and how `main`'s `AtomicFlowManager` obtains the root it verifies against is not
  modelled.

`HintSearchAtHead` re-models `InitOnce` at the current heads (`main` `70096e2`,
`draft/v0.35.0` `b17415d`; the two cited files are unchanged since `3605e82` and `d9f6789`).
There `insert`'s low-leaf walk has no hop bound (`b8cc61203`, `IndexedMerkleTree.sol:90-93`),
read as "some finite number of hops" (`WalkSucceedsAtHead`); gas is not modelled. No hash
premise.
- On a valid tree the walk is the search with `leafCount` hops, exits, and is deterministic
  (`WalkAtHeadIsLeafCountSearch`, `WalkAtHeadTerminates`, `WalkAtHeadDeterministic`); a head
  insert is the guarded insert at the landing index, which no hint changes
  (`InsertChecksAtHeadYieldGuard`, `InsertAtHeadLandingHintIndependent`).
- On a valid tree, for a nonzero unregistered `v`, the engine's checks pass from every
  occupied hint whose value is below `v` (`InsertAtHeadEnabledIff`), so
  `HonestInsertRevertsAtDeployedFuel` has no counterpart: `HonestInsertSucceedsAtHead`. Pin
  inserts are head inserts, and a head insert passes the pin's checks from its own landing
  index (`InsertChecksAtHeadVsPin`).
- Every pin run is a head run (`PinTxRunIsTxRunAtHead`), and a head run from the predeploy with
  each hint replaced by its landing index is a pin run with the same states
  (`TxRunAtHeadIsRelabelledTxRun`, `RelabelAtHeadKeepsShape`). So `PredeployRunStates`,
  `PredeployRunReclaimableIffAbsent`, `StoredLeavesAreLeafHashes` and
  `PredeployStoredRootExclusiveOrBreak` hold at head (the `…AtHead` forms), the last for
  every padding `z0`, so for `IMT_EMPTY_LEAF_HASH`. The results from any start are re-proved
  (`InitL2AtMostOnceAtHead`, `TxRunAtHeadAppendOnly`, `TxRunAtHeadKeysMono`,
  `TxRunAtHeadFromValidIsRun`).
- Witnesses on runs the pin does not have: `StaleHintRunWitnessAtHead` (an `insert(7, 0)` six
  hops from its landing index), `StaleHintRunFromValidWitnessAtHead`, and
  `StaleHintStoredRootWitnessAtHead` (the `_nodes[0]` results, with the pin's padding
  `hl {0,0,0}`; `LevelRunAtHeadExists`); `InsertAtHeadWitness` for the insert results.

Source finding at the pin `c67894b9`, since fixed upstream (see `PaddingAtHead` above): the
tree pads empty slots with `hashLeaf({0,0,0})` (`IndexedMerkleTree.sol:47-48`), against
`FullMerkle.sol:25-26`'s warning, and `verifyNonInclusion`
(`IndexedMerkleTree.sol:153-171`) bounds the low-leaf index only by `2^pathLength`
(`Merkle.sol:133-140`), not by the leaf count. So the padding forgery is accepted against
the root the contract stores (`CThreeLeafWitness`, `PublishedRootPaddingHitFires`,
`PaddingCollisionRefundsDeliveredLeg`). Both verifiers classified it as a bug, high
severity. At `main` (`3605e82`, unchanged at `70096e2`) and on draft/v0.35.0 (`b17415d20`)
`setup` pads with `IMT_EMPTY_LEAF_HASH`; the index bound is unchanged.

Root authentication and hash assumptions have separate proofs under `../Merkle/`
and `../FullMerkle/`. Caller checks are modelled in `InitOnce`; their source
correspondence, compiled search, and dispatcher-to-model correspondence remain
implementation obligations in `../../Refinement.lean`.
