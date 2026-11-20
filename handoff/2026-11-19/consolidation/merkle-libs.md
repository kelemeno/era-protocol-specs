# Consolidation inventory: the Merkle libraries (unit `merkle-libs`)

Branch `consol9/merkle-libs`, from `claude/proof-round-9` at `1ad0078`. Target commit: era-contracts
`draft/v0.35.0` head `b17415d20`. Folders: `EraSpec/Contracts/Merkle`, `EraSpec/Contracts/FullMerkle`,
`EraSpec/Contracts/DynamicIncrementalMerkle`. At the branch point they hold 305 of the 4535 property
statements, none tagged.

Concurrent wave-2 units (not touched here): atomic-proof (`AtomicInteropProof`), asset-router
(`AssetRouterBase`).

## What earlier round-9 units did here

`git log claude/proof-round-9 -- <the three folders>` shows only round-8 merges and the `imt` unit's
review fix. The `imt` unit (`imt.md`) re-pinned `IndexedMerkleTree` and `L2InteropCommitmentTree` and
says of these libraries only that `FullMerkle.sol` and `Merkle.sol` are identical at `d9f6789`,
`3605e82` and `70096e2ea`; it left `DynamicIncrementalMerkle` untouched. The `roots` unit left the
MessageRoot `Aggregation` model unbridged to `FullMerkle` (`roots.md`). So all three folders are
consolidated here.

## Source check

At `b17415d20` the libraries are `l1-contracts/contracts/common/libraries/Merkle.sol` (141 lines),
`FullMerkle.sol` (127), `DynamicIncrementalMerkle.sol` (171) and `DynamicIncrementalMerkleMemory.sol`.
Compared with the other local pins (`git show <pin>:<path> | diff - <b17415d20 file>`):

| File | `d9f6789` | `70096e2ea` (`main`) | `c67894b9` (interop pin) |
|---|---|---|---|
| `Merkle.sol`, `FullMerkle.sol` | identical | identical | not in the local clone |
| `DynamicIncrementalMerkle.sol` | identical | `reset` returns the unassigned `initialRoot` (`:68`) | not in the local clone |
| `DynamicIncrementalMerkleMemory.sol` | identical | `push`/`pushLazy` return name `index`, one-line signature | not in the local clone |

`c67894b9` is not reachable from the local clone (its interop code is the `ad-atomic-interop` feature
line). Earlier rounds recorded these files there as equal to `main`; that is kept as their record, not
re-checked.

Every `file:line` cited for the libraries in the folders' Specs headers was re-read against the
`b17415d20` tree: `Merkle.sol:27-44, 53-70, 79-122, 125-131, 133-140`; `FullMerkle.sol:23-35, 41-66,
73-94, 99-101, 107-126`; `DynamicIncrementalMerkle.sol:40-170`; the memory library's lines as the
MemoryLazy header gives them for `b17415d20`. They were written against `c67894b9` and are the same
lines at `b17415d20`, except where the DIM headers already said so. The citations of other contracts
(`MessageRootBase`, `MessageHashing`, `AtomicInteropProof`, `IndexedMerkleTree`, `Config.sol`) in
`ChainTreeBacking`, `DomainSeparation`, `RootForgeryPinned(Strong)` and `TreeShapeStrong` were pin
lines; step 1 re-cites them at `b17415d20`.

**Logic differences between the pin and `b17415d20` that matter here.** One: the IMT padding.
`IndexedMerkleTree.setup` at `b17415d20` passes `IMT_EMPTY_LEAF_HASH =
keccak256("zkSync:IndexedMerkleTree:emptyLeaf")` (`common/Config.sol:141`, a 34-byte preimage) to
`FullMerkle.setup` (`IndexedMerkleTree.sol:51`) and pushes `hashLeaf({0,0,0})` as the sentinel
(`:52`); the pin passed `hashLeaf({0,0,0})` to both. It is the upgrade-system pin `e561b9cc2`'s
padding ("UPG" in `DomainSeparation`). The DIM `reset` difference does not change the returned value
(`bytes32(0)`).

## Topics

"Importers" are modules outside the three folders that import the topic (grep of all of `EraSpec`,
`Protocol` included). All abstract layers are parameterised over the node hash `h`, so none is tied
to a pin except through its citations.

### Merkle (`Merkle.sol`)

| Topic | Commit modelled (verified) | Model | Importers | Decision |
|---|---|---|---|---|
| Verifier | none cited; `calculateRootMemory` `:53-70` | `walkPure` (in `FullMerkle/Specs/Model`), `honestSibs` | AtomicInteropProof LastLeaf; L2InteropCommitmentTree TreeRoot | canonical verifier walk; cite `b17415d20`. Its four `global-hinj` results stay, vacuous and untagged |
| PathCollision | none cited | `walkPair`, `treePair`, `PathCollision`, `HeightBreak` over `walkPure` | ChainBatchRootTree Layout; AtomicInteropProof LastLeaf; L2InteropCommitmentTree TreeRoot; MessageVerification StatusProof; Protocol InteropAtomicity Refund (proofs) | canonical located-collision layer; cite `b17415d20` |
| ProofSound, RootBinding, RootForgery | none cited | statements over `walkPure`/`rootOf`, no own model | none | keep, cite `b17415d20`. All their results are `global-hinj` (vacuous), each replaced in `RootForgeryPinned` |
| RootForgeryPinned | `c67894b9` lines, identical at `b17415d20` | `TreeCollision`, `WalkCollision`, `LevelCollision`, `PaddingHit` over `rootOf`/`walkPure` | MessageRoot Model; L2InteropCommitmentTree PublishedRootCommits | **re-pin**. "Pinned" means "the collision is pinned to the instance", not a pin record: the statements hold for the library at every commit. Not History |
| RootForgeryPinnedStrong | `c67894b9` lines, identical at `b17415d20` | `PaddingExtension` | none | **re-pin**. Its one pin-specific sentence (IMT padding = sentinel) is rewritten as what `b17415d20` does, the pin's version marked as the pin's |
| RootPaths | `b17415d20` (`:79-122`) | `calculateRootPaths` transcription | PriorityTree SegmentBinding | canonical; nothing to do |
| DomainSeparation | `c67894b9` (+ `e561b9cc2` for the IMT padding) | keccak instance over byte preimages | none | **re-pin** the length table and constants to `b17415d20` lines. The statements whose content is the pin's IMT padding go to **History** (below) |

### FullMerkle (`FullMerkle.sol`)

| Topic | Commit modelled (verified) | Model | Importers | Decision |
|---|---|---|---|---|
| Model | none cited | the fold `zeros`/`levelUp`/`levels`/`rootOf`, `walkPure`, `appendPath` | everything above; L2MessageVerification Verification | canonical abstract layer; cite `b17415d20` |
| CachedNodes | `c67894b9` lines, identical at `b17415d20` | statement-by-statement storage transcription, with `Represents` linking it to `rootOf` | MessageRoot Model; L2InteropCommitmentTree CachedRoot | **canonical storage model**; re-pin |
| CapacityInvariant | none cited | `TreeDims`, the counter rule `push` | MessageRoot; L2InteropCommitmentTree RunHeight | layer of CachedNodes (`pushNewLeaf` moves the counters by `push`); cite `b17415d20`, drop the stale "deployed rule not modelled" remark |
| CachedHashInjectivity, TreeShape | none cited | statements over `rootOf` | none | keep, cite `b17415d20` (one `global-hinj` result each, vacuous, untagged) |
| TreeShapeStrong | `c67894b9` lines, identical at `b17415d20` | statements over `rootOf` | none | re-pin; rewrite the IMT-padding sentence as for RootForgeryPinnedStrong |

One FullMerkle model: the fold is the specification, CachedNodes the storage transcription, and the
refinement between them is CachedNodes' `ReachableRepresents`/`ReachableRootIsFold`, already proved.
There is no other transcription (MessageRoot and L2InteropCommitmentTree import CachedNodes).

### DynamicIncrementalMerkle (`DynamicIncrementalMerkle.sol`, `DynamicIncrementalMerkleMemory.sol`)

| Topic | Commit modelled (verified) | Model | Importers | Decision |
|---|---|---|---|---|
| Model | `c67894b9`, lines identical at `b17415d20` | storage transcription `PushTree`, `push`, `Run`, `Represents` | none (DIM topics only) | **canonical**; re-pin to `b17415d20` |
| MemoryLazy | `c67894b9`; lines from `:150` are `+3` at `b17415d20` | memory transcription; `MemoryMatchesStorage` links it to Model | none | re-pin; a second library (the memory one), linked by its own refinement lemma |
| ChainTreeBacking | `c67894b9` lines for MessageRootBase, MessageHashing, AtomicInteropProof | `ChainTrees` over DIM runs; bridges to `Timeout.RootBacking` and `LastLeafFaithful` | none | re-pin the citations; keep (model bridge, untagged) |

**Duplicate model.** `Contracts.PriorityTree.Library.PushTree` (`PriorityTree/Specs/Library.lean`,
consolidated by `smalls-l1`) is a second transcription of the same `Bytes32PushTree` and `push`. Step
2 adds a refinement lemma in this folder (`PriorityTreeBridge`): within the `uint256` range its
`push` is the canonical `push` on the same storage, with the same root. The PriorityTree model is
kept: it is another unit's folder, and its reading of the `uint256` limits is finer.

`MessageRoot`'s `MODEL-MR-DIM` keeps chain trees as leaf lists with an uninterpreted root. It is not
a transcription and is left to the MessageRoot follow-up (`roots.md`).

## History

Merkle `DomainSeparation`, the Merkle-level record of the H2 padding finding (the IMT-level record is
`IndexedMerkleTree/History`): `PinPaddingIsEmptyPre`, `HashAssumptionsFieldsUpToCollision`,
`HashAssumptionsFieldsWitness`, `TreeRootBreakIsKeccakCollisionAtPin`,
`ProofsExclusiveOrKeccakBreakAtPin`, `InclusionSoundOrKeccakBreakAtPin`,
`NonInclusionSoundOrKeccakBreakAtPin`, `PaddingForgeryIsTheOnlyKeccakFreeBreak`. They move to
`Merkle/History/{Properties,Proofs}/DomainSeparationPinned.lean`, namespace
`MerkleSpec.DomainSeparation.History`. The current forms (any padding preimage of another length,
which `b17415d20`'s is) stay: `TreeRootBreakIsKeccakCollision`, `ProofsExclusiveOrKeccakBreak`,
`InclusionSoundOrKeccakBreak`, `NonInclusionSoundOrKeccakBreak`, and the byte facts
`ImtPreEqEmptyPreIff`, `EmptyConstantsCoincide`.

Nothing else is a pin record: every other result is abstract in the node hash or about code that is
the same at `b17415d20`.

## Not done here (by decision)

* The `global-hinj` results (28 in the two folders, `ASSUMPTIONS.md` "Results whose premises cannot
  hold") are kept, untagged, as the `imt` unit kept the vacuous `HashAssumptions` results. Each has a
  replacement in `RootForgeryPinned`/`PathCollision`.
* `DomainSeparation.L2Log` is a third copy of the `L2Log` struct (with `ChainBatchRootTree` and
  `MessageHashing`); merging them is the `roots.md` follow-up.
