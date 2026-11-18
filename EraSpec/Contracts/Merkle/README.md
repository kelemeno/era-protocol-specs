# Merkle

Source: `l1-contracts/contracts/common/libraries/Merkle.sol`, also supporting FullMerkle and
indexed-Merkle proof verification in the pinned era-contracts tree. This is the copy
`FullMerkle` and `IndexedMerkleTree` import; the pin's
`system-contracts/contracts/libraries/Merkle.sol` differs in layout and, unlike this copy,
rejects empty paths (this copy accepts them: `ZeroLengthPathAcceptsRoot`).

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| ProofSound | [Specs/ProofSound.lean](Specs/ProofSound.lean) | [Properties/ProofSound.lean](Properties/ProofSound.lean) | [Proofs/ProofSound.lean](Proofs/ProofSound.lean) |
| RootBinding | [Specs/RootBinding.lean](Specs/RootBinding.lean) | [Properties/RootBinding.lean](Properties/RootBinding.lean) | [Proofs/RootBinding.lean](Proofs/RootBinding.lean) |
| RootForgery | [Specs/RootForgery.lean](Specs/RootForgery.lean) | [Properties/RootForgery.lean](Properties/RootForgery.lean) | [Proofs/RootForgery.lean](Proofs/RootForgery.lean) |
| Verifier | [Specs/Verifier.lean](Specs/Verifier.lean) | [Properties/Verifier.lean](Properties/Verifier.lean) | [Proofs/Verifier.lean](Proofs/Verifier.lean) |
| PathCollision | [Specs/PathCollision.lean](Specs/PathCollision.lean) | [Properties/PathCollision.lean](Properties/PathCollision.lean) | [Proofs/PathCollision.lean](Proofs/PathCollision.lean) |
| RootForgeryPinned | [Specs/RootForgeryPinned.lean](Specs/RootForgeryPinned.lean) | [Properties/RootForgeryPinned.lean](Properties/RootForgeryPinned.lean) | [Proofs/RootForgeryPinned.lean](Proofs/RootForgeryPinned.lean) |
| RootPaths | [Specs/RootPaths.lean](Specs/RootPaths.lean) | [Properties/RootPaths.lean](Properties/RootPaths.lean) | [Proofs/RootPaths.lean](Proofs/RootPaths.lean) |
| DomainSeparation | [Specs/DomainSeparation.lean](Specs/DomainSeparation.lean) | [Properties/DomainSeparation.lean](Properties/DomainSeparation.lean) | [Proofs/DomainSeparation.lean](Proofs/DomainSeparation.lean) |

`Verifier` drops `ProofSound`'s two hypotheses (occupied index, path length equal to
the tree height), which `Merkle.calculateRootMemory` does not check: an accepted
walk pins the level-0 entry at any index (padding included), and under domain
separation the accepted path length is the tree height. All four non-padded results
(`AcceptPinsEntry`, `AcceptPinsEntryCases`, `AcceptForcesHeight`,
`AcceptPinsEntryAnyLength`) take a global pair-injectivity premise `hinj`, which no
`UInt256` hash satisfies (`Contracts.InteropCommitmentTree.not_nodeInj`), so they are
vacuous as stated. The honest-walk and padded-slot results take no such premise.

`PathCollision` is the repair: an accepted path opens the tree's entry, **or** the
theorem names the level at which the verifier hashed a pair different from the tree's
pair to the same value (`AcceptPinsEntryOrCollision`, no hash premise). The collision
is pinned to the instance, and `HonestWalkNoCollision` shows it is false on the honest
path, so the disjunction is not trivially true. `AcceptForcesHeightOrBreak` and
`AcceptPinsEntryAnyLengthOrBreak` (same module) repair two more of the four.

`RootForgeryPinned` (namespace `MerkleSpec.Pinned`) finishes the repair for this folder and
for `../FullMerkle/`: every result that took global pair-injectivity has a replacement with
no hash premise, mapped one-to-one in the Properties header (`RootForgery` ×9,
`RootBinding` ×3, `ProofSound` ×3, `Verifier` ×4, FullMerkle `Model` ×7,
`CachedHashInjectivity.rootOf_inj_of_h_inj_of_on`, `TreeShape.capacity_ok_root_commits`;
four map to existing `PathCollision` results).
- Two trees with equal roots agree at a committed index, or hash different pairs to the
  same value at a named level of that index's path (`RootPinsEntryOrCollision`,
  `TreeCollision`).
- Two walks of one length from the same index with equal results used the same leaf and
  the same climbed siblings, or collide at a named step (`WalkVsWalkOrCollision`,
  `WalkCollision`). From different indices no collision is needed
  (`WalkVsWalkNeedsSameIndex`).
- Without the equal-length premise, equal roots give equal lists, a `PaddingHit` (the
  longer list holds the padding constant at the shorter one's length), or a located
  collision (`RootCommitsListOrBreak`).

Each property has a `…Satisfiable` witness; where the conclusion is "sides equal, or a
collision", a collision-free witness must have equal sides. `PinnedFormsFire`,
`RootCommitsListCollisionFires` and `PaddingHitFires` give each replacement an instance
where its original conclusion fails and the collision holds. `EqualInstancesNeverCollide`
and `RootPinsEntryPinnedToPath` show the collisions are pinned to the instance.

`DomainSeparation` (namespace `MerkleSpec.DomainSeparation`; pins `c67894b9` and, for the IMT
padding, the upgrade-system pin `e561b9cc2`) instantiates the abstract node hash, leaf hash and
padding with an arbitrary `keccak : List UInt8 → UInt256` over the source's byte preimages, whose
lengths it proves (`PreimageLengths`: node 64; log leaf 88; chain-id leaf, IMT leaf, empty entry and
commit value 96; batch leaf 128; UPG's IMT padding 34). Each domain premise, and each located
break, becomes a keccak collision on two byte strings the instance names (`HashCollision keccak x
y`). No premise on keccak except `KeccakOfEmptyIsDocumented` (one conjunct of
`EmptyConstantsCoincide`); the keccak-derived tags are parameters with nonzero premises.
- IMT: a located break of the root check is an `ImtKeccakBreak`, or, at the pin, the zero leaf
  presented at an empty slot, the padding forgery (`TreeRootBreakIsKeccakCollisionAtPin`,
  `ProofsExclusiveOrKeccakBreakAtPin`). With a padding preimage of any length other than 64 and 96,
  as UPG's, the forgery disjunct is gone (`ProofsExclusiveOrKeccakBreak`, and the single-proof
  `InclusionSoundOrKeccakBreak`, `NonInclusionSoundOrKeccakBreak`).
- Chain and shared trees: an accepted path (any length `k`, any index below `2^k`) opens an
  occupied entry with exactly the presented batch (chain-id) fields, or keccak collides on named
  strings (`ChainTreeProofOpensBatchOrKeccakBreak`, `SharedTreeProofOpensChainOrKeccakBreak`).
  The batch-leaf hop with `_verifyLastBatchInRoot`, taking the path length and mask from the prover
  as deployed, pins the last pushed batch and its three fields up to a `LastBatchKeccakBreak`
  (`DeployedLastBatchCheckOrKeccakBreak`, the keccak form of `AtomicInteropProof`
  `AcceptedLastLeafAnyLengthOrBreak`); `AcceptedLastBatchOrKeccakBreak` is the form for a path of
  the tree's height from an occupied index. The chain-id-leaf hop and the batch hop are not
  composed.
- The located node collisions of `PathCollision`, `LastLeaf` and `RootForgeryPinned` are
  equivalent to 64-byte keccak collisions (`NodeCollisionLift`, `TreeAndWalkCollisionLift`).

The witnesses meet each collision-forcing premise under a keccak model changed at one string
(`plantKeccak`), and show the collision located is that one (`ImtKeccakBreakFires`,
`ProofsExclusiveOrKeccakBreakSatisfiable`, `HeightKeccakBreakFires`, `PinnedKeccakBreakFires`,
`DeployedLastBatchPaddedEntryFires`); honest proofs carry no break for every keccak
(`HonestProofNoKeccakBreak`, `ImtKeccakBreakNotTautology`, `DeployedLastBatchCheckWitness`, the
last on three batches at height 2 with the zero check exercised). The trees are the `rootOf` fold;
the chain trees' `DynamicIncrementalMerkle` storage has no transcription here (O7). Re-read at
`main` `70096e2ea` and `draft/v0.35.0` `b17415d20`: the cited preimages, constants, tree writes and
last-batch check are unchanged there, and the IMT padding is UPG's (Specs, "Current heads").

The tree levels and walk definitions are in `../FullMerkle/Specs/Model.lean`; capacity,
padding, and cached-hash properties are alongside that model. A pure root theorem
does not alone prove that contract storage, proof indices, and hash inputs
represent those same leaves. `../FullMerkle/` topic `CachedNodes` proves it for a
statement-by-statement transcription of the library's storage; that compiled code
executes the transcription remains obligation O7 in `../../Refinement.lean`.

`RootPaths` (era-contracts `b17415d20`, `draft/v0.35.0`; the file is unchanged at `main`
`70096e2ea`) models `calculateRootPaths` (`Merkle.sol:79-122`), the range proof
`PriorityTree.processBatch` checks against the priority tree's historical roots
(`../PriorityTree/`). No hash premise anywhere.
- The checks accept exactly two paths of one length `P < 256`, at least one item, and a range
  `[s, s + n)` ending at or below `2^P` (`RootPathsAcceptIff`); with empty paths only one item
  at index 0, returned as the root (`RootPathsEmptyPathIsTheItem`). The `MerklePathEmpty` check
  changes only the revert reason (`RootPathsEmptyCheckOnlyChangesReason`).
- The loop writes its levels into the caller's array in place. It reads and writes only in-range
  indices (`RootPathsReadsInBounds`), computes what a level-by-level computation into fresh
  lists computes (`RootPathsInPlaceIsLevelByLevel`), and leaves the array at its length with
  entry 0 the root and the entries from the first level's `nextLevelLen` on untouched
  (`RootPathsFrame`; `RootPathsClobbersItems` shows the rest is overwritten).
- A tree's own paths for the range's ends and its entries `[s, s + n)` as items (padding beyond
  the leaves) return the tree's root (`RootPathsComplete`).
- Each item's walk up the stream `rangeSib` (its neighbour inside the range, or a path entry at
  the ends) reaches the returned root, hashing the loop's own pairs (`RootPathsIsItemWalks`,
  `RootPathsWalkPairsAreLoopPairs`). So the single-leaf extractors apply per item: the items are
  the tree's entries `[s, s + n)`, or some item's walk has a `PathCollision`
  (`RootPathsSoundOrCollision`); each item's walk used the tree's siblings, path entries included,
  or has a `PathCollision` (`RootPathsSiblingsPinnedOrCollision`); at a path length other than the
  tree's height every item's walk
  has a `HeightBreak` (`RootPathsAnyLengthOrBreak`; `calculateRootPaths` does not know the
  height and `processBatch` does not check it).
- `RootPathsHonestNoBreak` shows neither break holds on an honest proof, for every hash;
  `RootPathsCollisionFires` (a reordered range accepted under the order-blind `sumHash`) and
  `RootPathsWrongLengthFires` (too short and too long) show each is reached;
  `RootPathsHonestWitness` meets the premises on a concrete proof.
