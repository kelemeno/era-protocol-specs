# Merkle

Source: `l1-contracts/contracts/common/libraries/Merkle.sol` at era-contracts `draft/v0.35.0`
`b17415d20`: `calculateRoot`/`calculateRootMemory` (:27-70), `calculateRootPaths` (:79-122),
`efficientHash` (:125-131) and the single-proof checks (:133-140). This is the copy `FullMerkle` and
`IndexedMerkleTree` import. The tree a proof is checked against is the `FullMerkle` fold
(`../FullMerkle/Specs/Model.lean`); the storage that holds it is `../FullMerkle/` topic `CachedNodes`.

## Headline guarantees

Every statement holds for every node hash `h` (no collision-resistance premise); a failure of the
binding property is reported as a collision located on the instance. Where a root is "the tree's
root", it is the `FullMerkle` fold `rootOf` of the tree's level-0 entries: for stored trees that is
obligation O7, proved for the transcribed `FullMerkle` storage (`../FullMerkle/`) and the
`DynamicIncrementalMerkle` storage (`../DynamicIncrementalMerkle/`).

- `MerkleSpec.Verifier.Properties.AcceptPinsEntryOrCollision`: a single proof that
  `calculateRootMemory` accepts against the tree's root opens the tree's entry at the index (padding
  included), or the verifier hashed a pair different from the tree's to the same value at a named
  level. Premises: any padding; the index is below `2^k` for the path length `k`; the walk from the
  claimed leaf equals the root at height `k`.
- `MerkleSpec.Verifier.Properties.AcceptForcesHeightOrBreak`: an accepted path of any length has the
  tree's height, or exhibits a located `HeightBreak`. Premises: the index is below `2^k`; the walk
  equals the tree's root at some height.
- `MerkleSpec.Pinned.Properties.RootPinsEntryOrCollision`: two trees with equal roots at a height
  agree at every index below `2^height`, or collide at a named level of that index's path. Premises:
  the two folds at that height are equal; the index is below `2^height`.
- `MerkleSpec.RootPaths.Properties.RootPathsAcceptIff`: `calculateRootPaths` returns exactly when the
  two paths have one length `P < 256`, there is at least one item, and the range ends at or below
  `2^P`. Premises: none beyond the transcription (lengths and indices as naturals).
- `MerkleSpec.RootPaths.Properties.RootPathsSoundOrCollision`: if `calculateRootPaths` returns the
  tree's root at height `pathLength`, the items are the tree's entries of the range, or some item's
  walk has a located collision. Premises: the returned value is the fold at the path length.
- `MerkleSpec.DomainSeparation.Properties.ProofsExclusiveOrKeccakBreak`: against the IMT root, an
  accepted inclusion proof and an accepted non-inclusion proof for one value mean that keccak
  collides on two byte strings the theorem names. Premises: `keccak` is any function; the padding
  preimage is neither 64 nor 96 bytes long (`b17415d20`'s `IMT_EMPTY_LEAF_HASH` is 34,
  `UpgPaddingLengthOk`); the tree is a `Valid` indexed list with every stored and presented leaf's
  `nextIndex` below `2^256`; the root is the fold of its leaf hashes.
- `MerkleSpec.DomainSeparation.Properties.DeployedLastBatchCheckOrKeccakBreak`: a batch-leaf path that
  passes the deployed walk and `_verifyLastBatchInRoot`, with the prover's own length and mask,
  opens the last pushed batch with exactly the presented fields, or keccak collides on named bytes.
  Premises: `keccak` and `BATCH_LEAF_PADDING` arbitrary; `n ≤ 2^height` pushed batch leaves; the chain
  root is their fold at `height` with empty entry `keccak(new bytes(96))`. Scope: the chain-id-leaf
  hop above the chain root is not composed with it.

## Topics

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Verifier | [Specs/Verifier.lean](Specs/Verifier.lean) | [Properties/Verifier.lean](Properties/Verifier.lean) | [Proofs/Verifier.lean](Proofs/Verifier.lean) |
| PathCollision | [Specs/PathCollision.lean](Specs/PathCollision.lean) | [Properties/PathCollision.lean](Properties/PathCollision.lean) | [Proofs/PathCollision.lean](Proofs/PathCollision.lean) |
| RootForgeryPinned | [Specs/RootForgeryPinned.lean](Specs/RootForgeryPinned.lean) | [Properties/RootForgeryPinned.lean](Properties/RootForgeryPinned.lean) | [Proofs/RootForgeryPinned.lean](Proofs/RootForgeryPinned.lean) |
| RootForgeryPinnedStrong | [Specs/RootForgeryPinnedStrong.lean](Specs/RootForgeryPinnedStrong.lean) | [Properties/RootForgeryPinnedStrong.lean](Properties/RootForgeryPinnedStrong.lean) | [Proofs/RootForgeryPinnedStrong.lean](Proofs/RootForgeryPinnedStrong.lean) |
| RootPaths | [Specs/RootPaths.lean](Specs/RootPaths.lean) | [Properties/RootPaths.lean](Properties/RootPaths.lean) | [Proofs/RootPaths.lean](Proofs/RootPaths.lean) |
| DomainSeparation | [Specs/DomainSeparation.lean](Specs/DomainSeparation.lean) | [Properties/DomainSeparation.lean](Properties/DomainSeparation.lean) | [Proofs/DomainSeparation.lean](Proofs/DomainSeparation.lean) |
| ProofSound | [Specs/ProofSound.lean](Specs/ProofSound.lean) | [Properties/ProofSound.lean](Properties/ProofSound.lean) | [Proofs/ProofSound.lean](Proofs/ProofSound.lean) |
| RootBinding | [Specs/RootBinding.lean](Specs/RootBinding.lean) | [Properties/RootBinding.lean](Properties/RootBinding.lean) | [Proofs/RootBinding.lean](Proofs/RootBinding.lean) |
| RootForgery | [Specs/RootForgery.lean](Specs/RootForgery.lean) | [Properties/RootForgery.lean](Properties/RootForgery.lean) | [Proofs/RootForgery.lean](Proofs/RootForgery.lean) |

- **Verifier, PathCollision.** The walk `walkPure` is the loop of `calculateRootMemory`, which checks
  neither the tree's height nor that the index is occupied. An accepted walk pins the level-0 entry
  at any index (padding included) or locates a `PathCollision`; at a wrong length it locates a
  `HeightBreak` (`ZeroLengthPathAcceptsRoot`: the empty path at index 0 accepts the root itself).
  Honest walks carry neither (`HonestWalkRoot`, `HonestWalkNoCollision`, `HeightBreakNotTautology`).
- **RootForgeryPinned(Strong).** The located-collision forms of tree versus tree (`TreeCollision`),
  walk versus walk (`WalkCollision`) and level versus level (`LevelCollision`), and the padding case
  `PaddingHit`; "Pinned" means the collision is pinned to the instance. Each has a `…Satisfiable`
  witness, and `PinnedFormsFire`, `PaddingHitFires`, `RootCommitsListCollisionFires` show the
  collision is reached. The Strong form restricts the padding case to padding extensions.
- **RootPaths.** `calculateRootPaths`, the priority tree's range proof (`../PriorityTree/`): the
  in-place loop is the level-by-level computation, an honest range proof returns the root, and each
  item's walk is a single-leaf walk, so the extractors above apply per item.
- **DomainSeparation.** The abstract hashes instantiated with an arbitrary keccak over the source's
  byte preimages (node 64; log leaf 88; chain-id leaf, IMT leaf, empty entry and commit value 96;
  batch leaf 128; IMT padding 34): every domain premise and every located break becomes a keccak
  collision on two named byte strings.
- **ProofSound, RootBinding, RootForgery** and four results of Verifier take global pair-injectivity
  of the node hash, which no `UInt256` hash has (`ASSUMPTIONS.md`, "Results whose premises cannot
  hold"), so they are vacuous. Each has a replacement with no hash premise in `RootForgeryPinned` or
  `PathCollision`, mapped in that Properties header.

## History

[History/](History/) is the record of an older commit, not a claim about `b17415d20`. At the interop
pin `c67894b9` the IMT padding was `hashLeaf({0,0,0})`, a leaf preimage (the H2 padding finding).
`MerkleSpec.DomainSeparation.History` keeps the keccak-level forms at that padding: the root check's
only keccak-free break is the zero leaf at an empty slot (`ProofsExclusiveOrKeccakBreakAtPin` and its
single-proof forms), the countermodel `PaddingForgeryIsTheOnlyKeccakFreeBreak`, and the
`HashAssumptions` fields at that padding. Renames: `handoff/2026-11-19/renames/merkle-libs.json`.
