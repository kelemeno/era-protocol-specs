import EraSpec.Contracts.AtomicInteropProof.Specs.LastLeaf

/-!
# The last-leaf check, with the batch-leaf path length and index the prover's

`MerkleSpec.LastLeaf`'s accepted-path forms (`AcceptedLastLeafOrPinnedBreak`,
`AcceptedLastLeafOn`) take `L.length ≤ 2 ^ height`, `j < L.length` and
`walkPure h sibs 0 height j x = rootOf h z0 L height`: ONE `height` for the submitted
walk and for the chain tree, and an occupied index.  The deployed verifier fixes
neither of the two:

* `MessageHashing.sol:131` (pinned `c67894b9`): `result.batchLeafProofLen =
  uint256(uint8(proofMetadata[2]))` — the batch-leaf path length is a prover-chosen
  metadata byte.  `_authenticateRoot` (`AtomicInteropProof.sol:260-263`) pins only
  `logLeafProofLen` to `ChainBatchRootTree.TREE_DEPTH`, never `batchLeafProofLen`.
* `MessageHashing.sol:201-208`: `batchLeafProofMask = uint256(bytes32(_proof[result.ptr]))`,
  then `chainIdRoot = Merkle.calculateRootMemory(extractSlice(..., batchLeafProofLen),
  batchLeafProofMask, localBatchLeafHash)` — the index is the prover's mask.
* `Merkle.sol:133-140` checks only `_pathLength < 256` and `_index < (1 << _pathLength)`:
  a padded index `j ≥ leafCount` below `2^len` is accepted, and so is any length.
* `AtomicInteropProof.sol:217-230` (`_verifyLastBatchInRoot`) runs its zero check over
  `levels = _path.batchLeafSiblings.length`, the SUBMITTED length.

`LastBatchPathAccepted` below is that acceptance with `k` (length) and `j` (mask) free.
`LastLeafAnyLengthBreak` is what such a path can exhibit instead of "`j` is the chain's
last leaf": a wrong length located by `MerkleSpec.Verifier.HeightBreak`, a padded index
whose claimed leaf hash is the empty-entry constant, or (at the right length) the
pinned break / path collision `LastLeaf` already names.

## Model boundary that remains: the outer hop

`authenticated` says the batch-leaf walk reaches chain `c`'s own batch-tree root.  On
chain that is the job of the next hop (`L2MessageVerification.sol:42-51`):
`chainIdLeaf = chainIdLeafHash(chainIdRoot, chainId)` is proven into the imported
settlement-layer root by another path whose length and mask are again the prover's.
That hop is not modelled here.  Applied to it, `MerkleSpec.Verifier.AcceptPinsEntryAnyLengthOrBreak`
yields "the opened shared-tree entry is `chainIdLeaf`, or a located break"; reading
that entry as chain `c`'s own leaf additionally needs the chain-id-leaf hash to separate
`(chainIdRoot, chainId)` pairs on the instance.

**This file is definitions only.**  Results: `../Properties/LastLeafFaithful.lean`.
-/

namespace MerkleSpec.LastLeafFaithful

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf

/-- **THE BATCH-LEAF HOP AND `_verifyLastBatchInRoot`, AS DEPLOYED.**  `L` is chain
`c`'s batch-leaf list inside the aggregated root, `height` its tree height, `z0` the
empty-entry constant `CHAIN_TREE_EMPTY_ENTRY_HASH` (the tree's padding and the base of
the zero cascade the check compares against).  The submitted length `k`, mask `j`,
siblings `sibs` and leaf hash `x` are the prover's. -/
structure LastBatchPathAccepted (h : Hash) (z0 : UInt256) (L : List UInt256) (height : ℕ)
    (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256) : Prop where
  /-- `Merkle.sol:138-140`, `MerkleIndexOutOfBounds`. -/
  inBounds : j < 2 ^ k
  /-- `calculateRootMemory` over the submitted path returns chain `c`'s root (the outer
  hop's conclusion; see the module docstring). -/
  authenticated : walkPure h sibs 0 k j x = rootOf h z0 L height
  /-- `_verifyLastBatchInRoot`: at every submitted level where the path goes left, the
  right sibling is that level's zero. -/
  zeroCheck : ∀ l < k, (j / 2 ^ l) % 2 = 0 → sibs l = zeros h z0 l

/-- **WHAT AN ACCEPTED BATCH-LEAF PATH CAN EXHIBIT INSTEAD OF THE LAST LEAF.**  Every
compared value is a function of the instance `(h, z0, L, sibs, k, height, j, x)`.

* `wrongLength` — the submitted length is not the tree's height, located by
  `HeightBreak` (an interior node presented as the leaf, a level-0 entry that is the
  node hash of the verifier's own pair, or a collision on the re-anchored / split walk);
* `paddedEntry` — the right length, an index beyond the occupied leaves, and the
  claimed leaf hash IS the empty-entry constant (on chain: `localBatchLeafHash ==
  CHAIN_TREE_EMPTY_ENTRY_HASH`, a preimage of that constant);
* `pinned` — the right length, and `LastLeaf.PinnedBreak` on the subtree after `j`;
* `pathCollision` — the right length, and a `PathCollision` on the submitted path. -/
inductive LastLeafAnyLengthBreak (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (k height j : ℕ) (x : UInt256) : Prop
  | wrongLength : HeightBreak h z0 L sibs k height j x →
      LastLeafAnyLengthBreak h z0 L sibs k height j x
  | paddedEntry : k = height → L.length ≤ j → x = z0 →
      LastLeafAnyLengthBreak h z0 L sibs k height j x
  | pinned : k = height → PinnedBreak h z0 L j →
      LastLeafAnyLengthBreak h z0 L sibs k height j x
  | pathCollision : k = height → PathCollision h z0 L sibs 0 k j x →
      LastLeafAnyLengthBreak h z0 L sibs k height j x

/-- The tree's own pairs along index `j`'s path, one per level below `height`.  With
`TreePair` and `VerifiedPair` this is the finite, instance-determined set the bounded
no-collision premise ranges over. -/
def PathTreePair (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ)
    (p : UInt256 × UInt256) : Prop :=
  ∃ i < height, p = treePair h z0 L i (j / 2 ^ i)

end MerkleSpec.LastLeafFaithful
