import EraSpec.Contracts.AtomicInteropProof.Specs.LastLeaf

/-!
# The last-leaf check, with the batch-leaf path length and index the prover's

`MerkleSpec.LastLeaf`'s accepted-path forms (`AcceptedLastLeafOrPinnedBreak`,
`AcceptedLastLeafOn`) take `L.length ≤ 2 ^ height`, `j < L.length` and
`walkPure h sibs 0 height j x = rootOf h z0 L height`: ONE `height` for the submitted
walk and for the chain tree, and an occupied index.  The deployed verifier fixes
neither of the two:

Paths below are under `l1-contracts/contracts/` at era-contracts `b17415d20`.

* `common/libraries/MessageHashing.sol:129`: `result.batchLeafProofLen =
  uint256(uint8(proofMetadata[2]))` — the batch-leaf path length is a prover-chosen
  metadata byte.  `_authenticateRoot`
  (`atomic-interop/libraries/AtomicInteropProof.sol:160-162`) pins only
  `logLeafProofLen` to `ChainBatchRootTree.TREE_DEPTH`, never `batchLeafProofLen`.
* `MessageHashing.sol:198-208`: `batchLeafProofMask = uint256(bytes32(_proof[result.ptr]))`,
  then `chainIdRoot = Merkle.calculateRootMemory(extractSlice(..., batchLeafProofLen),
  batchLeafProofMask, localBatchLeafHash)` — the index is the prover's mask.
* `common/libraries/Merkle.sol:133-140` checks only `_pathLength < 256` and `_index < (1 << _pathLength)`:
  a padded index `j ≥ leafCount` below `2^len` is accepted, and so is any length.
* `AtomicInteropProof.sol:130-143` (`_verifyLastBatchInRoot`) runs its zero check over
  `levels = _path.batchLeafSiblings.length`, the SUBMITTED length.

`LastBatchPathAccepted` below is that acceptance with `k` (length) and `j` (mask) free.
`LastLeafAnyLengthBreak` is what such a path can exhibit instead of "`j` is the chain's
last leaf": a wrong length located by `MerkleSpec.Verifier.HeightBreak`, a padded index
whose claimed leaf hash is the empty-entry constant, or (at the right length) the
pinned break / path collision `LastLeaf` already names.

## Model boundary: the claimed leaf hash

The model takes the claimed leaf hash `x` as free.  On chain it is computed:
`localBatchLeafHash = batchLeafHash(batchSettlementRoot, _batchNumber, l1BatchTimestamp)`
(`MessageHashing.sol:192-196`), that is `keccak256(BATCH_LEAF_PADDING ‖ root ‖ number ‖
timestamp)` over a 128-byte preimage (`:76-82`), which the prover controls only through
its inputs.  A tree node is the keccak of 64 bytes (`Merkle.sol:124-131`), and the
empty-entry constant is the keccak of 96 zero bytes (`core/message-root/IMessageRoot.sol:8-11`).  So, on
chain, presenting an interior node as the leaf (`HeightBreak.shortInteriorLeaf`) needs a
batch leaf equal to a node hash, `HeightBreak.longEntryIsNode` needs a stored entry (a
batch leaf or the empty-entry constant) equal to a node hash, and a padded entry needs a
batch leaf equal to the empty-entry constant: each is a cross-length keccak preimage,
excluded by hash domain separation and by no check the contract performs.  The other
`HeightBreak` cases (`shortCollision`, `longCollision`) are same-length 64-byte
collisions on the walk, so length separation alone does not exclude every wrong length.

## Model boundary that remains: the outer hop

`authenticated` says the batch-leaf walk reaches chain `c`'s own batch-tree root.  On
chain that is the job of the next hop (`interop/L2MessageVerification.sol:45-55`):
`chainIdLeaf = chainIdLeafHash(chainIdRoot, chainId)` is proven into the imported
settlement-layer root by another path whose length and mask are again the prover's.
That hop is not modelled here; it is modelled at `b17415d20` in `AuthenticateRootAtV35`
(`slHopPath`, `SLHopBreak`, `EndBranchTwoHopLastLeafOrBreakV35`).  Applied to it, `MerkleSpec.Verifier.AcceptPinsEntryAnyLengthOrBreak`
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
the zero cascade the check compares against).  The submitted length `k`, mask `j` and
siblings `sibs` are the prover's.  The claimed leaf hash `x` is modelled as free; on
chain it is `batchLeafHash(root, n, t)`, a keccak of a 128-byte preimage
(`MessageHashing.sol:76-82`, `:192-196`), see the module docstring. -/
structure LastBatchPathAccepted (h : Hash) (z0 : UInt256) (L : List UInt256) (height : ℕ)
    (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256) : Prop where
  /-- `Merkle.sol:137-139`, `MerkleIndexOutOfBounds`. -/
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
  CHAIN_TREE_EMPTY_ENTRY_HASH`, a 128-byte keccak preimage of that constant, which is
  itself the keccak of 96 zero bytes);
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
no-collision premise ranges over.  It adds nothing to that set: every such pair is
already a `TreePair` (`pathTreePair_sub_treePair` in the Proofs), so the set is the one
`LastLeaf.AcceptedLastLeafOn` uses. -/
def PathTreePair (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ)
    (p : UInt256 × UInt256) : Prop :=
  ∃ i < height, p = treePair h z0 L i (j / 2 ^ i)

end MerkleSpec.LastLeafFaithful
