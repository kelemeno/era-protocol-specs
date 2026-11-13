import EraSpec.Contracts.Merkle.Specs.RootForgeryPinned

/-!
# Contract spec: the padding case of root binding, pinned to the whole padded vector

## Why this file exists

`MerkleSpec.Pinned.Properties.RootCommitsListOrBreak` (`RootForgeryPinned`) classifies two
leaf lists within capacity whose roots at a height are equal: the lists are equal, or
`PaddingHit z0 L₁ L₂`, or at an index where they differ the two trees collide on that index's
path (`TreeCollision`).  `PaddingHit` reads only the two lengths and ONE entry, the longer
list's entry at the shorter one's length.  It says nothing about the positions both lists
occupy.  So that disjunct can hold while the lists differ at an occupied index, with a real
collision there that the theorem never extracts.  Under `constHash` (every pair collides),
`[1]` and `[2, 0]` with padding `0` have the same root at height 1, form a padding hit, differ
at index 0, and collide on index 0's path.

The padding case has a precise shape: one list IS the other followed by copies of the padding
constant (`PaddingExtension`).  Two lists in that relation agree at every index read with the
padding default, and conversely.  Lists that agree there are the same tree at every height
for every hash, with no collision on any path (`MerkleSpec.Pinned.same_tree_of_getD_eq`, an
internal lemma of `../Proofs/RootForgeryPinned.lean`, stated here as a property).
`../Properties/RootForgeryPinnedStrong.lean` states the classification with the padding case
restricted to that shape, and proves that within capacity, equal roots with no collision on
any committed path happen exactly for padding extensions.

## What the source does (era-contracts `c67894b9`)

`l1-contracts/contracts/common/libraries/FullMerkle.sol`:

    function setup(FullTree storage self, bytes32 zero) internal returns (bytes32) {  // :29
        self._zeros.push(zero);  self._nodes.push([zero]);  return zero;             // :31-34
    }
    …  maxNodeNumber == _index ? self._zeros[i] : self._nodes[i][_index + 1]       // :84

An absent right sibling at level `i` is read as `_zeros[i]`, the zero cascade above `zero`.  A
real leaf whose hash is `zero` therefore hashes exactly like an absent slot, and so does any
run of such leaves at the end of the list.  The NatSpec (:25-26) asks for a `zero` "that is not
expected to be part of the tree".  `IndexedMerkleTree.setup` (`IndexedMerkleTree.sol:47-50`)
passes `hashLeaf({0,0,0})` as `zero` and pushes the same hash as its sentinel leaf at index 0,
so in the commitment tree the padding constant is also a real leaf.

## Model boundary

As in `RootForgeryPinned`: an abstract node hash `h`, leaves and nodes in `UInt256`, indices and
heights in `ℕ`.  Nothing here depends on a hash premise.
-/

namespace MerkleSpec.PinnedStrong

open Clear MerkleSpec MerkleSpec.Pinned

/-- **One list is the other followed by padding leaves.**  `L₂` is `L₁` followed by `k` copies
of the padding constant `z0`, or `L₁` is `L₂` followed by `k` copies (`k = 0` is the equal
case).  Determined by `(z0, L₁, L₂)`. -/
def PaddingExtension (z0 : UInt256) (L₁ L₂ : List UInt256) : Prop :=
  ∃ k, L₂ = L₁ ++ List.replicate k z0 ∨ L₁ = L₂ ++ List.replicate k z0

end MerkleSpec.PinnedStrong
