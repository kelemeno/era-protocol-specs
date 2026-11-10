import EraSpec.Contracts.Merkle.Specs.Verifier

/-!
# The last-leaf proof, and what breaking it would cost

`_verifyLastBatchInRoot` establishes that a batch leaf is the **last** leaf of its
chain's batch tree inside an aggregated root, and it does so with a shape argument
rather than a count:

    /// @dev Verifies that the proven batch leaf is the LAST leaf of the source chain's batch tree
    /// inside the aggregated root: on every level of the batch-leaf Merkle path where the current
    /// node is a left child (mask bit 0), the right sibling must be the empty-subtree hash for that
    /// level (`zeros[0] = CHAIN_TREE_EMPTY_ENTRY_HASH`, `zeros[i+1] = keccak(zeros[i] || zeros[i])`).
    /// A non-last leaf necessarily has a populated right subtree on some level, whose hash cannot
    /// collide with the zero cascade.

This file proves that, in the form the comment's last sentence suggests: not "assume
the hash is injective, therefore the leaf is last", but **the leaf is last, or you
have produced a concrete collision**.  `HashBreak` is that alternative, and it has
exactly two constructors because there are exactly two ways out — a genuine node
collision, or a real entry that equals the empty-entry constant.

## The argument

Let `j` be the proven leaf and suppose leaf `j+1` is also occupied.  Walk up from
`j` to the first level `l` where the path goes left.  Below that level every step
went right, so `j`'s low `l` bits are all ones and the right sibling's subtree
*starts exactly at* `j+1` (`exists_left_level`).  The check says that sibling is
`zeros l`.  But its subtree contains an occupied leaf, and peeling
`zeros (l+1) = h (zeros l) (zeros l)` down that subtree either hits a node whose two
children are not both zeros — a collision — or bottoms out at an occupied level-0
entry equal to `z0` (`zero_subtree_or_break`).

Nothing in either lemma assumes injectivity.  Injectivity enters only where the
path has to be pinned to the tree's own siblings, which is
`MerkleSpec.Verifier.walk_pins`, and `not_hashBreak` is the corollary that closes
the disjunction when one is willing to assume both idealizations.

Ported from the `claude/proof-attempt-4f3778` line (`EraSpec/Core/LastLeaf.lean`).
`_verifyLastBatchInRoot` is in `AtomicInteropProof`, so it lives here, next to the
older `LastBatchInRoot` topic.  Results: `../Properties/LastLeaf.lean`.
-/

namespace MerkleSpec.LastLeaf

open Clear MerkleSpec MerkleSpec.Verifier

/-- What a failure of the last-leaf argument exhibits.

`nodeCollision` is a genuine keccak collision on a 64-byte node preimage.
`entryIsEmpty` is a domain-separation failure: an occupied leaf of the chain tree
equal to `CHAIN_TREE_EMPTY_ENTRY_HASH`, the constant the empty positions carry. -/
inductive HashBreak (h : Hash) (z0 : UInt256) (L : List UInt256) : Prop
  | nodeCollision (a b c d : UInt256) : (a ≠ c ∨ b ≠ d) → h a b = h c d → HashBreak h z0 L
  | entryIsEmpty (m : ℕ) : m < L.length → L.getD m z0 = z0 → HashBreak h z0 L

/-- The chain tree's domain separation: no occupied entry is the empty-entry
constant.  With this and node injectivity there is no way out — see
`not_hashBreak`. -/
def EntriesNotEmpty (z0 : UInt256) (L : List UInt256) : Prop :=
  ∀ m < L.length, L.getD m z0 ≠ z0

end MerkleSpec.LastLeaf
