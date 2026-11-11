import EraSpec.Contracts.Merkle.Specs.Verifier
import EraSpec.Contracts.Merkle.Specs.PathCollision

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

/-! ## The pinned break

`HashBreak` is always inhabited (`Properties.HashBreakAlways`): its `nodeCollision`
constructor takes any four words, and every `UInt256` hash collides somewhere.  The
argument above, though, only ever looks at ONE subtree: the right sibling at the
first left turn of `j`'s path, whose leftmost leaf is `j + 1`.  Peeling the zero
cascade down that subtree visits exactly the nodes whose subtree starts at `j + 1`,
one per level.  `PinnedBreak` records the collision there, so both colliding pairs
are functions of the instance `(h, z0, L, j)`:

* `nodeCollision l m` — the level-`(l+1)` node `m` with `m * 2^(l+1) = j + 1` has
  children `childPair h z0 L l m` different from `zeroPair h z0 l`, yet the two
  pairs hash equal;
* `entryIsEmpty` — the leaf `j + 1` itself equals the empty-entry constant.

Both constructors require `j + 1` to be occupied: the break is about the leaf that
makes `j` not last.  `Properties.PinnedBreakNotAlways` checks it is not a tautology. -/

/-- The two level-`l` entries under the level-`(l+1)` node `m` (padding read as the
level's zero, as `FullMerkle` stores it).  Their hash is that node. -/
def childPair (h : Hash) (z0 : UInt256) (L : List UInt256) (l m : ℕ) : UInt256 × UInt256 :=
  ((levels h z0 L l).getD (2 * m) (zeros h z0 l),
   (levels h z0 L l).getD (2 * m + 1) (zeros h z0 l))

/-- The pair the zero cascade hashes at level `l`: `zeros (l+1) = h (zeros l) (zeros l)`. -/
def zeroPair (h : Hash) (z0 : UInt256) (l : ℕ) : UInt256 × UInt256 :=
  (zeros h z0 l, zeros h z0 l)

/-- **A BREAK LOCATED ON THE SUBTREE THAT STARTS AT `j + 1`.**  See the section
docstring.  Every pair named here is determined by `(h, z0, L, j)` and the level. -/
inductive PinnedBreak (h : Hash) (z0 : UInt256) (L : List UInt256) (j : ℕ) : Prop
  | nodeCollision (l m : ℕ) : j + 1 < L.length → m * 2 ^ (l + 1) = j + 1 →
      childPair h z0 L l m ≠ zeroPair h z0 l →
      h (childPair h z0 L l m).1 (childPair h z0 L l m).2
        = h (zeroPair h z0 l).1 (zeroPair h z0 l).2 →
      PinnedBreak h z0 L j
  | entryIsEmpty : j + 1 < L.length → L.getD (j + 1) z0 = z0 → PinnedBreak h z0 L j

/-! ## Bounded no-collision premises

The satisfiable replacement for global pair-injectivity: `h` is injective on an
explicit, instance-determined finite set of pairs. -/

/-- `h` is injective on the pairs satisfying `P`. -/
def PairInjOn (h : Hash) (P : UInt256 × UInt256 → Prop) : Prop :=
  ∀ p q, P p → P q → h p.1 p.2 = h q.1 q.2 → p = q

/-- The pairs the tree over `L` (at height `height`) hashes above occupied
positions, and the zero cascade's pairs below the root: at most `L.length + 1`
pairs per level, `height` levels, all fixed by the instance. -/
def TreePair (h : Hash) (z0 : UInt256) (L : List UInt256) (height : ℕ)
    (p : UInt256 × UInt256) : Prop :=
  (∃ l < height, ∃ m, m * 2 ^ (l + 1) < L.length ∧ p = childPair h z0 L l m)
    ∨ ∃ l < height, p = zeroPair h z0 l

/-- The `height` pairs the verifier hashed while walking the submitted path
`(sibs, j, x)` from level 0. -/
def VerifiedPair (h : Hash) (sibs : ℕ → UInt256) (height j : ℕ) (x : UInt256)
    (p : UInt256 × UInt256) : Prop :=
  ∃ i < height, p = walkPair h sibs 0 j x i

/-! ## A concrete instance for the anti-vacuity witnesses -/

/-- A toy node hash, `a + 2b + 1` in wrapping arithmetic.  It collides freely
(`demoHash 2 0 = demoHash 0 1`), so nothing proved about it comes from global
injectivity. -/
def demoHash : Hash := fun a b => a + 2 * b + 1

end MerkleSpec.LastLeaf
