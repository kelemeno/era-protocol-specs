import EraSpec.Contracts.Merkle.Specs.Verifier

/-!
# Contract spec: a positional collision on a submitted Merkle path

Every soundness result for `Merkle.calculateRootMemory` so far either assumed global
pair-injectivity of the node hash (`hinj : ∀ a b c d, h a b = h c d → a = c ∧ b = d`),
which no `UInt256 → UInt256 → UInt256` satisfies, or concluded "…or there EXISTS some
collision", which pigeonhole makes always true.  Neither says anything.

What the reduction actually provides is an *extractor*: if a submitted path is
accepted but does not open the tree, then at a level the theorem names, the pair the
verifier hashed differs from the pair the tree hashed there, and the two hash to the
same value.  `PathCollision` is that statement.  Its witnesses are functions of the
instance (the tree, the submitted siblings, the index and the claimed leaf), so
it is not implied by the mere existence of collisions; `Properties.HonestWalkNoCollision`
checks that it is false on the honest path.

* `walkStep sibs lvl idx x` — the ordered pair the verifier hashes when its
  accumulator `x` sits at level `lvl`, index `idx`.
* `walkPair h sibs lvl j x i` — that pair at step `i` of the walk from `(lvl, j, x)`.
* `treePair h z0 L l idx` — the two tree entries under the node above index `idx`
  at level `l` (padding read as the level's zero, as `FullMerkle` stores it).
-/

namespace MerkleSpec.Verifier

open Clear MerkleSpec

/-- The pair hashed at one step: the sibling goes left iff the accumulator is a right
child. -/
def walkStep (sibs : ℕ → UInt256) (lvl idx : ℕ) (x : UInt256) : UInt256 × UInt256 :=
  if idx % 2 = 1 then (sibs lvl, x) else (x, sibs lvl)

/-- The pair hashed at step `i` of the walk that starts at level `lvl`, index `idx`,
accumulator `x`. -/
def walkPair (h : Hash) (sibs : ℕ → UInt256) : ℕ → ℕ → UInt256 → ℕ → UInt256 × UInt256
  | lvl, idx, x, 0 => walkStep sibs lvl idx x
  | lvl, idx, x, i + 1 =>
      walkPair h sibs (lvl + 1) (idx / 2)
        (h (walkStep sibs lvl idx x).1 (walkStep sibs lvl idx x).2) i

/-- The two level-`l` tree entries under the parent of index `idx`. -/
def treePair (h : Hash) (z0 : UInt256) (L : List UInt256) (l idx : ℕ) : UInt256 × UInt256 :=
  ((levels h z0 L l).getD (2 * (idx / 2)) (zeros h z0 l),
   (levels h z0 L l).getD (2 * (idx / 2) + 1) (zeros h z0 l))

/-- **A collision located on the submitted path.**  At some step `i < k` the verifier
hashed a pair different from the tree's pair at the same position, and both hash to
the same value.  Both pairs are determined by the instance. -/
def PathCollision (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256)
    (lvl k j : ℕ) (x : UInt256) : Prop :=
  ∃ i < k, walkPair h sibs lvl j x i ≠ treePair h z0 L (lvl + i) (j / 2 ^ i)
    ∧ h (walkPair h sibs lvl j x i).1 (walkPair h sibs lvl j x i).2
      = h (treePair h z0 L (lvl + i) (j / 2 ^ i)).1 (treePair h z0 L (lvl + i) (j / 2 ^ i)).2

/-! ## A wrong path length, located

`Merkle.calculateRootMemory` does not know the tree's height, so a path of length
`k ≠ height` can be submitted.  `accept_forces_height` excluded that under global
pair-injectivity and global domain separation, both of which are unsatisfiable or
false for `keccak`.  `HeightBreak` is what an accepted wrong-length walk actually
yields, with every compared value a function of the instance:

* **too short** (`k < height`): re-anchor the walk at level `height - k` (the stream
  `l ↦ sibs (l - (height - k))` reads the submitted siblings at the levels they now
  sit on).  Either the claimed leaf `x` IS the node hash of the tree's level
  `height - k - 1` pair below index `j` (an interior node presented as a leaf), or
  the re-anchored walk exhibits a `PathCollision`.
* **too long** (`height < k`): split off the first `k - height` steps.  Either the
  level-0 entry at `j / 2^(k - height)` (a leaf hash, or the padding constant) IS the
  node hash of the pair the verifier hashed at its last step below the split, or the
  remaining `height` steps (stream `l ↦ sibs (l + (k - height))`) exhibit a
  `PathCollision`. -/

/-- **An accepted walk of the wrong length, located.**  See the section comment.
Arguments: node hash `h`, padding `z0`, level-0 list `L`, submitted siblings `sibs`,
submitted length `k`, tree height `height`, index `j`, claimed leaf `x`. -/
inductive HeightBreak (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256)
    (k height j : ℕ) (x : UInt256) : Prop
  /-- Too short, and the claimed leaf is the node hash of a specific tree pair. -/
  | shortInteriorLeaf : k < height →
      x = h (treePair h z0 L (height - k - 1) (2 * j)).1
            (treePair h z0 L (height - k - 1) (2 * j)).2 →
      HeightBreak h z0 L sibs k height j x
  /-- Too short, and the re-anchored walk collides on the submitted path. -/
  | shortCollision : k < height →
      PathCollision h z0 L (fun l => sibs (l - (height - k))) (height - k) k j x →
      HeightBreak h z0 L sibs k height j x
  /-- Too long, and a level-0 entry is the node hash of the verifier's own pair. -/
  | longEntryIsNode : height < k →
      L.getD (j / 2 ^ (k - height)) z0
        = h (walkPair h sibs 0 j x (k - height - 1)).1 (walkPair h sibs 0 j x (k - height - 1)).2 →
      HeightBreak h z0 L sibs k height j x
  /-- Too long, and the top `height` steps collide on the submitted path. -/
  | longCollision : height < k →
      PathCollision h z0 L (fun l => sibs (l + (k - height))) 0 height (j / 2 ^ (k - height))
        (walkPure h sibs 0 (k - height) j x) →
      HeightBreak h z0 L sibs k height j x

end MerkleSpec.Verifier
