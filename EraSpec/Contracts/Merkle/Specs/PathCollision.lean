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

end MerkleSpec.Verifier
