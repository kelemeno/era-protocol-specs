import EraSpec.Contracts.Merkle.Specs.PathCollision

/-!
# Properties: an accepted path opens the tree, or the theorem locates a collision

No hash premise at all.  These replace `Verifier`'s `hinj`-premised pinning results,
which are vacuous.  Proofs: `../Proofs/PathCollision.lean`.
-/

namespace MerkleSpec.Verifier

open Clear MerkleSpec

/-- **THE EXTRACTOR.**  A walk that reaches the tree's node above `j` either used the
tree's own level-`lvl` entry and siblings, or exhibits a `PathCollision` at a named
level of that walk.  This is `walk_pins` with its global-injectivity premise replaced
by the collision it was hiding. -/
def Properties.WalkPinsOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k lvl j : ℕ) (x : UInt256),
    walkPure h sibs lvl k j x
        = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k)) →
      ((levels h z0 L lvl).getD j (zeros h z0 lvl) = x
        ∧ ∀ l, lvl ≤ l → l < lvl + k →
            sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l))
      ∨ PathCollision h z0 L sibs lvl k j x

/-- **ROOT FORM.**  A walk of length `k` from any index `j < 2^k`, accepted against the
root at height `k`, opens the level-0 entry at `j` (padding included), or locates a
collision on the submitted path. -/
def Properties.AcceptPinsEntryOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256),
    j < 2 ^ k → walkPure h sibs 0 k j x = rootOf h z0 L k →
      L.getD j z0 = x ∨ PathCollision h z0 L sibs 0 k j x

/-- **NON-TRIVIALITY.**  `PathCollision` is not a tautology: on the honest path (the
tree's own siblings and leaf) the verifier hashes exactly the tree's pairs, so no
collision is located, for every hash function. -/
def Properties.HonestWalkNoCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ),
    ¬ PathCollision h z0 L (honestSibs h z0 L j) 0 height j (L.getD j z0)

end MerkleSpec.Verifier
