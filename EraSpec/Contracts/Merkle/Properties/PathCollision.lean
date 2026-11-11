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

/-! ## The path length, without hash premises

These replace `Verifier`'s `AcceptForcesHeight` / `AcceptPinsEntryAnyLength`, whose
premises (global pair-injectivity, and "no leaf hash / padding constant / claimed
leaf is ANY node hash") cannot hold. -/

/-- **THE ACCEPTED PATH LENGTH IS THE TREE HEIGHT, OR A LOCATED BREAK.**  A walk of
any length `k`, accepted against the root at any `height`, has `k = height`, or
exhibits a `HeightBreak` (an interior node presented as the leaf, a level-0 entry
that is the node hash of the verifier's own pair, or a `PathCollision` on the
re-anchored / split walk). -/
def Properties.AcceptForcesHeightOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    j < 2 ^ k → walkPure h sibs 0 k j x = rootOf h z0 L height →
      k = height ∨ HeightBreak h z0 L sibs k height j x

/-- **FULL SOUNDNESS OF THE DEPLOYED VERIFIER, NO HASH PREMISE.**  Any accepted walk
has the tree's height and opens the level-0 entry at its index, or it collides on the
submitted path (at the right height), or it is a located `HeightBreak`. -/
def Properties.AcceptPinsEntryAnyLengthOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k height j : ℕ)
    (x : UInt256),
    j < 2 ^ k → walkPure h sibs 0 k j x = rootOf h z0 L height →
      (k = height ∧ L.getD j z0 = x)
        ∨ (k = height ∧ PathCollision h z0 L sibs 0 k j x)
        ∨ HeightBreak h z0 L sibs k height j x

/-- **NON-TRIVIALITY OF `HeightBreak`.**  It never holds at the right length (so on
every honest proof), and it fails on concrete wrong-length instances on both sides
(short: length 0 against height 1; long: length 1 against height 0), with the
constant hash `fun _ _ => 1`, leaves `[0]` and padding `0`. -/
def Properties.HeightBreakNotTautology : Prop :=
  (∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256),
      ¬ HeightBreak h z0 L sibs k k j x)
  ∧ ¬ HeightBreak (fun _ _ => 1) 0 [0] (fun _ => 0) 0 1 0 0
  ∧ ¬ HeightBreak (fun _ _ => 1) 0 [0] (fun _ => 0) 1 0 0 0

/-- **A WRONG LENGTH IS ACCEPTED, AND IS LOCATED.**  The premises of
`AcceptForcesHeightOrBreak` hold with `k ≠ height`: the empty path at index 0,
presenting the root itself as the leaf, is accepted against any tree of positive
height (`calculateRootMemory` with an empty path returns the item hash), and the
break located is `shortInteriorLeaf`: the "leaf" is the node hash of the tree's top
pair. -/
def Properties.ZeroLengthPathAcceptsRoot : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (sibs : ℕ → UInt256) (height : ℕ), 0 < height →
    (0 < 2 ^ 0 ∧ walkPure h sibs 0 0 0 (rootOf h z0 L height) = rootOf h z0 L height)
      ∧ HeightBreak h z0 L sibs 0 height 0 (rootOf h z0 L height)

end MerkleSpec.Verifier
