import EraSpec.Contracts.Merkle.Specs.Verifier

/-!
# Properties: the deployed verifier, with no range or height hypothesis

`Merkle.calculateRootMemory` accepts any index below `2^pathLength` and any path
length below 256; it cannot know the tree's leaf count or height.  These statements
are about the verifier as deployed: the index and the path length are the prover's.
`L` is the leaf-hash list, `z0` the padding constant, `h` the node hash; pair
injectivity (`hinj`) and domain separation (`hL`, `hz0`, `hx`: no leaf hash, padding
constant or claimed leaf is a node hash) are explicit premises where used.
Proofs: `../Proofs/Verifier.lean`.
-/

namespace MerkleSpec.Verifier

open Clear MerkleSpec

/-- **THE HONEST WALK RECOMPUTES THE ROOT, AT EVERY INDEX BELOW CAPACITY.**  For an
occupied index the accumulator is the leaf hash; for a padded one it is the padding
constant `z0`. -/
def Properties.HonestWalkRoot : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ), j < 2 ^ height →
    walkPure h (honestSibs h z0 L j) 0 height j (L.getD j z0) = rootOf h z0 L height

/-- **A PADDED SLOT VERIFIES.**  Below capacity but beyond the occupied range, the
honest siblings authenticate the padding constant as a leaf.  This is the verifier
working as designed, and it is why the padding constant must not be a possible
leaf hash. -/
def Properties.PaddedSlotVerifies : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L : List UInt256) (height j : ℕ),
    L.length ≤ j → j < 2 ^ height →
    walkPure h (honestSibs h z0 L j) 0 height j z0 = rootOf h z0 L height

/-- **ROOT FORM OF SOUNDNESS.**  An accepted walk of length `k` from any index
`j < 2^k` against the root at height `k` pins the level-0 entry at `j`, padding
included: `L.getD j z0` is the leaf hash if `j` is occupied and `z0` otherwise.
No capacity hypothesis is needed. -/
def Properties.AcceptPinsEntry : Prop :=
  ∀ (h : Hash) (z0 : UInt256), (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (L : List UInt256) (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256), j < 2 ^ k →
      walkPure h sibs 0 k j x = rootOf h z0 L k → L.getD j z0 = x

/-- The two cases of `Properties.AcceptPinsEntry`: the index is occupied and the
walk's leaf is that entry, or it is padding and the walk's leaf is the padding
constant. -/
def Properties.AcceptPinsEntryCases : Prop :=
  ∀ (h : Hash) (z0 : UInt256), (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (L : List UInt256) (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256), j < 2 ^ k →
      walkPure h sibs 0 k j x = rootOf h z0 L k →
      (j < L.length ∧ L.getD j z0 = x) ∨ (L.length ≤ j ∧ x = z0)

/-- **THE ACCEPTED PATH LENGTH IS THE TREE HEIGHT.**  Under pair injectivity and
domain separation, a walk accepted against the root at `height` has length exactly
`height`: a shorter one would present an interior node as the leaf, a longer one
would pass through a level-0 entry that is a node hash. -/
def Properties.AcceptForcesHeight : Prop :=
  ∀ (h : Hash) (z0 : UInt256), (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (L : List UInt256), (∀ y ∈ L, ∀ a b : UInt256, y ≠ h a b) →
    (∀ a b : UInt256, z0 ≠ h a b) →
    ∀ (sibs : ℕ → UInt256) (k height j : ℕ) (x : UInt256), (∀ a b : UInt256, x ≠ h a b) →
      j < 2 ^ k → walkPure h sibs 0 k j x = rootOf h z0 L height → k = height

/-- **FULL SOUNDNESS OF THE DEPLOYED VERIFIER.**  For any index and any accepted path
length, under pair injectivity and domain separation: the length is the tree's height
and the claimed leaf hash is the level-0 entry at that index. -/
def Properties.AcceptPinsEntryAnyLength : Prop :=
  ∀ (h : Hash) (z0 : UInt256), (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (L : List UInt256), (∀ y ∈ L, ∀ a b : UInt256, y ≠ h a b) →
    (∀ a b : UInt256, z0 ≠ h a b) →
    ∀ (sibs : ℕ → UInt256) (k height j : ℕ) (x : UInt256), (∀ a b : UInt256, x ≠ h a b) →
      j < 2 ^ k → walkPure h sibs 0 k j x = rootOf h z0 L height →
      k = height ∧ L.getD j z0 = x

end MerkleSpec.Verifier
