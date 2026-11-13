import EraSpec.Contracts.Merkle.Specs.RootForgeryPinnedStrong

/-!
# Properties: root binding without the equal-length premise, padding case pinned

No hash premise anywhere in this file.  Proofs: `../Proofs/RootForgeryPinnedStrong.lean`.

`MerkleSpec.Pinned.Properties.RootCommitsListOrBreak` concludes `L₁ = L₂ ∨ PaddingHit z0 L₁ L₂ ∨
(a located collision at a differing index)`.  Its padding disjunct reads two lengths and one
entry, so it is met by pairs that differ at an occupied index with a real collision there
(`RootCommitsListOrBreakStrongUnmasksCollision`).  The statements here close that gap:

* `RootCommitsListOrBreakStrong` — the same classification with the padding case restricted to
  lists that agree at every index read with the padding default, i.e. one list is the other
  followed by padding leaves.  Any disagreement at an index below both lengths' maximum now
  forces the collision case.
* `PaddedAgreementSameTree` — lists that agree at every padded entry are the same tree at every
  height, with no collision on any path, for every hash.  (`same_tree_of_getD_eq`, an internal
  lemma of `../Proofs/RootForgeryPinned.lean`, stated as a property.)
* `PaddedAgreementIffExtension` — agreement at every padded entry is exactly `PaddingExtension`.
* `CollisionFreeRootEqIffExtension` — within capacity, two lists have equal roots and no collision
  on any committed index's path exactly when one is the other followed by padding leaves.  The
  padding ambiguity is the only root ambiguity that needs no collision.
* `RootCommitsListUnderTrailingSeparation` — so root binding with no length premise needs only
  that neither list ENDS with the padding constant, which is weaker than
  `RootCommitsListUnderPadSeparation`'s "neither list contains it".

Witnesses: `RootCommitsListOrBreakStrongSatisfiable` reaches the padding case alone for every
hash; `RootCommitsListOrBreakStrongUnmasksCollision` is an instance on which the original's
padding disjunct holds, the strong padding case fails, and the collision is what holds;
`PaddedAgreementSameTreeSatisfiable` and `CollisionFreeRootEqIffExtensionSatisfiable` meet those
premises with two different lists; `RootCommitsListUnderTrailingSeparationSatisfiable` meets that
premise with a list that holds the padding constant.  The equal-lists case alone is the original
`MerkleSpec.Pinned.Properties.RootCommitsListOrBreakSatisfiable` instance.
-/

namespace MerkleSpec.PinnedStrong

open Clear MerkleSpec MerkleSpec.Pinned

/-- **ROOT BINDING WITH NO EQUAL-LENGTH PREMISE, PADDING CASE PINNED.**  Two leaf lists within
capacity with the same root at `height` are

1. equal; or
2. a padding hit that is a padding extension: the longer list holds the padding constant at the
   shorter one's length (`PaddingHit`), the two agree at every index read with the padding
   default, and so one is the other followed by copies of `z0` (`PaddingExtension`); or
3. at an index below both lengths' maximum where they differ, the two trees collide on that
   index's path.

This strengthens `MerkleSpec.Pinned.Properties.RootCommitsListOrBreak`, whose second case is a
bare `PaddingHit`: there, two lists that differ at an occupied index can satisfy the padding
case, and the collision at that index is never named
(`RootCommitsListOrBreakStrongUnmasksCollision`).  Here, if the lists differ at any index below
both lengths' maximum, the conclusion is case 3: a located collision at a differing index (and
there is one at every differing index, by `MerkleSpec.Pinned.Properties.RootPinsEntryOrCollision`).
The three cases exclude each other, and in case 2 no collision is located on any path, for every
hash (`PaddedAgreementSameTree`). -/
def Properties.RootCommitsListOrBreakStrong : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ),
    L₁.length ≤ 2 ^ height → L₂.length ≤ 2 ^ height →
    rootOf h z0 L₁ height = rootOf h z0 L₂ height →
      L₁ = L₂
        ∨ (PaddingHit z0 L₁ L₂ ∧ (∀ i, L₁.getD i z0 = L₂.getD i z0)
            ∧ PaddingExtension z0 L₁ L₂)
        ∨ ∃ i < max L₁.length L₂.length,
            L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i

/-- **LISTS THAT AGREE AT EVERY PADDED ENTRY ARE THE SAME TREE, FOR EVERY HASH.**  If two leaf
lists agree at every index read with the padding default `z0`, then at every height they have
the same root and no collision is located on any index's path.  No capacity premise.  This is
`MerkleSpec.Pinned.same_tree_of_getD_eq` (`../Proofs/RootForgeryPinned.lean`), which that file
proves and uses for `PaddingHitFires` but does not state as a property. -/
def Properties.PaddedAgreementSameTree : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256),
    (∀ j, L₁.getD j z0 = L₂.getD j z0) →
      ∀ height, rootOf h z0 L₁ height = rootOf h z0 L₂ height
        ∧ ∀ i, ¬ TreeCollision h z0 L₁ L₂ height i

/-- **AGREEMENT AT EVERY PADDED ENTRY IS EXACTLY A PADDING EXTENSION.**  Two lists agree at every
index read with the default `z0` iff one is the other followed by copies of `z0`. -/
def Properties.PaddedAgreementIffExtension : Prop :=
  ∀ (z0 : UInt256) (L₁ L₂ : List UInt256),
    (∀ j, L₁.getD j z0 = L₂.getD j z0) ↔ PaddingExtension z0 L₁ L₂

/-- **WITHIN CAPACITY, THE PADDING AMBIGUITY IS THE ONLY COLLISION-FREE ROOT AMBIGUITY.**  For two
lists within capacity at `height`: they have the same root and no collision is located on the
path of any index `i < 2^height` iff one is the other followed by copies of the padding
constant.  So with no located collision, the root commits the leaf list up to trailing padding
leaves, and nothing else. -/
def Properties.CollisionFreeRootEqIffExtension : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ),
    L₁.length ≤ 2 ^ height → L₂.length ≤ 2 ^ height →
      ((rootOf h z0 L₁ height = rootOf h z0 L₂ height
          ∧ ∀ i < 2 ^ height, ¬ TreeCollision h z0 L₁ L₂ height i)
        ↔ PaddingExtension z0 L₁ L₂)

/-- **ROOT BINDING UNDER TRAILING SEPARATION.**  If neither list ENDS with the padding constant
(`getLast? ≠ some z0`; the empty list qualifies), two lists within capacity with the same root
are equal, or at an index where they differ the trees collide on its path.  No length premise.
The premise is strictly weaker than the premises `z0 ∉ L₁`, `z0 ∉ L₂` of
`MerkleSpec.Pinned.Properties.RootCommitsListUnderPadSeparation`
(`RootCommitsListUnderTrailingSeparationSatisfiable`: a list holding `z0` at a non-final
position qualifies).  With the padding case pinned, two different lists share a
root without a collision only when the longer one ends in padding leaves.  The collision case
is reached under this premise by the instance of
`MerkleSpec.Pinned.Properties.RootCommitsListCollisionFires` (`[1]` and `[2, 5]` under
`constHash` with padding `0`). -/
def Properties.RootCommitsListUnderTrailingSeparation : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ),
    L₁.getLast? ≠ some z0 → L₂.getLast? ≠ some z0 →
    L₁.length ≤ 2 ^ height → L₂.length ≤ 2 ^ height →
    rootOf h z0 L₁ height = rootOf h z0 L₂ height →
      L₁ = L₂ ∨ ∃ i < max L₁.length L₂.length,
        L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i

/-! ## Witnesses -/

/-- `RootCommitsListOrBreakStrong`: for every hash, `[a]` and `[a, z0]` meet its premises
(within capacity at height 1, the same root) with the lists different, and the padding case
(case 2) holds while the collision case (case 3) fails. -/
def Properties.RootCommitsListOrBreakStrongSatisfiable : Prop :=
  ∀ (h : Hash) (z0 a : UInt256),
    ([a] : List UInt256).length ≤ 2 ^ 1 ∧ ([a, z0] : List UInt256).length ≤ 2 ^ 1
      ∧ rootOf h z0 [a] 1 = rootOf h z0 [a, z0] 1
      ∧ ([a] : List UInt256) ≠ [a, z0]
      ∧ PaddingHit z0 [a] [a, z0]
      ∧ (∀ i, ([a] : List UInt256).getD i z0 = ([a, z0] : List UInt256).getD i z0)
      ∧ PaddingExtension z0 [a] [a, z0]
      ∧ ¬ ∃ i < max ([a] : List UInt256).length ([a, z0] : List UInt256).length,
          ([a] : List UInt256).getD i z0 ≠ ([a, z0] : List UInt256).getD i z0
            ∧ TreeCollision h z0 [a] [a, z0] 1 i

/-- **THE STRONG FORM EXTRACTS THE COLLISION THAT `RootCommitsListOrBreak` LETS A PADDING HIT
EXCUSE.**  Under `constHash` with padding `0`, `[1]` and `[2, 0]` are within capacity at height 1
and have the same root.  They form a `PaddingHit` (the longer list holds `0` at index 1), so the
original `RootCommitsListOrBreak` is satisfied by its padding disjunct.  But they differ at index
0, a position both lists occupy: they do not agree at every padded entry and neither is the other
followed by padding.  So the padding case of `RootCommitsListOrBreakStrong` fails, the lists are
not equal, and the conclusion must be case 3, the collision located on index 0's path. -/
def Properties.RootCommitsListOrBreakStrongUnmasksCollision : Prop :=
  ([1] : List UInt256).length ≤ 2 ^ 1 ∧ ([2, 0] : List UInt256).length ≤ 2 ^ 1
    ∧ rootOf constHash 0 [1] 1 = rootOf constHash 0 [2, 0] 1
    ∧ PaddingHit 0 [1] [2, 0]
    ∧ ([1] : List UInt256) ≠ [2, 0]
    ∧ ¬ (∀ i, ([1] : List UInt256).getD i 0 = ([2, 0] : List UInt256).getD i 0)
    ∧ ¬ PaddingExtension 0 [1] [2, 0]
    ∧ ([1] : List UInt256).getD 0 0 ≠ ([2, 0] : List UInt256).getD 0 0
    ∧ TreeCollision constHash 0 [1] [2, 0] 1 0

/-- `PaddedAgreementSameTree`: its premise is met by two different lists, `[a]` and
`[a, z0, z0]`. -/
def Properties.PaddedAgreementSameTreeSatisfiable : Prop :=
  ∀ (z0 a : UInt256),
    (∀ j, ([a] : List UInt256).getD j z0 = ([a, z0, z0] : List UInt256).getD j z0)
      ∧ ([a] : List UInt256) ≠ [a, z0, z0]

/-- `CollisionFreeRootEqIffExtension`: its premises are met by `[a]` and `[a, z0, z0]` at
height 2, two different lists on which the right-hand side holds (so, by the property, they have
the same root and no located collision).  On the instance of
`RootCommitsListOrBreakStrongUnmasksCollision` both sides fail. -/
def Properties.CollisionFreeRootEqIffExtensionSatisfiable : Prop :=
  ∀ (z0 a : UInt256),
    ([a] : List UInt256).length ≤ 2 ^ 2 ∧ ([a, z0, z0] : List UInt256).length ≤ 2 ^ 2
      ∧ PaddingExtension z0 [a] [a, z0, z0] ∧ ([a] : List UInt256) ≠ [a, z0, z0]

/-- `RootCommitsListUnderTrailingSeparation`: for every hash and every `a ≠ z0`, met by `[z0, a]`
compared with itself (with no located collision, the two sides must be equal).  The list holds
the padding constant, so `RootCommitsListUnderPadSeparation` does not apply to it, but it does
not end with it. -/
def Properties.RootCommitsListUnderTrailingSeparationSatisfiable : Prop :=
  ∀ (h : Hash) (z0 a : UInt256), a ≠ z0 →
    ([z0, a] : List UInt256).getLast? ≠ some z0 ∧ z0 ∈ ([z0, a] : List UInt256)
      ∧ ([z0, a] : List UInt256).length ≤ 2 ^ 1
      ∧ rootOf h z0 [z0, a] 1 = rootOf h z0 [z0, a] 1
      ∧ ¬ ∃ i < max ([z0, a] : List UInt256).length ([z0, a] : List UInt256).length,
          ([z0, a] : List UInt256).getD i z0 ≠ ([z0, a] : List UInt256).getD i z0
            ∧ TreeCollision h z0 [z0, a] [z0, a] 1 i

end MerkleSpec.PinnedStrong
