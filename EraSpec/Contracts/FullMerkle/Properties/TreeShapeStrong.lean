import EraSpec.Contracts.FullMerkle.Specs.TreeShapeStrong

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false

/-!
# Properties: the padding ambiguity, within capacity and located

Statements about `EraSpec.Contracts.FullMerkle.Specs.TreeShapeStrong`; proofs in
`EraSpec.Contracts.FullMerkle.Proofs.TreeShapeStrong`.  No hash premise.

* `rootOf_append_padding` — appending any number of padding leaves to a list of ANY length
  leaves its root unchanged at every height.  (`TreeShape.rootOf_trailing_padding` is the case of
  one leaf on an odd-length list.)
* `padding_ambiguity_within_capacity` — the attack: a list and the same list followed by `k > 0`
  padding leaves, both within capacity, of different lengths, with the same root; the pair is a
  `PaddingHit` and no `TreeCollision` is located on any path, for every hash.
* `padding_twin_exists_iff_not_full` — such a twin within capacity exists exactly when the list
  is below capacity.  So every tree with a free slot has a padded twin at the same root.
* `padding_ambiguity_forges_root_pinned` — `TreeShape.padding_ambiguity_forges_root` as its
  docstring describes it: `[a]` and `[a, z0]`, within capacity at height 1, the same root, and no
  collision.  It is the instance `L = [a]`, `k = 1`, `height = 1` of the attack.
* `padding_ambiguity_within_capacity_satisfiable` — the attack's premises met by a nonempty list.

The root-binding statement that accounts for this ambiguity, with no equal-length premise, is
`MerkleSpec.PinnedStrong.Properties.RootCommitsListOrBreakStrong`, and
`MerkleSpec.PinnedStrong.Properties.CollisionFreeRootEqIffExtension` shows the padding twins are
the only pairs with equal roots and no located collision.
-/

namespace AttackVectors.TreeShapeStrong

open Clear MerkleSpec MerkleSpec.Pinned

/-- **TRAILING PADDING LEAVES NEVER CHANGE THE ROOT.**  For every hash, every list `L` of any
length, every number `k` of appended padding leaves `z0` and every height, the tree over
`L ++ replicate k z0` has the root of the tree over `L`.  At level 0 the appended leaves are `z0`,
which is what the zero-padded frontier reads; at each level above, the extra entries are the
level's zero, which is again what the frontier reads.  So the root does not commit the number of
leaves, whatever the parity of `L`. -/
abbrev Properties.rootOf_append_padding (h : Hash) (z0 : UInt256) (L : List UInt256)
    (k height : ℕ) :=
  rootOf h z0 (L ++ List.replicate k z0) height = rootOf h z0 L height

/-- **THE PADDING AMBIGUITY WITHIN CAPACITY, LOCATED.**  For every hash `h`: if `L` followed by
`k > 0` padding leaves fits at `height`, then `L` fits too, the two lists have different lengths
and differ, they have the same root at `height`, the pair is a `PaddingHit` (the longer list holds
`z0` at `L`'s length), and no `TreeCollision` is located on any index's path.  So this is no
failure of the node hash: the conclusion `L₁ = L₂ ∨ (a located collision)` of root binding fails
here for every hash, and only the equal-length premise (or a padding constant that no real leaf
can equal) excludes it. -/
abbrev Properties.padding_ambiguity_within_capacity (h : Hash) (z0 : UInt256) (L : List UInt256)
    (k height : ℕ) (hk : 0 < k) (hcap : (L ++ List.replicate k z0).length ≤ 2 ^ height) :=
  L.length ≤ 2 ^ height ∧ L.length ≠ (L ++ List.replicate k z0).length
    ∧ L ≠ L ++ List.replicate k z0
    ∧ rootOf h z0 L height = rootOf h z0 (L ++ List.replicate k z0) height
    ∧ PaddingHit z0 L (L ++ List.replicate k z0)
    ∧ ∀ i, ¬ TreeCollision h z0 L (L ++ List.replicate k z0) height i

/-- **EVERY TREE WITH A FREE SLOT HAS A PADDED TWIN.**  Some `k > 0` padding leaves can be
appended to `L` within capacity at `height` iff `L` is below capacity.  Together with
`padding_ambiguity_within_capacity`: exactly the full trees (`L.length = 2 ^ height`) have no
within-capacity twin at their root. -/
abbrev Properties.padding_twin_exists_iff_not_full (z0 : UInt256) (L : List UInt256)
    (height : ℕ) :=
  (∃ k, 0 < k ∧ (L ++ List.replicate k z0).length ≤ 2 ^ height) ↔ L.length < 2 ^ height

/-- **`TreeShape.padding_ambiguity_forges_root`, PINNED.**  For every hash `h`, padding constant
`z0` and leaf `a`: `[a]` and `[a, z0]` are within capacity at height 1, have different lengths,
differ, have the same root at height 1 (`h a z0` both ways), and no collision is located on any
path.  This is what the docstring of `padding_ambiguity_forges_root` describes; that statement's
bare existential is also met by capacity overflow (`[a]` and `[a, a]` at height 0), with no
padding leaf involved.  Since no collision is located, the conclusion of the pinned root-binding
form `MerkleSpec.Pinned.Properties.RootOfInjOrCollision` (equal lists, or a collision at a
differing index) fails on this pair for every hash, and only its equal-length premise excludes
it.  (No `UInt256` hash is pair-injective, `Contracts.InteropCommitmentTree.not_nodeInj`, so the
original's "even for a perfectly pair-injective hash" is read here as "for every hash, with no
collision located".) -/
abbrev Properties.padding_ambiguity_forges_root_pinned (h : Hash) (z0 a : UInt256) :=
  ([a] : List UInt256).length ≤ 2 ^ 1 ∧ ([a, z0] : List UInt256).length ≤ 2 ^ 1
    ∧ ([a] : List UInt256).length ≠ ([a, z0] : List UInt256).length
    ∧ ([a] : List UInt256) ≠ [a, z0]
    ∧ rootOf h z0 [a] 1 = rootOf h z0 [a, z0] 1
    ∧ ∀ i, ¬ TreeCollision h z0 [a] [a, z0] 1 i

/-- `padding_ambiguity_within_capacity`: its premises are met by the nonempty list `[a]` with one
padding leaf at height 1 (and, by `padding_twin_exists_iff_not_full`, by every list below
capacity at its height). -/
abbrev Properties.padding_ambiguity_within_capacity_satisfiable (z0 a : UInt256) :=
  ([a] : List UInt256) ≠ [] ∧ 0 < 1 ∧ ([a] ++ List.replicate 1 z0).length ≤ 2 ^ 1

end AttackVectors.TreeShapeStrong
