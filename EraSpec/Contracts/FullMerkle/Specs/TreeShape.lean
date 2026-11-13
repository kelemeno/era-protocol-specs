import EraSpec.Contracts.FullMerkle.Specs.Model


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/TreeShape.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  TREE-SHAPE ATTACK VECTORS — what happens when the SHAPE hypotheses of the
  pure Merkle layer (`specs/MerkleSpec.lean`) are dropped.  Companion to
  `specs/AttackVectors/RootForgery.lean`, which covers the attacks ruled out
  UNDER those hypotheses; this file proves the hypotheses themselves are
  INDISPENSABLE, by exhibiting the attacks that appear the moment one is
  removed.

  (A) CAPACITY-OVERFLOW ATTACK — the `hcap : L.length ≤ 2^height` hypothesis
      of `MerkleSpec.rootOf_inj_of_h_inj` is sharp.
      * `capacity_overflow_forges_root`: for ANY hash `h`, ANY zero `z0`, and
        ANY two distinct values `a ≠ b` there are a height and two
        equal-length, nonempty leaf lists that VIOLATE the capacity bound,
        DIFFER, and yet recompute to the SAME root.  Witness: `height = 0`,
        where `rootOf h z0 L 0 = L.headD z0` reads only the head — `[a, a]`
        and `[a, b]` collide.  A tree published at a height too small for its
        leaf count does not commit its leaves: inclusion proofs for the
        overflowed positions are forgeable.
        `h` is UNIVERSALLY quantified, so this holds even for a
        pair-injective (collision-resistant) hash: `hcap` is genuinely
        independent of `hinj`, and no strength of hash can substitute for
        checking the height bound.
        (Parameterized over `a ≠ b` rather than concrete `Fin (2^256)`
        numerals, which is strictly more general; any two distinct field
        values instantiate it.)
      * Positive companion — `capacity_top_is_singleton` (citing
        `MerkleSpec.levels_height_singleton`) and `capacity_ok_root_commits`
        (citing `MerkleSpec.rootOf_inj_of_h_inj`): UNDER the capacity bound
        the level-`height` list is exactly the singleton `[root]`, and the
        root pins every leaf.  Capacity is the dividing line.

  (B) ZEROS-COLLISION / PADDING-AMBIGUITY ATTACK — the tree pads an absent
      right sibling at level `l` with `zeros h z0 l`.  A REAL leaf whose value
      equals the level-0 padding constant `z0` is therefore indistinguishable
      from an ABSENT position:
      * `levelUp_pad_eq_real` (rfl): `levelUp h z [a] = levelUp h z [a, z]` —
        the parent level cannot tell "one leaf, padded" from "two leaves, the
        second being the padding value".
      * `levelUp_trailing_padding` / `levels_trailing_padding`: the general
        form — appending a trailing `z0` leaf to any ODD-length leaf list
        leaves every level `l ≥ 1` literally unchanged.
      * `rootOf_trailing_padding`: lifted to roots at EVERY height (height 0
        included, since an odd-length list is nonempty and keeps its head).
      * `padding_ambiguity_forges_root`: the packaged attack, proved with the
        witness `[a]` vs `[a, z0]` at height 1.  AS STATED it is only an
        existential with no capacity bound and no link between the two
        lists, so it is also met by capacity overflow with no padding leaf
        (`[a]` vs `[a, a]` at height 0, attack (A)).  The within-capacity,
        located form is `TreeShapeStrong.padding_ambiguity_forges_root_pinned`
        (for every hash: `[a]` and `[a, z0]` within capacity at height 1, the
        same root, no collision on any path), generalized by
        `TreeShapeStrong.padding_ambiguity_within_capacity` to every list
        followed by any number of padding leaves.  As no collision is
        involved, the pinned root-binding conclusion (`RootOfInjOrCollision`:
        equal lists, or a located collision) fails on that pair for every
        hash, and only its equal-length premise excludes it: the root
        commits the leaf CONTENT only relative to a known leaf COUNT.
        (`MerkleSpec.rootOf_inj_of_h_inj` itself takes global
        pair-injectivity, which no `UInt256` hash has, so no instance can
        refute it with `hlen` dropped.)

      This is the FullMerkle-level analogue of the known IMT vulnerability:
      empty slots MUST be padded with a dedicated constant that is provably
      outside the range of real leaf values — i.e. the leaf-hash domain must
      be separated from the padding constant (e.g. real leaves are hashes of
      nonempty payloads and `z0` is reserved / not a possible leaf hash).
      Nothing at this pure layer can rule the collision out, because at this
      layer a leaf IS just a `UInt256`; the separation obligation lives with
      the instantiation of the leaves, and these theorems make the obligation
      explicit.

  HONEST LIMITATIONS.
  * (A) is stated parameterized over two distinct values `a ≠ b` instead of
    closing the existential with concrete numerals — evaluating `Fin (2^256)`
    numeral disequalities is avoided deliberately.  Since `UInt256` has more
    than one element, this loses nothing.
  * (B)'s LEVEL-LIST equations are proved for an odd-length list (the only
    case where level 0 has a padded frontier slot): for an even-length list
    the appended `z0` occupies a genuine pair slot and DOES change the
    level-1 list (it gains the entry `h z0 z0`).  The ROOT is unchanged for
    every length all the same, since that entry is the level-1 zero the
    frontier reads anyway: `TreeShapeStrong.rootOf_append_padding` (any
    length, any number of padding leaves, every height).  The packaged
    `padding_ambiguity_forges_root` is proved with the minimal instance
    `[a]` vs `[a, z0]` at height 1, but its statement does not pin it (see
    (B) above).

  No new axioms, no `sorry`.  Pure list reasoning on top of `MerkleSpec`.
-/

namespace AttackVectors.TreeShape


open Clear

open MerkleSpec


end AttackVectors.TreeShape
