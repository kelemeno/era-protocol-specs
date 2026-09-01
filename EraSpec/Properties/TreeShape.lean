import EraSpec.Core.Merkle

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
      * `padding_ambiguity_forges_root`: the packaged attack — for ANY `h`,
        `z0`, `a` (no injectivity assumption needed, so this holds even for a
        perfectly collision-resistant hash): `[a]` and `[a, z0]` are distinct
        leaf lists of DIFFERENT lengths with the SAME root at height 1.
        This shows the equal-length hypothesis `hlen` of
        `MerkleSpec.rootOf_inj_of_h_inj` is also indispensable: the root
        commits the leaf CONTENT only relative to a known leaf COUNT.

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
  * (B)'s trailing-padding equations are proved for an odd-length list (the
    only case where level 0 has a padded frontier slot); the packaged
    `padding_ambiguity_forges_root` uses the minimal instance `[a]` vs
    `[a, z0]` at height 1.  We do NOT claim any ambiguity for even-length
    lists (there the appended `z0` occupies a genuine pair slot and DOES
    change level 1 in general).

  No new axioms, no `sorry`.  Pure list reasoning on top of `MerkleSpec`.
-/

namespace AttackVectors.TreeShape

open Clear
open MerkleSpec

/-! ## (A) Capacity overflow forges roots -/

/-- **(A) CAPACITY-OVERFLOW ATTACK — `hcap` is indispensable.**  Drop the
capacity bound `L.length ≤ 2^height` of `rootOf_inj_of_h_inj` and root
injectivity fails outright: there are equal-length, nonempty, over-capacity
leaf lists that differ but share a root.  Witness `height = 0`: the root is
`L.headD z0`, so `[a, a]` and `[a, b]` collide for any `a ≠ b` — the second
leaf is simply never hashed into the root.  Inclusion proofs at the
overflowed index are forgeable. -/
theorem capacity_overflow_forges_root (h : Hash) (z0 : UInt256)
    (a b : UInt256) (hab : a ≠ b) :
    ∃ (L₁ L₂ : List UInt256) (height : ℕ),
      L₁.length = L₂.length ∧ L₁.length ≠ 0 ∧ ¬ (L₁.length ≤ 2 ^ height) ∧
      L₁ ≠ L₂ ∧ rootOf h z0 L₁ height = rootOf h z0 L₂ height := by
  refine ⟨[a, a], [a, b], 0, rfl, by simp, by simp, ?_, rfl⟩
  intro he
  injection he with _ h2
  injection h2 with h3 _
  exact hab h3

/-- **(A) Positive companion (dividing line, part 1).**  UNDER the capacity
bound, the level-`height` list of a nonempty tree is exactly the singleton
`[root]` — the whole tree funnels into the root, nothing overflows past it.
(Direct citation of `MerkleSpec.levels_height_singleton`.) -/
theorem capacity_top_is_singleton (h : Hash) (z0 : UInt256) (L : List UInt256)
    (height : ℕ) (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height) :
    levels h z0 L height = [rootOf h z0 L height] :=
  levels_height_singleton h z0 L height hne hcap

/-- **(A) Positive companion (dividing line, part 2).**  UNDER the capacity
bound (and pair-injectivity of `h`), the root genuinely commits every leaf:
same width + same root ⟹ same leaves.  (Direct citation of
`MerkleSpec.rootOf_inj_of_h_inj`; contrast with
`capacity_overflow_forges_root` above, which shows the statement is FALSE
without `hcap`.) -/
theorem capacity_ok_root_commits (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    L₁ = L₂ :=
  rootOf_inj_of_h_inj h z0 hinj L₁ L₂ height hlen hne hcap hroot

/-! ## (B) Zeros-collision / padding ambiguity -/

/-- **(B.1) Padded and real padding-valued slots have the same parent.**
A lone leaf `a` (frontier-padded with `z`) and the two-leaf level `[a, z]`
(whose second leaf REALLY IS the padding value) produce identical parent
levels.  Level content alone cannot distinguish "position absent, padded"
from "position present, containing the padding value". -/
theorem levelUp_pad_eq_real (h : Hash) (z a : UInt256) :
    levelUp h z [a] = levelUp h z [a, z] := rfl

/-- **(B.1), general form.**  Appending the padding value `z` to any
odd-length level is invisible to `levelUp`: the appended `z` lands exactly in
the slot the frontier edge would have padded with `z` anyway. -/
theorem levelUp_trailing_padding (h : Hash) (z : UInt256) :
    ∀ L : List UInt256, L.length % 2 = 1 →
      levelUp h z (L ++ [z]) = levelUp h z L
  | [], hodd => by simp at hodd
  | [_], _ => rfl
  | a :: b :: rest, hodd => by
      have hrest : rest.length % 2 = 1 := by
        simp only [List.length_cons] at hodd; omega
      rw [List.cons_append, List.cons_append, levelUp_cons₂, levelUp_cons₂,
          levelUp_trailing_padding h z rest hrest]

/-- **(B.1) lifted through the tree.**  For an odd-length leaf list, appending
one trailing `z0` leaf leaves EVERY level `l ≥ 1` literally unchanged: the
extra leaf is absorbed at level 1 (`levelUp_trailing_padding` with
`zeros h z0 0 = z0`) and nothing above can see it. -/
theorem levels_trailing_padding (h : Hash) (z0 : UInt256) (L : List UInt256)
    (hodd : L.length % 2 = 1) :
    ∀ l : ℕ, l ≠ 0 → levels h z0 (L ++ [z0]) l = levels h z0 L l
  | 0, hl => absurd rfl hl
  | 1, _ => by
      rw [levels_succ, levels_succ, levels_zero, levels_zero, zeros_zero,
          levelUp_trailing_padding h z0 L hodd]
  | l + 2, _ => by
      rw [levels_succ, levels_trailing_padding h z0 L hodd (l + 1) (by omega)]
      exact (levels_succ h z0 L (l + 1)).symm

/-- **(B.2) PADDING-AMBIGUITY ATTACK — root form, all heights.**  A tree over
an odd-length leaf list `L` and the tree over `L ++ [z0]` — one MORE leaf,
whose value is the padding constant — have the same root at EVERY height.
At height 0 the root only reads the (unchanged) head of the nonempty list;
at height ≥ 1 the levels coincide (`levels_trailing_padding`).  The root
therefore cannot commit the leaf COUNT: a padded (non-existent) position and
a real leaf holding the padding value are indistinguishable. -/
theorem rootOf_trailing_padding (h : Hash) (z0 : UInt256) (L : List UInt256)
    (hodd : L.length % 2 = 1) (height : ℕ) :
    rootOf h z0 (L ++ [z0]) height = rootOf h z0 L height := by
  cases height with
  | zero =>
      cases L with
      | nil => simp at hodd
      | cons a t => rfl
  | succ n =>
      rw [rootOf_def, rootOf_def,
          levels_trailing_padding h z0 L hodd (n + 1) (by omega)]

/-- **(B.2) packaged.**  For ANY `h`, `z0`, `a` — including a perfectly
pair-injective `h`, since no hypothesis on `h` is needed — the leaf lists
`[a]` and `[a, z0]` are distinct, of DIFFERENT lengths, and share the same
root at height 1 (`h a z0` both ways).  This proves the equal-length
hypothesis `hlen` of `MerkleSpec.rootOf_inj_of_h_inj` is indispensable, and
it is exactly the padding-ambiguity attack: collision-resistance of the node
hash CANNOT save a tree whose padding constant collides with a possible real
leaf value.  The fix is domain separation between real leaves and `z0`,
which is an obligation on the INSTANTIATION of the leaves, not dischargeable
at this pure layer. -/
theorem padding_ambiguity_forges_root (h : Hash) (z0 a : UInt256) :
    ∃ (L₁ L₂ : List UInt256) (height : ℕ),
      L₁.length ≠ L₂.length ∧ L₁ ≠ L₂ ∧
      rootOf h z0 L₁ height = rootOf h z0 L₂ height := by
  refine ⟨[a], [a, z0], 1, by simp, ?_, rfl⟩
  intro he
  have hlen := congrArg List.length he
  simp at hlen

end AttackVectors.TreeShape
