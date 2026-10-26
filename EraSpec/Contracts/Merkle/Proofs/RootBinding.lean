import EraSpec.Contracts.Merkle.Properties.RootBinding
import EraSpec.Contracts.FullMerkle.Proofs.Model


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/RootBinding.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  ROOT BINDING — the abstract kernel of the last remaining obligation.

  `AttackVectors.CrossContract` reduced delivered-XOR-reclaimed to one hypothesis,
  `habs`: that every leaf committed under a published root really is a member of
  the represented leaf set.  That is ROOT BINDING, and it is the last real gap in
  the no-theft chain.

  Root binding factors into three pieces:

    (1) ABSTRACT KERNEL — equal roots force equal leaf lists, so membership
        transfers between any two lists sharing a root.  Proved here from
        `MerkleSpec.rootOf_inj_of_h_inj'` (M-D without its spurious nonemptiness
        hypothesis), with node-hash pair-injectivity as a HYPOTHESIS standing in for
        keccak collision resistance.  Since `hne` is gone these apply at an EMPTY
        tree too, which matters for instantiating them at genesis.
    (2) FOLD CORRESPONDENCE — the contract's `foldRoot` path recomputation agrees
        with `MerkleSpec.rootOf` on the same leaves.  NOT proved; this is the
        root-fidelity track (`ROOT_FIDELITY_BLUEPRINT.md` R0–R9), of which only the
        pure Merkle layer M-A/M-B/M-C/M-D exists.
    (3) SET CORRESPONDENCE — the leaf LIST the Merkle layer talks about and the
        leaf SET `leafSetOf` talks about are the same leaves.  NOT proved.

  Only (1) is established here.  Stating it separately is worth doing anyway: it
  shows the cryptographic content of root binding is exactly M-D, and that (2) and
  (3) are model-correspondence work rather than further cryptography.
-/

namespace AttackVectors.RootBinding


open Clear MerkleSpec


/-- **MEMBERSHIP TRANSFERS ACROSS EQUAL ROOTS.**  The abstract kernel of root
binding: for a non-full tree, if two equal-length leaf lists recompute to the same
root under a pair-injective node hash, then any leaf of one is a leaf of the other.

This is the shape the `habs` obligation needs — "a leaf committed under root `R` is
a leaf of any list whose root is `R`" — with the cryptographic assumption isolated
as `hinj`. -/
theorem mem_of_rootOf_eq (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height)
    {x : UInt256} (hx : x ∈ L₁) :
    Properties.mem_of_rootOf_eq (h := h) (z0 := z0) (hinj := hinj) (L₁ := L₁) (L₂ := L₂) (height := height) (hlen := hlen) (hcap := hcap) (hroot := hroot) (x := x) (hx := hx) := by
  unfold Properties.mem_of_rootOf_eq
  exact
    by
      rw [← rootOf_inj_of_h_inj' h z0 hinj L₁ L₂ height hlen hcap hroot]
      exact hx


/-- **THE INDEXED FORM.**  The same fact at a position: equal roots force equal
entries at every index.  This is the form a Merkle-path verifier consumes, since a
proof names the index it opens. -/
theorem getD_of_rootOf_eq (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height)
    (i : ℕ) (d : UInt256) :
    Properties.getD_of_rootOf_eq (h := h) (z0 := z0) (hinj := hinj) (L₁ := L₁) (L₂ := L₂) (height := height) (hlen := hlen) (hcap := hcap) (hroot := hroot) (i := i) (d := d) := by
  unfold Properties.getD_of_rootOf_eq
  exact
    by
      rw [rootOf_inj_of_h_inj' h z0 hinj L₁ L₂ height hlen hcap hroot]


/-- **CONTRAPOSITIVE: A FORGED LEAF CHANGES THE ROOT.**  If a leaf appears in one
list and not the other, the two roots differ — so a published root cannot be
reused to vouch for a leaf the tree does not contain. -/
theorem rootOf_ne_of_not_mem (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length)
    (hcap : L₁.length ≤ 2 ^ height)
    {x : UInt256} (hx : x ∈ L₁) (hnx : x ∉ L₂) :
    Properties.rootOf_ne_of_not_mem (h := h) (z0 := z0) (hinj := hinj) (L₁ := L₁) (L₂ := L₂) (height := height) (hlen := hlen) (hcap := hcap) (x := x) (hx := hx) (hnx := hnx) := by
  unfold Properties.rootOf_ne_of_not_mem
  exact
    by
      intro hroot
      exact hnx (mem_of_rootOf_eq h z0 hinj L₁ L₂ height hlen hcap hroot hx)


/-! ## Piece (3): the list/set correspondence, abstract kernel

The Merkle layer speaks of a leaf LIST; `leafSetOf` speaks of a Finset image over
an index range.  Nothing in the corpus yet defines the concrete leaf-hash list
(the blueprint schedules it as R7), so there is no concrete statement to aim at.
What CAN be settled now is the generic fact underneath: an image over
`Finset.range` and a `map` over `List.range` have the same members.

Small, but it is the shape the eventual correspondence proof consumes, and it
records that the list/set mismatch is pure bookkeeping with no hidden content. -/

/-- **IMAGE OVER A RANGE = MAP OVER A RANGE.**  Membership agrees between the
Finset-image view (`leafSetOf`'s shape) and the list-map view (the Merkle layer's
shape). -/
theorem mem_image_range_iff_mem_map_range {α : Type*} [DecidableEq α]
    (f : ℕ → α) (n : ℕ) (x : α) :
    Properties.mem_image_range_iff_mem_map_range (α := α) (f := f) (n := n) (x := x) := by
  unfold Properties.mem_image_range_iff_mem_map_range
  exact
    by
      rw [Finset.mem_image, List.mem_map]
      constructor
      · rintro ⟨i, hi, hfi⟩
        exact ⟨i, List.mem_range.mpr (Finset.mem_range.mp hi), hfi⟩
      · rintro ⟨i, hi, hfi⟩
        exact ⟨i, Finset.mem_range.mpr (List.mem_range.mp hi), hfi⟩


/-- The `leafSetOf`-shaped direction, spelled out: a value is in the image exactly
when some in-range index maps to it. -/
theorem mem_image_range_iff {α : Type*} [DecidableEq α]
    (f : ℕ → α) (n : ℕ) (x : α) :
    Properties.mem_image_range_iff (α := α) (f := f) (n := n) (x := x) := by
  unfold Properties.mem_image_range_iff
  exact
    by
      rw [Finset.mem_image]
      constructor
      · rintro ⟨i, hi, hfi⟩
        exact ⟨i, Finset.mem_range.mp hi, hfi⟩
      · rintro ⟨i, hi, hfi⟩
        exact ⟨i, Finset.mem_range.mpr hi, hfi⟩


end AttackVectors.RootBinding
