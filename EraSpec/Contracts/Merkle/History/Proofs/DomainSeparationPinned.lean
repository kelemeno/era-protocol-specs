import EraSpec.Contracts.Merkle.History.Properties.DomainSeparationPinned
import EraSpec.Contracts.Merkle.Proofs.DomainSeparation

/-!
# History proofs: Merkle domain separation at the interop pin's IMT padding (`c67894b9`)

Proofs of `../Properties/DomainSeparationPinned.lean`, the record of an older commit, not a claim
about `b17415d20`. They reuse the byte toolkit and the padding-general reductions of
`EraSpec.Contracts.Merkle.Proofs.DomainSeparation` (`treeRootBreak_keccak`, `imtPre_inj`, the
three-leaf run), instantiated at the pin's padding preimage `pinPaddingPre`.
-/

namespace MerkleSpec.DomainSeparation.History

open AttackVectors.BundleHashEncoding (HashCollision toBytesBE word fromBytesBE length_toBytesBE
  fromBytesBE_toBytesBE word_length uint256_val_lt word_val_inj toUInt256_val)
open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf MerkleSpec.Pinned MerkleSpec.DomainSeparation
open MerkleSpec.LastLeafFaithful (LastBatchPathAccepted)
open Contracts.InteropCommitmentTree (Leaf Tree LeafHash leafHashes TreeRootBreak InclusionAccepted
  NonInclusionAccepted Valid root setup threeLeafTree toAbs)

theorem hash_assumptions_fields_up_to_collision : Properties.HashAssumptionsFieldsUpToCollision := by
  intro keccak
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b c d h
    by_cases he : nodePre a b = nodePre c d
    · exact Or.inl (nodePre_inj he)
    · exact Or.inr ⟨he, h⟩
  · intro ℓ ℓ' hℓ hℓ' h
    by_cases he : imtPre ℓ = imtPre ℓ'
    · exact Or.inl (imtPre_inj hℓ hℓ' he)
    · exact Or.inr ⟨he, h⟩
  · intro ℓ a b h
    exact ⟨ne_pairPre_of_length_ne (by rw [imtPre_length]; decide) (a, b), h⟩
  · intro ℓ hℓ
    constructor
    · intro h
      by_cases hz : ℓ = ⟨0, 0, 0⟩
      · exact Or.inl hz
      · refine Or.inr ⟨fun he => hz ((imtPre_eq_emptyPre_iff hℓ).mp he), ?_⟩
        rw [← imtPre_zero]
        exact h
    · rintro (rfl | ⟨-, h⟩)
      · rfl
      · show keccak (imtPre ℓ) = keccak (imtPre ⟨0, 0, 0⟩)
        rw [imtPre_zero]
        exact h
  · intro a b h
    refine ⟨ne_pairPre_of_length_ne (by rw [emptyPre_length]; decide) (a, b), ?_⟩
    rw [← imtPre_zero]
    exact h

theorem hash_assumptions_fields_witness : Properties.HashAssumptionsFieldsWitness := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro κ a b c d hne
    refine ⟨plantKeccak_eq κ _ _, plantKeccak_collision κ fun he => hne ?_⟩
    obtain ⟨h1, h2⟩ := nodePre_inj he
    rw [h1, h2]
  · intro κ ℓ ℓ' hℓ hℓ' hne
    exact ⟨plantKeccak_eq κ _ _, plantKeccak_collision κ fun he => hne (imtPre_inj hℓ hℓ' he)⟩
  · intro κ ℓ a b
    exact ⟨plantKeccak_eq κ _ _, plantKeccak_collision κ
      (ne_pairPre_of_length_ne (by rw [imtPre_length]; decide) (a, b))⟩
  · intro κ ℓ hℓ hne
    refine ⟨?_, plantKeccak_collision κ fun he => hne ((imtPre_eq_emptyPre_iff hℓ).mp he)⟩
    show plantKeccak κ (imtPre ℓ) emptyPre (imtPre ℓ)
      = plantKeccak κ (imtPre ℓ) emptyPre (imtPre ⟨0, 0, 0⟩)
    rw [imtPre_zero]
    exact plantKeccak_eq κ _ _
  · intro κ a b
    refine ⟨?_, plantKeccak_collision κ
      (ne_pairPre_of_length_ne (by rw [emptyPre_length]; decide) (a, b))⟩
    show plantKeccak κ emptyPre (nodePre a b) (imtPre ⟨0, 0, 0⟩)
      = plantKeccak κ emptyPre (nodePre a b) (nodePre a b)
    rw [imtPre_zero]
    exact plantKeccak_eq κ _ _
  · intro ℓ a b
    refine ⟨?_, ?_⟩
    · show lengthKeccak (imtPre ℓ) ≠ lengthKeccak (nodePre a b)
      rw [lengthKeccak_of_length (imtPre_length ℓ), lengthKeccak_of_length (nodePre_length a b)]
      decide
    · show lengthKeccak (imtPre ⟨0, 0, 0⟩) ≠ lengthKeccak (nodePre a b)
      rw [lengthKeccak_of_length (imtPre_length _), lengthKeccak_of_length (nodePre_length a b)]
      decide
  · intro keccak
    exact ⟨rfl, fun hc => hc.1 imtPre_zero⟩
  · intro ℓ _ hv
    refine ⟨?_, ?_⟩
    · show firstWordKeccak (imtPre ℓ) ≠ firstWordKeccak (imtPre ⟨0, 0, 0⟩)
      rw [firstWordKeccak_imtPre, firstWordKeccak_imtPre]
      exact hv
    · rintro ⟨-, h⟩
      rw [firstWordKeccak_imtPre, firstWordKeccak_emptyPre] at h
      exact hv h

theorem pinPaddingPre_length_ne : pinPaddingPre.length ≠ 64 := by
  rw [pinPaddingPre, imtPre_length]; decide

theorem tree_root_break_is_keccak_collision_at_pin :
    Properties.TreeRootBreakIsKeccakCollisionAtPin := by
  intro keccak T height sibs k idx ℓ hT hℓ hb
  rcases treeRootBreak_keccak (zPre := pinPaddingPre) pinPaddingPre_length_ne hT hℓ hb with
    ⟨hle, he⟩ | hk
  · exact Or.inl ⟨hle, imtPre_inj hℓ zero_leafBounded he⟩
  · exact Or.inr hk

theorem proofs_exclusive_or_keccak_break_at_pin : Properties.ProofsExclusiveOrKeccakBreakAtPin := by
  intro keccak T hV hT height v ℓ₁ ℓ₂ i₁ i₂ s₁ s₂ k₁ k₂ hℓ₁ hℓ₂ hI hN
  rcases Contracts.InteropCommitmentTree.proofs_exclusive_or_break hV hI hN with hb | hb
  · rcases tree_root_break_is_keccak_collision_at_pin keccak T height s₁ k₁ i₁ ℓ₁ hT hℓ₁ hb with
      ⟨_, hz⟩ | hk
    · exfalso
      apply hN.nonzero
      rw [← hI.valueMatch, hz]
    · exact Or.inr (Or.inl hk)
  · rcases tree_root_break_is_keccak_collision_at_pin keccak T height s₂ k₂ i₂ ℓ₂ hT hℓ₂ hb with
      h | hk
    · exact Or.inl h
    · exact Or.inr (Or.inr hk)

theorem inclusion_sound_or_keccak_break_at_pin : Properties.InclusionSoundOrKeccakBreakAtPin := by
  intro keccak T hV hT height v ℓ idx sibs k hℓ hI
  rcases Contracts.InteropCommitmentTree.inclusion_sound_or_break hI with hmem | hb
  · exact Or.inl hmem
  · rcases tree_root_break_is_keccak_collision_at_pin keccak T height sibs k idx ℓ hT hℓ hb with
      ⟨_, hz⟩ | hk
    · left
      have hv : v = 0 := by rw [← hI.valueMatch, hz]
      rw [hv]
      exact zero_mem_keys_of_valid hV
    · exact Or.inr hk

theorem non_inclusion_sound_or_keccak_break_at_pin :
    Properties.NonInclusionSoundOrKeccakBreakAtPin := by
  intro keccak T height v ℓ idx sibs k hT hℓ hN
  rcases Contracts.InteropCommitmentTree.non_inclusion_sound_or_break hN with hW | hb
  · exact Or.inl hW
  · rcases tree_root_break_is_keccak_collision_at_pin keccak T height sibs k idx ℓ hT hℓ hb with
      h | hk
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr hk)

theorem padding_forgery_is_the_only_keccak_free_break :
    Properties.PaddingForgeryIsTheOnlyKeccakFreeBreak := by
  intro keccak a b ha hab
  obtain ⟨hV, hI, hN⟩ := Contracts.InteropCommitmentTree.proofs_exclusive_or_break_satisfiable
    (efficientHash keccak) (hashLeaf keccak) a b ha hab
  obtain ⟨_, hbreak⟩ := Contracts.InteropCommitmentTree.padding_countermodel_locates_padding_hit
    (efficientHash keccak) (hashLeaf keccak) a b
  have hT := threeLeafTree_bounded a b
  have hcount : (threeLeafTree a b).leafCount = 3 := rfl
  refine ⟨hV, hT, hT 1 (by rw [hcount]; norm_num), zero_leafBounded, hI, hN, hbreak, ?_, ?_⟩
  · exact imt_keccak_break_not_tautology keccak pinPaddingPre (threeLeafTree a b) 2 1
      (by rw [hcount]; norm_num)
  · intro hk
    cases hk with
    | wrongLength hh => cases hh <;> omega
    | pathCollision _ hc =>
      apply honest_walk_no_collision (efficientHash keccak) (imtPadding keccak)
        (leafHashes (hashLeaf keccak) (threeLeafTree a b)) 2 3
      rw [getD_default _ _ _ (by rw [Contracts.InteropCommitmentTree.leafHashes_length, hcount])]
      exact (pathCollision_iff ..).mpr hc
    | leafCollision hidx _ =>
      rw [hcount] at hidx
      omega
    | paddingCollision _ hc => exact hc.1 rfl

/-! ## Certificates -/

theorem PinPaddingIsEmptyPre : Properties.PinPaddingIsEmptyPre := MerkleSpec.DomainSeparation.pinPaddingPre_eq

theorem HashAssumptionsFieldsUpToCollision : Properties.HashAssumptionsFieldsUpToCollision :=
  hash_assumptions_fields_up_to_collision

theorem HashAssumptionsFieldsWitness : Properties.HashAssumptionsFieldsWitness :=
  hash_assumptions_fields_witness

theorem TreeRootBreakIsKeccakCollisionAtPin : Properties.TreeRootBreakIsKeccakCollisionAtPin :=
  tree_root_break_is_keccak_collision_at_pin

theorem ProofsExclusiveOrKeccakBreakAtPin : Properties.ProofsExclusiveOrKeccakBreakAtPin :=
  proofs_exclusive_or_keccak_break_at_pin

theorem InclusionSoundOrKeccakBreakAtPin : Properties.InclusionSoundOrKeccakBreakAtPin :=
  inclusion_sound_or_keccak_break_at_pin

theorem NonInclusionSoundOrKeccakBreakAtPin : Properties.NonInclusionSoundOrKeccakBreakAtPin :=
  non_inclusion_sound_or_keccak_break_at_pin

theorem PaddingForgeryIsTheOnlyKeccakFreeBreak :
    Properties.PaddingForgeryIsTheOnlyKeccakFreeBreak :=
  padding_forgery_is_the_only_keccak_free_break

end MerkleSpec.DomainSeparation.History
