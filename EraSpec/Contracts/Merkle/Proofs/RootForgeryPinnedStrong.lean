import EraSpec.Contracts.Merkle.Properties.RootForgeryPinnedStrong
import EraSpec.Contracts.Merkle.Proofs.RootForgeryPinned

/-!
# Proofs: root binding without the equal-length premise, padding case pinned

Proofs of `EraSpec.Contracts.Merkle.Properties.RootForgeryPinnedStrong`.  Everything reduces to
two existing engines of `../Proofs/RootForgeryPinned.lean`: `root_pins_entry_or_collision`
(equal roots pin every committed entry, or a collision on its path) and `same_tree_of_getD_eq`
(lists that agree at every padded entry are the same tree, with no collision), plus one list
lemma, `getD_append_replicate_pad`: trailing padding leaves change no entry read with the
padding default.
-/

namespace MerkleSpec.PinnedStrong

open Clear MerkleSpec MerkleSpec.Verifier MerkleSpec.Pinned

/-! ## Padding extensions -/

/-- Appending any number of padding leaves changes no `getD` read with the padding default. -/
theorem getD_append_replicate_pad (z0 : UInt256) : ∀ (L : List UInt256) (k j : ℕ),
    (L ++ List.replicate k z0).getD j z0 = L.getD j z0
  | [], 0, _ => rfl
  | [], _ + 1, 0 => rfl
  | [], k + 1, j + 1 => getD_append_replicate_pad z0 [] k j
  | _ :: _, _, 0 => rfl
  | _ :: t, k, j + 1 => getD_append_replicate_pad z0 t k j

/-- A list that agrees with a longer one at every padded entry is a prefix of it, the rest
being padding. -/
theorem extension_of_padded_agreement (z0 : UInt256) (L₁ L₂ : List UInt256)
    (hle : L₁.length ≤ L₂.length) (hL : ∀ j, L₁.getD j z0 = L₂.getD j z0) :
    L₂ = L₁ ++ List.replicate (L₂.length - L₁.length) z0 := by
  symm
  refine ext_getD' z0 _ _ (by simp only [List.length_append, List.length_replicate]; omega)
    (fun n _ => ?_)
  rw [getD_append_replicate_pad]
  exact hL n

theorem padded_agreement_iff_extension (z0 : UInt256) (L₁ L₂ : List UInt256) :
    (∀ j, L₁.getD j z0 = L₂.getD j z0) ↔ PaddingExtension z0 L₁ L₂ := by
  constructor
  · intro hL
    rcases le_total L₁.length L₂.length with hle | hle
    · exact ⟨_, Or.inl (extension_of_padded_agreement z0 L₁ L₂ hle hL)⟩
    · exact ⟨_, Or.inr (extension_of_padded_agreement z0 L₂ L₁ hle (fun j => (hL j).symm))⟩
  · rintro ⟨k, rfl | rfl⟩ j
    · exact (getD_append_replicate_pad z0 L₁ k j).symm
    · exact getD_append_replicate_pad z0 L₂ k j

/-! ## The classification -/

theorem root_commits_list_or_break_strong (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (height : ℕ) (hcap₁ : L₁.length ≤ 2 ^ height) (hcap₂ : L₂.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    L₁ = L₂
      ∨ (PaddingHit z0 L₁ L₂ ∧ (∀ i, L₁.getD i z0 = L₂.getD i z0) ∧ PaddingExtension z0 L₁ L₂)
      ∨ ∃ i < max L₁.length L₂.length,
          L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i := by
  by_cases hall : ∀ i, L₁.getD i z0 = L₂.getD i z0
  · rcases root_commits_list_or_break h z0 L₁ L₂ height hcap₁ hcap₂ hroot
      with he | hp | ⟨i, _, hne, _⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl ⟨hp, hall, (padded_agreement_iff_extension z0 L₁ L₂).mp hall⟩)
    · exact absurd (hall i) hne
  · right; right
    push Not at hall
    obtain ⟨i, hne⟩ := hall
    have hi : i < max L₁.length L₂.length := by
      by_contra hge
      push Not at hge
      exact hne (by rw [getD_default L₁ i z0 (by omega), getD_default L₂ i z0 (by omega)])
    rcases root_pins_entry_or_collision h z0 L₁ L₂ height i (by omega) hroot with he | hc
    · exact absurd he hne
    · exact ⟨i, hi, hne, hc⟩

theorem collision_free_root_eq_iff_extension (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (height : ℕ) (hcap₁ : L₁.length ≤ 2 ^ height) (hcap₂ : L₂.length ≤ 2 ^ height) :
    (rootOf h z0 L₁ height = rootOf h z0 L₂ height
        ∧ ∀ i < 2 ^ height, ¬ TreeCollision h z0 L₁ L₂ height i)
      ↔ PaddingExtension z0 L₁ L₂ := by
  rw [← padded_agreement_iff_extension]
  constructor
  · rintro ⟨hroot, hnc⟩ j
    by_cases hj : j < 2 ^ height
    · rcases root_pins_entry_or_collision h z0 L₁ L₂ height j hj hroot with he | hc
      · exact he
      · exact absurd hc (hnc j hj)
    · rw [getD_default L₁ j z0 (by omega), getD_default L₂ j z0 (by omega)]
  · intro hL
    obtain ⟨hroot, hnc⟩ := same_tree_of_getD_eq h z0 L₁ L₂ hL height
    exact ⟨hroot, fun i _ => hnc i⟩

/-- A list followed by at least one padding leaf ends with the padding constant. -/
theorem getLast?_append_replicate_succ (z0 : UInt256) (L : List UInt256) (k : ℕ) :
    (L ++ List.replicate (k + 1) z0).getLast? = some z0 := by
  rw [List.getLast?_append, List.getLast?_replicate]
  simp

/-- A padding extension between two lists, one of them longer (a padding hit), puts the padding
constant at the end of the longer one. -/
theorem padding_extension_ends_with_pad (z0 : UInt256) (L₁ L₂ : List UInt256)
    (hp : PaddingHit z0 L₁ L₂) (hx : PaddingExtension z0 L₁ L₂) :
    L₁.getLast? = some z0 ∨ L₂.getLast? = some z0 := by
  obtain ⟨k, hk | hk⟩ := hx
  · cases k with
    | zero =>
      rw [List.replicate_zero, List.append_nil] at hk
      subst hk
      rcases hp with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> omega
    | succ k => exact Or.inr (by rw [hk]; exact getLast?_append_replicate_succ z0 L₁ k)
  · cases k with
    | zero =>
      rw [List.replicate_zero, List.append_nil] at hk
      subst hk
      rcases hp with ⟨hlt, _⟩ | ⟨hlt, _⟩ <;> omega
    | succ k => exact Or.inl (by rw [hk]; exact getLast?_append_replicate_succ z0 L₂ k)

theorem root_commits_list_under_trailing_separation (h : Hash) (z0 : UInt256)
    (L₁ L₂ : List UInt256) (height : ℕ) (hz₁ : L₁.getLast? ≠ some z0)
    (hz₂ : L₂.getLast? ≠ some z0) (hcap₁ : L₁.length ≤ 2 ^ height)
    (hcap₂ : L₂.length ≤ 2 ^ height) (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    L₁ = L₂ ∨ ∃ i < max L₁.length L₂.length,
      L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i := by
  rcases root_commits_list_or_break_strong h z0 L₁ L₂ height hcap₁ hcap₂ hroot
    with he | ⟨hp, _, hx⟩ | hc
  · exact Or.inl he
  · rcases padding_extension_ends_with_pad z0 L₁ L₂ hp hx with he | he
    · exact absurd he hz₁
    · exact absurd he hz₂
  · exact Or.inr hc

/-! ## Certificates -/

theorem RootCommitsListOrBreakStrong : Properties.RootCommitsListOrBreakStrong :=
  root_commits_list_or_break_strong

theorem PaddedAgreementSameTree : Properties.PaddedAgreementSameTree :=
  fun h z0 L₁ L₂ hL height => same_tree_of_getD_eq h z0 L₁ L₂ hL height

theorem PaddedAgreementIffExtension : Properties.PaddedAgreementIffExtension :=
  padded_agreement_iff_extension

theorem CollisionFreeRootEqIffExtension : Properties.CollisionFreeRootEqIffExtension :=
  collision_free_root_eq_iff_extension

theorem RootCommitsListUnderTrailingSeparation :
    Properties.RootCommitsListUnderTrailingSeparation :=
  root_commits_list_under_trailing_separation

/-! ## Witnesses -/

/-- `[a]` and `[a, z0]` agree at every padded entry. -/
theorem getD_singleton_pad_agree (z0 a : UInt256) :
    ∀ i, ([a] : List UInt256).getD i z0 = ([a, z0] : List UInt256).getD i z0 :=
  fun i => (getD_append_replicate_pad z0 [a] 1 i).symm

theorem RootCommitsListOrBreakStrongSatisfiable :
    Properties.RootCommitsListOrBreakStrongSatisfiable := by
  intro h z0 a
  have hagree := getD_singleton_pad_agree z0 a
  have hsame := same_tree_of_getD_eq h z0 [a] [a, z0] hagree 1
  refine ⟨by simp, by simp, hsame.1, by simp, Or.inl ⟨by simp, rfl⟩, hagree,
    ⟨1, Or.inl rfl⟩, ?_⟩
  rintro ⟨i, _, hne, _⟩
  exact hne (hagree i)

theorem RootCommitsListOrBreakStrongUnmasksCollision :
    Properties.RootCommitsListOrBreakStrongUnmasksCollision := by
  unfold Properties.RootCommitsListOrBreakStrongUnmasksCollision
  refine ⟨by decide, by decide, by decide, by unfold PaddingHit; decide, by decide, ?_, ?_,
    by decide, by unfold TreeCollision; decide⟩
  · intro hall
    exact absurd (hall 0) (by decide)
  · rintro ⟨k, he | he⟩
    · have hh := congrArg List.head? he
      simp at hh
    · have hl := congrArg List.length he
      simp at hl

theorem PaddedAgreementSameTreeSatisfiable : Properties.PaddedAgreementSameTreeSatisfiable :=
  fun z0 a => ⟨fun j => (getD_append_replicate_pad z0 [a] 2 j).symm, by simp⟩

theorem CollisionFreeRootEqIffExtensionSatisfiable :
    Properties.CollisionFreeRootEqIffExtensionSatisfiable :=
  fun z0 a => ⟨by simp, by simp, ⟨2, Or.inl rfl⟩, by simp⟩

theorem RootCommitsListUnderTrailingSeparationSatisfiable :
    Properties.RootCommitsListUnderTrailingSeparationSatisfiable := by
  intro h z0 a ha
  refine ⟨by simp [ha], by simp, by simp, rfl, ?_⟩
  rintro ⟨i, _, hne, _⟩
  exact hne rfl

end MerkleSpec.PinnedStrong
