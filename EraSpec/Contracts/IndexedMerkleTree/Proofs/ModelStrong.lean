import EraSpec.Contracts.IndexedMerkleTree.Properties.ModelStrong
import EraSpec.Contracts.IndexedMerkleTree.Proofs.InsertGuard

/-!
# Proofs: the forged padding witness, pinned to the padding leaf

Proofs of `EraSpec.Contracts.IndexedMerkleTree.Properties.ModelStrong`.  The one observation:
in a `GapSound` set, a member with key `0` below some key `v` has a nonzero `nextKey`, so the
padding leaf `⟨0, 0⟩` is a member only of sets with no nonzero key.  The rest is
`present_not_reclaimable`, `guardedEvolution_sound` and the two-leaf witness
`AttackVectors.InsertGuard.two_leaf_soundState`.
-/

namespace IMTAbstract.ModelStrong

open Clear

/-- In a `GapSound` set with a nonzero key, the padding leaf is not a member. -/
theorem padding_leaf_not_mem {s : Finset AbsLeaf} {v : UInt256} (hgs : GapSound s)
    (hv : v ∈ keys s) (hv0 : v ≠ 0) : (⟨0, 0⟩ : AbsLeaf) ∉ s := by
  intro hmem
  obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hv
  have hlt : (⟨0, 0⟩ : AbsLeaf).key < L.key := by
    rw [hLkey]
    exact Fin.pos_of_ne_zero hv0
  exact (hgs ⟨0, 0⟩ hmem L hL hlt).1 rfl

theorem padding_leaf_forges_every_delivered {s : Finset AbsLeaf} {v : UInt256}
    (hgs : GapSound s) (hv : v ∈ keys s) (hv0 : v ≠ 0) :
    Properties.padding_leaf_forges_every_delivered hgs hv hv0 :=
  ⟨padding_leaf_not_mem hgs hv hv0, Fin.pos_of_ne_zero hv0, Or.inl rfl,
    present_not_reclaimable hgs hv⟩

theorem forged_padding_witness_pinned {a : UInt256} (ha : a ≠ 0) :
    Properties.forged_padding_witness_pinned ha := by
  have hss := AttackVectors.InsertGuard.two_leaf_soundState ha
  have hmem : a ∈ keys ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf) :=
    Finset.mem_image.mpr ⟨⟨a, 0⟩, by simp, rfl⟩
  exact ⟨hss, hmem, padding_leaf_forges_every_delivered hss.1 hmem ha⟩

theorem padding_leaf_forges_on_guarded_history {S : ℕ → Finset AbsLeaf}
    (hge : GuardedEvolution S) (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf))
    {n : ℕ} {v : UInt256} (hv : v ∈ keys (S n)) (hv0 : v ≠ 0) :
    Properties.padding_leaf_forges_on_guarded_history hge hgen hv hv0 := by
  have h0 : SoundState (S 0) := by rw [hgen]; exact genesis_soundState
  exact padding_leaf_forges_every_delivered (guardedEvolution_sound hge h0 n).1 hv hv0

theorem gapSound_iff_no_member_straddles_present (s : Finset AbsLeaf) :
    Properties.gapSound_iff_no_member_straddles_present s := by
  constructor
  · intro hgs v hv
    exact present_not_reclaimable hgs hv
  · intro hno W hW L hL hlt
    have hL' := hno L.key (Finset.mem_image.mpr ⟨L, hL, rfl⟩)
    refine ⟨fun h0 => hL' ⟨W, hW, hlt, Or.inl h0⟩, ?_⟩
    by_contra hgt
    exact hL' ⟨W, hW, hlt, Or.inr (not_le.mp hgt)⟩

/-- The step of `genesisInsertHistory`. -/
theorem genesisInsertHistory_one (a : UInt256) :
    genesisInsertHistory a 1 = ({⟨0, a⟩, ⟨a, 0⟩} : Finset AbsLeaf) := by
  simp [genesisInsertHistory, imtInsert, Finset.erase_singleton]

theorem genesisInsertHistory_guarded {a : UInt256} (ha : a ≠ 0) :
    Properties.genesisInsertHistory_guarded ha := by
  have h0 : genesisInsertHistory a 0 = ({⟨0, 0⟩} : Finset AbsLeaf) := rfl
  have hge : GuardedEvolution (genesisInsertHistory a) := by
    intro n
    cases n with
    | zero =>
      refine Or.inr ⟨⟨0, 0⟩, a, by rw [h0]; exact Finset.mem_singleton_self _,
        Fin.pos_of_ne_zero ha, Or.inl rfl, ?_, by simp [genesisInsertHistory]⟩
      rw [h0]
      intro hmem
      obtain ⟨L, hL, hLkey⟩ := Finset.mem_image.mp hmem
      rw [Finset.mem_singleton] at hL
      rw [hL] at hLkey
      exact ha hLkey.symm
    | succ m => exact Or.inl (by simp [genesisInsertHistory])
  have hsound : SoundState (genesisInsertHistory a 0) := by rw [h0]; exact genesis_soundState
  refine ⟨hge, guardedEvolution_isEvolution hge hsound, h0, genesisInsertHistory_one a, ?_⟩
  rw [genesisInsertHistory_one]
  exact Finset.mem_image.mpr ⟨⟨a, 0⟩, by simp, rfl⟩

end IMTAbstract.ModelStrong
