import EraSpec.Contracts.IndexedMerkleTree.Properties.ResetAndZeroStrong
import EraSpec.Contracts.IndexedMerkleTree.Proofs.ResetAndZero
import EraSpec.Contracts.IndexedMerkleTree.Proofs.ModelStrong

/-!
# Proofs: the zero sentinel, with its premises load-bearing

Proofs of `EraSpec.Contracts.IndexedMerkleTree.Properties.ResetAndZeroStrong`.  Presence of the
sentinel is key monotonicity (`guardedEvolution_keys_mono`, `evolution_keys_mono`); the absence
of straddling windows at present keys is `present_not_reclaimable` on the invariant
`evolution_sound`.  The countermodels are computed by `simp`.
-/

namespace AttackVectors.ResetAndZeroStrong

open Clear IMTAbstract IMTAbstract.ModelStrong

theorem guardedEvolution_keys_mono {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S) :
    Properties.guardedEvolution_keys_mono hge := by
  intro m n hmn
  induction n with
  | zero =>
    rcases Nat.le_zero.mp hmn with rfl
    exact Finset.Subset.refl _
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le hmn with rfl | hlt
    · exact Finset.Subset.refl _
    · have hstep : keys (S n) ⊆ keys (S (n + 1)) := by
        rcases hge n with heq | ⟨W, v, _, _, _, _, heq⟩
        · rw [heq]
        · rw [heq]
          exact imtInsert_keys_grow
      exact Finset.Subset.trans (ih (Nat.lt_succ_iff.mp hlt)) hstep

theorem guarded_dedup_gate_rejects_zero {S : ℕ → Finset AbsLeaf} (hge : GuardedEvolution S)
    (hgen : S 0 = ({⟨0, 0⟩} : Finset AbsLeaf)) (n : ℕ) :
    Properties.guarded_dedup_gate_rejects_zero hge hgen n :=
  guardedEvolution_keys_mono hge (Nat.zero_le n) (by rw [hgen]; exact genesis_zero_mem)

/-- A constant history is a `GuardedEvolution` and an `Evolution`. -/
theorem constHistory_guarded (s : Finset AbsLeaf) :
    GuardedEvolution (constHistory s) ∧ Evolution (constHistory s) :=
  ⟨fun _ => Or.inl rfl, fun _ => Or.inl rfl⟩

theorem zeroDroppingHistory_zero : zeroDroppingHistory 0 = ({⟨0, 0⟩} : Finset AbsLeaf) := rfl

theorem zero_not_mem_keys_zeroDroppingHistory_one :
    (0 : UInt256) ∉ keys (zeroDroppingHistory 1) := by
  simp [zeroDroppingHistory, keys]

theorem guarded_dedup_gate_rejects_zero_sharp :
    Properties.guarded_dedup_gate_rejects_zero_sharp := by
  refine ⟨⟨(constHistory_guarded ∅).1, ?_, by simp [constHistory, keys]⟩,
    ⟨zeroDroppingHistory_zero, fun hge => ?_, zero_not_mem_keys_zeroDroppingHistory_one⟩⟩
  · exact (Finset.singleton_ne_empty _).symm
  · exact zero_not_mem_keys_zeroDroppingHistory_one
      (guarded_dedup_gate_rejects_zero hge zeroDroppingHistory_zero 1)

theorem guarded_dedup_gate_rejects_zero_satisfiable {a : UInt256} (ha : a ≠ 0) :
    Properties.guarded_dedup_gate_rejects_zero_satisfiable ha := by
  obtain ⟨hge, _, h0, _, hmem⟩ := genesisInsertHistory_guarded ha
  exact ⟨hge, h0, hmem⟩

theorem zero_not_reclaimable_invariant_route {S : ℕ → Finset AbsLeaf} (hevo : Evolution S)
    (h0 : SoundState (S 0)) (hzero : (0 : UInt256) ∈ keys (S 0)) (n : ℕ) :
    Properties.zero_not_reclaimable_invariant_route hevo h0 hzero n :=
  ⟨AttackVectors.ResetAndZero.zero_always_present hevo hzero n,
    fun _ hv => present_not_reclaimable (evolution_sound hevo h0 n).1 hv⟩

theorem zero_not_reclaimable_invariant_route_sharp {a : UInt256} (ha : a ≠ 0) :
    Properties.zero_not_reclaimable_invariant_route_sharp ha := by
  have hapos : (0 : UInt256) < a := Fin.pos_of_ne_zero ha
  refine ⟨⟨(constHistory_guarded _).2, Finset.mem_image.mpr ⟨⟨0, 0⟩, by simp, rfl⟩, ?_,
      Finset.mem_image.mpr ⟨⟨a, 0⟩, by simp, rfl⟩, ⟨⟨0, 0⟩, by simp, hapos, Or.inl rfl⟩⟩,
    ⟨(constHistory_guarded _).2, ?_, ?_⟩,
    ⟨?_, ?_, fun hevo => ?_, zero_not_mem_keys_zeroDroppingHistory_one⟩⟩
  · -- the leaf ⟨0, 0⟩ lies below the key `a` with `nextKey = 0`: not `GapSound`
    intro hs
    exact (hs.1 ⟨0, 0⟩ (by simp) ⟨a, 0⟩ (by simp) hapos).1 rfl
  · -- the singleton `{⟨a, 0⟩}` is sound
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro W hW L hL hlt
      rw [Finset.mem_singleton] at hW hL
      rw [hW, hL] at hlt
      exact absurd hlt (lt_irrefl _)
    · intro A hA B hB _
      rw [Finset.mem_singleton] at hA hB
      rw [hA, hB]
    · intro W hW hnz
      rw [Finset.mem_singleton] at hW
      rw [hW] at hnz
      exact absurd rfl hnz
    · intro W hW
      rw [Finset.mem_singleton] at hW
      rw [hW]
      exact Or.inl rfl
  · -- `0` is not a key of `{⟨a, 0⟩}`
    simp only [keys, Finset.image_singleton, Finset.mem_singleton]
    exact fun h => ha h.symm
  · rw [zeroDroppingHistory_zero]; exact genesis_soundState
  · rw [zeroDroppingHistory_zero]; exact genesis_zero_mem
  · exact zero_not_mem_keys_zeroDroppingHistory_one
      (AttackVectors.ResetAndZero.zero_always_present hevo
        (by rw [zeroDroppingHistory_zero]; exact genesis_zero_mem) 1)

theorem zero_not_reclaimable_invariant_route_satisfiable {a : UInt256} (ha : a ≠ 0) :
    Properties.zero_not_reclaimable_invariant_route_satisfiable ha := by
  obtain ⟨_, hevo, h0, _, hmem⟩ := genesisInsertHistory_guarded ha
  exact ⟨hevo, by rw [h0]; exact genesis_soundState, by rw [h0]; exact genesis_zero_mem, hmem⟩

end AttackVectors.ResetAndZeroStrong
