import EraSpec.Contracts.AtomicInteropProof.Properties.StaleSnapshotFaithful
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Model
import EraSpec.Contracts.IndexedMerkleTree.Proofs.Model

/-! # Proofs: stale-snapshot reclaim against the deployed absence verifier
(see `../Specs/StaleSnapshotFaithful.lean`) -/

namespace AttackVectors.StaleSnapshotFaithful

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-! ## The headline, with the break located on the submitted proof -/

/-- A run from `setup` projects to an `Evolution` from a sound base. -/
theorem run_evolution {R : ℕ → Tree} (hR : Run R) (h0 : R 0 = setup) :
    Evolution (fun n => toAbs (R n)) ∧ SoundState (toAbs (R 0)) := by
  have hV0 : Valid (R 0) := by rw [h0]; exact setup_valid
  exact ⟨guardedEvolution_isEvolution (run_isGuardedEvolution hR hV0) hV0.absSound, hV0.absSound⟩

theorem stale_witness_not_redeemable_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {R : ℕ → Tree} {ht : ℕ → ℕ} {t : ℕ → UInt256} {D v : UInt256}
    (hR : Run R) (h0 : R 0 = setup) (htmono : Monotone t)
    {j : ℕ} {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hpin : D < t (j + 1))
    (hN : NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k) :
    (∀ i, t i ≤ D → v ∉ keys (toAbs (R i)))
      ∨ TreeRootBreak h z0 hl (R j) (ht j) sibs k idx ℓ := by
  rcases non_inclusion_sound_or_break hN with ⟨W, hW, hlow, hwin⟩ | hb
  · left
    intro i hti hmem
    obtain ⟨hevo, hs0⟩ := run_evolution hR h0
    exact delivered_and_reclaimed_impossible (S := fun n => toAbs (R n)) hevo hs0.1 hs0.2.1
      htmono hti hmem hpin hW hlow hwin
  · exact Or.inr hb

theorem pinning_gate_rejects_stale_witness_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {R : ℕ → Tree} {ht : ℕ → ℕ} {t : ℕ → UInt256} {D v : UInt256}
    (hR : Run R) (h0 : R 0 = setup) (htmono : Monotone t)
    {i : ℕ} (hti : t i ≤ D) (hdel : v ∈ keys (toAbs (R i)))
    {j : ℕ} {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k) :
    ¬ D < t (j + 1) ∨ TreeRootBreak h z0 hl (R j) (ht j) sibs k idx ℓ := by
  by_cases hpin : D < t (j + 1)
  · rcases stale_witness_not_redeemable_or_break hR h0 htmono hpin hN with hno | hb
    · exact absurd hdel (hno i hti)
    · exact Or.inr hb
  · exact Or.inl hpin

theorem stale_witness_not_redeemable_or_collision {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {R : ℕ → Tree} {ht : ℕ → ℕ} {t : ℕ → UInt256} {D v : UInt256}
    (hR : Run R) (h0 : R 0 = setup) (htmono : Monotone t)
    {j : ℕ} {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hpin : D < t (j + 1))
    (hN : NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k)
    (hne : hl ℓ ≠ z0) :
    (∀ i, t i ≤ D → v ∉ keys (toAbs (R i)))
      ∨ HeightBreak h z0 (leafHashes hl (R j)) sibs k (ht j) idx (hl ℓ)
      ∨ (k = ht j ∧ PathCollision h z0 (leafHashes hl (R j)) sibs 0 k idx (hl ℓ))
      ∨ (idx < (R j).leafCount ∧ (R j).leaf idx ≠ ℓ ∧ hl ((R j).leaf idx) = hl ℓ) := by
  rcases stale_witness_not_redeemable_or_break hR h0 htmono hpin hN with hno | hb
  · exact Or.inl hno
  · cases hb with
    | wrongLength hh => exact Or.inr (Or.inl hh)
    | pathCollision hk hc => exact Or.inr (Or.inr (Or.inl ⟨hk, hc⟩))
    | leafCollision hidx hne' heq => exact Or.inr (Or.inr (Or.inr ⟨hidx, hne', heq⟩))
    | paddingHit _ he => exact absurd he hne

/-! ## Satisfiability of the collision form -/

theorem oneInsertRun_run : Run oneInsertRun := by
  intro n
  match n with
  | 0 => exact Or.inr ⟨2, 0, setup_insertGuard (by decide), rfl⟩
  | n + 1 => left; simp [oneInsertRun]

theorem oneInsertRunTime_monotone : Monotone oneInsertRunTime := by
  intro m n hmn
  unfold oneInsertRunTime
  split_ifs with h1 h2 h2
  · exact le_refl _
  · decide
  · exact absurd (le_trans hmn h2) h1
  · exact le_refl _

theorem oneInsertRun_one_count : (oneInsertRun 1).leafCount = 2 := rfl

theorem oneInsertRun_one_leaf0 : (oneInsertRun 1).leaf 0 = ⟨0, 1, 2⟩ := by
  simp [oneInsertRun, Contracts.InteropCommitmentTree.insert, setup]

/-- The honest low-leaf proof for `1` at snapshot 1 is accepted. -/
theorem oneInsertRun_accepted :
    NonInclusionAccepted toyNodeHash toyLeafHash
      (root toyNodeHash 1 toyLeafHash (oneInsertRun 1) (oneInsertRunHeight 1)) 1
      ((oneInsertRun 1).leaf 0) 0
      (honestSibs toyNodeHash 1 (leafHashes toyLeafHash (oneInsertRun 1)) 0)
      (oneInsertRunHeight 1) := by
  have hcap : (oneInsertRun 1).leafCount ≤ 2 ^ (oneInsertRunHeight 1) := by
    rw [oneInsertRun_one_count]; simp [oneInsertRunHeight]
  have hI := inclusion_complete (h := toyNodeHash) (z0 := 1) (hl := toyLeafHash)
    (T := oneInsertRun 1) (height := oneInsertRunHeight 1) hcap (i := 0)
    (by rw [oneInsertRun_one_count]; norm_num)
  refine ⟨by decide, ?_, ?_, hI.path⟩
  · rw [oneInsertRun_one_leaf0]; decide
  · rw [oneInsertRun_one_leaf0]; right; decide

theorem oneInsertRun_keys (n : ℕ) : keys (toAbs (oneInsertRun n)) ⊆ {0, 2} := by
  by_cases h : n = 0
  · subst h; decide
  · have : oneInsertRun n = insert setup 2 0 := by simp [oneInsertRun, h]
    rw [this]; decide

theorem stale_witness_or_collision_satisfiable : Properties.StaleWitnessOrCollisionSatisfiable :=
  ⟨toyNodeHash, 1, toyLeafHash, oneInsertRun, oneInsertRunHeight, oneInsertRunTime, 0, 1, 1,
    (oneInsertRun 1).leaf 0, 0,
    honestSibs toyNodeHash 1 (leafHashes toyLeafHash (oneInsertRun 1)) 0,
    oneInsertRunHeight 1,
    oneInsertRun_run, rfl, oneInsertRunTime_monotone, by decide, oneInsertRun_accepted,
    by rw [oneInsertRun_one_leaf0]; decide,
    honest_proof_no_break toyNodeHash 1 toyLeafHash (oneInsertRun 1) (oneInsertRunHeight 1) 0
      (by rw [oneInsertRun_one_count]; norm_num),
    fun i _ hmem => by have := oneInsertRun_keys i hmem; simp at this,
    by decide,
    ⟨1, 2, by decide, by decide,
      by show (2 : UInt256) ∈ keys (toAbs (insert setup 2 0)); decide⟩⟩

/-! ## Certificates -/

theorem StaleWitnessNotRedeemableOrBreak : Properties.StaleWitnessNotRedeemableOrBreak :=
  fun _ _ _ _ _ _ _ _ hR h0 htmono _ _ _ _ _ hpin hN =>
    stale_witness_not_redeemable_or_break hR h0 htmono hpin hN

theorem PinningGateRejectsStaleWitnessOrBreak : Properties.PinningGateRejectsStaleWitnessOrBreak :=
  fun _ _ _ _ _ _ _ _ hR h0 htmono _ hti hdel _ _ _ _ _ hN =>
    pinning_gate_rejects_stale_witness_or_break hR h0 htmono hti hdel hN

theorem StaleWitnessNotRedeemableOrCollision : Properties.StaleWitnessNotRedeemableOrCollision :=
  fun _ _ _ _ _ _ _ _ hR h0 htmono _ _ _ _ _ hpin hN hne =>
    stale_witness_not_redeemable_or_collision hR h0 htmono hpin hN hne

theorem StaleWitnessOrCollisionSatisfiable : Properties.StaleWitnessOrCollisionSatisfiable :=
  stale_witness_or_collision_satisfiable

end AttackVectors.StaleSnapshotFaithful
