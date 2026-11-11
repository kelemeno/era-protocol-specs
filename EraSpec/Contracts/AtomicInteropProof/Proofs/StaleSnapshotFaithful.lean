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

/-! ## The countermodel run -/

theorem paddedRun_add_two (a b : UInt256) (n : ℕ) : paddedRun a b (n + 2) = threeLeafTree a b := by
  simp [paddedRun]

theorem paddedRun_run {a b : UInt256} (ha : 0 < a) (hab : a < b) : Run (paddedRun a b) := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  intro n
  match n with
  | 0 => exact Or.inr ⟨a, 0, hg1, rfl⟩
  | 1 => exact Or.inr ⟨b, 1, hg2, rfl⟩
  | n + 2 =>
    left
    rw [show n + 2 + 1 = (n + 1) + 2 from by omega, paddedRun_add_two, paddedRun_add_two]

theorem paddedRunTime_monotone : Monotone paddedRunTime := by
  intro m n hmn
  unfold paddedRunTime
  split_ifs with h1 h2 h2
  · exact le_refl _
  · decide
  · exact absurd (le_trans hmn h2) h1
  · exact le_refl _

theorem paddedRun_capacity (a b : UInt256) (n : ℕ) :
    (paddedRun a b n).leafCount ≤ 2 ^ paddedRunHeight n := by
  match n with
  | 0 => show setup.leafCount ≤ 2 ^ 0; simp [setup]
  | 1 => show (insert setup a 0).leafCount ≤ 2 ^ 1; simp [Contracts.InteropCommitmentTree.insert, setup]
  | n + 2 =>
    rw [paddedRun_add_two, show paddedRunHeight (n + 2) = 2 from by simp [paddedRunHeight]]
    have hc : (threeLeafTree a b).leafCount = 3 := rfl
    rw [hc]
    norm_num

/-- The forged low leaf's abstract view `⟨0, 0⟩` is not a leaf of the snapshot. -/
theorem zero_window_not_mem {a b : UInt256} (ha : 0 < a) (hab : a < b) :
    (⟨0, 0⟩ : AbsLeaf) ∉ toAbs (threeLeafTree a b) := by
  intro hmem
  obtain ⟨i, hi, hval, hnext⟩ := mem_toAbs.mp hmem
  have hc : (threeLeafTree a b).leafCount = 3 := rfl
  rw [hc] at hi
  interval_cases i
  · have h0 : ((threeLeafTree a b).leaf 0).nextValue = a := by
      simp [threeLeafTree, Contracts.InteropCommitmentTree.insert, setup]
    rw [h0] at hnext
    exact ha.ne' hnext
  · rw [threeLeafTree_leaf_one_value] at hval
    exact ha.ne' hval
  · have h2 : ((threeLeafTree a b).leaf 2).value = b := by
      simp [threeLeafTree, Contracts.InteropCommitmentTree.insert, setup]
    rw [h2] at hval
    exact (lt_trans ha hab).ne' hval

theorem padding_reclaim_redeems_delivered_leg : Properties.PaddingReclaimRedeemsDeliveredLeg := by
  intro h hl a b ha hab
  obtain ⟨_, hdel, hN⟩ := padding_collision_refunds_delivered_leg h hl ha hab
  refine ⟨paddedRun_run ha hab, rfl, paddedRunTime_monotone, paddedRun_capacity a b,
    by decide, hdel, by decide, hN, zero_window_not_mem ha hab, ?_,
    padding_countermodel_exactly_padding_hit h hl a b⟩
  intro hall
  exact hall 2 (by decide) hdel

/-! ## Satisfiability of the collision form -/

theorem stale_witness_or_collision_satisfiable : Properties.StaleWitnessOrCollisionSatisfiable := by
  have hcap : setup.leafCount ≤ 2 ^ 0 := by simp [setup]
  have hI := inclusion_complete (h := toyNodeHash) (z0 := 1) (hl := toyLeafHash) (T := setup)
    (height := 0) hcap (i := 0) (by simp [setup])
  have hlate : ¬ ((1 : UInt256) ≤ 0) := by decide
  refine ⟨toyNodeHash, 1, toyLeafHash, fun _ => setup, fun _ => 0, fun _ => 1, 0, 1, 0,
    ⟨0, 0, 0⟩, 0, honestSibs toyNodeHash 1 (leafHashes toyLeafHash setup) 0, 0,
    fun _ => Or.inl rfl, rfl, monotone_const, by decide, ?_, by decide, ?_, ?_⟩
  · exact ⟨by decide, by decide, Or.inl rfl, hI.path⟩
  · exact honest_proof_no_break toyNodeHash 1 toyLeafHash setup 0 0 (by simp [setup])
  · intro i hti
    exact absurd hti hlate

/-! ## Certificates -/

theorem StaleWitnessNotRedeemableOrBreak : Properties.StaleWitnessNotRedeemableOrBreak :=
  fun _ _ _ _ _ _ _ _ hR h0 htmono _ _ _ _ _ hpin hN =>
    stale_witness_not_redeemable_or_break hR h0 htmono hpin hN

theorem PinningGateRejectsStaleWitnessOrBreak : Properties.PinningGateRejectsStaleWitnessOrBreak :=
  fun _ _ _ _ _ _ _ _ hR h0 htmono _ hti hdel _ _ _ _ _ hN =>
    pinning_gate_rejects_stale_witness_or_break hR h0 htmono hti hdel hN

theorem PaddingReclaimRedeemsDeliveredLeg : Properties.PaddingReclaimRedeemsDeliveredLeg :=
  padding_reclaim_redeems_delivered_leg

theorem StaleWitnessNotRedeemableOrCollision : Properties.StaleWitnessNotRedeemableOrCollision :=
  fun _ _ _ _ _ _ _ _ hR h0 htmono _ _ _ _ _ hpin hN hne =>
    stale_witness_not_redeemable_or_collision hR h0 htmono hpin hN hne

theorem StaleWitnessOrCollisionSatisfiable : Properties.StaleWitnessOrCollisionSatisfiable :=
  stale_witness_or_collision_satisfiable

end AttackVectors.StaleSnapshotFaithful
