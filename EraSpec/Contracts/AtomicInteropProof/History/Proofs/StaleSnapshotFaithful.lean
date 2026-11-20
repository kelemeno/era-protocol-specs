import EraSpec.Contracts.AtomicInteropProof.History.Properties.StaleSnapshotFaithful
import EraSpec.Contracts.AtomicInteropProof.Proofs.StaleSnapshotFaithful

/-! # Proofs (History): the padding reclaim at the extraction pin -/

namespace AttackVectors.StaleSnapshotFaithful.History

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

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

theorem PaddingReclaimRedeemsDeliveredLeg : Properties.PaddingReclaimRedeemsDeliveredLeg :=
  padding_reclaim_redeems_delivered_leg

end AttackVectors.StaleSnapshotFaithful.History
