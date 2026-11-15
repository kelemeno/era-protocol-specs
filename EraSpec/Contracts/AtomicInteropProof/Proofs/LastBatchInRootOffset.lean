import EraSpec.Contracts.AtomicInteropProof.Properties.LastBatchInRootOffset
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastBatchInRoot

/-! # Proofs: the end-branch composition with positions and batch numbers apart
(see `../Specs/LastBatchInRootOffset.lean`) -/

namespace AttackVectors.LastBatchInRootOffset

open AttackVectors.TimeoutSoundness AttackVectors.LastBatchInRoot

theorem end_branch_from_onchain_check_offset {H : BatchHistory} {f n p hDepth B D T : ℕ}
    {v : UInt256} (hao : AppendOnly H) (hroot : D < T) (hB : B = batchAt f p)
    (hin : p < n) (hcap : n ≤ 2 ^ hDepth) (hemp : RightEmpty p n hDepth)
    (hout : ∀ m, f + n ≤ m → T ≤ H.time m) (habsent : v ∉ H.endSet B) :
    ∀ B', H.time B' ≤ D → v ∉ H.endSet B' := by
  have hlast : n = p + 1 := last_of_rightEmpty hin hcap hemp
  have hlate : ∀ m, B < m → T ≤ H.time m := by
    intro m hm
    apply hout m
    rw [hB, batchAt] at hm
    omega
  exact end_absence_implies_never_finalized' hao hroot hlate habsent

theorem batch_number_bound_or_collision (bl : UInt256 → ℕ → ℕ → UInt256) (R Rp : UInt256)
    (B tB f p tp : ℕ) (he : bl R B tB = bl Rp (batchAt f p) tp) :
    B = batchAt f p ∨ ((R, B, tB) ≠ (Rp, batchAt f p, tp) ∧ bl R B tB = bl Rp (batchAt f p) tp) := by
  by_cases hB : B = batchAt f p
  · exact Or.inl hB
  · refine Or.inr ⟨fun htrip => hB ?_, he⟩
    exact (Prod.mk.inj (Prod.mk.inj htrip).2).1

theorem position_as_batch_misreads : Properties.PositionAsBatchMisreads := by
  refine ⟨?_, by norm_num, by norm_num, by norm_num, rightEmpty_of_last, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    by_cases h : 1 ≤ n
    · simp [offsetHistory, h, show 1 ≤ n + 1 from by omega]
    · simp [offsetHistory, h]
  · simp [offsetHistory]
  · intro hout
    have h1 : 1 ≤ offsetHistory.time 1 := hout 1 (by norm_num)
    simp [offsetHistory] at h1
  · intro hall
    exact hall 1 (by simp [offsetHistory]) (by simp [offsetHistory])
  · intro m hm
    have hm' : ¬ m ≤ 1 := by omega
    simp [offsetHistory, hm']
  · simp [offsetHistory, batchAt]

theorem richOffsetHistory_appendOnly : AppendOnly richOffsetHistory := by
  intro n
  by_cases h0 : n = 0
  · subst h0; simp [richOffsetHistory]
  · by_cases h3 : n ≤ 3
    · by_cases h3' : n + 1 ≤ 3
      · simp [richOffsetHistory, h0, h3, h3']
      · simp [richOffsetHistory, h0, h3, h3']
    · have h3' : ¬ n + 1 ≤ 3 := by omega
      simp [richOffsetHistory, h0, h3, h3']

theorem end_branch_offset_satisfiable : Properties.EndBranchOffsetSatisfiable := by
  refine ⟨richOffsetHistory_appendOnly, by norm_num, rfl, by norm_num, by norm_num,
    rightEmpty_of_last, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    have : ¬ m ≤ 3 := by omega
    simp [richOffsetHistory, this]
  · simp [richOffsetHistory]
  · intro hout
    have h3 : 1 ≤ richOffsetHistory.time 3 := hout 3 (by norm_num)
    simp [richOffsetHistory] at h3
  · intro h
    have := h 0 (by norm_num) (by norm_num) 3 (by norm_num) (by norm_num)
    omega
  · simp [richOffsetHistory]
  · simp [richOffsetHistory]

/-! ## Certificates -/

theorem EndBranchFromOnchainCheckOffset : Properties.EndBranchFromOnchainCheckOffset :=
  fun _ _ _ _ _ _ _ _ _ hao hroot hB hin hcap hemp hout habsent =>
    end_branch_from_onchain_check_offset hao hroot hB hin hcap hemp hout habsent

theorem BatchNumberBoundOrCollision : Properties.BatchNumberBoundOrCollision :=
  batch_number_bound_or_collision

theorem PositionAsBatchMisreads : Properties.PositionAsBatchMisreads :=
  position_as_batch_misreads

theorem EndBranchOffsetSatisfiable : Properties.EndBranchOffsetSatisfiable :=
  end_branch_offset_satisfiable

end AttackVectors.LastBatchInRootOffset
