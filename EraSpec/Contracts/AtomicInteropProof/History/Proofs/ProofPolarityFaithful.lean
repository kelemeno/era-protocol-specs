import EraSpec.Contracts.AtomicInteropProof.History.Properties.ProofPolarityFaithful
import EraSpec.Contracts.AtomicInteropProof.Proofs.ProofPolarityFaithful

/-! # Proofs (History): the pinned `append` and the misdeclared double mint (H1) -/

namespace AttackVectors.ProofPolarityFaithful.History

variable {Chain Value : Type}

theorem pinnedReach_honest {srcOf : Value → Chain} {tree : Chain → Set Value}
    (h : PinnedReach srcOf tree) : HonestInsertion srcOf tree := by
  induction h with
  | genesis => intro c v hv; simp at hv
  | @append tree c v _ hsrc ih =>
    intro c' w hw
    rcases hw with hw | ⟨rfl, rfl⟩
    · exact ih c' w hw
    · exact hsrc

theorem cm_pinnedReach : PinnedReach cmSrc cmTree :=
  PinnedReach.append true () PinnedReach.genesis rfl

theorem pinned_misdeclared_double_mint : Properties.PinnedMisdeclaredDoubleMint := by
  refine ⟨cm_pinnedReach, pinnedReach_honest cm_pinnedReach, ?_, cm_mem_true, ?_, ?_, ?_, ?_⟩
  · intro hDI
    have h := hDI true () cm_mem_true
    simp [cmDecl] at h
  · simp [cmDecl, cmSrc]
  · intro v _
    cases v
    exact cm_mem_true
  · exact ⟨(), List.mem_singleton_self _, false, rfl, cm_not_mem_false⟩
  · intro pc h
    obtain ⟨hpc, hmem⟩ := h () (List.mem_singleton_self _)
    have hpc' : pc () = false := hpc
    rw [hpc'] at hmem
    exact cm_not_mem_false hmem

theorem refund_not_blocked_when_pinned_to_declared :
    Properties.RefundNotBlockedWhenPinnedToDeclared :=
  ⟨cm_pinnedReach, cm_mem_true, rfl, cm_not_mem_false⟩

theorem PinnedReachHonest : Properties.PinnedReachHonest :=
  fun _ _ _ _ h => pinnedReach_honest h

theorem PinnedMisdeclaredDoubleMint : Properties.PinnedMisdeclaredDoubleMint :=
  pinned_misdeclared_double_mint

theorem RefundNotBlockedWhenPinnedToDeclared : Properties.RefundNotBlockedWhenPinnedToDeclared :=
  refund_not_blocked_when_pinned_to_declared

end AttackVectors.ProofPolarityFaithful.History
