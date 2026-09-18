import EraSpec.Properties.AtomicFlowManager

/-!
# Proofs: the flow manager

Proofs of `EraSpec.Properties.AtomicFlowManager`.  Everything comes from
`step_rank_mono`: each operation guards on the exact predecessor state, so a step
never lowers any leg's rank.
-/

namespace Contracts.AtomicFlowManager

@[simp] lemma rank_unset : rank .Unset = 0 := rfl
@[simp] lemma rank_committed : rank .Committed = 1 := rfl
@[simp] lemma rank_revertable : rank .Revertable = 2 := rfl
@[simp] lemma rank_reverted : rank .Reverted = 3 := rfl

lemma rank_inj : ∀ {s t : LegState}, rank s = rank t → s = t := by
  intro s t h; cases s <;> cases t <;> simp_all [rank]

@[simp] lemma set_same {M : Manager} {f b s} : (M.set f b s).legState f b = s := by
  simp [Manager.set]

lemma set_other {M : Manager} {f b f' b' s} (h : ¬(f' = f ∧ b' = b)) :
    (M.set f b s).legState f' b' = M.legState f' b' := by
  simp [Manager.set, h]

/-! ## The rank is monotone -/

theorem step_rank_mono {M N : Manager} (h : Step M N) (f b : UInt256) :
    rank (M.legState f b) ≤ rank (N.legState f b) := by
  cases h with
  | @append f' b' hg =>
    by_cases he : f = f' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := he; rw [hg, set_same]; simp
    · rw [set_other he]
  | @authorize f' b' hg =>
    by_cases he : f = f' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := he; rw [hg, set_same]; simp
    · rw [set_other he]
  | @claim f' b' hg =>
    by_cases he : f = f' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := he; rw [hg, set_same]; simp
    · rw [set_other he]

theorem reach_rank_mono {M N : Manager} (h : Reach M N) (f b : UInt256) :
    rank (M.legState f b) ≤ rank (N.legState f b) := by
  induction h with
  | refl => exact le_refl _
  | tail hr hs ih => exact le_trans ih (step_rank_mono hs _ _)

/-! ## Consequences -/

theorem reverted_absorbing {M N : Manager} (h : Reach M N) {f b : UInt256}
    (hrev : M.legState f b = .Reverted) : N.legState f b = .Reverted := by
  have hmono := reach_rank_mono h f b
  rw [hrev] at hmono
  cases hN : N.legState f b with
  | Unset => rw [hN] at hmono; simp [rank] at hmono
  | Committed => rw [hN] at hmono; simp [rank] at hmono
  | Revertable => rw [hN] at hmono; simp [rank] at hmono
  | Reverted => rfl

theorem no_double_claim {M N : Manager} {f b : UInt256}
    (_hclaim : ClaimGuard M f b) (h : Reach (M.set f b .Reverted) N) :
    ¬ ClaimGuard N f b := by
  intro hg
  have hg' : N.legState f b = .Revertable := hg
  have hrev := reverted_absorbing h (show (M.set f b .Reverted).legState f b = .Reverted by simp)
  rw [hrev] at hg'
  exact absurd hg' (by decide)

theorem claim_requires_authorization {M : Manager} {f b : UInt256}
    (hg : ClaimGuard M f b) : rank (M.legState f b) = 2 := by
  have hg' : M.legState f b = .Revertable := hg
  rw [hg']
  rfl

theorem unset_not_claimable {M : Manager} {f b : UInt256}
    (h : M.legState f b = .Unset) : ¬ ClaimGuard M f b := by
  intro hg
  have hg' : M.legState f b = .Revertable := hg
  rw [h] at hg'
  exact absurd hg' (by decide)

theorem committed_not_claimable {M : Manager} {f b : UInt256}
    (h : M.legState f b = .Committed) : ¬ ClaimGuard M f b := by
  intro hg
  have hg' : M.legState f b = .Revertable := hg
  rw [h] at hg'
  exact absurd hg' (by decide)

theorem no_double_append {M N : Manager} {f b : UInt256}
    (_happ : AppendGuard M f b) (h : Reach (M.set f b .Committed) N) :
    ¬ AppendGuard N f b := by
  intro hg
  have hg' : N.legState f b = .Unset := hg
  have hmono := reach_rank_mono h f b
  rw [set_same, hg'] at hmono
  simp [rank] at hmono

theorem claim_closes_gate_before_interaction {M : Manager} {f b : UInt256} :
    ¬ ClaimGuard (M.set f b .Reverted) f b := by
  intro hg
  have hg' : (M.set f b .Reverted).legState f b = .Revertable := hg
  rw [set_same] at hg'
  exact absurd hg' (by decide)

theorem rank_le_three (M : Manager) (f b : UInt256) : rank (M.legState f b) ≤ 3 := by
  cases M.legState f b <;> simp [rank]

end Contracts.AtomicFlowManager

/-! ## Certificates -/

namespace Proofs.AtomicFlowManager

open Contracts.AtomicFlowManager

theorem StepRankMono : Properties.AtomicFlowManager.StepRankMono := @step_rank_mono
theorem ReachRankMono : Properties.AtomicFlowManager.ReachRankMono := @reach_rank_mono
theorem RevertedAbsorbing : Properties.AtomicFlowManager.RevertedAbsorbing := @reverted_absorbing
theorem NoDoubleClaim : Properties.AtomicFlowManager.NoDoubleClaim := @no_double_claim
theorem ClaimRequiresAuthorization : Properties.AtomicFlowManager.ClaimRequiresAuthorization :=
  @claim_requires_authorization
theorem UnsetNotClaimable : Properties.AtomicFlowManager.UnsetNotClaimable := @unset_not_claimable
theorem CommittedNotClaimable : Properties.AtomicFlowManager.CommittedNotClaimable :=
  @committed_not_claimable
theorem NoDoubleAppend : Properties.AtomicFlowManager.NoDoubleAppend := @no_double_append
theorem ClaimClosesGateBeforeInteraction :
    Properties.AtomicFlowManager.ClaimClosesGateBeforeInteraction :=
  @claim_closes_gate_before_interaction
theorem RankLeThree : Properties.AtomicFlowManager.RankLeThree := @rank_le_three

end Proofs.AtomicFlowManager
