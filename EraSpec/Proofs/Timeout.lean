import EraSpec.Properties.Timeout
import EraSpec.Proofs.Atomicity

/-!
# Proofs: the timeout decision is justified

`isLastOnTime_of_verified` is the whole idea in four lines: a batch that settled by
the deadline settled before the root was created, so the aggregation guarantee puts
it inside the root, so it is at or before the root's last batch — which is the batch
the proof pins.  Everything else follows the shape of
`Atomicity.executed_excludes_any_refund`, with the two branches handled by the same
two timestamp arguments.
-/

namespace Contracts.Timeout

open Contracts.InteropCommitmentTree Contracts.Atomicity MerkleSpec MerkleSpec.Verifier IMTAbstract

/-! ## The derivation -/

/-- **"LAST BATCH IN THIS ROOT" MEANS "LAST BATCH IN TIME".** -/
theorem isLastOnTime_of_verified {S : System} {R : SlRoot} (hagg : Aggregates S R)
    {c : Chain} {D N : ℕ} (he : EndBranchVerified S R c D N) : IsLastOnTime S c D N := by
  refine ⟨he.onTime, ?_⟩
  intro m hm
  by_contra hcon
  push_neg at hcon
  have hin : m ≤ R.upTo c := hagg c m (le_trans hcon (le_of_lt he.rootAfterDeadline))
  rw [← he.lastInRoot] at hin
  omega

/-- **A VERIFIED TIMEOUT IS A REFUNDABLE LEG.** -/
theorem verified_implies_refundable {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {R : SlRoot} (hagg : Aggregates S R)
    {F : Flow} {leg : FlowLeg} (hv : LegRefundableVerified h z0 hl cv S R F leg) :
    LegRefundable h z0 hl cv S F leg := by
  obtain ⟨N, p, hbr⟩ := hv
  refine ⟨N, p, ?_⟩
  rcases hbr with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact Or.inl ⟨hb.late, habs⟩
  · exact Or.inr ⟨isLastOnTime_of_verified hagg he, habs⟩

/-! ## The justification -/

/-- **A REFUNDED LEG REALLY MISSED ITS DEADLINE.** -/
theorem timeout_means_missed_deadline {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {S : System} (hS : Wf S)
    {R : SlRoot} (hagg : Aggregates S R) {F : Flow} {leg : FlowLeg}
    (hv : LegRefundableVerified h z0 hl cv S R F leg)
    (n : ℕ) (hon : S.time leg.chain n ≤ F.deadline) :
    legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)) := by
  intro hmem
  obtain ⟨N, p, hbr⟩ := hv
  rcases hbr with ⟨hb, habs⟩ | ⟨he, habs⟩
  · -- a late batch comes strictly after every on-time one
    have hlt : n < N := by
      by_contra hcon
      push_neg at hcon
      exact absurd hb.late (not_lt.mpr (le_trans (hS.timeOrdered leg.chain hcon) hon))
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    exact verified_absence_excludes_delivered hA (valid_batch hS leg.chain N') habs
      (keys_mono_batch hS leg.chain (by omega) hmem)
  · -- the derived last-on-time batch is at or after every on-time one
    have hlast := isLastOnTime_of_verified hagg he
    have hle : n ≤ N := by
      by_contra hcon
      push_neg at hcon
      exact absurd hon (not_le.mpr (hlast.2 n hcon))
    exact verified_absence_excludes_delivered hA (valid_batch hS leg.chain N) habs
      (keys_mono_batch hS leg.chain hle hmem)

/-- The same, in the form the finality gate consumes. -/
theorem timeout_excludes_finality {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {S : System} (hS : Wf S)
    {R : SlRoot} (hagg : Aggregates S R) {F : Flow} {leg : FlowLeg}
    (hv : LegRefundableVerified h z0 hl cv S R F leg) :
    ¬ LegFinalized h z0 hl cv S F leg := by
  rintro ⟨n, p, hon, hacc⟩
  exact timeout_means_missed_deadline hA hS hagg hv n hon (finality_means_membership hA hacc)

/-! ## The stale-root countermodel -/

@[simp] lemma staleSystem_tree_zero (a : UInt256) (c : Chain) :
    (staleSystem a).tree c 0 = setup := by simp [staleSystem]

lemma staleSystem_tree_succ (a : UInt256) (c : Chain) (n : ℕ) :
    (staleSystem a).tree c (n + 1) = insert setup a 0 := by simp [staleSystem]

@[simp] lemma staleSystem_time (a : UInt256) (c : Chain) (n : ℕ) :
    (staleSystem a).time c n = 0 := rfl

@[simp] lemma staleSystem_height_zero (a : UInt256) (c : Chain) :
    (staleSystem a).height c 0 = 0 := by simp [staleSystem]

lemma staleSystem_height_succ (a : UInt256) (c : Chain) (n : ℕ) :
    (staleSystem a).height c (n + 1) = 1 := by simp [staleSystem]

lemma staleSystem_wf {a : UInt256} (ha : 0 < a) : Wf (staleSystem a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    rw [staleSystem_tree_zero]
    exact Reaches.refl
  · intro c n
    cases n with
    | zero =>
      rw [staleSystem_tree_zero, staleSystem_tree_succ]
      exact Reaches.tail Reaches.refl (setup_insertGuard ha)
    | succ m =>
      rw [staleSystem_tree_succ, staleSystem_tree_succ]
      exact Reaches.refl
  · intro _ _ _ _
    exact le_refl 0
  · intro c n
    cases n with
    | zero =>
      rw [staleSystem_tree_zero, staleSystem_height_zero]
      norm_num [setup]
    | succ m =>
      rw [staleSystem_tree_succ, staleSystem_height_succ, insertSetup_leafCount]
      norm_num

/-- **A STALE ROOT REFUNDS A DELIVERED LEG.** -/
theorem stale_root_refunds_delivered_leg {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (_hA : HashAssumptions h z0 hl) {cv : CommitValue} {F : Flow} {leg : FlowLeg}
    (hD : F.deadline = 0) (hv : 0 < legValue cv F leg) :
    Wf (staleSystem (legValue cv F leg))
      ∧ ¬ Aggregates (staleSystem (legValue cv F leg)) staleRoot
      ∧ (staleSystem (legValue cv F leg)).time leg.chain 1 ≤ F.deadline
      ∧ legValue cv F leg
          ∈ keys (toAbs ((staleSystem (legValue cv F leg)).tree leg.chain 1))
      ∧ LegRefundableVerified h z0 hl cv (staleSystem (legValue cv F leg)) staleRoot F leg := by
  refine ⟨staleSystem_wf hv, ?_, ?_, ?_, ?_⟩
  · -- batch 1 had settled when the root was created, yet the root stops at batch 0
    intro hagg
    have := hagg leg.chain 1 (by norm_num [staleRoot])
    simp only [staleRoot] at this
    omega
  · simp [hD]
  · rw [staleSystem_tree_succ]
    exact mem_insertSetup hv
  · -- the END branch verifies at batch 0, where the tree is still empty
    obtain ⟨ℓ, idx, habs⟩ :=
      non_inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := setup) (height := 0)
        setup_valid (by norm_num [setup]) (ne_of_gt hv) (not_mem_setup hv)
    refine ⟨0, ⟨ℓ, idx, honestSibs h z0 (leafHashes hl setup) idx, 0⟩, Or.inr ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
    · rw [hD]; norm_num [staleRoot]
    · simp [hD]
    · rfl
    · rw [staleSystem_tree_zero, staleSystem_height_zero]
      exact habs

end Contracts.Timeout

/-! ## Certificates -/

namespace Proofs.Timeout

open Contracts.Timeout

theorem IsLastOnTimeDerived : Properties.Timeout.IsLastOnTimeDerived :=
  fun _ _ hagg _ _ _ he => isLastOnTime_of_verified hagg he
theorem VerifiedImpliesRefundable : Properties.Timeout.VerifiedImpliesRefundable :=
  fun _ _ _ _ _ _ hagg _ _ hv => verified_implies_refundable hagg hv
theorem TimeoutMeansMissedDeadline : Properties.Timeout.TimeoutMeansMissedDeadline :=
  fun _ _ _ hA _ _ hS _ hagg _ _ hv n hon => timeout_means_missed_deadline hA hS hagg hv n hon
theorem TimeoutExcludesFinality : Properties.Timeout.TimeoutExcludesFinality :=
  fun _ _ _ hA _ _ hS _ hagg _ _ hv => timeout_excludes_finality hA hS hagg hv
theorem StaleRootRefundsDeliveredLeg : Properties.Timeout.StaleRootRefundsDeliveredLeg :=
  fun _ _ _ hA _ _ _ hD hv => stale_root_refunds_delivered_leg hA hD hv

end Proofs.Timeout
