import EraSpec.Protocol.InteropAtomicity.Properties.Timeout
import EraSpec.Protocol.InteropAtomicity.Proofs.Atomicity
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeaf

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

open Contracts.InteropCommitmentTree Contracts.Atomicity MerkleSpec MerkleSpec.Verifier
open MerkleSpec.LastLeaf IMTAbstract

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

/-! ## The last-batch proof -/

theorem lastBatch_identifies_last {h : Hash} {ze : UInt256}
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    {R : SlRoot} {B : RootBacking h ze R} {c : Chain} {N : ℕ} {sibs : ℕ → UInt256}
    {x : UInt256} (ha : LastBatchAccepted B c N sibs x) :
    N = R.upTo c ∨ HashBreak h ze (B.leaves c) := by
  rcases accepted_last_leaf_or_break h ze hinj (B.leaves c) sibs (B.height c) N x
    (B.capacity c) ha.inRange ha.authenticated ha.zeroRightSiblings with hlast | hbreak
  · refine Or.inl ?_
    have hlen := B.upToLast c
    omega
  · exact Or.inr hbreak

theorem endBranch_of_accepted {h : Hash} {ze : UInt256}
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    {R : SlRoot} {B : RootBacking h ze R} {S : System} {c : Chain} {D N : ℕ}
    {sibs : ℕ → UInt256} {x : UInt256} (ha : EndBranchAccepted B S c D N sibs x) :
    EndBranchVerified S R c D N ∨ HashBreak h ze (B.leaves c) := by
  rcases lastBatch_identifies_last hinj ha.lastBatch with hlast | hbreak
  · exact Or.inl ⟨ha.rootAfterDeadline, ha.onTime, hlast⟩
  · exact Or.inr hbreak

theorem verified_of_accepted {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    {F : Flow} {leg : FlowLeg} (ha : LegRefundableAccepted h z0 hl cv S B F leg) :
    LegRefundableVerified h z0 hl cv S R F leg ∨ HashBreak h ze (B.leaves leg.chain) := by
  obtain ⟨N, p, hbr⟩ := ha
  rcases hbr with ⟨hb, habs⟩ | ⟨sibs, x, he, habs⟩
  · exact Or.inl ⟨N, p, Or.inl ⟨hb, habs⟩⟩
  · rcases endBranch_of_accepted hinj he with hv | hbreak
    · exact Or.inl ⟨N, p, Or.inr ⟨hv, habs⟩⟩
    · exact Or.inr hbreak

theorem accepted_implies_refundable {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : Aggregates S R) {F : Flow} {leg : FlowLeg}
    (ha : LegRefundableAccepted h z0 hl cv S B F leg) :
    LegRefundable h z0 hl cv S F leg ∨ HashBreak h ze (B.leaves leg.chain) := by
  rcases verified_of_accepted hinj ha with hv | hbreak
  · exact Or.inl (verified_implies_refundable hagg hv)
  · exact Or.inr hbreak

/-- **THE COMPLETE CHAIN.** -/
theorem accepted_timeout_means_missed_deadline {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {S : System} (hS : Wf S)
    {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R} (hagg : Aggregates S R)
    {F : Flow} {leg : FlowLeg} (ha : LegRefundableAccepted h z0 hl cv S B F leg) :
    (∀ n, S.time leg.chain n ≤ F.deadline →
        legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
      ∨ HashBreak h ze (B.leaves leg.chain) := by
  rcases verified_of_accepted hA.nodeInj ha with hv | hbreak
  · exact Or.inl (fun n hon => timeout_means_missed_deadline hA hS hagg hv n hon)
  · exact Or.inr hbreak

/-! ## The last-batch chain, pinned -/

theorem legRefundableAccepted_iff_by {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    {F : Flow} {leg : FlowLeg} :
    LegRefundableAccepted h z0 hl cv S B F leg
      ↔ ∃ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
          LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x := by
  constructor
  · rintro ⟨N, p, ⟨hb, habs⟩ | ⟨sibs, x, he, habs⟩⟩
    · exact ⟨N, p, fun _ => 0, 0, Or.inl ⟨hb, habs⟩⟩
    · exact ⟨N, p, sibs, x, Or.inr ⟨he, habs⟩⟩
  · rintro ⟨N, p, sibs, x, ⟨hb, habs⟩ | ⟨he, habs⟩⟩
    · exact ⟨N, p, Or.inl ⟨hb, habs⟩⟩
    · exact ⟨N, p, Or.inr ⟨sibs, x, he, habs⟩⟩

theorem lastBatch_identifies_last_pinned {h : Hash} {ze : UInt256}
    {R : SlRoot} {B : RootBacking h ze R} {c : Chain} {N : ℕ} {sibs : ℕ → UInt256}
    {x : UInt256} (ha : LastBatchAccepted B c N sibs x) :
    N = R.upTo c ∨ PinnedBreak h ze (B.leaves c) N
      ∨ PathCollision h ze (B.leaves c) sibs 0 (B.height c) N x := by
  rcases accepted_last_leaf_or_pinned_break h ze (B.leaves c) sibs (B.height c) N x
    (B.capacity c) ha.inRange ha.authenticated ha.zeroRightSiblings with hlast | hrest
  · refine Or.inl ?_
    have hlen := B.upToLast c
    omega
  · exact Or.inr hrest

theorem lastBatch_identifies_last_on {h : Hash} {ze : UInt256}
    {R : SlRoot} {B : RootBacking h ze R} {c : Chain} {N : ℕ} {sibs : ℕ → UInt256}
    {x : UInt256} (hsep : EntriesNotEmpty ze (B.leaves c))
    (hinj : PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
      ∨ VerifiedPair h sibs (B.height c) N x p))
    (ha : LastBatchAccepted B c N sibs x) : N = R.upTo c := by
  have hlast := accepted_last_leaf_on h ze (B.leaves c) sibs (B.height c) N x
    (B.capacity c) ha.inRange hsep hinj ha.authenticated ha.zeroRightSiblings
  have hlen := B.upToLast c
  omega

theorem endBranch_of_accepted_pinned {h : Hash} {ze : UInt256}
    {R : SlRoot} {B : RootBacking h ze R} {S : System} {c : Chain} {D N : ℕ}
    {sibs : ℕ → UInt256} {x : UInt256} (ha : EndBranchAccepted B S c D N sibs x) :
    EndBranchVerified S R c D N ∨ PinnedBreak h ze (B.leaves c) N
      ∨ PathCollision h ze (B.leaves c) sibs 0 (B.height c) N x := by
  rcases lastBatch_identifies_last_pinned ha.lastBatch with hlast | hrest
  · exact Or.inl ⟨ha.rootAfterDeadline, ha.onTime, hlast⟩
  · exact Or.inr hrest

theorem endBranch_of_accepted_on {h : Hash} {ze : UInt256}
    {R : SlRoot} {B : RootBacking h ze R} {S : System} {c : Chain} {D N : ℕ}
    {sibs : ℕ → UInt256} {x : UInt256} (hsep : EntriesNotEmpty ze (B.leaves c))
    (hinj : PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
      ∨ VerifiedPair h sibs (B.height c) N x p))
    (ha : EndBranchAccepted B S c D N sibs x) : EndBranchVerified S R c D N :=
  ⟨ha.rootAfterDeadline, ha.onTime, lastBatch_identifies_last_on hsep hinj ha.lastBatch⟩

theorem accepted_implies_refundable_pinned {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : Aggregates S R) {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    {sibs : ℕ → UInt256} {x : UInt256}
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    LegRefundable h z0 hl cv S F leg ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
  rcases ha with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact Or.inl (verified_implies_refundable hagg ⟨N, p, Or.inl ⟨hb, habs⟩⟩)
  · rcases endBranch_of_accepted_pinned he with hv | hrest
    · exact Or.inl (verified_implies_refundable hagg ⟨N, p, Or.inr ⟨hv, habs⟩⟩)
    · exact Or.inr ⟨he, hrest⟩

theorem accepted_implies_refundable_on {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : Aggregates S R) {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    {sibs : ℕ → UInt256} {x : UInt256}
    (hsep : EntriesNotEmpty ze (B.leaves leg.chain))
    (hinj : PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
      ∨ VerifiedPair h sibs (B.height leg.chain) N x q))
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    LegRefundable h z0 hl cv S F leg := by
  rcases ha with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact verified_implies_refundable hagg ⟨N, p, Or.inl ⟨hb, habs⟩⟩
  · exact verified_implies_refundable hagg
      ⟨N, p, Or.inr ⟨endBranch_of_accepted_on hsep hinj he, habs⟩⟩

theorem no_pinned_break_bounded {h : Hash} {ze : UInt256} {R : SlRoot}
    (B : RootBacking h ze R) (c : Chain) (N : ℕ) (hsep : EntriesNotEmpty ze (B.leaves c))
    (hinj : PairInjOn h (TreePair h ze (B.leaves c) (B.height c))) :
    ¬ PinnedBreak h ze (B.leaves c) N :=
  no_pinned_break_on h ze (B.leaves c) (B.height c) N (B.capacity c) hsep hinj

/-! ### Anti-vacuity witnesses -/

theorem demoSystem_aggregates : Aggregates demoSystem demoRoot := by
  intro c n hn
  show n ≤ 1
  by_contra hc
  have h2 : demoSystem.time c n = 2 := if_neg hc
  rw [h2] at hn
  exact absurd hn (by decide)

/-- The honest END branch for batch 1 of `demoBacking`. -/
theorem demo_endBranchAccepted :
    EndBranchAccepted demoBacking demoSystem 0 0 1 (honestSibs demoHash 0 [5, 7] 1) 7 :=
  ⟨by decide, by decide, ⟨by decide, by decide, by decide⟩⟩

theorem lastBatch_pinned_conclusion_not_always :
    Properties.LastBatchPinnedConclusionNotAlways := by
  refine ⟨demoHash, 0, demoRoot3, demoBacking3, 0, 1, honestSibs demoHash 0 [5, 7, 9] 1,
    ([5, 7, 9] : List UInt256).getD 1 0, by decide,
    honest_walk_root demoHash 0 [5, 7, 9] 2 1 (by norm_num), ?_⟩
  rintro (h1 | hb | hc)
  · exact absurd h1 (by decide)
  · exact demo_no_pinned_break hb
  · exact honest_walk_no_collision demoHash 0 [5, 7, 9] 2 1 hc

theorem endBranch_accepted_on_satisfiable : Properties.EndBranchAcceptedOnSatisfiable :=
  ⟨demoHash, 0, demoRoot, demoBacking, demoSystem, 0, 0, 1,
    honestSibs demoHash 0 [5, 7] 1, 7, demo_endBranchAccepted, demo_entriesNotEmpty,
    demo_pairInjOn, ⟨1, by decide, by decide⟩, demo_collides⟩

theorem accepted_implies_refundable_on_satisfiable :
    Properties.AcceptedImpliesRefundableOnSatisfiable := by
  obtain ⟨ℓ, idx, habs⟩ :=
    non_inclusion_complete (h := demoHash) (z0 := 0) (hl := fun _ => 0) (T := setup)
      (height := 0) setup_valid (by norm_num [setup]) (v := 1) (by decide)
      (not_mem_setup (by decide))
  refine ⟨demoHash, 0, fun _ => 0, fun _ _ => 1, demoSystem, 0, demoRoot, demoBacking,
    ⟨0, [], 0⟩, ⟨0, 0⟩, 1,
    ⟨ℓ, idx, honestSibs demoHash 0 (leafHashes (fun _ => 0) setup) idx, 0⟩,
    honestSibs demoHash 0 [5, 7] 1, 7, demoSystem_aggregates, demo_entriesNotEmpty,
    demo_pairInjOn, demo_endBranchAccepted, Or.inr ⟨demo_endBranchAccepted, habs⟩⟩

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
    {cv : CommitValue} {F : Flow} {leg : FlowLeg}
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

namespace Contracts.Timeout

open Contracts.Timeout

theorem IsLastOnTimeDerived : Contracts.Timeout.Properties.IsLastOnTimeDerived :=
  fun _ _ hagg _ _ _ he => isLastOnTime_of_verified hagg he
theorem VerifiedImpliesRefundable : Contracts.Timeout.Properties.VerifiedImpliesRefundable :=
  fun _ _ _ _ _ _ hagg _ _ hv => verified_implies_refundable hagg hv
theorem TimeoutMeansMissedDeadline : Contracts.Timeout.Properties.TimeoutMeansMissedDeadline :=
  fun _ _ _ hA _ _ hS _ hagg _ _ hv n hon => timeout_means_missed_deadline hA hS hagg hv n hon
theorem TimeoutExcludesFinality : Contracts.Timeout.Properties.TimeoutExcludesFinality :=
  fun _ _ _ hA _ _ hS _ hagg _ _ hv => timeout_excludes_finality hA hS hagg hv
theorem StaleRootRefundsDeliveredLeg : Contracts.Timeout.Properties.StaleRootRefundsDeliveredLeg :=
  fun _ _ _ _ _ _ hD hv => stale_root_refunds_delivered_leg hD hv
theorem LastBatchProofIdentifiesLastBatch :
    Contracts.Timeout.Properties.LastBatchProofIdentifiesLastBatch :=
  fun _ _ hinj _ _ _ _ _ _ ha => lastBatch_identifies_last hinj ha
theorem EndBranchAcceptedImpliesVerified :
    Contracts.Timeout.Properties.EndBranchAcceptedImpliesVerified :=
  fun _ _ hinj _ _ _ _ _ _ _ _ ha => endBranch_of_accepted hinj ha
theorem AcceptedTimeoutMeansMissedDeadline :
    Contracts.Timeout.Properties.AcceptedTimeoutMeansMissedDeadline :=
  fun _ _ _ hA _ _ hS _ _ _ hagg _ _ ha =>
    accepted_timeout_means_missed_deadline hA hS hagg ha
theorem AcceptedImpliesRefundable : Contracts.Timeout.Properties.AcceptedImpliesRefundable :=
  fun _ _ _ hinj _ _ _ _ _ hagg _ _ ha => accepted_implies_refundable hinj hagg ha
theorem NoBreakUnderIdealizations : Contracts.Timeout.Properties.NoBreakUnderIdealizations :=
  fun _ _ _ hinj hsep => MerkleSpec.LastLeaf.not_hashBreak hinj hsep

theorem LegRefundableAcceptedIffBy : Contracts.Timeout.Properties.LegRefundableAcceptedIffBy :=
  fun _ _ _ _ _ _ _ _ _ _ => legRefundableAccepted_iff_by
theorem LastBatchProofIdentifiesLastBatchPinned :
    Contracts.Timeout.Properties.LastBatchProofIdentifiesLastBatchPinned :=
  fun _ _ _ _ _ _ _ _ ha => lastBatch_identifies_last_pinned ha
theorem LastBatchPinnedConclusionNotAlways :
    Contracts.Timeout.Properties.LastBatchPinnedConclusionNotAlways :=
  lastBatch_pinned_conclusion_not_always
theorem LastBatchProofIdentifiesLastBatchOn :
    Contracts.Timeout.Properties.LastBatchProofIdentifiesLastBatchOn :=
  fun _ _ _ _ _ _ _ _ hsep hinj ha => lastBatch_identifies_last_on hsep hinj ha
theorem EndBranchAcceptedImpliesVerifiedPinned :
    Contracts.Timeout.Properties.EndBranchAcceptedImpliesVerifiedPinned :=
  fun _ _ _ _ _ _ _ _ _ _ ha => endBranch_of_accepted_pinned ha
theorem EndBranchAcceptedImpliesVerifiedOn :
    Contracts.Timeout.Properties.EndBranchAcceptedImpliesVerifiedOn :=
  fun _ _ _ _ _ _ _ _ _ _ hsep hinj ha => endBranch_of_accepted_on hsep hinj ha
theorem EndBranchAcceptedOnSatisfiable :
    Contracts.Timeout.Properties.EndBranchAcceptedOnSatisfiable :=
  endBranch_accepted_on_satisfiable
theorem AcceptedImpliesRefundablePinned :
    Contracts.Timeout.Properties.AcceptedImpliesRefundablePinned :=
  fun _ _ _ _ _ _ _ _ hagg _ _ _ _ _ _ ha => accepted_implies_refundable_pinned hagg ha
theorem AcceptedImpliesRefundableOn : Contracts.Timeout.Properties.AcceptedImpliesRefundableOn :=
  fun _ _ _ _ _ _ _ _ hagg _ _ _ _ _ _ hsep hinj ha =>
    accepted_implies_refundable_on hagg hsep hinj ha
theorem AcceptedImpliesRefundableOnSatisfiable :
    Contracts.Timeout.Properties.AcceptedImpliesRefundableOnSatisfiable :=
  accepted_implies_refundable_on_satisfiable
theorem NoPinnedBreakUnderBoundedInjectivity :
    Contracts.Timeout.Properties.NoPinnedBreakUnderBoundedInjectivity :=
  fun _ _ _ B c N hsep hinj => no_pinned_break_bounded B c N hsep hinj

end Contracts.Timeout

/-! ## The justification without hash premises -/

namespace Contracts.Timeout

open Contracts.InteropCommitmentTree Contracts.Atomicity MerkleSpec MerkleSpec.Verifier
open MerkleSpec.LastLeaf IMTAbstract

theorem legRefundableVerified_iff_by {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {R : SlRoot} {F : Flow} {leg : FlowLeg} :
    LegRefundableVerified h z0 hl cv S R F leg
      ↔ ∃ (N : ℕ) (p : ImtProof), LegRefundableVerifiedBy h z0 hl cv S R F leg N p :=
  Iff.rfl

/-- A verified timeout, witnesses named, is a refundable leg, witnesses named. -/
theorem refundableBy_of_verifiedBy {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {R : SlRoot} (hagg : Aggregates S R)
    {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    (hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p) :
    LegRefundableBy h z0 hl cv S F leg N p := by
  rcases hv with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact Or.inl ⟨hb.late, habs⟩
  · exact Or.inr ⟨isLastOnTime_of_verified hagg he, habs⟩

theorem timeout_means_missed_deadline_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {R : SlRoot} (hagg : Aggregates S R)
    {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    (hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p) :
    (∀ n, S.time leg.chain n ≤ F.deadline →
        legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
      ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p := by
  by_cases hb : AbsenceBreak h z0 hl S F.deadline leg.chain N p
  · exact Or.inr hb
  · refine Or.inl fun n hon hmem => ?_
    rcases member_not_refundable_or_break hS hon hmem N p with hn | hb'
    · exact hn (refundableBy_of_verifiedBy hagg hv)
    · exact hb hb'

theorem timeout_excludes_finality_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {R : SlRoot} (hagg : Aggregates S R)
    {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    (hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p) (n : ℕ) (p' : ImtProof) :
    ¬ LegFinalizedBy h z0 hl cv S F leg n p'
      ∨ InclusionBreak h z0 hl S leg.chain n p'
      ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p := by
  by_cases hfin : LegFinalizedBy h z0 hl cv S F leg n p'
  · obtain ⟨hon, hacc⟩ := hfin
    rcases finality_means_membership_or_break hacc with hmem | hb
    · rcases member_not_refundable_or_break hS hon hmem N p with hn | hb'
      · exact absurd (refundableBy_of_verifiedBy hagg hv) hn
      · exact Or.inr (Or.inr hb')
    · exact Or.inr (Or.inl hb)
  · exact Or.inl hfin

theorem accepted_timeout_means_missed_deadline_or_break {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {S : System} (hS : Wf S) {ze : UInt256} {R : SlRoot}
    {B : RootBacking h ze R} (hagg : Aggregates S R) {F : Flow} {leg : FlowLeg} {N : ℕ}
    {p : ImtProof} {sibs : ℕ → UInt256} {x : UInt256}
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    (∀ n, S.time leg.chain n ≤ F.deadline →
        legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
      ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p
      ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
  have hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p
      ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
    rcases ha with ⟨hb, habs⟩ | ⟨he, habs⟩
    · exact Or.inl (Or.inl ⟨hb, habs⟩)
    · rcases endBranch_of_accepted_pinned he with hver | hrest
      · exact Or.inl (Or.inr ⟨hver, habs⟩)
      · exact Or.inr ⟨he, hrest⟩
  rcases hv with hv | hrest
  · rcases timeout_means_missed_deadline_or_break hS hagg hv with hm | hb
    · exact Or.inl hm
    · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hrest)

/-! ### Anti-vacuity witnesses -/

theorem timeOneRoot_aggregates_mixed (a : UInt256) : Aggregates (mixedSystem a) timeOneRoot :=
  fun _ _ hn => hn

theorem timeOneRoot_aggregates_padded (a b : UInt256) :
    Aggregates (paddedSystem a b) timeOneRoot :=
  fun _ _ hn => hn

/-- The honest absence proof against `setup`: the sentinel `{0,0,0}` is the low leaf of
every nonzero value. -/
theorem setup_absence_accepted (h : Hash) (z0 : UInt256) (hl : LeafHash) {v : UInt256}
    (hv : 0 < v) :
    NonInclusionAccepted h hl (root h z0 hl setup 0) v ⟨0, 0, 0⟩ 0
      (honestSibs h z0 (leafHashes hl setup) 0) 0 where
  nonzero := (ne_of_lt hv).symm
  lowBelow := hv
  window := Or.inl rfl
  path := (inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := setup) (height := 0)
    (by norm_num [setup]) (i := 0) (by norm_num [setup])).path

theorem timeout_or_break_satisfiable (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (S : System) (R : SlRoot) (F : Flow) (leg : FlowLeg) (N : ℕ)
      (p : ImtProof),
      Wf S ∧ Aggregates S R ∧ LegRefundableVerifiedBy h z0 hl cv S R F leg N p
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∧ (∀ n, S.time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n))) := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  refine ⟨fun _ _ => 1, mixedSystem 1, timeOneRoot, mixedFlow 0 1 2, ⟨1, 2⟩, 1,
    ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩,
    mixedSystem_wf h1, timeOneRoot_aggregates_mixed 1, ?_, ?_, ?_⟩
  · refine Or.inl ⟨⟨by norm_num [timeOneRoot, mixedFlow], by norm_num [mixedFlow]⟩, ?_⟩
    show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
      (beginHeight (mixedSystem 1) 1 1) 1 _
    rw [hbegin, hbeginH]
    exact setup_absence_accepted h z0 hl h1
  · rintro (⟨_, hb⟩ | ⟨hon, _⟩)
    · unfold ImtProofBreak at hb
      rw [hbegin, hbeginH] at hb
      exact honest_proof_no_break h z0 hl setup 0 0 (by norm_num [setup]) hb
    · exact absurd hon (by norm_num [mixedFlow])
  · intro n _ hmem
    rw [mixedSystem_tree_other hne] at hmem
    exact not_mem_setup h1 hmem

theorem padding_timeout_locates_absence_break (h : Hash) (hl : LeafHash) (a b : UInt256)
    (ha : 0 < a) (hab : a < b) :
    ∃ (cv : CommitValue) (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      Wf (paddedSystem a b) ∧ Aggregates (paddedSystem a b) timeOneRoot
        ∧ LegRefundableVerifiedBy h (hl ⟨0, 0, 0⟩) hl cv (paddedSystem a b) timeOneRoot F leg N p
        ∧ ¬ (∀ n, (paddedSystem a b).time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs ((paddedSystem a b).tree leg.chain n)))
        ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) F.deadline leg.chain N p
        ∧ (threeLeafTree a b).leafCount ≤ p.index ∧ hl p.leaf = hl ⟨0, 0, 0⟩ := by
  let z0 := hl ⟨0, 0, 0⟩
  let T := threeLeafTree a b
  have hbegin : beginTree (paddedSystem a b) 0 1 = T := paddedSystem_tree_zero a b 0
  have hbeginH : beginHeight (paddedSystem a b) 0 1 = 2 := paddedSystem_height_zero a b 0
  obtain ⟨_, _, hN⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  obtain ⟨_, hpad⟩ := padding_countermodel_locates_padding_hit h hl a b
  have hmemA : a ∈ keys (toAbs T) := (padding_collision_refunds_delivered_leg h hl ha hab).2.1
  have hcount : T.leafCount = 3 := rfl
  refine ⟨fun _ _ => a, subsetFlow 0 0, ⟨0, 0⟩, 1,
    ⟨⟨0, 0, 0⟩, 3, honestSibs h z0 (leafHashes hl T) 3, 2⟩,
    paddedSystem_wf ha hab, timeOneRoot_aggregates_padded a b, ?_, ?_, ?_,
    by show T.leafCount ≤ 3; rw [hcount], rfl⟩
  · refine Or.inl ⟨⟨by norm_num [timeOneRoot, subsetFlow], by norm_num [subsetFlow]⟩, ?_⟩
    show AbsenceAccepted h z0 hl (beginTree (paddedSystem a b) 0 1)
      (beginHeight (paddedSystem a b) 0 1) a _
    rw [hbegin, hbeginH]
    exact hN
  · intro hall
    refine hall 0 (by norm_num [subsetFlow]) ?_
    show a ∈ keys (toAbs ((paddedSystem a b).tree 0 0))
    rw [paddedSystem_tree_zero]
    exact hmemA
  · refine Or.inl ⟨by norm_num [subsetFlow], ?_⟩
    unfold ImtProofBreak
    rw [hbegin, hbeginH]
    exact hpad

end Contracts.Timeout

namespace Contracts.Timeout

theorem LegRefundableVerifiedIffBy : Properties.LegRefundableVerifiedIffBy :=
  fun _ _ _ _ _ _ _ _ => legRefundableVerified_iff_by
theorem TimeoutMeansMissedDeadlineOrBreak : Properties.TimeoutMeansMissedDeadlineOrBreak :=
  fun _ _ _ _ _ hS _ hagg _ _ _ _ hv => timeout_means_missed_deadline_or_break hS hagg hv
theorem TimeoutExcludesFinalityOrBreak : Properties.TimeoutExcludesFinalityOrBreak :=
  fun _ _ _ _ _ hS _ hagg _ _ _ _ hv n p' => timeout_excludes_finality_or_break hS hagg hv n p'
theorem AcceptedTimeoutMeansMissedDeadlineOrBreak :
    Properties.AcceptedTimeoutMeansMissedDeadlineOrBreak :=
  fun _ _ _ _ _ hS _ _ _ hagg _ _ _ _ _ _ ha =>
    accepted_timeout_means_missed_deadline_or_break hS hagg ha
theorem TimeoutOrBreakSatisfiable : Properties.TimeoutOrBreakSatisfiable :=
  timeout_or_break_satisfiable
theorem PaddingTimeoutLocatesAbsenceBreak : Properties.PaddingTimeoutLocatesAbsenceBreak :=
  padding_timeout_locates_absence_break

end Contracts.Timeout

/-! ## More anti-vacuity witnesses for the repaired timeout results -/

namespace Contracts.Timeout

open Contracts.InteropCommitmentTree Contracts.Atomicity MerkleSpec MerkleSpec.Verifier
open MerkleSpec.LastLeaf IMTAbstract

theorem timeout_excludes_finality_or_break_witness :
    Properties.TimeoutExcludesFinalityOrBreakWitness := by
  intro h z0 hl
  -- the instance of `timeout_or_break_satisfiable`: `mixedSystem 1`, leg `⟨1, 2⟩`
  have hne : (1 : Chain) ≠ 0 := by decide
  have hcount : ((mixedSystem 1).tree 1 0).leafCount = 1 := by
    rw [mixedSystem_tree_other hne]; rfl
  have hnb := honestProof_no_break h z0 hl (mixedSystem 1) 1 0 0 (by rw [hcount]; norm_num)
  have h1 : (0 : UInt256) < 1 := by decide
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  have hv' : LegRefundableVerifiedBy h z0 hl (fun _ _ => 1) (mixedSystem 1) timeOneRoot
      (mixedFlow 0 1 2) ⟨1, 2⟩ 1 ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩ := by
    refine Or.inl ⟨⟨by norm_num [timeOneRoot, mixedFlow], by norm_num [mixedFlow]⟩, ?_⟩
    show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
      (beginHeight (mixedSystem 1) 1 1) 1 _
    rw [hbegin, hbeginH]
    exact setup_absence_accepted h z0 hl h1
  have hnab' : ¬ AbsenceBreak h z0 hl (mixedSystem 1) (mixedFlow 0 1 2).deadline 1 1
      ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩ := by
    rintro (⟨_, hb⟩ | ⟨hon, _⟩)
    · unfold ImtProofBreak at hb
      rw [hbegin, hbeginH] at hb
      exact honest_proof_no_break h z0 hl setup 0 0 (by norm_num [setup]) hb
    · exact absurd hon (by norm_num [mixedFlow])
  have hS' := mixedSystem_wf h1
  have hagg' := timeOneRoot_aggregates_mixed 1
  refine ⟨fun _ _ => 1, mixedSystem 1, timeOneRoot, mixedFlow 0 1 2, ⟨1, 2⟩, 1, _, 0,
    honestProof h z0 hl (mixedSystem 1) 1 0 0, hS', hagg', hv', hnb, hnab', ?_⟩
  rcases timeout_excludes_finality_or_break hS' hagg' hv' 0
      (honestProof h z0 hl (mixedSystem 1) 1 0 0) with hn | hb | hb
  · exact hn
  · exact absurd hb hnb
  · exact absurd hb hnab'

theorem demoSystem_wf : Wf demoSystem := by
  refine ⟨fun _ => Reaches.refl, fun _ _ => Reaches.refl, ?_, fun _ _ => by norm_num [demoSystem, setup]⟩
  intro c i j hij
  simp only [demoSystem]
  split_ifs <;> omega

theorem accepted_timeout_or_break_witness : Properties.AcceptedTimeoutOrBreakWitness := by
  have h1 : (0 : UInt256) < 1 := by decide
  have habs : AbsenceAccepted demoHash 0 (fun _ => 0) (demoSystem.tree 0 1) (demoSystem.height 0 1)
      1 ⟨⟨0, 0, 0⟩, 0, honestSibs demoHash 0 (leafHashes (fun _ => 0) setup) 0, 0⟩ :=
    setup_absence_accepted demoHash 0 (fun _ => 0) h1
  have hnab : ¬ AbsenceBreak demoHash 0 (fun _ => 0) demoSystem 0 0 1
      ⟨⟨0, 0, 0⟩, 0, honestSibs demoHash 0 (leafHashes (fun _ => 0) setup) 0, 0⟩ := by
    rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
    · exact absurd hlate (by decide)
    · exact honest_proof_no_break demoHash 0 (fun _ => 0) setup 0 0 (by norm_num [setup]) hb
  refine ⟨demoHash, 0, fun _ => 0, fun _ _ => 1, demoSystem, 0, demoRoot, demoBacking,
    ⟨0, [⟨0, 0⟩], 0⟩, ⟨0, 0⟩, 1, _, honestSibs demoHash 0 [5, 7] 1, 7, demoSystem_wf,
    demoSystem_aggregates, Or.inr ⟨demo_endBranchAccepted, habs⟩, hnab,
    no_pinned_break_bounded demoBacking 0 1 demo_entriesNotEmpty
      (fun p q hp hq => demo_pairInjOn p q (Or.inl hp) (Or.inl hq)),
    honest_walk_no_collision demoHash 0 [5, 7] 2 1, ?_⟩
  intro n _ hmem
  exact not_mem_setup h1 hmem

theorem TimeoutExcludesFinalityOrBreakWitness : Properties.TimeoutExcludesFinalityOrBreakWitness :=
  timeout_excludes_finality_or_break_witness
theorem AcceptedTimeoutOrBreakWitness : Properties.AcceptedTimeoutOrBreakWitness :=
  accepted_timeout_or_break_witness

end Contracts.Timeout
