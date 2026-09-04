import EraSpec.Properties.Atomicity
import EraSpec.Proofs.TreeRoot

/-!
# Proofs: partial atomicity

Proofs of `EraSpec.Properties.Atomicity`.  Three ingredients do the work, and each
comes from a layer below: `inclusion_sound` (the finality signal means membership),
`reaches_keys_mono` (the signal is permanent), and `inclusion_complete` (a member
has an honest proof).  What this file adds is the batch/chain bookkeeping and the
timestamp arguments for the two timeout branches.
-/

namespace Contracts.Atomicity

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-! ## System basics -/

/-- Every batch of every chain is a valid tree state. -/
theorem valid_batch {S : System} (hS : Wf S) (c : Chain) (n : ℕ) : Valid (S.tree c n) := by
  induction n with
  | zero => exact reaches_valid (hS.start c) setup_valid
  | succ n ih => exact reaches_valid (hS.batch c n) ih

/-- **THE FINALITY SIGNAL IS PERMANENT.**  Keys only accumulate across batches. -/
theorem keys_mono_batch {S : System} (hS : Wf S) (c : Chain) {n m : ℕ} (hnm : n ≤ m) :
    keys (toAbs (S.tree c n)) ⊆ keys (toAbs (S.tree c m)) := by
  induction m with
  | zero =>
    obtain rfl : n = 0 := Nat.le_zero.mp hnm
    exact fun _ hx => hx
  | succ m ih =>
    rcases Nat.eq_or_lt_of_le hnm with rfl | hlt
    · exact fun _ hx => hx
    · exact fun x hx =>
        reaches_keys_mono (hS.batch c m) (valid_batch hS c m) (ih (by omega) hx)

/-! ## The finality signal -/

/-- **AN ACCEPTED INCLUSION PROOF MEANS THE LEG IS COMMITTED.** -/
theorem finality_means_membership {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {S : System} {c : Chain} {n : ℕ} {v : UInt256}
    {p : ImtProof} (hacc : Accepts h z0 hl S c n v p) :
    v ∈ keys (toAbs (S.tree c n)) :=
  inclusion_sound hA hacc

/-- A committed value has an accepted honest proof at that batch, at an occupied
index.  Both directions of use below: with the DA field it is presentable, without
it it still exists. -/
theorem honest_accepts {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : System}
    (hS : Wf S) {c : Chain} {n : ℕ} {v : UInt256}
    (hmem : v ∈ keys (toAbs (S.tree c n))) :
    ∃ i, i < (S.tree c n).leafCount ∧ Accepts h z0 hl S c n v (honestProof h z0 hl S c n i) := by
  obtain ⟨i, hi, hval⟩ := mem_keys_iff_index.mp hmem
  refine ⟨i, hi, ?_⟩
  have hcomp := inclusion_complete (h := h) (z0 := z0) (hl := hl) (hS.capacity c n) hi
  rw [hval] at hcomp
  exact hcomp

/-- A committed value at an on-time batch is finalized: the evidence exists. -/
theorem member_is_finalized {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : System}
    (hS : Wf S) {D : ℕ} {leg : FlowLeg} {n : ℕ} (hon : S.time leg.chain n ≤ D)
    (hmem : leg.commit ∈ keys (toAbs (S.tree leg.chain n))) :
    LegFinalized h z0 hl S D leg := by
  obtain ⟨i, _, hacc⟩ := honest_accepts hS hmem
  exact ⟨n, honestProof h z0 hl S leg.chain n i, hon, hacc⟩

/-- **MEMBERSHIP PLUS DA GIVES A PRESENTABLE, ACCEPTED PROOF.** -/
theorem member_is_finalizable {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : System}
    (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A) {D : ℕ} {leg : FlowLeg}
    {n : ℕ} (hon : S.time leg.chain n ≤ D)
    (hmem : leg.commit ∈ keys (toAbs (S.tree leg.chain n))) :
    LegFinalizableBy h z0 hl S A D leg := by
  obtain ⟨i, hi, hacc⟩ := honest_accepts hS hmem
  exact ⟨n, honestProof h z0 hl S leg.chain n i, hon, hDA _ _ _ hi, hacc⟩

/-! ## Partial atomicity -/

/-- **PARTIAL ATOMICITY.**  One leg executed ⟹ every leg finalizable. -/
theorem executed_implies_all_finalizable {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {F : Flow} {leg : FlowLeg}
    (hex : ExecutedVia h z0 hl S F leg) :
    FlowFinalizableBy h z0 hl S A F := by
  intro other hother
  obtain ⟨n, p, hon, hacc⟩ := hex.2 other hother
  exact member_is_finalizable hS hDA hon (finality_means_membership hA hacc)

/-- **NONE OR ALL.** -/
theorem none_or_all {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) (F : Flow) :
    FlowFinalizableBy h z0 hl S A F ∨ ∀ leg, ¬ ExecutedVia h z0 hl S F leg := by
  by_cases hex : ∃ leg, ExecutedVia h z0 hl S F leg
  · obtain ⟨leg, hleg⟩ := hex
    exact Or.inl (executed_implies_all_finalizable hA hS hDA hleg)
  · push_neg at hex
    exact Or.inr hex

/-- **FINALIZABILITY DOES NOT DECAY.** -/
theorem executed_implies_finality_persists {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {F : Flow} {leg : FlowLeg}
    (hex : ExecutedVia h z0 hl S F leg) :
    ∀ other ∈ F.legs, ∃ n, S.time other.chain n ≤ F.deadline ∧
      ∀ m, n ≤ m → S.time other.chain m ≤ F.deadline →
        ∃ p, A other.chain m p ∧ Accepts h z0 hl S other.chain m other.commit p := by
  intro other hother
  obtain ⟨n, p, hon, hacc⟩ := hex.2 other hother
  refine ⟨n, hon, ?_⟩
  intro m hnm _
  obtain ⟨i, hi, hacc'⟩ :=
    honest_accepts hS (keys_mono_batch hS other.chain hnm (finality_means_membership hA hacc))
  exact ⟨honestProof h z0 hl S other.chain m i, hDA _ _ _ hi, hacc'⟩

/-- **EXECUTION EXCLUDES EVERY REFUND IN THE FLOW.**

Both timeout branches reduce to "the absence proof is against a batch at or after
the one that proved inclusion", where membership persists and
`verified_absence_excludes_delivered` applies:

* BEGIN branch — the batch settled after the deadline, so by monotone time it is
  strictly after the on-time inclusion batch, and `begin(N) = end(N-1)` still
  contains the commit value.
* END branch — the batch is the last on-time one, so it is at or after every
  on-time batch, the inclusion batch included. -/
theorem executed_excludes_any_refund {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {S : System} (hS : Wf S) {F : Flow} {leg : FlowLeg}
    (hex : ExecutedVia h z0 hl S F leg) (other : FlowLeg) (hother : other ∈ F.legs) :
    ¬ LegRefundable h z0 hl S F.deadline other := by
  obtain ⟨n, p, hon, hacc⟩ := hex.2 other hother
  have hmem := finality_means_membership hA hacc
  rintro ⟨N, q, hbranch⟩
  rcases hbranch with ⟨hlate, habs⟩ | ⟨⟨_, hlast⟩, habs⟩
  · -- a late batch comes strictly after every on-time one
    have hnN : n < N := by
      by_contra hcon
      push_neg at hcon
      exact absurd hlate (not_lt.mpr (le_trans (hS.timeOrdered other.chain hcon) hon))
    obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    exact verified_absence_excludes_delivered hA (valid_batch hS other.chain N') habs
      (keys_mono_batch hS other.chain (by omega) hmem)
  · -- the last on-time batch comes at or after every on-time one
    have hnN : n ≤ N := by
      by_contra hcon
      push_neg at hcon
      exact absurd hon (not_le.mpr (hlast n hcon))
    exact verified_absence_excludes_delivered hA (valid_batch hS other.chain N) habs
      (keys_mono_batch hS other.chain hnN hmem)

/-! ## The concrete configuration -/

@[simp] lemma mixedSystem_tree_zero (a : UInt256) (n : ℕ) :
    (mixedSystem a).tree 0 n = insert setup a 0 := by simp [mixedSystem]

lemma mixedSystem_tree_other {a : UInt256} {c : Chain} (hc : c ≠ 0) (n : ℕ) :
    (mixedSystem a).tree c n = setup := by simp [mixedSystem, hc]

@[simp] lemma mixedSystem_height_zero (a : UInt256) (n : ℕ) :
    (mixedSystem a).height 0 n = 1 := by simp [mixedSystem]

lemma mixedSystem_height_other {a : UInt256} {c : Chain} (hc : c ≠ 0) (n : ℕ) :
    (mixedSystem a).height c n = 0 := by simp [mixedSystem, hc]

@[simp] lemma mixedSystem_time (a : UInt256) (c : Chain) (n : ℕ) :
    (mixedSystem a).time c n = n := rfl

lemma insertSetup_leafCount (a : UInt256) : (insert setup a 0).leafCount = 2 := rfl

lemma insertSetup_valid {a : UInt256} (ha : 0 < a) : Valid (insert setup a 0) :=
  insert_preserves_valid setup_valid (setup_insertGuard ha)

/-- The committed leg really is a key of chain `0`'s tree. -/
lemma mem_insertSetup {a : UInt256} (ha : 0 < a) : a ∈ keys (toAbs (insert setup a 0)) := by
  rw [(insert_sound_step setup_valid (setup_insertGuard ha)).2]
  exact Finset.mem_insert_self _ _

/-- …and the uncommitted one is absent from a tree that never inserted anything. -/
lemma not_mem_setup {b : UInt256} (hb : 0 < b) : b ∉ keys (toAbs setup) := by
  rw [toAbs_setup]
  intro hmem
  obtain ⟨X, hX, hXv⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_singleton] at hX
  subst hX
  exact absurd (hXv : (0 : UInt256) = b) (ne_of_lt hb)

lemma mixedSystem_wf {a : UInt256} (ha : 0 < a) : Wf (mixedSystem a) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    by_cases hc : c = 0
    · subst hc
      rw [mixedSystem_tree_zero]
      exact Reaches.tail Reaches.refl (setup_insertGuard ha)
    · rw [mixedSystem_tree_other hc]
      exact Reaches.refl
  · intro c n
    by_cases hc : c = 0
    · subst hc
      rw [mixedSystem_tree_zero, mixedSystem_tree_zero]
      exact Reaches.refl
    · rw [mixedSystem_tree_other hc, mixedSystem_tree_other hc]
      exact Reaches.refl
  · intro c i j hij
    simpa using hij
  · intro c n
    by_cases hc : c = 0
    · subst hc
      rw [mixedSystem_tree_zero, mixedSystem_height_zero, insertSetup_leafCount]
      norm_num
    · rw [mixedSystem_tree_other hc, mixedSystem_height_other hc]
      show (1 : ℕ) ≤ 2 ^ 0
      norm_num

/-- **THE ALL-LEGS LOOP IS NECESSARY.**  A self-only gate admits one leg executed
with its sibling refundable. -/
theorem selfOnly_gate_admits_mixed_outcome {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (_hA : HashAssumptions h z0 hl) {a b : UInt256} (ha : 0 < a) (hb : 0 < b) :
    Wf (mixedSystem a) ∧ FlowWf (mixedFlow a b)
      ∧ SelfOnlyGate h z0 hl (mixedSystem a) (mixedFlow a b) ⟨0, a⟩
      ∧ LegRefundable h z0 hl (mixedSystem a) (mixedFlow a b).deadline ⟨1, b⟩ := by
  have hS := mixedSystem_wf ha
  refine ⟨hS, ?_, ⟨by simp [mixedFlow], ?_⟩, ?_⟩
  · intro leg hleg
    have hleg' : leg = ⟨0, a⟩ ∨ leg = ⟨1, b⟩ := by
      rcases List.mem_cons.mp hleg with hh | hh
      · exact Or.inl hh
      · exact Or.inr (List.mem_singleton.mp hh)
    rcases hleg' with hh | hh <;> rw [hh]
    · exact ne_of_gt ha
    · exact ne_of_gt hb
  · -- leg `a` is committed on chain 0 at batch 0, which is on time for deadline 0
    refine member_is_finalized hS (leg := ⟨0, a⟩) (n := 0) (by simp [mixedFlow]) ?_
    show a ∈ keys (toAbs ((mixedSystem a).tree 0 0))
    rw [mixedSystem_tree_zero]
    exact mem_insertSetup ha
  · -- leg `b` is absent from chain 1's tree, and batch 1 settled after the deadline
    obtain ⟨ℓ, idx, habs⟩ :=
      non_inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := setup) (height := 0)
        setup_valid (by norm_num [setup]) (ne_of_gt hb) (not_mem_setup hb)
    refine ⟨1, ⟨ℓ, idx, honestSibs h z0 (leafHashes hl setup) idx, 0⟩, Or.inl ⟨?_, ?_⟩⟩
    · show (mixedFlow a b).deadline < (mixedSystem a).time 1 1
      simp [mixedFlow]
    · show AbsenceAccepted h z0 hl (beginTree (mixedSystem a) 1 1)
        (beginHeight (mixedSystem a) 1 1) b _
      show AbsenceAccepted h z0 hl ((mixedSystem a).tree 1 0)
        ((mixedSystem a).height 1 0) b _
      rw [mixedSystem_tree_other (by decide : (1 : Chain) ≠ 0),
          mixedSystem_height_other (by decide : (1 : Chain) ≠ 0)]
      exact habs

/-- **THE REAL GATE REFUSES IN THAT STATE.** -/
theorem full_gate_blocks_mixed_outcome {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {a b : UInt256} (_ha : 0 < a) (hb : 0 < b) :
    ¬ FlowFinalized h z0 hl (mixedSystem a) (mixedFlow a b)
      ∧ ∀ leg, ¬ ExecutedVia h z0 hl (mixedSystem a) (mixedFlow a b) leg := by
  have hno : ¬ FlowFinalized h z0 hl (mixedSystem a) (mixedFlow a b) := by
    intro hall
    obtain ⟨n, p, hon, hacc⟩ := hall ⟨1, b⟩ (by simp [mixedFlow])
    -- on time for deadline `0` forces batch `0`, whose tree on chain 1 is `setup`
    obtain rfl : n = 0 := by
      have : n ≤ 0 := by simpa [mixedFlow] using hon
      omega
    have hmem := finality_means_membership hA hacc
    rw [mixedSystem_tree_other (by decide : (1 : Chain) ≠ 0)] at hmem
    exact not_mem_setup hb hmem
  exact ⟨hno, fun _ hex => hno hex.2⟩

/-- **DATA AVAILABILITY IS NECESSARY.**  Without it the committed leg is stuck:
its finality proof exists but cannot be presented, and it cannot be refunded
either, because it really is in the tree. -/
theorem without_da_committed_leg_is_stuck {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {a : UInt256} (ha : 0 < a) :
    Wf (mixedSystem a)
      ∧ ¬ DataAvailable h z0 hl (mixedSystem a) noAccess
      ∧ LegFinalized h z0 hl (mixedSystem a) 0 ⟨0, a⟩
      ∧ ¬ LegFinalizableBy h z0 hl (mixedSystem a) noAccess 0 ⟨0, a⟩
      ∧ ¬ LegRefundable h z0 hl (mixedSystem a) 0 ⟨0, a⟩ := by
  have hS := mixedSystem_wf ha
  have hmem0 : a ∈ keys (toAbs ((mixedSystem a).tree 0 0)) := by
    rw [mixedSystem_tree_zero]; exact mem_insertSetup ha
  refine ⟨hS, ?_, member_is_finalized hS (leg := ⟨0, a⟩) (n := 0) (by simp) hmem0, ?_, ?_⟩
  · -- index 0 of chain 0's tree is occupied, so DA would have to supply its proof
    intro hDA
    exact hDA 0 0 0 (by rw [mixedSystem_tree_zero, insertSetup_leafCount]; omega)
  · rintro ⟨n, p, _, hpres, _⟩
    exact hpres
  · rintro ⟨N, q, hbranch⟩
    have hmemN : ∀ m : ℕ, a ∈ keys (toAbs ((mixedSystem a).tree 0 m)) := by
      intro m; rw [mixedSystem_tree_zero]; exact mem_insertSetup ha
    rcases hbranch with ⟨hlate, habs⟩ | ⟨_, habs⟩
    · -- batch 0 is on time, so a late batch is some `N' + 1`, whose begin root is `end N'`
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := by
        cases N with
        | zero => exact absurd hlate (by simp)
        | succ N' => exact ⟨N', rfl⟩
      exact verified_absence_excludes_delivered hA (valid_batch hS 0 N') habs (hmemN N')
    · exact verified_absence_excludes_delivered hA (valid_batch hS 0 N) habs (hmemN N)

end Contracts.Atomicity

/-! ## Certificates -/

namespace Proofs.Atomicity

open Contracts.Atomicity

theorem GateRequiresEveryLeg : Properties.Atomicity.GateRequiresEveryLeg :=
  fun _ _ _ _ _ _ hex other hother => hex.2 other hother
theorem FinalitySignalMeansMembership : Properties.Atomicity.FinalitySignalMeansMembership :=
  fun _ _ _ hA _ _ _ _ _ hacc => finality_means_membership hA hacc
theorem FinalitySignalPersists : Properties.Atomicity.FinalitySignalPersists :=
  fun _ hS c _ _ hnm => keys_mono_batch hS c hnm
theorem MemberIsFinalizable : Properties.Atomicity.MemberIsFinalizable :=
  fun _ _ _ _ hS _ hDA _ _ _ hon hmem => member_is_finalizable hS hDA hon hmem
theorem ExecutedImpliesAllFinalizable : Properties.Atomicity.ExecutedImpliesAllFinalizable :=
  fun _ _ _ hA _ hS _ hDA _ _ hex => executed_implies_all_finalizable hA hS hDA hex
theorem NoneOrAll : Properties.Atomicity.NoneOrAll :=
  fun _ _ _ hA _ hS _ hDA F => none_or_all hA hS hDA F
theorem ExecutedImpliesFinalityPersists : Properties.Atomicity.ExecutedImpliesFinalityPersists :=
  fun _ _ _ hA _ hS _ hDA _ _ hex => executed_implies_finality_persists hA hS hDA hex
theorem ExecutedExcludesAnyRefund : Properties.Atomicity.ExecutedExcludesAnyRefund :=
  fun _ _ _ hA _ hS _ _ hex => executed_excludes_any_refund hA hS hex
theorem SelfOnlyGateAdmitsMixedOutcome : Properties.Atomicity.SelfOnlyGateAdmitsMixedOutcome :=
  fun _ _ _ hA _ _ ha hb => selfOnly_gate_admits_mixed_outcome hA ha hb
theorem FullGateBlocksMixedOutcome : Properties.Atomicity.FullGateBlocksMixedOutcome :=
  fun _ _ _ hA _ _ ha hb => full_gate_blocks_mixed_outcome hA ha hb
theorem WithoutDaCommittedLegIsStuck : Properties.Atomicity.WithoutDaCommittedLegIsStuck :=
  fun _ _ _ hA _ ha => without_da_committed_leg_is_stuck hA ha

end Proofs.Atomicity
