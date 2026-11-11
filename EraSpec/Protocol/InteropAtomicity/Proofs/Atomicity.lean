import EraSpec.Protocol.InteropAtomicity.Properties.Atomicity
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot

/-!
# Proofs: partial atomicity

Proofs of `EraSpec.Protocol.InteropAtomicity.Properties.Atomicity`.  Three ingredients do the work, and each
comes from a layer below: `inclusion_sound` (the finality signal means membership),
`reaches_keys_mono` (the signal is permanent), and `inclusion_complete` (a member
has an honest proof).  What this file adds is the batch/chain bookkeeping, the
timestamp arguments for the two timeout branches, and the flow-id reasoning.
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
theorem member_is_finalized {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} (hS : Wf S) {F : Flow} {leg : FlowLeg} {n : ℕ}
    (hon : S.time leg.chain n ≤ F.deadline)
    (hmem : legValue cv F leg ∈ keys (toAbs (S.tree leg.chain n))) :
    LegFinalized h z0 hl cv S F leg := by
  obtain ⟨i, _, hacc⟩ := honest_accepts hS hmem
  exact ⟨n, honestProof h z0 hl S leg.chain n i, hon, hacc⟩

/-- **MEMBERSHIP PLUS DA GIVES A PRESENTABLE, ACCEPTED PROOF.** -/
theorem member_is_finalizable {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A)
    {F : Flow} {leg : FlowLeg} {n : ℕ} (hon : S.time leg.chain n ≤ F.deadline)
    (hmem : legValue cv F leg ∈ keys (toAbs (S.tree leg.chain n))) :
    LegFinalizableBy h z0 hl cv S A F leg := by
  obtain ⟨i, hi, hacc⟩ := honest_accepts hS hmem
  exact ⟨n, honestProof h z0 hl S leg.chain n i, hon, hDA _ _ _ hi, hacc⟩

/-! ## Partial atomicity -/

/-- **PARTIAL ATOMICITY.**  One leg executed ⟹ every leg finalizable. -/
theorem executed_implies_all_finalizable {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash} {S : System}
    (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A) {F : Flow} {leg : FlowLeg}
    (hex : ExecutedVia h z0 hl cv fh S F leg) :
    FlowFinalizableBy h z0 hl cv S A F := by
  intro other hother
  obtain ⟨n, p, hon, hacc⟩ := hex.2.2 other hother
  exact member_is_finalizable hS hDA hon (finality_means_membership hA hacc)

/-- **NONE OR ALL.** -/
theorem none_or_all {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash} {S : System}
    (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A) (F : Flow) :
    FlowFinalizableBy h z0 hl cv S A F ∨ ∀ leg, ¬ ExecutedVia h z0 hl cv fh S F leg := by
  by_cases hex : ∃ leg, ExecutedVia h z0 hl cv fh S F leg
  · obtain ⟨leg, hleg⟩ := hex
    exact Or.inl (executed_implies_all_finalizable hA hS hDA hleg)
  · push_neg at hex
    exact Or.inr hex

/-- **FINALIZABILITY DOES NOT DECAY.** -/
theorem executed_implies_finality_persists {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash} {S : System}
    (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A) {F : Flow} {leg : FlowLeg}
    (hex : ExecutedVia h z0 hl cv fh S F leg) :
    ∀ other ∈ F.legs, ∃ n, S.time other.chain n ≤ F.deadline ∧
      ∀ m, n ≤ m → S.time other.chain m ≤ F.deadline →
        ∃ p, A other.chain m p ∧ Accepts h z0 hl S other.chain m (legValue cv F other) p := by
  intro other hother
  obtain ⟨n, p, hon, hacc⟩ := hex.2.2 other hother
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
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash} {S : System}
    (hS : Wf S) {F : Flow} {leg : FlowLeg} (hex : ExecutedVia h z0 hl cv fh S F leg)
    (other : FlowLeg) (hother : other ∈ F.legs) :
    ¬ LegRefundable h z0 hl cv S F other := by
  obtain ⟨n, p, hon, hacc⟩ := hex.2.2 other hother
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

/-! ## The flow-id check -/

/-- **`_checkFlowId` PINS THE LEG LIST.**  Two checked flows claiming the same id
are the same flow, so "the checked flow with id `X`" is well defined. -/
theorem flowId_check_pins_legList {fh : FlowHash} (hinj : FlowHashInj fh) {F F' : Flow}
    (hF : FlowIdChecked fh F) (hF' : FlowIdChecked fh F') (hid : F.flowId = F'.flowId) :
    F = F' := by
  obtain ⟨hlegs, hdl⟩ := hinj _ _ _ _ (hF.trans (hid.trans hF'.symm))
  cases F; cases F'
  simp_all

/-- **PARTIAL ATOMICITY OVER THE REAL FLOW.** -/
theorem executed_implies_real_flow_finalizable {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash} (hinj : FlowHashInj fh)
    {S : System} (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A)
    {F F' : Flow} {leg : FlowLeg} (hex : ExecutedVia h z0 hl cv fh S F leg)
    (hF' : FlowIdChecked fh F') (hid : F.flowId = F'.flowId) :
    FlowFinalizableBy h z0 hl cv S A F' := by
  obtain rfl : F = F' := flowId_check_pins_legList hinj hex.2.1 hF' hid
  exact executed_implies_all_finalizable hA hS hDA hex

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

/-- Leg `hA` is finalized under any flow claiming id `id` — including a truncated
one, since the commit value is computed from the claimed id. -/
private lemma legA_finalized {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {id hA : UInt256} (ha : 0 < cv id hA) (F : Flow) (hid : F.flowId = id) :
    LegFinalized h z0 hl cv (mixedSystem (cv id hA)) F ⟨0, hA⟩ := by
  refine member_is_finalized (mixedSystem_wf ha) (leg := ⟨0, hA⟩) (n := 0) (by simp) ?_
  show legValue cv F ⟨0, hA⟩ ∈ keys (toAbs ((mixedSystem (cv id hA)).tree 0 0))
  rw [mixedSystem_tree_zero]
  show cv F.flowId hA ∈ _
  rw [hid]
  exact mem_insertSetup ha

/-- Leg `hB` is refundable: absent from chain `1`'s tree, and batch 1 settled after
the deadline. -/
private lemma legB_refundable {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {id hA hB : UInt256} (hb : 0 < cv id hB) :
    LegRefundable h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨1, hB⟩ := by
  obtain ⟨ℓ, idx, habs⟩ :=
    non_inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := setup) (height := 0)
      setup_valid (by norm_num [setup]) (ne_of_gt hb) (not_mem_setup hb)
  refine ⟨1, ⟨ℓ, idx, honestSibs h z0 (leafHashes hl setup) idx, 0⟩, Or.inl ⟨?_, ?_⟩⟩
  · show (mixedFlow id hA hB).deadline < (mixedSystem (cv id hA)).time 1 1
    simp [mixedFlow]
  · show AbsenceAccepted h z0 hl (beginTree (mixedSystem (cv id hA)) 1 1)
      (beginHeight (mixedSystem (cv id hA)) 1 1) (legValue cv (mixedFlow id hA hB) ⟨1, hB⟩) _
    show AbsenceAccepted h z0 hl ((mixedSystem (cv id hA)).tree 1 0)
      ((mixedSystem (cv id hA)).height 1 0) (cv id hB) _
    rw [mixedSystem_tree_other (by decide : (1 : Chain) ≠ 0),
        mixedSystem_height_other (by decide : (1 : Chain) ≠ 0)]
    exact habs

/-- Leg `hB` is not finalized: chain `1`'s only on-time batch has an empty tree. -/
private lemma legB_not_finalized {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    (hA' : HashAssumptions h z0 hl) {id hA hB : UInt256} (hb : 0 < cv id hB) :
    ¬ LegFinalized h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨1, hB⟩ := by
  rintro ⟨n, p, hon, hacc⟩
  obtain rfl : n = 0 := by
    have : n ≤ 0 := by simpa [mixedFlow] using hon
    omega
  have hmem := finality_means_membership hA' hacc
  rw [mixedSystem_tree_other (by decide : (1 : Chain) ≠ 0)] at hmem
  exact not_mem_setup hb (by simpa [mixedFlow, legValue] using hmem)

/-! ## What is load-bearing -/

/-- **WITHOUT `_checkFlowId`, A TRUNCATED FLOW PASSES THE GATE.** -/
theorem subset_flow_passes_unchecked_gate {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {id hA hB : UInt256}
    (ha : 0 < cv id hA) (hb : 0 < cv id hB) :
    Wf (mixedSystem (cv id hA))
      ∧ ExecutedViaUncheckedFlowId h z0 hl cv (mixedSystem (cv id hA))
          (subsetFlow id hA) ⟨0, hA⟩
      ∧ LegRefundable h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨1, hB⟩ := by
  refine ⟨mixedSystem_wf ha, ⟨by simp [subsetFlow], ?_⟩, legB_refundable hb⟩
  intro leg hleg
  obtain rfl : leg = ⟨0, hA⟩ := List.mem_singleton.mp hleg
  exact legA_finalized ha _ rfl

/-- **THE CHECK REJECTS IT.** -/
theorem subset_flow_rejected_by_check {fh : FlowHash} (hinj : FlowHashInj fh)
    (id hA hB : UInt256) (hreal : FlowIdChecked fh (mixedFlow id hA hB)) :
    ¬ FlowIdChecked fh (subsetFlow id hA) := by
  intro hsub
  have heq := flowId_check_pins_legList hinj hreal hsub rfl
  have hlegs := congrArg Flow.legs heq
  simp [mixedFlow, subsetFlow] at hlegs

/-- **THE ALL-LEGS LOOP IS NECESSARY.** -/
theorem selfOnly_gate_admits_mixed_outcome {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {id hA hB : UInt256}
    (ha : 0 < cv id hA) (hb : 0 < cv id hB) :
    Wf (mixedSystem (cv id hA)) ∧ FlowWf cv (mixedFlow id hA hB)
      ∧ SelfOnlyGate h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩
      ∧ LegRefundable h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨1, hB⟩ := by
  refine ⟨mixedSystem_wf ha, ?_, ⟨by simp [mixedFlow], legA_finalized ha _ rfl⟩,
    legB_refundable hb⟩
  intro leg hleg
  have hleg' : leg = ⟨0, hA⟩ ∨ leg = ⟨1, hB⟩ := by
    rcases List.mem_cons.mp hleg with hh | hh
    · exact Or.inl hh
    · exact Or.inr (List.mem_singleton.mp hh)
  rcases hleg' with hh | hh <;> rw [hh]
  · exact ne_of_gt ha
  · exact ne_of_gt hb

/-- **THE REAL GATE REFUSES IN THAT STATE.** -/
theorem full_gate_blocks_mixed_outcome {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA' : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash} {id hA hB : UInt256}
    (_ha : 0 < cv id hA) (hb : 0 < cv id hB) :
    ¬ FlowFinalized h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB)
      ∧ ∀ leg, ¬ ExecutedVia h z0 hl cv fh (mixedSystem (cv id hA)) (mixedFlow id hA hB) leg := by
  have hno : ¬ FlowFinalized h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) := by
    intro hall
    exact legB_not_finalized hA' hb (hall ⟨1, hB⟩ (by simp [mixedFlow]))
  exact ⟨hno, fun _ hex => hno hex.2.2⟩

/-- **DATA AVAILABILITY IS NECESSARY.** -/
theorem without_da_committed_leg_is_stuck {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA' : HashAssumptions h z0 hl) {cv : CommitValue} {id hA hB : UInt256}
    (ha : 0 < cv id hA) :
    Wf (mixedSystem (cv id hA))
      ∧ ¬ DataAvailable h z0 hl (mixedSystem (cv id hA)) noAccess
      ∧ LegFinalized h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩
      ∧ ¬ LegFinalizableBy h z0 hl cv (mixedSystem (cv id hA)) noAccess
            (mixedFlow id hA hB) ⟨0, hA⟩
      ∧ ¬ LegRefundable h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩ := by
  have hS := mixedSystem_wf ha
  refine ⟨hS, ?_, legA_finalized ha _ rfl, ?_, ?_⟩
  · -- index 0 of chain 0's tree is occupied, so DA would have to supply its proof
    intro hDA
    exact hDA 0 0 0 (by rw [mixedSystem_tree_zero, insertSetup_leafCount]; omega)
  · rintro ⟨n, p, _, hpres, _⟩
    exact hpres
  · rintro ⟨N, q, hbranch⟩
    have hval : legValue cv (mixedFlow id hA hB) ⟨0, hA⟩ = cv id hA := rfl
    have hmemN : ∀ m : ℕ,
        legValue cv (mixedFlow id hA hB) ⟨0, hA⟩
          ∈ keys (toAbs ((mixedSystem (cv id hA)).tree 0 m)) := by
      intro m
      rw [hval, mixedSystem_tree_zero]
      exact mem_insertSetup ha
    rcases hbranch with ⟨hlate, habs⟩ | ⟨_, habs⟩
    · -- batch 0 is on time, so a late batch is some `N' + 1`, whose begin root is `end N'`
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := by
        cases N with
        | zero => exact absurd hlate (by simp [mixedFlow])
        | succ N' => exact ⟨N', rfl⟩
      exact verified_absence_excludes_delivered hA' (valid_batch hS 0 N') habs (hmemN N')
    · exact verified_absence_excludes_delivered hA' (valid_batch hS 0 N) habs (hmemN N)

end Contracts.Atomicity

/-! ## Certificates -/

namespace Contracts.Atomicity

open Contracts.Atomicity

theorem GateRequiresEveryLeg : Contracts.Atomicity.Properties.GateRequiresEveryLeg :=
  fun _ _ _ _ _ _ _ _ hex other hother => hex.2.2 other hother
theorem FinalitySignalMeansMembership : Contracts.Atomicity.Properties.FinalitySignalMeansMembership :=
  fun _ _ _ hA _ _ _ _ _ hacc => finality_means_membership hA hacc
theorem FinalitySignalPersists : Contracts.Atomicity.Properties.FinalitySignalPersists :=
  fun _ hS c _ _ hnm => keys_mono_batch hS c hnm
theorem MemberIsFinalizable : Contracts.Atomicity.Properties.MemberIsFinalizable :=
  fun _ _ _ _ _ hS _ hDA _ _ _ hon hmem => member_is_finalizable hS hDA hon hmem
theorem ExecutedImpliesAllFinalizable : Contracts.Atomicity.Properties.ExecutedImpliesAllFinalizable :=
  fun _ _ _ hA _ _ _ hS _ hDA _ _ hex => executed_implies_all_finalizable hA hS hDA hex
theorem NoneOrAll : Contracts.Atomicity.Properties.NoneOrAll :=
  fun _ _ _ hA _ _ _ hS _ hDA F => none_or_all hA hS hDA F
theorem ExecutedImpliesFinalityPersists : Contracts.Atomicity.Properties.ExecutedImpliesFinalityPersists :=
  fun _ _ _ hA _ _ _ hS _ hDA _ _ hex => executed_implies_finality_persists hA hS hDA hex
theorem ExecutedExcludesAnyRefund : Contracts.Atomicity.Properties.ExecutedExcludesAnyRefund :=
  fun _ _ _ hA _ _ _ hS _ _ hex => executed_excludes_any_refund hA hS hex
theorem FlowIdCheckPinsLegList : Contracts.Atomicity.Properties.FlowIdCheckPinsLegList :=
  fun _ hinj _ _ hF hF' hid => flowId_check_pins_legList hinj hF hF' hid
theorem SubsetFlowPassesUncheckedGate : Contracts.Atomicity.Properties.SubsetFlowPassesUncheckedGate :=
  fun _ _ _ _ _ _ _ ha hb => subset_flow_passes_unchecked_gate ha hb
theorem SubsetFlowRejectedByCheck : Contracts.Atomicity.Properties.SubsetFlowRejectedByCheck :=
  fun _ hinj id hA hB hreal => subset_flow_rejected_by_check hinj id hA hB hreal
theorem ExecutedImpliesRealFlowFinalizable :
    Contracts.Atomicity.Properties.ExecutedImpliesRealFlowFinalizable :=
  fun _ _ _ hA _ _ hinj _ hS _ hDA _ _ _ hex hF' hid =>
    executed_implies_real_flow_finalizable hA hinj hS hDA hex hF' hid
theorem SelfOnlyGateAdmitsMixedOutcome : Contracts.Atomicity.Properties.SelfOnlyGateAdmitsMixedOutcome :=
  fun _ _ _ _ _ _ _ ha hb => selfOnly_gate_admits_mixed_outcome ha hb
theorem FullGateBlocksMixedOutcome : Contracts.Atomicity.Properties.FullGateBlocksMixedOutcome :=
  fun _ _ _ hA _ _ _ _ _ ha hb => full_gate_blocks_mixed_outcome hA ha hb
theorem WithoutDaCommittedLegIsStuck : Contracts.Atomicity.Properties.WithoutDaCommittedLegIsStuck :=
  fun _ _ _ hA _ _ _ _ ha => without_da_committed_leg_is_stuck hA ha


theorem FlowHashInjUnsatisfiable : Properties.FlowHashInjUnsatisfiable := by
  intro fh hinj
  have hf : Function.Injective (fun d : ℕ => fh [] d) := fun d₁ d₂ he => (hinj [] d₁ [] d₂ he).2
  exact not_injective_infinite_finite _ hf

/-! ## The flow-id check, repaired -/

/-- `x + 1 ≠ x` in `UInt256`: the honest flow hash really separates. -/
lemma uint256_succ_ne_self (x : UInt256) : x + 1 ≠ x := by
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_add] at hv
  have h1 : (1 : UInt256).val = 1 := rfl
  rw [h1] at hv
  have := x.isLt
  simp only [UInt256.size] at this hv
  omega

/-- The position of `x` in `P`, as a `UInt256` (or `0` past `2^256`).  Injective on the
members of any list shorter than `2^256`, which is what the bounded-injectivity
satisfiability witnesses need. -/
def indexHash {α : Type} [DecidableEq α] (P : List α) (x : α) : UInt256 :=
  if hi : P.indexOf x < UInt256.size then ⟨P.indexOf x, hi⟩ else 0

lemma indexHash_inj_on {α : Type} [DecidableEq α] {P : List α} (hP : P.length < UInt256.size)
    {x y : α} (hx : x ∈ P) (hy : y ∈ P) (he : indexHash P x = indexHash P y) : x = y := by
  have hlt := lt_trans (List.indexOf_lt_length.mpr hx) hP
  have hlt' := lt_trans (List.indexOf_lt_length.mpr hy) hP
  unfold indexHash at he
  rw [dif_pos hlt, dif_pos hlt'] at he
  exact (List.indexOf_inj hx hy).mp (Fin.mk.inj_iff.mp he)

/-- Equal preimages and equal claimed ids make equal flows. -/
lemma flow_eq_of_preimage {F F' : Flow} (hid : F.flowId = F'.flowId)
    (hp : (F.legs, F.deadline) = (F'.legs, F'.deadline)) : F = F' := by
  obtain ⟨hl, hd⟩ := Prod.mk.inj hp
  cases F; cases F'
  simp_all

/-- **`_checkFlowId` PINS THE LEG LIST, OR `fh` COLLIDES ON THESE TWO FLOWS.** -/
theorem flowId_check_pins_legList_or_collision {fh : FlowHash} {F F' : Flow}
    (hF : FlowIdChecked fh F) (hF' : FlowIdChecked fh F') (hid : F.flowId = F'.flowId) :
    F = F' ∨ FlowIdClash fh F F' := by
  by_cases hp : (F.legs, F.deadline) = (F'.legs, F'.deadline)
  · exact Or.inl (flow_eq_of_preimage hid hp)
  · exact Or.inr ⟨hp, hF.trans (hid.trans hF'.symm)⟩

theorem honest_flowHash_no_clash (F : Flow) :
    FlowIdChecked (honestFlowHash F) F ∧ ∀ F' : Flow, ¬ FlowIdClash (honestFlowHash F) F F' := by
  refine ⟨by simp [FlowIdChecked, honestFlowHash], ?_⟩
  rintro F' ⟨hne, heq⟩
  have hne' : ¬ (F'.legs, F'.deadline) = (F.legs, F.deadline) := fun h => hne h.symm
  simp only [honestFlowHash, if_pos rfl, if_neg hne'] at heq
  exact uint256_succ_ne_self _ heq.symm

end Contracts.Atomicity

/-! ## Certificates for the repaired flow-id results -/

namespace Contracts.Atomicity

theorem FlowIdCheckPinsLegListOrCollision : Properties.FlowIdCheckPinsLegListOrCollision :=
  fun _ _ _ hF hF' hid => flowId_check_pins_legList_or_collision hF hF' hid

theorem FlowIdCheckPinsLegListOn : Properties.FlowIdCheckPinsLegListOn := by
  intro fh Fs hinj F hFs F' hF's hF hF' hid
  rcases flowId_check_pins_legList_or_collision hF hF' hid with h | h
  · exact h
  · exact absurd h (hinj F hFs F' hF's)

theorem FlowHashInjOnSatisfiable : Properties.FlowHashInjOnSatisfiable := by
  intro Fs hlen
  let P : List (List FlowLeg × ℕ) := Fs.map (fun F => (F.legs, F.deadline))
  have hPlen : P.length < UInt256.size := by
    show (Fs.map _).length < _
    rw [List.length_map]; exact hlen
  refine ⟨fun l d => indexHash P (l, d), ?_⟩
  rintro F hF F' hF' ⟨hne, heq⟩
  exact hne (indexHash_inj_on hPlen (List.mem_map_of_mem (fun F => (F.legs, F.deadline)) hF)
    (List.mem_map_of_mem (fun F => (F.legs, F.deadline)) hF') heq)

theorem HonestFlowHashNoClash : Properties.HonestFlowHashNoClash := honest_flowHash_no_clash

theorem SubsetFlowCheckedOnlyByCollision : Properties.SubsetFlowCheckedOnlyByCollision := by
  intro fh id hA hB hreal hsub
  refine ⟨?_, hreal.trans hsub.symm⟩
  intro hp
  have := congrArg (fun p => p.1.length) hp
  simp [mixedFlow, subsetFlow] at this

theorem SubsetFlowRejectedByCheckOn : Properties.SubsetFlowRejectedByCheckOn := by
  intro fh id hA hB hinj hreal hsub
  exact hinj _ (List.mem_cons_self _ _) _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    (SubsetFlowCheckedOnlyByCollision fh id hA hB hreal hsub)

theorem SubsetFlowRejectedByCheckOnSatisfiable :
    Properties.SubsetFlowRejectedByCheckOnSatisfiable := by
  intro id hA hB
  obtain ⟨hchk, hno⟩ := honest_flowHash_no_clash (mixedFlow id hA hB)
  refine ⟨?_, hchk⟩
  intro F hF F' hF' hcl
  have hF : F = mixedFlow id hA hB ∨ F = subsetFlow id hA := by simpa using hF
  have hF' : F' = mixedFlow id hA hB ∨ F' = subsetFlow id hA := by simpa using hF'
  rcases hF with rfl | rfl <;> rcases hF' with rfl | rfl
  · exact hcl.1 rfl
  · exact hno _ hcl
  · exact hno _ ⟨fun h => hcl.1 h.symm, hcl.2.symm⟩
  · exact hcl.1 rfl

end Contracts.Atomicity

/-! ## The headlines without hash premises

Each proof is the vacuous one with `inclusion_sound hA` replaced by
`inclusion_sound_or_break` and `verified_absence_excludes_delivered hA` replaced by
`verified_absence_excludes_delivered_or_break`, the break threaded to the conclusion. -/

namespace Contracts.Atomicity

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

theorem executedVia_iff_by {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {F : Flow} {leg : FlowLeg} :
    ExecutedVia h z0 hl cv fh S F leg ↔ ∃ ev : GateEvidence, ExecutedViaBy h z0 hl cv fh S F ev leg := by
  classical
  constructor
  · rintro ⟨hmem, hchk, hfin⟩
    refine ⟨fun l => if hl' : l ∈ F.legs then
        (Classical.choose (hfin l hl'), Classical.choose (Classical.choose_spec (hfin l hl')))
      else (0, ⟨⟨0, 0, 0⟩, 0, fun _ => 0, 0⟩), hmem, hchk, ?_⟩
    intro l hl'
    simp only [dif_pos hl']
    exact Classical.choose_spec (Classical.choose_spec (hfin l hl'))
  · rintro ⟨ev, hmem, hchk, hfin⟩
    exact ⟨hmem, hchk, fun l hl' => ⟨(ev l).1, (ev l).2, hfin l hl'⟩⟩

theorem legRefundable_iff_by {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} {F : Flow} {leg : FlowLeg} :
    LegRefundable h z0 hl cv S F leg ↔ ∃ (N : ℕ) (p : ImtProof), LegRefundableBy h z0 hl cv S F leg N p :=
  Iff.rfl

/-- **AN ACCEPTED INCLUSION PROOF MEANS THE LEG IS COMMITTED, OR IT CARRIES A BREAK.** -/
theorem finality_means_membership_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {S : System} {c : Chain} {n : ℕ} {v : UInt256} {p : ImtProof}
    (hacc : Accepts h z0 hl S c n v p) :
    v ∈ keys (toAbs (S.tree c n)) ∨ InclusionBreak h z0 hl S c n p :=
  inclusion_sound_or_break hacc

theorem executed_implies_all_finalizable_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {F : Flow} {ev : GateEvidence} {leg : FlowLeg}
    (hex : ExecutedViaBy h z0 hl cv fh S F ev leg) (other : FlowLeg) (hother : other ∈ F.legs) :
    LegFinalizableBy h z0 hl cv S A F other
      ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2 := by
  obtain ⟨hon, hacc⟩ := hex.2.2 other hother
  rcases finality_means_membership_or_break hacc with hmem | hb
  · exact Or.inl (member_is_finalizable hS hDA hon hmem)
  · exact Or.inr hb

theorem none_or_all_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A)
    (F : Flow) (ev : GateEvidence) :
    FlowFinalizableBy h z0 hl cv S A F
      ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh S F ev leg)
      ∨ GateBreak h z0 hl S F ev := by
  by_cases hex : ∃ leg, ExecutedViaBy h z0 hl cv fh S F ev leg
  · obtain ⟨leg, hleg⟩ := hex
    by_cases hb : GateBreak h z0 hl S F ev
    · exact Or.inr (Or.inr hb)
    · refine Or.inl fun other hother => ?_
      rcases executed_implies_all_finalizable_or_break hS hDA hleg other hother with hf | hbo
      · exact hf
      · exact absurd ⟨other, hother, hbo⟩ hb
  · push_neg at hex
    exact Or.inr (Or.inl hex)

theorem executed_implies_finality_persists_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {F : Flow} {ev : GateEvidence} {leg : FlowLeg}
    (hex : ExecutedViaBy h z0 hl cv fh S F ev leg) (other : FlowLeg) (hother : other ∈ F.legs) :
    (∃ n, S.time other.chain n ≤ F.deadline ∧
      ∀ m, n ≤ m → S.time other.chain m ≤ F.deadline →
        ∃ p, A other.chain m p ∧ Accepts h z0 hl S other.chain m (legValue cv F other) p)
      ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2 := by
  obtain ⟨hon, hacc⟩ := hex.2.2 other hother
  rcases finality_means_membership_or_break hacc with hmem | hb
  · refine Or.inl ⟨(ev other).1, hon, ?_⟩
    intro m hnm _
    obtain ⟨i, hi, hacc'⟩ := honest_accepts hS (keys_mono_batch hS other.chain hnm hmem)
    exact ⟨honestProof h z0 hl S other.chain m i, hDA _ _ _ hi, hacc'⟩
  · exact Or.inr hb

/-- The core of the refund exclusion, for one leg: committed by an on-time batch `n`,
so the absence proof `q` at batch `N` passes the gate only with a break on `q`. -/
theorem member_not_refundable_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {F : Flow} {other : FlowLeg} {n : ℕ}
    (hon : S.time other.chain n ≤ F.deadline)
    (hmem : legValue cv F other ∈ keys (toAbs (S.tree other.chain n))) (N : ℕ) (q : ImtProof) :
    ¬ LegRefundableBy h z0 hl cv S F other N q
      ∨ AbsenceBreak h z0 hl S F.deadline other.chain N q := by
  by_cases hr : LegRefundableBy h z0 hl cv S F other N q
  · refine Or.inr ?_
    rcases hr with ⟨hlate, habs⟩ | ⟨⟨hon', hlast⟩, habs⟩
    · have hnN : n < N := by
        by_contra hcon
        push_neg at hcon
        exact absurd hlate (not_lt.mpr (le_trans (hS.timeOrdered other.chain hcon) hon))
      obtain ⟨N', rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
      rcases verified_absence_excludes_delivered_or_break (valid_batch hS other.chain N') habs
        with hnot | hb
      · exact absurd (keys_mono_batch hS other.chain (by omega) hmem) hnot
      · exact Or.inl ⟨hlate, hb⟩
    · have hnN : n ≤ N := by
        by_contra hcon
        push_neg at hcon
        exact absurd hon (not_le.mpr (hlast n hcon))
      rcases verified_absence_excludes_delivered_or_break (valid_batch hS other.chain N) habs
        with hnot | hb
      · exact absurd (keys_mono_batch hS other.chain hnN hmem) hnot
      · exact Or.inr ⟨hon', hb⟩
  · exact Or.inl hr

theorem executed_excludes_any_refund_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {F : Flow} {ev : GateEvidence}
    {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg)
    (other : FlowLeg) (hother : other ∈ F.legs) (N : ℕ) (q : ImtProof) :
    ¬ LegRefundableBy h z0 hl cv S F other N q
      ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2
      ∨ AbsenceBreak h z0 hl S F.deadline other.chain N q := by
  obtain ⟨hon, hacc⟩ := hex.2.2 other hother
  rcases finality_means_membership_or_break hacc with hmem | hb
  · rcases member_not_refundable_or_break hS hon hmem N q with hn | hb'
    · exact Or.inl hn
    · exact Or.inr (Or.inr hb')
  · exact Or.inr (Or.inl hb)

theorem full_gate_blocks_mixed_outcome_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {id hA hB : UInt256} (hb : 0 < cv id hB) (ev : GateEvidence) :
    ¬ FlowFinalizedBy h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ev
      ∨ InclusionBreak h z0 hl (mixedSystem (cv id hA)) 1 (ev ⟨1, hB⟩).1 (ev ⟨1, hB⟩).2 := by
  by_cases hfin : FlowFinalizedBy h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ev
  · refine Or.inr ?_
    obtain ⟨_, hacc⟩ := hfin ⟨1, hB⟩ (by simp [mixedFlow])
    rcases finality_means_membership_or_break hacc with hmem | hbr
    · exfalso
      rw [mixedSystem_tree_other (by decide : (1 : Chain) ≠ 0)] at hmem
      exact not_mem_setup hb (by simpa [mixedFlow, legValue] using hmem)
    · exact hbr
  · exact Or.inl hfin

/-! ### Anti-vacuity witnesses -/

/-- The honest proof of leaf `i` of chain `c`'s batch `n` carries no break. -/
theorem honestProof_no_break (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System) (c : Chain)
    (n i : ℕ) (hi : i < (S.tree c n).leafCount) :
    ¬ InclusionBreak h z0 hl S c n (honestProof h z0 hl S c n i) :=
  honest_proof_no_break h z0 hl (S.tree c n) (S.height c n) i hi

/-- `insert setup a 0` holds `a` at index 1. -/
lemma insertSetup_leaf_one_value (a : UInt256) : ((insert setup a 0).leaf 1).value = a := by
  simp [Contracts.InteropCommitmentTree.insert, setup]

theorem executed_or_break_satisfiable (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (F : Flow)
      (ev : GateEvidence) (leg : FlowLeg) (N : ℕ) (q : ImtProof),
      Wf S ∧ DataAvailable h z0 hl S A ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ¬ GateBreak h z0 hl S F ev
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N q
        ∧ FlowFinalizableBy h z0 hl cv S A F
        ∧ ¬ LegRefundableBy h z0 hl cv S F leg N q := by
  have h1 : (0 : UInt256) < 1 := by decide
  let cv : CommitValue := fun _ _ => 1
  let S : System := mixedSystem 1
  let F : Flow := subsetFlow 0 1
  let p : ImtProof := honestProof h z0 hl S 0 0 1
  have hS : Wf S := mixedSystem_wf h1
  have hcount : (S.tree 0 0).leafCount = 2 := by
    show ((mixedSystem 1).tree 0 0).leafCount = 2
    rw [mixedSystem_tree_zero]; rfl
  have hacc : Accepts h z0 hl S 0 0 1 p := by
    have := inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := S.tree 0 0)
      (height := S.height 0 0) (hS.capacity 0 0) (i := 1) (by rw [hcount]; norm_num)
    have hv : ((S.tree 0 0).leaf 1).value = 1 := by
      show (((mixedSystem 1).tree 0 0).leaf 1).value = 1
      rw [mixedSystem_tree_zero, insertSetup_leaf_one_value]
    rw [hv] at this
    exact this
  have hnb : ¬ InclusionBreak h z0 hl S 0 0 p :=
    honestProof_no_break h z0 hl S 0 0 1 (by rw [hcount]; norm_num)
  have hmem : (⟨0, 1⟩ : FlowLeg) ∈ F.legs := List.mem_singleton_self _
  have hex : ExecutedViaBy h z0 hl cv (honestFlowHash F) S F (fun _ => (0, p)) ⟨0, 1⟩ := by
    refine ⟨hmem, (honest_flowHash_no_clash F).1, ?_⟩
    intro l hl'
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    exact ⟨by simp [S, F, subsetFlow], hacc⟩
  have hDA : DataAvailable h z0 hl S (fun _ _ _ => True) := fun _ _ _ _ => trivial
  refine ⟨cv, honestFlowHash F, S, fun _ _ _ => True, F, fun _ => (0, p), ⟨0, 1⟩, 0, p,
    hS, hDA, hex, ?_, ?_, ?_, ?_⟩
  · rintro ⟨l, hl', hb⟩
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    exact hnb hb
  · rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
    · exact absurd hlate (by simp [S, F, subsetFlow])
    · exact hnb hb
  · intro other hother
    rcases executed_implies_all_finalizable_or_break hS hDA hex other hother with hf | hb
    · exact hf
    · obtain rfl : other = ⟨0, 1⟩ := List.mem_singleton.mp hother
      exact absurd hb hnb
  · rcases executed_excludes_any_refund_or_break hS hex ⟨0, 1⟩ hmem 0 p with hn | hb | hb
    · exact hn
    · exact absurd hb hnb
    · rcases hb with ⟨hlate, _⟩ | ⟨_, hb⟩
      · exact absurd hlate (by simp [S, F, subsetFlow])
      · exact absurd hb hnb

theorem full_gate_or_break_not_tautology (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (cv : CommitValue) (id hA hB : UInt256) (_ha : 0 < cv id hA) (hb : 0 < cv id hB) :
    ∃ ev : GateEvidence,
      ¬ InclusionBreak h z0 hl (mixedSystem (cv id hA)) 1 (ev ⟨1, hB⟩).1 (ev ⟨1, hB⟩).2
        ∧ ¬ FlowFinalizedBy h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ev := by
  have hcount : ((mixedSystem (cv id hA)).tree 1 0).leafCount = 1 := by
    rw [mixedSystem_tree_other (by decide : (1 : Chain) ≠ 0)]; rfl
  have hnb := honestProof_no_break h z0 hl (mixedSystem (cv id hA)) 1 0 0 (by rw [hcount]; norm_num)
  refine ⟨fun _ => (0, honestProof h z0 hl (mixedSystem (cv id hA)) 1 0 0), hnb, ?_⟩
  intro hfin
  rcases full_gate_blocks_mixed_outcome_or_break (h := h) (z0 := z0) (hl := hl) (hA := hA) hb
      (fun _ => (0, honestProof h z0 hl (mixedSystem (cv id hA)) 1 0 0)) with hn | hbr
  · exact hn hfin
  · exact hnb hbr

/-! ### The padded system -/

@[simp] lemma paddedSystem_tree_zero (a b : UInt256) (n : ℕ) :
    (paddedSystem a b).tree 0 n = threeLeafTree a b := by simp [paddedSystem]

lemma paddedSystem_tree_other {a b : UInt256} {c : Chain} (hc : c ≠ 0) (n : ℕ) :
    (paddedSystem a b).tree c n = setup := by simp [paddedSystem, hc]

@[simp] lemma paddedSystem_height_zero (a b : UInt256) (n : ℕ) :
    (paddedSystem a b).height 0 n = 2 := by simp [paddedSystem]

lemma paddedSystem_height_other {a b : UInt256} {c : Chain} (hc : c ≠ 0) (n : ℕ) :
    (paddedSystem a b).height c n = 0 := by simp [paddedSystem, hc]

@[simp] lemma paddedSystem_time (a b : UInt256) (c : Chain) (n : ℕ) :
    (paddedSystem a b).time c n = n := rfl

lemma paddedSystem_wf {a b : UInt256} (ha : 0 < a) (hab : a < b) : Wf (paddedSystem a b) := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    by_cases hc : c = 0
    · subst hc
      rw [paddedSystem_tree_zero]
      exact Reaches.tail (Reaches.tail Reaches.refl hg1) hg2
    · rw [paddedSystem_tree_other hc]
      exact Reaches.refl
  · intro c n
    by_cases hc : c = 0
    · subst hc
      rw [paddedSystem_tree_zero, paddedSystem_tree_zero]
      exact Reaches.refl
    · rw [paddedSystem_tree_other hc, paddedSystem_tree_other hc]
      exact Reaches.refl
  · intro c i j hij
    simpa using hij
  · intro c n
    by_cases hc : c = 0
    · subst hc
      rw [paddedSystem_tree_zero, paddedSystem_height_zero]
      show (3 : ℕ) ≤ 2 ^ 2
      norm_num
    · rw [paddedSystem_tree_other hc, paddedSystem_height_other hc]
      show (1 : ℕ) ≤ 2 ^ 0
      norm_num

theorem padding_refund_of_executed_leg_locates_absence_break (h : Hash) (hl : LeafHash)
    (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    ∃ (cv : CommitValue) (fh : FlowHash) (F : Flow) (ev : GateEvidence) (leg : FlowLeg)
      (N : ℕ) (q : ImtProof),
      Wf (paddedSystem a b)
        ∧ ExecutedViaBy h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) F ev leg
        ∧ LegRefundableBy h (hl ⟨0, 0, 0⟩) hl cv (paddedSystem a b) F leg N q
        ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) leg.chain (ev leg).1 (ev leg).2
        ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) F.deadline leg.chain N q
        ∧ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2 q.sibs q.pathLen q.index q.leaf
        ∧ (threeLeafTree a b).leafCount ≤ q.index ∧ hl q.leaf = hl ⟨0, 0, 0⟩ := by
  let z0 := hl ⟨0, 0, 0⟩
  let T := threeLeafTree a b
  let F : Flow := subsetFlow 0 0
  let p : ImtProof := ⟨T.leaf 1, 1, honestSibs h z0 (leafHashes hl T) 1, 2⟩
  let q : ImtProof := ⟨⟨0, 0, 0⟩, 3, honestSibs h z0 (leafHashes hl T) 3, 2⟩
  obtain ⟨_, hI, hN⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  obtain ⟨hnb, hpad⟩ := padding_countermodel_locates_padding_hit h hl a b
  have hcount : T.leafCount = 3 := rfl
  refine ⟨fun _ _ => a, honestFlowHash F, F, fun _ => (0, p), ⟨0, 0⟩, 0, q,
    paddedSystem_wf ha hab, ⟨List.mem_singleton_self _, (honest_flowHash_no_clash F).1, ?_⟩,
    Or.inr ⟨⟨le_refl 0, fun m hm => hm⟩, hN⟩, hnb, Or.inr ⟨le_refl 0, hpad⟩, hpad,
    by show T.leafCount ≤ 3; rw [hcount], rfl⟩
  intro l hl'
  obtain rfl : l = ⟨0, 0⟩ := List.mem_singleton.mp hl'
  exact ⟨le_refl 0, hI⟩

end Contracts.Atomicity

/-! ## Certificates for the repaired headlines -/

namespace Contracts.Atomicity

theorem ExecutedViaIffBy : Properties.ExecutedViaIffBy :=
  fun _ _ _ _ _ _ _ _ => executedVia_iff_by
theorem LegRefundableIffBy : Properties.LegRefundableIffBy :=
  fun _ _ _ _ _ _ _ => legRefundable_iff_by
theorem FinalitySignalMeansMembershipOrBreak : Properties.FinalitySignalMeansMembershipOrBreak :=
  fun _ _ _ _ _ _ _ _ hacc => finality_means_membership_or_break hacc
theorem ExecutedImpliesAllFinalizableOrBreak : Properties.ExecutedImpliesAllFinalizableOrBreak :=
  fun _ _ _ _ _ _ hS _ hDA _ _ _ hex other hother =>
    executed_implies_all_finalizable_or_break hS hDA hex other hother
theorem NoneOrAllOrBreak : Properties.NoneOrAllOrBreak :=
  fun _ _ _ _ _ _ hS _ hDA F ev => none_or_all_or_break hS hDA F ev
theorem ExecutedImpliesFinalityPersistsOrBreak : Properties.ExecutedImpliesFinalityPersistsOrBreak :=
  fun _ _ _ _ _ _ hS _ hDA _ _ _ hex other hother =>
    executed_implies_finality_persists_or_break hS hDA hex other hother
theorem ExecutedExcludesAnyRefundOrBreak : Properties.ExecutedExcludesAnyRefundOrBreak :=
  fun _ _ _ _ _ _ hS _ _ _ hex other hother N q =>
    executed_excludes_any_refund_or_break hS hex other hother N q
theorem FullGateBlocksMixedOutcomeOrBreak : Properties.FullGateBlocksMixedOutcomeOrBreak :=
  fun _ _ _ _ _ _ _ hb ev => full_gate_blocks_mixed_outcome_or_break hb ev
theorem ExecutedOrBreakSatisfiable : Properties.ExecutedOrBreakSatisfiable :=
  executed_or_break_satisfiable
theorem FullGateOrBreakNotTautology : Properties.FullGateOrBreakNotTautology :=
  full_gate_or_break_not_tautology
theorem PaddingRefundOfExecutedLegLocatesAbsenceBreak :
    Properties.PaddingRefundOfExecutedLegLocatesAbsenceBreak :=
  padding_refund_of_executed_leg_locates_absence_break

end Contracts.Atomicity

/-! ## Data availability is necessary, without hash premises -/

namespace Contracts.Atomicity

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

theorem without_da_committed_leg_is_stuck_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {id hA hB : UInt256} (ha : 0 < cv id hA) :
    Wf (mixedSystem (cv id hA))
      ∧ ¬ DataAvailable h z0 hl (mixedSystem (cv id hA)) noAccess
      ∧ LegFinalized h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩
      ∧ ¬ LegFinalizableBy h z0 hl cv (mixedSystem (cv id hA)) noAccess
            (mixedFlow id hA hB) ⟨0, hA⟩
      ∧ ∀ (N : ℕ) (q : ImtProof),
          ¬ LegRefundableBy h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩ N q
            ∨ AbsenceBreak h z0 hl (mixedSystem (cv id hA)) (mixedFlow id hA hB).deadline 0 N q := by
  have hS := mixedSystem_wf ha
  refine ⟨hS, ?_, legA_finalized ha _ rfl, ?_, ?_⟩
  · intro hDA
    exact hDA 0 0 0 (by rw [mixedSystem_tree_zero, insertSetup_leafCount]; omega)
  · rintro ⟨n, p, _, hpres, _⟩
    exact hpres
  · intro N q
    refine member_not_refundable_or_break hS (n := 0) (by simp [mixedFlow]) ?_ N q
    show cv id hA ∈ keys (toAbs ((mixedSystem (cv id hA)).tree 0 0))
    rw [mixedSystem_tree_zero]
    exact mem_insertSetup ha

theorem without_da_or_break_not_tautology (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (cv : CommitValue) (id hA hB : UInt256) (ha : 0 < cv id hA) :
    ∃ (N : ℕ) (q : ImtProof),
      ¬ AbsenceBreak h z0 hl (mixedSystem (cv id hA)) (mixedFlow id hA hB).deadline 0 N q
        ∧ ¬ LegRefundableBy h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩ N q := by
  have hcount : ((mixedSystem (cv id hA)).tree 0 0).leafCount = 2 := by
    rw [mixedSystem_tree_zero]; rfl
  have hnb := honestProof_no_break h z0 hl (mixedSystem (cv id hA)) 0 0 1 (by rw [hcount]; norm_num)
  have hnab : ¬ AbsenceBreak h z0 hl (mixedSystem (cv id hA)) (mixedFlow id hA hB).deadline 0 0
      (honestProof h z0 hl (mixedSystem (cv id hA)) 0 0 1) := by
    rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
    · exact absurd hlate (by simp [mixedFlow])
    · exact hnb hb
  refine ⟨0, honestProof h z0 hl (mixedSystem (cv id hA)) 0 0 1, hnab, ?_⟩
  rcases (without_da_committed_leg_is_stuck_or_break (h := h) (z0 := z0) (hl := hl) (hB := hB)
      ha).2.2.2.2 0 (honestProof h z0 hl (mixedSystem (cv id hA)) 0 0 1) with hn | hb
  · exact hn
  · exact absurd hb hnab

theorem WithoutDaCommittedLegIsStuckOrBreak : Properties.WithoutDaCommittedLegIsStuckOrBreak :=
  fun _ _ _ _ _ _ _ ha => without_da_committed_leg_is_stuck_or_break ha
theorem WithoutDaOrBreakNotTautology : Properties.WithoutDaOrBreakNotTautology :=
  without_da_or_break_not_tautology

end Contracts.Atomicity

/-! ## None or all, with the break pinned to a leg -/

namespace Contracts.Atomicity

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-- The list core of uniqueness: two "first failures" of the same predicate in the same
list are the same element. -/
theorem first_failure_unique {P : FlowLeg → Prop} :
    ∀ (pre₁ pre₂ post₁ post₂ : List FlowLeg) (l₁ l₂ : FlowLeg),
      pre₁ ++ l₁ :: post₁ = pre₂ ++ l₂ :: post₂ →
      (∀ x ∈ pre₁, P x) → ¬ P l₁ → (∀ x ∈ pre₂, P x) → ¬ P l₂ → l₁ = l₂
  | [], [], _, _, _, _, he, _, _, _, _ => by
      simp only [List.nil_append, List.cons.injEq] at he
      exact he.1
  | [], y :: ys, _, _, l₁, _, he, _, n₁, h₂, _ => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      rw [he.1] at n₁
      exact absurd (h₂ y (List.mem_cons_self _ _)) n₁
  | x :: xs, [], _, _, _, l₂, he, h₁, _, _, n₂ => by
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
      rw [← he.1] at n₂
      exact absurd (h₁ x (List.mem_cons_self _ _)) n₂
  | x :: xs, y :: ys, post₁, post₂, l₁, l₂, he, h₁, n₁, h₂, n₂ => by
      simp only [List.cons_append, List.cons.injEq] at he
      exact first_failure_unique xs ys post₁ post₂ l₁ l₂ he.2
        (fun z hz => h₁ z (List.mem_cons_of_mem _ hz)) n₁
        (fun z hz => h₂ z (List.mem_cons_of_mem _ hz)) n₂

/-- The list core of existence: a list with a failure has a first one. -/
theorem first_failure_exists {P : FlowLeg → Prop} :
    ∀ L : List FlowLeg, (∃ l ∈ L, ¬ P l) →
      ∃ (pre : List FlowLeg) (l : FlowLeg) (post : List FlowLeg),
        L = pre ++ l :: post ∧ (∀ x ∈ pre, P x) ∧ ¬ P l
  | [], ⟨_, hl, _⟩ => absurd hl (List.not_mem_nil _)
  | a :: t, hex => by
      by_cases ha : P a
      · obtain ⟨l, hl, hnl⟩ := hex
        have hlt : ∃ l ∈ t, ¬ P l := by
          rcases List.mem_cons.mp hl with rfl | hlt
          · exact absurd ha hnl
          · exact ⟨l, hlt, hnl⟩
        obtain ⟨pre, l', post, he, hpre, hn⟩ := first_failure_exists t hlt
        refine ⟨a :: pre, l', post, by rw [he]; rfl, ?_, hn⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hpre x hx
      · exact ⟨[], a, t, rfl, fun x hx => absurd hx (List.not_mem_nil _), ha⟩

theorem first_stranded_leg_unique {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} {A : Access} {F : Flow} {l₁ l₂ : FlowLeg}
    (h₁ : FirstStrandedLeg h z0 hl cv S A F l₁) (h₂ : FirstStrandedLeg h z0 hl cv S A F l₂) :
    l₁ = l₂ := by
  obtain ⟨pre₁, post₁, he₁, hp₁, hn₁⟩ := h₁
  obtain ⟨pre₂, post₂, he₂, hp₂, hn₂⟩ := h₂
  exact first_failure_unique pre₁ pre₂ post₁ post₂ l₁ l₂ (he₁.symm.trans he₂) hp₁ hn₁ hp₂ hn₂

theorem firstStrandedLeg_mem {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} {A : Access} {F : Flow} {leg : FlowLeg}
    (hf : FirstStrandedLeg h z0 hl cv S A F leg) : leg ∈ F.legs := by
  obtain ⟨pre, post, he, _, _⟩ := hf
  rw [he]
  exact List.mem_append_right _ (List.mem_cons_self _ _)

theorem first_stranded_leg_iff_not_finalizable {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {A : Access} {F : Flow} :
    (∃ leg, FirstStrandedLeg h z0 hl cv S A F leg) ↔ ¬ FlowFinalizableBy h z0 hl cv S A F := by
  constructor
  · rintro ⟨leg, hf⟩ hall
    have hm := firstStrandedLeg_mem hf
    obtain ⟨_, _, _, _, hn⟩ := hf
    exact hn (hall leg hm)
  · intro hnot
    have hex : ∃ l ∈ F.legs, ¬ LegFinalizableBy h z0 hl cv S A F l := by
      by_contra hno
      push_neg at hno
      exact hnot hno
    obtain ⟨pre, l, post, he, hpre, hn⟩ := first_failure_exists F.legs hex
    exact ⟨l, pre, post, he, hpre, hn⟩

theorem pinned_gate_break_implies_gate_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {A : Access} {F : Flow} {ev : GateEvidence}
    (hp : PinnedGateBreak h z0 hl cv S A F ev) : GateBreak h z0 hl S F ev := by
  obtain ⟨leg, hf, hb⟩ := hp
  exact ⟨leg, firstStrandedLeg_mem hf, hb⟩

theorem none_or_all_or_break_pinned {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A)
    (F : Flow) (ev : GateEvidence) :
    FlowFinalizableBy h z0 hl cv S A F
      ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh S F ev leg)
      ∨ PinnedGateBreak h z0 hl cv S A F ev := by
  by_cases hfin : FlowFinalizableBy h z0 hl cv S A F
  · exact Or.inl hfin
  by_cases hex : ∃ leg, ExecutedViaBy h z0 hl cv fh S F ev leg
  · obtain ⟨leg, hleg⟩ := hex
    obtain ⟨l, hfirst⟩ := first_stranded_leg_iff_not_finalizable.2 hfin
    have hn : ¬ LegFinalizableBy h z0 hl cv S A F l := by
      obtain ⟨_, _, _, _, hn⟩ := hfirst
      exact hn
    rcases executed_implies_all_finalizable_or_break hS hDA hleg l (firstStrandedLeg_mem hfirst)
      with hf | hb
    · exact absurd hf hn
    · exact Or.inr (Or.inr ⟨l, hfirst, hb⟩)
  · push_neg at hex
    exact Or.inr (Or.inl hex)

theorem none_or_all_or_break_pinned_not_tautology (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (F : Flow)
      (ev : GateEvidence) (leg : FlowLeg),
      Wf S ∧ DataAvailable h z0 hl S A ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ¬ PinnedGateBreak h z0 hl cv S A F ev := by
  obtain ⟨cv, fh, S, A, F, ev, leg, _, _, hS, hDA, hex, hng, _⟩ :=
    executed_or_break_satisfiable h z0 hl
  exact ⟨cv, fh, S, A, F, ev, leg, hS, hDA, hex,
    fun hp => hng (pinned_gate_break_implies_gate_break hp)⟩

/-- Chain `1`'s tree in `mixedSystem 1` is `setup` at height 0, whose root is the
sentinel's leaf hash. -/
lemma setup_root_zero (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    root h z0 hl setup 0 = hl ⟨0, 0, 0⟩ := rfl

theorem pinned_gate_break_fires (h : Hash) (z0 : UInt256) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (F : Flow)
      (ev : GateEvidence) (legA legB : FlowLeg),
      Wf S ∧ DataAvailable h z0 toyLeafHash S A
        ∧ ExecutedViaBy h z0 toyLeafHash cv fh S F ev legA
        ∧ ¬ FlowFinalizableBy h z0 toyLeafHash cv S A F
        ∧ FirstStrandedLeg h z0 toyLeafHash cv S A F legB
        ∧ InclusionBreak h z0 toyLeafHash S legB.chain (ev legB).1 (ev legB).2
        ∧ legA ∈ F.legs ∧ legA ≠ legB
        ∧ LegFinalizableBy h z0 toyLeafHash cv S A F legA
        ∧ InclusionBreak h z0 toyLeafHash S legA.chain (ev legA).1 (ev legA).2 := by
  have h1 : (0 : UInt256) < 1 := by decide
  have h10 : (1 : Chain) ≠ 0 := by decide
  -- The instance.
  let hl : LeafHash := toyLeafHash
  let cv : CommitValue := fun _ b => b
  let S : System := mixedSystem 1
  let F : Flow := mixedFlow 0 1 2
  let A : Access := fun c n p => ∃ i, i < (S.tree c n).leafCount ∧ p = honestProof h z0 hl S c n i
  let legA : FlowLeg := ⟨0, 1⟩
  let legB : FlowLeg := ⟨1, 2⟩
  let TA : Tree := insert setup 1 0
  let pA : ImtProof := ⟨⟨1, 5, 0⟩, 1, honestSibs h z0 (leafHashes hl TA) 1, 1⟩
  let pB : ImtProof := ⟨⟨2, 0, 2⟩, 0, fun _ => 0, 0⟩
  let ev : GateEvidence := fun l => if l = legA then (0, pA) else (0, pB)
  have hAB : legA ≠ legB := by
    show (⟨0, 1⟩ : FlowLeg) ≠ ⟨1, 2⟩
    decide
  have evA : ev legA = (0, pA) := if_pos rfl
  have evB : ev legB = (0, pB) := if_neg (fun he => hAB he.symm)
  have hS : Wf S := mixedSystem_wf h1
  have hDA : DataAvailable h z0 hl S A := fun c n i hi => ⟨i, hi, rfl⟩
  have hmemA : legA ∈ F.legs := List.mem_cons_self _ _
  have hmemB : legB ∈ F.legs := List.mem_cons_of_mem _ (List.mem_singleton_self _)
  -- Leg A: the forged proof is accepted (a leaf-hash collision with the stored leaf 1).
  have hcountA : TA.leafCount = 2 := rfl
  have hleafA : TA.leaf 1 = ⟨1, 0, 0⟩ := rfl
  have accA : Accepts h z0 hl S 0 0 1 pA := by
    have hI := inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := TA) (height := 1)
      (by rw [hcountA]; norm_num) (i := 1) (by rw [hcountA]; norm_num)
    show InclusionAccepted h hl (root h z0 hl ((mixedSystem 1).tree 0 0)
      ((mixedSystem 1).height 0 0)) 1 ⟨1, 5, 0⟩ 1 (honestSibs h z0 (leafHashes hl TA) 1) 1
    rw [mixedSystem_tree_zero, mixedSystem_height_zero]
    refine ⟨rfl, hI.path.inBounds, ?_⟩
    have hrec := hI.path.recompute
    rw [hleafA] at hrec
    exact hrec
  have brkA : InclusionBreak h z0 hl S legA.chain (ev legA).1 (ev legA).2 := by
    rw [evA]
    show TreeRootBreak h z0 hl ((mixedSystem 1).tree 0 0) ((mixedSystem 1).height 0 0)
      (honestSibs h z0 (leafHashes hl TA) 1) 1 1 ⟨1, 5, 0⟩
    rw [mixedSystem_tree_zero, mixedSystem_height_zero]
    exact TreeRootBreak.leafCollision (by rw [hcountA]; norm_num) (by rw [hleafA]; decide)
      (by rw [hleafA]; rfl)
  -- Leg B: never committed; the forged empty-path proof is accepted (a leaf-hash
  -- collision with chain 1's sentinel).
  have accB : Accepts h z0 hl S 1 0 2 pB := by
    show InclusionAccepted h hl (root h z0 hl ((mixedSystem 1).tree 1 0)
      ((mixedSystem 1).height 1 0)) 2 ⟨2, 0, 2⟩ 0 (fun _ => 0) 0
    rw [mixedSystem_tree_other h10, mixedSystem_height_other h10, setup_root_zero]
    refine ⟨rfl, by norm_num, ?_⟩
    show toyLeafHash ⟨2, 0, 2⟩ = toyLeafHash ⟨0, 0, 0⟩
    decide
  have brkB : InclusionBreak h z0 hl S legB.chain (ev legB).1 (ev legB).2 := by
    rw [evB]
    show TreeRootBreak h z0 hl ((mixedSystem 1).tree 1 0) ((mixedSystem 1).height 1 0)
      (fun _ => 0) 0 0 ⟨2, 0, 2⟩
    rw [mixedSystem_tree_other h10, mixedSystem_height_other h10]
    exact TreeRootBreak.leafCollision (by norm_num [setup]) (by decide) (by decide)
  -- The gate passes on `ev`.
  have hex : ExecutedViaBy h z0 hl cv (honestFlowHash F) S F ev legA := by
    refine ⟨hmemA, (honest_flowHash_no_clash F).1, ?_⟩
    intro l hl'
    rcases List.mem_cons.mp hl' with rfl | hl'
    · rw [evA]; exact ⟨le_refl _, accA⟩
    · obtain rfl := List.mem_singleton.mp hl'
      rw [evB]; exact ⟨le_refl _, accB⟩
  -- Finalizability: A is, B is not.
  have finA : LegFinalizableBy h z0 hl cv S A F legA := by
    refine member_is_finalizable hS hDA (n := 0) (le_refl _) ?_
    show (1 : UInt256) ∈ keys (toAbs ((mixedSystem 1).tree 0 0))
    rw [mixedSystem_tree_zero]
    exact mem_insertSetup h1
  have nfinB : ¬ LegFinalizableBy h z0 hl cv S A F legB := by
    rintro ⟨n, p, _, ⟨i, _, rfl⟩, hacc⟩
    have hv := hacc.valueMatch
    change (((mixedSystem 1).tree 1 n).leaf i).value = 2 at hv
    rw [mixedSystem_tree_other h10] at hv
    change (0 : UInt256) = 2 at hv
    exact absurd hv (by decide)
  refine ⟨cv, honestFlowHash F, S, A, F, ev, legA, legB, hS, hDA, hex,
    fun hall => nfinB (hall legB hmemB), ⟨[legA], [], rfl, ?_, nfinB⟩, brkB, hmemA, hAB, finA,
    brkA⟩
  intro l hl'
  obtain rfl := List.mem_singleton.mp hl'
  exact finA

theorem FirstStrandedLegUnique : Properties.FirstStrandedLegUnique :=
  fun _ _ _ _ _ _ _ _ _ h₁ h₂ => first_stranded_leg_unique h₁ h₂
theorem FirstStrandedLegIffNotFinalizable : Properties.FirstStrandedLegIffNotFinalizable :=
  fun _ _ _ _ _ _ _ => first_stranded_leg_iff_not_finalizable
theorem PinnedGateBreakImpliesGateBreak : Properties.PinnedGateBreakImpliesGateBreak :=
  fun _ _ _ _ _ _ _ _ hp => pinned_gate_break_implies_gate_break hp
theorem NoneOrAllOrBreakPinned : Properties.NoneOrAllOrBreakPinned :=
  fun _ _ _ _ _ _ hS _ hDA F ev => none_or_all_or_break_pinned hS hDA F ev
theorem NoneOrAllOrBreakPinnedNotTautology : Properties.NoneOrAllOrBreakPinnedNotTautology :=
  none_or_all_or_break_pinned_not_tautology
theorem PinnedGateBreakFires : Properties.PinnedGateBreakFires := pinned_gate_break_fires

end Contracts.Atomicity

/-! ## The pinned break, evaluated on a stranded leg -/

namespace Contracts.Atomicity

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

theorem honestAccess_dataAvailable (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System) :
    DataAvailable h z0 hl S (honestAccess h z0 hl S) :=
  fun _ _ i hi => ⟨i, hi, rfl⟩

/-- The world shared by the two witnesses: leg `⟨0, 1⟩` is finalizable, leg `⟨1, 2⟩` is
not, so `⟨1, 2⟩` is the first stranded leg. -/
theorem mixed_stranded_world (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    LegFinalizableBy h z0 hl (fun _ b => b) (mixedSystem 1) (honestAccess h z0 hl (mixedSystem 1))
        (mixedFlow 0 1 2) ⟨0, 1⟩
      ∧ ¬ LegFinalizableBy h z0 hl (fun _ b => b) (mixedSystem 1)
          (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ FirstStrandedLeg h z0 hl (fun _ b => b) (mixedSystem 1)
          (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2) ⟨1, 2⟩ := by
  have h1 : (0 : UInt256) < 1 := by decide
  have h10 : (1 : Chain) ≠ 0 := by decide
  have hS : Wf (mixedSystem 1) := mixedSystem_wf h1
  have finA : LegFinalizableBy h z0 hl (fun _ b => b) (mixedSystem 1)
      (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2) ⟨0, 1⟩ := by
    refine member_is_finalizable hS (honestAccess_dataAvailable h z0 hl _) (n := 0) (le_refl _) ?_
    show (1 : UInt256) ∈ keys (toAbs ((mixedSystem 1).tree 0 0))
    rw [mixedSystem_tree_zero]
    exact mem_insertSetup h1
  have nfinB : ¬ LegFinalizableBy h z0 hl (fun _ b => b) (mixedSystem 1)
      (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2) ⟨1, 2⟩ := by
    rintro ⟨n, p, _, ⟨i, _, rfl⟩, hacc⟩
    have hv := hacc.valueMatch
    change (((mixedSystem 1).tree 1 n).leaf i).value = 2 at hv
    rw [mixedSystem_tree_other h10] at hv
    change (0 : UInt256) = 2 at hv
    exact absurd hv (by decide)
  refine ⟨finA, nfinB, [⟨0, 1⟩], [], rfl, ?_, nfinB⟩
  intro l hl'
  obtain rfl := List.mem_singleton.mp hl'
  exact finA

/-- The honest proof of chain `1`'s only leaf (the sentinel) is not accepted for the
commit value `2`. -/
theorem honest_legB_rejected (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ¬ Accepts h z0 hl (mixedSystem 1) 1 0 2 (honestProof h z0 hl (mixedSystem 1) 1 0 0) := by
  intro hacc
  have hv := hacc.valueMatch
  change (((mixedSystem 1).tree 1 0).leaf 0).value = 2 at hv
  rw [mixedSystem_tree_other (by decide : (1 : Chain) ≠ 0)] at hv
  change (0 : UInt256) = 2 at hv
  exact absurd hv (by decide)

/-- On any evidence that submits the honest sentinel proof for `⟨1, 2⟩`: no leg executes,
and the pinned break is false. -/
theorem honest_legB_evidence (h : Hash) (z0 : UInt256) (hl : LeafHash) (fh : FlowHash)
    (ev : GateEvidence) (hev : ev ⟨1, 2⟩ = (0, honestProof h z0 hl (mixedSystem 1) 1 0 0)) :
    (∀ leg, ¬ ExecutedViaBy h z0 hl (fun _ b => b) fh (mixedSystem 1) (mixedFlow 0 1 2) ev leg)
      ∧ ¬ InclusionBreak h z0 hl (mixedSystem 1) 1 (ev ⟨1, 2⟩).1 (ev ⟨1, 2⟩).2
      ∧ ¬ PinnedGateBreak h z0 hl (fun _ b => b) (mixedSystem 1)
          (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2) ev := by
  have hmemB : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 0 1 2).legs :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hcount : ((mixedSystem 1).tree 1 0).leafCount = 1 := by
    rw [mixedSystem_tree_other (by decide : (1 : Chain) ≠ 0)]; rfl
  have hnb : ¬ InclusionBreak h z0 hl (mixedSystem 1) 1 (ev ⟨1, 2⟩).1 (ev ⟨1, 2⟩).2 := by
    rw [hev]
    exact honestProof_no_break h z0 hl (mixedSystem 1) 1 0 0 (by rw [hcount]; norm_num)
  refine ⟨?_, hnb, ?_⟩
  · rintro leg ⟨_, _, hfin⟩
    obtain ⟨_, hacc⟩ := hfin ⟨1, 2⟩ hmemB
    rw [hev] at hacc
    exact honest_legB_rejected h z0 hl hacc
  · rintro ⟨l, hf, hb⟩
    obtain rfl := first_stranded_leg_unique hf (mixed_stranded_world h z0 hl).2.2
    exact hnb hb

theorem none_or_all_or_break_pinned_stranded_not_tautology (h : Hash) (z0 : UInt256)
    (hl : LeafHash) :
    Wf (mixedSystem 1)
      ∧ DataAvailable h z0 hl (mixedSystem 1) (honestAccess h z0 hl (mixedSystem 1))
      ∧ FlowIdChecked (honestFlowHash (mixedFlow 0 1 2)) (mixedFlow 0 1 2)
      ∧ ¬ FlowFinalizableBy h z0 hl (fun _ b => b) (mixedSystem 1)
            (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2)
      ∧ FirstStrandedLeg h z0 hl (fun _ b => b) (mixedSystem 1)
            (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ ∃ ev : GateEvidence,
          ev ⟨1, 2⟩ = (0, honestProof h z0 hl (mixedSystem 1) 1 0 0)
          ∧ LegFinalizedBy h z0 hl (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨0, 1⟩
              (ev ⟨0, 1⟩).1 (ev ⟨0, 1⟩).2
          ∧ (∀ leg, ¬ ExecutedViaBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
              (mixedSystem 1) (mixedFlow 0 1 2) ev leg)
          ∧ ¬ PinnedGateBreak h z0 hl (fun _ b => b) (mixedSystem 1)
              (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2) ev := by
  have h1 : (0 : UInt256) < 1 := by decide
  obtain ⟨_, nfinB, hfirst⟩ := mixed_stranded_world h z0 hl
  have hmemB : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 0 1 2).legs :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  -- Leg `⟨0, 1⟩`: the honest proof of chain `0`'s leaf 1, which holds the value `1`.
  have hcountA : ((mixedSystem 1).tree 0 0).leafCount = 2 := by
    rw [mixedSystem_tree_zero]; rfl
  have accA : Accepts h z0 hl (mixedSystem 1) 0 0 1 (honestProof h z0 hl (mixedSystem 1) 0 0 1) := by
    have := inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := (mixedSystem 1).tree 0 0)
      (height := (mixedSystem 1).height 0 0) ((mixedSystem_wf h1).capacity 0 0) (i := 1)
      (by rw [hcountA]; norm_num)
    have hv : (((mixedSystem 1).tree 0 0).leaf 1).value = 1 := by
      rw [mixedSystem_tree_zero, insertSetup_leaf_one_value]
    rw [hv] at this
    exact this
  let ev : GateEvidence := fun l =>
    if l = ⟨0, 1⟩ then (0, honestProof h z0 hl (mixedSystem 1) 0 0 1)
    else (0, honestProof h z0 hl (mixedSystem 1) 1 0 0)
  have evB : ev ⟨1, 2⟩ = (0, honestProof h z0 hl (mixedSystem 1) 1 0 0) := if_neg (by decide)
  obtain ⟨hnex, _, hnp⟩ := honest_legB_evidence h z0 hl (honestFlowHash (mixedFlow 0 1 2)) ev evB
  refine ⟨mixedSystem_wf h1, honestAccess_dataAvailable h z0 hl _,
    (honest_flowHash_no_clash _).1, fun hall => nfinB (hall _ hmemB), hfirst, ev, evB, ?_,
    hnex, hnp⟩
  show (mixedSystem 1).time 0 0 ≤ 0
      ∧ Accepts h z0 hl (mixedSystem 1) 0 0 1 (honestProof h z0 hl (mixedSystem 1) 0 0 1)
  exact ⟨le_refl _, accA⟩

theorem pinned_gate_break_fires_only_on_stranded_leg (h : Hash) (z0 : UInt256) :
    Wf (mixedSystem 1)
      ∧ DataAvailable h z0 toyLeafHash (mixedSystem 1) (honestAccess h z0 toyLeafHash (mixedSystem 1))
      ∧ FirstStrandedLeg h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
          (honestAccess h z0 toyLeafHash (mixedSystem 1)) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ ∃ evH evF : GateEvidence,
          evH ⟨0, 1⟩ = evF ⟨0, 1⟩
          ∧ ¬ InclusionBreak h z0 toyLeafHash (mixedSystem 1) 0 (evF ⟨0, 1⟩).1 (evF ⟨0, 1⟩).2
          ∧ ExecutedViaBy h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
              (mixedSystem 1) (mixedFlow 0 1 2) evF ⟨0, 1⟩
          ∧ InclusionBreak h z0 toyLeafHash (mixedSystem 1) 1 (evF ⟨1, 2⟩).1 (evF ⟨1, 2⟩).2
          ∧ PinnedGateBreak h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
              (honestAccess h z0 toyLeafHash (mixedSystem 1)) (mixedFlow 0 1 2) evF
          ∧ (∀ leg, ¬ ExecutedViaBy h z0 toyLeafHash (fun _ b => b)
              (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1) (mixedFlow 0 1 2) evH leg)
          ∧ ¬ PinnedGateBreak h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
              (honestAccess h z0 toyLeafHash (mixedSystem 1)) (mixedFlow 0 1 2) evH := by
  have h1 : (0 : UInt256) < 1 := by decide
  have h10 : (1 : Chain) ≠ 0 := by decide
  let hl : LeafHash := toyLeafHash
  let S : System := mixedSystem 1
  obtain ⟨_, _, hfirst⟩ := mixed_stranded_world h z0 hl
  -- Leg `⟨0, 1⟩`: the honest proof of chain `0`'s leaf 1, in both evidences.
  let pA : ImtProof := honestProof h z0 hl S 0 0 1
  have hcountA : (S.tree 0 0).leafCount = 2 := by
    show ((mixedSystem 1).tree 0 0).leafCount = 2
    rw [mixedSystem_tree_zero]; rfl
  have accA : Accepts h z0 hl S 0 0 1 pA := by
    have := inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := S.tree 0 0)
      (height := S.height 0 0) ((mixedSystem_wf h1).capacity 0 0) (i := 1)
      (by rw [hcountA]; norm_num)
    have hv : ((S.tree 0 0).leaf 1).value = 1 := by
      show (((mixedSystem 1).tree 0 0).leaf 1).value = 1
      rw [mixedSystem_tree_zero, insertSetup_leaf_one_value]
    rw [hv] at this
    exact this
  have nbA : ¬ InclusionBreak h z0 hl S 0 0 pA :=
    honestProof_no_break h z0 hl S 0 0 1 (by rw [hcountA]; norm_num)
  -- Leg `⟨1, 2⟩`: honest sentinel proof in `evH`, forged empty-path proof in `evF`.
  let pB : ImtProof := ⟨⟨2, 0, 2⟩, 0, fun _ => 0, 0⟩
  let evH : GateEvidence := fun l => if l = ⟨0, 1⟩ then (0, pA) else (0, honestProof h z0 hl S 1 0 0)
  let evF : GateEvidence := fun l => if l = ⟨0, 1⟩ then (0, pA) else (0, pB)
  have evFA : evF ⟨0, 1⟩ = (0, pA) := if_pos rfl
  have evFB : evF ⟨1, 2⟩ = (0, pB) := if_neg (by decide)
  have evHB : evH ⟨1, 2⟩ = (0, honestProof h z0 hl S 1 0 0) := if_neg (by decide)
  have accB : Accepts h z0 hl S 1 0 2 pB := by
    show InclusionAccepted h hl (root h z0 hl ((mixedSystem 1).tree 1 0)
      ((mixedSystem 1).height 1 0)) 2 ⟨2, 0, 2⟩ 0 (fun _ => 0) 0
    rw [mixedSystem_tree_other h10, mixedSystem_height_other h10, setup_root_zero]
    refine ⟨rfl, by norm_num, ?_⟩
    show toyLeafHash ⟨2, 0, 2⟩ = toyLeafHash ⟨0, 0, 0⟩
    decide
  have brkB : InclusionBreak h z0 hl S 1 (evF ⟨1, 2⟩).1 (evF ⟨1, 2⟩).2 := by
    rw [evFB]
    show TreeRootBreak h z0 hl ((mixedSystem 1).tree 1 0) ((mixedSystem 1).height 1 0)
      (fun _ => 0) 0 0 ⟨2, 0, 2⟩
    rw [mixedSystem_tree_other h10, mixedSystem_height_other h10]
    exact TreeRootBreak.leafCollision (by norm_num [setup]) (by decide) (by decide)
  have hex : ExecutedViaBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) S
      (mixedFlow 0 1 2) evF ⟨0, 1⟩ := by
    refine ⟨List.mem_cons_self _ _, (honest_flowHash_no_clash _).1, ?_⟩
    intro l hl'
    rcases List.mem_cons.mp hl' with rfl | hl'
    · rw [evFA]; exact ⟨le_refl _, accA⟩
    · obtain rfl := List.mem_singleton.mp hl'
      rw [evFB]; exact ⟨le_refl _, accB⟩
  obtain ⟨hnexH, _, hnpH⟩ :=
    honest_legB_evidence h z0 hl (honestFlowHash (mixedFlow 0 1 2)) evH evHB
  refine ⟨mixedSystem_wf h1, honestAccess_dataAvailable h z0 hl _, hfirst, evH, evF, rfl,
    by rw [evFA]; exact nbA, hex, brkB, ⟨⟨1, 2⟩, hfirst, brkB⟩, hnexH, hnpH⟩

theorem HonestAccessDataAvailable : Properties.HonestAccessDataAvailable :=
  honestAccess_dataAvailable
theorem NoneOrAllOrBreakPinnedStrandedNotTautology :
    Properties.NoneOrAllOrBreakPinnedStrandedNotTautology :=
  none_or_all_or_break_pinned_stranded_not_tautology
theorem PinnedGateBreakFiresOnlyOnStrandedLeg : Properties.PinnedGateBreakFiresOnlyOnStrandedLeg :=
  pinned_gate_break_fires_only_on_stranded_leg

end Contracts.Atomicity
