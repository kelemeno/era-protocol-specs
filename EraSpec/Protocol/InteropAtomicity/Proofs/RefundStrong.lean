import EraSpec.Protocol.InteropAtomicity.Properties.RefundStrong
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund

/-!
# Proofs: the refund side, strengthened

Proofs of `EraSpec.Protocol.InteropAtomicity.Properties.RefundStrong`.

Completeness rests on one observation: at the FIRST batch of the leg's chain that settled
after the deadline, the BEGIN tree is either the genesis `setup` (batch `0`) or the END
tree of an on-time batch.  A leg that missed its deadline is absent from it, so the IMT's
own non-inclusion completeness (`honest_absence_accepted`, the low-leaf proof at an
occupied index) gives a proof the gate accepts, and an honest proof carries no
`TreeRootBreak` (`honest_proof_no_break`).  On the END branch the honest batch-leaf path
of the root's last batch passes `_verifyLastBatchInRoot`: every right sibling on a
left-going step is past the end of its level, so it reads the level's zero.

The run-level results are one induction (`logged_mark_refunded`: the manager's lifecycle
is monotone) plus `refund_logged` from `Proofs/Refund.lean`.

The sealed witness (`sealed_absence_rejected`) is a computation: under `sealedNodeHash`
every node hash is `1` or `3`, so a walk of length two or more ends at `3`, and a walk of
length one reaches the root `1` only through the pair `(2, 4)`, i.e. through one of the
tree's two real leaves, neither of which is a low leaf of the value `1`.
-/

namespace Contracts.Refund

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager

/-! ## Completeness of the absence check -/

/-- `non_inclusion_complete` with the low leaf named: an occupied index `i` whose leaf and
honest siblings are accepted as an absence proof. -/
theorem honest_absence_accepted {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    (hV : Valid T) {height : ℕ} (hcap : T.leafCount ≤ 2 ^ height)
    {v : UInt256} (hv : v ≠ 0) (habs : v ∉ keys (toAbs T)) :
    ∃ i, i < T.leafCount ∧ NonInclusionAccepted h hl (root h z0 hl T height) v (T.leaf i) i
      (honestSibs h z0 (leafHashes hl T) i) height := by
  obtain ⟨_, _, hnc, hwp⟩ := hV.absSound
  have hbelow : ∃ X ∈ toAbs T, X.key < v :=
    ⟨⟨(T.leaf 0).value, (T.leaf 0).nextValue⟩,
     mem_toAbs.mpr ⟨0, hV.occupied, rfl, rfl⟩,
     by show (T.leaf 0).value < v; rw [hV.sentinel]; exact Fin.pos_of_ne_zero hv⟩
  obtain ⟨W, hW, hlow, hwin⟩ := gap_witness_exists hnc hwp hbelow habs
  obtain ⟨i, hi, hval, hnext⟩ := mem_toAbs.mp hW
  refine ⟨i, hi, hv, by rw [hval]; exact hlow, by rw [hnext]; exact hwin,
    ⟨lt_of_lt_of_le hi hcap, ?_⟩⟩
  have := honest_walk_root h z0 (leafHashes hl T) height i (lt_of_lt_of_le hi hcap)
  rw [leafHashes_getD hi] at this
  exact this

lemma beginTree_valid {S : System} (hS : Wf S) (c : Chain) : ∀ N, Valid (beginTree S c N)
  | 0 => setup_valid
  | n + 1 => valid_batch hS c n

lemma beginTree_capacity {S : System} (hS : Wf S) (c : Chain) :
    ∀ N, (beginTree S c N).leafCount ≤ 2 ^ beginHeight S c N
  | 0 => by simp [beginTree, beginHeight, setup]
  | n + 1 => hS.capacity c n

/-- The first batch of a chain that settled after `D`, when one exists. -/
lemma exists_first_late {S : System} {c : Chain} {D : ℕ} (hlate : ∃ N, D < S.time c N) :
    ∃ N, D < S.time c N ∧ ∀ M < N, S.time c M ≤ D := by
  classical
  exact ⟨Nat.find hlate, Nat.find_spec hlate, fun M hM => not_lt.mp (Nat.find_min hlate hM)⟩

/-- A leg that missed its deadline is absent from the BEGIN tree of the first late batch:
that tree is `setup` or the END tree of an on-time batch. -/
lemma missed_absent_begin {cv : CommitValue} {S : System} {F : Flow} {leg : FlowLeg}
    (hmiss : LegMissedDeadline cv S F leg) (hv : legValue cv F leg ≠ 0) {N : ℕ}
    (hfirst : ∀ M < N, S.time leg.chain M ≤ F.deadline) :
    legValue cv F leg ∉ keys (toAbs (beginTree S leg.chain N)) := by
  cases N with
  | zero => exact not_mem_setup (Fin.pos_of_ne_zero hv)
  | succ M => exact hmiss M (hfirst M (Nat.lt_succ_self M))

/-- **THE HONEST PROOF AT THE FIRST LATE BATCH PASSES, WITH NO BREAK.** -/
theorem honest_begin_refundable {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} (hS : Wf S) {F : Flow} {leg : FlowLeg} (hv : legValue cv F leg ≠ 0)
    (hmiss : LegMissedDeadline cv S F leg) {N : ℕ} (hlate : F.deadline < S.time leg.chain N)
    (hfirst : ∀ M < N, S.time leg.chain M ≤ F.deadline) :
    ∃ i, i < (beginTree S leg.chain N).leafCount
      ∧ AbsenceAccepted h z0 hl (beginTree S leg.chain N) (beginHeight S leg.chain N)
          (legValue cv F leg) (honestBeginProof h z0 hl S leg.chain N i)
      ∧ LegRefundableBy h z0 hl cv S F leg N (honestBeginProof h z0 hl S leg.chain N i)
      ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N
          (honestBeginProof h z0 hl S leg.chain N i) := by
  obtain ⟨i, hi, hacc⟩ := honest_absence_accepted (h := h) (z0 := z0) (hl := hl)
    (beginTree_valid hS leg.chain N) (beginTree_capacity hS leg.chain N) hv
    (missed_absent_begin hmiss hv hfirst)
  refine ⟨i, hi, hacc, Or.inl ⟨hlate, hacc⟩, ?_⟩
  rintro (⟨_, hb⟩ | ⟨hon, _⟩)
  · exact honest_proof_no_break h z0 hl _ _ i hi hb
  · exact absurd hlate (not_lt.mpr hon)

/-! ## 1. Completeness of the timeout gate -/

theorem refundable_iff_missed_deadline {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {F : Flow} {leg : FlowLeg}
    (hv : legValue cv F leg ≠ 0) :
    ((∃ N, F.deadline < S.time leg.chain N) ∧ LegMissedDeadline cv S F leg)
      ↔ ∃ (N : ℕ) (p : ImtProof), LegRefundableBy h z0 hl cv S F leg N p
          ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p := by
  constructor
  · rintro ⟨hlate, hmiss⟩
    obtain ⟨N, hN, hfirst⟩ := exists_first_late hlate
    obtain ⟨i, _, _, hr, hnb⟩ :=
      honest_begin_refundable (h := h) (z0 := z0) (hl := hl) hS hv hmiss hN hfirst
    exact ⟨N, _, hr, hnb⟩
  · rintro ⟨N, p, hr, hnb⟩
    refine ⟨?_, fun n hon hmem => ?_⟩
    · rcases hr with ⟨hlate, _⟩ | ⟨⟨_, hlast⟩, _⟩
      · exact ⟨N, hlate⟩
      · exact ⟨N + 1, hlast (N + 1) (Nat.lt_succ_self N)⟩
    · rcases member_not_refundable_or_break hS hon hmem N p with hn | hb
      · exact hn hr
      · exact hnb hb

theorem missed_deadline_refundable_by_honest_proof {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A)
    {F : Flow} {leg : FlowLeg} (hv : legValue cv F leg ≠ 0) (hmiss : LegMissedDeadline cv S F leg)
    {N : ℕ} (hlate : F.deadline < S.time leg.chain N)
    (hfirst : ∀ M < N, S.time leg.chain M ≤ F.deadline) :
    ∃ i, i < (beginTree S leg.chain N).leafCount
      ∧ LegRefundableBy h z0 hl cv S F leg N (honestBeginProof h z0 hl S leg.chain N i)
      ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N (honestBeginProof h z0 hl S leg.chain N i)
      ∧ (N = 0 ∨ A leg.chain (N - 1) (honestBeginProof h z0 hl S leg.chain N i)) := by
  obtain ⟨i, hi, _, hr, hnb⟩ :=
    honest_begin_refundable (h := h) (z0 := z0) (hl := hl) hS hv hmiss hlate hfirst
  refine ⟨i, hi, hr, hnb, ?_⟩
  cases N with
  | zero => exact Or.inl rfl
  | succ M => exact Or.inr (hDA leg.chain M i hi)

theorem accepted_gate_iff_missed_deadline {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {ze : UInt256} {R : SlRoot}
    (B : RootBacking h ze R) (hagg : Aggregates S R) {F : Flow} {leg : FlowLeg}
    (hR : F.deadline < R.created) (hv : legValue cv F leg ≠ 0) :
    LegMissedDeadline cv S F leg
      ↔ ∃ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
          LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x
          ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
          ∧ ¬ (EndBranchAccepted B S leg.chain F.deadline N sibs x
              ∧ (PinnedBreak h ze (B.leaves leg.chain) N
                ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
  constructor
  · intro hmiss
    have hlate : ∃ N, F.deadline < S.time leg.chain N := by
      refine ⟨R.upTo leg.chain + 1, ?_⟩
      by_contra hcon
      push Not at hcon
      have := hagg leg.chain _ (le_trans hcon (le_of_lt hR))
      omega
    obtain ⟨N, hN, hfirst⟩ := exists_first_late hlate
    obtain ⟨i, _, hacc, _, hnb⟩ :=
      honest_begin_refundable (h := h) (z0 := z0) (hl := hl) hS hv hmiss hN hfirst
    refine ⟨N, _, fun _ => 0, 0, Or.inl ⟨⟨hR, hN⟩, hacc⟩, hnb, ?_⟩
    rintro ⟨he, _⟩
    exact absurd hN (not_lt.mpr he.onTime)
  · rintro ⟨N, p, sibs, x, ha, hnb, hne⟩
    rcases accepted_timeout_means_missed_deadline_or_break hS hagg ha with hm | hb | hrest
    · exact hm
    · exact absurd hb hnb
    · exact absurd hrest hne

/-- The honest path of the LAST leaf of a list reads the level's zero wherever it goes
left: the right neighbour is past the end of the level. -/
lemma honest_last_zero_right {h : Hash} {ze : UInt256} {L : List UInt256} {j : ℕ}
    (hlen : L.length = j + 1) (l : ℕ) (hev : (j / 2 ^ l) % 2 = 0) :
    honestSibs h ze L j l = zeros h ze l := by
  have hne : L.length ≠ 0 := by omega
  have hw := levels_length h ze L hne l
  have hidx : sibIdx (j / 2 ^ l) = j / 2 ^ l + 1 := by simp [sibIdx, hev]
  simp only [honestSibs, hidx]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [hw, hlen, Nat.add_sub_cancel])]
  rfl

theorem end_branch_accepts_honest_proofs {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {ze : UInt256} {R : SlRoot}
    (B : RootBacking h ze R) {F : Flow} {leg : FlowLeg} (hR : F.deadline < R.created)
    (hon : S.time leg.chain (R.upTo leg.chain) ≤ F.deadline) (hv : legValue cv F leg ≠ 0)
    (habs : legValue cv F leg ∉ keys (toAbs (S.tree leg.chain (R.upTo leg.chain)))) :
    ∃ i, i < (S.tree leg.chain (R.upTo leg.chain)).leafCount
      ∧ LegRefundableAcceptedBy h z0 hl cv S B F leg (R.upTo leg.chain)
          (honestProof h z0 hl S leg.chain (R.upTo leg.chain) i)
          (honestSibs h ze (B.leaves leg.chain) (R.upTo leg.chain))
          ((B.leaves leg.chain).getD (R.upTo leg.chain) ze)
      ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain (R.upTo leg.chain)
          (honestProof h z0 hl S leg.chain (R.upTo leg.chain) i)
      ∧ ¬ PinnedBreak h ze (B.leaves leg.chain) (R.upTo leg.chain)
      ∧ ¬ PathCollision h ze (B.leaves leg.chain)
          (honestSibs h ze (B.leaves leg.chain) (R.upTo leg.chain)) 0 (B.height leg.chain)
          (R.upTo leg.chain) ((B.leaves leg.chain).getD (R.upTo leg.chain) ze) := by
  obtain ⟨i, hi, hacc⟩ := honest_absence_accepted (h := h) (z0 := z0) (hl := hl)
    (valid_batch hS leg.chain (R.upTo leg.chain)) (hS.capacity leg.chain (R.upTo leg.chain)) hv habs
  have hlen := B.upToLast leg.chain
  have hj : R.upTo leg.chain < 2 ^ B.height leg.chain :=
    lt_of_lt_of_le (by omega) (B.capacity leg.chain)
  have hlast : LastBatchAccepted B leg.chain (R.upTo leg.chain)
      (honestSibs h ze (B.leaves leg.chain) (R.upTo leg.chain))
      ((B.leaves leg.chain).getD (R.upTo leg.chain) ze) :=
    ⟨by omega, honest_walk_root h ze (B.leaves leg.chain) (B.height leg.chain) _ hj,
      fun l _ hev => honest_last_zero_right hlen l hev⟩
  refine ⟨i, hi, Or.inr ⟨⟨hR, hon, hlast⟩, hacc⟩, ?_,
    no_pinned_break_at_end h ze _ _ (by omega), honest_walk_no_collision h ze _ _ _⟩
  rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
  · exact absurd hlate (not_lt.mpr hon)
  · exact honestProof_no_break h z0 hl S leg.chain _ i hi hb

theorem stranded_flow_committed_leg_refundable {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {F : Flow}
    (hchk : FlowIdChecked fh F) {m : FlowLeg} (hm : m ∈ F.legs) (hv : legValue cv F m ≠ 0)
    (hlate : ∃ N, F.deadline < S.time m.chain N) (hmiss : LegMissedDeadline cv S F m)
    {Ms : Managers} {log : List AuthCall}
    (hrun : ReachLog h z0 hl cv fh S emptyManagers Ms log) {leg : FlowLeg} (hleg : leg ∈ F.legs)
    (hcom : stateOf Ms (obligationOf F leg) = .Committed) :
    ∃ (a : AuthCall) (Ms₁ Ms₂ : Managers),
      a.flow = F ∧ a.leg = leg ∧ a.missing = m ∧ a.Verified h z0 hl cv fh S
      ∧ ¬ AbsenceBreak h z0 hl S F.deadline m.chain a.batch a.proof
      ∧ ReachLog h z0 hl cv fh S emptyManagers Ms₁ (a :: log)
      ∧ stateOf Ms₁ (obligationOf F leg) = .Revertable
      ∧ ReachLog h z0 hl cv fh S emptyManagers Ms₂ (a :: log)
      ∧ stateOf Ms₂ (obligationOf F leg) = .Reverted
      ∧ ∀ o, o ≠ obligationOf F leg → stateOf Ms₂ o = stateOf Ms o := by
  obtain ⟨N, p, hr, hnb⟩ :=
    (refundable_iff_missed_deadline (h := h) (z0 := z0) (hl := hl) hS hv).mp ⟨hlate, hmiss⟩
  have hver : AuthCall.Verified h z0 hl cv fh S ⟨F, leg, m, N, p⟩ := ⟨hchk, hleg, hm, hr⟩
  have r1 := ReachLog.authorize ⟨F, leg, m, N, p⟩ hrun hver hcom
  have hs1 : stateOf (setAt Ms leg.chain ((Ms leg.chain).set F.flowId leg.bundleHash .Revertable))
      (obligationOf F leg) = .Revertable :=
    stateOf_setAt_self Ms leg.chain F.flowId leg.bundleHash .Revertable
  have r2 := ReachLog.claim (c := leg.chain) (f := F.flowId) (b := leg.bundleHash) r1 hs1
  refine ⟨⟨F, leg, m, N, p⟩, _, _, rfl, rfl, rfl, hver, hnb, r1, hs1, r2,
    stateOf_setAt_self _ leg.chain F.flowId leg.bundleHash .Reverted, ?_⟩
  intro o ho
  rw [stateOf_setAt_other ho, stateOf_setAt_other ho]

/-! ## 2. Cross-flow refunds, at run level -/

/-- **A LOGGED MARK STAYS PAST `Committed`.**  The converse of `refund_logged`. -/
theorem logged_mark_refunded {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms : Managers} {log : List AuthCall}
    (hr : ReachLog h z0 hl cv fh S emptyManagers Ms log) :
    ∀ (o : Obligation), (∃ a ∈ log, obligationOf a.flow a.leg = o) → Refunded Ms o := by
  induction hr with
  | refl =>
    rintro o ⟨a, ha, _⟩
    simp at ha
  | @append Ns log c f b _ hg ih =>
    rintro o hex
    have hR := ih o hex
    by_cases heq : o = ⟨f, b, c⟩
    · exfalso
      subst heq
      simp only [Refunded, stateOf] at hR
      rw [show (Ns c).legState f b = LegState.Unset from hg] at hR
      simp [rank] at hR
    · simpa only [Refunded, stateOf_setAt_other heq] using hR
  | @authorize Ns log a' _ _ _ ih =>
    rintro o ⟨a, ha, hobl⟩
    by_cases heq : o = obligationOf a'.flow a'.leg
    · subst heq
      simp only [Refunded, obligationOf_eq, stateOf_setAt_self]
      simp [rank]
    · rw [obligationOf_eq] at heq
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact absurd hobl.symm heq
      · simpa only [Refunded, stateOf_setAt_other heq] using ih o ⟨a, ha', hobl⟩
  | @claim Ns log c f b _ _ ih =>
    rintro o hex
    by_cases heq : o = ⟨f, b, c⟩
    · subst heq
      simp only [Refunded, stateOf_setAt_self]
      simp [rank]
    · simpa only [Refunded, stateOf_setAt_other heq] using ih o hex

theorem refunded_iff_logged_mark {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms : Managers} {log : List AuthCall}
    (hr : ReachLog h z0 hl cv fh S emptyManagers Ms log) (o : Obligation) :
    Refunded Ms o ↔ ∃ a ∈ log, obligationOf a.flow a.leg = o := by
  constructor
  · intro hrf
    obtain ⟨a, ha, _, hobl⟩ := refund_logged hr o hrf
    exact ⟨a, ha, hobl⟩
  · exact logged_mark_refunded hr o

theorem cross_flow_refund_yields_logged_pinned_clash {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} {F : Flow} {leg : FlowLeg}
    (hchk : FlowIdChecked fh F) {Ms : Managers} {log : List AuthCall}
    (hr : ReachLog h z0 hl cv fh S emptyManagers Ms log) (hrf : Refunded Ms (obligationOf F leg))
    (hnot : ∀ a ∈ log, obligationOf a.flow a.leg = obligationOf F leg → a.flow ≠ F) :
    ∃ a ∈ log, a.Verified h z0 hl cv fh S ∧ obligationOf a.flow a.leg = obligationOf F leg
      ∧ FlowIdClash fh F a.flow := by
  obtain ⟨a, ha, hv, hobl⟩ := refund_logged hr _ hrf
  have hid : F.flowId = a.flow.flowId := (congrArg Obligation.flowId hobl).symm
  rcases flowId_check_pins_legList_or_collision hchk hv.1 hid with heq | hcl
  · exact absurd heq.symm (hnot a ha hobl)
  · exact ⟨a, ha, hv, hobl, hcl⟩

/-! ## 3. The executed obligation -/

theorem refund_break_implies_refunded {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} {Ms : Managers} {log : List AuthCall}
    (hr : ReachLog h z0 hl cv fh S emptyManagers Ms log) {F : Flow} {ev : GateEvidence}
    {o : Obligation} (hb : RefundBreak h z0 hl fh S F ev o log) : Refunded Ms o := by
  apply logged_mark_refunded hr
  cases hb with
  | flowIdClash a ha hobl _ => exact ⟨a, ha, hobl⟩
  | inclusion a ha hobl _ _ => exact ⟨a, ha, hobl⟩
  | absence a ha hobl _ _ => exact ⟨a, ha, hobl⟩

/-! ## Anti-vacuity witnesses -/

lemma mixed_leg_one_missed :
    LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩ := by
  intro n _ hmem
  have hne : (1 : Chain) ≠ 0 := by decide
  change (2 : UInt256) ∈ keys (toAbs ((mixedSystem 1).tree 1 n)) at hmem
  rw [mixedSystem_tree_other hne] at hmem
  exact not_mem_setup (by decide) hmem

lemma mixed_leg_zero_not_missed :
    ¬ LegMissedDeadline (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨0, 1⟩ := by
  intro hmiss
  apply hmiss 0 (by simp [mixedFlow])
  change (1 : UInt256) ∈ keys (toAbs ((mixedSystem 1).tree 0 0))
  rw [mixedSystem_tree_zero]
  exact mem_insertSetup (by decide)

theorem refundable_iff_missed_deadline_witness : Properties.RefundableIffMissedDeadlineWitness :=
  ⟨mixedSystem_wf (by decide), by decide, ⟨1, by simp [mixedFlow]⟩, mixed_leg_one_missed,
    by decide, mixed_leg_zero_not_missed⟩

theorem missed_deadline_refundable_by_honest_proof_witness :
    Properties.MissedDeadlineRefundableByHonestProofWitness := fun h z0 hl =>
  ⟨mixedSystem_wf (by decide), honestAccess_dataAvailable h z0 hl _, by decide,
    mixed_leg_one_missed, by simp [mixedFlow], fun M hM => by simp [mixedFlow]; omega⟩

theorem accepted_gate_iff_missed_deadline_witness :
    Properties.AcceptedGateIffMissedDeadlineWitness := fun h ze =>
  ⟨⟨trivialBacking h ze⟩, mixedSystem_wf (by decide), timeOneRoot_aggregates_mixed 1,
    by simp [mixedFlow, timeOneRoot], by decide, mixed_leg_one_missed, by decide,
    mixed_leg_zero_not_missed⟩

/-- A backing for `demoRoot` under any node hash and padding: two batch leaves, height 1. -/
def demoRootAnyBacking (h : Hash) (ze : UInt256) : RootBacking h ze demoRoot where
  leaves := fun _ => [0, 0]
  height := fun _ => 1
  upToLast := fun _ => rfl
  capacity := fun _ => by norm_num

theorem end_branch_accepts_honest_proofs_witness :
    Properties.EndBranchAcceptsHonestProofsWitness := fun h ze =>
  ⟨⟨demoRootAnyBacking h ze⟩, demoSystem_wf, by decide, by decide, by decide,
    not_mem_setup (by decide)⟩

theorem stranded_flow_committed_leg_refundable_witness :
    Properties.StrandedFlowCommittedLegRefundableWitness := fun h z0 hl =>
  ⟨setAt emptyManagers 0 ((emptyManagers 0).set 0 1 .Committed), [],
    mixedSystem_wf (by decide), (honest_flowHash_no_clash _).1, by simp [mixedFlow], by decide,
    ⟨1, by simp [mixedFlow]⟩, mixed_leg_one_missed,
    ReachLog.append (c := 0) (f := 0) (b := 1) ReachLog.refl rfl, by simp [mixedFlow],
    stateOf_setAt_self _ 0 0 1 .Committed, mixed_leg_zero_not_missed⟩

theorem refunded_iff_logged_mark_witness : Properties.RefundedIffLoggedMarkWitness := by
  intro h z0 hl
  have hg : AppendGuard (twoFlowMs 0) 0 1 := by
    show (twoFlowMs 0).legState 0 1 = .Unset
    simp [twoFlowMs, twoFlowM1, setAt, emptyManagers, Contracts.AtomicFlowManager.empty]
  refine ⟨_, _, ⟨1, 2, 1⟩, ⟨0, 1, 0⟩, ReachLog.append (c := 0) (twoFlow_run h z0 hl) hg, ?_,
    stateOf_setAt_self _ 0 0 1 .Committed⟩
  have hne : (⟨1, 2, 1⟩ : Obligation) ≠ ⟨0, 1, 0⟩ := by decide
  simp only [Refunded]
  rw [stateOf_setAt_other hne]
  show 2 ≤ rank (stateOf (setAt twoFlowM1 1 ((twoFlowM1 1).set 1 2 .Revertable)) ⟨1, 2, 1⟩)
  rw [stateOf_setAt_self]
  simp [rank]

/-- The absence proof of any nonzero value against chain `1` of `mixedSystem`, which stays
`setup`: the sentinel at index `0`. -/
def setupProof (h : Hash) (z0 : UInt256) (hl : LeafHash) : ImtProof :=
  ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩

/-- Chain `1` of `mixedSystem 1` never commits, so the leg `⟨1, 2⟩` of any flow passes the
BEGIN branch at any batch after the deadline, under the constant commit value `1`. -/
lemma chainOne_refundable (h : Hash) (z0 : UInt256) (hl : LeafHash) (G : Flow) (N : ℕ)
    (hN : G.deadline < N) :
    LegRefundableBy h z0 hl (fun _ _ => 1) (mixedSystem 1) G ⟨1, 2⟩ N (setupProof h z0 hl) := by
  have hne : (1 : Chain) ≠ 0 := by decide
  refine Or.inl ⟨by simpa using hN, ?_⟩
  cases N with
  | zero => exact absurd hN (Nat.not_lt_zero _)
  | succ M =>
    show AbsenceAccepted h z0 hl ((mixedSystem 1).tree 1 M) ((mixedSystem 1).height 1 M) 1 _
    rw [mixedSystem_tree_other hne, mixedSystem_height_other hne]
    exact setup_absence_accepted h z0 hl (by decide)

theorem cross_flow_refund_yields_logged_pinned_clash_witness :
    Properties.CrossFlowRefundYieldsLoggedPinnedClashWitness := by
  intro h z0 hl
  let F : Flow := ⟨0, [⟨1, 2⟩], 0⟩
  let G : Flow := ⟨0, [⟨1, 2⟩], 5⟩
  let M1 : Managers := setAt emptyManagers 1 ((emptyManagers 1).set 0 2 .Committed)
  let a : AuthCall := ⟨G, ⟨1, 2⟩, ⟨1, 2⟩, 6, setupProof h z0 hl⟩
  have hchkF : FlowIdChecked lengthFlowHash F := by simp [FlowIdChecked, lengthFlowHash, F]
  have hchkG : FlowIdChecked lengthFlowHash G := by simp [FlowIdChecked, lengthFlowHash, G]
  have hmemG : (⟨1, 2⟩ : FlowLeg) ∈ G.legs := List.mem_singleton_self _
  have r1 : ReachLog h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) emptyManagers M1 [] :=
    ReachLog.append (c := 1) (f := 0) (b := 2) ReachLog.refl rfl
  have hg : AuthorizeGuard (M1 a.leg.chain) a.flow.flowId a.leg.bundleHash :=
    stateOf_setAt_self emptyManagers 1 0 2 .Committed
  have r2 := ReachLog.authorize a r1
    ⟨hchkG, hmemG, hmemG, chainOne_refundable h z0 hl G 6 (by simp [G])⟩ hg
  refine ⟨F, ⟨1, 2⟩, _, [a], hchkF, List.mem_singleton_self _, r2, List.cons_ne_nil _ _, ?_, ?_⟩
  · simp only [Refunded]
    show 2 ≤ rank (stateOf (setAt M1 1 ((M1 1).set 0 2 .Revertable)) ⟨0, 2, 1⟩)
    rw [stateOf_setAt_self]
    simp [rank]
  · intro c hc _ heq
    rw [List.mem_singleton] at hc
    subst hc
    exact absurd (congrArg Flow.deadline heq) (by simp [a, G, F])

theorem refund_break_implies_refunded_witness : Properties.RefundBreakImpliesRefundedWitness := by
  intro h hl
  obtain ⟨cv, fh, F, ev, leg, Ms, log, _, _, hr, _, hb, _⟩ :=
    padding_refund_of_executed_obligation_locates_absence_break h hl 1 2 (by decide) (by decide)
  exact ⟨cv, fh, Ms, log, F, ev, _, hr, hb⟩

/-! ### The executed obligation, appended and live -/

/-- A one-leg flow on chain `1` claiming the id `0` that `subsetFlow 0 1` also claims. -/
def clashFlow : Flow := ⟨0, [⟨1, 2⟩], 0⟩

/-- `authorizeRefund` for `clashFlow`'s leg, on the absence of its commit value from chain
`1` at batch `1`. -/
def clashCall (h : Hash) (z0 : UInt256) (hl : LeafHash) : AuthCall :=
  ⟨clashFlow, ⟨1, 2⟩, ⟨1, 2⟩, 1, setupProof h z0 hl⟩

/-- Append the executed obligation `(0, 1)` on chain `0`. -/
def liveM1 : Managers := setAt emptyManagers 0 ((emptyManagers 0).set 0 1 .Committed)

/-- …then `clashFlow`'s obligation `(0, 2)` on chain `1`. -/
def liveM2 : Managers := setAt liveM1 1 ((liveM1 1).set 0 2 .Committed)

/-- …then authorize `clashFlow`'s refund. -/
def liveMs : Managers := setAt liveM2 1 ((liveM2 1).set 0 2 .Revertable)

theorem live_run (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ReachLog h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) emptyManagers liveMs
      [clashCall h z0 hl] := by
  have r1 : ReachLog h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) emptyManagers
      liveM1 [] := ReachLog.append (c := 0) (f := 0) (b := 1) ReachLog.refl rfl
  have hg1 : AppendGuard (liveM1 1) 0 2 := by
    show (liveM1 1).legState 0 2 = .Unset
    simp [liveM1, setAt, emptyManagers, Contracts.AtomicFlowManager.empty]
  have r2 := ReachLog.append (c := 1) r1 hg1
  have hchk : FlowIdChecked lengthFlowHash clashFlow := by
    simp [FlowIdChecked, lengthFlowHash, clashFlow]
  have hmem : (⟨1, 2⟩ : FlowLeg) ∈ clashFlow.legs := List.mem_singleton_self _
  have hg2 : AuthorizeGuard (liveM2 1) 0 2 := stateOf_setAt_self liveM1 1 0 2 .Committed
  exact ReachLog.authorize (clashCall h z0 hl) r2
    ⟨hchk, hmem, hmem, chainOne_refundable h z0 hl clashFlow 1 (by simp [clashFlow])⟩ hg2

lemma liveMs_executed : stateOf liveMs ⟨0, 1, 0⟩ = .Committed := by
  have hne : (⟨0, 1, 0⟩ : Obligation) ≠ ⟨0, 2, 1⟩ := by decide
  show stateOf (setAt liveM2 1 ((liveM2 1).set 0 2 .Revertable)) ⟨0, 1, 0⟩ = .Committed
  rw [stateOf_setAt_other hne]
  show stateOf (setAt liveM1 1 ((liveM1 1).set 0 2 .Committed)) ⟨0, 1, 0⟩ = .Committed
  rw [stateOf_setAt_other hne]
  exact stateOf_setAt_self _ 0 0 1 .Committed

lemma subset_clash : FlowIdClash lengthFlowHash (subsetFlow 0 1) clashFlow := by
  refine ⟨by simp [subsetFlow, clashFlow], by simp [lengthFlowHash, subsetFlow, clashFlow]⟩

/-- Everything `ExecutedObligationNeverRefundedOrBreakAppendedWitness` claims, for one hash. -/
theorem live_run_facts (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    Wf (mixedSystem 1)
      ∧ ExecutedViaBy h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) (subsetFlow 0 1)
          (fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1)) ⟨0, 1⟩
      ∧ ¬ GateBreak h z0 hl (mixedSystem 1) (subsetFlow 0 1)
          (fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1))
      ∧ ReachLog h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) emptyManagers liveMs
          [clashCall h z0 hl]
      ∧ stateOf liveMs (obligationOf (subsetFlow 0 1) ⟨0, 1⟩) = .Committed
      ∧ (∃ a ∈ [clashCall h z0 hl], a.flow.flowId = (subsetFlow 0 1).flowId
          ∧ FlowIdClash lengthFlowHash (subsetFlow 0 1) a.flow)
      ∧ ¬ RefundBreak h z0 hl lengthFlowHash (mixedSystem 1) (subsetFlow 0 1)
          (fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1))
          (obligationOf (subsetFlow 0 1) ⟨0, 1⟩) [clashCall h z0 hl]
      ∧ ¬ Refunded liveMs (obligationOf (subsetFlow 0 1) ⟨0, 1⟩) := by
  obtain ⟨hex, hnb⟩ := subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset
  have hneq : obligationOf (clashCall h z0 hl).flow (clashCall h z0 hl).leg
      ≠ obligationOf (subsetFlow 0 1) ⟨0, 1⟩ := by
    show (⟨0, 2, 1⟩ : Obligation) ≠ ⟨0, 1, 0⟩
    decide
  refine ⟨mixedSystem_wf (by decide), hex, ?_, live_run h z0 hl, liveMs_executed,
    ⟨clashCall h z0 hl, List.mem_singleton_self _, rfl, subset_clash⟩, ?_, ?_⟩
  · rintro ⟨l, hl', hb⟩
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    exact hnb hb
  · intro hb
    cases hb with
    | flowIdClash a ha hobl _ =>
      rw [List.mem_singleton] at ha; subst ha; exact hneq hobl
    | inclusion a ha hobl _ _ =>
      rw [List.mem_singleton] at ha; subst ha; exact hneq hobl
    | absence a ha hobl _ _ =>
      rw [List.mem_singleton] at ha; subst ha; exact hneq hobl
  · show ¬ 2 ≤ rank (stateOf liveMs ⟨0, 1, 0⟩)
    rw [liveMs_executed]
    simp [rank]

theorem executed_obligation_never_refunded_or_break_appended_witness :
    Properties.ExecutedObligationNeverRefundedOrBreakAppendedWitness := fun h z0 hl =>
  ⟨_, _, _, _, _, _, _, _, live_run_facts h z0 hl⟩

/-! ### The sealed hash pair -/

lemma sealedNodeHash_eq_one {a b : UInt256} (he : sealedNodeHash a b = 1) : a = 2 ∧ b = 4 := by
  unfold sealedNodeHash at he
  split_ifs at he with hab
  · exact hab
  · exact absurd he (by decide)

lemma sealedNodeHash_cases (a b : UInt256) : sealedNodeHash a b = 1 ∨ sealedNodeHash a b = 3 := by
  unfold sealedNodeHash
  split_ifs <;> simp

/-- One step of the walk on a node-hash output (`1` or `3`) gives `3`: the pair `(2, 4)`
needs the accumulator to be `2` or `4`. -/
lemma sealed_step (sibs : ℕ → UInt256) (lvl idx : ℕ) {x : UInt256} (hx : x = 1 ∨ x = 3) :
    (if idx % 2 = 1 then sealedNodeHash (sibs lvl) x else sealedNodeHash x (sibs lvl)) = 3 := by
  split_ifs
  · rcases sealedNodeHash_cases (sibs lvl) x with he | he
    · exact absurd (sealedNodeHash_eq_one he).2 (by rcases hx with rfl | rfl <;> decide)
    · exact he
  · rcases sealedNodeHash_cases x (sibs lvl) with he | he
    · exact absurd (sealedNodeHash_eq_one he).1 (by rcases hx with rfl | rfl <;> decide)
    · exact he

/-- A nonempty walk started on a node-hash output ends at `3`. -/
lemma sealed_walk_three (sibs : ℕ → UInt256) :
    ∀ (k lvl idx : ℕ) (x : UInt256), (x = 1 ∨ x = 3) →
      walkPure sealedNodeHash sibs lvl (k + 1) idx x = 3 := by
  intro k
  induction k with
  | zero =>
    intro lvl idx x hx
    exact sealed_step sibs lvl idx hx
  | succ k ih =>
    intro lvl idx x hx
    exact ih (lvl + 1) (idx / 2) _ (Or.inr (sealed_step sibs lvl idx hx))

lemma sealed_root (z0 : UInt256) :
    root sealedNodeHash z0 sealedLeafHash (insert setup 1 0) 1 = 1 := by
  have h0 : sealedLeafHash ((insert setup 1 0).leaf 0) = 2 := by
    simp [sealedLeafHash, Contracts.InteropCommitmentTree.insert, setup]
  have h1 : sealedLeafHash ((insert setup 1 0).leaf 1) = 4 := by
    simp [sealedLeafHash, Contracts.InteropCommitmentTree.insert, setup]
  have hL : leafHashes sealedLeafHash (insert setup 1 0) = [2, 4] := by
    show List.map (fun i => sealedLeafHash ((insert setup 1 0).leaf i)) (List.range 2) = [2, 4]
    simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
      List.nil_append, List.cons_append, h0, h1]
  rw [root, hL]
  simp [rootOf, levels, levelUp, sealedNodeHash]

/-- **NO ABSENCE PROOF OF `1` IS ACCEPTED AGAINST THE SEALED ONE-COMMIT TREE.** -/
theorem sealed_absence_rejected (z0 : UInt256) (p : ImtProof) :
    ¬ AbsenceAccepted sealedNodeHash z0 sealedLeafHash (insert setup 1 0) 1 1 p := by
  rintro ⟨_, hlow, hwin, ⟨_, hwalk⟩⟩
  rw [sealed_root] at hwalk
  obtain ⟨ℓ, idx, sibs, k⟩ := p
  simp only at hlow hwin hwalk
  cases k with
  | zero =>
    have : sealedLeafHash ℓ = 1 := hwalk
    revert this
    unfold sealedLeafHash
    split_ifs <;> decide
  | succ k =>
    have hy : walkPure sealedNodeHash sibs 1 k (idx / 2)
        (if idx % 2 = 1 then sealedNodeHash (sibs 0) (sealedLeafHash ℓ)
          else sealedNodeHash (sealedLeafHash ℓ) (sibs 0)) = 1 := hwalk
    have hstep : (if idx % 2 = 1 then sealedNodeHash (sibs 0) (sealedLeafHash ℓ)
          else sealedNodeHash (sealedLeafHash ℓ) (sibs 0)) = 1 := by
      cases k with
      | zero => exact hy
      | succ k =>
        rcases (by split_ifs <;> exact sealedNodeHash_cases _ _ :
          (if idx % 2 = 1 then sealedNodeHash (sibs 0) (sealedLeafHash ℓ)
            else sealedNodeHash (sealedLeafHash ℓ) (sibs 0)) = 1
          ∨ (if idx % 2 = 1 then sealedNodeHash (sibs 0) (sealedLeafHash ℓ)
            else sealedNodeHash (sealedLeafHash ℓ) (sibs 0)) = 3) with he | he
        · exact he
        · rw [sealed_walk_three sibs k 1 (idx / 2) _ (Or.inr he)] at hy
          exact absurd hy (by decide)
    split_ifs at hstep
    · have h4 := (sealedNodeHash_eq_one hstep).2
      revert h4 hlow
      unfold sealedLeafHash
      split_ifs with ha hb
      · intro _ h; exact absurd h (by decide)
      · subst hb; decide
      · intro _ h; exact absurd h (by decide)
    · have h2 := (sealedNodeHash_eq_one hstep).1
      revert h2 hwin
      unfold sealedLeafHash
      split_ifs with ha hb
      · subst ha; decide
      · intro _ h; exact absurd h (by decide)
      · intro _ h; exact absurd h (by decide)

/-- Under the sealed pair and the constant commit value `1`, no leg on chain `0` of
`mixedSystem 1` passes the timeout gate: every tree the gate can select there is
`insert setup 1 0` at height 1. -/
lemma sealed_no_refund_chain_zero (z0 : UInt256) (G : Flow) (l : FlowLeg) (hc : l.chain = 0)
    (N : ℕ) (p : ImtProof) :
    ¬ LegRefundableBy sealedNodeHash z0 sealedLeafHash (fun _ _ => 1) (mixedSystem 1) G l N p := by
  obtain ⟨c, b⟩ := l
  simp only at hc
  subst hc
  rintro (⟨hlate, hacc⟩ | ⟨_, hacc⟩)
  · cases N with
    | zero => exact absurd hlate (by simp)
    | succ M =>
      have : AbsenceAccepted sealedNodeHash z0 sealedLeafHash ((mixedSystem 1).tree 0 M)
          ((mixedSystem 1).height 0 M) 1 p := hacc
      rw [mixedSystem_tree_zero, mixedSystem_height_zero] at this
      exact sealed_absence_rejected z0 p this
  · have : AbsenceAccepted sealedNodeHash z0 sealedLeafHash ((mixedSystem 1).tree 0 N)
        ((mixedSystem 1).height 0 N) 1 p := hacc
    rw [mixedSystem_tree_zero, mixedSystem_height_zero] at this
    exact sealed_absence_rejected z0 p this

theorem executed_obligation_refund_blocked_only_by_timeout_gate :
    Properties.ExecutedObligationRefundBlockedOnlyByTimeoutGate := by
  obtain ⟨hS, hex, hnb, hr, hcom, hcl, hnrb, hnr⟩ := live_run_facts sealedNodeHash 0 sealedLeafHash
  refine ⟨sealedNodeHash, 0, sealedLeafHash, _, _, _, _, _, _, _, _, hS, hex, hnb, hr, hcom, hcl,
    fun N p => sealed_no_refund_chain_zero 0 _ ⟨0, 1⟩ rfl N p, ?_, hnrb, hnr⟩
  rintro a ⟨hchk, hleg, hmiss, href⟩ hobl
  have hid : a.flow.flowId = 0 := congrArg Obligation.flowId hobl
  have hc : a.leg.chain = 0 := congrArg Obligation.chain hobl
  have hlen : a.flow.legs.length = 1 := by
    unfold FlowIdChecked lengthFlowHash at hchk
    rw [hid] at hchk
    split_ifs at hchk with hl1
    · exact hl1
    · exact absurd hchk (by decide)
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  rw [hx, List.mem_singleton] at hleg hmiss
  exact sealed_no_refund_chain_zero 0 a.flow a.missing (by rw [hmiss, ← hleg, hc]) _ _ href

end Contracts.Refund

/-! ## The named theorems -/

namespace Contracts.Refund

theorem RefundableIffMissedDeadline : Properties.RefundableIffMissedDeadline :=
  fun _ _ _ _ _ hS _ _ hv => refundable_iff_missed_deadline hS hv
theorem RefundableIffMissedDeadlineWitness : Properties.RefundableIffMissedDeadlineWitness :=
  refundable_iff_missed_deadline_witness
theorem MissedDeadlineRefundableByHonestProof : Properties.MissedDeadlineRefundableByHonestProof :=
  fun _ _ _ _ _ hS _ hDA _ _ hv hmiss _ hlate hfirst =>
    missed_deadline_refundable_by_honest_proof hS hDA hv hmiss hlate hfirst
theorem MissedDeadlineRefundableByHonestProofWitness :
    Properties.MissedDeadlineRefundableByHonestProofWitness :=
  missed_deadline_refundable_by_honest_proof_witness
theorem AcceptedGateIffMissedDeadline : Properties.AcceptedGateIffMissedDeadline :=
  fun _ _ _ _ _ hS _ _ B hagg _ _ hR hv => accepted_gate_iff_missed_deadline hS B hagg hR hv
theorem AcceptedGateIffMissedDeadlineWitness : Properties.AcceptedGateIffMissedDeadlineWitness :=
  accepted_gate_iff_missed_deadline_witness
theorem EndBranchAcceptsHonestProofs : Properties.EndBranchAcceptsHonestProofs :=
  fun _ _ _ _ _ hS _ _ B _ _ hR hon hv habs => end_branch_accepts_honest_proofs hS B hR hon hv habs
theorem EndBranchAcceptsHonestProofsWitness : Properties.EndBranchAcceptsHonestProofsWitness :=
  end_branch_accepts_honest_proofs_witness
theorem StrandedFlowCommittedLegRefundable : Properties.StrandedFlowCommittedLegRefundable :=
  fun _ _ _ _ _ _ hS _ hchk _ hm hv hlate hmiss _ _ hrun _ hleg hcom =>
    stranded_flow_committed_leg_refundable hS hchk hm hv hlate hmiss hrun hleg hcom
theorem StrandedFlowCommittedLegRefundableWitness :
    Properties.StrandedFlowCommittedLegRefundableWitness :=
  stranded_flow_committed_leg_refundable_witness
theorem RefundedIffLoggedMark : Properties.RefundedIffLoggedMark :=
  fun _ _ _ _ _ _ _ _ hr o => refunded_iff_logged_mark hr o
theorem RefundedIffLoggedMarkWitness : Properties.RefundedIffLoggedMarkWitness :=
  refunded_iff_logged_mark_witness
theorem CrossFlowRefundYieldsLoggedPinnedClash :
    Properties.CrossFlowRefundYieldsLoggedPinnedClash :=
  fun _ _ _ _ _ _ _ _ hchk _ _ hr hrf hnot =>
    cross_flow_refund_yields_logged_pinned_clash hchk hr hrf hnot
theorem CrossFlowRefundYieldsLoggedPinnedClashWitness :
    Properties.CrossFlowRefundYieldsLoggedPinnedClashWitness :=
  cross_flow_refund_yields_logged_pinned_clash_witness
theorem RefundBreakImpliesRefunded : Properties.RefundBreakImpliesRefunded :=
  fun _ _ _ _ _ _ _ _ hr _ _ _ hb => refund_break_implies_refunded hr hb
theorem RefundBreakImpliesRefundedWitness : Properties.RefundBreakImpliesRefundedWitness :=
  refund_break_implies_refunded_witness
theorem ExecutedObligationNeverRefundedOrBreakAppendedWitness :
    Properties.ExecutedObligationNeverRefundedOrBreakAppendedWitness :=
  executed_obligation_never_refunded_or_break_appended_witness
theorem ExecutedObligationRefundBlockedOnlyByTimeoutGate :
    Properties.ExecutedObligationRefundBlockedOnlyByTimeoutGate :=
  executed_obligation_refund_blocked_only_by_timeout_gate

end Contracts.Refund
