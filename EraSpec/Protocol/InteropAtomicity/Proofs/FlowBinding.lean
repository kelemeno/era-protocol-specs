import EraSpec.Protocol.InteropAtomicity.Properties.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund

/-!
# Proofs: the flow-id check binds every flow the run presents

One induction (`logged_calls_verified`: every logged call passed its checks) and one
case split per result.  The split is `flowId_check_pins_legList_or_collision` on the
two logged flows:

* if they are the same flow, the existing no-hash-premise results about one executed
  flow finish the case: `none_or_all_or_break_pinned`,
  `executed_implies_all_finalizable_or_break` and
  `executed_excludes_any_refund_or_break`;
* otherwise the two logged preimages clash.
-/

namespace Contracts.FlowBinding

open MerkleSpec MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree
open Contracts.Atomicity Contracts.Timeout Contracts.Refund Contracts.AtomicFlowManager

/-! ## The logged run -/

/-- A verified call's flow passed `_checkFlowId`. -/
theorem CheckedCall.Verified.flowIdChecked {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} {c : CheckedCall}
    (hv : c.Verified h z0 hl cv fh S) : FlowIdChecked fh c.flow := by
  cases c with
  | execute e => exact hv.2.1
  | authorize a => exact hv.1

/-- **EVERY LOGGED CALL PASSED ITS CHECKS.** -/
theorem logged_calls_verified {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms Ns : Managers} {log : List CheckedCall}
    (hr : RunLog h z0 hl cv fh S Ms Ns log) :
    ∀ c ∈ log, c.Verified h z0 hl cv fh S := by
  induction hr with
  | refl => intro c hc; exact absurd hc List.not_mem_nil
  | append _ _ ih => exact ih
  | execute e _ hv ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hv
    · exact ih c hc
  | authorize a _ hv _ ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hv
    · exact ih c hc
  | claim _ _ ih => exact ih

/-- A logged execution is an execution through the deployed gate. -/
theorem logged_execution_executes {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms Ns : Managers} {log : List CheckedCall}
    (hr : RunLog h z0 hl cv fh S Ms Ns log) {e : ExecCall} (he : CheckedCall.execute e ∈ log) :
    ExecutedViaBy h z0 hl cv fh S e.flow e.evidence e.leg :=
  logged_calls_verified hr _ he

/-- A logged `authorizeRefund` call passed its checks. -/
theorem logged_authorize_verified {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms Ns : Managers} {log : List CheckedCall}
    (hr : RunLog h z0 hl cv fh S Ms Ns log) {a : AuthCall} (ha : CheckedCall.authorize a ∈ log) :
    a.Verified h z0 hl cv fh S :=
  logged_calls_verified hr _ ha

@[simp] theorem authCalls_nil : authCalls [] = [] := rfl

@[simp] theorem authCalls_execute (e : ExecCall) (log : List CheckedCall) :
    authCalls (CheckedCall.execute e :: log) = authCalls log := rfl

@[simp] theorem authCalls_authorize (a : AuthCall) (log : List CheckedCall) :
    authCalls (CheckedCall.authorize a :: log) = a :: authCalls log := rfl

theorem authCalls_map_authorize (alog : List AuthCall) :
    authCalls (alog.map CheckedCall.authorize) = alog := by
  induction alog with
  | nil => rfl
  | cons a t ih => rw [List.map_cons, authCalls_authorize, ih]

/-- **THE AUTHORIZE CALLS OF A `RunLog` ARE A `ReachLog`.** -/
theorem runLog_reachLog {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms Ns : Managers} {log : List CheckedCall}
    (hr : RunLog h z0 hl cv fh S Ms Ns log) : ReachLog h z0 hl cv fh S Ms Ns (authCalls log) := by
  induction hr with
  | refl => exact ReachLog.refl
  | append _ hg ih => exact ReachLog.append ih hg
  | execute e _ _ ih => rw [authCalls_execute]; exact ih
  | authorize a _ hv hg ih => rw [authCalls_authorize]; exact ReachLog.authorize a ih hv hg
  | claim _ hg ih => exact ReachLog.claim ih hg

/-- **A `ReachLog` IS A `RunLog` WITHOUT EXECUTIONS.** -/
theorem reachLog_runLog {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms Ns : Managers} {alog : List AuthCall}
    (hr : ReachLog h z0 hl cv fh S Ms Ns alog) :
    RunLog h z0 hl cv fh S Ms Ns (alog.map CheckedCall.authorize) := by
  induction hr with
  | refl => exact RunLog.refl
  | append _ hg ih => exact RunLog.append ih hg
  | authorize a _ hv hg ih => exact RunLog.authorize a ih hv hg
  | claim _ hg ih => exact RunLog.claim ih hg

/-! ## The real flow -/

/-- **PARTIAL ATOMICITY OVER THE REAL FLOW, OR A LOCATED BREAK, OR A LOGGED CLASH.** -/
theorem executed_implies_real_flow_finalizable_or_logged_clash {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {Ms Ns : Managers} {log : List CheckedCall}
    (hr : RunLog h z0 hl cv fh S Ms Ns log) {e : ExecCall} (he : CheckedCall.execute e ∈ log)
    {c : CheckedCall} (hc : c ∈ log) (hid : c.flow.flowId = e.flow.flowId) :
    FlowFinalizableBy h z0 hl cv S A c.flow
      ∨ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
      ∨ FlowIdClash fh e.flow c.flow := by
  have hex := logged_execution_executes hr he
  have hchk : FlowIdChecked fh c.flow := (logged_calls_verified hr c hc).flowIdChecked
  rcases flowId_check_pins_legList_or_collision hex.2.1 hchk hid.symm with heq | hcl
  · rw [← heq]
    rcases none_or_all_or_break_pinned (fh := fh) hS hDA e.flow e.evidence with hfin | hnex | hpin
    · exact Or.inl hfin
    · exact absurd hex (hnex e.leg)
    · exact Or.inr (Or.inl hpin)
  · exact Or.inr (Or.inr hcl)

/-- **THE SAME, PER LEG.** -/
theorem executed_implies_real_flow_leg_finalizable_or_logged_clash {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {Ms Ns : Managers} {log : List CheckedCall}
    (hr : RunLog h z0 hl cv fh S Ms Ns log) {e : ExecCall} (he : CheckedCall.execute e ∈ log)
    {c : CheckedCall} (hc : c ∈ log) (hid : c.flow.flowId = e.flow.flowId)
    {other : FlowLeg} (hother : other ∈ c.flow.legs) :
    LegFinalizableBy h z0 hl cv S A c.flow other
      ∨ InclusionBreak h z0 hl S other.chain (e.evidence other).1 (e.evidence other).2
      ∨ FlowIdClash fh e.flow c.flow := by
  have hex := logged_execution_executes hr he
  have hchk : FlowIdChecked fh c.flow := (logged_calls_verified hr c hc).flowIdChecked
  rcases flowId_check_pins_legList_or_collision hex.2.1 hchk hid.symm with heq | hcl
  · rw [← heq] at hother ⊢
    rcases executed_implies_all_finalizable_or_break hS hDA hex other hother with hf | hb
    · exact Or.inl hf
    · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hcl)

/-! ## The refund side -/

/-- **A LOGGED EXECUTION AND A LOGGED REFUND AUTHORIZATION OF ONE FLOW ID: A LOCATED
BREAK OR A LOGGED CLASH.** -/
theorem logged_execution_excludes_logged_refund_or_break {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S)
    {Ms Ns : Managers} {log : List CheckedCall} (hr : RunLog h z0 hl cv fh S Ms Ns log)
    {e : ExecCall} (he : CheckedCall.execute e ∈ log) {a : AuthCall}
    (ha : CheckedCall.authorize a ∈ log) (hid : a.flow.flowId = e.flow.flowId) :
    InclusionBreak h z0 hl S a.missing.chain (e.evidence a.missing).1 (e.evidence a.missing).2
      ∨ AbsenceBreak h z0 hl S a.flow.deadline a.missing.chain a.batch a.proof
      ∨ FlowIdClash fh e.flow a.flow := by
  have hex := logged_execution_executes hr he
  obtain ⟨hchk, _, hmiss, href⟩ := logged_authorize_verified hr ha
  rcases flowId_check_pins_legList_or_collision hex.2.1 hchk hid.symm with heq | hcl
  · rw [← heq] at hmiss href ⊢
    rcases executed_excludes_any_refund_or_break hS hex a.missing hmiss a.batch a.proof
      with hn | hb | hb
    · exact absurd href hn
    · exact Or.inl hb
    · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hcl)

end Contracts.FlowBinding

/-! ## Certificates -/

namespace Contracts.FlowBinding

theorem LoggedCallsVerified : Properties.LoggedCallsVerified :=
  fun _ _ _ _ _ _ _ _ _ hr c hc =>
    ⟨logged_calls_verified hr c hc, (logged_calls_verified hr c hc).flowIdChecked⟩

theorem RunLogAuthCallsReachLog : Properties.RunLogAuthCallsReachLog :=
  fun _ _ _ _ _ _ _ _ _ hr => runLog_reachLog hr

theorem ReachLogEmbedsInRunLog : Properties.ReachLogEmbedsInRunLog :=
  fun _ _ _ _ _ _ _ _ alog hr => ⟨reachLog_runLog hr, authCalls_map_authorize alog⟩

theorem ExecutedImpliesRealFlowFinalizableOrLoggedClash :
    Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClash :=
  fun _ _ _ _ _ _ hS _ hDA _ _ _ hr _ he _ hc hid =>
    executed_implies_real_flow_finalizable_or_logged_clash hS hDA hr he hc hid

theorem ExecutedImpliesRealFlowLegFinalizableOrLoggedClash :
    Properties.ExecutedImpliesRealFlowLegFinalizableOrLoggedClash :=
  fun _ _ _ _ _ _ hS _ hDA _ _ _ hr _ he _ hc hid _ hother =>
    executed_implies_real_flow_leg_finalizable_or_logged_clash hS hDA hr he hc hid hother

theorem LoggedExecutionExcludesLoggedRefundOrBreak :
    Properties.LoggedExecutionExcludesLoggedRefundOrBreak :=
  fun _ _ _ _ _ _ hS _ _ _ hr _ he _ ha hid =>
    logged_execution_excludes_logged_refund_or_break hS hr he ha hid

end Contracts.FlowBinding

/-! ## Witnesses -/

namespace Contracts.FlowBinding

open MerkleSpec MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree
open Contracts.Atomicity Contracts.Timeout Contracts.Refund Contracts.AtomicFlowManager

/-! ### Shared pieces -/

/-- The honest proof of an occupied leaf is accepted for that leaf's value. -/
theorem honestProof_accepts {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : System} (hS : Wf S)
    {c : Chain} {n i : ℕ} (hi : i < (S.tree c n).leafCount) {v : UInt256}
    (hv : ((S.tree c n).leaf i).value = v) :
    Accepts h z0 hl S c n v (honestProof h z0 hl S c n i) := by
  have := inclusion_complete (h := h) (z0 := z0) (hl := hl) (hS.capacity c n) hi
  rw [hv] at this
  exact this

/-- The honest absence proof against `setup`: the sentinel at index 0, at height 0. -/
def setupAbsence (h : Hash) (z0 : UInt256) (hl : LeafHash) : ImtProof :=
  ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩

/-- On a chain whose batch-`N` tree is `setup` at height 0, the honest absence proof
passes the BEGIN branch of the timeout gate at the late batch `N + 1`, for any nonzero
commit value. -/
theorem setupAbsence_refundable {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} {F : Flow} {leg : FlowLeg} {N : ℕ}
    (hlate : F.deadline < S.time leg.chain (N + 1))
    (htree : S.tree leg.chain N = setup) (hheight : S.height leg.chain N = 0)
    (hv : 0 < legValue cv F leg) :
    LegRefundableBy h z0 hl cv S F leg (N + 1) (setupAbsence h z0 hl) := by
  refine Or.inl ⟨hlate, ?_⟩
  show AbsenceAccepted h z0 hl (S.tree leg.chain N) (S.height leg.chain N) (legValue cv F leg) _
  rw [htree, hheight]
  exact setup_absence_accepted h z0 hl hv

/-- …and it carries no `AbsenceBreak` there. -/
theorem setupAbsence_no_break {h : Hash} {z0 : UInt256} {hl : LeafHash} {S : System}
    {D : ℕ} {c : Chain} {N : ℕ} (hlate : D < S.time c (N + 1))
    (htree : S.tree c N = setup) (hheight : S.height c N = 0) :
    ¬ AbsenceBreak h z0 hl S D c (N + 1) (setupAbsence h z0 hl) := by
  rintro (⟨_, hb⟩ | ⟨hle, _⟩)
  · have hb' : TreeRootBreak h z0 hl (S.tree c N) (S.height c N)
        (honestSibs h z0 (leafHashes hl setup) 0) 0 0 ⟨0, 0, 0⟩ := hb
    rw [htree, hheight] at hb'
    exact honest_proof_no_break h z0 hl setup 0 0 (by norm_num [setup]) hb'
  · exact absurd hle (not_le.mpr hlate)

/-- A flow every leg of which is finalizable has no pinned gate break, whatever the
evidence. -/
theorem no_pinned_break_of_finalizable {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {A : Access} {F : Flow} (ev : GateEvidence)
    (hfin : FlowFinalizableBy h z0 hl cv S A F) : ¬ PinnedGateBreak h z0 hl cv S A F ev := by
  rintro ⟨l, hfirst, _⟩
  exact first_stranded_leg_iff_not_finalizable.1 ⟨l, hfirst⟩ hfin

/-- Leg lists of different lengths are different preimages. -/
theorem preimage_ne_of_legs_length_ne {F F' : Flow} (hlen : F.legs.length ≠ F'.legs.length) :
    (F.legs, F.deadline) ≠ (F'.legs, F'.deadline) := by
  intro hp
  exact hlen (congrArg (fun p => p.1.length) hp)

/-! ### The two-chain system

`Contracts.Atomicity.mixedSystem` commits on chain `0` only.  The witness in which a
two-chain flow executes both of its legs needs both chains to commit. -/

/-- Chain `0` commits the value `a` and chain `1` commits the value `b`, both during
batch 0.  Every other chain stays at `setup`.  Batch numbers are timestamps, so with
deadline `0` batch 0 is on time and every later batch is late. -/
def pairSystem (a b : UInt256) : System where
  tree := fun c _ => if c = 0 then insert setup a 0 else if c = 1 then insert setup b 0 else setup
  time := fun _ n => n
  height := fun c _ => if c = 0 ∨ c = 1 then 1 else 0

@[simp] lemma pairSystem_tree_zero (a b : UInt256) (n : ℕ) :
    (pairSystem a b).tree 0 n = insert setup a 0 := by simp [pairSystem]

@[simp] lemma pairSystem_tree_one (a b : UInt256) (n : ℕ) :
    (pairSystem a b).tree 1 n = insert setup b 0 := by
  simp [pairSystem, (by decide : (1 : Chain) ≠ 0)]

lemma pairSystem_tree_other {a b : UInt256} {c : Chain} (h0 : c ≠ 0) (h1 : c ≠ 1) (n : ℕ) :
    (pairSystem a b).tree c n = setup := by simp [pairSystem, h0, h1]

@[simp] lemma pairSystem_height_zero (a b : UInt256) (n : ℕ) :
    (pairSystem a b).height 0 n = 1 := by simp [pairSystem]

@[simp] lemma pairSystem_height_one (a b : UInt256) (n : ℕ) :
    (pairSystem a b).height 1 n = 1 := by simp [pairSystem]

lemma pairSystem_height_other {a b : UInt256} {c : Chain} (h0 : c ≠ 0) (h1 : c ≠ 1) (n : ℕ) :
    (pairSystem a b).height c n = 0 := by simp [pairSystem, h0, h1]

@[simp] lemma pairSystem_time (a b : UInt256) (c : Chain) (n : ℕ) :
    (pairSystem a b).time c n = n := rfl

lemma pairSystem_wf {a b : UInt256} (ha : 0 < a) (hb : 0 < b) : Wf (pairSystem a b) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    by_cases h0 : c = 0
    · subst h0
      rw [pairSystem_tree_zero]
      exact Reaches.tail Reaches.refl (setup_insertGuard ha)
    by_cases h1 : c = 1
    · subst h1
      rw [pairSystem_tree_one]
      exact Reaches.tail Reaches.refl (setup_insertGuard hb)
    rw [pairSystem_tree_other h0 h1]
    exact Reaches.refl
  · intro c n
    exact Reaches.refl
  · intro c i j hij
    simpa using hij
  · intro c n
    by_cases h0 : c = 0
    · subst h0
      rw [pairSystem_tree_zero, pairSystem_height_zero, insertSetup_leafCount]
      norm_num
    by_cases h1 : c = 1
    · subst h1
      rw [pairSystem_tree_one, pairSystem_height_one, insertSetup_leafCount]
      norm_num
    rw [pairSystem_tree_other h0 h1, pairSystem_height_other h0 h1]
    show (1 : ℕ) ≤ 2 ^ 0
    norm_num

/-! ### The honest run: both legs of a two-chain flow execute

In `pairSystem 1 2`, with `cv _ b = b` and `lengthFlowHash`, the flow `mixedFlow 1 1 2`
(id `1`, legs `⟨0, 1⟩` and `⟨1, 2⟩`, both committed at batch 0) executes both of its legs
on honest evidence.  The run also appends and authorizes a refund of `strandedFlow` (id
`0`, one leg on chain `2`, which commits nothing). -/

/-- Honest gate evidence on `pairSystem 1 2`: for each leg, the honest proof of leaf 1 of
its chain's batch-0 tree. -/
def pairEvidence (h : Hash) (z0 : UInt256) (hl : LeafHash) : GateEvidence :=
  fun l => (0, honestProof h z0 hl (pairSystem 1 2) l.chain 0 1)

/-- A one-leg flow with id `0` whose leg sits on chain `2`. -/
def strandedFlow : Flow := ⟨0, [⟨2, 3⟩], 0⟩

/-- The execution of leg `leg` of `mixedFlow 1 1 2`. -/
def pairExec (h : Hash) (z0 : UInt256) (hl : LeafHash) (leg : FlowLeg) : ExecCall :=
  ⟨mixedFlow 1 1 2, pairEvidence h z0 hl, leg⟩

/-- The refund authorization of `strandedFlow`, on the honest absence proof at batch 1. -/
def strandedAuth (h : Hash) (z0 : UInt256) (hl : LeafHash) : AuthCall :=
  ⟨strandedFlow, ⟨2, 3⟩, ⟨2, 3⟩, 1, setupAbsence h z0 hl⟩

def pairM1 : Managers := setAt emptyManagers 2 ((emptyManagers 2).set 0 3 .Committed)

def pairMs : Managers := setAt pairM1 2 ((pairM1 2).set 0 3 .Revertable)

/-- The log, most recent first: the second leg's execution, the first leg's execution, the
refund authorization. -/
def pairLog (h : Hash) (z0 : UInt256) (hl : LeafHash) : List CheckedCall :=
  [.execute (pairExec h z0 hl ⟨1, 2⟩), .execute (pairExec h z0 hl ⟨0, 1⟩),
    .authorize (strandedAuth h z0 hl)]

theorem lengthFlowHash_checks_stranded : FlowIdChecked lengthFlowHash strandedFlow := by
  simp [FlowIdChecked, lengthFlowHash, strandedFlow]

/-- Each leg of `mixedFlow 1 1 2` is occupied at index 1 of its chain's batch-0 tree. -/
theorem pair_leg_occupied {l : FlowLeg} (hl' : l ∈ (mixedFlow 1 1 2).legs) :
    1 < ((pairSystem 1 2).tree l.chain 0).leafCount
      ∧ (((pairSystem 1 2).tree l.chain 0).leaf 1).value = l.bundleHash := by
  rcases List.mem_cons.mp hl' with rfl | hl'
  · show 1 < ((pairSystem 1 2).tree 0 0).leafCount ∧ (((pairSystem 1 2).tree 0 0).leaf 1).value = 1
    rw [pairSystem_tree_zero, insertSetup_leafCount, insertSetup_leaf_one_value]
    exact ⟨by norm_num, rfl⟩
  · obtain rfl := List.mem_singleton.mp hl'
    show 1 < ((pairSystem 1 2).tree 1 0).leafCount ∧ (((pairSystem 1 2).tree 1 0).leaf 1).value = 2
    rw [pairSystem_tree_one, insertSetup_leafCount, insertSetup_leaf_one_value]
    exact ⟨by norm_num, rfl⟩

/-- Each leg's honest evidence passes that leg's check. -/
theorem pair_leg_finalizedBy (h : Hash) (z0 : UInt256) (hl : LeafHash) {l : FlowLeg}
    (hl' : l ∈ (mixedFlow 1 1 2).legs) :
    LegFinalizedBy h z0 hl (fun _ b => b) (pairSystem 1 2) (mixedFlow 1 1 2) l
      (pairEvidence h z0 hl l).1 (pairEvidence h z0 hl l).2 := by
  obtain ⟨hi, hv⟩ := pair_leg_occupied hl'
  exact ⟨le_refl _, honestProof_accepts (pairSystem_wf (by decide) (by decide)) hi hv⟩

theorem pairExec_verified (h : Hash) (z0 : UInt256) (hl : LeafHash) {leg : FlowLeg}
    (hleg : leg ∈ (mixedFlow 1 1 2).legs) :
    (pairExec h z0 hl leg).Verified h z0 hl (fun _ b => b) lengthFlowHash (pairSystem 1 2) :=
  ⟨hleg, lengthFlowHash_checks_mixed, fun _ hl' => pair_leg_finalizedBy h z0 hl hl'⟩

/-- With honest access, every leg of `mixedFlow 1 1 2` is finalizable. -/
theorem pair_flow_finalizable (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    FlowFinalizableBy h z0 hl (fun _ b => b) (pairSystem 1 2)
      (honestAccess h z0 hl (pairSystem 1 2)) (mixedFlow 1 1 2) := by
  intro l hl'
  obtain ⟨hon, hacc⟩ := pair_leg_finalizedBy h z0 hl hl'
  exact ⟨0, _, hon, ⟨1, (pair_leg_occupied hl').1, rfl⟩, hacc⟩

theorem strandedAuth_verified (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    (strandedAuth h z0 hl).Verified h z0 hl (fun _ b => b) lengthFlowHash (pairSystem 1 2) := by
  have h20 : (2 : Chain) ≠ 0 := by decide
  have h21 : (2 : Chain) ≠ 1 := by decide
  have hmem : (⟨2, 3⟩ : FlowLeg) ∈ strandedFlow.legs := List.mem_singleton_self _
  refine ⟨lengthFlowHash_checks_stranded, hmem, hmem, ?_⟩
  exact setupAbsence_refundable (F := strandedFlow) (leg := ⟨2, 3⟩) (N := 0)
    (by show (0 : ℕ) < 1; norm_num) (pairSystem_tree_other h20 h21 0)
    (pairSystem_height_other h20 h21 0) (by show (0 : UInt256) < 3; decide)

theorem pair_run (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    RunLog h z0 hl (fun _ b => b) lengthFlowHash (pairSystem 1 2) emptyManagers pairMs
      (pairLog h z0 hl) := by
  have happ : RunLog h z0 hl (fun _ b => b) lengthFlowHash (pairSystem 1 2) emptyManagers
      pairM1 [] := RunLog.append (c := 2) (f := 0) (b := 3) RunLog.refl rfl
  have hguard : AuthorizeGuard (pairM1 2) 0 3 := by
    show (pairM1 2).legState 0 3 = .Committed
    simp [pairM1, setAt, Manager.set]
  have hauth := RunLog.authorize (strandedAuth h z0 hl) happ (strandedAuth_verified h z0 hl) hguard
  have hex₁ := RunLog.execute (pairExec h z0 hl ⟨0, 1⟩) hauth
    (pairExec_verified h z0 hl List.mem_cons_self)
  exact RunLog.execute (pairExec h z0 hl ⟨1, 2⟩) hex₁
    (pairExec_verified h z0 hl (List.mem_cons_of_mem _ (List.mem_singleton_self _)))

theorem executed_implies_real_flow_finalizable_or_logged_clash_witness (h : Hash) (z0 : UInt256)
    (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (Ms : Managers)
      (log : List CheckedCall) (e e' : ExecCall) (c d : CheckedCall) (r : AuthCall),
      Wf S ∧ DataAvailable h z0 hl S A ∧ RunLog h z0 hl cv fh S emptyManagers Ms log
        ∧ CheckedCall.execute e ∈ log ∧ c ∈ log ∧ d ∈ log
        ∧ c = CheckedCall.execute e' ∧ e'.flow = e.flow ∧ e'.leg ≠ e.leg
        ∧ d = CheckedCall.authorize r
        ∧ c.flow.flowId = e.flow.flowId
        ∧ FlowFinalizableBy h z0 hl cv S A c.flow
        ∧ ¬ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
        ∧ (∀ c' ∈ log, ¬ FlowIdClash fh e.flow c'.flow)
        ∧ d.flow.flowId ≠ e.flow.flowId
        ∧ ¬ (FlowFinalizableBy h z0 hl cv S A d.flow
              ∨ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
              ∨ FlowIdClash fh e.flow d.flow) := by
  have h20 : (2 : Chain) ≠ 0 := by decide
  have h21 : (2 : Chain) ≠ 1 := by decide
  have hfin := pair_flow_finalizable h z0 hl
  have hnp : ¬ PinnedGateBreak h z0 hl (fun _ b => b) (pairSystem 1 2)
      (honestAccess h z0 hl (pairSystem 1 2)) (mixedFlow 1 1 2) (pairEvidence h z0 hl) :=
    no_pinned_break_of_finalizable _ hfin
  have hnoclashF : ¬ FlowIdClash lengthFlowHash (mixedFlow 1 1 2) (mixedFlow 1 1 2) :=
    fun hcl => hcl.1 rfl
  have hnoclashG : ¬ FlowIdClash lengthFlowHash (mixedFlow 1 1 2) strandedFlow := by
    rintro ⟨_, heq⟩
    exact absurd heq (by decide)
  have hnfinG : ¬ FlowFinalizableBy h z0 hl (fun _ b => b) (pairSystem 1 2)
      (honestAccess h z0 hl (pairSystem 1 2)) strandedFlow := by
    intro hall
    obtain ⟨n, p, _, ⟨i, _, rfl⟩, hacc⟩ := hall ⟨2, 3⟩ (List.mem_singleton_self _)
    have hv := hacc.valueMatch
    change (((pairSystem 1 2).tree 2 n).leaf i).value = 3 at hv
    rw [pairSystem_tree_other h20 h21] at hv
    change (0 : UInt256) = 3 at hv
    exact absurd hv (by decide)
  refine ⟨fun _ b => b, lengthFlowHash, pairSystem 1 2, honestAccess h z0 hl (pairSystem 1 2),
    pairMs, pairLog h z0 hl, pairExec h z0 hl ⟨0, 1⟩, pairExec h z0 hl ⟨1, 2⟩,
    .execute (pairExec h z0 hl ⟨1, 2⟩), .authorize (strandedAuth h z0 hl), strandedAuth h z0 hl,
    pairSystem_wf (by decide) (by decide), honestAccess_dataAvailable h z0 hl _, pair_run h z0 hl,
    List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl, rfl,
    by show (⟨1, 2⟩ : FlowLeg) ≠ ⟨0, 1⟩; decide, rfl, rfl, hfin, hnp, ?_,
    by show (0 : UInt256) ≠ 1; decide, ?_⟩
  · intro c' hc'
    simp only [pairLog, List.mem_cons, List.mem_nil_iff, or_false] at hc'
    rcases hc' with rfl | rfl | rfl
    · exact hnoclashF
    · exact hnoclashF
    · exact hnoclashG
  · rintro (hf | hp | hcl)
    · exact hnfinG hf
    · exact hnp hp
    · exact hnoclashG hcl

/-! ### The subset-flow attack, as a run -/

/-- The truncated flow's gate evidence on `S`: for leg `⟨0, hA⟩`, the honest proof of leaf
1 of chain `0`'s batch-0 tree; for every other leg, the honest proof of chain `1`'s
sentinel. -/
def subsetEvidence (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System) (hA : UInt256)
    (l : FlowLeg) : ℕ × ImtProof :=
  if l = ⟨0, hA⟩ then (0, honestProof h z0 hl S 0 0 1) else (0, honestProof h z0 hl S 1 0 0)

theorem subsetEvidence_legA (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (hA : UInt256) : subsetEvidence h z0 hl S hA ⟨0, hA⟩ = (0, honestProof h z0 hl S 0 0 1) :=
  ite_eq_left rfl

theorem subsetEvidence_chain_one (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (hA hB : UInt256) :
    subsetEvidence h z0 hl S hA ⟨1, hB⟩ = (0, honestProof h z0 hl S 1 0 0) :=
  ite_eq_right (fun he => (by decide : (1 : Chain) ≠ 0) (congrArg FlowLeg.chain he))

theorem subset_flow_attack_lands_in_logged_clash (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (cv : CommitValue) (id hA hB : UInt256) (ha : 0 < cv id hA) (hb : 0 < cv id hB) :
    ∃ (Ms : Managers) (log : List CheckedCall) (e : ExecCall) (a : AuthCall),
      Wf (mixedSystem (cv id hA))
        ∧ DataAvailable h z0 hl (mixedSystem (cv id hA))
            (honestAccess h z0 hl (mixedSystem (cv id hA)))
        ∧ RunLog h z0 hl cv (fun _ _ => id) (mixedSystem (cv id hA)) emptyManagers Ms log
        ∧ CheckedCall.execute e ∈ log ∧ CheckedCall.authorize a ∈ log
        ∧ e.flow = subsetFlow id hA ∧ e.leg = ⟨0, hA⟩
        ∧ a.flow = mixedFlow id hA hB ∧ a.missing = ⟨1, hB⟩
        ∧ a.flow.flowId = e.flow.flowId
        ∧ ¬ LegFinalizableBy h z0 hl cv (mixedSystem (cv id hA))
            (honestAccess h z0 hl (mixedSystem (cv id hA))) a.flow a.missing
        ∧ ¬ FlowFinalizableBy h z0 hl cv (mixedSystem (cv id hA))
            (honestAccess h z0 hl (mixedSystem (cv id hA))) a.flow
        ∧ ¬ PinnedGateBreak h z0 hl cv (mixedSystem (cv id hA))
            (honestAccess h z0 hl (mixedSystem (cv id hA))) e.flow e.evidence
        ∧ ¬ InclusionBreak h z0 hl (mixedSystem (cv id hA)) a.missing.chain
            (e.evidence a.missing).1 (e.evidence a.missing).2
        ∧ ¬ AbsenceBreak h z0 hl (mixedSystem (cv id hA)) a.flow.deadline a.missing.chain
            a.batch a.proof
        ∧ FlowIdClash (fun _ _ => id) e.flow a.flow := by
  have h10 : (1 : Chain) ≠ 0 := by decide
  have hS : Wf (mixedSystem (cv id hA)) := mixedSystem_wf ha
  have hcountA : ((mixedSystem (cv id hA)).tree 0 0).leafCount = 2 := by
    rw [mixedSystem_tree_zero]; rfl
  have accA : Accepts h z0 hl (mixedSystem (cv id hA)) 0 0 (cv id hA)
      (honestProof h z0 hl (mixedSystem (cv id hA)) 0 0 1) :=
    honestProof_accepts hS (by rw [hcountA]; norm_num)
      (by rw [mixedSystem_tree_zero, insertSetup_leaf_one_value])
  have hmemB : (⟨1, hB⟩ : FlowLeg) ∈ (mixedFlow id hA hB).legs :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  -- The execution of the truncated flow passes the deployed gate under `fun _ _ => id`.
  have hex : ExecutedViaBy h z0 hl cv (fun _ _ => id) (mixedSystem (cv id hA)) (subsetFlow id hA)
      (subsetEvidence h z0 hl (mixedSystem (cv id hA)) hA) ⟨0, hA⟩ := by
    refine ⟨List.mem_singleton_self _, rfl, ?_⟩
    intro l hl'
    obtain rfl : l = ⟨0, hA⟩ := List.mem_singleton.mp hl'
    show LegFinalizedBy h z0 hl cv (mixedSystem (cv id hA)) (subsetFlow id hA) ⟨0, hA⟩
      (subsetEvidence h z0 hl (mixedSystem (cv id hA)) hA ⟨0, hA⟩).1
      (subsetEvidence h z0 hl (mixedSystem (cv id hA)) hA ⟨0, hA⟩).2
    rw [subsetEvidence_legA]
    exact ⟨le_refl _, accA⟩
  -- The refund of the real flow passes `authorizeRefund` under the same flow hash.
  have hav : AuthCall.Verified h z0 hl cv (fun _ _ => id) (mixedSystem (cv id hA))
      ⟨mixedFlow id hA hB, ⟨1, hB⟩, ⟨1, hB⟩, 1, setupAbsence h z0 hl⟩ :=
    ⟨rfl, hmemB, hmemB,
      setupAbsence_refundable (F := mixedFlow id hA hB) (leg := ⟨1, hB⟩) (N := 0)
        (by show (0 : ℕ) < 1; norm_num) (mixedSystem_tree_other h10 0)
        (mixedSystem_height_other h10 0) hb⟩
  have happ : RunLog h z0 hl cv (fun _ _ => id) (mixedSystem (cv id hA)) emptyManagers
      (setAt emptyManagers 1 ((emptyManagers 1).set id hB .Committed)) [] :=
    RunLog.append (c := 1) (f := id) (b := hB) RunLog.refl rfl
  have hguard : AuthorizeGuard
      ((setAt emptyManagers 1 ((emptyManagers 1).set id hB .Committed)) 1) id hB := by
    show ((setAt emptyManagers 1 ((emptyManagers 1).set id hB .Committed)) 1).legState id hB
      = .Committed
    simp [setAt, Manager.set]
  have hrun := RunLog.authorize ⟨mixedFlow id hA hB, ⟨1, hB⟩, ⟨1, hB⟩, 1, setupAbsence h z0 hl⟩
    (RunLog.execute ⟨subsetFlow id hA, subsetEvidence h z0 hl (mixedSystem (cv id hA)) hA, ⟨0, hA⟩⟩
      happ hex) hav hguard
  -- The real flow's missing leg is not finalizable: chain `1` holds only its sentinel.
  have hnleg : ¬ LegFinalizableBy h z0 hl cv (mixedSystem (cv id hA))
      (honestAccess h z0 hl (mixedSystem (cv id hA))) (mixedFlow id hA hB) ⟨1, hB⟩ := by
    rintro ⟨n, p, _, ⟨i, _, rfl⟩, hacc⟩
    have hv := hacc.valueMatch
    change (((mixedSystem (cv id hA)).tree 1 n).leaf i).value = cv id hB at hv
    rw [mixedSystem_tree_other h10] at hv
    change (0 : UInt256) = cv id hB at hv
    exact absurd hv (ne_of_lt hb)
  -- The truncated flow is all finalizable, so it has no stranded leg to break on.
  have hfinSub : FlowFinalizableBy h z0 hl cv (mixedSystem (cv id hA))
      (honestAccess h z0 hl (mixedSystem (cv id hA))) (subsetFlow id hA) := by
    intro l hl'
    obtain rfl : l = ⟨0, hA⟩ := List.mem_singleton.mp hl'
    exact ⟨0, _, le_refl _, ⟨1, by rw [hcountA]; norm_num, rfl⟩, accA⟩
  have hnb : ¬ InclusionBreak h z0 hl (mixedSystem (cv id hA)) 1
      (subsetEvidence h z0 hl (mixedSystem (cv id hA)) hA ⟨1, hB⟩).1
      (subsetEvidence h z0 hl (mixedSystem (cv id hA)) hA ⟨1, hB⟩).2 := by
    rw [subsetEvidence_chain_one]
    exact honestProof_no_break h z0 hl _ 1 0 0
      (by rw [mixedSystem_tree_other h10]; norm_num [setup])
  refine ⟨_, _, ⟨subsetFlow id hA, subsetEvidence h z0 hl (mixedSystem (cv id hA)) hA, ⟨0, hA⟩⟩,
    ⟨mixedFlow id hA hB, ⟨1, hB⟩, ⟨1, hB⟩, 1, setupAbsence h z0 hl⟩, hS,
    honestAccess_dataAvailable h z0 hl _, hrun, List.mem_cons_of_mem _ List.mem_cons_self,
    List.mem_cons_self, rfl, rfl, rfl, rfl, rfl, hnleg, fun hall => hnleg (hall _ hmemB),
    no_pinned_break_of_finalizable _ hfinSub, hnb,
    setupAbsence_no_break (N := 0) (by show (0 : ℕ) < 1; norm_num)
      (mixedSystem_tree_other h10 0) (mixedSystem_height_other h10 0),
    preimage_ne_of_legs_length_ne (by show (1 : ℕ) ≠ 2; decide), rfl⟩

/-! ### A forged proof for the stranded sibling, as a run -/

theorem forged_sibling_proof_lands_in_pinned_break (h : Hash) (z0 : UInt256) :
    ∃ (Ms : Managers) (log : List CheckedCall) (e : ExecCall) (a : AuthCall),
      Wf (mixedSystem 1)
        ∧ DataAvailable h z0 toyLeafHash (mixedSystem 1)
            (honestAccess h z0 toyLeafHash (mixedSystem 1))
        ∧ RunLog h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
            (mixedSystem 1) emptyManagers Ms log
        ∧ CheckedCall.execute e ∈ log ∧ CheckedCall.authorize a ∈ log
        ∧ e.flow = mixedFlow 0 1 2 ∧ e.leg = ⟨0, 1⟩
        ∧ a.flow = mixedFlow 0 1 2 ∧ a.missing = ⟨1, 2⟩
        ∧ ¬ LegFinalizableBy h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
            (honestAccess h z0 toyLeafHash (mixedSystem 1)) a.flow a.missing
        ∧ ¬ FlowFinalizableBy h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
            (honestAccess h z0 toyLeafHash (mixedSystem 1)) a.flow
        ∧ PinnedGateBreak h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
            (honestAccess h z0 toyLeafHash (mixedSystem 1)) e.flow e.evidence
        ∧ ¬ FlowIdClash (honestFlowHash (mixedFlow 0 1 2)) e.flow a.flow
        ∧ ¬ InclusionBreak h z0 toyLeafHash (mixedSystem 1) e.leg.chain
            (e.evidence e.leg).1 (e.evidence e.leg).2
        ∧ InclusionBreak h z0 toyLeafHash (mixedSystem 1) a.missing.chain
            (e.evidence a.missing).1 (e.evidence a.missing).2
        ∧ ¬ AbsenceBreak h z0 toyLeafHash (mixedSystem 1) a.flow.deadline a.missing.chain
            a.batch a.proof := by
  have h10 : (1 : Chain) ≠ 0 := by decide
  obtain ⟨hS, hDA, _, _, evF, _, nbA, hex, brkB, hpin, _, _⟩ :=
    pinned_gate_break_fires_only_on_stranded_leg h z0
  obtain ⟨_, nfinB, _⟩ := mixed_stranded_world h z0 toyLeafHash
  have hmemB : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 0 1 2).legs :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hav : AuthCall.Verified h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
      (mixedSystem 1) ⟨mixedFlow 0 1 2, ⟨1, 2⟩, ⟨1, 2⟩, 1, setupAbsence h z0 toyLeafHash⟩ :=
    ⟨(honest_flowHash_no_clash _).1, hmemB, hmemB,
      setupAbsence_refundable (F := mixedFlow 0 1 2) (leg := ⟨1, 2⟩) (N := 0)
        (by show (0 : ℕ) < 1; norm_num) (mixedSystem_tree_other h10 0)
        (mixedSystem_height_other h10 0) (by show (0 : UInt256) < 2; decide)⟩
  have happ : RunLog h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
      (mixedSystem 1) emptyManagers
      (setAt emptyManagers 1 ((emptyManagers 1).set 0 2 .Committed)) [] :=
    RunLog.append (c := 1) (f := 0) (b := 2) RunLog.refl rfl
  have hguard : AuthorizeGuard
      ((setAt emptyManagers 1 ((emptyManagers 1).set 0 2 .Committed)) 1) 0 2 := by
    show ((setAt emptyManagers 1 ((emptyManagers 1).set 0 2 .Committed)) 1).legState 0 2
      = .Committed
    simp [setAt, Manager.set]
  have hrun := RunLog.authorize ⟨mixedFlow 0 1 2, ⟨1, 2⟩, ⟨1, 2⟩, 1, setupAbsence h z0 toyLeafHash⟩
    (RunLog.execute ⟨mixedFlow 0 1 2, evF, ⟨0, 1⟩⟩ happ hex) hav hguard
  exact ⟨_, _, ⟨mixedFlow 0 1 2, evF, ⟨0, 1⟩⟩,
    ⟨mixedFlow 0 1 2, ⟨1, 2⟩, ⟨1, 2⟩, 1, setupAbsence h z0 toyLeafHash⟩, hS, hDA, hrun,
    List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self, rfl, rfl, rfl, rfl,
    nfinB, fun hall => nfinB (hall _ hmemB), hpin, fun hcl => hcl.1 rfl, nbA, brkB,
    setupAbsence_no_break (N := 0) (by show (0 : ℕ) < 1; norm_num)
      (mixedSystem_tree_other h10 0) (mixedSystem_height_other h10 0)⟩

/-! ### A forged padding absence proof, as a run -/

theorem padding_refund_lands_in_absence_break (h : Hash) (hl : LeafHash) (a b : UInt256)
    (ha : 0 < a) (hab : a < b) :
    ∃ (cv : CommitValue) (fh : FlowHash) (Ms : Managers) (log : List CheckedCall)
      (e : ExecCall) (r : AuthCall),
      Wf (paddedSystem a b)
        ∧ RunLog h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) emptyManagers Ms log
        ∧ CheckedCall.execute e ∈ log ∧ CheckedCall.authorize r ∈ log
        ∧ r.flow = e.flow
        ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) r.missing.chain
            (e.evidence r.missing).1 (e.evidence r.missing).2
        ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) r.flow.deadline r.missing.chain
            r.batch r.proof
        ∧ ¬ FlowIdClash fh e.flow r.flow := by
  let z0 := hl ⟨0, 0, 0⟩
  let T := threeLeafTree a b
  let F : Flow := subsetFlow 0 0
  let p : ImtProof := ⟨T.leaf 1, 1, honestSibs h z0 (leafHashes hl T) 1, 2⟩
  let q : ImtProof := ⟨⟨0, 0, 0⟩, 3, honestSibs h z0 (leafHashes hl T) 3, 2⟩
  let M1 : Managers := setAt emptyManagers 0 ((emptyManagers 0).set 0 0 .Committed)
  obtain ⟨_, hI, hN⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  obtain ⟨hnb, hpad⟩ := padding_countermodel_locates_padding_hit h hl a b
  have hchk : FlowIdChecked (honestFlowHash F) F := (honest_flowHash_no_clash F).1
  have hmem : (⟨0, 0⟩ : FlowLeg) ∈ F.legs := List.mem_singleton_self _
  have hex : ExecutedViaBy h z0 hl (fun _ _ => a) (honestFlowHash F) (paddedSystem a b) F
      (fun _ => (0, p)) ⟨0, 0⟩ := by
    refine ⟨hmem, hchk, ?_⟩
    intro l hl'
    obtain rfl : l = ⟨0, 0⟩ := List.mem_singleton.mp hl'
    exact ⟨le_refl 0, hI⟩
  have href : LegRefundableBy h z0 hl (fun _ _ => a) (paddedSystem a b) F ⟨0, 0⟩ 0 q :=
    Or.inr ⟨⟨le_refl 0, fun m hm => hm⟩, hN⟩
  have hab' : AbsenceBreak h z0 hl (paddedSystem a b) F.deadline (0 : Chain) 0 q :=
    Or.inr ⟨le_refl 0, hpad⟩
  have happ : RunLog h z0 hl (fun _ _ => a) (honestFlowHash F) (paddedSystem a b)
      emptyManagers M1 [] := RunLog.append (c := 0) (f := 0) (b := 0) RunLog.refl rfl
  have hguard : AuthorizeGuard (M1 0) 0 0 := by
    show (M1 0).legState 0 0 = .Committed
    simp [M1, setAt, Manager.set]
  have hrun := RunLog.authorize ⟨F, ⟨0, 0⟩, ⟨0, 0⟩, 0, q⟩
    (RunLog.execute ⟨F, fun _ => (0, p), ⟨0, 0⟩⟩ happ hex) ⟨hchk, hmem, hmem, href⟩ hguard
  exact ⟨fun _ _ => a, honestFlowHash F, _, _, ⟨F, fun _ => (0, p), ⟨0, 0⟩⟩,
    ⟨F, ⟨0, 0⟩, ⟨0, 0⟩, 0, q⟩, paddedSystem_wf ha hab, hrun,
    List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self, rfl, hnb, hab',
    fun hcl => hcl.1 rfl⟩

end Contracts.FlowBinding

/-! ## Certificates for the witnesses -/

namespace Contracts.FlowBinding

theorem ExecutedImpliesRealFlowFinalizableOrLoggedClashWitness :
    Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClashWitness :=
  executed_implies_real_flow_finalizable_or_logged_clash_witness

theorem SubsetFlowAttackLandsInLoggedClash : Properties.SubsetFlowAttackLandsInLoggedClash :=
  subset_flow_attack_lands_in_logged_clash

theorem ForgedSiblingProofLandsInPinnedBreak : Properties.ForgedSiblingProofLandsInPinnedBreak :=
  forged_sibling_proof_lands_in_pinned_break

theorem PaddingRefundLandsInAbsenceBreak : Properties.PaddingRefundLandsInAbsenceBreak :=
  padding_refund_lands_in_absence_break

end Contracts.FlowBinding
