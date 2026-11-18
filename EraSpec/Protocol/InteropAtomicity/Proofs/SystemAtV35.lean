import EraSpec.Protocol.InteropAtomicity.Properties.SystemAtV35
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund
import EraSpec.Protocol.InteropAtomicity.Proofs.Atomicity
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLegAtHead
import EraSpec.Protocol.InteropAtomicity.Proofs.LegSourceFilterAtV35

/-!
# Proofs: the composed system at `draft/v0.35.0`

Proofs of `EraSpec.Protocol.InteropAtomicity.Properties.SystemAtV35`.  Each run-level result is
one induction over `RunV35`.  The transfers apply the merged results to a projected run
(`runV35_reachLog`, `runV35_sysStepsAtHead`).  The refinement of a code `authorizeRefund` call
(`runV35_code_marks`) is an induction over the presented flow's legs, one `authorize` step per
`Committed` key.
-/

namespace Contracts.SystemAtV35

open MerkleSpec MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund Contracts.FlowBinding Contracts.AppendPath

/-! ## World updates -/

@[simp] lemma v35_set_self (W : WorldV35) (c : Chain) (x : ChainV35) : W.set c x c = x := by
  simp [WorldV35.set]

lemma v35_set_other (W : WorldV35) {c y : Chain} (x : ChainV35) (h : y ≠ c) :
    W.set c x y = W y := by
  simp [WorldV35.set, h]

lemma v35_mgrs_set (W : WorldV35) (c : Chain) (x : ChainV35) :
    (W.set c x).mgrs = setAt W.mgrs c x.base.mgr := by
  funext y
  by_cases hy : y = c
  · subst hy; simp [WorldV35.mgrs, setAt]
  · simp [WorldV35.mgrs, setAt, v35_set_other _ _ hy, hy]

/-- A step that leaves the chain's manager alone leaves every manager alone. -/
lemma v35_mgrs_set_same (W : WorldV35) (c : Chain) {x : ChainV35}
    (hx : x.base.mgr = (W c).base.mgr) : (W.set c x).mgrs = W.mgrs := by
  funext y
  by_cases hy : y = c
  · subst hy; simp [WorldV35.mgrs, hx]
  · simp [WorldV35.mgrs, v35_set_other _ _ hy]

lemma v35_hubs_set_same (W : WorldV35) (c : Chain) {x : ChainV35} (hx : x.hub = (W c).hub) :
    (W.set c x).hubs = W.hubs := by
  funext y
  by_cases hy : y = c
  · subst hy; simp [WorldV35.hubs, hx]
  · simp [WorldV35.hubs, v35_set_other _ _ hy]

lemma v35_roots_set_same (W : WorldV35) (c : Chain) {x : ChainV35} (hx : x.roots = (W c).roots)
    (y : Chain) : (W.set c x y).roots = (W y).roots := by
  by_cases hy : y = c
  · subst hy; simp [hx]
  · simp [v35_set_other _ _ hy]

lemma v35_status_set_same (W : WorldV35) (c : Chain) {x : ChainV35}
    (hx : x.status = (W c).status) (y : Chain) : (W.set c x y).status = (W y).status := by
  by_cases hy : y = c
  · subst hy; simp [hx]
  · simp [v35_set_other _ _ hy]

lemma v35_mgr_set_same (W : WorldV35) (c : Chain) {x : ChainV35}
    (hx : x.base.mgr = (W c).base.mgr) (y : Chain) : (W.set c x y).base.mgr = (W y).base.mgr := by
  by_cases hy : y = c
  · subst hy; simp [hx]
  · simp [v35_set_other _ _ hy]

/-! ## The logs -/

@[simp] lemma authLog_cons_append (c : Chain) (F : Flow) (b : UInt256) (d : Chain)
    (log : List CallV35) : authLog (.append c F b d :: log) = authLog log := rfl
@[simp] lemma authLog_cons_gate (d : Chain) (e : ExecCall) (log : List CallV35) :
    authLog (.gate d e :: log) = authLog log := rfl
@[simp] lemma authLog_cons_authorize (a : AuthCall) (log : List CallV35) :
    authLog (.authorize a :: log) = a :: authLog log := rfl
@[simp] lemma authLog_cons_admin (c : Chain) (op : AdminOp) (log : List CallV35) :
    authLog (.admin c op :: log) = authLog log := rfl

@[simp] lemma checkedLog_cons_append (c : Chain) (F : Flow) (b : UInt256) (d : Chain)
    (log : List CallV35) : checkedLog (.append c F b d :: log) = checkedLog log := rfl
@[simp] lemma checkedLog_cons_gate (d : Chain) (e : ExecCall) (log : List CallV35) :
    checkedLog (.gate d e :: log) = .execute e :: checkedLog log := rfl
@[simp] lemma checkedLog_cons_authorize (a : AuthCall) (log : List CallV35) :
    checkedLog (.authorize a :: log) = .authorize a :: checkedLog log := rfl
@[simp] lemma checkedLog_cons_admin (c : Chain) (op : AdminOp) (log : List CallV35) :
    checkedLog (.admin c op :: log) = checkedLog log := rfl

@[simp] lemma appendLog_cons_append (c : Chain) (F : Flow) (b : UInt256) (d : Chain)
    (log : List CallV35) : appendLog (.append c F b d :: log) = ⟨F.flowId, b, c⟩ :: appendLog log :=
  rfl
@[simp] lemma appendLog_cons_gate (d : Chain) (e : ExecCall) (log : List CallV35) :
    appendLog (.gate d e :: log) = appendLog log := rfl
@[simp] lemma appendLog_cons_authorize (a : AuthCall) (log : List CallV35) :
    appendLog (.authorize a :: log) = appendLog log := rfl
@[simp] lemma appendLog_cons_admin (c : Chain) (op : AdminOp) (log : List CallV35) :
    appendLog (.admin c op :: log) = appendLog log := rfl

@[simp] lemma hubsAfter_cons_append (H : Chain → Hub) (c : Chain) (F : Flow) (b : UInt256)
    (d : Chain) (log : List CallV35) : hubsAfter H (.append c F b d :: log) = hubsAfter H log := rfl
@[simp] lemma hubsAfter_cons_gate (H : Chain → Hub) (d : Chain) (e : ExecCall)
    (log : List CallV35) : hubsAfter H (.gate d e :: log) = hubsAfter H log := rfl
@[simp] lemma hubsAfter_cons_authorize (H : Chain → Hub) (a : AuthCall) (log : List CallV35) :
    hubsAfter H (.authorize a :: log) = hubsAfter H log := rfl
lemma hubsAfter_cons_admin (H : Chain → Hub) (c : Chain) (op : AdminOp) (log : List CallV35) :
    hubsAfter H (.admin c op :: log)
      = fun x => if x = c then op.apply (hubsAfter H log c) else hubsAfter H log x := rfl

/-- Splitting a log at a call: the head is that call, or the call is further back. -/
lemma v35_cons_eq_append_cons {c x : CallV35} {log later earlier : List CallV35}
    (h : c :: log = later ++ x :: earlier) :
    (later = [] ∧ c = x ∧ log = earlier)
      ∨ ∃ later', later = c :: later' ∧ log = later' ++ x :: earlier := by
  cases later with
  | nil =>
    left
    simp only [List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h.1, h.2⟩
  | cons y later' =>
    right
    simp only [List.cons_append, List.cons.injEq] at h
    exact ⟨later', by rw [h.1], h.2⟩

/-! ## The pin's results hold at v35 -/

theorem runV35_reachLog {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S X Y log) :
    ReachLog h z0 hl cv fh S X.mgrs Y.mgrs (authLog log) := by
  induction hr with
  | refl => exact ReachLog.refl
  | @append Y log c F b dest hint low _ ha ih =>
    rw [v35_mgrs_set, authLog_cons_append]
    exact ReachLog.append (c := c) (f := F.flowId) (b := b) ih ha.legUnset
  | importRoot _ _ _ ih => simpa only [v35_mgrs_set_same] using ih
  | gate _ _ _ _ ih => simpa only [v35_mgrs_set_same, authLog_cons_gate] using ih
  | resume _ _ ih => simpa only [v35_mgrs_set_same] using ih
  | @authorize Y log a _ hok hg ih =>
    rw [v35_mgrs_set, authLog_cons_authorize]
    exact ReachLog.authorize a ih hok.1 hg
  | @claim Y log c f b _ hg ih =>
    rw [v35_mgrs_set]
    exact ReachLog.claim (c := c) (f := f) (b := b) ih hg
  | admin _ _ _ ih => simpa only [v35_mgrs_set_same, authLog_cons_admin] using ih
  | initL2 _ _ ih => simpa only [v35_mgrs_set_same] using ih

theorem runV35_runLog {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S X Y log) :
    RunLog h z0 hl cv fh S X.mgrs Y.mgrs (checkedLog log) := by
  induction hr with
  | refl => exact RunLog.refl
  | @append Y log c F b dest hint low _ ha ih =>
    rw [v35_mgrs_set, checkedLog_cons_append]
    exact RunLog.append (c := c) (f := F.flowId) (b := b) ih ha.legUnset
  | importRoot _ _ _ ih => simpa only [v35_mgrs_set_same] using ih
  | @gate Y log d e st _ _ _ hok ih =>
    simp only [v35_mgrs_set_same, checkedLog_cons_gate]
    exact RunLog.execute e ih hok.1
  | resume _ _ ih => simpa only [v35_mgrs_set_same] using ih
  | @authorize Y log a _ hok hg ih =>
    rw [v35_mgrs_set, checkedLog_cons_authorize]
    exact RunLog.authorize a ih hok.1 hg
  | @claim Y log c f b _ hg ih =>
    rw [v35_mgrs_set]
    exact RunLog.claim (c := c) (f := f) (b := b) ih hg
  | admin _ _ _ ih => simpa only [v35_mgrs_set_same, checkedLog_cons_admin] using ih
  | initL2 _ _ ih => simpa only [v35_mgrs_set_same] using ih

theorem RunV35ProjectsToReachLog : Properties.RunV35ProjectsToReachLog :=
  fun _ _ _ _ _ _ _ _ _ hr => runV35_reachLog hr

theorem RunV35ProjectsToRunLog : Properties.RunV35ProjectsToRunLog :=
  fun _ _ _ _ _ _ _ _ _ hr => runV35_runLog hr

lemma genesisV35_mgrs (H0 : Chain → Hub) : (genesisV35 H0).mgrs = emptyManagers := rfl

theorem V35ExecutedObligationNeverRefundedOrBreak :
    Properties.V35ExecutedObligationNeverRefundedOrBreak := by
  intro h z0 hl cv fh S hS F ev leg hex H0 Y log hr
  have hrl := runV35_reachLog hr
  rw [genesisV35_mgrs] at hrl
  exact Contracts.Refund.ExecutedObligationNeverRefundedOrBreak h z0 hl cv fh S hS F ev leg hex
    Y.mgrs (authLog log) hrl

/-! ## The head system run -/

lemma v35_chains_set (W : WorldV35) (c : Chain) (x : ChainV35) :
    (W.set c x).chains = W.chains.update c x.base := by
  funext y
  by_cases hy : y = c
  · subst hy; simp [WorldV35.chains, Chains.update]
  · simp [WorldV35.chains, Chains.update, v35_set_other _ _ hy, hy]

/-- A step that leaves the chain's manager and tree alone leaves every chain's alone. -/
lemma v35_chains_set_same (W : WorldV35) (c : Chain) {x : ChainV35} (hx : x.base = (W c).base) :
    (W.set c x).chains = W.chains := by
  funext y
  by_cases hy : y = c
  · subst hy; simp [WorldV35.chains, hx]
  · simp [WorldV35.chains, v35_set_other _ _ hy]

theorem runV35_sysStepsAtHead {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S X Y log) :
    SysStepsAtHead h z0 hl cv fh S X.chains Y.chains (appendLog log) (authLog log) := by
  induction hr with
  | refl => exact SysStepsAtHead.refl
  | @append Y log c F b dest hint low _ ha ih =>
    rw [v35_chains_set, appendLog_cons_append, authLog_cons_append]
    exact SysStepsAtHead.append (c := c) (f := F.flowId) (b := b) (hint := hint) (low := low) ih
      ⟨ha.legUnset, ha.treeInsert⟩
  | importRoot _ _ _ ih => simpa only [v35_chains_set_same] using ih
  | gate _ _ _ _ ih =>
    simpa only [v35_chains_set_same, appendLog_cons_gate, authLog_cons_gate] using ih
  | resume _ _ ih => simpa only [v35_chains_set_same] using ih
  | @authorize Y log a _ hok hg ih =>
    rw [v35_chains_set, appendLog_cons_authorize, authLog_cons_authorize]
    exact SysStepsAtHead.authorize a ih hok.1 hg
  | @claim Y log c f b _ hg ih =>
    rw [v35_chains_set]
    exact SysStepsAtHead.claim (c := c) (f := f) (b := b) ih hg
  | admin _ _ _ ih =>
    simpa only [v35_chains_set_same, appendLog_cons_admin, authLog_cons_admin] using ih
  | @initL2 Y log c _ h0 ih =>
    rw [v35_chains_set]
    exact SysStepsAtHead.initL2 (c := c) ih h0

theorem RunV35ProjectsToSysStepsAtHead : Properties.RunV35ProjectsToSysStepsAtHead :=
  fun _ _ _ _ _ _ _ _ _ hr => runV35_sysStepsAtHead hr

lemma genesisV35_chains (H0 : Chain → Hub) : (genesisV35 H0).chains = genesisAll := rfl

theorem SystemOncePerLegV35 : Properties.SystemOncePerLegV35 := by
  intro h z0 hl cv fh S H0 Y log hr
  have hs := runV35_sysStepsAtHead hr
  rw [genesisV35_chains] at hs
  exact Contracts.AppendPath.SystemOncePerLegAtHead h z0 hl cv fh S Y.chains (appendLog log)
    (authLog log) hs

/-! ## Refund before append, on one chain -/

/-- The root storage of a chain after `importRoot`, and of every other chain. -/
lemma v35_roots_import (Y : WorldV35) (c y : Chain) (blk t : ℕ) :
    ((Y.set c { Y c with roots := (Y c).roots.import blk t }) y).roots
      = if y = c then (Y c).roots.import blk t else (Y y).roots := by
  by_cases hy : y = c
  · subst hy; simp
  · simp [v35_set_other _ _ hy, hy]

theorem runV35_roots {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S X Y log) (hX : RootsWf X) :
    RootsWf Y ∧ ∀ c, (X c).roots.latest ≤ (Y c).roots.latest := by
  induction hr with
  | refl => exact ⟨hX, fun _ => le_rfl⟩
  | append _ _ ih =>
    exact ⟨fun y blk => by simpa only [v35_roots_set_same] using ih.1 y blk,
      fun y => by simpa only [v35_roots_set_same] using ih.2 y⟩
  | @importRoot Y log c blk t _ _ _ ih =>
    obtain ⟨hwf, hmono⟩ := ih
    refine ⟨fun y blk' => ?_, fun y => ?_⟩
    · rw [v35_roots_import]
      split_ifs with hy
      · subst hy
        simp only [Roots.import]
        split_ifs
        · exact le_max_right _ _
        · exact le_trans (hwf y blk') (le_max_left _ _)
      · exact hwf y blk'
    · rw [v35_roots_import]
      split_ifs with hy
      · subst hy
        exact le_trans (hmono y) (le_max_left _ _)
      · exact hmono y
  | gate _ _ _ _ ih =>
    exact ⟨fun y blk => by simpa only [v35_roots_set_same] using ih.1 y blk,
      fun y => by simpa only [v35_roots_set_same] using ih.2 y⟩
  | resume _ _ ih =>
    exact ⟨fun y blk => by simpa only [v35_roots_set_same] using ih.1 y blk,
      fun y => by simpa only [v35_roots_set_same] using ih.2 y⟩
  | authorize _ _ _ _ ih =>
    exact ⟨fun y blk => by simpa only [v35_roots_set_same] using ih.1 y blk,
      fun y => by simpa only [v35_roots_set_same] using ih.2 y⟩
  | claim _ _ ih =>
    exact ⟨fun y blk => by simpa only [v35_roots_set_same] using ih.1 y blk,
      fun y => by simpa only [v35_roots_set_same] using ih.2 y⟩
  | admin _ _ _ ih =>
    exact ⟨fun y blk => by simpa only [v35_roots_set_same] using ih.1 y blk,
      fun y => by simpa only [v35_roots_set_same] using ih.2 y⟩
  | initL2 _ _ ih =>
    exact ⟨fun y blk => by simpa only [v35_roots_set_same] using ih.1 y blk,
      fun y => by simpa only [v35_roots_set_same] using ih.2 y⟩

theorem LatestRootTimestampMonotoneMaxV35 : Properties.LatestRootTimestampMonotoneMaxV35 :=
  fun _ _ _ _ _ _ _ _ _ hr hX => runV35_roots hr hX

theorem runV35_refunded_latest {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S X Y log) (hX : RootsWf X) :
    ∀ a, CallV35.authorize a ∈ log → a.flow.deadline < (Y a.leg.chain).roots.latest := by
  induction hr with
  | refl => intro a ha; simp at ha
  | append _ _ ih =>
    intro a ha
    simp only [v35_roots_set_same]
    exact ih a (by simpa using ha)
  | @importRoot Y log c blk t _ _ _ ih =>
    intro a ha
    have := ih a ha
    rw [v35_roots_import]
    split_ifs with hy
    · rw [hy] at this
      simp only [Roots.import]
      exact lt_of_lt_of_le this (le_max_left _ _)
    · exact this
  | gate _ _ _ _ ih =>
    intro a ha
    simp only [v35_roots_set_same]
    exact ih a (by simpa using ha)
  | resume _ _ ih =>
    intro a ha
    simp only [v35_roots_set_same]
    exact ih a ha
  | @authorize Y log a' hr' hok _ ih =>
    intro a ha
    simp only [v35_roots_set_same]
    rcases List.mem_cons.mp ha with heq | hmem
    · obtain rfl : a = a' := by injection heq
      obtain ⟨blk, hblk⟩ := hok.2.2
      exact lt_of_lt_of_le hblk ((runV35_roots hr' hX).1 _ blk)
    · exact ih a hmem
  | claim _ _ ih =>
    intro a ha
    simp only [v35_roots_set_same]
    exact ih a ha
  | admin _ _ _ ih =>
    intro a ha
    simp only [v35_roots_set_same]
    exact ih a (by simpa using ha)
  | initL2 _ _ ih =>
    intro a ha
    simp only [v35_roots_set_same]
    exact ih a ha

theorem RefundedChainLatestPastDeadlineV35 : Properties.RefundedChainLatestPastDeadlineV35 :=
  fun _ _ _ _ _ _ _ _ _ hr hX => runV35_refunded_latest hr hX

theorem runV35_no_append_after_refund {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} {X Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S X Y log) (hX : RootsWf X) :
    ∀ (later : List CallV35) (a : AuthCall) (earlier : List CallV35),
      log = later ++ CallV35.authorize a :: earlier →
        ∀ (c : Chain) (F : Flow) (b : UInt256) (dest : Chain),
          CallV35.append c F b dest ∈ later → c = a.leg.chain → a.flow.deadline < F.deadline := by
  induction hr with
  | refl =>
    intro later a earlier hlog
    exact absurd hlog.symm (by simp)
  | @append Y log c' F' b' dest' hint low hr' ha ih =>
    intro later a earlier hlog c F b dest hmem hc
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, _⟩ | ⟨later', rfl, hlog'⟩
    · exact absurd hx (by simp)
    · rcases List.mem_cons.mp hmem with heq | hmem'
      · -- the new append is on the refunded chain
        simp only [CallV35.append.injEq] at heq
        obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
        have hauth : CallV35.authorize a ∈ log := by
          rw [hlog']; exact List.mem_append_right _ List.mem_cons_self
        have hlt := runV35_refunded_latest hr' hX a hauth
        rw [← hc] at hlt
        exact lt_of_lt_of_le hlt ha.notExpired
      · exact ih later' a earlier hlog' c F b dest hmem' hc
  | importRoot _ _ _ ih => exact ih
  | gate _ _ _ _ ih =>
    intro later a earlier hlog c F b dest hmem hc
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, _⟩ | ⟨later', rfl, hlog'⟩
    · exact absurd hx (by simp)
    · rcases List.mem_cons.mp hmem with heq | hmem'
      · exact absurd heq (by simp)
      · exact ih later' a earlier hlog' c F b dest hmem' hc
  | resume _ _ ih => exact ih
  | authorize _ _ _ _ ih =>
    intro later a earlier hlog c F b dest hmem hc
    rcases v35_cons_eq_append_cons hlog with ⟨rfl, _, _⟩ | ⟨later', rfl, hlog'⟩
    · simp at hmem
    · rcases List.mem_cons.mp hmem with heq | hmem'
      · exact absurd heq (by simp)
      · exact ih later' a earlier hlog' c F b dest hmem' hc
  | claim _ _ ih => exact ih
  | admin _ _ _ ih =>
    intro later a earlier hlog c F b dest hmem hc
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, _⟩ | ⟨later', rfl, hlog'⟩
    · exact absurd hx (by simp)
    · rcases List.mem_cons.mp hmem with heq | hmem'
      · exact absurd heq (by simp)
      · exact ih later' a earlier hlog' c F b dest hmem' hc
  | initL2 _ _ ih => exact ih

theorem NoAppendAfterRefundOnSameChainV35 : Properties.NoAppendAfterRefundOnSameChainV35 :=
  fun _ _ _ _ _ _ _ _ _ hr hX => runV35_no_append_after_refund hr hX

/-! ## The receive filter is read when a call runs -/

theorem runV35_hubs {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S X Y log) : Y.hubs = hubsAfter X.hubs log := by
  induction hr with
  | refl => rfl
  | append _ _ ih => simpa only [v35_hubs_set_same, hubsAfter_cons_append] using ih
  | importRoot _ _ _ ih => simpa only [v35_hubs_set_same] using ih
  | gate _ _ _ _ ih => simpa only [v35_hubs_set_same, hubsAfter_cons_gate] using ih
  | resume _ _ ih => simpa only [v35_hubs_set_same] using ih
  | authorize _ _ _ _ ih => simpa only [v35_hubs_set_same, hubsAfter_cons_authorize] using ih
  | claim _ _ ih => simpa only [v35_hubs_set_same] using ih
  | @admin Y log c op _ ih =>
    rw [hubsAfter_cons_admin]
    funext y
    by_cases hy : y = c
    · subst hy
      simp only [WorldV35.hubs, v35_set_self, ite_eq_left]
      rw [← ih]; rfl
    · simp only [WorldV35.hubs, v35_set_other _ _ hy, ite_eq_right hy]
      rw [← ih]; rfl
  | initL2 _ _ ih => simpa only [v35_hubs_set_same] using ih

theorem HubsAreReplayedAdminLogV35 : Properties.HubsAreReplayedAdminLogV35 :=
  fun _ _ _ _ _ _ _ _ _ hr => runV35_hubs hr

theorem runV35_gate_filter {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S X Y log) :
    ∀ (later : List CallV35) (d : Chain) (e : ExecCall) (earlier : List CallV35),
      log = later ++ CallV35.gate d e :: earlier →
        e.Verified h z0 hl cv fh S
          ∧ ∀ l ∈ e.flow.legs, SourceAllowed (hubsAfter X.hubs earlier d) d l.chain := by
  induction hr with
  | refl =>
    intro later d e earlier hlog
    exact absurd hlog.symm (by simp)
  | append _ _ ih =>
    intro later d e earlier hlog
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, _⟩ | ⟨later', _, hlog'⟩
    · exact absurd hx (by simp)
    · exact ih later' d e earlier hlog'
  | importRoot _ _ _ ih => exact ih
  | @gate Y log d' e' st hr' _ _ hok ih =>
    intro later d e earlier hlog
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, hlog'⟩ | ⟨later', _, hlog'⟩
    · simp only [CallV35.gate.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      subst hlog'
      refine ⟨hok.1, fun l hl' => ?_⟩
      have hhub : (Y d').hub = hubsAfter X.hubs log d' := congrFun (runV35_hubs hr') d'
      rw [← hhub]
      exact hok.2 l hl'
    · exact ih later' d e earlier hlog'
  | resume _ _ ih => exact ih
  | authorize _ _ _ _ ih =>
    intro later d e earlier hlog
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, _⟩ | ⟨later', _, hlog'⟩
    · exact absurd hx (by simp)
    · exact ih later' d e earlier hlog'
  | claim _ _ ih => exact ih
  | admin _ _ _ ih =>
    intro later d e earlier hlog
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, _⟩ | ⟨later', _, hlog'⟩
    · exact absurd hx (by simp)
    · exact ih later' d e earlier hlog'
  | initL2 _ _ ih => exact ih

theorem GateFilterHeldWhenLoggedV35 : Properties.GateFilterHeldWhenLoggedV35 :=
  fun _ _ _ _ _ _ _ _ _ hr => runV35_gate_filter hr

theorem runV35_refund_filter {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S X Y log) :
    ∀ (later : List CallV35) (a : AuthCall) (earlier : List CallV35),
      log = later ++ CallV35.authorize a :: earlier →
        a.Verified h z0 hl cv fh S
          ∧ SourceAllowed (hubsAfter X.hubs earlier a.leg.chain) a.leg.chain a.missing.chain := by
  induction hr with
  | refl =>
    intro later a earlier hlog
    exact absurd hlog.symm (by simp)
  | append _ _ ih =>
    intro later a earlier hlog
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, _⟩ | ⟨later', _, hlog'⟩
    · exact absurd hx (by simp)
    · exact ih later' a earlier hlog'
  | importRoot _ _ _ ih => exact ih
  | gate _ _ _ _ ih =>
    intro later a earlier hlog
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, _⟩ | ⟨later', _, hlog'⟩
    · exact absurd hx (by simp)
    · exact ih later' a earlier hlog'
  | resume _ _ ih => exact ih
  | @authorize Y log a' hr' hok _ ih =>
    intro later a earlier hlog
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, hlog'⟩ | ⟨later', _, hlog'⟩
    · obtain rfl : a' = a := by injection hx
      subst hlog'
      refine ⟨hok.1, ?_⟩
      have hhub : (Y a'.leg.chain).hub = hubsAfter X.hubs log a'.leg.chain :=
        congrFun (runV35_hubs hr') a'.leg.chain
      rw [← hhub]
      exact hok.2.1
    · exact ih later' a earlier hlog'
  | claim _ _ ih => exact ih
  | admin _ _ _ ih =>
    intro later a earlier hlog
    rcases v35_cons_eq_append_cons hlog with ⟨_, hx, _⟩ | ⟨later', _, hlog'⟩
    · exact absurd hx (by simp)
    · exact ih later' a earlier hlog'
  | initL2 _ _ ih => exact ih

theorem RefundFilterHeldWhenLoggedV35 : Properties.RefundFilterHeldWhenLoggedV35 :=
  fun _ _ _ _ _ _ _ _ _ hr => runV35_refund_filter hr

/-- After `deregister s` on `d`, replaying calls with no `allow s` on `d` keeps `s` disallowed
on `d`. -/
lemma hubsAfter_peer_deregistered (H : Chain → Hub) (d s : Chain) (earlier : List CallV35) :
    ∀ l1 : List CallV35, CallV35.admin d (.allow s) ∉ l1 →
      (hubsAfter H (l1 ++ CallV35.admin d (.deregister s) :: earlier) d).peer s = false
  | [], _ => by simp [hubsAfter_cons_admin, AdminOp.apply]
  | c :: l1, hno => by
    have ih := hubsAfter_peer_deregistered H d s earlier l1
      (fun hm => hno (List.mem_cons_of_mem _ hm))
    rw [List.cons_append]
    cases c with
    | append _ _ _ _ => simpa using ih
    | gate _ _ => simpa using ih
    | authorize _ => simpa using ih
    | admin c' op =>
      rw [hubsAfter_cons_admin]
      by_cases hc : d = c'
      · subst hc
        simp only [ite_eq_left]
        cases op with
        | allow s' =>
          have hs : s' ≠ s := fun hss => hno (by rw [hss]; exact List.mem_cons_self)
          simp only [AdminOp.apply, ite_eq_right (Ne.symm hs)]
          exact ih
        | deregister s' =>
          simp only [AdminOp.apply]
          split_ifs
          · rfl
          · exact ih
        | setBaseToken s' r =>
          simp only [AdminOp.apply]
          exact ih
      · simp only [ite_eq_right hc]
        exact ih

theorem DeregisteredPeerBlocksLaterGatesAndRefundsV35 :
    Properties.DeregisteredPeerBlocksLaterGatesAndRefundsV35 := by
  intro h z0 hl cv fh S X Y log hr later d s earlier hlog hsd hno
  constructor
  · intro e he l hl' hls
    obtain ⟨l2, l1, rfl⟩ := List.append_of_mem he
    have hlog2 : log = l2 ++ CallV35.gate d e :: (l1 ++ CallV35.admin d (.deregister s) :: earlier) := by
      rw [hlog]; simp
    have hf := (runV35_gate_filter hr l2 d e _ hlog2).2 l hl'
    have hpeer := hubsAfter_peer_deregistered X.hubs d s earlier l1
      (fun hm => hno (List.mem_append_right _ (List.mem_cons_of_mem _ hm)))
    rcases hf with h1 | h1
    · exact hsd (hls ▸ h1)
    · rw [hls, hpeer] at h1
      exact absurd h1 (by simp)
  · intro a ha hd hms
    obtain ⟨l2, l1, rfl⟩ := List.append_of_mem ha
    have hlog2 : log = l2 ++ CallV35.authorize a :: (l1 ++ CallV35.admin d (.deregister s) :: earlier) := by
      rw [hlog]; simp
    have hf := (runV35_refund_filter hr l2 a _ hlog2).2
    have hpeer := hubsAfter_peer_deregistered X.hubs d s earlier l1
      (fun hm => hno (List.mem_append_right _ (List.mem_cons_of_mem _ hm)))
    rw [hd, hms] at hf
    rcases hf with h1 | h1
    · exact hsd h1
    · rw [hpeer] at h1
      exact absurd h1 (by simp)

theorem runV35_status {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S X Y log) :
    ∀ (d : Chain) (b : UInt256), (X d).status b = .Unreceived → (Y d).status b ≠ .Unreceived →
      ∃ e, CallV35.gate d e ∈ log ∧ e.leg.bundleHash = b := by
  induction hr with
  | refl => intro d b h1 h2; exact absurd h1 h2
  | append _ _ ih =>
    intro d b h1 h2
    simp only [v35_status_set_same] at h2
    obtain ⟨e, he, hb⟩ := ih d b h1 h2
    exact ⟨e, List.mem_cons_of_mem _ he, hb⟩
  | importRoot _ _ _ ih =>
    intro d b h1 h2
    simp only [v35_status_set_same] at h2
    exact ih d b h1 h2
  | @gate Y log d' e' st _ _ _ _ ih =>
    intro d b h1 h2
    by_cases hdb : d = d' ∧ b = e'.leg.bundleHash
    · obtain ⟨rfl, rfl⟩ := hdb
      exact ⟨e', List.mem_cons_self, rfl⟩
    · have hst : ((Y.set d' { Y d' with status := setStatus (Y d').status e'.leg.bundleHash st })
          d).status b = (Y d).status b := by
        by_cases hd : d = d'
        · subst hd
          have hb : b ≠ e'.leg.bundleHash := fun hb => hdb ⟨rfl, hb⟩
          simp [setStatus, hb]
        · simp [v35_set_other _ _ hd]
      rw [hst] at h2
      obtain ⟨e, he, hb⟩ := ih d b h1 h2
      exact ⟨e, List.mem_cons_of_mem _ he, hb⟩
  | @resume Y log d' b' st' _ hedge ih =>
    intro d b h1 h2
    by_cases hdb : d = d' ∧ b = b'
    · obtain ⟨rfl, rfl⟩ := hdb
      have hne : (Y d).status b ≠ .Unreceived := by
        generalize (Y d).status b = s at hedge
        cases hedge <;> simp
      exact ih d b h1 hne
    · have hst : ((Y.set d' { Y d' with status := setStatus (Y d').status b' st' }) d).status b
          = (Y d).status b := by
        by_cases hd : d = d'
        · subst hd
          have hb : b ≠ b' := fun hb => hdb ⟨rfl, hb⟩
          simp [setStatus, hb]
        · simp [v35_set_other _ _ hd]
      rw [hst] at h2
      exact ih d b h1 h2
  | authorize _ _ _ _ ih =>
    intro d b h1 h2
    simp only [v35_status_set_same] at h2
    obtain ⟨e, he, hb⟩ := ih d b h1 h2
    exact ⟨e, List.mem_cons_of_mem _ he, hb⟩
  | claim _ _ ih =>
    intro d b h1 h2
    simp only [v35_status_set_same] at h2
    exact ih d b h1 h2
  | admin _ _ _ ih =>
    intro d b h1 h2
    simp only [v35_status_set_same] at h2
    obtain ⟨e, he, hb⟩ := ih d b h1 h2
    exact ⟨e, List.mem_cons_of_mem _ he, hb⟩
  | initL2 _ _ ih =>
    intro d b h1 h2
    simp only [v35_status_set_same] at h2
    exact ih d b h1 h2

theorem StatusLeavesUnreceivedOnlyThroughGateV35 :
    Properties.StatusLeavesUnreceivedOnlyThroughGateV35 :=
  fun _ _ _ _ _ _ _ _ _ hr => runV35_status hr

/-! ## The refund simplification -/

/-- The manager of a chain after a step that writes one key there. -/
lemma v35_mgr_set_key (Y : WorldV35) (c x : Chain) (s : ChainV35) (f b f' b' : UInt256)
    (st : LegState) (hs : s.base.mgr = (Y c).base.mgr.set f' b' st) :
    ((Y.set c s) x).base.mgr.legState f b
      = if x = c ∧ f = f' ∧ b = b' then st else (Y x).base.mgr.legState f b := by
  by_cases hx : x = c
  · subst hx
    simp only [v35_set_self, hs, Manager.set, true_and]
  · simp [v35_set_other _ _ hx, hx]

theorem runV35_set_key {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {H0 : Chain → Hub} {Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S (genesisV35 H0) Y log) :
    ∀ (x : Chain) (f b : UInt256), (Y x).base.mgr.legState f b ≠ .Unset →
      ∃ (F : Flow) (dest : Chain), CallV35.append x F b dest ∈ log ∧ F.flowId = f
        ∧ FlowIdChecked fh F ∧ (⟨x, b⟩ : FlowLeg) ∈ F.legs
        ∧ (F.legs.map FlowLeg.bundleHash).Pairwise (· < ·) := by
  induction hr with
  | refl => intro x f b hne; exact absurd rfl hne
  | @append Y log c F b' dest hint low _ ha ih =>
    intro x f b hne
    rw [v35_mgr_set_key Y c x _ f b F.flowId b' .Committed rfl] at hne
    by_cases hk : x = c ∧ f = F.flowId ∧ b = b'
    · obtain ⟨rfl, rfl, rfl⟩ := hk
      exact ⟨F, dest, List.mem_cons_self, rfl, ha.flowId, ha.isLegHere, ha.sorted⟩
    · rw [ite_eq_right hk] at hne
      obtain ⟨F', d', hm, h1, h2, h3, h4⟩ := ih x f b hne
      exact ⟨F', d', List.mem_cons_of_mem _ hm, h1, h2, h3, h4⟩
  | importRoot _ _ _ ih =>
    intro x f b hne
    simp only [v35_mgr_set_same] at hne
    exact ih x f b hne
  | gate _ _ _ _ ih =>
    intro x f b hne
    simp only [v35_mgr_set_same] at hne
    obtain ⟨F', d', hm, h1, h2, h3, h4⟩ := ih x f b hne
    exact ⟨F', d', List.mem_cons_of_mem _ hm, h1, h2, h3, h4⟩
  | resume _ _ ih =>
    intro x f b hne
    simp only [v35_mgr_set_same] at hne
    exact ih x f b hne
  | @authorize Y log a _ _ hg ih =>
    intro x f b hne
    rw [v35_mgr_set_key Y a.leg.chain x _ f b a.flow.flowId a.leg.bundleHash .Revertable rfl]
      at hne
    have hold : (Y x).base.mgr.legState f b ≠ .Unset := by
      by_cases hk : x = a.leg.chain ∧ f = a.flow.flowId ∧ b = a.leg.bundleHash
      · obtain ⟨rfl, rfl, rfl⟩ := hk
        unfold AuthorizeGuard at hg
        rw [hg]; simp
      · rwa [ite_eq_right hk] at hne
    obtain ⟨F', d', hm, h1, h2, h3, h4⟩ := ih x f b hold
    exact ⟨F', d', List.mem_cons_of_mem _ hm, h1, h2, h3, h4⟩
  | @claim Y log c f' b' _ hg ih =>
    intro x f b hne
    rw [v35_mgr_set_key Y c x _ f b f' b' .Reverted rfl] at hne
    have hold : (Y x).base.mgr.legState f b ≠ .Unset := by
      by_cases hk : x = c ∧ f = f' ∧ b = b'
      · obtain ⟨rfl, rfl, rfl⟩ := hk
        unfold ClaimGuard at hg
        rw [hg]; simp
      · rwa [ite_eq_right hk] at hne
    exact ih x f b hold
  | admin _ _ _ ih =>
    intro x f b hne
    simp only [v35_mgr_set_same] at hne
    obtain ⟨F', d', hm, h1, h2, h3, h4⟩ := ih x f b hne
    exact ⟨F', d', List.mem_cons_of_mem _ hm, h1, h2, h3, h4⟩
  | initL2 _ _ ih =>
    intro x f b hne
    simp only [v35_mgr_set_same] at hne
    exact ih x f b hne

theorem SetKeyHasLoggedAppendV35 : Properties.SetKeyHasLoggedAppendV35 :=
  fun _ _ _ _ _ _ _ _ _ hr => runV35_set_key hr

theorem runV35_appended_once {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {H0 : Chain → Hub} {Y : WorldV35} {log : List CallV35}
    (hr : RunV35 h z0 hl cv fh S (genesisV35 H0) Y log) :
    (appendLog log).Nodup
      ∧ ∀ o ∈ appendLog log, (Y o.chain).base.mgr.legState o.flowId o.bundleHash ≠ .Unset := by
  induction hr with
  | refl => exact ⟨List.nodup_nil, fun o ho => by simp [appendLog] at ho⟩
  | @append Y log c F b dest hint low _ ha ih =>
    obtain ⟨hnd, hset⟩ := ih
    rw [appendLog_cons_append]
    refine ⟨List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩, fun o ho => ?_⟩
    · exact hset _ hmem ha.legUnset
    · rw [v35_mgr_set_key Y c o.chain _ o.flowId o.bundleHash F.flowId b .Committed rfl]
      split_ifs with hk
      · simp
      · rcases List.mem_cons.mp ho with rfl | ho'
        · exact absurd ⟨rfl, rfl, rfl⟩ hk
        · exact hset o ho'
  | importRoot _ _ _ ih =>
    refine ⟨ih.1, fun o ho => ?_⟩
    simp only [v35_mgr_set_same]
    exact ih.2 o ho
  | gate _ _ _ _ ih =>
    rw [appendLog_cons_gate]
    refine ⟨ih.1, fun o ho => ?_⟩
    simp only [v35_mgr_set_same]
    exact ih.2 o ho
  | resume _ _ ih =>
    refine ⟨ih.1, fun o ho => ?_⟩
    simp only [v35_mgr_set_same]
    exact ih.2 o ho
  | @authorize Y log a _ _ hg ih =>
    rw [appendLog_cons_authorize]
    refine ⟨ih.1, fun o ho => ?_⟩
    rw [v35_mgr_set_key Y a.leg.chain o.chain _ o.flowId o.bundleHash a.flow.flowId
      a.leg.bundleHash .Revertable rfl]
    split_ifs
    · simp
    · exact ih.2 o ho
  | @claim Y log c f b _ hg ih =>
    refine ⟨ih.1, fun o ho => ?_⟩
    rw [v35_mgr_set_key Y c o.chain _ o.flowId o.bundleHash f b .Reverted rfl]
    split_ifs
    · simp
    · exact ih.2 o ho
  | admin _ _ _ ih =>
    rw [appendLog_cons_admin]
    refine ⟨ih.1, fun o ho => ?_⟩
    simp only [v35_mgr_set_same]
    exact ih.2 o ho
  | initL2 _ _ ih =>
    refine ⟨ih.1, fun o ho => ?_⟩
    simp only [v35_mgr_set_same]
    exact ih.2 o ho

theorem AppendedAtMostOnceV35 : Properties.AppendedAtMostOnceV35 :=
  fun _ _ _ _ _ _ _ _ _ hr => runV35_appended_once hr

/-- In a flow with strictly ascending bundle hashes, a bundle hash is declared on one chain. -/
lemma v35_chain_unique_of_sorted :
    ∀ {L : List FlowLeg}, (L.map FlowLeg.bundleHash).Pairwise (· < ·) →
      ∀ {x y : Chain} {b : UInt256}, (⟨x, b⟩ : FlowLeg) ∈ L → (⟨y, b⟩ : FlowLeg) ∈ L → x = y
  | [], _, _, _, _, hx, _ => absurd hx List.not_mem_nil
  | l :: L, hs, x, y, b, hx, hy => by
    rw [List.map_cons, List.pairwise_cons] at hs
    obtain ⟨hlt, hs'⟩ := hs
    have hnot : ∀ z, (⟨z, b⟩ : FlowLeg) ∈ L → l.bundleHash ≠ b := by
      intro z hz heq
      have := hlt b (List.mem_map.mpr ⟨⟨z, b⟩, hz, rfl⟩)
      rw [heq] at this
      exact lt_irrefl _ this
    rcases List.mem_cons.mp hx with hx1 | hx'
    · rcases List.mem_cons.mp hy with hy1 | hy'
      · rw [← hx1] at hy1
        injection hy1 with h1
        exact h1.symm
      · exact absurd (by rw [← hx1]) (hnot y hy')
    · rcases List.mem_cons.mp hy with hy1 | hy'
      · exact absurd (by rw [← hy1]) (hnot x hx')
      · exact v35_chain_unique_of_sorted hs' hx' hy'

theorem CodeAuthorizeMarksDeclaredLegOrLoggedClashV35 :
    Properties.CodeAuthorizeMarksDeclaredLegOrLoggedClashV35 := by
  intro h z0 hl cv fh S H0 Y log hr x F l hF hl' hcom
  have hne : (Y x).base.mgr.legState F.flowId l.bundleHash ≠ .Unset := by rw [hcom]; simp
  obtain ⟨F', dest, hm, hid, hF', hx, hs⟩ := runV35_set_key hr x F.flowId l.bundleHash hne
  by_cases hlx : l.chain = x
  · exact Or.inl hlx
  · refine Or.inr ⟨F', dest, hm, ?_, ?_⟩
    · intro heq
      have hlegs : F.legs = F'.legs := congrArg Prod.fst heq
      have hl2 : (⟨l.chain, l.bundleHash⟩ : FlowLeg) ∈ F'.legs := by rw [← hlegs]; exact hl'
      exact hlx (v35_chain_unique_of_sorted hs hl2 hx)
    · show fh F.legs F.deadline = fh F'.legs F'.deadline
      rw [hF, hF', hid]

/-! ## One code `authorizeRefund` call as model steps -/

lemma v35_set_set (W : WorldV35) (c : Chain) (x x' : ChainV35) :
    (W.set c x).set c x' = W.set c x' := by
  funext y
  by_cases hy : y = c <;> simp [WorldV35.set, hy]

lemma v35_set_eta (W : WorldV35) (c : Chain) : W.set c (W c) = W := by
  funext y
  by_cases hy : y = c
  · subst hy; simp [WorldV35.set]
  · simp [WorldV35.set, hy]

/-- The marking loop, run over the legs `L` of the presented flow: one `authorize` step per key
that is `Committed` when the loop reaches it.  The steps change only chain `x`'s manager, so the
filter and the root check read the same state at every step, and the keys of later legs, whose
bundle hashes differ, are untouched. -/
theorem runV35_code_marks {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X : WorldV35} {x : Chain} {F : Flow} {m : FlowLeg} {N : ℕ}
    {p : ImtProof} (hF : FlowIdChecked fh F) (hm : m ∈ F.legs)
    (hrf : LegRefundableBy h z0 hl cv S F m N p) :
    ∀ (L : List FlowLeg), (∀ l ∈ L, l ∈ F.legs) → (L.map FlowLeg.bundleHash).Pairwise (· < ·) →
    ∀ (Z : WorldV35) (logZ : List CallV35), RunV35 h z0 hl cv fh S X Z logZ →
      SourceAllowed (Z x).hub x m.chain → (∃ blk, F.deadline < (Z x).roots.stored blk) →
      (∀ l ∈ L, (Z x).base.mgr.legState F.flowId l.bundleHash = .Committed → l.chain = x) →
        ∃ steps : List CallV35,
          (∀ c ∈ steps, ∃ l ∈ L, l.chain = x ∧ c = CallV35.authorize ⟨F, l, m, N, p⟩)
          ∧ RunV35 h z0 hl cv fh S X
              (Z.set x { Z x with base :=
                ⟨RefundClosesAppend.markCommittedRevertable (Z x).base.mgr F.flowId
                    (L.map FlowLeg.bundleHash), (Z x).base.tree⟩ })
              (steps ++ logZ) := by
  intro L
  induction L with
  | nil =>
    intro _ _ Z logZ hr _ _ _
    refine ⟨[], fun c hc => absurd hc List.not_mem_nil, ?_⟩
    have hZ : Z.set x { Z x with base :=
        ⟨RefundClosesAppend.markCommittedRevertable (Z x).base.mgr F.flowId
          (([] : List FlowLeg).map FlowLeg.bundleHash), (Z x).base.tree⟩ } = Z := by
      simp only [List.map_nil, RefundClosesAppend.markCommittedRevertable]
      exact v35_set_eta Z x
    rw [hZ, List.nil_append]
    exact hr
  | cons l L ih =>
    intro hsub hsort Z logZ hr hsrc hroot hdecl
    rw [List.map_cons, List.pairwise_cons] at hsort
    obtain ⟨hlt, hsort'⟩ := hsort
    have hlF : l ∈ F.legs := hsub l List.mem_cons_self
    have hsub' : ∀ l' ∈ L, l' ∈ F.legs := fun l' hl' => hsub l' (List.mem_cons_of_mem _ hl')
    have hne : ∀ l' ∈ L, l'.bundleHash ≠ l.bundleHash := by
      intro l' hl' heq
      have := hlt l'.bundleHash (List.mem_map.mpr ⟨l', hl', rfl⟩)
      rw [heq] at this
      exact lt_irrefl _ this
    by_cases hc : (Z x).base.mgr.legState F.flowId l.bundleHash = .Committed
    · -- the loop marks `l`: one model step on `x`, then the rest of the legs
      have hlx : l.chain = x := hdecl l List.mem_cons_self hc
      subst hlx
      have hr' : RunV35 h z0 hl cv fh S X
          (Z.set l.chain { Z l.chain with
            base := ⟨(Z l.chain).base.mgr.set F.flowId l.bundleHash .Revertable,
              (Z l.chain).base.tree⟩ })
          (CallV35.authorize ⟨F, l, m, N, p⟩ :: logZ) :=
        RunV35.authorize ⟨F, l, m, N, p⟩ hr ⟨⟨hF, hlF, hm, hrf⟩, hsrc, hroot⟩ hc
      obtain ⟨steps, hsteps, hrun⟩ := ih hsub' hsort' _ _ hr'
        (by simpa only [v35_set_self] using hsrc) (by simpa only [v35_set_self] using hroot)
        (by
          intro l' hl' hc'
          simp [v35_set_self, Manager.set, hne l' hl'] at hc'
          exact hdecl l' (List.mem_cons_of_mem _ hl') hc')
      refine ⟨steps ++ [CallV35.authorize ⟨F, l, m, N, p⟩], fun c hc' => ?_, ?_⟩
      · rcases List.mem_append.mp hc' with hc' | hc'
        · obtain ⟨l', hl', h1, h2⟩ := hsteps c hc'
          exact ⟨l', List.mem_cons_of_mem _ hl', h1, h2⟩
        · rw [List.mem_singleton] at hc'
          exact ⟨l, List.mem_cons_self, rfl, hc'⟩
      · rw [List.append_assoc, List.singleton_append]
        rw [v35_set_set, v35_set_self] at hrun
        have hmark : RefundClosesAppend.markCommittedRevertable (Z l.chain).base.mgr F.flowId
            ((l :: L).map FlowLeg.bundleHash)
            = RefundClosesAppend.markCommittedRevertable
                ((Z l.chain).base.mgr.set F.flowId l.bundleHash .Revertable) F.flowId
                (L.map FlowLeg.bundleHash) := by
          simp only [List.map_cons, RefundClosesAppend.markCommittedRevertable, hc, ↓reduceIte]
        rw [hmark]
        exact hrun
    · -- the loop skips `l`
      obtain ⟨steps, hsteps, hrun⟩ := ih hsub' hsort' Z logZ hr hsrc hroot
        (fun l' hl' => hdecl l' (List.mem_cons_of_mem _ hl'))
      refine ⟨steps, fun c hc' => ?_, ?_⟩
      · obtain ⟨l', hl', h1, h2⟩ := hsteps c hc'
        exact ⟨l', List.mem_cons_of_mem _ hl', h1, h2⟩
      · have hmark : RefundClosesAppend.markCommittedRevertable (Z x).base.mgr F.flowId
            ((l :: L).map FlowLeg.bundleHash)
            = RefundClosesAppend.markCommittedRevertable (Z x).base.mgr F.flowId
                (L.map FlowLeg.bundleHash) := by
          simp only [List.map_cons, RefundClosesAppend.markCommittedRevertable, hc, ↓reduceIte]
        rw [hmark]
        exact hrun

theorem CodeAuthorizeCallIsAuthorizeStepsV35 :
    Properties.CodeAuthorizeCallIsAuthorizeStepsV35 := by
  intro h z0 hl cv fh S H0 Y log hr x F m N p hF hsort hm hrf hsrc hroot hnoclash
  have hdecl : ∀ l ∈ F.legs,
      (Y x).base.mgr.legState F.flowId l.bundleHash = .Committed → l.chain = x := by
    intro l hlF hc
    rcases CodeAuthorizeMarksDeclaredLegOrLoggedClashV35 h z0 hl cv fh S H0 Y log hr x F l hF hlF hc
      with h1 | ⟨F', dest, hmem, hcl⟩
    · exact h1
    · exact absurd hcl (hnoclash l hlF F' dest hmem)
  exact runV35_code_marks hF hm hrf F.legs (fun _ hl' => hl') hsort Y log hr hsrc hroot hdecl

/-! ## Witnesses

The worlds of the witness runs are named, one per step, so that every check on them is a closed
computation.  Each is the world the corresponding `RunV35` constructor produces. -/

/-- The common start: genesis, no peers anywhere. -/
def v35W0 : WorldV35 := genesisV35 (fun _ => v35ClosedHub)

/-- Chain `1` allows peer `0`. -/
def v35W1 : WorldV35 := v35W0.set 1 { v35W0 1 with hub := (AdminOp.allow 0).apply (v35W0 1).hub }

/-! ### The refund-then-append run -/

/-- Chain `0` allows peer `1`. -/
def v35RefundW2 : WorldV35 :=
  v35W1.set 0 { v35W1 0 with hub := (AdminOp.allow 1).apply (v35W1 0).hub }

/-- Chain `1` appends leg `⟨1, 2⟩` of `v35RefundFlow`. -/
def v35RefundW3 : WorldV35 :=
  v35RefundW2.set 1
    { v35RefundW2 1 with base := (v35RefundW2 1).base.appended v35BundleCv v35RefundFlow.flowId 2 0 }

/-- Chain `1` imports an L1 root with timestamp `1` at block `0`. -/
def v35RefundW4 : WorldV35 :=
  v35RefundW3.set 1 { v35RefundW3 1 with roots := (v35RefundW3 1).roots.import 0 1 }

/-- Chain `1` marks `(1, 2)` `Revertable`. -/
def v35RefundW5 : WorldV35 :=
  v35RefundW4.set 1 { v35RefundW4 1 with
    base := ⟨(v35RefundW4 1).base.mgr.set v35RefundFlow.flowId 2 .Revertable,
      (v35RefundW4 1).base.tree⟩ }

/-- Chain `0` appends leg `⟨0, 1⟩` of `v35RefundFlow`. -/
def v35RefundW6 : WorldV35 :=
  v35RefundW5.set 0
    { v35RefundW5 0 with base := (v35RefundW5 0).base.appended v35BundleCv v35RefundFlow.flowId 1 0 }

/-- Chain `1` appends leg `⟨1, 4⟩` of `v35LaterFlow`, landing on leaf `1`. -/
def v35RefundW7 : WorldV35 :=
  v35RefundW6.set 1
    { v35RefundW6 1 with base := (v35RefundW6 1).base.appended v35BundleCv v35LaterFlow.flowId 4 1 }

/-- The absence proof for leg `⟨1, 3⟩` of `v35RefundFlow`: chain `1` never commits in
`mixedSystem 1`, and batch `1` settled after the deadline `0`. -/
lemma v35_refund_leg13 (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ N p, LegRefundableBy h z0 hl v35BundleCv (mixedSystem 1) v35RefundFlow ⟨1, 3⟩ N p := by
  obtain ⟨N, p, href⟩ := (subset_flow_passes_unchecked_gate (h := h) (z0 := z0) (hl := hl)
    (cv := v35BundleCv) (id := 1) (hA := 1) (hB := 3) (by decide) (by decide)).2.2
  exact ⟨N, p, href⟩

/-- The absence proof for leg `⟨2, 4⟩` of `v35SameChainLegsFlow`: chain `2` never commits in
`mixedSystem 1`, and batch `1` settled after the deadline `0`. -/
lemma v35_refund_leg24 (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ N p, LegRefundableBy h z0 hl v35BundleCv (mixedSystem 1) v35SameChainLegsFlow ⟨2, 4⟩ N p := by
  have hb : (0 : UInt256) < 4 := by decide
  obtain ⟨ℓ, idx, habs⟩ :=
    non_inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := setup) (height := 0)
      setup_valid (by norm_num [setup]) (ne_of_gt hb) (not_mem_setup hb)
  refine ⟨1, ⟨ℓ, idx, honestSibs h z0 (leafHashes hl setup) idx, 0⟩, Or.inl ⟨?_, ?_⟩⟩
  · show (0 : ℕ) < (mixedSystem 1).time 2 1
    simp
  · show AbsenceAccepted h z0 hl ((mixedSystem 1).tree 2 0) ((mixedSystem 1).height 2 0) 4 _
    rw [mixedSystem_tree_other (by decide : (2 : Chain) ≠ 0),
      mixedSystem_height_other (by decide : (2 : Chain) ≠ 0)]
    exact habs

/-- `subsetFlow 0 1` executes on honest evidence in `mixedSystem 1` under `v35BundleCv`. -/
lemma v35_subset_executes (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ExecutedViaBy h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) (subsetFlow 0 1)
      (fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1)) ⟨0, 1⟩ := by
  have hex := (subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset).1
  refine ⟨hex.1, hex.2.1, ?_⟩
  intro l hl'
  obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
  exact hex.2.2 _ hl'

/-- The refund call of the refund-then-append run. -/
def v35RefundCall (N : ℕ) (p : ImtProof) : AuthCall := ⟨v35RefundFlow, ⟨1, 2⟩, ⟨1, 3⟩, N, p⟩

/-- The log of the refund-then-append run. -/
def v35RefundLog (N : ℕ) (p : ImtProof) : List CallV35 :=
  [.append 1 v35LaterFlow 4 0, .append 0 v35RefundFlow 1 1, .authorize (v35RefundCall N p),
    .append 1 v35RefundFlow 2 0, .admin 0 (.allow 1), .admin 1 (.allow 0)]

theorem v35_refund_run (h : Hash) (z0 : UInt256) (hl : LeafHash) (N : ℕ) (p : ImtProof)
    (href : LegRefundableBy h z0 hl v35BundleCv (mixedSystem 1) v35RefundFlow ⟨1, 3⟩ N p) :
    RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35RefundW7
      (v35RefundLog N p) := by
  have r1 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35W1
      [.admin 1 (.allow 0)] := RunV35.admin 1 (.allow 0) RunV35.refl
  have r2 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35RefundW2
      [.admin 0 (.allow 1), .admin 1 (.allow 0)] := RunV35.admin 0 (.allow 1) r1
  have hok3 : AppendOkV35 v35BundleCv lengthFlowHash (v35RefundW2 1) 1 v35RefundFlow 2 0 0 0 :=
    ⟨by decide, by decide, by unfold FlowIdChecked; decide, by decide, by decide, by decide,
      by decide, by decide, by unfold AppendGuard; decide,
      ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, ⟨0, by decide⟩⟩⟩
  have r3 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35RefundW3
      [.append 1 v35RefundFlow 2 0, .admin 0 (.allow 1), .admin 1 (.allow 0)] :=
    RunV35.append (c := 1) (F := v35RefundFlow) (b := 2) (dest := 0) (hint := 0) (low := 0) r2 hok3
  have r4 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35RefundW4
      [.append 1 v35RefundFlow 2 0, .admin 0 (.allow 1), .admin 1 (.allow 0)] :=
    RunV35.importRoot (c := 1) (blk := 0) (t := 1) r3 (by decide) (by decide)
  have hok5 : AuthorizeOkV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) (v35RefundW4 1)
      (v35RefundCall N p) := by
    refine ⟨⟨?_, ?_, ?_, href⟩, Or.inl rfl, ⟨0, ?_⟩⟩
    · show FlowIdChecked lengthFlowHash v35RefundFlow
      unfold FlowIdChecked; decide
    · show (⟨1, 2⟩ : FlowLeg) ∈ v35RefundFlow.legs
      decide
    · show (⟨1, 3⟩ : FlowLeg) ∈ v35RefundFlow.legs
      decide
    · show v35RefundFlow.deadline < (v35RefundW4 1).roots.stored 0
      decide
  have hg5 : AuthorizeGuard (v35RefundW4 1).base.mgr v35RefundFlow.flowId 2 := by
    unfold AuthorizeGuard; decide
  have r5 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35RefundW5
      [.authorize (v35RefundCall N p), .append 1 v35RefundFlow 2 0, .admin 0 (.allow 1),
        .admin 1 (.allow 0)] :=
    RunV35.authorize (v35RefundCall N p) r4 hok5 hg5
  have hok6 : AppendOkV35 v35BundleCv lengthFlowHash (v35RefundW5 0) 0 v35RefundFlow 1 1 0 0 :=
    ⟨by decide, by decide, by unfold FlowIdChecked; decide, by decide, by decide, by decide,
      by decide, by decide, by unfold AppendGuard; decide,
      ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, ⟨0, by decide⟩⟩⟩
  have r6 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35RefundW6
      [.append 0 v35RefundFlow 1 1, .authorize (v35RefundCall N p), .append 1 v35RefundFlow 2 0,
        .admin 0 (.allow 1), .admin 1 (.allow 0)] :=
    RunV35.append (c := 0) (F := v35RefundFlow) (b := 1) (dest := 1) (hint := 0) (low := 0) r5 hok6
  have hok7 : AppendOkV35 v35BundleCv lengthFlowHash (v35RefundW6 1) 1 v35LaterFlow 4 0 0 1 :=
    ⟨by decide, by decide, by unfold FlowIdChecked; decide, by decide, by decide, by decide,
      by decide, by decide, by unfold AppendGuard; decide,
      ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, ⟨1, by decide⟩⟩⟩
  exact RunV35.append (c := 1) (F := v35LaterFlow) (b := 4) (dest := 0) (hint := 0) (low := 1)
    r6 hok7

lemma v35W0_rootsWf : RootsWf v35W0 := fun _ _ => Nat.le_refl _

theorem RefundThenAppendWitnessV35 : Properties.RefundThenAppendWitnessV35 := by
  intro h z0 hl
  obtain ⟨N, p, href⟩ := v35_refund_leg13 h z0 hl
  have r := v35_refund_run h z0 hl N p href
  refine ⟨v35RefundW7, v35RefundCall N p, rfl, rfl, rfl, r, rfl, v35W0_rootsWf, by decide,
    by unfold FlowIdChecked; decide, by decide, ?_, by decide, by unfold FlowIdChecked; decide,
    by decide, List.mem_cons_of_mem _ List.mem_cons_self, by unfold FlowIdClash; decide⟩
  · rintro ⟨F', dest, hmem, hcl⟩
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
    rcases hmem with h1 | h1 | h1 | h1 | h1 | h1
    · simp only [CallV35.append.injEq] at h1
      obtain ⟨-, rfl, -, -⟩ := h1
      exact hcl.1 rfl
    · simp only [CallV35.append.injEq] at h1
      exact absurd h1.1 (by decide)
    · cases h1
    · simp only [CallV35.append.injEq] at h1
      exact absurd h1.2.2.1 (by decide)
    · cases h1
    · cases h1

theorem WithoutDeadlineGateAppendAfterRefundV35 :
    Properties.WithoutDeadlineGateAppendAfterRefundV35 := by
  intro h z0 hl
  obtain ⟨N, p, href⟩ := v35_refund_leg13 h z0 hl
  refine ⟨v35RefundW7, v35RefundCall N p, rfl, rfl, rfl, v35_refund_run h z0 hl N p href, ?_, ?_⟩
  · exact ⟨by decide, by decide, by unfold FlowIdChecked; decide, by decide, by decide, by decide,
      by decide, by unfold AppendGuard; decide,
      ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, ⟨1, by decide⟩⟩⟩
  · intro hint low hok
    exact absurd hok.notExpired (by decide)

/-! ### The verify, deregister, execute run -/

/-- The gate call on chain `1` (and on chain `0` in the deregistration witness). -/
def v35ExecCall (h : Hash) (z0 : UInt256) (hl : LeafHash) : ExecCall :=
  ⟨subsetFlow 0 1, fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1), ⟨0, 1⟩⟩

/-- Chain `1` verifies bundle `1`. -/
def v35ExecW2 : WorldV35 :=
  v35W1.set 1 { v35W1 1 with status := setStatus (v35W1 1).status 1 .Verified }

/-- Chain `1` deregisters peer `0`. -/
def v35ExecW3 : WorldV35 :=
  v35ExecW2.set 1 { v35ExecW2 1 with hub := (AdminOp.deregister 0).apply (v35ExecW2 1).hub }

/-- Chain `1` executes the `Verified` bundle `1`. -/
def v35ExecW4 : WorldV35 :=
  v35ExecW3.set 1 { v35ExecW3 1 with status := setStatus (v35ExecW3 1).status 1 .FullyExecuted }

theorem VerifiedBundleExecutesAfterDeregistrationV35 :
    Properties.VerifiedBundleExecutesAfterDeregistrationV35 := by
  intro h z0 hl
  have hex := v35_subset_executes h z0 hl
  have r1 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35W1
      [.admin 1 (.allow 0)] := RunV35.admin 1 (.allow 0) RunV35.refl
  have hgate : GateOkV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) (v35W1 1) 1
      (v35ExecCall h z0 hl) := by
    refine ⟨hex, fun l hl' => ?_⟩
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    decide
  have r2 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ExecW2
      [.gate 1 (v35ExecCall h z0 hl), .admin 1 (.allow 0)] :=
    RunV35.gate (d := 1) (e := v35ExecCall h z0 hl) (st := .Verified) r1
      (show (v35W1 1).status 1 = .Unreceived by decide) (Or.inl rfl) hgate
  have r3 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ExecW3
      [.admin 1 (.deregister 0), .gate 1 (v35ExecCall h z0 hl), .admin 1 (.allow 0)] :=
    RunV35.admin 1 (.deregister 0) r2
  have hedge : NoGateEdge ((v35ExecW3 1).status 1) .FullyExecuted := by
    rw [show (v35ExecW3 1).status 1 = .Verified by decide]
    exact NoGateEdge.execute
  have r4 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ExecW4
      [.admin 1 (.deregister 0), .gate 1 (v35ExecCall h z0 hl), .admin 1 (.allow 0)] :=
    RunV35.resume (d := 1) (b := 1) (st' := .FullyExecuted) r3 hedge
  have hnot : ¬ SourceAllowed (v35ExecW4 1).hub 1 0 := by decide
  refine ⟨v35ExecW3, v35ExecW4, v35ExecCall h z0 hl, rfl, rfl, r3, rfl, by decide, by decide,
    hedge, rfl, r4, by decide, hnot, ?_, by simp⟩
  intro hg
  exact hnot (hg.2 ⟨0, 1⟩ List.mem_cons_self)

/-! ### An executed obligation next to a refunded one -/

/-- Chain `0` appends leg `⟨0, 1⟩` of `subsetFlow 0 1`. -/
def v35ExObW3 : WorldV35 :=
  v35RefundW2.set 0
    { v35RefundW2 0 with
      base := (v35RefundW2 0).base.appended v35BundleCv (subsetFlow 0 1).flowId 1 0 }

/-- Chain `1` appends leg `⟨1, 2⟩` of `v35RefundFlow`. -/
def v35ExObW4 : WorldV35 :=
  v35ExObW3.set 1
    { v35ExObW3 1 with base := (v35ExObW3 1).base.appended v35BundleCv v35RefundFlow.flowId 2 0 }

/-- Chain `1` imports an L1 root with timestamp `1` at block `0`. -/
def v35ExObW5 : WorldV35 :=
  v35ExObW4.set 1 { v35ExObW4 1 with roots := (v35ExObW4 1).roots.import 0 1 }

/-- Chain `1` marks `(1, 2)` `Revertable`. -/
def v35ExObW6 : WorldV35 :=
  v35ExObW5.set 1 { v35ExObW5 1 with
    base := ⟨(v35ExObW5 1).base.mgr.set v35RefundFlow.flowId 2 .Revertable,
      (v35ExObW5 1).base.tree⟩ }

/-- Chain `1` executes bundle `1`. -/
def v35ExObW7 : WorldV35 :=
  v35ExObW6.set 1 { v35ExObW6 1 with status := setStatus (v35ExObW6 1).status 1 .FullyExecuted }

theorem ExecutedObligationStaysCommittedWitnessV35 :
    Properties.ExecutedObligationStaysCommittedWitnessV35 := by
  intro h z0 hl
  obtain ⟨N, p, href⟩ := v35_refund_leg13 h z0 hl
  have r1 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35W1
      [.admin 1 (.allow 0)] := RunV35.admin 1 (.allow 0) RunV35.refl
  have r2 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35RefundW2
      [.admin 0 (.allow 1), .admin 1 (.allow 0)] := RunV35.admin 0 (.allow 1) r1
  have hok3 : AppendOkV35 v35BundleCv lengthFlowHash (v35RefundW2 0) 0 (subsetFlow 0 1) 1 1 0 0 :=
    ⟨by decide, by decide, by unfold FlowIdChecked; decide, by decide, by decide, by decide,
      by decide, by decide, by unfold AppendGuard; decide,
      ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, ⟨0, by decide⟩⟩⟩
  have r3 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ExObW3
      [.append 0 (subsetFlow 0 1) 1 1, .admin 0 (.allow 1), .admin 1 (.allow 0)] :=
    RunV35.append (c := 0) (F := subsetFlow 0 1) (b := 1) (dest := 1) (hint := 0) (low := 0) r2
      hok3
  have hok4 : AppendOkV35 v35BundleCv lengthFlowHash (v35ExObW3 1) 1 v35RefundFlow 2 0 0 0 :=
    ⟨by decide, by decide, by unfold FlowIdChecked; decide, by decide, by decide, by decide,
      by decide, by decide, by unfold AppendGuard; decide,
      ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, ⟨0, by decide⟩⟩⟩
  have r4 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ExObW4
      [.append 1 v35RefundFlow 2 0, .append 0 (subsetFlow 0 1) 1 1, .admin 0 (.allow 1),
        .admin 1 (.allow 0)] :=
    RunV35.append (c := 1) (F := v35RefundFlow) (b := 2) (dest := 0) (hint := 0) (low := 0) r3 hok4
  have r5 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ExObW5
      [.append 1 v35RefundFlow 2 0, .append 0 (subsetFlow 0 1) 1 1, .admin 0 (.allow 1),
        .admin 1 (.allow 0)] :=
    RunV35.importRoot (c := 1) (blk := 0) (t := 1) r4 (by decide) (by decide)
  have hok6 : AuthorizeOkV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) (v35ExObW5 1)
      (v35RefundCall N p) := by
    refine ⟨⟨?_, ?_, ?_, href⟩, Or.inl rfl, ⟨0, ?_⟩⟩
    · show FlowIdChecked lengthFlowHash v35RefundFlow
      unfold FlowIdChecked; decide
    · show (⟨1, 2⟩ : FlowLeg) ∈ v35RefundFlow.legs
      decide
    · show (⟨1, 3⟩ : FlowLeg) ∈ v35RefundFlow.legs
      decide
    · show v35RefundFlow.deadline < (v35ExObW5 1).roots.stored 0
      decide
  have hg6 : AuthorizeGuard (v35ExObW5 1).base.mgr v35RefundFlow.flowId 2 := by
    unfold AuthorizeGuard; decide
  have r6 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ExObW6
      [.authorize (v35RefundCall N p), .append 1 v35RefundFlow 2 0, .append 0 (subsetFlow 0 1) 1 1,
        .admin 0 (.allow 1), .admin 1 (.allow 0)] :=
    RunV35.authorize (v35RefundCall N p) r5 hok6 hg6
  have hex := v35_subset_executes h z0 hl
  have hgate : GateOkV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) (v35ExObW6 1) 1
      (v35ExecCall h z0 hl) := by
    refine ⟨hex, fun l hl' => ?_⟩
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    decide
  have r7 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ExObW7
      [.gate 1 (v35ExecCall h z0 hl), .authorize (v35RefundCall N p), .append 1 v35RefundFlow 2 0,
        .append 0 (subsetFlow 0 1) 1 1, .admin 0 (.allow 1), .admin 1 (.allow 0)] :=
    RunV35.gate (d := 1) (e := v35ExecCall h z0 hl) (st := .FullyExecuted) r6
      (show (v35ExObW6 1).status 1 = .Unreceived by decide) (Or.inr rfl) hgate
  have hneq : obligationOf (v35RefundCall N p).flow (v35RefundCall N p).leg
      ≠ obligationOf (subsetFlow 0 1) ⟨0, 1⟩ := by
    show (⟨1, 2, 1⟩ : Obligation) ≠ ⟨0, 1, 0⟩
    decide
  refine ⟨v35ExObW7, v35RefundCall N p, v35ExecCall h z0 hl, rfl, rfl, rfl, rfl, rfl, r7,
    mixedSystem_wf (by decide), hex, ?_, by decide, by unfold Refunded; decide,
    by unfold Refunded; decide, ?_⟩
  · rw [appendLog_cons_gate, appendLog_cons_authorize, appendLog_cons_append, appendLog_cons_append]
    exact List.mem_cons_of_mem _ List.mem_cons_self
  · rw [authLog_cons_gate, authLog_cons_authorize, authLog_cons_append, authLog_cons_append,
      authLog_cons_admin, authLog_cons_admin]
    intro hb
    cases hb with
    | flowIdClash a ha hobl _ =>
      simp only [authLog, List.filterMap_nil, List.mem_singleton] at ha; subst ha; exact hneq hobl
    | inclusion a ha hobl _ _ =>
      simp only [authLog, List.filterMap_nil, List.mem_singleton] at ha; subst ha; exact hneq hobl
    | absence a ha hobl _ _ =>
      simp only [authLog, List.filterMap_nil, List.mem_singleton] at ha; subst ha; exact hneq hobl

/-! ### The re-allow run -/

/-- Chain `1` deregisters peer `0`. -/
def v35ReallowW2 : WorldV35 :=
  v35W1.set 1 { v35W1 1 with hub := (AdminOp.deregister 0).apply (v35W1 1).hub }

/-- Chain `1` allows peer `0` again. -/
def v35ReallowW3 : WorldV35 :=
  v35ReallowW2.set 1 { v35ReallowW2 1 with hub := (AdminOp.allow 0).apply (v35ReallowW2 1).hub }

/-- Chain `1` executes bundle `1`. -/
def v35ReallowW4 : WorldV35 :=
  v35ReallowW3.set 1
    { v35ReallowW3 1 with status := setStatus (v35ReallowW3 1).status 1 .FullyExecuted }

theorem ReallowedPeerGateWitnessV35 : Properties.ReallowedPeerGateWitnessV35 := by
  intro h z0 hl
  have r1 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35W1
      [.admin 1 (.allow 0)] := RunV35.admin 1 (.allow 0) RunV35.refl
  have r2 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ReallowW2
      [.admin 1 (.deregister 0), .admin 1 (.allow 0)] := RunV35.admin 1 (.deregister 0) r1
  have r3 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ReallowW3
      [.admin 1 (.allow 0), .admin 1 (.deregister 0), .admin 1 (.allow 0)] :=
    RunV35.admin 1 (.allow 0) r2
  have hgate : GateOkV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) (v35ReallowW3 1) 1
      (v35ExecCall h z0 hl) := by
    refine ⟨v35_subset_executes h z0 hl, fun l hl' => ?_⟩
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    decide
  have r4 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35ReallowW4
      [.gate 1 (v35ExecCall h z0 hl), .admin 1 (.allow 0), .admin 1 (.deregister 0),
        .admin 1 (.allow 0)] :=
    RunV35.gate (d := 1) (e := v35ExecCall h z0 hl) (st := .FullyExecuted) r3
      (show (v35ReallowW3 1).status 1 = .Unreceived by decide) (Or.inr rfl) hgate
  exact ⟨v35ReallowW4, v35ExecCall h z0 hl, rfl, rfl, r4, by decide⟩

/-! ### The deregistration run on chain `0`, over the complete swap -/

/-- Chain `0` allows peer `1`. -/
def v35PeerW1 : WorldV35 :=
  v35W0.set 0 { v35W0 0 with hub := (AdminOp.allow 1).apply (v35W0 0).hub }

/-- Chain `0` allows peer `2`. -/
def v35PeerW2 : WorldV35 :=
  v35PeerW1.set 0 { v35PeerW1 0 with hub := (AdminOp.allow 2).apply (v35PeerW1 0).hub }

/-- Chain `0` deregisters peer `2`. -/
def v35PeerW3 : WorldV35 :=
  v35PeerW2.set 0 { v35PeerW2 0 with hub := (AdminOp.deregister 2).apply (v35PeerW2 0).hub }

/-- Chain `0` appends leg `⟨0, 4⟩` of `v35PeerRefundFlow`. -/
def v35PeerW4 : WorldV35 :=
  v35PeerW3.set 0
    { v35PeerW3 0 with
      base := (v35PeerW3 0).base.appended v35BundleCv v35PeerRefundFlow.flowId 4 0 }

/-- Chain `0` imports an L1 root with timestamp `1` at block `0`. -/
def v35PeerW5 : WorldV35 :=
  v35PeerW4.set 0 { v35PeerW4 0 with roots := (v35PeerW4 0).roots.import 0 1 }

/-- Chain `0` marks `(1, 4)` `Revertable`. -/
def v35PeerW6 : WorldV35 :=
  v35PeerW5.set 0 { v35PeerW5 0 with
    base := ⟨(v35PeerW5 0).base.mgr.set v35PeerRefundFlow.flowId 4 .Revertable,
      (v35PeerW5 0).base.tree⟩ }

/-- Chain `0` executes bundle `2`. -/
def v35PeerW7 : WorldV35 :=
  v35PeerW6.set 0 { v35PeerW6 0 with status := setStatus (v35PeerW6 0).status 2 .FullyExecuted }

/-- In the complete swap chain `1` never commits `5`: its tree holds `2` only. -/
lemma v35_swap_five_not_committed :
    ¬ Contracts.LegSourceFilterAtV35.CommittedOnTime v35BundleCv
      Contracts.LegSourceFilterAtV35.swapSystem v35PeerRefundFlow ⟨1, 5⟩ := by
  rintro ⟨n, _, hmem⟩
  change (5 : UInt256) ∈ keys (toAbs (Contracts.LegSourceFilterAtV35.swapSystem.tree 1 n)) at hmem
  rw [Contracts.LegSourceFilterAtV35.swapSystem_eq, pairSystem_tree_one,
    (insert_sound_step setup_valid (setup_insertGuard (by decide : (0 : UInt256) < 2))).2] at hmem
  rcases Finset.mem_insert.mp hmem with h5 | h5
  · exact absurd h5 (by decide)
  · exact not_mem_setup (by decide) h5

/-- The honest absence proof for leg `⟨1, 5⟩` of `v35PeerRefundFlow` in the complete swap. -/
lemma v35_refund_leg15 (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ N p, LegRefundableBy h z0 hl v35BundleCv Contracts.LegSourceFilterAtV35.swapSystem
      v35PeerRefundFlow ⟨1, 5⟩ N p := by
  obtain ⟨N, p, href, _⟩ := Contracts.LegSourceFilterAtV35.honest_refund_evidence (h := h)
    (z0 := z0) (hl := hl) (cv := v35BundleCv) (F := v35PeerRefundFlow) (m := ⟨1, 5⟩)
    Contracts.LegSourceFilterAtV35.swap_wf (show (5 : UInt256) ≠ 0 by decide)
    v35_swap_five_not_committed ⟨1, by decide⟩
  exact ⟨N, p, href⟩

theorem DeregisteredPeerWitnessV35 : Properties.DeregisteredPeerWitnessV35 := by
  intro h z0 hl
  obtain ⟨N, p, href⟩ := v35_refund_leg15 h z0 hl
  let a : AuthCall := ⟨v35PeerRefundFlow, ⟨0, 4⟩, ⟨1, 5⟩, N, p⟩
  let e : ExecCall := pairExec h z0 hl ⟨1, 2⟩
  have r1 : RunV35 h z0 hl v35BundleCv lengthFlowHash Contracts.LegSourceFilterAtV35.swapSystem
      v35W0 v35PeerW1 [.admin 0 (.allow 1)] := RunV35.admin 0 (.allow 1) RunV35.refl
  have r2 : RunV35 h z0 hl v35BundleCv lengthFlowHash Contracts.LegSourceFilterAtV35.swapSystem
      v35W0 v35PeerW2 [.admin 0 (.allow 2), .admin 0 (.allow 1)] := RunV35.admin 0 (.allow 2) r1
  have r3 : RunV35 h z0 hl v35BundleCv lengthFlowHash Contracts.LegSourceFilterAtV35.swapSystem
      v35W0 v35PeerW3 [.admin 0 (.deregister 2), .admin 0 (.allow 2), .admin 0 (.allow 1)] :=
    RunV35.admin 0 (.deregister 2) r2
  have hok4 : AppendOkV35 v35BundleCv lengthFlowHash (v35PeerW3 0) 0 v35PeerRefundFlow 4 1 0 0 :=
    ⟨by decide, by decide, by unfold FlowIdChecked; decide, by decide, by decide, by decide,
      by decide, by decide, by unfold AppendGuard; decide,
      ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, ⟨0, by decide⟩⟩⟩
  have r4 : RunV35 h z0 hl v35BundleCv lengthFlowHash Contracts.LegSourceFilterAtV35.swapSystem
      v35W0 v35PeerW4
      [.append 0 v35PeerRefundFlow 4 1, .admin 0 (.deregister 2), .admin 0 (.allow 2),
        .admin 0 (.allow 1)] :=
    RunV35.append (c := 0) (F := v35PeerRefundFlow) (b := 4) (dest := 1) (hint := 0) (low := 0)
      r3 hok4
  have r5 : RunV35 h z0 hl v35BundleCv lengthFlowHash Contracts.LegSourceFilterAtV35.swapSystem
      v35W0 v35PeerW5
      [.append 0 v35PeerRefundFlow 4 1, .admin 0 (.deregister 2), .admin 0 (.allow 2),
        .admin 0 (.allow 1)] :=
    RunV35.importRoot (c := 0) (blk := 0) (t := 1) r4 (by decide) (by decide)
  have hok6 : AuthorizeOkV35 h z0 hl v35BundleCv lengthFlowHash
      Contracts.LegSourceFilterAtV35.swapSystem (v35PeerW5 0) a := by
    refine ⟨⟨?_, ?_, ?_, href⟩, ?_, ⟨0, ?_⟩⟩
    · show FlowIdChecked lengthFlowHash v35PeerRefundFlow
      unfold FlowIdChecked; decide
    · show (⟨0, 4⟩ : FlowLeg) ∈ v35PeerRefundFlow.legs
      decide
    · show (⟨1, 5⟩ : FlowLeg) ∈ v35PeerRefundFlow.legs
      decide
    · show SourceAllowed (v35PeerW5 0).hub 0 1
      decide
    · show v35PeerRefundFlow.deadline < (v35PeerW5 0).roots.stored 0
      decide
  have hg6 : AuthorizeGuard (v35PeerW5 0).base.mgr v35PeerRefundFlow.flowId 4 := by
    unfold AuthorizeGuard; decide
  have r6 : RunV35 h z0 hl v35BundleCv lengthFlowHash Contracts.LegSourceFilterAtV35.swapSystem
      v35W0 v35PeerW6
      [.authorize a, .append 0 v35PeerRefundFlow 4 1, .admin 0 (.deregister 2),
        .admin 0 (.allow 2), .admin 0 (.allow 1)] :=
    RunV35.authorize a r5 hok6 hg6
  have hgate : GateOkV35 h z0 hl v35BundleCv lengthFlowHash
      Contracts.LegSourceFilterAtV35.swapSystem (v35PeerW6 0) 0 e := by
    refine ⟨Contracts.LegSourceFilterAtV35.pairExec_verified_swap lengthFlowHash_checks_mixed
      h z0 hl Contracts.LegSourceFilterAtV35.swap_legB_mem, fun l hl' => ?_⟩
    change l ∈ [(⟨0, 1⟩ : FlowLeg), ⟨1, 2⟩] at hl'
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hl'
    rcases hl' with rfl | rfl
    · exact Or.inl rfl
    · show SourceAllowed (v35PeerW6 0).hub 0 1
      decide
  have r7 : RunV35 h z0 hl v35BundleCv lengthFlowHash Contracts.LegSourceFilterAtV35.swapSystem
      v35W0 v35PeerW7
      [.gate 0 e, .authorize a, .append 0 v35PeerRefundFlow 4 1,
        .admin 0 (.deregister 2), .admin 0 (.allow 2), .admin 0 (.allow 1)] :=
    RunV35.gate (d := 0) (e := e) (st := .FullyExecuted) r6
      (show (v35PeerW6 0).status 2 = .Unreceived by decide) (Or.inr rfl) hgate
  exact ⟨v35PeerW7, a, e, rfl, rfl, rfl, rfl, rfl, r7, by decide, by decide⟩

/-! ### The two-key code call -/

/-- Chain `1` allows peer `2` (after `v35W1`, where it allowed peer `0`). -/
def v35SameW2 : WorldV35 :=
  v35W1.set 1 { v35W1 1 with hub := (AdminOp.allow 2).apply (v35W1 1).hub }

/-- Chain `1` appends leg `⟨1, 2⟩` of `v35SameChainLegsFlow`. -/
def v35SameW3 : WorldV35 :=
  v35SameW2.set 1
    { v35SameW2 1 with
      base := (v35SameW2 1).base.appended v35BundleCv v35SameChainLegsFlow.flowId 2 0 }

/-- Chain `1` appends leg `⟨1, 3⟩` of `v35SameChainLegsFlow`, landing on leaf `1`. -/
def v35SameW4 : WorldV35 :=
  v35SameW3.set 1
    { v35SameW3 1 with
      base := (v35SameW3 1).base.appended v35BundleCv v35SameChainLegsFlow.flowId 3 1 }

/-- Chain `1` imports an L1 root with timestamp `1` at block `0`. -/
def v35SameW5 : WorldV35 :=
  v35SameW4.set 1 { v35SameW4 1 with roots := (v35SameW4 1).roots.import 0 1 }

theorem CodeAuthorizeCallIsAuthorizeStepsWitnessV35 :
    Properties.CodeAuthorizeCallIsAuthorizeStepsWitnessV35 := by
  intro h z0 hl
  obtain ⟨N, p, href⟩ := v35_refund_leg24 h z0 hl
  have r1 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35W1
      [.admin 1 (.allow 0)] := RunV35.admin 1 (.allow 0) RunV35.refl
  have r2 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35SameW2
      [.admin 1 (.allow 2), .admin 1 (.allow 0)] := RunV35.admin 1 (.allow 2) r1
  have hok3 : AppendOkV35 v35BundleCv lengthFlowHash (v35SameW2 1) 1 v35SameChainLegsFlow 2 0 0 0 :=
    ⟨by decide, by decide, by unfold FlowIdChecked; decide, by decide, by decide, by decide,
      by decide, by decide, by unfold AppendGuard; decide,
      ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, ⟨0, by decide⟩⟩⟩
  have r3 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35SameW3
      [.append 1 v35SameChainLegsFlow 2 0, .admin 1 (.allow 2), .admin 1 (.allow 0)] :=
    RunV35.append (c := 1) (F := v35SameChainLegsFlow) (b := 2) (dest := 0) (hint := 0) (low := 0)
      r2 hok3
  have hok4 : AppendOkV35 v35BundleCv lengthFlowHash (v35SameW3 1) 1 v35SameChainLegsFlow 3 0 0 1 :=
    ⟨by decide, by decide, by unfold FlowIdChecked; decide, by decide, by decide, by decide,
      by decide, by decide, by unfold AppendGuard; decide,
      ⟨by unfold Initialized; decide, by decide, by decide, by decide, by decide, ⟨1, by decide⟩⟩⟩
  have r4 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35SameW4
      [.append 1 v35SameChainLegsFlow 3 0, .append 1 v35SameChainLegsFlow 2 0,
        .admin 1 (.allow 2), .admin 1 (.allow 0)] :=
    RunV35.append (c := 1) (F := v35SameChainLegsFlow) (b := 3) (dest := 0) (hint := 0) (low := 1)
      r3 hok4
  have r5 : RunV35 h z0 hl v35BundleCv lengthFlowHash (mixedSystem 1) v35W0 v35SameW5
      [.append 1 v35SameChainLegsFlow 3 0, .append 1 v35SameChainLegsFlow 2 0,
        .admin 1 (.allow 2), .admin 1 (.allow 0)] :=
    RunV35.importRoot (c := 1) (blk := 0) (t := 1) r4 (by decide) (by decide)
  refine ⟨v35SameW5, N, p, r5, by unfold FlowIdChecked; decide, by decide, by decide, href,
    by decide, ⟨0, by decide⟩, ?_, by decide, by decide, by decide, by decide⟩
  intro l _ F' dest hmem
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hmem
  rcases hmem with h1 | h1 | h1 | h1
  · simp only [CallV35.append.injEq] at h1
    obtain ⟨-, rfl, -, -⟩ := h1
    exact fun hcl => hcl.1 rfl
  · simp only [CallV35.append.injEq] at h1
    obtain ⟨-, rfl, -, -⟩ := h1
    exact fun hcl => hcl.1 rfl
  · cases h1
  · cases h1

end Contracts.SystemAtV35
