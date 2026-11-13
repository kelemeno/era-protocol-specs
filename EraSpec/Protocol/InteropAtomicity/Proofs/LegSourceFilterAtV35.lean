import EraSpec.Protocol.InteropAtomicity.Properties.LegSourceFilterAtV35
import EraSpec.Protocol.InteropAtomicity.Proofs.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg

/-!
# Proofs: the v35 receive filter

Proofs of `EraSpec.Protocol.InteropAtomicity.Properties.LegSourceFilterAtV35`.

* Safety is one projection (`runAtV35_runLog`, `sysStepsAtV35_sysSteps`): a v35 gate call is a
  pin `execute`, a v35 `authorizeRefund` is a pin `authorize`, and the admin steps touch no
  manager.  Every exclusion result is then the pin's, applied to the projected run.  The
  allowed-chain refinement re-runs the pin's case split and reads the filter off the two logged
  calls.
* Stranding is the filter read in the two cases the IMT leaves: a complete flow has honest gate
  evidence (`honest_gate_evidence`) and no unbroken refund (`member_not_refundable_or_break`); an
  incomplete flow has honest timeout evidence (`honest_refund_evidence`, from
  `non_inclusion_complete_idx`) and no unbroken execution (`finality_means_membership_or_break`).
* Re-allowing is one `allowPeer` step and the same call; blocking is a frame induction.
-/

namespace Contracts.LegSourceFilterAtV35

open MerkleSpec MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree
open Contracts.Atomicity Contracts.Timeout Contracts.Refund Contracts.FlowBinding
open Contracts.AtomicFlowManager Contracts.AppendPath

/-! ## The allow-lists -/

theorem sourceAllowed_self (P : Peers) (c : Chain) : SourceAllowed P c c := Or.inl rfl

theorem sourceAllowed_allPeers (c s : Chain) : SourceAllowed allPeersAllowed c s := Or.inr rfl

theorem not_sourceAllowed {P : Peers} {c s : Chain} (hne : s ≠ c) (hP : P c s = false) :
    ¬ SourceAllowed P c s := by
  rintro (heq | ht)
  · exact hne heq
  · rw [hP] at ht; exact Bool.false_ne_true ht

@[simp] theorem allow_self (P : Peers) (c s : Chain) : (P.allow c s) c s = true := by
  simp [Peers.allow]

theorem allow_other (P : Peers) {c s c' s' : Chain} (hne : ¬ (c' = c ∧ s' = s)) :
    (P.allow c s) c' s' = P c' s' := by
  exact ite_eq_right hne

@[simp] theorem deregister_self (P : Peers) (c s : Chain) : (P.deregister c s) c s = false := by
  simp [Peers.deregister]

theorem deregister_other (P : Peers) {c s c' s' : Chain} (hne : ¬ (c' = c ∧ s' = s)) :
    (P.deregister c s) c' s' = P c' s' := by
  exact ite_eq_right hne

/-- **DEREGISTERING AND THEN RE-ALLOWING A PEER CHANGES NOTHING.** -/
theorem deregister_then_allow (P : Peers) (c s : Chain) (hP : P c s = true) :
    (P.deregister c s).allow c s = P := by
  funext c' s'
  by_cases hcs : c' = c ∧ s' = s
  · obtain ⟨rfl, rfl⟩ := hcs
    rw [allow_self, hP]
  · rw [allow_other _ hcs, deregister_other _ hcs]

/-! ## The gates -/

theorem executedViaByAtV35_iff {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {P : Peers} {d : Chain} {F : Flow} {ev : GateEvidence}
    {leg : FlowLeg} :
    ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg
      ↔ ExecutedViaBy h z0 hl cv fh S F ev leg ∧ ∀ l ∈ F.legs, SourceAllowed P d l.chain := by
  constructor
  · rintro ⟨hmem, hchk, hfin⟩
    exact ⟨⟨hmem, hchk, fun l hl' => (hfin l hl').2⟩, fun l hl' => (hfin l hl').1⟩
  · rintro ⟨⟨hmem, hchk, hfin⟩, hall⟩
    exact ⟨hmem, hchk, fun l hl' => ⟨hall l hl', hfin l hl'⟩⟩

/-- A v35 gate pass is a pin gate pass. -/
theorem ExecutedViaByAtV35.toPin {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {P : Peers} {d : Chain} {F : Flow} {ev : GateEvidence}
    {leg : FlowLeg} (hex : ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg) :
    ExecutedViaBy h z0 hl cv fh S F ev leg :=
  (executedViaByAtV35_iff.1 hex).1

/-- …and the destination allowed every leg's source. -/
theorem ExecutedViaByAtV35.allowed {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {P : Peers} {d : Chain} {F : Flow} {ev : GateEvidence}
    {leg : FlowLeg} (hex : ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg) :
    ∀ l ∈ F.legs, SourceAllowed P d l.chain :=
  (executedViaByAtV35_iff.1 hex).2

/-- Under full allowance the v35 gate is the pin's. -/
theorem executedViaByAtV35_of_allPeers {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} {d : Chain} {F : Flow} {ev : GateEvidence}
    {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg) :
    ExecutedViaByAtV35 h z0 hl cv fh S allPeersAllowed d F ev leg :=
  executedViaByAtV35_iff.2 ⟨hex, fun l _ => sourceAllowed_allPeers d l.chain⟩

theorem sourceAllowed_mono {P Q : Peers} {c s : Chain} (hPQ : ∀ s, P c s = true → Q c s = true)
    (ha : SourceAllowed P c s) : SourceAllowed Q c s := by
  rcases ha with heq | ht
  · exact Or.inl heq
  · exact Or.inr (hPQ s ht)

theorem gate_mono {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue} {fh : FlowHash}
    {S : System} {P Q : Peers} {d : Chain} (hPQ : ∀ s, P d s = true → Q d s = true)
    {F : Flow} {ev : GateEvidence} {leg : FlowLeg}
    (hex : ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg) :
    ExecutedViaByAtV35 h z0 hl cv fh S Q d F ev leg :=
  executedViaByAtV35_iff.2 ⟨hex.toPin, fun l hl' => sourceAllowed_mono hPQ (hex.allowed l hl')⟩

theorem refund_mono {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue} {S : System}
    {P Q : Peers} {c : Chain} (hPQ : ∀ s, P c s = true → Q c s = true) {F : Flow} {m : FlowLeg}
    {N : ℕ} {q : ImtProof} (hr : LegRefundableByAtV35 h z0 hl cv S P c F m N q) :
    LegRefundableByAtV35 h z0 hl cv S Q c F m N q :=
  ⟨sourceAllowed_mono hPQ hr.1, hr.2⟩

/-! ## Logs -/

@[simp] theorem pinLog_nil : pinLog [] = [] := rfl

@[simp] theorem pinLog_gate (e : ExecCall) (P : Peers) (log : List CallAtV35) :
    pinLog (.gate e P :: log) = .execute e :: pinLog log := rfl

@[simp] theorem pinLog_authorize (a : AuthCall) (P : Peers) (log : List CallAtV35) :
    pinLog (.authorize a P :: log) = .authorize a :: pinLog log := rfl

@[simp] theorem pinLog_allowPeer (c s : Chain) (log : List CallAtV35) :
    pinLog (.allowPeer c s :: log) = pinLog log := rfl

@[simp] theorem pinLog_deregisterPeer (c s : Chain) (log : List CallAtV35) :
    pinLog (.deregisterPeer c s :: log) = pinLog log := rfl

@[simp] theorem authLogAtV35_nil : authLogAtV35 [] = [] := rfl

@[simp] theorem authLogAtV35_gate (e : ExecCall) (P : Peers) (log : List CallAtV35) :
    authLogAtV35 (.gate e P :: log) = authLogAtV35 log := rfl

@[simp] theorem authLogAtV35_authorize (a : AuthCall) (P : Peers) (log : List CallAtV35) :
    authLogAtV35 (.authorize a P :: log) = a :: authLogAtV35 log := rfl

@[simp] theorem authLogAtV35_allowPeer (c s : Chain) (log : List CallAtV35) :
    authLogAtV35 (.allowPeer c s :: log) = authLogAtV35 log := rfl

@[simp] theorem authLogAtV35_deregisterPeer (c s : Chain) (log : List CallAtV35) :
    authLogAtV35 (.deregisterPeer c s :: log) = authLogAtV35 log := rfl

/-- The pin's authorize log of the projected run is the v35 authorize log. -/
theorem authCalls_pinLog (log : List CallAtV35) : authCalls (pinLog log) = authLogAtV35 log := by
  induction log with
  | nil => rfl
  | cons c log ih =>
    cases c with
    | gate e P => rw [pinLog_gate, authCalls_execute, authLogAtV35_gate, ih]
    | authorize a P => rw [pinLog_authorize, authCalls_authorize, authLogAtV35_authorize, ih]
    | allowPeer c s => rw [pinLog_allowPeer, authLogAtV35_allowPeer, ih]
    | deregisterPeer c s => rw [pinLog_deregisterPeer, authLogAtV35_deregisterPeer, ih]

theorem gate_mem_pinLog {log : List CallAtV35} {e : ExecCall} {P : Peers}
    (he : CallAtV35.gate e P ∈ log) : CheckedCall.execute e ∈ pinLog log :=
  List.mem_filterMap.2 ⟨_, he, rfl⟩

theorem authorize_mem_pinLog {log : List CallAtV35} {a : AuthCall} {P : Peers}
    (ha : CallAtV35.authorize a P ∈ log) : CheckedCall.authorize a ∈ pinLog log :=
  List.mem_filterMap.2 ⟨_, ha, rfl⟩

/-! ## Every v35 run is a pin run -/

theorem GateCallPassesAtV35.toPin {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {dst : Dest} {P : Peers} {e : ExecCall}
    (he : GateCallPassesAtV35 h z0 hl cv fh S dst P e) : e.Verified h z0 hl cv fh S :=
  ExecutedViaByAtV35.toPin he

/-- **EVERY v35 RUN IS A PIN RUN.** -/
theorem runAtV35_runLog {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {dst : Dest} {X Y : WorldAtV35} {log : List CallAtV35}
    (hr : RunAtV35 h z0 hl cv fh S dst X Y log) :
    RunLog h z0 hl cv fh S X.mgrs Y.mgrs (pinLog log) := by
  induction hr with
  | refl => exact RunLog.refl
  | append _ hg ih => exact RunLog.append ih hg
  | gate e _ he ih => rw [pinLog_gate]; exact RunLog.execute e ih he.toPin
  | authorize a _ ha hg ih => rw [pinLog_authorize]; exact RunLog.authorize a ih ha.1 hg
  | claim _ hg ih => exact RunLog.claim ih hg
  | allowPeer c s _ ih => rw [pinLog_allowPeer]; exact ih
  | deregisterPeer c s _ ih => rw [pinLog_deregisterPeer]; exact ih

/-- **UNDER FULL MUTUAL ALLOWANCE THE FILTER CHANGES NOTHING.** -/
theorem runLog_runAtV35 {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} (dst : Dest) {Ms Ns : Managers} {log : List CheckedCall}
    (hr : RunLog h z0 hl cv fh S Ms Ns log) :
    ∃ log' : List CallAtV35,
      RunAtV35 h z0 hl cv fh S dst ⟨Ms, allPeersAllowed⟩ ⟨Ns, allPeersAllowed⟩ log'
        ∧ pinLog log' = log := by
  induction hr with
  | refl => exact ⟨[], RunAtV35.refl, rfl⟩
  | append _ hg ih =>
    obtain ⟨log', hr', hp⟩ := ih
    exact ⟨log', RunAtV35.append (X := ⟨_, allPeersAllowed⟩) (Y := ⟨_, allPeersAllowed⟩) hr' hg, hp⟩
  | execute e _ he ih =>
    obtain ⟨log', hr', hp⟩ := ih
    exact ⟨.gate e allPeersAllowed :: log',
      RunAtV35.gate (Y := ⟨_, allPeersAllowed⟩) e hr' (executedViaByAtV35_of_allPeers he),
      by rw [pinLog_gate, hp]⟩
  | authorize a _ ha hg ih =>
    obtain ⟨log', hr', hp⟩ := ih
    exact ⟨.authorize a allPeersAllowed :: log',
      RunAtV35.authorize (Y := ⟨_, allPeersAllowed⟩) a hr'
        ⟨ha, sourceAllowed_allPeers _ _⟩ hg,
      by rw [pinLog_authorize, hp]⟩
  | claim _ hg ih =>
    obtain ⟨log', hr', hp⟩ := ih
    exact ⟨log', RunAtV35.claim (Y := ⟨_, allPeersAllowed⟩) hr' hg, hp⟩

/-- **EVERY LOGGED v35 CALL PASSED ITS v35 CHECKS, AGAINST THE ALLOW-LISTS IT RECORDS.** -/
theorem logged_calls_pass_at_v35 {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {dst : Dest} {X Y : WorldAtV35} {log : List CallAtV35}
    (hr : RunAtV35 h z0 hl cv fh S dst X Y log) :
    (∀ (e : ExecCall) (P : Peers), CallAtV35.gate e P ∈ log →
        GateCallPassesAtV35 h z0 hl cv fh S dst P e)
      ∧ ∀ (a : AuthCall) (P : Peers), CallAtV35.authorize a P ∈ log →
        AuthorizeCallPassesAtV35 h z0 hl cv fh S P a := by
  induction hr with
  | refl => exact ⟨fun _ _ he => absurd he List.not_mem_nil, fun _ _ ha => absurd ha List.not_mem_nil⟩
  | append _ _ ih => exact ih
  | gate e _ he ih =>
    refine ⟨fun e' P' he' => ?_, fun a' P' ha' => ?_⟩
    · rcases List.mem_cons.mp he' with heq | hmem
      · cases heq; exact he
      · exact ih.1 e' P' hmem
    · rcases List.mem_cons.mp ha' with heq | hmem
      · cases heq
      · exact ih.2 a' P' hmem
  | authorize a _ ha _ ih =>
    refine ⟨fun e' P' he' => ?_, fun a' P' ha' => ?_⟩
    · rcases List.mem_cons.mp he' with heq | hmem
      · cases heq
      · exact ih.1 e' P' hmem
    · rcases List.mem_cons.mp ha' with heq | hmem
      · cases heq; exact ha
      · exact ih.2 a' P' hmem
  | claim _ _ ih => exact ih
  | allowPeer c s _ ih =>
    refine ⟨fun e' P' he' => ?_, fun a' P' ha' => ?_⟩
    · rcases List.mem_cons.mp he' with heq | hmem
      · cases heq
      · exact ih.1 e' P' hmem
    · rcases List.mem_cons.mp ha' with heq | hmem
      · cases heq
      · exact ih.2 a' P' hmem
  | deregisterPeer c s _ ih =>
    refine ⟨fun e' P' he' => ?_, fun a' P' ha' => ?_⟩
    · rcases List.mem_cons.mp he' with heq | hmem
      · cases heq
      · exact ih.1 e' P' hmem
    · rcases List.mem_cons.mp ha' with heq | hmem
      · cases heq
      · exact ih.2 a' P' hmem

/-! ## Safety at v35 -/

theorem executed_excludes_any_refund_or_break_at_v35 {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {P : Peers} {d : Chain} {F : Flow}
    {ev : GateEvidence} {leg : FlowLeg} (hex : ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg)
    (other : FlowLeg) (hother : other ∈ F.legs) (Q : Peers) (c : Chain) (N : ℕ) (q : ImtProof) :
    ¬ LegRefundableByAtV35 h z0 hl cv S Q c F other N q
      ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2
      ∨ AbsenceBreak h z0 hl S F.deadline other.chain N q := by
  rcases executed_excludes_any_refund_or_break hS hex.toPin other hother N q with hn | hb | hb
  · exact Or.inl fun hr => hn hr.2
  · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hb)

theorem none_or_all_or_break_at_v35 {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A)
    (P : Peers) (d : Chain) (F : Flow) (ev : GateEvidence) :
    FlowFinalizableBy h z0 hl cv S A F
      ∨ (∀ leg, ¬ ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg)
      ∨ PinnedGateBreak h z0 hl cv S A F ev := by
  rcases none_or_all_or_break_pinned (fh := fh) hS hDA F ev with hf | hn | hp
  · exact Or.inl hf
  · exact Or.inr (Or.inl fun leg hex => hn leg hex.toPin)
  · exact Or.inr (Or.inr hp)

theorem logged_gate_excludes_logged_refund_or_allowed_break_at_v35 {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {dst : Dest}
    {X Y : WorldAtV35} {log : List CallAtV35} (hr : RunAtV35 h z0 hl cv fh S dst X Y log)
    {e : ExecCall} {P : Peers} (he : CallAtV35.gate e P ∈ log) {a : AuthCall} {Q : Peers}
    (ha : CallAtV35.authorize a Q ∈ log) (hid : a.flow.flowId = e.flow.flowId) :
    (InclusionBreak h z0 hl S a.missing.chain (e.evidence a.missing).1 (e.evidence a.missing).2
        ∧ SourceAllowed P (dst e.leg.bundleHash) a.missing.chain)
      ∨ (AbsenceBreak h z0 hl S a.flow.deadline a.missing.chain a.batch a.proof
        ∧ SourceAllowed Q a.leg.chain a.missing.chain)
      ∨ FlowIdClash fh e.flow a.flow := by
  have hex : ExecutedViaByAtV35 h z0 hl cv fh S P (dst e.leg.bundleHash) e.flow e.evidence e.leg :=
    (logged_calls_pass_at_v35 hr).1 e P he
  obtain ⟨⟨hchk, _, hmiss, href⟩, hallow⟩ := (logged_calls_pass_at_v35 hr).2 a Q ha
  rcases flowId_check_pins_legList_or_collision hex.toPin.2.1 hchk hid.symm with heq | hcl
  · have hmiss' : a.missing ∈ e.flow.legs := by rw [heq]; exact hmiss
    have href' : LegRefundableBy h z0 hl cv S e.flow a.missing a.batch a.proof := by
      rw [heq]; exact href
    rcases executed_excludes_any_refund_or_break hS hex.toPin a.missing hmiss' a.batch a.proof
      with hn | hb | hb
    · exact absurd href' hn
    · exact Or.inl ⟨hb, hex.allowed a.missing hmiss'⟩
    · refine Or.inr (Or.inl ⟨?_, hallow⟩)
      rw [← heq]; exact hb
  · exact Or.inr (Or.inr hcl)

theorem executed_freezes_flow_or_break_at_v35 {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {P : Peers} {d : Chain} {F : Flow}
    {ev : GateEvidence} {leg : FlowLeg} (hex : ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg)
    {dst : Dest} {P₀ : Peers} {Y : WorldAtV35} {log : List CallAtV35}
    (hr : RunAtV35 h z0 hl cv fh S dst ⟨emptyManagers, P₀⟩ Y log)
    (o : Obligation) (ho : o.flowId = F.flowId) :
    ¬ Refunded Y.mgrs o ∨ RefundBreak h z0 hl fh S F ev o (authLogAtV35 log) := by
  have hrl : ReachLog h z0 hl cv fh S emptyManagers Y.mgrs (authCalls (pinLog log)) :=
    runLog_reachLog (runAtV35_runLog hr)
  rw [authCalls_pinLog] at hrl
  exact executed_freezes_flow_or_break hS hex.toPin hrl o ho

theorem executed_implies_real_flow_finalizable_or_logged_clash_at_v35 {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) {dst : Dest} {X Y : WorldAtV35} {log : List CallAtV35}
    (hr : RunAtV35 h z0 hl cv fh S dst X Y log) {e : ExecCall} {P : Peers}
    (he : CallAtV35.gate e P ∈ log) {c : CheckedCall} (hc : c ∈ pinLog log)
    (hid : c.flow.flowId = e.flow.flowId) :
    FlowFinalizableBy h z0 hl cv S A c.flow
      ∨ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
      ∨ FlowIdClash fh e.flow c.flow :=
  executed_implies_real_flow_finalizable_or_logged_clash hS hDA (runAtV35_runLog hr)
    (gate_mem_pinLog he) hc hid

/-! ## Every v35 system run is a pin system run -/

theorem sysStepsAtV35_sysSteps {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : SysWorldAtV35} {log : List Obligation}
    {alog : List AuthCall} (hr : SysStepsAtV35 h z0 hl cv fh S X Y log alog) :
    SysSteps h z0 hl cv fh S X.chains Y.chains log alog := by
  induction hr with
  | refl => exact SysSteps.refl
  | append _ hs ih => exact SysSteps.append ih hs
  | authorize a _ ha hg ih => exact SysSteps.authorize a ih ha.1 hg
  | claim _ hg ih => exact SysSteps.claim ih hg
  | initL2 _ h0 ih => exact SysSteps.initL2 ih h0
  | allowPeer c s _ ih => exact ih
  | deregisterPeer c s _ ih => exact ih

theorem sysSteps_sysStepsAtV35 {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {X Y : Chains} {log : List Obligation} {alog : List AuthCall}
    (hr : SysSteps h z0 hl cv fh S X Y log alog) :
    SysStepsAtV35 h z0 hl cv fh S ⟨X, allPeersAllowed⟩ ⟨Y, allPeersAllowed⟩ log alog := by
  induction hr with
  | refl => exact SysStepsAtV35.refl
  | append _ hs ih => exact SysStepsAtV35.append (Y := ⟨_, allPeersAllowed⟩) ih hs
  | authorize a _ ha hg ih =>
    exact SysStepsAtV35.authorize (Y := ⟨_, allPeersAllowed⟩) a ih
      ⟨ha, sourceAllowed_allPeers _ _⟩ hg
  | claim _ hg ih => exact SysStepsAtV35.claim (Y := ⟨_, allPeersAllowed⟩) ih hg
  | initL2 _ h0 ih => exact SysStepsAtV35.initL2 (Y := ⟨_, allPeersAllowed⟩) ih h0

/-! ## Honest evidence on both sides -/

/-- `Contracts.InteropCommitmentTree.non_inclusion_complete` with the low leaf's index exposed:
the low leaf is the occupied leaf `T.leaf i`, so the honest proof carries no break. -/
theorem non_inclusion_complete_idx {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
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

/-- **HONEST TIMEOUT EVIDENCE FOR A LEG THAT MISSED THE DEADLINE.**  The honest low-leaf proof
against the BEGIN root of the first late batch passes the timeout check and carries no break. -/
theorem honest_refund_evidence {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} (hS : Wf S) {F : Flow} {m : FlowLeg} (hv : legValue cv F m ≠ 0)
    (hnot : ¬ CommittedOnTime cv S F m) (hlate : SettledAfterDeadline S F m) :
    ∃ (N : ℕ) (q : ImtProof), LegRefundableBy h z0 hl cv S F m N q
      ∧ ¬ AbsenceBreak h z0 hl S F.deadline m.chain N q := by
  classical
  obtain ⟨N, hN, hmin⟩ : ∃ N, F.deadline < S.time m.chain N
      ∧ ∀ k < N, S.time m.chain k ≤ F.deadline :=
    ⟨Nat.find hlate, Nat.find_spec hlate, fun k hk => not_lt.mp (Nat.find_min hlate hk)⟩
  have key : Valid (beginTree S m.chain N)
      ∧ (beginTree S m.chain N).leafCount ≤ 2 ^ beginHeight S m.chain N
      ∧ legValue cv F m ∉ keys (toAbs (beginTree S m.chain N)) := by
    cases N with
    | zero =>
      refine ⟨setup_valid, by show (1 : ℕ) ≤ 2 ^ 0; norm_num, ?_⟩
      exact not_mem_setup (Fin.pos_of_ne_zero hv)
    | succ k =>
      refine ⟨valid_batch hS m.chain k, hS.capacity m.chain k, ?_⟩
      intro hmem
      exact hnot ⟨k, hmin k (Nat.lt_succ_self k), hmem⟩
  obtain ⟨hV, hcap, habs⟩ := key
  obtain ⟨i, hi, hacc⟩ := non_inclusion_complete_idx (h := h) (z0 := z0) (hl := hl) hV hcap hv habs
  refine ⟨N, ⟨(beginTree S m.chain N).leaf i, i,
    honestSibs h z0 (leafHashes hl (beginTree S m.chain N)) i, beginHeight S m.chain N⟩,
    Or.inl ⟨hN, hacc⟩, ?_⟩
  rintro (⟨_, hb⟩ | ⟨hle, _⟩)
  · exact honest_proof_no_break h z0 hl _ _ i hi hb
  · exact absurd hle (not_le.mpr hN)

/-- **HONEST GATE EVIDENCE FOR A COMPLETE FLOW.**  For each leg, the honest proof of its leaf at an
on-time batch where it is committed: it passes that leg's check, carries no break, and is an
honest proof of an occupied leaf (so data availability presents it). -/
theorem honest_gate_evidence {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} (hS : Wf S) {F : Flow} (hc : ∀ l ∈ F.legs, CommittedOnTime cv S F l) :
    ∃ ev : GateEvidence,
      (∀ l ∈ F.legs, LegFinalizedBy h z0 hl cv S F l (ev l).1 (ev l).2
          ∧ ∃ i, i < (S.tree l.chain (ev l).1).leafCount
              ∧ (ev l).2 = honestProof h z0 hl S l.chain (ev l).1 i)
        ∧ ¬ GateBreak h z0 hl S F ev := by
  classical
  have key : ∀ l ∈ F.legs, ∃ (n i : ℕ), S.time l.chain n ≤ F.deadline
      ∧ i < (S.tree l.chain n).leafCount
      ∧ Accepts h z0 hl S l.chain n (legValue cv F l) (honestProof h z0 hl S l.chain n i) := by
    intro l hl'
    obtain ⟨n, hon, hmem⟩ := hc l hl'
    obtain ⟨i, hi, hacc⟩ := honest_accepts (h := h) (z0 := z0) (hl := hl) hS hmem
    exact ⟨n, i, hon, hi, hacc⟩
  choose! n i hon hi hacc using key
  refine ⟨fun l => (n l, honestProof h z0 hl S l.chain (n l) (i l)),
    fun l hl' => ⟨⟨hon l hl', hacc l hl'⟩, i l, hi l hl', rfl⟩, ?_⟩
  rintro ⟨l, hl', hb⟩
  exact honestProof_no_break h z0 hl S l.chain (n l) (i l) (hi l hl') hb

/-! ## Exactly which legs are stranded -/

theorem refund_evidence_complete_at_v35 {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {F : Flow} {m : FlowLeg} (hv : legValue cv F m ≠ 0)
    (hnot : ¬ CommittedOnTime cv S F m) (hlate : SettledAfterDeadline S F m) (P : Peers)
    (c : Chain) (hallow : SourceAllowed P c m.chain) :
    ∃ (N : ℕ) (q : ImtProof), LegRefundableByAtV35 h z0 hl cv S P c F m N q
      ∧ ¬ AbsenceBreak h z0 hl S F.deadline m.chain N q := by
  obtain ⟨N, q, href, hnb⟩ := honest_refund_evidence (h := h) (z0 := z0) (hl := hl) hS hv hnot hlate
  exact ⟨N, q, ⟨hallow, href⟩, hnb⟩

theorem complete_flow_gate_open_iff {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A)
    {F : Flow} (hchk : FlowIdChecked fh F) (hc : ∀ l ∈ F.legs, CommittedOnTime cv S F l)
    {leg : FlowLeg} (hleg : leg ∈ F.legs) (P : Peers) (d : Chain) :
    GateOpenAtV35 h z0 hl cv fh S A P d F leg ↔ ∀ l ∈ F.legs, SourceAllowed P d l.chain := by
  constructor
  · rintro ⟨ev, _, hex⟩
    exact hex.allowed
  · intro hall
    obtain ⟨ev, hev, _⟩ := honest_gate_evidence (h := h) (z0 := z0) (hl := hl) hS hc
    refine ⟨ev, fun l hl' => ?_, hleg, hchk, fun l hl' => ⟨hall l hl', (hev l hl').1⟩⟩
    obtain ⟨_, i, hi, hp⟩ := hev l hl'
    rw [hp]
    exact hDA _ _ _ hi

/-- A committed-on-time leg has no unbroken timeout evidence, whatever the allow-lists. -/
theorem committed_not_refundable_at_v35 {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {F : Flow} {m : FlowLeg}
    (hcm : CommittedOnTime cv S F m) (P : Peers) (c : Chain) (N : ℕ) (q : ImtProof) :
    ¬ LegRefundableByAtV35 h z0 hl cv S P c F m N q
      ∨ AbsenceBreak h z0 hl S F.deadline m.chain N q := by
  obtain ⟨n, hon, hmem⟩ := hcm
  rcases member_not_refundable_or_break hS hon hmem N q with hn | hb
  · exact Or.inl fun hr => hn hr.2
  · exact Or.inr hb

/-- A leg that missed the deadline blocks every gate call of its flow, unless the proof submitted
for it carries a break. -/
theorem missing_blocks_gate_at_v35 {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {F : Flow} {m₀ : FlowLeg} (hm₀ : m₀ ∈ F.legs)
    (hnot : ¬ CommittedOnTime cv S F m₀) (P : Peers) (d : Chain) (ev : GateEvidence)
    (leg : FlowLeg) :
    ¬ ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg
      ∨ InclusionBreak h z0 hl S m₀.chain (ev m₀).1 (ev m₀).2 := by
  by_cases hex : ExecutedViaByAtV35 h z0 hl cv fh S P d F ev leg
  · refine Or.inr ?_
    obtain ⟨hon, hacc⟩ := hex.toPin.2.2 m₀ hm₀
    rcases finality_means_membership_or_break hacc with hmem | hb
    · exact absurd ⟨(ev m₀).1, hon, hmem⟩ hnot
    · exact hb
  · exact Or.inl hex

theorem stranded_iff_at_v35 {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} (hS : Wf S) {F : Flow} (hchk : FlowIdChecked fh F)
    (hwf : FlowWf cv F)
    (hprog : ∀ l ∈ F.legs, ¬ CommittedOnTime cv S F l → SettledAfterDeadline S F l)
    {leg : FlowLeg} (hleg : leg ∈ F.legs) (P : Peers) (d : Chain) :
    StrandedOrBreakAtV35 h z0 hl cv fh S P d F leg ↔
      ((∀ l ∈ F.legs, CommittedOnTime cv S F l) ∧ ∃ l ∈ F.legs, ¬ SourceAllowed P d l.chain)
        ∨ ((∃ l ∈ F.legs, ¬ CommittedOnTime cv S F l)
            ∧ ∀ m ∈ F.legs, ¬ CommittedOnTime cv S F m → ¬ SourceAllowed P leg.chain m.chain) := by
  classical
  constructor
  · rintro ⟨hgate, hrefund⟩
    by_cases hcomp : ∀ l ∈ F.legs, CommittedOnTime cv S F l
    · refine Or.inl ⟨hcomp, ?_⟩
      by_contra hall
      push Not at hall
      obtain ⟨ev, hev, hnb⟩ := honest_gate_evidence (h := h) (z0 := z0) (hl := hl) hS hcomp
      rcases hgate ev with hn | hb
      · exact hn ⟨hleg, hchk, fun l hl' => ⟨hall l hl', (hev l hl').1⟩⟩
      · exact hnb hb
    · push Not at hcomp
      refine Or.inr ⟨hcomp, fun m hm hnot hallow => ?_⟩
      obtain ⟨N, q, href, hnb⟩ :=
        refund_evidence_complete_at_v35 (h := h) (z0 := z0) (hl := hl) hS (hwf m hm) hnot
          (hprog m hm hnot) P leg.chain hallow
      rcases hrefund m hm N q with hn | hb
      · exact hn href
      · exact hnb hb
  · rintro (⟨hcomp, l₀, hl₀, hnot₀⟩ | ⟨⟨m₀, hm₀, hnot₀⟩, hblock⟩)
    · exact ⟨fun ev => Or.inl fun hex => hnot₀ (hex.allowed l₀ hl₀),
        fun m hm N q => committed_not_refundable_at_v35 hS (hcomp m hm) P leg.chain N q⟩
    · refine ⟨fun ev => ?_, fun m hm N q => ?_⟩
      · rcases missing_blocks_gate_at_v35 (fh := fh) hm₀ hnot₀ P d ev leg with hn | hb
        · exact Or.inl hn
        · exact Or.inr ⟨m₀, hm₀, hb⟩
      · by_cases hcm : CommittedOnTime cv S F m
        · exact committed_not_refundable_at_v35 hS hcm P leg.chain N q
        · exact Or.inl fun hr => hblock m hm hcm hr.1

/-! ## Re-allowing restores progress; until then the source stays blocked -/

theorem allow_of_true {P : Peers} {c' s' : Chain} (c s : Chain) (ht : P c' s' = true) :
    (P.allow c s) c' s' = true := by
  by_cases hcs : c' = c ∧ s' = s
  · obtain ⟨rfl, rfl⟩ := hcs; exact allow_self _ _ _
  · rw [allow_other _ hcs]; exact ht

theorem reallow_restores_gate {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {dst : Dest} {X Y : WorldAtV35} {log : List CallAtV35}
    {e : ExecCall} {s : Chain} (hr : RunAtV35 h z0 hl cv fh S dst X Y log)
    (he : e.Verified h z0 hl cv fh S)
    (hs : ∀ l ∈ e.flow.legs, l.chain = s ∨ SourceAllowed Y.peers (dst e.leg.bundleHash) l.chain) :
    RunAtV35 h z0 hl cv fh S dst X ⟨Y.mgrs, Y.peers.allow (dst e.leg.bundleHash) s⟩
      (.gate e (Y.peers.allow (dst e.leg.bundleHash) s)
        :: .allowPeer (dst e.leg.bundleHash) s :: log) := by
  refine RunAtV35.gate (Y := ⟨Y.mgrs, Y.peers.allow (dst e.leg.bundleHash) s⟩) e
    (RunAtV35.allowPeer _ _ hr) (executedViaByAtV35_iff.2 ⟨he, fun l hl' => ?_⟩)
  rcases hs l hl' with heq | hself | ht
  · exact Or.inr (by rw [heq]; exact allow_self _ _ _)
  · exact Or.inl hself
  · exact Or.inr (allow_of_true _ _ ht)

theorem reallow_restores_refund {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {dst : Dest} {X Y : WorldAtV35} {log : List CallAtV35}
    {a : AuthCall} (hr : RunAtV35 h z0 hl cv fh S dst X Y log) (ha : a.Verified h z0 hl cv fh S)
    (hg : AuthorizeGuard (Y.mgrs a.leg.chain) a.flow.flowId a.leg.bundleHash) :
    RunAtV35 h z0 hl cv fh S dst X
      ⟨setAt Y.mgrs a.leg.chain
          ((Y.mgrs a.leg.chain).set a.flow.flowId a.leg.bundleHash .Revertable),
        Y.peers.allow a.leg.chain a.missing.chain⟩
      (.authorize a (Y.peers.allow a.leg.chain a.missing.chain)
        :: .allowPeer a.leg.chain a.missing.chain :: log) :=
  RunAtV35.authorize (Y := ⟨Y.mgrs, Y.peers.allow a.leg.chain a.missing.chain⟩) a
    (RunAtV35.allowPeer _ _ hr) ⟨ha, Or.inr (allow_self _ _ _)⟩ hg

theorem blocked_until_reallowed {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {dst : Dest} {X Y : WorldAtV35} {log : List CallAtV35}
    (hr : RunAtV35 h z0 hl cv fh S dst X Y log) {c s : Chain} (hsc : s ≠ c)
    (hX : X.peers c s = false) (hno : CallAtV35.allowPeer c s ∉ log) :
    Y.peers c s = false
      ∧ (∀ (e : ExecCall) (P : Peers), CallAtV35.gate e P ∈ log → dst e.leg.bundleHash = c →
          ∀ l ∈ e.flow.legs, l.chain ≠ s)
      ∧ (∀ (a : AuthCall) (P : Peers), CallAtV35.authorize a P ∈ log → a.leg.chain = c →
          a.missing.chain ≠ s) := by
  induction hr with
  | refl =>
    exact ⟨hX, fun _ _ he => absurd he List.not_mem_nil, fun _ _ ha => absurd ha List.not_mem_nil⟩
  | append _ _ ih => exact ih hno
  | @gate Y log e _ he ih =>
    obtain ⟨hY, hg, ha⟩ := ih (fun hm => hno (List.mem_cons_of_mem _ hm))
    refine ⟨hY, fun e' P' he' hd l hl' hls => ?_, fun a' P' ha' hc => ?_⟩
    · rcases List.mem_cons.mp he' with heq | hm
      · cases heq
        have hal := he.allowed l hl'
        rw [hd, hls] at hal
        exact not_sourceAllowed hsc hY hal
      · exact hg e' P' hm hd l hl' hls
    · rcases List.mem_cons.mp ha' with heq | hm
      · cases heq
      · exact ha a' P' hm hc
  | @authorize Y log a _ hpass _ ih =>
    obtain ⟨hY, hg, ha⟩ := ih (fun hm => hno (List.mem_cons_of_mem _ hm))
    refine ⟨hY, fun e' P' he' hd l hl' hls => ?_, fun a' P' ha' hc hms => ?_⟩
    · rcases List.mem_cons.mp he' with heq | hm
      · cases heq
      · exact hg e' P' hm hd l hl' hls
    · rcases List.mem_cons.mp ha' with heq | hm
      · cases heq
        have hal := hpass.2
        rw [hc, hms] at hal
        exact not_sourceAllowed hsc hY hal
      · exact ha a' P' hm hc hms
  | claim _ _ ih => exact ih hno
  | @allowPeer Y log c' s' _ ih =>
    have hne : ¬ (c = c' ∧ s = s') := by
      rintro ⟨rfl, rfl⟩
      exact hno List.mem_cons_self
    obtain ⟨hY, hg, ha⟩ := ih (fun hm => hno (List.mem_cons_of_mem _ hm))
    refine ⟨by show (Y.peers.allow c' s') c s = false; rw [allow_other _ hne]; exact hY,
      fun e' P' he' hd l hl' hls => ?_, fun a' P' ha' hc hms => ?_⟩
    · rcases List.mem_cons.mp he' with heq | hm
      · cases heq
      · exact hg e' P' hm hd l hl' hls
    · rcases List.mem_cons.mp ha' with heq | hm
      · cases heq
      · exact ha a' P' hm hc hms
  | @deregisterPeer Y log c' s' _ ih =>
    obtain ⟨hY, hg, ha⟩ := ih (fun hm => hno (List.mem_cons_of_mem _ hm))
    refine ⟨?_, fun e' P' he' hd l hl' hls => ?_, fun a' P' ha' hc hms => ?_⟩
    · show (Y.peers.deregister c' s') c s = false
      by_cases hcs : c = c' ∧ s = s'
      · obtain ⟨rfl, rfl⟩ := hcs; exact deregister_self _ _ _
      · rw [deregister_other _ hcs]; exact hY
    · rcases List.mem_cons.mp he' with heq | hm
      · cases heq
      · exact hg e' P' hm hd l hl' hls
    · rcases List.mem_cons.mp ha' with heq | hm
      · cases heq
      · exact ha a' P' hm hc hms

/-! ## The complete swap -/

theorem swapSystem_eq : swapSystem = pairSystem 1 2 := rfl

theorem swapDest_one : swapDest 1 = 1 := by decide

theorem swapDest_two : swapDest 2 = 0 := by decide

theorem swap_wf : Wf swapSystem := by
  rw [swapSystem_eq]; exact pairSystem_wf (by decide) (by decide)

theorem swap_legA_mem : (⟨0, 1⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs := List.mem_cons_self

theorem swap_legB_mem : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs :=
  List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem swap_committedOnTime :
    ∀ l ∈ (mixedFlow 1 1 2).legs, CommittedOnTime (fun _ b => b) swapSystem (mixedFlow 1 1 2) l := by
  intro l hl'
  rcases List.mem_cons.mp hl' with rfl | hl'
  · refine ⟨0, le_refl _, ?_⟩
    show (1 : UInt256) ∈ keys (toAbs (swapSystem.tree 0 0))
    rw [swapSystem_eq, pairSystem_tree_zero]
    exact mem_insertSetup (by decide)
  · obtain rfl := List.mem_singleton.mp hl'
    refine ⟨0, le_refl _, ?_⟩
    show (2 : UInt256) ∈ keys (toAbs (swapSystem.tree 1 0))
    rw [swapSystem_eq, pairSystem_tree_one]
    exact mem_insertSetup (by decide)

/-- Leg `⟨0, 1⟩` appended on chain `0`. -/
def swapM1 : Managers := setAt emptyManagers 0 ((emptyManagers 0).set 1 1 .Committed)

/-- …and leg `⟨1, 2⟩` on chain `1`. -/
def swapM2 : Managers := setAt swapM1 1 ((swapM1 1).set 1 2 .Committed)

theorem swapM2_legA : stateOf swapM2 ⟨1, 1, 0⟩ = .Committed := by
  rw [swapM2, stateOf_setAt_other (by decide), swapM1, stateOf_setAt_self]

theorem swapM2_legB : stateOf swapM2 ⟨1, 2, 1⟩ = .Committed := by
  rw [swapM2]; exact stateOf_setAt_self _ _ _ _ _

theorem swap_run_appends (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
      ⟨emptyManagers, allPeersAllowed⟩ ⟨swapM2, allPeersAllowed⟩ [] := by
  have h1 : RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
      ⟨emptyManagers, allPeersAllowed⟩ ⟨swapM1, allPeersAllowed⟩ [] :=
    RunAtV35.append (Y := ⟨emptyManagers, allPeersAllowed⟩) (c := 0) (f := 1) (b := 1)
      RunAtV35.refl rfl
  have hg : AppendGuard (swapM1 1) 1 2 := by
    show stateOf swapM1 ⟨1, 2, 1⟩ = .Unset
    rw [swapM1, stateOf_setAt_other (by decide), stateOf_emptyManagers]
  exact RunAtV35.append (Y := ⟨swapM1, allPeersAllowed⟩) (c := 1) (f := 1) (b := 2) h1 hg

theorem swap_gateA (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    GateCallPassesAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest allPeersAllowed
      (pairExec h z0 hl ⟨0, 1⟩) :=
  executedViaByAtV35_of_allPeers (pairExec_verified h z0 hl swap_legA_mem)

theorem swap_run (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
      ⟨emptyManagers, allPeersAllowed⟩ ⟨swapM2, allPeersAllowed.deregister 0 1⟩
      [.deregisterPeer 0 1, .gate (pairExec h z0 hl ⟨0, 1⟩) allPeersAllowed] :=
  RunAtV35.deregisterPeer (Y := ⟨swapM2, allPeersAllowed⟩) 0 1
    (RunAtV35.gate (Y := ⟨swapM2, allPeersAllowed⟩) _ (swap_run_appends h z0 hl) (swap_gateA h z0 hl))

theorem swap_legB_gate_closed (h : Hash) (z0 : UInt256) (hl : LeafHash) (ev : GateEvidence) :
    ¬ ExecutedViaByAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem
      (allPeersAllowed.deregister 0 1) (swapDest 2) (mixedFlow 1 1 2) ev ⟨1, 2⟩ := by
  intro hex
  have hal := hex.allowed ⟨1, 2⟩ swap_legB_mem
  rw [swapDest_two] at hal
  exact not_sourceAllowed (by decide) (deregister_self _ _ _) hal

theorem swap_stranded_by_deregistration (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    Wf swapSystem
      ∧ DataAvailable h z0 hl swapSystem (honestAccess h z0 hl swapSystem)
      ∧ FlowFinalizableBy h z0 hl (fun _ b => b) swapSystem (honestAccess h z0 hl swapSystem)
          (mixedFlow 1 1 2)
      ∧ ∃ (Y : WorldAtV35) (log : List CallAtV35) (e : ExecCall),
          RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
              ⟨emptyManagers, allPeersAllowed⟩ Y log
            ∧ log = [.deregisterPeer 0 1, .gate e allPeersAllowed]
            ∧ e.flow = mixedFlow 1 1 2 ∧ e.leg = ⟨0, 1⟩
            ∧ Y.peers = allPeersAllowed.deregister 0 1
            ∧ stateOf Y.mgrs (obligationOf (mixedFlow 1 1 2) ⟨0, 1⟩) = .Committed
            ∧ stateOf Y.mgrs (obligationOf (mixedFlow 1 1 2) ⟨1, 2⟩) = .Committed
            ∧ (∀ ev : GateEvidence, ¬ ExecutedViaByAtV35 h z0 hl (fun _ b => b) lengthFlowHash
                swapSystem Y.peers (swapDest 2) (mixedFlow 1 1 2) ev ⟨1, 2⟩)
            ∧ (∀ (Q : Peers) (c : Chain), ∀ m ∈ (mixedFlow 1 1 2).legs, ∀ (N : ℕ) (q : ImtProof),
                ¬ LegRefundableByAtV35 h z0 hl (fun _ b => b) swapSystem Q c (mixedFlow 1 1 2) m N q
                  ∨ AbsenceBreak h z0 hl swapSystem (mixedFlow 1 1 2).deadline m.chain N q)
            ∧ ∃ e' : ExecCall, e'.flow = mixedFlow 1 1 2 ∧ e'.leg = ⟨1, 2⟩
                ∧ RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
                    ⟨emptyManagers, allPeersAllowed⟩ ⟨Y.mgrs, Y.peers.allow 0 1⟩
                    (.gate e' (Y.peers.allow 0 1) :: .allowPeer 0 1 :: log) := by
  have hfin : FlowFinalizableBy h z0 hl (fun _ b => b) swapSystem (honestAccess h z0 hl swapSystem)
      (mixedFlow 1 1 2) := by
    rw [swapSystem_eq]; exact pair_flow_finalizable h z0 hl
  have hre := reallow_restores_gate (s := 1) (swap_run h z0 hl)
    (pairExec_verified h z0 hl swap_legB_mem) (by
      intro l hl'
      rcases List.mem_cons.mp hl' with rfl | hl'
      · exact Or.inr (Or.inl swapDest_two.symm)
      · obtain rfl := List.mem_singleton.mp hl'; exact Or.inl rfl)
  refine ⟨swap_wf, honestAccess_dataAvailable h z0 hl _, hfin,
    ⟨swapM2, allPeersAllowed.deregister 0 1⟩, _, pairExec h z0 hl ⟨0, 1⟩, swap_run h z0 hl, rfl,
    rfl, rfl, rfl, swapM2_legA, swapM2_legB, swap_legB_gate_closed h z0 hl,
    fun Q c m hm N q => committed_not_refundable_at_v35 swap_wf (swap_committedOnTime m hm) Q c N q,
    pairExec h z0 hl ⟨1, 2⟩, rfl, rfl, ?_⟩
  exact hre

/-! ## The incomplete swap -/

/-- Leg `⟨0, 1⟩` of `mixedFlow 0 1 2` appended on chain `0`. -/
def incM : Managers := setAt emptyManagers 0 ((emptyManagers 0).set 0 1 .Committed)

/-- The refund of leg `⟨0, 1⟩` on the honest absence proof of the missing leg `⟨1, 2⟩`, at the
late batch 1. -/
def incAuth (h : Hash) (z0 : UInt256) (hl : LeafHash) : AuthCall :=
  ⟨mixedFlow 0 1 2, ⟨0, 1⟩, ⟨1, 2⟩, 1, setupAbsence h z0 hl⟩

theorem inc_legA_mem : (⟨0, 1⟩ : FlowLeg) ∈ (mixedFlow 0 1 2).legs := List.mem_cons_self

theorem inc_legB_mem : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 0 1 2).legs :=
  List.mem_cons_of_mem _ (List.mem_singleton_self _)

theorem inc_legA_committed :
    CommittedOnTime (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨0, 1⟩ := by
  refine ⟨0, le_refl _, ?_⟩
  show (1 : UInt256) ∈ keys (toAbs ((mixedSystem 1).tree 0 0))
  rw [mixedSystem_tree_zero]
  exact mem_insertSetup (by decide)

theorem inc_legB_not_committed :
    ¬ CommittedOnTime (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩ := by
  rintro ⟨n, _, hmem⟩
  have hm : (2 : UInt256) ∈ keys (toAbs ((mixedSystem 1).tree 1 n)) := hmem
  rw [mixedSystem_tree_other (by decide)] at hm
  exact not_mem_setup (by decide) hm

theorem inc_run (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    RunAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1) swapDest
      ⟨emptyManagers, allPeersAllowed⟩ ⟨incM, allPeersAllowed.deregister 0 1⟩
      [.deregisterPeer 0 1] :=
  RunAtV35.deregisterPeer (Y := ⟨incM, allPeersAllowed⟩) 0 1
    (RunAtV35.append (Y := ⟨emptyManagers, allPeersAllowed⟩) (c := 0) (f := 0) (b := 1)
      RunAtV35.refl rfl)

theorem incAuth_verified (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    (incAuth h z0 hl).Verified h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
      (mixedSystem 1) :=
  ⟨(honest_flowHash_no_clash _).1, inc_legA_mem, inc_legB_mem,
    setupAbsence_refundable (F := mixedFlow 0 1 2) (leg := ⟨1, 2⟩) (N := 0)
      (by show (0 : ℕ) < 1; norm_num) (mixedSystem_tree_other (by decide) 0)
      (mixedSystem_height_other (by decide) 0) (by show (0 : UInt256) < 2; decide)⟩

theorem inc_guard : AuthorizeGuard (incM 0) 0 1 := by
  show stateOf incM ⟨0, 1, 0⟩ = .Committed
  rw [incM]; exact stateOf_setAt_self _ _ _ _ _

theorem incomplete_swap_refund_stranded (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    Wf (mixedSystem 1)
      ∧ ∃ (Y : WorldAtV35) (log : List CallAtV35) (a : AuthCall),
          RunAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1) swapDest
              ⟨emptyManagers, allPeersAllowed⟩ Y log
            ∧ log = [.deregisterPeer 0 1]
            ∧ Y.peers = allPeersAllowed.deregister 0 1
            ∧ stateOf Y.mgrs (obligationOf (mixedFlow 0 1 2) ⟨0, 1⟩) = .Committed
            ∧ ¬ CommittedOnTime (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
            ∧ a.flow = mixedFlow 0 1 2 ∧ a.leg = ⟨0, 1⟩ ∧ a.missing = ⟨1, 2⟩
            ∧ a.Verified h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1)
            ∧ ¬ AbsenceBreak h z0 hl (mixedSystem 1) (mixedFlow 0 1 2).deadline 1 a.batch a.proof
            ∧ AuthorizeGuard (Y.mgrs 0) 0 1
            ∧ (∀ m ∈ (mixedFlow 0 1 2).legs, ∀ (N : ℕ) (q : ImtProof),
                ¬ LegRefundableByAtV35 h z0 hl (fun _ b => b) (mixedSystem 1) Y.peers 0
                    (mixedFlow 0 1 2) m N q
                  ∨ (m = ⟨0, 1⟩
                    ∧ AbsenceBreak h z0 hl (mixedSystem 1) (mixedFlow 0 1 2).deadline 0 N q))
            ∧ (∀ (Q : Peers) (d : Chain) (ev : GateEvidence) (l : FlowLeg),
                ¬ ExecutedViaByAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
                    (mixedSystem 1) Q d (mixedFlow 0 1 2) ev l
                  ∨ InclusionBreak h z0 hl (mixedSystem 1) 1 (ev ⟨1, 2⟩).1 (ev ⟨1, 2⟩).2)
            ∧ RunAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1)
                swapDest ⟨emptyManagers, allPeersAllowed⟩
                ⟨setAt Y.mgrs 0 ((Y.mgrs 0).set 0 1 .Revertable), Y.peers.allow 0 1⟩
                (.authorize a (Y.peers.allow 0 1) :: .allowPeer 0 1 :: log) := by
  have hS : Wf (mixedSystem 1) := mixedSystem_wf (by decide)
  have h10 : (1 : Chain) ≠ 0 := by decide
  refine ⟨hS, ⟨incM, allPeersAllowed.deregister 0 1⟩, _, incAuth h z0 hl, inc_run h z0 hl, rfl,
    rfl, ?_, inc_legB_not_committed, rfl, rfl, rfl, incAuth_verified h z0 hl,
    setupAbsence_no_break (N := 0) (by show (0 : ℕ) < 1; norm_num)
      (mixedSystem_tree_other h10 0) (mixedSystem_height_other h10 0),
    inc_guard, ?_, ?_, reallow_restores_refund (inc_run h z0 hl) (incAuth_verified h z0 hl) inc_guard⟩
  · show stateOf incM ⟨0, 1, 0⟩ = .Committed
    rw [incM]; exact stateOf_setAt_self _ _ _ _ _
  · intro m hm N q
    rcases List.mem_cons.mp hm with rfl | hm'
    · rcases committed_not_refundable_at_v35 hS inc_legA_committed
          (allPeersAllowed.deregister 0 1) 0 N q with hn | hb
      · exact Or.inl hn
      · exact Or.inr ⟨rfl, hb⟩
    · obtain rfl := List.mem_singleton.mp hm'
      exact Or.inl fun hr => not_sourceAllowed h10 (deregister_self _ _ _) hr.1
  · intro Q d ev l
    exact missing_blocks_gate_at_v35 inc_legB_mem inc_legB_not_committed Q d ev l

/-! ## The characterisation, on both swaps -/

theorem stranded_iff_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    Wf swapSystem ∧ FlowIdChecked lengthFlowHash (mixedFlow 1 1 2)
      ∧ FlowWf (fun _ b => b) (mixedFlow 1 1 2)
      ∧ (∀ l ∈ (mixedFlow 1 1 2).legs, CommittedOnTime (fun _ b => b) swapSystem (mixedFlow 1 1 2) l)
      ∧ StrandedOrBreakAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem
          (allPeersAllowed.deregister 0 1) (swapDest 2) (mixedFlow 1 1 2) ⟨1, 2⟩
      ∧ ¬ StrandedOrBreakAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem allPeersAllowed
          (swapDest 2) (mixedFlow 1 1 2) ⟨1, 2⟩
      ∧ Wf (mixedSystem 1) ∧ FlowIdChecked (honestFlowHash (mixedFlow 0 1 2)) (mixedFlow 0 1 2)
      ∧ FlowWf (fun _ b => b) (mixedFlow 0 1 2)
      ∧ (∀ l ∈ (mixedFlow 0 1 2).legs, SettledAfterDeadline (mixedSystem 1) (mixedFlow 0 1 2) l)
      ∧ ¬ CommittedOnTime (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ StrandedOrBreakAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
          (mixedSystem 1) (allPeersAllowed.deregister 0 1) (swapDest 1) (mixedFlow 0 1 2) ⟨0, 1⟩
      ∧ ¬ StrandedOrBreakAtV35 h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
          (mixedSystem 1) allPeersAllowed (swapDest 1) (mixedFlow 0 1 2) ⟨0, 1⟩ := by
  have h10 : (1 : Chain) ≠ 0 := by decide
  -- the complete swap
  have hwfA : FlowWf (fun _ b => b) (mixedFlow 1 1 2) := by
    intro l hl'
    rcases List.mem_cons.mp hl' with rfl | hl'
    · show (1 : UInt256) ≠ 0; decide
    · obtain rfl := List.mem_singleton.mp hl'; show (2 : UInt256) ≠ 0; decide
  have hprogA : ∀ l ∈ (mixedFlow 1 1 2).legs,
      ¬ CommittedOnTime (fun _ b => b) swapSystem (mixedFlow 1 1 2) l →
        SettledAfterDeadline swapSystem (mixedFlow 1 1 2) l :=
    fun l hl' hn => absurd (swap_committedOnTime l hl') hn
  have iffA := fun P d => stranded_iff_at_v35 (h := h) (z0 := z0) (hl := hl) swap_wf
    lengthFlowHash_checks_mixed hwfA hprogA swap_legB_mem P d
  -- the incomplete swap
  have hS : Wf (mixedSystem 1) := mixedSystem_wf (by decide)
  have hchkB : FlowIdChecked (honestFlowHash (mixedFlow 0 1 2)) (mixedFlow 0 1 2) :=
    (honest_flowHash_no_clash _).1
  have hwfB : FlowWf (fun _ b => b) (mixedFlow 0 1 2) := by
    intro l hl'
    rcases List.mem_cons.mp hl' with rfl | hl'
    · show (1 : UInt256) ≠ 0; decide
    · obtain rfl := List.mem_singleton.mp hl'; show (2 : UInt256) ≠ 0; decide
  have hsettled : ∀ l ∈ (mixedFlow 0 1 2).legs,
      SettledAfterDeadline (mixedSystem 1) (mixedFlow 0 1 2) l :=
    fun _ _ => ⟨1, by show (0 : ℕ) < 1; norm_num⟩
  have iffB := fun P d => stranded_iff_at_v35 (h := h) (z0 := z0) (hl := hl) hS hchkB hwfB
    (fun l hl' _ => hsettled l hl') inc_legA_mem P d
  refine ⟨swap_wf, lengthFlowHash_checks_mixed, hwfA, swap_committedOnTime,
    (iffA _ _).2 (Or.inl ⟨swap_committedOnTime, ⟨1, 2⟩, swap_legB_mem, ?_⟩), ?_,
    hS, hchkB, hwfB, hsettled, inc_legB_not_committed,
    (iffB _ _).2 (Or.inr ⟨⟨⟨1, 2⟩, inc_legB_mem, inc_legB_not_committed⟩, ?_⟩), ?_⟩
  · rw [swapDest_two]
    exact not_sourceAllowed (by decide) (deregister_self _ _ _)
  · intro hst
    rcases (iffA _ _).1 hst with ⟨_, l, _, hn⟩ | ⟨⟨l, hl', hn⟩, _⟩
    · exact hn (sourceAllowed_allPeers _ _)
    · exact hn (swap_committedOnTime l hl')
  · intro m hm hnot
    rcases List.mem_cons.mp hm with rfl | hm'
    · exact absurd inc_legA_committed hnot
    · obtain rfl := List.mem_singleton.mp hm'
      exact not_sourceAllowed h10 (deregister_self _ _ _)
  · intro hst
    rcases (iffB _ _).1 hst with ⟨hall, _⟩ | ⟨_, hblock⟩
    · exact inc_legB_not_committed (hall ⟨1, 2⟩ inc_legB_mem)
    · exact hblock ⟨1, 2⟩ inc_legB_mem inc_legB_not_committed (sourceAllowed_allPeers _ _)

/-! ## The pin's forged-sibling execution at v35 -/

theorem forged_sibling_execution_needs_allowed_forger (h : Hash) (z0 : UInt256) :
    ∃ ev : GateEvidence,
      ExecutedViaBy h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
          (mixedSystem 1) (mixedFlow 0 1 2) ev ⟨0, 1⟩
        ∧ ¬ InclusionBreak h z0 toyLeafHash (mixedSystem 1) 0 (ev ⟨0, 1⟩).1 (ev ⟨0, 1⟩).2
        ∧ InclusionBreak h z0 toyLeafHash (mixedSystem 1) 1 (ev ⟨1, 2⟩).1 (ev ⟨1, 2⟩).2
        ∧ ∀ (P : Peers) (d : Chain),
            ExecutedViaByAtV35 h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
                (mixedSystem 1) P d (mixedFlow 0 1 2) ev ⟨0, 1⟩
              ↔ SourceAllowed P d 0 ∧ SourceAllowed P d 1 := by
  obtain ⟨_, _, _, _, evF, _, nbA, hex, brkB, _, _, _⟩ :=
    pinned_gate_break_fires_only_on_stranded_leg h z0
  refine ⟨evF, hex, nbA, brkB, fun P d => ?_⟩
  rw [executedViaByAtV35_iff]
  constructor
  · rintro ⟨_, hall⟩
    exact ⟨hall ⟨0, 1⟩ inc_legA_mem, hall ⟨1, 2⟩ inc_legB_mem⟩
  · rintro ⟨h0, h1⟩
    refine ⟨hex, fun l hl' => ?_⟩
    rcases List.mem_cons.mp hl' with rfl | hl'
    · exact h0
    · obtain rfl := List.mem_singleton.mp hl'; exact h1

/-! ## A forged absence proof about a foreign chain -/

@[simp] lemma foreignPaddedSystem_tree_zero (a b y : UInt256) (n : ℕ) :
    (foreignPaddedSystem a b y).tree 0 n = threeLeafTree a b := by simp [foreignPaddedSystem]

@[simp] lemma foreignPaddedSystem_tree_one (a b y : UInt256) (n : ℕ) :
    (foreignPaddedSystem a b y).tree 1 n = insert setup y 0 := by
  simp [foreignPaddedSystem, (by decide : (1 : Chain) ≠ 0)]

lemma foreignPaddedSystem_tree_other {a b y : UInt256} {c : Chain} (h0 : c ≠ 0) (h1 : c ≠ 1)
    (n : ℕ) : (foreignPaddedSystem a b y).tree c n = setup := by
  simp [foreignPaddedSystem, h0, h1]

@[simp] lemma foreignPaddedSystem_height_zero (a b y : UInt256) (n : ℕ) :
    (foreignPaddedSystem a b y).height 0 n = 2 := by simp [foreignPaddedSystem]

@[simp] lemma foreignPaddedSystem_height_one (a b y : UInt256) (n : ℕ) :
    (foreignPaddedSystem a b y).height 1 n = 1 := by
  simp [foreignPaddedSystem, (by decide : (1 : Chain) ≠ 0)]

lemma foreignPaddedSystem_height_other {a b y : UInt256} {c : Chain} (h0 : c ≠ 0) (h1 : c ≠ 1)
    (n : ℕ) : (foreignPaddedSystem a b y).height c n = 0 := by
  simp [foreignPaddedSystem, h0, h1]

lemma foreignPaddedSystem_wf {a b y : UInt256} (ha : 0 < a) (hab : a < b) (hy : 0 < y) :
    Wf (foreignPaddedSystem a b y) := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c
    by_cases h0 : c = 0
    · subst h0
      rw [foreignPaddedSystem_tree_zero]
      exact Reaches.tail (Reaches.tail Reaches.refl hg1) hg2
    by_cases h1 : c = 1
    · subst h1
      rw [foreignPaddedSystem_tree_one]
      exact Reaches.tail Reaches.refl (setup_insertGuard hy)
    rw [foreignPaddedSystem_tree_other h0 h1]
    exact Reaches.refl
  · intro c n
    exact Reaches.refl
  · intro c i j hij
    exact hij
  · intro c n
    by_cases h0 : c = 0
    · subst h0
      rw [foreignPaddedSystem_tree_zero, foreignPaddedSystem_height_zero]
      show (3 : ℕ) ≤ 2 ^ 2
      norm_num
    by_cases h1 : c = 1
    · subst h1
      rw [foreignPaddedSystem_tree_one, foreignPaddedSystem_height_one, insertSetup_leafCount]
      norm_num
    rw [foreignPaddedSystem_tree_other h0 h1, foreignPaddedSystem_height_other h0 h1]
    show (1 : ℕ) ≤ 2 ^ 0
    norm_num

theorem foreign_forged_refund_needs_allowed_forger (h : Hash) (hl : LeafHash) (a b y : UInt256)
    (ha : 0 < a) (hab : a < b) (hy : 0 < y) :
    Wf (foreignPaddedSystem a b y)
      ∧ ∃ (ev : GateEvidence) (q : ImtProof) (r : AuthCall),
          ExecutedViaBy h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (honestFlowHash (foreignFlow a y))
              (foreignPaddedSystem a b y) (foreignFlow a y) ev ⟨1, y⟩
            ∧ ¬ GateBreak h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y) (foreignFlow a y) ev
            ∧ LegRefundableBy h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (foreignPaddedSystem a b y)
                (foreignFlow a y) ⟨0, a⟩ 0 q
            ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y)
                (foreignFlow a y).deadline 0 0 q
            ∧ r = ⟨foreignFlow a y, ⟨1, y⟩, ⟨0, a⟩, 0, q⟩
            ∧ (∃ (Ms : Managers) (log : List CheckedCall),
                RunLog h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (honestFlowHash (foreignFlow a y))
                    (foreignPaddedSystem a b y) emptyManagers Ms log
                  ∧ CheckedCall.execute ⟨foreignFlow a y, ev, ⟨1, y⟩⟩ ∈ log
                  ∧ CheckedCall.authorize r ∈ log
                  ∧ Refunded Ms (obligationOf (foreignFlow a y) ⟨1, y⟩))
            ∧ (∃ (Y : WorldAtV35) (log : List CallAtV35),
                RunAtV35 h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (honestFlowHash (foreignFlow a y))
                    (foreignPaddedSystem a b y) (fun _ => 2) ⟨emptyManagers, allPeersAllowed⟩ Y log
                  ∧ CallAtV35.gate ⟨foreignFlow a y, ev, ⟨1, y⟩⟩ allPeersAllowed ∈ log
                  ∧ CallAtV35.authorize r allPeersAllowed ∈ log
                  ∧ Refunded Y.mgrs (obligationOf (foreignFlow a y) ⟨1, y⟩))
            ∧ ∀ P : Peers,
                LegRefundableByAtV35 h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (foreignPaddedSystem a b y)
                    P 1 (foreignFlow a y) ⟨0, a⟩ 0 q
                  ↔ P 1 0 = true := by
  have hS := foreignPaddedSystem_wf (y := y) ha hab hy
  obtain ⟨_, _, hN⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  obtain ⟨_, hpad⟩ := padding_countermodel_locates_padding_hit h hl a b
  have hmemA : (⟨0, a⟩ : FlowLeg) ∈ (foreignFlow a y).legs := List.mem_cons_self
  have hmemB : (⟨1, y⟩ : FlowLeg) ∈ (foreignFlow a y).legs :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  have hcount0 : ((foreignPaddedSystem a b y).tree 0 0).leafCount = 3 := by
    rw [foreignPaddedSystem_tree_zero]; rfl
  have hcount1 : ((foreignPaddedSystem a b y).tree 1 0).leafCount = 2 := by
    rw [foreignPaddedSystem_tree_one, insertSetup_leafCount]
  have acc0 : Accepts h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y) 0 0 a
      (honestProof h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y) 0 0 1) :=
    honestProof_accepts hS (by rw [hcount0]; norm_num)
      (by rw [foreignPaddedSystem_tree_zero, threeLeafTree_leaf_one_value])
  have acc1 : Accepts h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y) 1 0 y
      (honestProof h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y) 1 0 1) :=
    honestProof_accepts hS (by rw [hcount1]; norm_num)
      (by rw [foreignPaddedSystem_tree_one, insertSetup_leaf_one_value])
  let ev : GateEvidence := fun l => (0, honestProof h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y) l.chain 0 1)
  have hchk : FlowIdChecked (honestFlowHash (foreignFlow a y)) (foreignFlow a y) :=
    (honest_flowHash_no_clash _).1
  have hex : ExecutedViaBy h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (honestFlowHash (foreignFlow a y))
      (foreignPaddedSystem a b y) (foreignFlow a y) ev ⟨1, y⟩ := by
    refine ⟨hmemB, hchk, fun l hl' => ?_⟩
    rcases List.mem_cons.mp hl' with rfl | hl'
    · exact ⟨le_refl _, acc0⟩
    · obtain rfl := List.mem_singleton.mp hl'
      exact ⟨le_refl _, acc1⟩
  have hnb : ¬ GateBreak h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y) (foreignFlow a y) ev := by
    rintro ⟨l, hl', hb⟩
    rcases List.mem_cons.mp hl' with rfl | hl'
    · exact honestProof_no_break h _ hl _ 0 0 1 (by rw [hcount0]; norm_num) hb
    · obtain rfl := List.mem_singleton.mp hl'
      exact honestProof_no_break h _ hl _ 1 0 1 (by rw [hcount1]; norm_num) hb
  let q : ImtProof :=
    ⟨⟨0, 0, 0⟩, 3, honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3, 2⟩
  have href : LegRefundableBy h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (foreignPaddedSystem a b y)
      (foreignFlow a y) ⟨0, a⟩ 0 q :=
    Or.inr ⟨⟨le_refl 0, fun m hm => hm⟩, hN⟩
  have habs : AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (foreignPaddedSystem a b y)
      (foreignFlow a y).deadline 0 0 q :=
    Or.inr ⟨le_refl 0, hpad⟩
  let r : AuthCall := ⟨foreignFlow a y, ⟨1, y⟩, ⟨0, a⟩, 0, q⟩
  have hav : r.Verified h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (honestFlowHash (foreignFlow a y))
      (foreignPaddedSystem a b y) := ⟨hchk, hmemB, hmemA, href⟩
  let M1 : Managers := setAt emptyManagers 1 ((emptyManagers 1).set 0 y .Committed)
  have hguard : AuthorizeGuard (M1 1) 0 y := by
    show stateOf M1 ⟨0, y, 1⟩ = .Committed
    exact stateOf_setAt_self _ _ _ _ _
  have hrefunded : Refunded (setAt M1 1 ((M1 1).set 0 y .Revertable))
      (obligationOf (foreignFlow a y) ⟨1, y⟩) := by
    show 2 ≤ rank (stateOf (setAt M1 1 ((M1 1).set 0 y .Revertable)) ⟨0, y, 1⟩)
    rw [stateOf_setAt_self]; simp [rank]
  have happ : RunLog h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (honestFlowHash (foreignFlow a y))
      (foreignPaddedSystem a b y) emptyManagers M1 [] :=
    RunLog.append (c := 1) (f := 0) (b := y) RunLog.refl rfl
  have hrun := RunLog.authorize r (RunLog.execute ⟨foreignFlow a y, ev, ⟨1, y⟩⟩ happ hex) hav hguard
  have v1 : RunAtV35 h (hl ⟨0, 0, 0⟩) hl (fun _ k => k) (honestFlowHash (foreignFlow a y))
      (foreignPaddedSystem a b y) (fun _ => 2) ⟨emptyManagers, allPeersAllowed⟩
      ⟨M1, allPeersAllowed⟩ [] :=
    RunAtV35.append (Y := ⟨emptyManagers, allPeersAllowed⟩) (c := 1) (f := 0) (b := y)
      RunAtV35.refl rfl
  have v2 := RunAtV35.gate (Y := ⟨M1, allPeersAllowed⟩) ⟨foreignFlow a y, ev, ⟨1, y⟩⟩ v1
    (executedViaByAtV35_of_allPeers hex)
  have v3 := RunAtV35.authorize (Y := ⟨M1, allPeersAllowed⟩) r v2
    ⟨hav, sourceAllowed_allPeers _ _⟩ hguard
  refine ⟨hS, ev, q, r, hex, hnb, href, habs, rfl,
    ⟨_, _, hrun, List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self, hrefunded⟩,
    ⟨_, _, v3, List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self, hrefunded⟩,
    fun P => ⟨fun hr => ?_, fun ht => ⟨Or.inr ht, href⟩⟩⟩
  rcases hr.1 with heq | ht
  · exact absurd heq (by show (0 : Chain) ≠ 1; decide)
  · exact ht

/-! ## Witnesses -/

theorem refundBreak_marks {h : Hash} {z0 : UInt256} {hl : LeafHash} {fh : FlowHash} {S : System}
    {F : Flow} {ev : GateEvidence} {o : Obligation} {log : List AuthCall}
    (hb : RefundBreak h z0 hl fh S F ev o log) : ∃ a ∈ log, obligationOf a.flow a.leg = o := by
  cases hb with
  | flowIdClash a ha hobl _ => exact ⟨a, ha, hobl⟩
  | inclusion a ha hobl _ _ => exact ⟨a, ha, hobl⟩
  | absence a ha hobl _ _ => exact ⟨a, ha, hobl⟩

/-- The swap run, with the refund of the other one-leg flow on chain `2` before the gate call. -/
def safeM3 : Managers := setAt swapM2 2 ((swapM2 2).set 0 3 .Committed)

def safeM4 : Managers := setAt safeM3 2 ((safeM3 2).set 0 3 .Revertable)

theorem safety_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (Y : WorldAtV35) (log : List CallAtV35) (ev : GateEvidence),
      Wf swapSystem ∧ DataAvailable h z0 hl swapSystem (honestAccess h z0 hl swapSystem)
        ∧ ExecutedViaByAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem allPeersAllowed
            (swapDest 1) (mixedFlow 1 1 2) ev ⟨0, 1⟩
        ∧ RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
            ⟨emptyManagers, allPeersAllowed⟩ Y log
        ∧ CallAtV35.gate ⟨mixedFlow 1 1 2, ev, ⟨0, 1⟩⟩ allPeersAllowed ∈ log
        ∧ CallAtV35.deregisterPeer 0 1 ∈ log
        ∧ authLogAtV35 log ≠ []
        ∧ (∀ other ∈ (mixedFlow 1 1 2).legs,
            ¬ Refunded Y.mgrs (obligationOf (mixedFlow 1 1 2) other)
              ∧ ¬ RefundBreak h z0 hl lengthFlowHash swapSystem (mixedFlow 1 1 2) ev
                  (obligationOf (mixedFlow 1 1 2) other) (authLogAtV35 log)) := by
  have hg3 : AppendGuard (swapM2 2) 0 3 := by
    show stateOf swapM2 ⟨0, 3, 2⟩ = .Unset
    rw [swapM2, stateOf_setAt_other (by decide), swapM1, stateOf_setAt_other (by decide),
      stateOf_emptyManagers]
  have r3 : RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
      ⟨emptyManagers, allPeersAllowed⟩ ⟨safeM3, allPeersAllowed⟩ [] :=
    RunAtV35.append (Y := ⟨swapM2, allPeersAllowed⟩) (c := 2) (f := 0) (b := 3)
      (swap_run_appends h z0 hl) hg3
  have hg4 : AuthorizeGuard (safeM3 2) 0 3 := by
    show stateOf safeM3 ⟨0, 3, 2⟩ = .Committed
    rw [safeM3]; exact stateOf_setAt_self _ _ _ _ _
  have r4 : RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem swapDest
      ⟨emptyManagers, allPeersAllowed⟩ ⟨safeM4, allPeersAllowed⟩
      [.authorize (strandedAuth h z0 hl) allPeersAllowed] :=
    RunAtV35.authorize (Y := ⟨safeM3, allPeersAllowed⟩) (strandedAuth h z0 hl) r3
      ⟨strandedAuth_verified h z0 hl, sourceAllowed_allPeers _ _⟩ hg4
  have r5 := RunAtV35.gate (Y := ⟨safeM4, allPeersAllowed⟩) (pairExec h z0 hl ⟨0, 1⟩) r4
    (swap_gateA h z0 hl)
  have r6 := RunAtV35.deregisterPeer (Y := ⟨safeM4, allPeersAllowed⟩) 0 1 r5
  have hstate : ∀ other ∈ (mixedFlow 1 1 2).legs,
      stateOf safeM4 (obligationOf (mixedFlow 1 1 2) other) = .Committed := by
    intro other ho
    rcases List.mem_cons.mp ho with rfl | ho
    · show stateOf safeM4 ⟨1, 1, 0⟩ = .Committed
      rw [safeM4, stateOf_setAt_other (by decide), safeM3, stateOf_setAt_other (by decide)]
      exact swapM2_legA
    · obtain rfl := List.mem_singleton.mp ho
      show stateOf safeM4 ⟨1, 2, 1⟩ = .Committed
      rw [safeM4, stateOf_setAt_other (by decide), safeM3, stateOf_setAt_other (by decide)]
      exact swapM2_legB
  refine ⟨_, _, pairEvidence h z0 hl, swap_wf, honestAccess_dataAvailable h z0 hl _,
    swap_gateA h z0 hl, r6, List.mem_cons_of_mem _ List.mem_cons_self, List.mem_cons_self,
    by simp [authLogAtV35, CallAtV35.authCall?], fun other ho => ⟨?_, ?_⟩⟩
  · show ¬ 2 ≤ rank (stateOf safeM4 (obligationOf (mixedFlow 1 1 2) other))
    rw [hstate other ho]; simp [rank]
  · intro hb
    obtain ⟨a, ha, hobl⟩ := refundBreak_marks hb
    have ha' : strandedAuth h z0 hl = a := by
      simpa [authLogAtV35, CallAtV35.authCall?] using ha
    subst ha'
    have hid := congrArg Obligation.flowId hobl
    exact absurd hid (by show (0 : UInt256) ≠ 1; decide)

theorem system_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg) (d : Chain) (Y : SysWorldAtV35) (log : List Obligation) (alog : List AuthCall),
      Wf S ∧ ExecutedViaByAtV35 h z0 hl cv fh S allPeersAllowed d F ev leg
        ∧ SysStepsAtV35 h z0 hl cv fh S ⟨genesisAll, allPeersAllowed⟩ Y log alog
        ∧ Y.peers = allPeersAllowed.deregister 0 1
        ∧ obligationOf F leg ∈ log ∧ alog ≠ []
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) alog
        ∧ ¬ Refunded Y.chains.mgrs (obligationOf F leg) := by
  obtain ⟨cv, fh, S, F, ev, leg, Y, log, alog, hS, hex, hrun, hlog, halog, _, hnb, hnr, _⟩ :=
    Contracts.AppendPath.SystemWitness h z0 hl
  exact ⟨cv, fh, S, F, ev, leg, 0, ⟨Y, allPeersAllowed.deregister 0 1⟩, log, alog, hS,
    executedViaByAtV35_of_allPeers hex,
    SysStepsAtV35.deregisterPeer (Y := ⟨Y, allPeersAllowed⟩) 0 1 (sysSteps_sysStepsAtV35 hrun),
    rfl, hlog, halog, hnb, hnr⟩

theorem safeM3_guard : AuthorizeGuard (safeM3 2) 0 3 := by
  show stateOf safeM3 ⟨0, 3, 2⟩ = .Committed
  rw [safeM3]; exact stateOf_setAt_self _ _ _ _ _

theorem reallow_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    (∃ ev : GateEvidence,
      ExecutedViaByAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem
        (allPeersAllowed.deregister 0 1) (swapDest 1) (mixedFlow 1 1 2) ev ⟨0, 1⟩)
      ∧ (∀ s, (allPeersAllowed.deregister 0 1) (swapDest 1) s = true
          → allPeersAllowed (swapDest 1) s = true)
      ∧ allPeersAllowed 0 1 = true
      ∧ ∃ (X Y : WorldAtV35) (log : List CallAtV35) (e : ExecCall) (a : AuthCall),
          RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem (fun _ => 2) X Y log
            ∧ X.peers 2 3 = false ∧ CallAtV35.allowPeer 2 3 ∉ log
            ∧ log = [.deregisterPeer 0 1, .gate e X.peers, .authorize a X.peers]
            ∧ e.flow = mixedFlow 1 1 2 ∧ e.leg = ⟨0, 1⟩
            ∧ a.leg = ⟨2, 3⟩ ∧ a.missing = ⟨2, 3⟩ := by
  -- the segment on chain `2`, which does not allow chain `3`
  have r1 : RunAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem (fun _ => 2)
      ⟨safeM3, allPeersAllowed.deregister 2 3⟩ ⟨safeM4, allPeersAllowed.deregister 2 3⟩
      [.authorize (strandedAuth h z0 hl) (allPeersAllowed.deregister 2 3)] :=
    RunAtV35.authorize (Y := ⟨safeM3, allPeersAllowed.deregister 2 3⟩) (strandedAuth h z0 hl)
      RunAtV35.refl ⟨strandedAuth_verified h z0 hl, Or.inl rfl⟩ safeM3_guard
  have hgate : GateCallPassesAtV35 h z0 hl (fun _ b => b) lengthFlowHash swapSystem (fun _ => 2)
      (allPeersAllowed.deregister 2 3) (pairExec h z0 hl ⟨0, 1⟩) := by
    refine executedViaByAtV35_iff.2 ⟨pairExec_verified h z0 hl swap_legA_mem, fun l hl' => ?_⟩
    show SourceAllowed (allPeersAllowed.deregister 2 3) 2 l.chain
    rcases List.mem_cons.mp hl' with rfl | hl'
    · exact Or.inr (by rw [deregister_other _ (by decide)]; rfl)
    · obtain rfl := List.mem_singleton.mp hl'
      exact Or.inr (by rw [deregister_other _ (by decide)]; rfl)
  have r2 := RunAtV35.gate (Y := ⟨safeM4, allPeersAllowed.deregister 2 3⟩)
    (pairExec h z0 hl ⟨0, 1⟩) r1 hgate
  have r3 := RunAtV35.deregisterPeer (Y := ⟨safeM4, allPeersAllowed.deregister 2 3⟩) 0 1 r2
  refine ⟨⟨pairEvidence h z0 hl, executedViaByAtV35_iff.2
      ⟨pairExec_verified h z0 hl swap_legA_mem, fun l hl' => ?_⟩⟩,
    fun _ _ => rfl, rfl,
    ⟨safeM3, allPeersAllowed.deregister 2 3⟩, _, _, pairExec h z0 hl ⟨0, 1⟩, strandedAuth h z0 hl,
    r3, deregister_self allPeersAllowed 2 3, by simp, rfl, rfl, rfl, rfl, rfl⟩
  rw [swapDest_one]
  rcases List.mem_cons.mp hl' with rfl | hl'
  · exact Or.inr (by rw [deregister_other _ (by decide)]; rfl)
  · obtain rfl := List.mem_singleton.mp hl'; exact Or.inl rfl

end Contracts.LegSourceFilterAtV35

/-! ## Certificates -/

namespace Contracts.LegSourceFilterAtV35

theorem GateAtV35IffPinGateAndSourcesAllowed : Properties.GateAtV35IffPinGateAndSourcesAllowed :=
  fun _ _ _ _ _ _ _ _ _ _ _ => executedViaByAtV35_iff

theorem GateMonotoneInPeersAtV35 : Properties.GateMonotoneInPeersAtV35 :=
  fun _ _ _ _ _ _ _ _ _ hPQ _ _ _ hex => gate_mono hPQ hex

theorem RefundMonotoneInPeersAtV35 : Properties.RefundMonotoneInPeersAtV35 :=
  fun _ _ _ _ _ _ _ _ hPQ _ _ _ _ hr => refund_mono hPQ hr

theorem DeregisterThenAllowIsIdentity : Properties.DeregisterThenAllowIsIdentity :=
  deregister_then_allow

theorem RunAtV35ProjectsToRunLog : Properties.RunAtV35ProjectsToRunLog :=
  fun _ _ _ _ _ _ _ _ _ _ hr => runAtV35_runLog hr

theorem RunLogIsRunAtV35UnderFullAllowance : Properties.RunLogIsRunAtV35UnderFullAllowance :=
  fun _ _ _ _ _ _ dst _ _ _ hr => runLog_runAtV35 dst hr

theorem ExecutedExcludesAnyRefundOrBreakAtV35 : Properties.ExecutedExcludesAnyRefundOrBreakAtV35 :=
  fun _ _ _ _ _ _ hS _ _ _ _ _ hex other hother Q c N q =>
    executed_excludes_any_refund_or_break_at_v35 hS hex other hother Q c N q

theorem NoneOrAllOrBreakAtV35 : Properties.NoneOrAllOrBreakAtV35 :=
  fun _ _ _ _ _ _ hS _ hDA P d F ev => none_or_all_or_break_at_v35 hS hDA P d F ev

theorem LoggedGateExcludesLoggedRefundOrAllowedBreakAtV35 :
    Properties.LoggedGateExcludesLoggedRefundOrAllowedBreakAtV35 :=
  fun _ _ _ _ _ _ hS _ _ _ _ hr _ _ he _ _ ha hid =>
    logged_gate_excludes_logged_refund_or_allowed_break_at_v35 hS hr he ha hid

theorem ExecutedObligationNeverRefundedOrBreakAtV35 :
    Properties.ExecutedObligationNeverRefundedOrBreakAtV35 :=
  fun _ _ _ _ _ _ hS _ _ _ _ _ hex _ _ _ _ hr => executed_freezes_flow_or_break_at_v35 hS hex hr _ rfl

theorem OneExecutionFreezesTheFlowOrBreakAtV35 : Properties.OneExecutionFreezesTheFlowOrBreakAtV35 :=
  fun _ _ _ _ _ _ hS _ _ _ _ _ hex _ _ _ _ hr _ _ =>
    executed_freezes_flow_or_break_at_v35 hS hex hr _ rfl

theorem ExecutedImpliesRealFlowFinalizableOrLoggedClashAtV35 :
    Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClashAtV35 :=
  fun _ _ _ _ _ _ hS _ hDA _ _ _ _ hr _ _ he _ hc hid =>
    executed_implies_real_flow_finalizable_or_logged_clash_at_v35 hS hDA hr he hc hid

theorem SysStepsAtV35ProjectsToSysSteps : Properties.SysStepsAtV35ProjectsToSysSteps :=
  fun _ _ _ _ _ _ _ _ _ _ hr => sysStepsAtV35_sysSteps hr

theorem SysStepsIsSysStepsAtV35UnderFullAllowance :
    Properties.SysStepsIsSysStepsAtV35UnderFullAllowance :=
  fun _ _ _ _ _ _ _ _ _ _ hr => sysSteps_sysStepsAtV35 hr

theorem SystemOncePerLegAtV35 : Properties.SystemOncePerLegAtV35 :=
  fun h z0 hl cv fh S _ Y log alog hr =>
    Contracts.AppendPath.SystemOncePerLeg h z0 hl cv fh S Y.chains log alog
      (sysStepsAtV35_sysSteps hr)

theorem SystemExecutedObligationNeverRefundedOrBreakAtV35 :
    Properties.SystemExecutedObligationNeverRefundedOrBreakAtV35 :=
  fun h z0 hl cv fh S hS _ _ F ev leg hex _ Y log alog hr =>
    Contracts.AppendPath.SystemExecutedObligationNeverRefundedOrBreak h z0 hl cv fh S hS F ev leg
      hex.toPin Y.chains log alog (sysStepsAtV35_sysSteps hr)

theorem SwapStrandedByDeregistrationAtV35 : Properties.SwapStrandedByDeregistrationAtV35 :=
  swap_stranded_by_deregistration

theorem IncompleteSwapRefundStrandedByDeregistrationAtV35 :
    Properties.IncompleteSwapRefundStrandedByDeregistrationAtV35 :=
  incomplete_swap_refund_stranded

theorem RefundEvidenceCompleteAtV35 : Properties.RefundEvidenceCompleteAtV35 :=
  fun _ _ _ _ _ hS _ _ hv hnot hlate P c hallow =>
    refund_evidence_complete_at_v35 hS hv hnot hlate P c hallow

theorem CompleteFlowGateOpenIffSourcesAllowedAtV35 :
    Properties.CompleteFlowGateOpenIffSourcesAllowedAtV35 :=
  fun _ _ _ _ _ _ hS _ hDA _ hchk hc _ hleg P d => complete_flow_gate_open_iff hS hDA hchk hc hleg P d

theorem StrandedIffAtV35 : Properties.StrandedIffAtV35 :=
  fun _ _ _ _ _ _ hS _ hchk hwf hprog _ hleg P d => stranded_iff_at_v35 hS hchk hwf hprog hleg P d

theorem StrandedIffAtV35Witness : Properties.StrandedIffAtV35Witness := stranded_iff_witness

theorem ReallowRestoresGateAtV35 : Properties.ReallowRestoresGateAtV35 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hr he hs => reallow_restores_gate hr he hs

theorem ReallowRestoresRefundAtV35 : Properties.ReallowRestoresRefundAtV35 :=
  fun _ _ _ _ _ _ _ _ _ _ _ hr ha hg => reallow_restores_refund hr ha hg

theorem BlockedUntilReallowedAtV35 : Properties.BlockedUntilReallowedAtV35 :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hr hsc hX hno => blocked_until_reallowed hr hsc hX hno

theorem ForgedSiblingExecutionNeedsAllowedForgerAtV35 :
    Properties.ForgedSiblingExecutionNeedsAllowedForgerAtV35 :=
  forged_sibling_execution_needs_allowed_forger

theorem ForeignForgedRefundNeedsAllowedForgerAtV35 :
    Properties.ForeignForgedRefundNeedsAllowedForgerAtV35 :=
  foreign_forged_refund_needs_allowed_forger

theorem SafetyAtV35Witness : Properties.SafetyAtV35Witness := safety_witness

theorem SystemAtV35Witness : Properties.SystemAtV35Witness := system_witness

theorem ReallowAtV35Witness : Properties.ReallowAtV35Witness := reallow_witness

end Contracts.LegSourceFilterAtV35
