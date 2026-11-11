import EraSpec.Protocol.InteropAtomicity.Properties.Pause
import EraSpec.Protocol.InteropAtomicity.Proofs.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg

/-!
# Proofs: pausing delays atomic flows and never unwinds them

Proofs of `EraSpec.Protocol.InteropAtomicity.Properties.Pause`.

* Section 1 is one induction, `pRun_runLog`: forgetting the flags maps each paused step to the
  `RunLog` step it restricts, and each `pause`/`unpause` to nothing.  Every safety result is then
  the matching `RunLog`/`ReachLog` result composed with it.
* Section 2 is `member_not_refundable_or_break` per leg, and over the run `refund_logged` plus
  `flowId_check_pins_legList_or_collision` (`committed_freezes_flow_or_break`).  The run-level
  persistence is an induction that tracks one flag.
* Sections 3 and 4 build the extension of the run explicitly.
-/

namespace Contracts.InteropPause

open MerkleSpec MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree
open Contracts.Atomicity Contracts.Timeout Contracts.Refund Contracts.FlowBinding
open Contracts.AtomicFlowManager

/-! ## Reading traces and flags -/

@[simp] theorem checkedCalls_nil : checkedCalls [] = [] := rfl

@[simp] theorem checkedCalls_append_step (c : Chain) (f b : UInt256) (tr : List Action) :
    checkedCalls (.append c f b :: tr) = checkedCalls tr := rfl

@[simp] theorem checkedCalls_execute (e : ExecCall) (tr : List Action) :
    checkedCalls (.execute e :: tr) = .execute e :: checkedCalls tr := rfl

@[simp] theorem checkedCalls_authorize (a : AuthCall) (tr : List Action) :
    checkedCalls (.authorize a :: tr) = .authorize a :: checkedCalls tr := rfl

@[simp] theorem checkedCalls_claim (c : Chain) (f b : UInt256) (tr : List Action) :
    checkedCalls (.claim c f b :: tr) = checkedCalls tr := rfl

@[simp] theorem checkedCalls_pause (c : Chain) (k : Pausable) (tr : List Action) :
    checkedCalls (.pause c k :: tr) = checkedCalls tr := rfl

@[simp] theorem checkedCalls_unpause (c : Chain) (k : Pausable) (tr : List Action) :
    checkedCalls (.unpause c k :: tr) = checkedCalls tr := rfl

theorem mem_checkedCalls_execute {e : ExecCall} {tr : List Action} (he : Action.execute e ∈ tr) :
    CheckedCall.execute e ∈ checkedCalls tr :=
  List.mem_filterMap.mpr ⟨.execute e, he, rfl⟩

theorem mem_checkedCalls_authorize {a : AuthCall} {tr : List Action}
    (ha : Action.authorize a ∈ tr) : CheckedCall.authorize a ∈ checkedCalls tr :=
  List.mem_filterMap.mpr ⟨.authorize a, ha, rfl⟩

theorem execute_mem_of_checked {e : ExecCall} {tr : List Action}
    (he : CheckedCall.execute e ∈ checkedCalls tr) : Action.execute e ∈ tr := by
  obtain ⟨a, ha, hsome⟩ := List.mem_filterMap.mp he
  cases a with
  | execute e' =>
    cases hsome
    exact ha
  | authorize _ => cases hsome
  | append _ _ _ => cases hsome
  | claim _ _ _ => cases hsome
  | pause _ _ => cases hsome
  | unpause _ _ => cases hsome

theorem authorize_mem_of_checked {a : AuthCall} {tr : List Action}
    (ha : CheckedCall.authorize a ∈ checkedCalls tr) : Action.authorize a ∈ tr := by
  obtain ⟨x, hx, hsome⟩ := List.mem_filterMap.mp ha
  cases x with
  | authorize a' =>
    cases hsome
    exact hx
  | execute _ => cases hsome
  | append _ _ _ => cases hsome
  | claim _ _ _ => cases hsome
  | pause _ _ => cases hsome
  | unpause _ _ => cases hsome

theorem Flags.set_same (P : Flags) (c : Chain) (k : Pausable) (v : Bool) :
    P.set c k v c k = v := by
  simp [Flags.set]

theorem Flags.set_other {P : Flags} {c c' : Chain} {k k' : Pausable} (v : Bool)
    (hne : ¬ (c' = c ∧ k' = k)) : P.set c k v c' k' = P c' k' := by
  simp only [Flags.set, ite_eq_right_iff]; intro hc; exact absurd hc hne

theorem noFlags_open_send (prof : Profile) (c : Chain) (b : UInt256) :
    SendOpen prof noFlags c b :=
  ⟨rfl, fun _ => rfl, fun _ => rfl⟩

theorem noFlags_open_exec (prof : Profile) (b : UInt256) : ExecOpen prof noFlags b :=
  fun _ => rfl

theorem noFlags_open_recover (prof : Profile) (c : Chain) (b : UInt256) :
    RecoverOpen prof noFlags c b :=
  fun _ => rfl

/-! ## Runs compose -/

theorem PRun.trans {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue} {fh : FlowHash}
    {S : System} {prof : Profile} {X Y Z : PState} {tr tr' : List Action}
    (h₁ : PRun h z0 hl cv fh S prof X Y tr) (h₂ : PRun h z0 hl cv fh S prof Y Z tr') :
    PRun h z0 hl cv fh S prof X Z (tr' ++ tr) := by
  induction h₂ with
  | refl => exact h₁
  | append _ hg ho ih => exact PRun.append ih hg ho
  | execute e _ hv ho ih => exact PRun.execute e ih hv ho
  | authorize a _ hv hg ih => exact PRun.authorize a ih hv hg
  | claim _ hg ho ih => exact PRun.claim ih hg ho
  | pause _ hf ih => exact PRun.pause ih hf
  | unpause _ hf ih => exact PRun.unpause ih hf

/-! ## 1. Pause only removes steps -/

/-- **A PAUSED RUN IS A RUN.** -/
theorem pRun_runLog {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue} {fh : FlowHash}
    {S : System} {prof : Profile} {X Y : PState} {tr : List Action}
    (hr : PRun h z0 hl cv fh S prof X Y tr) : RunLog h z0 hl cv fh S X.mgrs Y.mgrs (checkedCalls tr) := by
  induction hr with
  | refl => exact RunLog.refl
  | append _ hg _ ih => exact RunLog.append ih hg
  | execute e _ hv _ ih => exact RunLog.execute e ih hv
  | authorize a _ hv hg ih => exact RunLog.authorize a ih hv hg
  | claim _ hg _ ih => exact RunLog.claim ih hg
  | pause _ _ ih => exact ih
  | unpause _ _ ih => exact ih

theorem pRun_reachLog {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {prof : Profile} {X Y : PState} {tr : List Action}
    (hr : PRun h z0 hl cv fh S prof X Y tr) :
    ReachLog h z0 hl cv fh S X.mgrs Y.mgrs (authCalls (checkedCalls tr)) :=
  runLog_reachLog (pRun_runLog hr)

/-- **WITH NOTHING PAUSED, NOTHING IS LOST.** -/
theorem runLog_pRun {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue} {fh : FlowHash}
    {S : System} (prof : Profile) {Ms Ns : Managers} {log : List CheckedCall}
    (hr : RunLog h z0 hl cv fh S Ms Ns log) :
    ∃ tr, PRun h z0 hl cv fh S prof ⟨Ms, noFlags⟩ ⟨Ns, noFlags⟩ tr ∧ checkedCalls tr = log := by
  induction hr with
  | refl => exact ⟨[], PRun.refl, rfl⟩
  | @append _ _ c f b _ hg ih =>
    obtain ⟨tr, htr, hlog⟩ := ih
    exact ⟨.append c f b :: tr, PRun.append htr hg (noFlags_open_send prof c b), hlog⟩
  | execute e _ hv ih =>
    obtain ⟨tr, htr, hlog⟩ := ih
    exact ⟨.execute e :: tr, PRun.execute e htr hv (noFlags_open_exec prof _),
      by rw [checkedCalls_execute, hlog]⟩
  | authorize a _ hv hg ih =>
    obtain ⟨tr, htr, hlog⟩ := ih
    exact ⟨.authorize a :: tr, PRun.authorize a htr hv hg, by rw [checkedCalls_authorize, hlog]⟩
  | @claim _ _ c f b _ hg ih =>
    obtain ⟨tr, htr, hlog⟩ := ih
    exact ⟨.claim c f b :: tr, PRun.claim htr hg (noFlags_open_recover prof c b), hlog⟩

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED, OR A LOCATED BREAK, UNDER PAUSE.** -/
theorem executed_freezes_flow_or_break_under_pause {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {F : Flow} {ev : GateEvidence}
    {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg) {prof : Profile} {P₀ : Flags}
    {Y : PState} {tr : List Action} (hr : PRun h z0 hl cv fh S prof ⟨emptyManagers, P₀⟩ Y tr)
    (o : Obligation) (ho : o.flowId = F.flowId) :
    ¬ Refunded Y.mgrs o ∨ RefundBreak h z0 hl fh S F ev o (authCalls (checkedCalls tr)) :=
  executed_freezes_flow_or_break hS hex (pRun_reachLog hr) o ho

/-- **THE TREE-ATTACHED PAUSED RUN IS A SYSTEM RUN.** -/
theorem pSysSteps_sysSteps {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {prof : Profile} {X Y : PSysState} {log : List Obligation}
    {alog : List AuthCall} (hr : PSysSteps h z0 hl cv fh S prof X Y log alog) :
    Contracts.AppendPath.SysSteps h z0 hl cv fh S X.chains Y.chains log alog := by
  induction hr with
  | refl => exact Contracts.AppendPath.SysSteps.refl
  | append _ ha _ ih => exact Contracts.AppendPath.SysSteps.append ih ha
  | authorize a _ hv hg ih => exact Contracts.AppendPath.SysSteps.authorize a ih hv hg
  | claim _ hg _ ih => exact Contracts.AppendPath.SysSteps.claim ih hg
  | initL2 _ h0 ih => exact Contracts.AppendPath.SysSteps.initL2 ih h0
  | pause _ _ ih => exact ih
  | unpause _ _ ih => exact ih

/-- **WITH NOTHING PAUSED, NO SYSTEM RUN IS LOST.** -/
theorem sysSteps_pSysSteps {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} (prof : Profile) {X Y : Contracts.AppendPath.Chains}
    {log : List Obligation} {alog : List AuthCall}
    (hr : Contracts.AppendPath.SysSteps h z0 hl cv fh S X Y log alog) :
    PSysSteps h z0 hl cv fh S prof ⟨X, noFlags⟩ ⟨Y, noFlags⟩ log alog := by
  induction hr with
  | refl => exact PSysSteps.refl
  | append _ ha ih => exact PSysSteps.append ih ha (noFlags_open_send prof _ _)
  | authorize a _ hv hg ih => exact PSysSteps.authorize a ih hv hg
  | claim _ hg ih => exact PSysSteps.claim ih hg (noFlags_open_recover prof _ _)
  | initL2 _ h0 ih => exact PSysSteps.initL2 ih h0

/-- **NONE OR ALL, OR A LOCATED BREAK, UNDER PAUSE.** -/
theorem none_or_all_or_break_under_pause {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) (prof : Profile) (P : Flags) (F : Flow) (ev : GateEvidence) :
    FlowFinalizableBy h z0 hl cv S A F
      ∨ (∀ leg, ¬ ExecutedViaPausedBy h z0 hl cv fh S prof P F ev leg)
      ∨ GateBreak h z0 hl S F ev := by
  rcases none_or_all_or_break (fh := fh) hS hDA F ev with hfin | hnex | hb
  · exact Or.inl hfin
  · exact Or.inr (Or.inl fun leg hp => hnex leg hp.2)
  · exact Or.inr (Or.inr hb)

theorem none_or_all_or_break_pinned_under_pause {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {A : Access}
    (hDA : DataAvailable h z0 hl S A) (prof : Profile) (P : Flags) (F : Flow) (ev : GateEvidence) :
    FlowFinalizableBy h z0 hl cv S A F
      ∨ (∀ leg, ¬ ExecutedViaPausedBy h z0 hl cv fh S prof P F ev leg)
      ∨ PinnedGateBreak h z0 hl cv S A F ev := by
  rcases none_or_all_or_break_pinned (fh := fh) hS hDA F ev with hfin | hnex | hb
  · exact Or.inl hfin
  · exact Or.inr (Or.inl fun leg hp => hnex leg hp.2)
  · exact Or.inr (Or.inr hb)

/-- **EACH GATE READS ONLY ITS OWN FLAGS.** -/
theorem pause_gates_read_only_their_own_flags (prof : Profile) (P P' : Flags) (c : Chain)
    (b : UInt256) :
    ((prof.mintsViaVault b = true → P (prof.dest b) .vault = P' (prof.dest b) .vault) →
        (ExecOpen prof P b ↔ ExecOpen prof P' b))
    ∧ (prof.mintsViaVault b = false → ExecOpen prof P b)
    ∧ ((prof.recoversViaVault b = true → P c .vault = P' c .vault) →
        (RecoverOpen prof P c b ↔ RecoverOpen prof P' c b))
    ∧ ((∀ k, P c k = P' c k) → (SendOpen prof P c b ↔ SendOpen prof P' c b)) := by
  refine ⟨fun hagree => ?_, fun hnot hmint => absurd hmint (by rw [hnot]; decide),
    fun hagree => ?_, fun hagree => ?_⟩
  · constructor
    · intro hP hmint; rw [← hagree hmint]; exact hP hmint
    · intro hP hmint; rw [hagree hmint]; exact hP hmint
  · constructor
    · intro hP hrec; rw [← hagree hrec]; exact hP hrec
    · intro hP hrec; rw [hagree hrec]; exact hP hrec
  · unfold SendOpen
    rw [hagree .center, hagree .router, hagree .vault]

/-! ## 2. A paused destination leaves a committed flow stuck -/

/-- **A COMMITTED FLOW HAS NO VALID TIMEOUT EVIDENCE, OR A BREAK.** -/
theorem committed_not_refundable_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {F : Flow} (hcom : CommittedOnTime cv S F)
    {other : FlowLeg} (hother : other ∈ F.legs) (N : ℕ) (q : ImtProof) :
    ¬ LegRefundableBy h z0 hl cv S F other N q
      ∨ AbsenceBreak h z0 hl S F.deadline other.chain N q := by
  obtain ⟨n, hon, hmem⟩ := hcom other hother
  exact member_not_refundable_or_break hS hon hmem N q

/-- **A COMMITTED FLOW'S OBLIGATIONS ARE NEVER REFUNDED, OR A LOCATED BREAK.**  Over a
`ReachLog`: the logged call that marked a refunded obligation either clashes with `F`, or is
`F`'s own and its absence proof for a committed leg carries a break. -/
theorem committed_freezes_flow_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {F : Flow}
    (hcom : CommittedOnTime cv S F) (hchk : FlowIdChecked fh F) {Ms : Managers}
    {log : List AuthCall} (hr : ReachLog h z0 hl cv fh S emptyManagers Ms log)
    (o : Obligation) (ho : o.flowId = F.flowId) :
    ¬ Refunded Ms o ∨ CommittedRefundBreak h z0 hl fh S F o log := by
  by_cases hrf : Refunded Ms o
  · refine Or.inr ?_
    obtain ⟨a, ha, ⟨hchk', _, hmiss, href⟩, hobl⟩ := refund_logged hr o hrf
    have hid : F.flowId = a.flow.flowId := by
      rw [← ho, ← hobl]; rfl
    rcases flowId_check_pins_legList_or_collision hchk hchk' hid with heq | hcl
    · have hmiss' : a.missing ∈ F.legs := by rw [heq]; exact hmiss
      have href' : LegRefundableBy h z0 hl cv S F a.missing a.batch a.proof := by
        rw [heq]; exact href
      rcases committed_not_refundable_or_break hS hcom hmiss' a.batch a.proof with hn | hb
      · exact absurd href' hn
      · exact ⟨a, ha, hobl, Or.inr ⟨heq.symm, hb⟩⟩
    · exact ⟨a, ha, hobl, Or.inl hcl⟩
  · exact Or.inl hrf

/-- **HEADLINE 2: A PAUSED DESTINATION LEAVES A COMMITTED FLOW STUCK.** -/
theorem paused_destination_leaves_flow_stuck {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {F : Flow} {leg : FlowLeg}
    (hcom : CommittedOnTime cv S F) (hchk : FlowIdChecked fh F) {prof : Profile} {P₀ : Flags}
    {Y : PState} {tr : List Action} (hr : PRun h z0 hl cv fh S prof ⟨emptyManagers, P₀⟩ Y tr)
    (hmint : prof.mintsViaVault leg.bundleHash = true)
    (hpaused : Y.flags (prof.dest leg.bundleHash) .vault = true) :
    (∀ ev : GateEvidence, ¬ ExecutedViaPausedBy h z0 hl cv fh S prof Y.flags F ev leg)
    ∧ ∀ other ∈ F.legs,
        (¬ Refunded Y.mgrs (obligationOf F other)
          ∨ CommittedRefundBreak h z0 hl fh S F (obligationOf F other)
              (authCalls (checkedCalls tr)))
        ∧ ∀ (N : ℕ) (q : ImtProof),
            ¬ LegRefundableBy h z0 hl cv S F other N q
              ∨ AbsenceBreak h z0 hl S F.deadline other.chain N q := by
  refine ⟨fun ev hex => ?_, fun other hother =>
    ⟨committed_freezes_flow_or_break hS hcom hchk (pRun_reachLog hr) _ rfl,
      committed_not_refundable_or_break hS hcom hother⟩⟩
  have hopen := hex.1 hmint
  rw [hpaused] at hopen
  exact absurd hopen (by decide)

/-- **WHILE THE DESTINATION VAULT STAYS PAUSED, NOTHING MINTS THROUGH IT.** -/
theorem paused_destination_stays_paused {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} {prof : Profile} {X Y : PState}
    {tr : List Action} (hr : PRun h z0 hl cv fh S prof X Y tr) {d : Chain}
    (hX : X.flags d .vault = true) (hnu : Action.unpause d .vault ∉ tr) :
    Y.flags d .vault = true
      ∧ ∀ e, Action.execute e ∈ tr → prof.mintsViaVault e.leg.bundleHash = true →
          prof.dest e.leg.bundleHash ≠ d := by
  induction hr with
  | refl => exact ⟨hX, fun e he => absurd he List.not_mem_nil⟩
  | append _ _ _ ih =>
    obtain ⟨hY, hex⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨hY, fun e he => ?_⟩
    rcases List.mem_cons.mp he with he | he
    · cases he
    · exact hex e he
  | execute e' _ _ hopen ih =>
    obtain ⟨hY, hex⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨hY, fun e he hmint => ?_⟩
    rcases List.mem_cons.mp he with he | he
    · cases he
      intro hd
      have := hopen hmint
      rw [hd, hY] at this
      exact absurd this (by decide)
    · exact hex e he hmint
  | authorize _ _ _ _ ih =>
    obtain ⟨hY, hex⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨hY, fun e he => ?_⟩
    rcases List.mem_cons.mp he with he | he
    · cases he
    · exact hex e he
  | claim _ _ _ ih =>
    obtain ⟨hY, hex⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨hY, fun e he => ?_⟩
    rcases List.mem_cons.mp he with he | he
    · cases he
    · exact hex e he
  | @pause Y _ c k _ _ ih =>
    obtain ⟨hY, hex⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨?_, fun e he => ?_⟩
    · show Y.flags.set c k true d .vault = true
      by_cases hck : d = c ∧ Pausable.vault = k
      · simp only [Flags.set, ite_eq_left hck]
      · rw [Flags.set_other _ hck]; exact hY
    · rcases List.mem_cons.mp he with he | he
      · cases he
      · exact hex e he
  | @unpause Y _ c k _ _ ih =>
    obtain ⟨hY, hex⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    have hck : ¬ (d = c ∧ Pausable.vault = k) := by
      rintro ⟨rfl, rfl⟩
      exact hnu List.mem_cons_self
    refine ⟨?_, fun e he => ?_⟩
    · show Y.flags.set c k false d .vault = true
      rw [Flags.set_other _ hck]; exact hY
    · rcases List.mem_cons.mp he with he | he
      · cases he
      · exact hex e he

/-- **WHILE A SOURCE CENTER STAYS PAUSED, NOTHING IS SENT FROM ITS CHAIN.** -/
theorem paused_center_stays_paused {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} {prof : Profile} {X Y : PState}
    {tr : List Action} (hr : PRun h z0 hl cv fh S prof X Y tr) {c : Chain}
    (hX : X.flags c .center = true) (hnu : Action.unpause c .center ∉ tr) :
    Y.flags c .center = true ∧ ∀ c' f b, Action.append c' f b ∈ tr → c' ≠ c := by
  induction hr with
  | refl => exact ⟨hX, fun _ _ _ he => absurd he List.not_mem_nil⟩
  | @append Y _ c' f' b' _ _ hopen ih =>
    obtain ⟨hY, hap⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨hY, fun c'' f b he => ?_⟩
    rcases List.mem_cons.mp he with he | he
    · obtain ⟨rfl, rfl, rfl⟩ := Action.append.inj he
      intro hc
      have := hopen.1
      rw [hc, hY] at this
      exact absurd this (by decide)
    · exact hap c'' f b he
  | execute _ _ _ _ ih =>
    obtain ⟨hY, hap⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨hY, fun c'' f b he => ?_⟩
    rcases List.mem_cons.mp he with he | he
    · cases he
    · exact hap c'' f b he
  | authorize _ _ _ _ ih =>
    obtain ⟨hY, hap⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨hY, fun c'' f b he => ?_⟩
    rcases List.mem_cons.mp he with he | he
    · cases he
    · exact hap c'' f b he
  | claim _ _ _ ih =>
    obtain ⟨hY, hap⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨hY, fun c'' f b he => ?_⟩
    rcases List.mem_cons.mp he with he | he
    · cases he
    · exact hap c'' f b he
  | @pause Y _ c' k _ _ ih =>
    obtain ⟨hY, hap⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨?_, fun c'' f b he => ?_⟩
    · show Y.flags.set c' k true c .center = true
      by_cases hck : c = c' ∧ Pausable.center = k
      · simp only [Flags.set, ite_eq_left hck]
      · rw [Flags.set_other _ hck]; exact hY
    · rcases List.mem_cons.mp he with he | he
      · cases he
      · exact hap c'' f b he
  | @unpause Y _ c' k _ _ ih =>
    obtain ⟨hY, hap⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    have hck : ¬ (c = c' ∧ Pausable.center = k) := by
      rintro ⟨rfl, rfl⟩
      exact hnu List.mem_cons_self
    refine ⟨?_, fun c'' f b he => ?_⟩
    · show Y.flags.set c' k false c .center = true
      rw [Flags.set_other _ hck]; exact hY
    · rcases List.mem_cons.mp he with he | he
      · cases he
      · exact hap c'' f b he

/-- **A DESTINATION PAUSE THAT IS NEVER LIFTED STRANDS THE LEG FOR AS LONG AS IT LASTS.** -/
theorem permanent_destination_pause_strands_leg {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {F : Flow} {leg : FlowLeg}
    (hcom : CommittedOnTime cv S F) (hchk : FlowIdChecked fh F) {prof : Profile} {P₀ : Flags}
    {X : PState} {tr₀ : List Action} (hr₀ : PRun h z0 hl cv fh S prof ⟨emptyManagers, P₀⟩ X tr₀)
    (hmint : prof.mintsViaVault leg.bundleHash = true)
    (hX : X.flags (prof.dest leg.bundleHash) .vault = true) {Y : PState} {tr : List Action}
    (hr : PRun h z0 hl cv fh S prof X Y tr)
    (hnu : Action.unpause (prof.dest leg.bundleHash) .vault ∉ tr) :
    (∀ e, Action.execute e ∈ tr → e.leg.bundleHash ≠ leg.bundleHash)
    ∧ ∀ other ∈ F.legs,
        ¬ Refunded Y.mgrs (obligationOf F other)
          ∨ CommittedRefundBreak h z0 hl fh S F (obligationOf F other)
              (authCalls (checkedCalls (tr ++ tr₀))) := by
  obtain ⟨_, hex⟩ := paused_destination_stays_paused hr hX hnu
  refine ⟨fun e he hb => ?_, fun other _ =>
    committed_freezes_flow_or_break hS hcom hchk (pRun_reachLog (PRun.trans hr₀ hr)) _ rfl⟩
  have hm : prof.mintsViaVault e.leg.bundleHash = true := by rw [hb]; exact hmint
  exact hex e he hm (by rw [hb])

/-! ## 3. Unpausing restores enabledness -/

/-- **AFTER UNPAUSE, THE GATE IS THE UNPAUSED GATE.** -/
theorem unpaused_gate_is_the_gate {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} (prof : Profile) (P : Flags) (F : Flow) (ev : GateEvidence)
    (leg : FlowLeg) :
    ExecutedViaPausedBy h z0 hl cv fh S prof (P.set (prof.dest leg.bundleHash) .vault false) F ev leg
      ↔ ExecutedViaBy h z0 hl cv fh S F ev leg :=
  ⟨fun hp => hp.2, fun hex => ⟨fun _ => Flags.set_same _ _ _ _, hex⟩⟩

/-- Presentable gate evidence for a finalizable flow: for every leg, a batch and a proof a prover
can present, on which the deployed gate passes. -/
theorem finalizable_evidence {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} {A : Access} {F : Flow} (hfin : FlowFinalizableBy h z0 hl cv S A F) :
    ∃ ev : GateEvidence, (∀ l ∈ F.legs, A l.chain (ev l).1 (ev l).2)
      ∧ FlowFinalizedBy h z0 hl cv S F ev := by
  classical
  let ev : GateEvidence := fun l =>
    if hl' : l ∈ F.legs then
      (Classical.choose (hfin l hl'), Classical.choose (Classical.choose_spec (hfin l hl')))
    else (0, ⟨⟨0, 0, 0⟩, 0, fun _ => 0, 0⟩)
  have hspec : ∀ l (hl' : l ∈ F.legs), ev l =
      (Classical.choose (hfin l hl'), Classical.choose (Classical.choose_spec (hfin l hl'))) :=
    fun l hl' => dite_eq_left hl'
  refine ⟨ev, fun l hl' => ?_, fun l hl' => ?_⟩
  · rw [hspec l hl']
    exact (Classical.choose_spec (Classical.choose_spec (hfin l hl'))).2.1
  · rw [hspec l hl']
    obtain ⟨hon, _, hacc⟩ := Classical.choose_spec (Classical.choose_spec (hfin l hl'))
    exact ⟨hon, hacc⟩

/-- A committed flow is finalizable, given data availability. -/
theorem committed_finalizable {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {S : System} (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A) {F : Flow}
    (hcom : CommittedOnTime cv S F) : FlowFinalizableBy h z0 hl cv S A F := by
  intro l hl'
  obtain ⟨n, hon, hmem⟩ := hcom l hl'
  exact member_is_finalizable hS hDA hon hmem

/-- **HEADLINE 3: UNPAUSING RESTORES EXECUTION, AT ANY TIME.** -/
theorem unpause_restores_execution {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} (hS : Wf S) {A : Access} (hDA : DataAvailable h z0 hl S A)
    {F : Flow} {leg : FlowLeg} (hcom : CommittedOnTime cv S F) (hchk : FlowIdChecked fh F)
    (hleg : leg ∈ F.legs) {prof : Profile} {X Y : PState} {tr : List Action}
    (hr : PRun h z0 hl cv fh S prof X Y tr) :
    ∃ (ev : GateEvidence) (Z : PState) (tr' : List Action),
      (∀ l ∈ F.legs, A l.chain (ev l).1 (ev l).2)
      ∧ (∀ a ∈ tr', a = Action.unpause (prof.dest leg.bundleHash) .vault)
      ∧ PRun h z0 hl cv fh S prof X Z (Action.execute ⟨F, ev, leg⟩ :: (tr' ++ tr))
      ∧ Z.mgrs = Y.mgrs ∧ Z.flags (prof.dest leg.bundleHash) .vault = false
      ∧ ∀ c k, ¬ (c = prof.dest leg.bundleHash ∧ k = .vault) → Z.flags c k = Y.flags c k := by
  obtain ⟨ev, hpres, hfin⟩ := finalizable_evidence (committed_finalizable hS hDA hcom)
  have hver : ExecCall.Verified h z0 hl cv fh S ⟨F, ev, leg⟩ := ⟨hleg, hchk, hfin⟩
  set d := prof.dest leg.bundleHash with hd
  by_cases hflag : Y.flags d .vault = true
  · refine ⟨ev, Y.setFlag d .vault false, [Action.unpause d .vault], hpres,
      fun a ha => List.mem_singleton.mp ha, ?_, rfl, Flags.set_same _ _ _ _,
      fun c k hck => Flags.set_other _ (by
        rintro ⟨rfl, rfl⟩; exact hck ⟨rfl, rfl⟩)⟩
    exact PRun.execute ⟨F, ev, leg⟩ (PRun.unpause hr hflag) hver
      (fun _ => Flags.set_same _ _ _ _)
  · have hfalse : Y.flags d .vault = false := by simpa using hflag
    exact ⟨ev, Y, [], hpres, fun a ha => absurd ha List.not_mem_nil,
      PRun.execute ⟨F, ev, leg⟩ hr hver (fun _ => hfalse), rfl, hfalse, fun _ _ _ => rfl⟩

/-! ## 4. A paused source vault blocks the claim, and the claim can be retried -/

/-- A step on another leg does not change this leg's state. -/
theorem stateOf_setLeg_other {Y : PState} {c c' : Chain} {f b f' b' : UInt256} {s : LegState}
    (hne : (⟨f, b, c⟩ : Obligation) ≠ ⟨f', b', c'⟩) :
    stateOf (Y.setLeg c' f' b' s).mgrs ⟨f, b, c⟩ = stateOf Y.mgrs ⟨f, b, c⟩ :=
  stateOf_setAt_other hne

theorem stateOf_setLeg_self (Y : PState) (c : Chain) (f b : UInt256) (s : LegState) :
    stateOf (Y.setLeg c f b s).mgrs ⟨f, b, c⟩ = s :=
  stateOf_setAt_self Y.mgrs c f b s

/-- **HEADLINE 4a: WHILE THE SOURCE VAULT STAYS PAUSED, A REVERTABLE LEG STAYS REVERTABLE.** -/
theorem paused_vault_keeps_leg_revertable {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} {prof : Profile} {X Y : PState}
    {tr : List Action} (hr : PRun h z0 hl cv fh S prof X Y tr) {c : Chain} {f b : UInt256}
    (hrec : prof.recoversViaVault b = true) (hX : X.flags c .vault = true)
    (hnu : Action.unpause c .vault ∉ tr) (hst : stateOf X.mgrs ⟨f, b, c⟩ = .Revertable) :
    stateOf Y.mgrs ⟨f, b, c⟩ = .Revertable ∧ Y.flags c .vault = true
      ∧ Action.claim c f b ∉ tr := by
  induction hr with
  | refl => exact ⟨hst, hX, List.not_mem_nil⟩
  | @append Y _ c' f' b' _ hg _ ih =>
    obtain ⟨hYs, hYf, hnc⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    have hne : (⟨f, b, c⟩ : Obligation) ≠ ⟨f', b', c'⟩ := by
      intro heq
      have hg' : stateOf Y.mgrs ⟨f', b', c'⟩ = .Unset := hg
      rw [← heq, hYs] at hg'
      exact absurd hg' (by decide)
    refine ⟨by rw [stateOf_setLeg_other hne]; exact hYs, hYf, ?_⟩
    rintro (_ | ⟨_, hm⟩)
    exact hnc hm
  | execute _ _ _ _ ih =>
    obtain ⟨hYs, hYf, hnc⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨hYs, hYf, ?_⟩
    rintro (_ | ⟨_, hm⟩)
    exact hnc hm
  | @authorize Y _ a _ _ hg ih =>
    obtain ⟨hYs, hYf, hnc⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    have hne : (⟨f, b, c⟩ : Obligation) ≠ ⟨a.flow.flowId, a.leg.bundleHash, a.leg.chain⟩ := by
      intro heq
      have hg' : stateOf Y.mgrs ⟨a.flow.flowId, a.leg.bundleHash, a.leg.chain⟩ = .Committed := hg
      rw [← heq, hYs] at hg'
      exact absurd hg' (by decide)
    refine ⟨by rw [stateOf_setLeg_other hne]; exact hYs, hYf, ?_⟩
    rintro (_ | ⟨_, hm⟩)
    exact hnc hm
  | @claim Y _ c' f' b' _ _ hopen ih =>
    obtain ⟨hYs, hYf, hnc⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    have hne : (⟨f, b, c⟩ : Obligation) ≠ ⟨f', b', c'⟩ := by
      intro heq
      obtain ⟨rfl, rfl, rfl⟩ : f = f' ∧ b = b' ∧ c = c' := by
        simpa using heq
      have := hopen hrec
      rw [hYf] at this
      exact absurd this (by decide)
    refine ⟨by rw [stateOf_setLeg_other hne]; exact hYs, hYf, ?_⟩
    intro hm
    rcases List.mem_cons.mp hm with hm | hm
    · obtain ⟨rfl, rfl, rfl⟩ := Action.claim.inj hm
      exact hne rfl
    · exact hnc hm
  | @pause Y _ c' k _ _ ih =>
    obtain ⟨hYs, hYf, hnc⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    refine ⟨hYs, ?_, ?_⟩
    · show Y.flags.set c' k true c .vault = true
      by_cases hck : c = c' ∧ Pausable.vault = k
      · simp only [Flags.set, ite_eq_left hck]
      · rw [Flags.set_other _ hck]; exact hYf
    · rintro (_ | ⟨_, hm⟩)
      exact hnc hm
  | @unpause Y _ c' k _ _ ih =>
    obtain ⟨hYs, hYf, hnc⟩ := ih (fun hm => hnu (List.mem_cons_of_mem _ hm))
    have hck : ¬ (c = c' ∧ Pausable.vault = k) := by
      rintro ⟨rfl, rfl⟩
      exact hnu List.mem_cons_self
    refine ⟨hYs, ?_, ?_⟩
    · show Y.flags.set c' k false c .vault = true
      rw [Flags.set_other _ hck]; exact hYf
    · rintro (_ | ⟨_, hm⟩)
      exact hnc hm

/-- **HEADLINE 4b: UNPAUSING RE-ENABLES THE CLAIM.** -/
theorem unpause_reenables_claim {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {prof : Profile} {X Y : PState} {tr : List Action}
    (hr : PRun h z0 hl cv fh S prof X Y tr) {c : Chain} {f b : UInt256}
    (hst : stateOf Y.mgrs ⟨f, b, c⟩ = .Revertable) :
    ∃ (Z : PState) (tr' : List Action),
      (∀ a ∈ tr', a = Action.unpause c .vault)
      ∧ PRun h z0 hl cv fh S prof X Z (Action.claim c f b :: (tr' ++ tr))
      ∧ stateOf Z.mgrs ⟨f, b, c⟩ = .Reverted ∧ Z.flags c .vault = false
      ∧ ∀ c' k, ¬ (c' = c ∧ k = .vault) → Z.flags c' k = Y.flags c' k := by
  by_cases hflag : Y.flags c .vault = true
  · refine ⟨(Y.setFlag c .vault false).setLeg c f b .Reverted, [Action.unpause c .vault],
      fun a ha => List.mem_singleton.mp ha, ?_, stateOf_setLeg_self _ _ _ _ _,
      Flags.set_same _ _ _ _, fun c' k hck => Flags.set_other _ (by
        rintro ⟨rfl, rfl⟩; exact hck ⟨rfl, rfl⟩)⟩
    exact PRun.claim (PRun.unpause hr hflag) hst (fun _ => Flags.set_same _ _ _ _)
  · have hfalse : Y.flags c .vault = false := by simpa using hflag
    exact ⟨Y.setLeg c f b .Reverted, [], fun a ha => absurd ha List.not_mem_nil,
      PRun.claim hr hst (fun _ => hfalse), stateOf_setLeg_self _ _ _ _ _, hfalse,
      fun _ _ _ => rfl⟩

end Contracts.InteropPause

/-! ## Witnesses

One run in `mixedSystem 1` under the commit value `fun _ _ => 1`, the flow hash
`lengthFlowHash` and the profile `vaultProfile` (every destination is chain `7`):

1. `append 1 1 2`: the obligation `⟨1, 2, 1⟩` of `mixedFlow 1 1 2`'s silent leg;
2. `authorize (twoFlowCall ..)`: its timeout, on the honest absence proof of chain `1`;
3. `pause 7 vault`, then `pause 1 vault`: the state `pauseStuckState`;
4. `unpause 7 vault`, then `execute` the one leg `⟨0, 1⟩` of the committed flow `subsetFlow 0 1`;
5. `unpause 1 vault`, then `claim 1 1 2`. -/

namespace Contracts.InteropPause

open MerkleSpec MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree
open Contracts.Atomicity Contracts.Timeout Contracts.Refund Contracts.FlowBinding
open Contracts.AtomicFlowManager

/-- The committed flow's gate evidence: the honest proof of leaf `1` of chain `0`'s batch `0`. -/
def pauseCommittedEv (h : Hash) (z0 : UInt256) (hl : LeafHash) : GateEvidence :=
  fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1)

/-- The execution of the committed flow's one leg. -/
def pauseCommittedExec (h : Hash) (z0 : UInt256) (hl : LeafHash) : ExecCall :=
  ⟨subsetFlow 0 1, pauseCommittedEv h z0 hl, ⟨0, 1⟩⟩

/-- The state after both pauses: `⟨1, 2, 1⟩` is `Revertable`, and the vaults of chains `7` and
`1` are paused. -/
def pauseStuckState : PState := ⟨twoFlowMs, (noFlags.set 7 .vault true).set 1 .vault true⟩

/-- The trace up to `pauseStuckState`, most recent first. -/
def pauseStuckTrace (h : Hash) (z0 : UInt256) (hl : LeafHash) : List Action :=
  [.pause 1 .vault, .pause 7 .vault, .authorize (twoFlowCall h z0 hl), .append 1 1 2]

/-- The state after unpausing chain `7`'s vault (and executing, which writes nothing). -/
def pauseResumedState : PState := pauseStuckState.setFlag 7 .vault false

/-- The final state: chain `1`'s vault unpaused too, and `⟨1, 2, 1⟩` claimed. -/
def pauseFinalState : PState := (pauseResumedState.setFlag 1 .vault false).setLeg 1 1 2 .Reverted

theorem twoFlowCall_verified (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    (twoFlowCall h z0 hl).Verified h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  have hmem : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs := by simp [mixedFlow]
  have href : LegRefundableBy h z0 hl (fun _ _ => 1) (mixedSystem 1) (mixedFlow 1 1 2) ⟨1, 2⟩ 1
      ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩ := by
    refine Or.inl ⟨by norm_num [mixedFlow], ?_⟩
    show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
      (beginHeight (mixedSystem 1) 1 1) 1 _
    rw [hbegin, hbeginH]
    exact setup_absence_accepted h z0 hl h1
  exact ⟨lengthFlowHash_checks_mixed, hmem, hmem, href⟩

theorem pauseCommittedExec_verified (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    (pauseCommittedExec h z0 hl).Verified h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) :=
  (subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset).1

theorem pauseCommittedEv_no_break (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ¬ InclusionBreak h z0 hl (mixedSystem 1) 0 0 (honestProof h z0 hl (mixedSystem 1) 0 0 1) :=
  (subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset).2

theorem pause_committed :
    CommittedOnTime (fun _ _ => 1) (mixedSystem 1) (subsetFlow 0 1) := by
  intro l hl'
  obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
  refine ⟨0, by simp [subsetFlow], ?_⟩
  show (1 : UInt256) ∈ keys (toAbs ((mixedSystem 1).tree 0 0))
  rw [mixedSystem_tree_zero]
  exact mem_insertSetup (by decide)

theorem pause_stuck_run (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    PRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) vaultProfile
      ⟨emptyManagers, noFlags⟩ pauseStuckState (pauseStuckTrace h z0 hl) := by
  have r1 : PRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) vaultProfile
      ⟨emptyManagers, noFlags⟩ ⟨twoFlowM1, noFlags⟩ [.append 1 1 2] :=
    PRun.append (c := 1) (f := 1) (b := 2) PRun.refl rfl (noFlags_open_send _ _ _)
  have hguard : AuthorizeGuard (twoFlowM1 1) 1 2 := by
    show (twoFlowM1 1).legState 1 2 = .Committed
    simp [twoFlowM1, setAt, Manager.set]
  have r2 : PRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) vaultProfile
      ⟨emptyManagers, noFlags⟩ ⟨twoFlowMs, noFlags⟩
      [.authorize (twoFlowCall h z0 hl), .append 1 1 2] :=
    PRun.authorize (twoFlowCall h z0 hl) r1 (twoFlowCall_verified h z0 hl) hguard
  have r3 := PRun.pause (c := 7) (k := .vault) r2 rfl
  exact PRun.pause (c := 1) (k := .vault) r3 (by decide)

theorem pauseStuckState_flag_seven : pauseStuckState.flags 7 .vault = true := by decide

theorem pauseStuckState_flag_one : pauseStuckState.flags 1 .vault = true := by decide

theorem pause_resume_execute (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    PRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) vaultProfile pauseStuckState
      pauseResumedState [.execute (pauseCommittedExec h z0 hl), .unpause 7 .vault] :=
  PRun.execute (pauseCommittedExec h z0 hl)
    (PRun.unpause (c := 7) (k := .vault) PRun.refl pauseStuckState_flag_seven)
    (pauseCommittedExec_verified h z0 hl)
    (fun _ => Flags.set_same pauseStuckState.flags 7 .vault false)

theorem pause_full_run (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    PRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) vaultProfile
      ⟨emptyManagers, noFlags⟩ pauseFinalState
      (.claim 1 1 2 :: .unpause 1 .vault :: ([.execute (pauseCommittedExec h z0 hl),
        .unpause 7 .vault] ++ pauseStuckTrace h z0 hl)) := by
  have r6 := PRun.trans (pause_stuck_run h z0 hl) (pause_resume_execute h z0 hl)
  have hflag : pauseResumedState.flags 1 .vault = true := by decide
  have r7 := PRun.unpause (c := 1) (k := .vault) r6 hflag
  have hguard : ClaimGuard ((pauseResumedState.setFlag 1 .vault false).mgrs 1) 1 2 := by
    show (twoFlowMs 1).legState 1 2 = .Revertable
    simp [twoFlowMs, setAt, Manager.set]
  exact PRun.claim (c := 1) (f := 1) (b := 2) r7 hguard
    (fun _ => Flags.set_same pauseResumedState.flags 1 .vault false)

theorem pause_stuck_revertable : stateOf pauseStuckState.mgrs ⟨1, 2, 1⟩ = .Revertable :=
  stateOf_setAt_self twoFlowM1 1 1 2 .Revertable

/-- The committed flow's obligation `⟨0, 1, 0⟩` is never touched by the run. -/
theorem pause_committed_obligation_unset :
    stateOf pauseFinalState.mgrs ⟨0, 1, 0⟩ = .Unset := by
  have hne : (⟨0, 1, 0⟩ : Obligation) ≠ ⟨1, 2, 1⟩ := by decide
  show stateOf (setAt twoFlowMs 1 ((twoFlowMs 1).set 1 2 .Reverted)) ⟨0, 1, 0⟩ = .Unset
  rw [stateOf_setAt_other hne]
  show stateOf (setAt twoFlowM1 1 ((twoFlowM1 1).set 1 2 .Revertable)) ⟨0, 1, 0⟩ = .Unset
  rw [stateOf_setAt_other hne]
  show stateOf (setAt emptyManagers 1 ((emptyManagers 1).set 1 2 .Committed)) ⟨0, 1, 0⟩ = .Unset
  rw [stateOf_setAt_other hne, stateOf_emptyManagers]

/-- The logged authorization is of a different flow id than the committed flow, so it carries
no break of either kind against it. -/
theorem twoFlowCall_obligation_ne (h : Hash) (z0 : UInt256) (hl : LeafHash) (leg : FlowLeg) :
    obligationOf (twoFlowCall h z0 hl).flow (twoFlowCall h z0 hl).leg
      ≠ obligationOf (subsetFlow 0 1) leg := by
  intro he
  have hid : (1 : UInt256) = 0 := congrArg Obligation.flowId he
  exact absurd hid (by decide)

theorem pause_auth_log (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    authCalls (checkedCalls (pauseStuckTrace h z0 hl)) = [twoFlowCall h z0 hl] := rfl

theorem pause_full_auth_log (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    authCalls (checkedCalls (.claim 1 1 2 :: .unpause 1 .vault ::
      ([.execute (pauseCommittedExec h z0 hl), .unpause 7 .vault] ++ pauseStuckTrace h z0 hl)))
      = [twoFlowCall h z0 hl] := rfl

theorem pause_run_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (prof : Profile)
      (Y : PState) (tr : List Action) (F : Flow) (ev : GateEvidence) (leg : FlowLeg)
      (o : Obligation),
      Wf S ∧ DataAvailable h z0 hl S A
        ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩ Y tr
        ∧ (∃ c k, Action.pause c k ∈ tr) ∧ (∃ c k, Action.unpause c k ∈ tr)
        ∧ Action.execute ⟨F, ev, leg⟩ ∈ tr ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ authCalls (checkedCalls tr) ≠ []
        ∧ FlowFinalizableBy h z0 hl cv S A F ∧ ¬ GateBreak h z0 hl S F ev
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) (authCalls (checkedCalls tr))
        ∧ ¬ Refunded Y.mgrs (obligationOf F leg)
        ∧ stateOf Y.mgrs o = .Reverted := by
  have hS : Wf (mixedSystem 1) := mixedSystem_wf (by decide)
  have hDA := honestAccess_dataAvailable h z0 hl (mixedSystem 1)
  refine ⟨fun _ _ => 1, lengthFlowHash, mixedSystem 1, honestAccess h z0 hl (mixedSystem 1),
    vaultProfile, pauseFinalState, _, subsetFlow 0 1, pauseCommittedEv h z0 hl, ⟨0, 1⟩,
    ⟨1, 2, 1⟩, hS, hDA, pause_full_run h z0 hl, ⟨7, .vault, by simp [pauseStuckTrace]⟩,
    ⟨7, .vault, by simp⟩,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ List.mem_cons_self)),
    pauseCommittedExec_verified h z0 hl, ?_, committed_finalizable hS hDA pause_committed,
    ?_, ?_, ?_, ?_⟩
  · rw [pause_full_auth_log]; exact List.cons_ne_nil _ _
  · rintro ⟨l, hl', hb⟩
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    exact pauseCommittedEv_no_break h z0 hl hb
  · rw [pause_full_auth_log]
    intro hb
    cases hb with
    | flowIdClash a ha hobl _ =>
      rw [List.mem_singleton] at ha; subst ha; exact twoFlowCall_obligation_ne h z0 hl _ hobl
    | inclusion a ha hobl _ _ =>
      rw [List.mem_singleton] at ha; subst ha; exact twoFlowCall_obligation_ne h z0 hl _ hobl
    | absence a ha hobl _ _ =>
      rw [List.mem_singleton] at ha; subst ha; exact twoFlowCall_obligation_ne h z0 hl _ hobl
  · show ¬ 2 ≤ rank (stateOf pauseFinalState.mgrs ⟨0, 1, 0⟩)
    rw [pause_committed_obligation_unset]
    simp [rank]
  · exact stateOf_setAt_self _ 1 1 2 .Reverted

/-- The honest proof of the committed leaf, as timeout evidence at batch `0`: no break, and it
does not pass the timeout gate. -/
theorem pause_honest_timeout_rejected (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ¬ AbsenceBreak h z0 hl (mixedSystem 1) (subsetFlow 0 1).deadline (0 : Chain) 0
        (honestProof h z0 hl (mixedSystem 1) 0 0 1)
      ∧ ¬ LegRefundableBy h z0 hl (fun _ _ => 1) (mixedSystem 1) (subsetFlow 0 1) ⟨0, 1⟩ 0
          (honestProof h z0 hl (mixedSystem 1) 0 0 1) := by
  have hS : Wf (mixedSystem 1) := mixedSystem_wf (by decide)
  have hnab : ¬ AbsenceBreak h z0 hl (mixedSystem 1) (subsetFlow 0 1).deadline (0 : Chain) 0
      (honestProof h z0 hl (mixedSystem 1) 0 0 1) := by
    rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
    · exact absurd hlate (by simp [subsetFlow])
    · exact pauseCommittedEv_no_break h z0 hl hb
  refine ⟨hnab, ?_⟩
  rcases committed_not_refundable_or_break (h := h) (z0 := z0) (hl := hl) hS pause_committed
      (List.mem_singleton_self _) 0 (honestProof h z0 hl (mixedSystem 1) 0 0 1) with hn | hb
  · exact hn
  · exact absurd hb hnab

theorem paused_destination_stuck_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (prof : Profile)
      (Y : PState) (tr : List Action) (F : Flow) (leg : FlowLeg) (ev : GateEvidence)
      (N : ℕ) (q : ImtProof),
      Wf S ∧ DataAvailable h z0 hl S A ∧ CommittedOnTime cv S F ∧ FlowIdChecked fh F
        ∧ leg ∈ F.legs ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩ Y tr
        ∧ prof.mintsViaVault leg.bundleHash = true
        ∧ Y.flags (prof.dest leg.bundleHash) .vault = true
        ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ (∀ l ∈ F.legs, A l.chain (ev l).1 (ev l).2)
        ∧ authCalls (checkedCalls tr) ≠ []
        ∧ (∀ other ∈ F.legs, ¬ CommittedRefundBreak h z0 hl fh S F (obligationOf F other)
            (authCalls (checkedCalls tr)))
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N q
        ∧ ¬ LegRefundableBy h z0 hl cv S F leg N q
        ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩
            (Y.setFlag (prof.dest leg.bundleHash) .vault false)
            (Action.execute ⟨F, ev, leg⟩ :: Action.unpause (prof.dest leg.bundleHash) .vault
              :: tr) := by
  have hS : Wf (mixedSystem 1) := mixedSystem_wf (by decide)
  have hcount : ((mixedSystem 1).tree 0 0).leafCount = 2 := by
    rw [mixedSystem_tree_zero]; rfl
  obtain ⟨hnab, hnr⟩ := pause_honest_timeout_rejected h z0 hl
  refine ⟨fun _ _ => 1, lengthFlowHash, mixedSystem 1, honestAccess h z0 hl (mixedSystem 1),
    vaultProfile, pauseStuckState, pauseStuckTrace h z0 hl, subsetFlow 0 1, ⟨0, 1⟩,
    pauseCommittedEv h z0 hl, 0, honestProof h z0 hl (mixedSystem 1) 0 0 1, hS,
    honestAccess_dataAvailable h z0 hl _, pause_committed, lengthFlowHash_checks_subset,
    List.mem_singleton_self _, pause_stuck_run h z0 hl, rfl, pauseStuckState_flag_seven,
    pauseCommittedExec_verified h z0 hl, ?_, ?_, ?_, hnab, hnr,
    PRun.trans (pause_stuck_run h z0 hl) (pause_resume_execute h z0 hl)⟩
  · intro l hl'
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    exact ⟨1, show 1 < ((mixedSystem 1).tree 0 0).leafCount by rw [hcount]; norm_num, rfl⟩
  · rw [pause_auth_log]; exact List.cons_ne_nil _ _
  · intro other _ ⟨a, ha, hobl, _⟩
    rw [pause_auth_log, List.mem_singleton] at ha
    subst ha
    exact twoFlowCall_obligation_ne h z0 hl _ hobl

theorem paused_vault_claim_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (prof : Profile)
      (X Y : PState) (tr tr₁ : List Action) (c : Chain) (f b : UInt256),
      PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩ X tr
        ∧ prof.recoversViaVault b = true ∧ X.flags c .vault = true
        ∧ stateOf X.mgrs ⟨f, b, c⟩ = .Revertable
        ∧ PRun h z0 hl cv fh S prof X Y tr₁ ∧ Action.unpause c .vault ∉ tr₁
        ∧ (∃ e, Action.execute e ∈ tr₁) ∧ stateOf Y.mgrs ⟨f, b, c⟩ = .Revertable
        ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩
            ((Y.setFlag c .vault false).setLeg c f b .Reverted)
            (Action.claim c f b :: Action.unpause c .vault :: (tr₁ ++ tr))
        ∧ stateOf ((Y.setFlag c .vault false).setLeg c f b .Reverted).mgrs ⟨f, b, c⟩
            = .Reverted := by
  refine ⟨fun _ _ => 1, lengthFlowHash, mixedSystem 1, vaultProfile, pauseStuckState,
    pauseResumedState, pauseStuckTrace h z0 hl, [.execute (pauseCommittedExec h z0 hl),
      .unpause 7 .vault], 1, 1, 2, pause_stuck_run h z0 hl, rfl, pauseStuckState_flag_one,
    pause_stuck_revertable, pause_resume_execute h z0 hl, ?_,
    ⟨_, List.mem_cons_self⟩, pause_stuck_revertable, pause_full_run h z0 hl,
    stateOf_setLeg_self _ _ _ _ _⟩
  simp

/-- The two-leg witness's profile: bundle `2` goes to chain `6`, every other bundle to chain `5`,
and every bundle goes through the router and the vault. -/
def splitProfile : Profile where
  dest := fun b => if b = 2 then 6 else 5
  sendsViaRouter := fun _ => true
  burnsViaVault := fun _ => true
  mintsViaVault := fun _ => true
  recoversViaVault := fun _ => true

theorem pair_committed :
    CommittedOnTime (fun _ b => b) (pairSystem 1 2) (mixedFlow 1 1 2) := by
  intro l hl'
  refine ⟨0, by simp [mixedFlow], ?_⟩
  rcases List.mem_cons.mp hl' with rfl | hl'
  · show (1 : UInt256) ∈ keys (toAbs ((pairSystem 1 2).tree 0 0))
    rw [pairSystem_tree_zero]
    exact mem_insertSetup (by decide)
  · obtain rfl := List.mem_singleton.mp hl'
    show (2 : UInt256) ∈ keys (toAbs ((pairSystem 1 2).tree 1 0))
    rw [pairSystem_tree_one]
    exact mem_insertSetup (by decide)

theorem destination_pause_strands_sibling_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (prof : Profile) (F : Flow)
      (legA legB : FlowLeg) (evA evB : GateEvidence) (X Y : PState) (tr₀ tr : List Action),
      Wf S ∧ CommittedOnTime cv S F ∧ FlowIdChecked fh F ∧ legA ∈ F.legs ∧ legB ∈ F.legs
        ∧ legA ≠ legB
        ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩ X tr₀
        ∧ prof.mintsViaVault legB.bundleHash = true
        ∧ X.flags (prof.dest legB.bundleHash) .vault = true
        ∧ PRun h z0 hl cv fh S prof X Y tr
        ∧ Action.unpause (prof.dest legB.bundleHash) .vault ∉ tr
        ∧ Action.execute ⟨F, evA, legA⟩ ∈ tr
        ∧ (∀ other ∈ F.legs, ¬ Refunded Y.mgrs (obligationOf F other))
        ∧ PRun h z0 hl cv fh S prof ⟨emptyManagers, noFlags⟩
            (Y.setFlag (prof.dest legB.bundleHash) .vault false)
            (Action.execute ⟨F, evB, legB⟩ :: Action.unpause (prof.dest legB.bundleHash) .vault
              :: (tr ++ tr₀)) := by
  have hA : (⟨0, 1⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs := List.mem_cons_self
  have hB : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs :=
    List.mem_cons_of_mem _ (List.mem_singleton_self _)
  let X : PState := (⟨emptyManagers, noFlags⟩ : PState).setFlag 6 .vault true
  have hr₀ : PRun h z0 hl (fun _ b => b) lengthFlowHash (pairSystem 1 2) splitProfile
      ⟨emptyManagers, noFlags⟩ X [.pause 6 .vault] :=
    PRun.pause (c := 6) (k := .vault) PRun.refl rfl
  have hX6 : X.flags 6 .vault = true := Flags.set_same noFlags 6 .vault true
  have hX5 : X.flags 5 .vault = false := by decide
  have hr : PRun h z0 hl (fun _ b => b) lengthFlowHash (pairSystem 1 2) splitProfile X X
      [.execute (pairExec h z0 hl ⟨0, 1⟩)] :=
    PRun.execute (pairExec h z0 hl ⟨0, 1⟩) PRun.refl (pairExec_verified h z0 hl hA)
      (fun _ => hX5)
  have hfinal := PRun.execute (pairExec h z0 hl ⟨1, 2⟩)
    (PRun.unpause (c := 6) (k := .vault) (PRun.trans hr₀ hr) hX6)
    (pairExec_verified h z0 hl hB) (fun _ => Flags.set_same X.flags 6 .vault false)
  refine ⟨fun _ b => b, lengthFlowHash, pairSystem 1 2, splitProfile, mixedFlow 1 1 2, ⟨0, 1⟩,
    ⟨1, 2⟩, pairEvidence h z0 hl, pairEvidence h z0 hl, X, X, [.pause 6 .vault],
    [.execute (pairExec h z0 hl ⟨0, 1⟩)], pairSystem_wf (by decide) (by decide), pair_committed,
    lengthFlowHash_checks_mixed, hA, hB, by decide, hr₀, rfl, hX6, hr, by simp,
    List.mem_cons_self, ?_, hfinal⟩
  intro other _
  show ¬ 2 ≤ rank (stateOf emptyManagers _)
  rw [stateOf_emptyManagers]
  simp [rank]

theorem paused_center_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (prof : Profile) (X Y : PState)
      (tr : List Action) (c c' : Chain) (f b : UInt256),
      PRun h z0 hl cv fh S prof X Y tr ∧ X.flags c .center = true
        ∧ Action.unpause c .center ∉ tr ∧ Action.append c' f b ∈ tr
        ∧ ¬ SendOpen prof X.flags c b ∧ SendOpen prof X.flags c' b := by
  let X : PState := ⟨emptyManagers, noFlags.set 3 .center true⟩
  have hopen : SendOpen vaultProfile X.flags 1 2 := ⟨by decide, fun _ => by decide, fun _ => by decide⟩
  have hr : PRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) vaultProfile X
      (X.setLeg 1 1 2 .Committed) [.append 1 1 2] :=
    PRun.append (c := 1) (f := 1) (b := 2) PRun.refl rfl hopen
  refine ⟨fun _ _ => 1, lengthFlowHash, mixedSystem 1, vaultProfile, X, _, _, 3, 1, 1, 2, hr,
    Flags.set_same noFlags 3 .center true, by simp, List.mem_cons_self, ?_, hopen⟩
  rintro ⟨hc, _, _⟩
  exact absurd hc (by decide)

theorem paused_system_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (prof : Profile) (F : Flow)
      (ev : GateEvidence) (leg : FlowLeg) (Y : PSysState) (log : List Obligation)
      (alog : List AuthCall),
      Wf S ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ PSysSteps h z0 hl cv fh S prof ⟨Contracts.AppendPath.genesisAll, noFlags⟩ Y log alog
        ∧ (∃ c k, Y.flags c k = true) ∧ log ≠ [] ∧ alog ≠ []
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) alog
        ∧ ¬ Refunded (Contracts.AppendPath.Chains.mgrs Y.chains) (obligationOf F leg) := by
  obtain ⟨cv, fh, S, F, ev, leg, Y, log, alog, hS, hex, hsys, hmem, halog, _, hnb, hnr, _⟩ :=
    Contracts.AppendPath.SystemWitness h z0 hl
  have hp := PSysSteps.pause (c := 0) (k := .center) (sysSteps_pSysSteps vaultProfile hsys) rfl
  exact ⟨cv, fh, S, vaultProfile, F, ev, leg, _, log, alog, hS, hex, hp,
    ⟨0, .center, Flags.set_same noFlags 0 .center true⟩, List.ne_nil_of_mem hmem, halog, hnb, hnr⟩

theorem logged_execution_under_pause_witness (h : Hash) (hl : LeafHash) (a b : UInt256)
    (ha : 0 < a) (hab : a < b) :
    ∃ (cv : CommitValue) (fh : FlowHash) (prof : Profile) (Y : PState) (tr : List Action)
      (e : ExecCall) (r : AuthCall),
      Wf (paddedSystem a b)
        ∧ PRun h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) prof ⟨emptyManagers, noFlags⟩ Y tr
        ∧ (∃ c k, Action.pause c k ∈ tr) ∧ (∃ c k, Action.unpause c k ∈ tr)
        ∧ Action.execute e ∈ tr ∧ Action.authorize r ∈ tr ∧ r.flow.flowId = e.flow.flowId
        ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) r.missing.chain
            (e.evidence r.missing).1 (e.evidence r.missing).2
        ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) r.flow.deadline r.missing.chain
            r.batch r.proof
        ∧ ¬ FlowIdClash fh e.flow r.flow := by
  obtain ⟨cv, fh, Ms, log, e, r, hS, hrun, he, hr, hflow, hnI, hA, hnC⟩ :=
    padding_refund_lands_in_absence_break h hl a b ha hab
  obtain ⟨tr, htr, hlog⟩ := runLog_pRun vaultProfile hrun
  have hp := PRun.unpause (c := 5) (k := .center)
    (PRun.pause (c := 5) (k := .center) htr rfl) (Flags.set_same noFlags 5 .center true)
  rw [← hlog] at he hr
  refine ⟨cv, fh, vaultProfile, _, _, e, r, hS, hp, ⟨5, .center, by simp⟩,
    ⟨5, .center, by simp⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (execute_mem_of_checked he)), List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (authorize_mem_of_checked hr)), by rw [hflow], hnI, hA, hnC⟩

end Contracts.InteropPause

/-! ## Certificates -/

namespace Contracts.InteropPause

open Contracts.Atomicity Contracts.Refund Contracts.FlowBinding

theorem PausedRunIsRunLog : Properties.PausedRunIsRunLog :=
  fun _ _ _ _ _ _ _ _ _ _ hr => pRun_runLog hr

theorem PausedRunAuthCallsReachLog : Properties.PausedRunAuthCallsReachLog :=
  fun _ _ _ _ _ _ _ _ _ _ hr => pRun_reachLog hr

theorem RunLogIsUnpausedRun : Properties.RunLogIsUnpausedRun :=
  fun _ _ _ _ _ _ prof _ _ _ hr => runLog_pRun prof hr

theorem PausedExecutionIsExecution : Properties.PausedExecutionIsExecution :=
  fun _ _ _ _ _ _ _ _ _ _ _ hp => hp.2

theorem ExecutedObligationNeverRefundedOrBreakUnderPause :
    Properties.ExecutedObligationNeverRefundedOrBreakUnderPause :=
  fun _ _ _ _ _ _ hS _ _ _ hex _ _ _ _ hr => executed_freezes_flow_or_break_under_pause hS hex hr _ rfl

theorem OneExecutionFreezesTheFlowOrBreakUnderPause :
    Properties.OneExecutionFreezesTheFlowOrBreakUnderPause :=
  fun _ _ _ _ _ _ hS _ _ _ hex _ _ _ _ hr _ _ =>
    executed_freezes_flow_or_break_under_pause hS hex hr _ rfl

theorem NoneOrAllOrBreakUnderPause : Properties.NoneOrAllOrBreakUnderPause :=
  fun _ _ _ _ _ _ hS _ hDA prof P F ev => none_or_all_or_break_under_pause hS hDA prof P F ev

theorem NoneOrAllOrBreakPinnedUnderPause : Properties.NoneOrAllOrBreakPinnedUnderPause :=
  fun _ _ _ _ _ _ hS _ hDA prof P F ev => none_or_all_or_break_pinned_under_pause hS hDA prof P F ev

theorem LoggedExecutionExcludesLoggedRefundOrBreakUnderPause :
    Properties.LoggedExecutionExcludesLoggedRefundOrBreakUnderPause :=
  fun _ _ _ _ _ _ hS _ _ _ _ hr _ he _ ha hid =>
    logged_execution_excludes_logged_refund_or_break hS (pRun_runLog hr)
      (mem_checkedCalls_execute he) (mem_checkedCalls_authorize ha) hid

theorem ExecutedImpliesRealFlowFinalizableOrLoggedClashUnderPause :
    Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClashUnderPause :=
  fun _ _ _ _ _ _ hS _ hDA _ _ _ _ hr _ he _ hc hid =>
    executed_implies_real_flow_finalizable_or_logged_clash hS hDA (pRun_runLog hr)
      (mem_checkedCalls_execute he) hc hid

theorem PausedSystemIsSystemRun : Properties.PausedSystemIsSystemRun :=
  fun _ _ _ _ _ _ _ _ _ _ _ hr => pSysSteps_sysSteps hr

theorem SystemRunIsUnpausedSystemRun : Properties.SystemRunIsUnpausedSystemRun :=
  fun _ _ _ _ _ _ prof _ _ _ _ hr => sysSteps_pSysSteps prof hr

theorem SystemOncePerLegUnderPause : Properties.SystemOncePerLegUnderPause :=
  fun h z0 hl cv fh S _ _ Y log alog hr =>
    Contracts.AppendPath.SystemOncePerLeg h z0 hl cv fh S Y.chains log alog (pSysSteps_sysSteps hr)

theorem SystemExecutedObligationNeverRefundedOrBreakUnderPause :
    Properties.SystemExecutedObligationNeverRefundedOrBreakUnderPause :=
  fun h z0 hl cv fh S hS F ev leg hex _ _ Y log alog hr =>
    Contracts.AppendPath.SystemExecutedObligationNeverRefundedOrBreak h z0 hl cv fh S hS F ev leg
      hex Y.chains log alog (pSysSteps_sysSteps hr)

theorem PauseGatesReadOnlyTheirOwnFlags : Properties.PauseGatesReadOnlyTheirOwnFlags :=
  pause_gates_read_only_their_own_flags

theorem CommittedOnTimeExcludesRefundOrBreak : Properties.CommittedOnTimeExcludesRefundOrBreak :=
  fun _ _ _ _ _ hS _ hcom _ hother N q => committed_not_refundable_or_break hS hcom hother N q

theorem CommittedOnTimeNeverRefundedOrBreak : Properties.CommittedOnTimeNeverRefundedOrBreak :=
  fun _ _ _ _ _ _ hS _ hcom hchk _ _ _ _ hr o ho =>
    committed_freezes_flow_or_break hS hcom hchk (pRun_reachLog hr) o ho

theorem PausedDestinationLeavesFlowStuck : Properties.PausedDestinationLeavesFlowStuck :=
  fun _ _ _ _ _ _ hS _ _ hcom hchk _ _ _ _ _ hr hmint hp =>
    paused_destination_leaves_flow_stuck hS hcom hchk hr hmint hp

theorem PausedDestinationStaysPausedAlongRuns :
    Properties.PausedDestinationStaysPausedAlongRuns :=
  fun _ _ _ _ _ _ _ _ _ _ _ hr hX hnu => paused_destination_stays_paused hr hX hnu

theorem PausedCenterStaysPausedAlongRuns : Properties.PausedCenterStaysPausedAlongRuns :=
  fun _ _ _ _ _ _ _ _ _ _ _ hr hX hnu => paused_center_stays_paused hr hX hnu

theorem PausedCenterWitness : Properties.PausedCenterWitness := paused_center_witness

theorem PermanentDestinationPauseStrandsLeg : Properties.PermanentDestinationPauseStrandsLeg :=
  fun _ _ _ _ _ _ hS _ _ hcom hchk _ _ _ _ _ hr₀ hmint hX _ _ hr hnu =>
    permanent_destination_pause_strands_leg hS hcom hchk hr₀ hmint hX hr hnu

theorem UnpausedGateIsTheGate : Properties.UnpausedGateIsTheGate :=
  fun _ _ _ _ _ _ prof P F ev leg => unpaused_gate_is_the_gate prof P F ev leg

theorem UnpauseRestoresExecution : Properties.UnpauseRestoresExecution :=
  fun _ _ _ _ _ _ hS _ hDA _ _ hcom hchk hleg _ _ _ _ hr =>
    unpause_restores_execution hS hDA hcom hchk hleg hr

theorem PausedVaultKeepsLegRevertable : Properties.PausedVaultKeepsLegRevertable :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hr hrec hX hnu hst =>
    paused_vault_keeps_leg_revertable hr hrec hX hnu hst

theorem UnpauseReEnablesClaim : Properties.UnpauseReEnablesClaim :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ hr hst => unpause_reenables_claim hr hst

theorem PauseRunWitness : Properties.PauseRunWitness := pause_run_witness

theorem PausedDestinationStuckWitness : Properties.PausedDestinationStuckWitness :=
  paused_destination_stuck_witness

theorem PausedVaultClaimWitness : Properties.PausedVaultClaimWitness :=
  paused_vault_claim_witness

theorem DestinationPauseStrandsSiblingWitness : Properties.DestinationPauseStrandsSiblingWitness :=
  destination_pause_strands_sibling_witness

theorem PausedSystemWitness : Properties.PausedSystemWitness := paused_system_witness

theorem LoggedExecutionExcludesLoggedRefundOrBreakUnderPauseWitness :
    Properties.LoggedExecutionExcludesLoggedRefundOrBreakUnderPauseWitness :=
  logged_execution_under_pause_witness

end Contracts.InteropPause
