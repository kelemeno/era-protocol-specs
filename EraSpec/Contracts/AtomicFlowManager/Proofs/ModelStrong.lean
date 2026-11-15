import EraSpec.Contracts.AtomicFlowManager.Properties.ModelStrong
import EraSpec.Contracts.AtomicFlowManager.Proofs.Model


/-!
# Proofs: `AtomicFlowManager`, stated over runs and over reentrant claims

Proofs of `EraSpec.Contracts.AtomicFlowManager.Properties.ModelStrong`.

Everything about traces comes from one induction, `legRun_leg_trace`.  A step either names leg `(f, b)` and moves
it from its operation's guard state to its write state (`legStep_spec`), or names another leg and leaves `(f, b)`
alone (`applyEvent_legState`).  Monotonicity (`reach_rank_mono`) keeps the rest of the run above the written state,
so the operations that touch the leg line up with `opsBetween`.  The reentrancy results come from
`writeFirst_nestedRun_reach`: under the deployed order a nested execution is a `Reach`.  Then `Reverted` is
absorbing (`reverted_absorbing`), and the payout count adds up along the execution (`reached_add`).
-/

namespace Contracts.AtomicFlowManager.ModelStrong


/-! ## Point updates and runs -/

lemma legState_set (M : Manager) (f b f' b' : UInt256) (s : LegState) :
    (M.set f b s).legState f' b' = if f' = f ∧ b' = b then s else M.legState f' b' :=
  rfl

lemma applyEvent_legState (M : Manager) (e : LegEvent) (f b : UInt256) :
    (applyEvent M e).legState f b = if e.flow = f ∧ e.bundle = b then e.op.writes else M.legState f b := by
  unfold applyEvent
  rw [legState_set]
  by_cases h : e.flow = f ∧ e.bundle = b
  · rw [ite_eq_left ⟨h.1.symm, h.2.symm⟩, ite_eq_left h]
  · rw [ite_eq_right (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), ite_eq_right h]

lemma rank_writes (op : LegOp) : rank op.writes = rank op.needs + 1 := by
  cases op <;> rfl

lemma writes_ne_needs (op : LegOp) : op.writes ≠ op.needs := by
  cases op <;> decide

lemma rank_le_three' (s : LegState) : rank s ≤ 3 := by
  cases s <;> decide

lemma reach_head {M N P : Manager} (hs : Step M N) (hr : Reach N P) : Reach M P := by
  induction hr with
  | refl => exact Reach.tail Reach.refl hs
  | tail _ hs' ih => exact Reach.tail ih hs'

lemma reach_trans {M N P : Manager} (h₁ : Reach M N) (h₂ : Reach N P) : Reach M P := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact Reach.tail ih hs

lemma rank_mono {M N : Manager} (h : Reach M N) (f b : UInt256) :
    rank (M.legState f b) ≤ rank (N.legState f b) :=
  reach_rank_mono h f b

lemma reverted_stays {M N : Manager} (h : Reach M N) {f b : UInt256}
    (hrev : M.legState f b = .Reverted) : N.legState f b = .Reverted :=
  reverted_absorbing h hrev


/-! ## Labelled steps and runs -/

lemma legStep_step {M N : Manager} {e : LegEvent} (h : LegStep M e N) : Step M N := by
  cases h with
  | append hg => exact Step.append hg
  | authorize hg => exact Step.authorize hg
  | claim hg => exact Step.claim hg

lemma step_legStep {M N : Manager} (h : Step M N) : ∃ e, LegStep M e N := by
  cases h with
  | append hg => exact ⟨_, LegStep.append hg⟩
  | authorize hg => exact ⟨_, LegStep.authorize hg⟩
  | claim hg => exact ⟨_, LegStep.claim hg⟩

/-- A labelled step's guard, and the state it leaves. -/
lemma legStep_spec {M N : Manager} {e : LegEvent} (h : LegStep M e N) :
    M.legState e.flow e.bundle = e.op.needs ∧ N = applyEvent M e := by
  cases h with
  | append hg => exact ⟨hg, rfl⟩
  | authorize hg => exact ⟨hg, rfl⟩
  | claim hg => exact ⟨hg, rfl⟩

lemma legRun_reach {M N : Manager} {es : List LegEvent} (h : LegRun M es N) : Reach M N := by
  induction h with
  | nil => exact Reach.refl
  | cons hs _ ih => exact reach_head (legStep_step hs) ih

lemma legRun_snoc {M N P : Manager} {es : List LegEvent} {e : LegEvent} (h : LegRun M es N)
    (hs : LegStep N e P) : LegRun M (es ++ [e]) P := by
  induction h with
  | nil => exact LegRun.cons hs LegRun.nil
  | cons hs' _ ih => exact LegRun.cons hs' (ih hs)

lemma reach_legRun {M N : Manager} (h : Reach M N) : ∃ es, LegRun M es N := by
  induction h with
  | refl => exact ⟨[], LegRun.nil⟩
  | tail _ hs ih =>
    obtain ⟨es, hr⟩ := ih
    obtain ⟨e, he⟩ := step_legStep hs
    exact ⟨es ++ [e], legRun_snoc hr he⟩

lemma legRun_split {M N : Manager} {es₂ : List LegEvent} {e : LegEvent} :
    ∀ {es₁ : List LegEvent}, LegRun M (es₁ ++ e :: es₂) N →
      ∃ P Q, LegRun M es₁ P ∧ LegStep P e Q ∧ LegRun Q es₂ N := by
  intro es₁
  induction es₁ generalizing M with
  | nil =>
    intro h
    cases h with
    | cons hs hr => exact ⟨M, _, LegRun.nil, hs, hr⟩
  | cons e' es₁ ih =>
    intro h
    cases h with
    | cons hs hr =>
      obtain ⟨P, Q, h₁, h₂, h₃⟩ := ih hr
      exact ⟨P, Q, LegRun.cons hs h₁, h₂, h₃⟩


/-! ## Leg traces -/

lemma legTrace_nil (f b : UInt256) : legTrace f b [] = [] := rfl

lemma legTrace_cons_pos {f b : UInt256} {e : LegEvent} (es : List LegEvent)
    (he : e.flow = f ∧ e.bundle = b) : legTrace f b (e :: es) = e :: legTrace f b es := by
  unfold legTrace
  rw [List.filter_cons_of_pos (by simpa using he)]

lemma legTrace_cons_neg {f b : UInt256} {e : LegEvent} (es : List LegEvent)
    (he : ¬(e.flow = f ∧ e.bundle = b)) : legTrace f b (e :: es) = legTrace f b es := by
  unfold legTrace
  rw [List.filter_cons_of_neg (by simpa using he)]

lemma mem_of_mem_legTrace_op {f b : UInt256} {es : List LegEvent} {op : LegOp}
    (h : op ∈ (legTrace f b es).map LegEvent.op) : (⟨op, f, b⟩ : LegEvent) ∈ es := by
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp h
  unfold legTrace at he
  rw [List.mem_filter] at he
  obtain ⟨hmem, hdec⟩ := he
  have hfb : e.flow = f ∧ e.bundle = b := of_decide_eq_true hdec
  have he' : e = ⟨e.op, f, b⟩ := by
    cases e
    simp only at hfb
    rw [hfb.1, hfb.2]
  rw [← he']
  exact hmem

/-- The operations from an operation's guard state are that operation, then the ones from its write state. -/
lemma opsBetween_needs (op : LegOp) (t : LegState) (ht : rank op.writes ≤ rank t) :
    opsBetween op.needs t = op :: opsBetween op.writes t := by
  cases op <;> cases t <;> revert ht <;> decide

lemma opsBetween_length (s t : LegState) (h : rank s ≤ rank t) :
    (opsBetween s t).length = rank t - rank s := by
  cases s <;> cases t <;> revert h <;> decide


/-! ## The labelled machine is the machine -/

theorem legStep_iff_step {M N : Manager} :
    Properties.legStep_iff_step (M := M) (N := N) := by
  unfold Properties.legStep_iff_step
  exact ⟨step_legStep, fun ⟨_, he⟩ => legStep_step he⟩

theorem reach_iff_legRun {M N : Manager} :
    Properties.reach_iff_legRun (M := M) (N := N) := by
  unfold Properties.reach_iff_legRun
  exact ⟨reach_legRun, fun ⟨_, hr⟩ => legRun_reach hr⟩


/-! ## What a run does to one leg -/

theorem legRun_leg_trace {M N : Manager} {es : List LegEvent} (h : LegRun M es N) (f b : UInt256) :
    Properties.legRun_leg_trace (h := h) (f := f) (b := b) := by
  unfold Properties.legRun_leg_trace
  induction h with
  | nil => simp [legTrace_nil, opsBetween]
  | @cons M e N es P hs hr ih =>
    obtain ⟨hneed, rfl⟩ := legStep_spec hs
    have hmono := rank_mono (legRun_reach hr) f b
    rw [applyEvent_legState] at hmono ih
    by_cases he : e.flow = f ∧ e.bundle = b
    · rw [ite_eq_left he] at hmono ih
      rw [legTrace_cons_pos es he, List.map_cons, ih]
      obtain ⟨rfl, rfl⟩ := he
      rw [hneed]
      exact (opsBetween_needs e.op _ hmono).symm
    · rw [ite_eq_right he] at ih
      rw [legTrace_cons_neg es he, ih]


/-! ## A refund requires a prior authorization -/

/-- The only step into an operation's write state is that operation, from its guard state. -/
lemma step_into_writes {M N : Manager} (h : Step M N) {f b : UInt256} (op : LegOp)
    (hpre : M.legState f b ≠ op.writes) (hpost : N.legState f b = op.writes) :
    M.legState f b = op.needs ∧ N = M.set f b op.writes := by
  obtain ⟨e, he⟩ := step_legStep h
  obtain ⟨hneed, rfl⟩ := legStep_spec he
  rw [applyEvent_legState] at hpost
  by_cases hfb : e.flow = f ∧ e.bundle = b
  · rw [ite_eq_left hfb] at hpost
    obtain ⟨rfl, rfl⟩ := hfb
    have hop : e.op = op := by
      revert hpost
      cases e.op <;> cases op <;> decide
    refine ⟨by rw [hneed, hop], ?_⟩
    unfold applyEvent
    rw [hop]
  · rw [ite_eq_right hfb] at hpost
    exact absurd hpost hpre

/-- …and along a run, the leg passed through that operation. -/
lemma reach_into_writes {M N : Manager} (h : Reach M N) {f b : UInt256} (op : LegOp)
    (hpre : M.legState f b ≠ op.writes) (hpost : N.legState f b = op.writes) :
    ∃ P, Reach M P ∧ P.legState f b = op.needs ∧ Reach (P.set f b op.writes) N := by
  induction h with
  | refl => exact absurd hpost hpre
  | @tail N' P' hr hs ih =>
    by_cases hmid : N'.legState f b = op.writes
    · obtain ⟨P, h₁, h₂, h₃⟩ := ih hmid
      exact ⟨P, h₁, h₂, Reach.tail h₃ hs⟩
    · obtain ⟨h₁, rfl⟩ := step_into_writes hs op hmid hpost
      exact ⟨N', hr, h₁, Reach.refl⟩

theorem step_into_revertable_is_authorize {M N : Manager} (h : Step M N) {f b : UInt256}
    (hpre : M.legState f b ≠ .Revertable) (hpost : N.legState f b = .Revertable) :
    Properties.step_into_revertable_is_authorize (h := h) (hpre := hpre) (hpost := hpost) := by
  unfold Properties.step_into_revertable_is_authorize
  exact step_into_writes h .authorize hpre hpost

theorem claimable_reach_passed_authorize {M N : Manager} (h : Reach M N) {f b : UInt256}
    (hpre : M.legState f b ≠ .Revertable) (hg : ClaimGuard N f b) :
    Properties.claimable_reach_passed_authorize (h := h) (hpre := hpre) (hg := hg) := by
  unfold Properties.claimable_reach_passed_authorize
  exact reach_into_writes h .authorize hpre hg

theorem claim_event_preceded_by_authorize {M N : Manager} {es : List LegEvent}
    (h : LegRun M es N) {f b : UInt256} (hpre : M.legState f b ≠ .Revertable)
    {es₁ es₂ : List LegEvent} (hsplit : es = es₁ ++ ⟨.claim, f, b⟩ :: es₂) :
    Properties.claim_event_preceded_by_authorize (h := h) (hpre := hpre) (hsplit := hsplit) := by
  unfold Properties.claim_event_preceded_by_authorize
  subst hsplit
  obtain ⟨P, Q, h₁, h₂, -⟩ := legRun_split h
  obtain ⟨hP, -⟩ := legStep_spec h₂
  have hP' : P.legState f b = .Revertable := hP
  have htrace := legRun_leg_trace h₁ f b
  unfold Properties.legRun_leg_trace at htrace
  have hmono := rank_mono (legRun_reach h₁) f b
  rw [hP'] at htrace hmono
  apply mem_of_mem_legTrace_op
  rw [htrace]
  revert hpre hmono
  cases M.legState f b <;> decide


/-! ## From `Committed` or `Unset`, the claim gate opens only through `authorize` -/

theorem committed_claimable_trace {M N : Manager} {es : List LegEvent} (h : LegRun M es N)
    {f b : UInt256} (hc : M.legState f b = .Committed) (hg : ClaimGuard N f b) :
    Properties.committed_claimable_trace (h := h) (hc := hc) (hg := hg) := by
  unfold Properties.committed_claimable_trace
  have htrace := legRun_leg_trace h f b
  unfold Properties.legRun_leg_trace at htrace
  have hg' : N.legState f b = .Revertable := hg
  rw [htrace, hc, hg']
  decide

theorem unset_claimable_trace {M N : Manager} {es : List LegEvent} (h : LegRun M es N)
    {f b : UInt256} (hu : M.legState f b = .Unset) (hg : ClaimGuard N f b) :
    Properties.unset_claimable_trace (h := h) (hu := hu) (hg := hg) := by
  unfold Properties.unset_claimable_trace
  have htrace := legRun_leg_trace h f b
  unfold Properties.legRun_leg_trace at htrace
  have hg' : N.legState f b = .Revertable := hg
  rw [htrace, hu, hg']
  decide


/-! ## How often a run moves a leg -/

theorem step_leg_same_or_next {M N : Manager} (h : Step M N) (f b : UInt256) :
    Properties.step_leg_same_or_next (h := h) (f := f) (b := b) := by
  unfold Properties.step_leg_same_or_next
  obtain ⟨e, he⟩ := step_legStep h
  obtain ⟨hneed, rfl⟩ := legStep_spec he
  rw [applyEvent_legState]
  by_cases hfb : e.flow = f ∧ e.bundle = b
  · rw [ite_eq_left hfb]
    right
    obtain ⟨rfl, rfl⟩ := hfb
    rw [hneed]
    exact rank_writes e.op
  · rw [ite_eq_right hfb]
    left
    rfl

theorem legStep_changes_iff_names {M N : Manager} {e : LegEvent} (h : LegStep M e N)
    (f b : UInt256) :
    Properties.legStep_changes_iff_names (h := h) (f := f) (b := b) := by
  unfold Properties.legStep_changes_iff_names
  obtain ⟨hneed, rfl⟩ := legStep_spec h
  rw [applyEvent_legState]
  by_cases hfb : e.flow = f ∧ e.bundle = b
  · rw [ite_eq_left hfb]
    refine ⟨fun _ => hfb, fun _ => ?_⟩
    obtain ⟨rfl, rfl⟩ := hfb
    rw [hneed]
    exact writes_ne_needs e.op
  · rw [ite_eq_right hfb]
    exact ⟨fun hne => absurd rfl hne, fun h' => absurd h' hfb⟩

/-- The count of changing steps, by the same induction as `legRun_leg_trace`. -/
lemma legRun_legChanges {M N : Manager} {es : List LegEvent} (h : LegRun M es N) (f b : UInt256) :
    legChanges f b M es = rank (N.legState f b) - rank (M.legState f b) := by
  induction h with
  | nil => simp [legChanges]
  | @cons M e N es P hs hr ih =>
    obtain ⟨hneed, rfl⟩ := legStep_spec hs
    have hmono := rank_mono (legRun_reach hr) f b
    simp only [legChanges]
    rw [ih]
    rw [applyEvent_legState] at hmono ⊢
    by_cases hfb : e.flow = f ∧ e.bundle = b
    · rw [ite_eq_left hfb] at hmono ⊢
      obtain ⟨rfl, rfl⟩ := hfb
      rw [hneed, ite_eq_right (writes_ne_needs e.op)]
      have hr := rank_writes e.op
      omega
    · rw [ite_eq_right hfb, ite_eq_left rfl]
      omega

theorem legRun_changes_eq_rank_gain {M N : Manager} {es : List LegEvent} (h : LegRun M es N)
    (f b : UInt256) :
    Properties.legRun_changes_eq_rank_gain (h := h) (f := f) (b := b) := by
  unfold Properties.legRun_changes_eq_rank_gain
  refine ⟨legRun_legChanges h f b, ?_⟩
  have htrace := legRun_leg_trace h f b
  unfold Properties.legRun_leg_trace at htrace
  rw [← List.length_map (f := LegEvent.op), htrace]
  exact opsBetween_length _ _ (rank_mono (legRun_reach h) f b)

theorem legRun_changes_le_three {M N : Manager} {es : List LegEvent} (h : LegRun M es N)
    (f b : UInt256) :
    Properties.legRun_changes_le_three (h := h) (f := f) (b := b) := by
  unfold Properties.legRun_changes_le_three
  rw [legRun_legChanges h f b]
  have := rank_le_three' (N.legState f b)
  omega


/-! ## The premises are satisfiable, and the bound is attained -/

theorem modelStrong_runs_witness : Properties.modelStrong_runs_witness := by
  unfold Properties.modelStrong_runs_witness
  have s₁ : LegStep empty ⟨.append, 0, 0⟩ witness₁ := LegStep.append (by unfold AppendGuard; decide)
  have s₂ : LegStep witness₁ ⟨.append, 0, 1⟩ witness₂ := LegStep.append (by unfold AppendGuard; decide)
  have s₃ : LegStep witness₂ ⟨.authorize, 0, 0⟩ witness₃ :=
    LegStep.authorize (by unfold AuthorizeGuard; decide)
  have s₄ : LegStep witness₃ ⟨.claim, 0, 0⟩ witness₄ := LegStep.claim (by unfold ClaimGuard; decide)
  have r₃ : LegRun empty (witnessTrace.take 3) witness₃ :=
    LegRun.cons s₁ (LegRun.cons s₂ (LegRun.cons s₃ LegRun.nil))
  refine ⟨LegRun.cons s₁ (LegRun.cons s₂ (LegRun.cons s₃ (LegRun.cons s₄ LegRun.nil))), by decide,
    by decide, r₃, legRun_reach r₃, by unfold ClaimGuard; decide,
    LegRun.cons s₂ (LegRun.cons s₃ LegRun.nil), by decide, s₃, legStep_step s₃, by decide, by decide,
    by decide, by decide⟩


/-! ## Reentrant claims -/

lemma nestedRun_trans {o : ClaimOrder} {M N P : Manager} {l₁ l₂ : List LegKey}
    (h₁ : NestedRun o M l₁ N) (h₂ : NestedRun o N l₂ P) : NestedRun o M (l₁ ++ l₂) P := by
  induction h₁ with
  | nil => simpa using h₂
  | append hg _ ih => exact NestedRun.append hg (ih h₂)
  | authorize hg _ ih => exact NestedRun.authorize hg (ih h₂)
  | claimWriteFirst ho hg hcb _ _ ih₂ =>
    rw [List.append_assoc, List.cons_append]
    exact NestedRun.claimWriteFirst ho hg hcb (ih₂ h₂)
  | claimWriteAfter ho hg hcb _ _ ih₂ =>
    rw [List.append_assoc, List.cons_append]
    exact NestedRun.claimWriteAfter ho hg hcb (ih₂ h₂)

lemma step_nestedRun (o : ClaimOrder) {M N : Manager} (h : Step M N) : ∃ log, NestedRun o M log N := by
  cases h with
  | append hg => exact ⟨[], NestedRun.append hg NestedRun.nil⟩
  | authorize hg => exact ⟨[], NestedRun.authorize hg NestedRun.nil⟩
  | @claim f b hg =>
    cases o with
    | writeFirst => exact ⟨_, NestedRun.claimWriteFirst rfl hg NestedRun.nil NestedRun.nil⟩
    | writeAfter => exact ⟨_, NestedRun.claimWriteAfter rfl hg NestedRun.nil NestedRun.nil⟩

theorem writeFirst_nestedRun_reach {M N : Manager} {log : List LegKey}
    (h : NestedRun .writeFirst M log N) :
    Properties.writeFirst_nestedRun_reach (h := h) := by
  unfold Properties.writeFirst_nestedRun_reach
  induction h with
  | nil => exact Reach.refl
  | append hg _ ih => exact reach_head (Step.append hg) ih
  | authorize hg _ ih => exact reach_head (Step.authorize hg) ih
  | claimWriteFirst _ hg _ _ ih₁ ih₂ => exact reach_head (Step.claim hg) (reach_trans ih₁ ih₂)
  | claimWriteAfter ho _ _ _ _ _ => exact absurd ho (by decide)

theorem reach_nestedRun (o : ClaimOrder) {M N : Manager} (h : Reach M N) :
    Properties.reach_nestedRun (o := o) (h := h) := by
  unfold Properties.reach_nestedRun
  induction h with
  | refl => exact ⟨[], NestedRun.nil⟩
  | tail _ hs ih =>
    obtain ⟨l, hl⟩ := ih
    obtain ⟨l', hl'⟩ := step_nestedRun o hs
    exact ⟨l ++ l', nestedRun_trans hl hl'⟩

/-- `1` if the leg went to `Reverted` between `M` and `N`, else `0`. -/
def reached (f b : UInt256) (M N : Manager) : ℕ :=
  if M.legState f b ≠ .Reverted ∧ N.legState f b = .Reverted then 1 else 0

/-- Along a run, `reached` adds up. -/
lemma reached_add {M N P : Manager} (h₁ : Reach M N) (h₂ : Reach N P) (f b : UInt256) :
    reached f b M P = reached f b M N + reached f b N P := by
  unfold reached
  by_cases hM : M.legState f b = .Reverted
  · have hN := reverted_stays h₁ hM
    have hP := reverted_stays h₂ hN
    simp [hM, hN, hP]
  · by_cases hN : N.legState f b = .Reverted
    · have hP := reverted_stays h₂ hN
      simp [hM, hN, hP]
    · simp [hM, hN]

/-- A write that is not `Reverted`, onto a leg that is not `Reverted`, keeps every leg's "is it `Reverted`". -/
lemma reached_set {M N : Manager} {f b f' b' : UInt256} {s : LegState} (hs : s ≠ .Reverted)
    (hM : M.legState f' b' ≠ .Reverted) :
    reached f b (M.set f' b' s) N = reached f b M N := by
  unfold reached
  rw [legState_set]
  by_cases he : f = f' ∧ b = b'
  · rw [ite_eq_left he]
    obtain ⟨rfl, rfl⟩ := he
    simp [hs, hM]
  · rw [ite_eq_right he]

lemma writeFirst_count {M N : Manager} {log : List LegKey} (h : NestedRun .writeFirst M log N)
    (f b : UInt256) : log.count (f, b) = reached f b M N := by
  induction h with
  | nil => simp [reached]
  | @append M f' b' log N hg _ ih =>
    rw [ih, reached_set (by decide) (by rw [show M.legState f' b' = .Unset from hg]; decide)]
  | @authorize M f' b' log N hg _ ih =>
    rw [ih, reached_set (by decide) (by rw [show M.legState f' b' = .Committed from hg]; decide)]
  | @claimWriteFirst M f' b' callback N₁ rest N _ hg hcb hrest ih₁ ih₂ =>
    have r₁ := writeFirst_nestedRun_reach hcb
    have r₂ := writeFirst_nestedRun_reach hrest
    unfold Properties.writeFirst_nestedRun_reach at r₁ r₂
    rw [List.count_append, List.count_cons, ih₁, ih₂]
    have hg' : M.legState f' b' = .Revertable := hg
    by_cases he : (f', b') = (f, b)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      have hw : (M.set f' b' .Reverted).legState f' b' = .Reverted := set_same
      have hN₁ := reverted_stays r₁ hw
      have hN := reverted_stays r₂ hN₁
      simp [reached, hN₁, hN, hg']
    · have hb : ((f', b') == (f, b)) = false := by simpa using he
      have hne : ¬(f = f' ∧ b = b') := fun ⟨h₁, h₂⟩ => he (by rw [h₁, h₂])
      have hset : reached f b (M.set f' b' .Reverted) N₁ = reached f b M N₁ := by
        unfold reached
        rw [legState_set, ite_eq_right hne]
      rw [hb, hset, reached_add (reach_head (Step.claim hg) r₁) r₂]
      simp
  | claimWriteAfter ho _ _ _ _ _ => exact absurd ho (by decide)

theorem writeFirst_payouts_exact {M N : Manager} {log : List LegKey}
    (h : NestedRun .writeFirst M log N) (f b : UInt256) :
    Properties.writeFirst_payouts_exact (h := h) (f := f) (b := b) := by
  unfold Properties.writeFirst_payouts_exact
  exact writeFirst_count h f b

theorem writeFirst_payout_at_most_once {M N : Manager} {log : List LegKey}
    (h : NestedRun .writeFirst M log N) (f b : UInt256) :
    Properties.writeFirst_payout_at_most_once (h := h) (f := f) (b := b) := by
  unfold Properties.writeFirst_payout_at_most_once
  rw [writeFirst_count h f b]
  unfold reached
  split_ifs <;> omega

theorem writeFirst_callback_never_reclaims {M N₁ : Manager} {f b : UInt256}
    {callback : List LegKey} (hg : ClaimGuard M f b)
    (hcb : NestedRun .writeFirst (M.set f b .Reverted) callback N₁) :
    Properties.writeFirst_callback_never_reclaims (hg := hg) (hcb := hcb) := by
  unfold Properties.writeFirst_callback_never_reclaims
  have hw : (M.set f b .Reverted).legState f b = .Reverted := set_same
  have hcount := writeFirst_count hcb f b
  have r := writeFirst_nestedRun_reach hcb
  unfold Properties.writeFirst_nestedRun_reach at r
  refine ⟨?_, reverted_stays r hw⟩
  rw [← List.count_eq_zero, hcount]
  simp [reached]

theorem writeAfter_unbounded_payouts {M : Manager} {f b : UInt256} (hg : ClaimGuard M f b) (k : ℕ) :
    Properties.writeAfter_unbounded_payouts (hg := hg) (k := k) := by
  unfold Properties.writeAfter_unbounded_payouts
  induction k with
  | zero => exact ⟨M, NestedRun.nil⟩
  | succ k ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨N.set f b .Reverted, ?_⟩
    have h := NestedRun.claimWriteAfter rfl hg hN (NestedRun.nil (M := N.set f b .Reverted))
    rwa [List.replicate_succ']

theorem claim_order_decides_double_payout {M : Manager} {f b : UInt256} (hg : ClaimGuard M f b) :
    Properties.claim_order_decides_double_payout (hg := hg) := by
  unfold Properties.claim_order_decides_double_payout
  refine ⟨fun log N h => writeFirst_payout_at_most_once h f b, ?_⟩
  exact writeAfter_unbounded_payouts hg 2

theorem nestedRun_witness : Properties.nestedRun_witness := by
  unfold Properties.nestedRun_witness
  let M₁ := empty.set 0 0 .Committed
  let M₂ := M₁.set 0 1 .Committed
  let M₃ := M₂.set 0 0 .Revertable
  let M₄ := M₃.set 0 1 .Revertable
  have hr : Reach empty M₄ :=
    Reach.tail (Reach.tail (Reach.tail (Reach.tail Reach.refl
      (Step.append (by unfold AppendGuard; decide))) (Step.append (by unfold AppendGuard; decide)))
      (Step.authorize (by unfold AuthorizeGuard; decide))) (Step.authorize (by unfold AuthorizeGuard; decide))
  have hcb : NestedRun .writeFirst (M₄.set 0 0 .Reverted) [(0, 1)]
      ((M₄.set 0 0 .Reverted).set 0 1 .Reverted) :=
    NestedRun.claimWriteFirst (callback := []) (rest := []) rfl (by unfold ClaimGuard; decide)
      NestedRun.nil NestedRun.nil
  have hall : NestedRun .writeFirst M₄ [(0, 1), (0, 0)] ((M₄.set 0 0 .Reverted).set 0 1 .Reverted) :=
    NestedRun.claimWriteFirst (callback := [(0, 1)]) (rest := []) rfl (by unfold ClaimGuard; decide) hcb
      NestedRun.nil
  exact ⟨M₄, _, _, hr, by unfold ClaimGuard; decide, by unfold ClaimGuard; decide, hcb, hall, by decide,
    by decide⟩


end Contracts.AtomicFlowManager.ModelStrong
