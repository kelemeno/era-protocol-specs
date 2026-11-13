import EraSpec.Contracts.InteropHandlerBase.Properties.AtomicUnbundlingAtHead
import EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyAtHead
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachine

/-!
# Proofs: an atomic bundle on the unbundled route at head

* The finding is a computation: `partialRun` is evaluated symbolically on any bundle with two calls
  (`submitAll_partialRun`). Its permanence is the pinned invariant `Good` read at head
  (`ReentrancyAtHead.submitAll_good`): a `Cancelled` call status only loops to itself, a committed
  delivery is recorded `Executed`, and an `Unbundled` bundle stays `Unbundled`.
* `EveryDeliveryFollowsTheFlowGateAtHead` is a second invariant over every committed frame,
  `Gated`, proved by induction on the budget (`exec_gated`): a bundle hash leaves `Unreceived` only
  with a gate event logged, and each delivery is of a hash that had left `Unreceived` where the
  frame started or follows a gate event in the frame's log. A call loop satisfies it once its own
  bundle has left `Unreceived`, which its entry point's write before the calls ensures.
* `PartialExecutionNeedsVerifyAtomicBundleAtHead` is a third, `Routed` (`exec_routed`): a hash
  becomes `Verified` or `Unbundled` only with `verifyAtomicBundle`'s event logged, and each delivery
  is of such a hash or of one whose `BundleExecuted` is in the log.
-/

namespace Contracts.InteropHandlerAtHead

open AttackVectors.BundleStatusMachine
open Contracts.InteropHandler (BundleHash Bundle State Effect Spent CallsClosed init wA
  markCalls toExecute)

/-! ## The partial run, computed -/

/-- The first loop of `unbundleBundle` over requests that skip changes nothing. -/
lemma markCalls_skip (h : BundleHash) : ∀ (k i : ℕ) (s : State),
    markCalls true h i (List.replicate k .Unprocessed) s = some s
  | 0, _, _ => rfl
  | k + 1, i, s => by
      rw [List.replicate_succ, markCalls]
      exact markCalls_skip h k (i + 1) s

/-- Requests that skip deliver nothing. -/
lemma toExecute_skip : ∀ (k i : ℕ), toExecute i (List.replicate k CallStatus.Unprocessed) = []
  | 0, _ => rfl
  | k + 1, i => by
      rw [List.replicate_succ, toExecute]
      exact toExecute_skip k (i + 1)

/-- In a `CallsClosed` state, an `Unreceived` bundle's calls are `Unprocessed`. -/
lemma unprocessed_of_callsClosed {s : State} {h : BundleHash} (hc : CallsClosed s)
    (hu : s.bundle h = .Unreceived) (i : ℕ) : s.call h i = .Unprocessed := by
  by_contra hne
  rcases hc h i hne with h1 | h1 <;> rw [hu] at h1 <;> cases h1

lemma submit_verify {s : State} {b : Bundle} (hu : s.bundle b.hash = .Unreceived) :
    submit s ⟨1, .verifyAtomicBundle b true, []⟩ =
      (s.setBundle b.hash .Verified, [.verified b.hash]) := by
  simp [submit, exec, hu, commit]

lemma submit_partial {u : State} {b : Bundle} (hv : u.bundle b.hash = .Verified)
    (h0 : u.call b.hash 0 = .Unprocessed) (h1 : u.call b.hash 1 = .Unprocessed)
    (hn : 2 ≤ b.calls) :
    submit u ⟨4, .unbundleBundle b (partialRequest b.calls), []⟩ =
      (((u.setBundle b.hash .Unbundled).setCall b.hash 0 .Executed).setCall b.hash 1 .Cancelled,
        [.effect (.delivered b.hash 0)]) := by
  have hlen : (partialRequest b.calls).length = b.calls := by
    simp only [partialRequest, List.length_cons, List.length_replicate]
    omega
  have hm : markCalls true b.hash 0 (partialRequest b.calls) (u.setBundle b.hash .Unbundled) =
      some (((u.setBundle b.hash .Unbundled).setCall b.hash 0 .Executed).setCall
        b.hash 1 .Cancelled) := by
    simp [partialRequest, markCalls, h0, h1, markCalls_skip]
  have ht : toExecute 0 (partialRequest b.calls) = [0] := by
    simp [partialRequest, toExecute, toExecute_skip]
  simp only [submit]
  show commit u (exec (2 + 1 + 1) _ u) = _
  simp only [exec]
  rw [if_pos ⟨hlen, Or.inl hv⟩, hm, ht]
  simp [exec, commit]

/-- `partialRun`, evaluated. -/
lemma submitAll_partialRun {s : State} {b : Bundle} (hc : CallsClosed s)
    (hu : s.bundle b.hash = .Unreceived) (hn : 2 ≤ b.calls) :
    submitAll s (partialRun b) =
      (((((s.setBundle b.hash .Verified).setBundle b.hash .Unbundled).setCall
          b.hash 0 .Executed).setCall b.hash 1 .Cancelled),
        [.verified b.hash, .effect (.delivered b.hash 0)]) := by
  have h0 := unprocessed_of_callsClosed hc hu 0
  have h1 := unprocessed_of_callsClosed hc hu 1
  have hp := submit_partial (u := s.setBundle b.hash .Verified) (b := b) (by simp)
    (by simpa using h0) (by simpa using h1) hn
  simp only [partialRun, submitAll, submit_verify hu, hp]
  rfl

lemma submitAll_append : ∀ (s : State) (a c : List Tx),
    submitAll s (a ++ c) =
      ((submitAll (submitAll s a).1 c).1, (submitAll s a).2 ++ (submitAll (submitAll s a).1 c).2)
  | s, [], c => by simp [submitAll]
  | s, t :: a, c => by
      simp only [List.cons_append, submitAll]
      rw [submitAll_append (submit s t).1 a c]
      simp [List.append_assoc]

/-! ## The finding -/

theorem CancelledCallNeverRunsAtHead : Properties.CancelledCallNeverRunsAtHead := by
  intro s txs h i hc hx
  have g := submitAll_good s txs
  obtain ⟨_, hr⟩ := g.calls hc
  have hcan : (submitAll s txs).1.call h i = .Cancelled :=
    callReach_from_cancelled (hx ▸ hr h i)
  refine ⟨hcan, fun hm => ?_, fun hm => ?_⟩
  · have hrec := g.recorded _ hm
    simp only [InteropHandler.Recorded] at hrec
    rw [hcan] at hrec
    cases hrec
  · have hfresh := g.fresh _ hm
    have hsp := g.spent _ hm
    simp only [Spent] at hfresh hsp
    have hub : s.bundle h = .Unbundled :=
      (hc h i (by rw [hx]; simp)).resolve_left hfresh
    have hend : (submitAll s txs).1.bundle h = .Unbundled :=
      reach_from_unbundled (hub ▸ g.reach h)
    rw [hend] at hsp
    cases hsp

theorem AtomicBundleCanBePartlyExecutedForGoodAtHead :
    Properties.AtomicBundleCanBePartlyExecutedForGoodAtHead := by
  intro s b txs hc hu hn
  have hrun := submitAll_partialRun hc hu hn
  have hc' : CallsClosed (submitAll s (partialRun b)).1 :=
    (NestedExecutionFollowsTheStatusMachineAtHead.2 s (partialRun b) hc).1
  have hcan : (submitAll s (partialRun b)).1.call b.hash 1 = .Cancelled := by
    rw [hrun]; simp
  obtain ⟨_, hnd, hne⟩ :=
    CancelledCallNeverRunsAtHead (submitAll s (partialRun b)).1 txs b.hash 1 hc' hcan
  refine ⟨by rw [hrun], by rw [hrun]; simp, by rw [hrun]; simp, hcan, ?_, ?_⟩
  · rw [submitAll_append, effects_append]
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · rw [hrun] at hm
      simp at hm
    · exact hnd hm
  · rw [submitAll_append, effects_append]
    intro hm
    rcases List.mem_append.1 hm with hm | hm
    · rw [hrun] at hm
      simp at hm
    · exact hne hm

theorem PartialExecutionWitnessAtHead : Properties.PartialExecutionWitnessAtHead := by
  refine ⟨NestedExecutionFollowsTheStatusMachineAtHead.1, ?_⟩
  decide

theorem HeadStatusesLeaveThePinnedAtomicSubMachine :
    Properties.HeadStatusesLeaveThePinnedAtomicSubMachine := by
  refine ⟨fun h => ?_, atomic_never_unbundled, fun s b hc hu => ⟨?_, fun hn => ?_⟩⟩
  · rcases atomic_reach_two_states h with h1 | h1 <;> cases h1
  · rw [submit_verify hu]; simp
  · rw [submitAll_partialRun hc hu hn]; simp

/-! ## Every delivery follows the flow gate -/

/-- Every delivery in `l` is of a bundle hash satisfying `ok`, or follows a gate event for its hash
in `l`. -/
def DeliveriesGated (ok : BundleHash → Prop) (l : List Event) : Prop :=
  ∀ (l₁ l₂ : List Event) (h : BundleHash) (i : ℕ),
    l = l₁ ++ .effect (.delivered h i) :: l₂ → ok h ∨ GatePassed h l₁

lemma GatePassed.append_left {h : BundleHash} {l₁ : List Event} (l₂ : List Event)
    (g : GatePassed h l₁) : GatePassed h (l₁ ++ l₂) :=
  g.imp (List.mem_append_left _) (List.mem_append_left _)

lemma GatePassed.append_right {h : BundleHash} {l₂ : List Event} (l₁ : List Event)
    (g : GatePassed h l₂) : GatePassed h (l₁ ++ l₂) :=
  g.imp (List.mem_append_right _) (List.mem_append_right _)

lemma DeliveriesGated.of_no_delivery {ok : BundleHash → Prop} {l : List Event}
    (hl : ∀ h i, Event.effect (.delivered h i) ∉ l) : DeliveriesGated ok l := by
  intro l₁ l₂ h i he
  refine absurd ?_ (hl h i)
  rw [he]
  exact List.mem_append_right _ List.mem_cons_self

lemma DeliveriesGated.mono {ok ok' : BundleHash → Prop} {l : List Event}
    (g : DeliveriesGated ok l) (hok : ∀ x, ok x → ok' x) : DeliveriesGated ok' l :=
  fun l₁ l₂ x i he => (g l₁ l₂ x i he).imp_left (hok x)

lemma DeliveriesGated.append {ok : BundleHash → Prop} {la lb : List Event}
    (ga : DeliveriesGated ok la)
    (gb : DeliveriesGated (fun h => ok h ∨ GatePassed h la) lb) :
    DeliveriesGated ok (la ++ lb) := by
  intro l₁ l₂ h i he
  rcases List.append_eq_append_iff.1 he with ⟨a', rfl, hb⟩ | ⟨c', hla, hc⟩
  · rcases gb a' l₂ h i hb with (hok | hg) | hg
    · exact Or.inl hok
    · exact Or.inr (hg.append_left _)
    · exact Or.inr (hg.append_right _)
  · cases c' with
    | nil =>
      simp only [List.append_nil] at hla
      subst hla
      simp only [List.nil_append] at hc
      rcases gb [] l₂ h i hc.symm with (hok | hg) | hg
      · exact Or.inl hok
      · exact Or.inr hg
      · exact absurd hg (by simp [GatePassed])
    | cons x c'' =>
      simp only [List.cons_append, List.cons.injEq] at hc
      obtain ⟨rfl, rfl⟩ := hc
      exact ga l₁ c'' h i hla

lemma DeliveriesGated.cons_delivered {ok : BundleHash → Prop} {h : BundleHash} {i : ℕ}
    {l : List Event} (hok : ok h) (g : DeliveriesGated ok l) :
    DeliveriesGated ok (.effect (.delivered h i) :: l) := by
  have hone : DeliveriesGated ok [Event.effect (.delivered h i)] := by
    intro l₁ l₂ h' i' he
    cases l₁ with
    | nil =>
      simp only [List.nil_append] at he
      injection he with h1 _
      cases h1
      exact Or.inl hok
    | cons x l₁ => simp at he
  exact hone.append (g.mono fun _ => Or.inl)

/-- What every committed frame of an entry point or a target satisfies, from `s` to `s'` committing
`l`: a hash that is not `Unreceived` stays so; a hash leaves `Unreceived` only with a gate event in
`l`; and each delivery in `l` is of a hash that was not `Unreceived` in `s` or follows a gate event
for it. -/
structure Gated (s s' : State) (l : List Event) : Prop where
  stays : ∀ h, s.bundle h ≠ .Unreceived → s'.bundle h ≠ .Unreceived
  left : ∀ h, s'.bundle h ≠ .Unreceived → s.bundle h ≠ .Unreceived ∨ GatePassed h l
  gated : DeliveriesGated (fun h => s.bundle h ≠ .Unreceived) l

/-- A frame that changes no status and delivers nothing. -/
lemma Gated.log_only {s : State} {l : List Event}
    (hl : ∀ h i, Event.effect (.delivered h i) ∉ l) : Gated s s l :=
  ⟨fun _ h => h, fun _ h => Or.inl h, .of_no_delivery hl⟩

lemma Gated.refl (s : State) : Gated s s [] := .log_only (by simp)

lemma Gated.append {s s₁ s₂ : State} {l₁ l₂ : List Event} (g₁ : Gated s s₁ l₁)
    (g₂ : Gated s₁ s₂ l₂) : Gated s s₂ (l₁ ++ l₂) where
  stays h hh := g₂.stays h (g₁.stays h hh)
  left h hh := by
    rcases g₂.left h hh with h1 | h1
    · rcases g₁.left h h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (h2.append_left _)
    · exact Or.inr (h1.append_right _)
  gated := g₁.gated.append (g₂.gated.mono fun h hh => g₁.left h hh)

lemma Gated.cons_delivered {s s' : State} {h : BundleHash} {i : ℕ} {l : List Event}
    (hh : s.bundle h ≠ .Unreceived) (g : Gated s s' l) :
    Gated s s' (.effect (.delivered h i) :: l) where
  stays := g.stays
  left h' hh' := (g.left h' hh').imp_right fun gp =>
    gp.imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
  gated := g.gated.cons_delivered hh

/-- `verifyAtomicBundle`. -/
lemma gated_verify (s : State) (h : BundleHash) :
    Gated s (s.setBundle h .Verified) [.verified h] where
  stays h' hh := by
    by_cases e : h' = h <;> simp [e, hh]
  left h' hh := by
    by_cases e : h' = h
    · subst e
      exact Or.inr (Or.inr (by simp))
    · exact Or.inl (by simpa [e] using hh)
  gated := .of_no_delivery (by simp)

/-- `executeAtomicBundle`'s gate and its writes before the calls. -/
lemma gated_mark {s : State} {b : Bundle}
    (hG : s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unreceived) :
    Gated s (markFullyExecuted b s) (gateLog s b.hash) where
  stays h hh := by
    by_cases e : h = b.hash <;> simp [markFullyExecuted, e, hh]
  left h hh := by
    by_cases e : h = b.hash
    · subst e
      rcases hG with hv | hu
      · exact Or.inl (by simp [hv])
      · exact Or.inr (Or.inl (by simp [gateLog, hu]))
    · exact Or.inl (by simpa [markFullyExecuted, e] using hh)
  gated := .of_no_delivery (by
    intro h i
    unfold gateLog
    split_ifs <;> simp)

/-- `unbundleBundle`'s status write and first loop. -/
lemma gated_unbundle_pre {s s₁ : State} {b : Bundle}
    (hG : s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled)
    (hb : s₁.bundle = (s.setBundle b.hash .Unbundled).bundle) : Gated s s₁ [] where
  stays h hh := by
    rw [hb]
    by_cases e : h = b.hash <;> simp [e, hh]
  left h hh := by
    by_cases e : h = b.hash
    · subst e
      rcases hG with hv | hv <;> exact Or.inl (by simp [hv])
    · rw [hb] at hh
      exact Or.inl (by simpa [e] using hh)
  gated := .of_no_delivery (by simp)

/-- The invariant a frame of each kind satisfies: a call loop once its own bundle has left
`Unreceived`. -/
def FrameGated : Frame → State → State → List Event → Prop
  | .entry _ _, s, s', l => Gated s s' l
  | .calls h _ _, s, s', l => s.bundle h ≠ .Unreceived → Gated s s' l
  | .target _, s, s', l => Gated s s' l

/-- **The gate invariant.** Every frame that commits, at every budget, is `Gated`. -/
theorem exec_gated : ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Event),
    exec n f s = some (s', l) → FrameGated f s s' l := by
  intro n
  induction n with
  | zero => intro f s s' l h; simp [exec] at h
  | succ n ih =>
    intro f s s' l h
    match f with
    | .entry (.executeAtomicBundle b ok) cs =>
      simp only [exec] at h
      split_ifs at h with hG
      split at h
      · rename_i s₂ l₂ heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have g₁ := gated_mark (b := b) (hG.imp_right And.left)
        have g₂ : Gated (markFullyExecuted b s) s₂ l₂ :=
          ih _ _ _ _ heq (by simp [markFullyExecuted])
        exact (g₁.append g₂).append (Gated.log_only (by simp))
      · simp at h
    | .entry (.verifyAtomicBundle b ok) cs =>
      simp only [exec] at h
      split_ifs at h with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact gated_verify s b.hash
    | .entry (.unbundleBundle b req) cs =>
      simp only [exec] at h
      split_ifs at h with hG
      split at h
      · rename_i s₁ hm
        have hb := (InteropHandler.markCalls_spec req 0 _ s₁ hm).1
        have g₁ := gated_unbundle_pre (b := b) hG.2 hb
        have g₂ : Gated s₁ s' l := ih _ _ _ _ h (by rw [hb]; simp)
        exact g₁.append g₂
      · simp at h
    | .calls hb [] cs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun _ => Gated.refl s
    | .calls hb (i :: is) cs =>
      simp only [exec] at h
      split at h
      · rename_i s₁ l₁ heq₁
        split at h
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          show s.bundle hb ≠ .Unreceived → Gated _ _ _
          intro hh
          have g₁ : Gated s s₁ l₁ := ih _ _ _ _ heq₁
          have g₂ : Gated s₁ s₂ l₂ := ih _ _ _ _ heq₂ (g₁.stays _ hh)
          exact (g₁.append g₂).cons_delivered hh
        · simp at h
      · simp at h
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Gated.refl s
    | .target .reverts => simp [exec] at h
    | .target (.calls e inner caught next) =>
      simp only [exec] at h
      split at h
      · rename_i s₁ l₁ heq₁
        split at h
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have g₁ : Gated s s₁ l₁ := ih _ _ _ _ heq₁
          have g₂ : Gated s₁ s₂ l₂ := ih _ _ _ _ heq₂
          exact g₁.append g₂
        · simp at h
      · split_ifs at h
        exact (ih (.target next) s s' l h : Gated s s' l)

lemma submit_gated (s : State) (t : Tx) : Gated s (submit s t).1 (submit s t).2 := by
  unfold submit
  cases hx : exec t.fuel (.entry t.entry t.callees) s with
  | none => exact Gated.refl s
  | some r =>
    obtain ⟨s', l⟩ := r
    exact exec_gated _ _ _ _ _ hx

lemma submitAll_gated : ∀ (s : State) (txs : List Tx),
    Gated s (submitAll s txs).1 (submitAll s txs).2
  | s, [] => Gated.refl s
  | s, t :: ts => (submit_gated s t).append (submitAll_gated _ ts)

theorem EveryDeliveryFollowsTheFlowGateAtHead :
    Properties.EveryDeliveryFollowsTheFlowGateAtHead := by
  intro s txs h i l₁ l₂ hu hl
  rcases (submitAll_gated s txs).gated l₁ l₂ h i hl with hne | hg
  · exact absurd hu hne
  · exact hg

theorem FailingFlowGateRefusesAnUnverifiedBundleAtHead :
    Properties.FailingFlowGateRefusesAnUnverifiedBundleAtHead := by
  intro n b cs s
  refine ⟨?_, fun hv => ?_⟩
  · cases n <;> simp [exec]
  · cases n <;> simp [exec, hv]

/-! ## Partial execution needs `verifyAtomicBundle` -/

/-- The unbundled route is open for `h`: it is `Verified` or `Unbundled`. -/
def Opened (s : State) (h : BundleHash) : Prop :=
  s.bundle h = .Verified ∨ s.bundle h = .Unbundled

/-- What every committed frame satisfies, from `s` to `s'` committing `l`, where `own` holds of the
hash of the call loop the frame is (and of none for an entry point or a target): a hash is `Opened`
only if it was or `verifyAtomicBundle`'s event for it is in `l`; and each delivery in `l` is the
loop's own, or of a hash that was `Opened` in `s`, or of one whose `verifyAtomicBundle` event or
`BundleExecuted` is in `l`. -/
structure Routed (own : BundleHash → Prop) (s s' : State) (l : List Event) : Prop where
  opened : ∀ h, Opened s' h → Opened s h ∨ Event.verified h ∈ l
  whole : ∀ h i, Event.effect (.delivered h i) ∈ l →
    own h ∨ Opened s h ∨ Event.verified h ∈ l ∨ Event.effect (.executed h) ∈ l

lemma Routed.refl (own : BundleHash → Prop) (s : State) : Routed own s s [] :=
  ⟨fun _ h => Or.inl h, fun _ _ h => by simp at h⟩

lemma Routed.mono {own own' : BundleHash → Prop} {s s' : State} {l : List Event}
    (g : Routed own s s' l) (ho : ∀ x, own x → own' x) : Routed own' s s' l :=
  ⟨g.opened, fun h i hm => (g.whole h i hm).imp_left (ho h)⟩

lemma Routed.append {own : BundleHash → Prop} {s s₁ s₂ : State} {l₁ l₂ : List Event}
    (g₁ : Routed own s s₁ l₁) (g₂ : Routed own s₁ s₂ l₂) : Routed own s s₂ (l₁ ++ l₂) where
  opened h hh := by
    rcases g₂.opened h hh with h1 | h1
    · rcases g₁.opened h h1 with h2 | h2
      · exact Or.inl h2
      · exact Or.inr (List.mem_append_left _ h2)
    · exact Or.inr (List.mem_append_right _ h1)
  whole h i hm := by
    rcases List.mem_append.1 hm with hm | hm
    · rcases g₁.whole h i hm with a | a | a | a
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ a)))
      · exact Or.inr (Or.inr (Or.inr (List.mem_append_left _ a)))
    · rcases g₂.whole h i hm with a | a | a | a
      · exact Or.inl a
      · rcases g₁.opened h a with a' | a'
        · exact Or.inr (Or.inl a')
        · exact Or.inr (Or.inr (Or.inl (List.mem_append_left _ a')))
      · exact Or.inr (Or.inr (Or.inl (List.mem_append_right _ a)))
      · exact Or.inr (Or.inr (Or.inr (List.mem_append_right _ a)))

lemma Routed.cons_own {own : BundleHash → Prop} {s s' : State} {h : BundleHash} {i : ℕ}
    {l : List Event} (ho : own h) (g : Routed own s s' l) :
    Routed own s s' (.effect (.delivered h i) :: l) where
  opened h' hh := (g.opened h' hh).imp_right (List.mem_cons_of_mem _)
  whole h' i' hm := by
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      exact Or.inl ho
    · rcases g.whole h' i' hm with a | a | a | a
      · exact Or.inl a
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr (Or.inl (List.mem_cons_of_mem _ a)))
      · exact Or.inr (Or.inr (Or.inr (List.mem_cons_of_mem _ a)))

lemma opened_of_mark {b : Bundle} {s : State} {h : BundleHash}
    (hh : Opened (markFullyExecuted b s) h) : Opened s h := by
  by_cases e : h = b.hash
  · subst e
    simp [Opened, markFullyExecuted] at hh
  · simpa [Opened, markFullyExecuted, e] using hh

lemma eq_gated_of_mem_gateLog {s : State} {h : BundleHash} {x : Event}
    (hx : x ∈ gateLog s h) : x = .gated h := by
  unfold gateLog at hx
  split_ifs at hx
  · simp at hx
  · simpa using hx

/-- `executeAtomicBundle`, from its call loop. -/
lemma routed_execute {b : Bundle} {s s₂ : State} {l₂ : List Event}
    (g : Routed (· = b.hash) (markFullyExecuted b s) s₂ l₂) :
    Routed (fun _ => False) s s₂
      (gateLog s b.hash ++ l₂ ++ [.effect (.executed b.hash)]) where
  opened h hh := by
    rcases g.opened h hh with h1 | h1
    · exact Or.inl (opened_of_mark h1)
    · exact Or.inr (List.mem_append_left _ (List.mem_append_right _ h1))
  whole h i hm := by
    have hin : Event.effect (.delivered h i) ∈ l₂ := by
      rcases List.mem_append.1 hm with hm | hm
      · rcases List.mem_append.1 hm with hm | hm
        · cases eq_gated_of_mem_gateLog hm
        · exact hm
      · simp at hm
    rcases g.whole h i hin with a | a | a | a
    · subst a
      exact Or.inr (Or.inr (Or.inr (List.mem_append_right _ List.mem_cons_self)))
    · exact Or.inr (Or.inl (opened_of_mark a))
    · exact Or.inr (Or.inr (Or.inl
        (List.mem_append_left _ (List.mem_append_right _ a))))
    · exact Or.inr (Or.inr (Or.inr
        (List.mem_append_left _ (List.mem_append_right _ a))))

/-- `verifyAtomicBundle`. -/
lemma routed_verify (s : State) (h : BundleHash) :
    Routed (fun _ => False) s (s.setBundle h .Verified) [.verified h] where
  opened h' hh := by
    by_cases e : h' = h
    · subst e
      exact Or.inr (by simp)
    · exact Or.inl (by simpa [Opened, e] using hh)
  whole h' i hm := by simp at hm

/-- `unbundleBundle`, from its call loop. -/
lemma routed_unbundle {b : Bundle} {s s₁ s₂ : State} {l : List Event}
    (hG : s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled)
    (hb : s₁.bundle = (s.setBundle b.hash .Unbundled).bundle)
    (g : Routed (· = b.hash) s₁ s₂ l) : Routed (fun _ => False) s s₂ l := by
  have hopen : ∀ h, Opened s₁ h → Opened s h := by
    intro h hh
    by_cases e : h = b.hash
    · subst e
      exact hG
    · simpa [Opened, hb, e] using hh
  refine ⟨fun h hh => (g.opened h hh).imp_left (hopen h), fun h i hm => ?_⟩
  rcases g.whole h i hm with a | a | a | a
  · subst a
    exact Or.inr (Or.inl hG)
  · exact Or.inr (Or.inl (hopen h a))
  · exact Or.inr (Or.inr (Or.inl a))
  · exact Or.inr (Or.inr (Or.inr a))

/-- The invariant a frame of each kind satisfies. -/
def FrameRouted : Frame → State → State → List Event → Prop
  | .entry _ _, s, s', l => Routed (fun _ => False) s s' l
  | .calls h _ _, s, s', l => Routed (· = h) s s' l
  | .target _, s, s', l => Routed (fun _ => False) s s' l

/-- **The route invariant.** Every frame that commits, at every budget, is `Routed`. -/
theorem exec_routed : ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Event),
    exec n f s = some (s', l) → FrameRouted f s s' l := by
  intro n
  induction n with
  | zero => intro f s s' l h; simp [exec] at h
  | succ n ih =>
    intro f s s' l h
    match f with
    | .entry (.executeAtomicBundle b ok) cs =>
      simp only [exec] at h
      split_ifs at h with hG
      split at h
      · rename_i s₂ l₂ heq
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact routed_execute (ih _ _ _ _ heq)
      · simp at h
    | .entry (.verifyAtomicBundle b ok) cs =>
      simp only [exec] at h
      split_ifs at h with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact routed_verify s b.hash
    | .entry (.unbundleBundle b req) cs =>
      simp only [exec] at h
      split_ifs at h with hG
      split at h
      · rename_i s₁ hm
        exact routed_unbundle hG.2 (InteropHandler.markCalls_spec req 0 _ s₁ hm).1
          (ih _ _ _ _ h)
      · simp at h
    | .calls hb [] cs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Routed.refl _ s
    | .calls hb (i :: is) cs =>
      simp only [exec] at h
      split at h
      · rename_i s₁ l₁ heq₁
        split at h
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have g₁ : Routed (fun _ => False) s s₁ l₁ := ih _ _ _ _ heq₁
          have g₂ : Routed (· = hb) s₁ s₂ l₂ := ih _ _ _ _ heq₂
          exact ((g₁.mono fun _ hf => hf.elim).append g₂).cons_own rfl
        · simp at h
      · simp at h
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Routed.refl _ s
    | .target .reverts => simp [exec] at h
    | .target (.calls e inner caught next) =>
      simp only [exec] at h
      split at h
      · rename_i s₁ l₁ heq₁
        split at h
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have g₁ : Routed (fun _ => False) s s₁ l₁ := ih _ _ _ _ heq₁
          have g₂ : Routed (fun _ => False) s₁ s₂ l₂ := ih _ _ _ _ heq₂
          exact g₁.append g₂
        · simp at h
      · split_ifs at h
        exact (ih (.target next) s s' l h : Routed (fun _ => False) s s' l)

lemma submit_routed (s : State) (t : Tx) :
    Routed (fun _ => False) s (submit s t).1 (submit s t).2 := by
  unfold submit
  cases hx : exec t.fuel (.entry t.entry t.callees) s with
  | none => exact Routed.refl _ s
  | some r =>
    obtain ⟨s', l⟩ := r
    exact exec_routed _ _ _ _ _ hx

lemma submitAll_routed : ∀ (s : State) (txs : List Tx),
    Routed (fun _ => False) s (submitAll s txs).1 (submitAll s txs).2
  | s, [] => Routed.refl _ s
  | s, t :: ts => (submit_routed s t).append (submitAll_routed _ ts)

theorem PartialExecutionNeedsVerifyAtomicBundleAtHead :
    Properties.PartialExecutionNeedsVerifyAtomicBundleAtHead := by
  intro s txs h i hu hm
  rcases (submitAll_routed s txs).whole h i hm with a | a | a | a
  · exact a.elim
  · rcases a with a | a <;> rw [hu] at a <;> cases a
  · exact Or.inl a
  · exact Or.inr a

/-! ## Who may unbundle -/

theorem DefaultUnbundlerUsesTheRescuePathAtHead :
    Properties.DefaultUnbundlerUsesTheRescuePathAtHead := by
  intro here self caller source sender hne h0
  refine ⟨?_, fun m => ?_, fun r => ?_⟩
  · simp only [DirectUnbundleAllowed, defaultUnbundler]
    constructor
    · rintro (h | ⟨h | h, _⟩)
      · exact h
      · exact absurd h hne
      · exact absurd h h0
    · exact Or.inl
  · obtain ⟨c, a⟩ := m
    simp only [RescueUnbundleAllowed, defaultUnbundler, InteropAddress.mk.injEq]
    constructor
    · rintro ⟨h | h, h'⟩
      · exact ⟨h.symm, h'.symm⟩
      · exact absurd h h0
    · rintro ⟨rfl, rfl⟩
      exact ⟨Or.inl rfl, rfl⟩
  · simp only [DirectUnbundleAllowed]
    constructor
    · rintro (h | ⟨_, h⟩)
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | h)
      · exact Or.inl h
      · exact Or.inr ⟨Or.inl trivial, h.symm⟩

theorem DefaultUnbundlerWitnessAtHead : Properties.DefaultUnbundlerWitnessAtHead := by
  simp [Properties.DefaultUnbundlerWitnessAtHead, DirectUnbundleAllowed, RescueUnbundleAllowed,
    defaultUnbundler]

end Contracts.InteropHandlerAtHead
