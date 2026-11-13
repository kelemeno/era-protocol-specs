import EraSpec.Contracts.InteropHandlerBase.Properties.BundleStatusMachineFaithful
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachine
import EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy
import Mathlib.Tactic

/-!
# Proofs: the never-published premise is what keeps the atomicity gate unbypassable

(a) is by induction on labelled paths. (b) rests on two frame invariants proved, like
`Reentrancy.exec_good`, by induction on the budget, for every frame whose entry-point calls all
satisfy a predicate (`FrameAll`):

* `exec_untouched`: with no accepted inclusion proof and no passing flow gate for `h`, a committed
  frame leaves an `Unreceived` hash `h` `Unreceived` and commits no effect of it;
* `exec_atomicStates`: with no accepted inclusion proof for `h`, a committed frame keeps `h` in
  `Unreceived` or `FullyExecuted`.

Both lift to transactions through `commit`, which either commits a frame or changes nothing. The
countermodels evaluate the deployed `exec` symbolically, on any bundle, with `exec_calls_returns`.
-/

namespace AttackVectors.BundleStatusMachine.Faithful

theorem lstep_refines_step : Properties.lstep_refines_step := by
  intro s t
  constructor
  · intro h
    cases h
    · exact ⟨_, _, .verify⟩
    · exact ⟨_, _, .executeFresh⟩
    · exact ⟨_, _, .executeVerified⟩
    · exact ⟨_, _, .unbundleFirst⟩
    · exact ⟨_, _, .unbundleAgain⟩
    · exact ⟨_, _, .executeAtomic⟩
  · rintro ⟨e, c, h⟩
    cases h
    · exact .verify
    · exact .executeFresh
    · exact .executeVerified
    · exact .unbundleFirst
    · exact .unbundleAgain
    · exact .executeAtomic

theorem atomic_entry_needs_unreceived : Properties.atomic_entry_needs_unreceived := by
  intro s t c h
  cases h
  rfl

theorem verified_runs_unchecked : Properties.verified_runs_unchecked :=
  ⟨.executeVerified, .unbundleFirst⟩

/-- Along a labelled path from `Unreceived`, either the bundle is still `Unreceived`, or an inclusion
proof or the flow gate was consulted. -/
lemma lreach_from_unreceived {a t : Status} {cs : List Check} (h : LReach a cs t) :
    a = .Unreceived → t = .Unreceived ∨ Check.inclusionProof ∈ cs ∨ Check.flowGate ∈ cs := by
  induction h with
  | refl => exact Or.inl
  | tail _ hs ih =>
    intro ha
    rcases ih ha with hb | hin | hin
    · subst hb
      cases hs <;> simp
    · exact Or.inr (Or.inl (List.mem_append_left _ hin))
    · exact Or.inr (Or.inr (List.mem_append_left _ hin))

theorem route_consults_inclusion_or_flowGate :
    Properties.route_consults_inclusion_or_flowGate := by
  intro cs t h ht
  rcases lreach_from_unreceived h rfl with hu | hin
  · subst hu
    rcases ht with h' | h' <;> exact absurd h' (by decide)
  · exact hin

/-- A labelled path from `Unreceived` consulting no inclusion proof stays inside `AtomicReach`. -/
lemma lreach_no_inclusion {a t : Status} {cs : List Check} (h : LReach a cs t) :
    a = .Unreceived → Check.inclusionProof ∉ cs → AtomicReach .Unreceived t := by
  induction h with
  | refl => intro ha _; subst ha; exact .refl _
  | @tail b d cs e c _ hs ih =>
    intro ha hno
    have hno₁ : Check.inclusionProof ∉ cs := fun hm => hno (List.mem_append_left _ hm)
    have hc : c ≠ Check.inclusionProof := fun hc => hno (by simp [hc])
    have hb := ih ha hno₁
    rcases AttackVectors.BundleStatusMachine.atomic_reach_two_states hb with hb' | hb'
    · subst hb'
      cases hs with
      | verify => exact absurd rfl hc
      | executeFresh => exact absurd rfl hc
      | executeAtomic => exact .tail hb .executeAtomic
    · subst hb'
      cases hs

theorem no_inclusion_paths_are_atomic : Properties.no_inclusion_paths_are_atomic :=
  fun _ _ h hno => lreach_no_inclusion h rfl hno

theorem inclusion_routes_skip_flowGate : Properties.inclusion_routes_skip_flowGate := by
  have h₁ : LReach .Unreceived ([] ++ [Check.inclusionProof]) .FullyExecuted :=
    .tail (.refl _) .executeFresh
  have h₂ : LReach .Unreceived ([] ++ [Check.inclusionProof] ++ [Check.noCheck]) .FullyExecuted :=
    .tail (.tail (.refl _) .verify) .executeVerified
  have h₃ : LReach .Unreceived ([] ++ [Check.inclusionProof] ++ [Check.noCheck]) .Unbundled :=
    .tail (.tail (.refl _) .verify) .unbundleFirst
  exact ⟨h₁, h₂, h₃⟩

end AttackVectors.BundleStatusMachine.Faithful

namespace Contracts.InteropHandler.Faithful

open AttackVectors.BundleStatusMachine

/-! ## Predicates on call trees -/

/-- Every entry-point call a frame makes or contains satisfies `P`. -/
def FrameAll (P : Entry → Prop) : Frame → Prop
  | .entry e cs => P e ∧ ∀ c ∈ cs, CalleeAll P c
  | .calls _ _ cs => ∀ c ∈ cs, CalleeAll P c
  | .target c => CalleeAll P c

lemma CalleeAll.and {P Q : Entry → Prop} {c : Callee} (hp : CalleeAll P c) :
    CalleeAll Q c → CalleeAll (fun e => P e ∧ Q e) c := by
  induction hp with
  | returns => intro _; exact .returns
  | reverts => intro _; exact .reverts
  | calls hpe _ _ ihi ihn =>
    intro hq
    cases hq with
    | calls hqe hqi hqn => exact .calls ⟨hpe, hqe⟩ (fun c hc => ihi c hc (hqi c hc)) (ihn hqn)

lemma TxAll.and {P Q : Entry → Prop} {t : Tx} (hp : TxAll P t) (hq : TxAll Q t) :
    TxAll (fun e => P e ∧ Q e) t :=
  ⟨⟨hp.1, hq.1⟩, fun c hc => (hp.2 c hc).and (hq.2 c hc)⟩

lemma calleeAll_headD {P : Entry → Prop} {cs : List Callee} (h : ∀ c ∈ cs, CalleeAll P c) :
    CalleeAll P (cs.headD .returns) := by
  cases cs with
  | nil => exact .returns
  | cons c cs => exact h c List.mem_cons_self

lemma calleeAll_tail {P : Entry → Prop} {cs : List Callee} (h : ∀ c ∈ cs, CalleeAll P c) :
    ∀ c ∈ cs.tail, CalleeAll P c :=
  fun c hc => h c (List.mem_of_mem_tail hc)

/-- `_verifyBundle`'s status write touches only its own bundle. -/
lemma verifyIfUnreceived_bundle_ne {s : State} {h h' : BundleHash} (hne : h' ≠ h) :
    (s.verifyIfUnreceived h).bundle h' = s.bundle h' := by
  unfold State.verifyIfUnreceived
  split_ifs <;> simp [hne]

lemma verifyIfUnreceived_call (s : State) (h : BundleHash) :
    (s.verifyIfUnreceived h).call = s.call := by
  unfold State.verifyIfUnreceived
  split_ifs <;> rfl

/-! ## (b) The two frame invariants -/

/-- **No accepted inclusion proof and no passing flow gate for `h`: nothing of `h` happens.** -/
theorem exec_untouched (h : BundleHash) : ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
    exec .deployed n f s = some (s', l) →
    FrameAll (fun e => ¬ ProvesInclusion h e ∧ ¬ PassesFlowGate h e) f →
    (∀ h' is cs, f = .calls h' is cs → h' ≠ h) →
    s.bundle h = .Unreceived →
    s'.bundle h = .Unreceived ∧ ∀ e ∈ l, e.bundleHash ≠ h := by
  intro n
  induction n with
  | zero => intro f s s' l hx; simp [exec] at hx
  | succ n ih =>
    intro f s s' l hx hf hloop hu
    match f with
    | .entry (.executeBundle b ok) cs =>
      obtain ⟨⟨hpi, -⟩, hcs⟩ := hf
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        by_cases hb : b.hash = h
        · exfalso
          rcases hG with hv | ⟨_, hok⟩
          · rw [hb, hu] at hv; exact absurd hv (by decide)
          · exact hpi ⟨hb, hok⟩
        · have hu' : (beforeCalls .deployed b (s.verifyIfUnreceived b.hash)).bundle h =
              .Unreceived := by
            simp [Ne.symm hb, verifyIfUnreceived_bundle_ne (Ne.symm hb), hu]
          obtain ⟨h1, h2⟩ :=
            ih _ _ _ _ heq hcs (fun h' is cs' he => by cases he; exact hb) hu'
          refine ⟨h1, fun e he => ?_⟩
          rcases List.mem_append.1 he with he | he
          · exact h2 e he
          · rw [List.mem_singleton] at he; subst he; exact hb
      · simp at hx
    | .entry (.executeAtomicBundle b ok) cs =>
      obtain ⟨⟨-, hpf⟩, hcs⟩ := hf
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        by_cases hb : b.hash = h
        · exact absurd ⟨hb, hG.2⟩ hpf
        · have hu' : (beforeCalls .deployed b s).bundle h = .Unreceived := by
            simp [Ne.symm hb, hu]
          obtain ⟨h1, h2⟩ :=
            ih _ _ _ _ heq hcs (fun h' is cs' he => by cases he; exact hb) hu'
          refine ⟨h1, fun e he => ?_⟩
          rcases List.mem_append.1 he with he | he
          · exact h2 e he
          · rw [List.mem_singleton] at he; subst he; exact hb
      · simp at hx
    | .entry (.verifyBundle b ok) cs =>
      obtain ⟨⟨hpi, -⟩, -⟩ := hf
      simp only [exec] at hx
      split_ifs at hx with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      by_cases hb : b.hash = h
      · exact absurd ⟨hb, hG.2⟩ hpi
      · exact ⟨by simp [Ne.symm hb, hu], by simp⟩
    | .entry (.unbundleBundle b req) cs =>
      obtain ⟨-, hcs⟩ := hf
      simp only [exec, writesCallsFirst_deployed] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₁ hm
        split at hx
        · rename_i s₂ l₂ heq
          simp only [afterUnbundle_deployed, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          by_cases hb : b.hash = h
          · exfalso
            rw [hb, hu] at hG
            rcases hG.2 with h' | h' <;> exact absurd h' (by decide)
          · obtain ⟨hmb, -, -, -⟩ := markCalls_spec req 0 _ s₁ hm
            have hu₁ : s₁.bundle h = .Unreceived := by
              rw [hmb]; simp [Ne.symm hb, hu]
            exact ih _ _ _ _ heq hcs (fun h' is cs' he => by cases he; exact hb) hu₁
        · simp at hx
      · simp at hx
    | .calls hb [] cs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨hu, by simp⟩
    | .calls hb (i :: is) cs =>
      have hne : hb ≠ h := hloop hb (i :: is) cs rfl
      simp only [exec] at hx
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          obtain ⟨h1, h2⟩ := ih _ _ _ _ heq₁ (calleeAll_headD hf) (fun _ _ _ he => by cases he) hu
          obtain ⟨h3, h4⟩ := ih _ _ _ _ heq₂ (calleeAll_tail hf)
            (fun h' is' cs' he => by cases he; exact hne) h1
          refine ⟨h3, fun e he => ?_⟩
          rcases List.mem_cons.1 he with rfl | he
          · exact hne
          rcases List.mem_append.1 he with he | he
          · exact h2 e he
          · exact h4 e he
        · simp at hx
      · simp at hx
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact ⟨hu, by simp⟩
    | .target .reverts => simp [exec] at hx
    | .target (.calls e inner caught next) =>
      cases hf with
      | calls hpe hinner hnext =>
        simp only [exec] at hx
        split at hx
        · rename_i s₁ l₁ heq₁
          split at hx
          · rename_i s₂ l₂ heq₂
            simp only [Option.some.injEq, Prod.mk.injEq] at hx
            obtain ⟨rfl, rfl⟩ := hx
            obtain ⟨h1, h2⟩ := ih _ _ _ _ heq₁ ⟨hpe, hinner⟩ (fun _ _ _ he => by cases he) hu
            obtain ⟨h3, h4⟩ := ih _ _ _ _ heq₂ hnext (fun _ _ _ he => by cases he) h1
            refine ⟨h3, fun e he => ?_⟩
            rcases List.mem_append.1 he with he | he
            · exact h2 e he
            · exact h4 e he
          · simp at hx
        · split_ifs at hx
          exact ih _ _ _ _ hx hnext (fun _ _ _ he => by cases he) hu

/-- **No accepted inclusion proof for `h`: `h` stays in `Unreceived` or `FullyExecuted`.** -/
theorem exec_atomicStates (h : BundleHash) : ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
    exec .deployed n f s = some (s', l) →
    FrameAll (fun e => ¬ ProvesInclusion h e) f →
    (s.bundle h = .Unreceived ∨ s.bundle h = .FullyExecuted) →
    s'.bundle h = .Unreceived ∨ s'.bundle h = .FullyExecuted := by
  intro n
  induction n with
  | zero => intro f s s' l hx; simp [exec] at hx
  | succ n ih =>
    intro f s s' l hx hf hs
    match f with
    | .entry (.executeBundle b ok) cs =>
      obtain ⟨hpi, hcs⟩ := hf
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        by_cases hb : b.hash = h
        · exfalso
          rcases hG with hv | ⟨_, hok⟩
          · rw [hb] at hv
            rcases hs with h' | h' <;> rw [h'] at hv <;> exact absurd hv (by decide)
          · exact hpi ⟨hb, hok⟩
        · have hs' : (beforeCalls .deployed b (s.verifyIfUnreceived b.hash)).bundle h =
              s.bundle h := by
            simp [Ne.symm hb, verifyIfUnreceived_bundle_ne (Ne.symm hb)]
          exact ih _ _ _ _ heq hcs (hs' ▸ hs)
      · simp at hx
    | .entry (.executeAtomicBundle b ok) cs =>
      obtain ⟨-, hcs⟩ := hf
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        by_cases hb : b.hash = h
        · subst hb
          exact ih _ _ _ _ heq hcs (Or.inr (by simp))
        · have hs' : (beforeCalls .deployed b s).bundle h = s.bundle h := by
            simp [Ne.symm hb]
          exact ih _ _ _ _ heq hcs (hs' ▸ hs)
      · simp at hx
    | .entry (.verifyBundle b ok) cs =>
      obtain ⟨hpi, -⟩ := hf
      simp only [exec] at hx
      split_ifs at hx with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      by_cases hb : b.hash = h
      · exact absurd ⟨hb, hG.2⟩ hpi
      · simpa [Ne.symm hb] using hs
    | .entry (.unbundleBundle b req) cs =>
      obtain ⟨-, hcs⟩ := hf
      simp only [exec, writesCallsFirst_deployed] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₁ hm
        split at hx
        · rename_i s₂ l₂ heq
          simp only [afterUnbundle_deployed, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          by_cases hb : b.hash = h
          · exfalso
            rw [hb] at hG
            rcases hs with h' | h' <;> rw [h'] at hG <;>
              rcases hG.2 with h'' | h'' <;> exact absurd h'' (by decide)
          · obtain ⟨hmb, -, -, -⟩ := markCalls_spec req 0 _ s₁ hm
            have hs₁ : s₁.bundle h = s.bundle h := by
              rw [hmb]; simp [Ne.symm hb]
            exact ih _ _ _ _ heq hcs (hs₁ ▸ hs)
        · simp at hx
      · simp at hx
    | .calls hb [] cs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hs
    | .calls hb (i :: is) cs =>
      simp only [exec] at hx
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ih _ _ _ _ heq₂ (calleeAll_tail hf) (ih _ _ _ _ heq₁ (calleeAll_headD hf) hs)
        · simp at hx
      · simp at hx
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hs
    | .target .reverts => simp [exec] at hx
    | .target (.calls e inner caught next) =>
      cases hf with
      | calls hpe hinner hnext =>
        simp only [exec] at hx
        split at hx
        · rename_i s₁ l₁ heq₁
          split at hx
          · rename_i s₂ l₂ heq₂
            simp only [Option.some.injEq, Prod.mk.injEq] at hx
            obtain ⟨rfl, rfl⟩ := hx
            exact ih _ _ _ _ heq₂ hnext (ih _ _ _ _ heq₁ ⟨hpe, hinner⟩ hs)
          · simp at hx
        · split_ifs at hx
          exact ih _ _ _ _ hx hnext hs

/-! ## Transactions -/

lemma submitAll_untouched (h : BundleHash) : ∀ (s : State) (txs : List Tx),
    s.bundle h = .Unreceived →
    (∀ t ∈ txs, TxAll (fun e => ¬ ProvesInclusion h e ∧ ¬ PassesFlowGate h e) t) →
    (submitAll .deployed s txs).1.bundle h = .Unreceived ∧
      ∀ e ∈ (submitAll .deployed s txs).2, e.bundleHash ≠ h
  | s, [], hu, _ => ⟨hu, by simp [submitAll]⟩
  | s, t :: ts, hu, ht => by
    have h1 : (submit .deployed s t).1.bundle h = .Unreceived ∧
        ∀ e ∈ (submit .deployed s t).2, e.bundleHash ≠ h := by
      unfold submit
      cases hx : exec .deployed t.fuel (.entry t.entry t.callees) s with
      | none => exact ⟨hu, by simp [commit]⟩
      | some r =>
        obtain ⟨s', l⟩ := r
        exact exec_untouched h _ _ _ _ _ hx (ht t List.mem_cons_self)
          (fun _ _ _ he => by cases he) hu
    obtain ⟨h2, h3⟩ := submitAll_untouched h _ ts h1.1
      (fun t' ht' => ht t' (List.mem_cons_of_mem _ ht'))
    refine ⟨h2, fun e he => ?_⟩
    simp only [submitAll, List.mem_append] at he
    rcases he with he | he
    · exact h1.2 e he
    · exact h3 e he

lemma submitAll_atomicStates (h : BundleHash) : ∀ (s : State) (txs : List Tx),
    (s.bundle h = .Unreceived ∨ s.bundle h = .FullyExecuted) →
    (∀ t ∈ txs, TxAll (fun e => ¬ ProvesInclusion h e) t) →
    (submitAll .deployed s txs).1.bundle h = .Unreceived ∨
      (submitAll .deployed s txs).1.bundle h = .FullyExecuted
  | s, [], hs, _ => hs
  | s, t :: ts, hs, ht => by
    have h1 : (submit .deployed s t).1.bundle h = .Unreceived ∨
        (submit .deployed s t).1.bundle h = .FullyExecuted := by
      unfold submit
      cases hx : exec .deployed t.fuel (.entry t.entry t.callees) s with
      | none => exact hs
      | some r =>
        obtain ⟨s', l⟩ := r
        exact exec_atomicStates h _ _ _ _ _ hx (ht t List.mem_cons_self) hs
    exact submitAll_atomicStates h _ ts h1 (fun t' ht' => ht t' (List.mem_cons_of_mem _ ht'))

theorem DeliveryNeedsInclusionOrFlowGate : Properties.DeliveryNeedsInclusionOrFlowGate :=
  fun s h txs hu ht => submitAll_untouched h s txs hu ht

theorem NeverPublishedBundleNeedsTheFlowGate :
    Properties.NeverPublishedBundleNeedsTheFlowGate := by
  intro s h txs hu hno
  refine ⟨?_, fun ⟨e, he, heh⟩ hgate => ?_⟩
  · rcases submitAll_atomicStates h s txs (Or.inl hu) hno with h1 | h1
    · rw [h1]; exact .refl _
    · rw [h1]; exact .tail (.refl _) .executeAtomic
  · exact (submitAll_untouched h s txs hu
      (fun t ht => TxAll.and (hno t ht) (hgate t ht))).2 e he heh

/-! ## The countermodels -/

/-- `executeBundle` with an accepted proof, from `Unreceived`, targets returning. -/
lemma exec_public_fresh {s : State} {b : Bundle} (hu : s.bundle b.hash = .Unreceived) :
    exec .deployed (b.calls + 2) (.entry (.executeBundle b true) (List.replicate b.calls .returns)) s =
      some (beforeCalls .deployed b (s.verifyIfUnreceived b.hash),
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]) := by
  show exec .deployed (b.calls + 1 + 1) _ s = _
  simp only [exec]
  rw [exec_calls_returns .deployed b.hash _ _ _ _ (fun c hc => (List.mem_replicate.1 hc).2)
    (by simp)]
  simp [hu]

/-- `executeBundle` with no accepted proof, from `Verified`, targets returning. -/
lemma exec_public_verified {s : State} {b : Bundle} (hv : s.bundle b.hash = .Verified) :
    exec .deployed (b.calls + 2) (.entry (.executeBundle b false) (List.replicate b.calls .returns))
        s =
      some (beforeCalls .deployed b (s.verifyIfUnreceived b.hash),
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]) := by
  show exec .deployed (b.calls + 1 + 1) _ s = _
  simp only [exec]
  rw [exec_calls_returns .deployed b.hash _ _ _ _ (fun c hc => (List.mem_replicate.1 hc).2)
    (by simp)]
  simp [hv]

lemma txAll_replicate_returns {P : Entry → Prop} {e : Entry} (he : P e) (fuel n : ℕ) :
    TxAll P ⟨fuel, e, List.replicate n .returns⟩ :=
  ⟨he, fun c hc => by rw [(List.mem_replicate.1 hc).2]; exact .returns⟩

theorem ProvableBytesBypassTheFlowGate : Properties.ProvableBytesBypassTheFlowGate := by
  intro s b hu
  refine ⟨fun fuel cs => ?_, txAll_replicate_returns (fun h => h) _ _, ?_⟩
  · cases fuel with
    | zero => rfl
    | succ n => simp [submit, exec, commit]
  · simp only [submit, freshPublicRun]
    rw [exec_public_fresh hu]
    rfl

theorem VerifiedBundleRunsWithoutAnyGate : Properties.VerifiedBundleRunsWithoutAnyGate := by
  intro s b hv
  refine ⟨fun fuel gate cs => ?_,
    txAll_replicate_returns ⟨fun h => Bool.false_ne_true h.2, fun h => h⟩ _ _, ?_⟩
  · cases fuel with
    | zero => rfl
    | succ n => simp [submit, exec, commit, hv]
  · simp only [submit, provelessPublicRun]
    rw [exec_public_verified hv]
    rfl

theorem FlowGateRoutesWitness : Properties.FlowGateRoutesWitness := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, ?_⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl <;>
    exact ⟨fun h => h, fun c hc => by cases hc⟩

end Contracts.InteropHandler.Faithful
