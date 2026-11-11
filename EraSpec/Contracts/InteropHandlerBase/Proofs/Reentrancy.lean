import EraSpec.Contracts.InteropHandlerBase.Properties.Reentrancy
import Mathlib.Tactic

/-!
# Proofs: re-entrant execution cannot run a bundle or a call twice

The deployed results come from one invariant, `Good`, proved for every committed frame by
induction on the budget (`exec_good`). A frame is `Good` when every effect it commits was not
spent where it started and is spent where it ended, none repeats, and every record it wrote is
logged. `Good` composes along a target's successive calls and along a sequence of
transactions (`Good.append`), and that is the whole argument: an effect a nested frame commits
is fresh at the nested frame's start, while everything the outer frame has already done or
will still do itself is spent there, because the outer frame wrote its replay state before its
calls. The call loop carries the weaker `LoopGood`, whose own deliveries are spent from its
start rather than fresh. `Good` also carries the `BundleStatusMachine` edges, which gives
`NestedExecutionFollowsTheStatusMachine`.

The rollback results are two loop lemmas, valid in every order: a loop in which some target
reverts reverts (`exec_calls_reverts`), and a loop whose targets all return delivers every call
(`exec_calls_returns`). The concrete witnesses and countermodels are evaluated by `decide`; the
general countermodels are the same computation done symbolically, on any bundle with a call.
-/

namespace Contracts.InteropHandler

open AttackVectors.BundleStatusMachine

/-! ## State updates -/

@[simp] lemma setBundle_bundle (s : State) (h h' : BundleHash) (st : Status) :
    (s.setBundle h st).bundle h' = if h' = h then st else s.bundle h' := rfl

@[simp] lemma setBundle_call (s : State) (h : BundleHash) (st : Status) :
    (s.setBundle h st).call = s.call := rfl

@[simp] lemma setCall_bundle (s : State) (h : BundleHash) (i : ℕ) (st : CallStatus) :
    (s.setCall h i st).bundle = s.bundle := rfl

@[simp] lemma setCall_call (s : State) (h h' : BundleHash) (i i' : ℕ) (st : CallStatus) :
    (s.setCall h i st).call h' i' = if h' = h ∧ i' = i then st else s.call h' i' := rfl

@[simp] lemma executeAll_bundle (s : State) (h : BundleHash) (n : ℕ) :
    (s.executeAll h n).bundle = s.bundle := rfl

@[simp] lemma executeAll_call (s : State) (h h' : BundleHash) (n i : ℕ) :
    (s.executeAll h n).call h' i = if h' = h ∧ i < n then .Executed else s.call h' i := rfl

@[simp] lemma beforeCalls_deployed (b : Bundle) (s : State) :
    beforeCalls .deployed b s = (s.setBundle b.hash .FullyExecuted).executeAll b.hash b.calls :=
  rfl

@[simp] lemma afterCalls_deployed (b : Bundle) (s : State) : afterCalls .deployed b s = s := rfl

@[simp] lemma afterUnbundle_deployed (h : BundleHash) (req : List CallStatus) (s : State) :
    afterUnbundle .deployed h req s = s := rfl

@[simp] lemma writesCallsFirst_deployed : writesCallsFirst .deployed = true := rfl

/-! ## The status machines' closures are transitive -/

lemma reach_trans {a b c : Status} (h₁ : Reach a b) (h₂ : Reach b c) : Reach a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail ih hs

lemma reach_of_step {a b : Status} (h : Step a b) : Reach a b := .tail (.refl _) h

lemma callReach_trans {a b c : CallStatus} (h₁ : CallReach a b) (h₂ : CallReach b c) :
    CallReach a c := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact .tail ih hs

lemma callReach_of_step {a b : CallStatus} (h : CallStep a b) : CallReach a b :=
  .tail (.refl _) h

/-! ## `unbundleBundle`'s first loop -/

lemma toExecute_ge : ∀ {i j : ℕ} {req : List CallStatus}, j ∈ toExecute i req → i ≤ j
  | _, _, [], h => by simp [toExecute] at h
  | i, j, .Executed :: req, h => by
      rcases List.mem_cons.1 h with h | h
      · omega
      · have := toExecute_ge h; omega
  | i, j, .Cancelled :: req, h => by have := toExecute_ge (i := i + 1) h; omega
  | i, j, .Unprocessed :: req, h => by have := toExecute_ge (i := i + 1) h; omega

lemma toExecute_nodup : ∀ (i : ℕ) (req : List CallStatus), (toExecute i req).Nodup
  | _, [] => List.nodup_nil
  | i, .Executed :: req => by
      refine List.Nodup.cons (fun h => ?_) (toExecute_nodup _ _)
      have := toExecute_ge h; omega
  | i, .Cancelled :: req => toExecute_nodup (i + 1) req
  | i, .Unprocessed :: req => toExecute_nodup (i + 1) req

/-- What the deployed first loop does: it leaves the bundle statuses and other bundles alone,
records each requested execution over an `Unprocessed` call, and otherwise leaves a call as it
was or cancels an `Unprocessed` one. -/
lemma markCalls_spec {h : BundleHash} :
    ∀ (req : List CallStatus) (i : ℕ) (u s₁ : State), markCalls true h i req u = some s₁ →
      s₁.bundle = u.bundle ∧
      (∀ h' j, h' ≠ h → s₁.call h' j = u.call h' j) ∧
      (∀ j ∈ toExecute i req, u.call h j = .Unprocessed ∧ s₁.call h j = .Executed) ∧
      (∀ j, j ∉ toExecute i req →
        s₁.call h j = u.call h j ∨ (u.call h j = .Unprocessed ∧ s₁.call h j = .Cancelled))
  | [], i, u, s₁, hm => by
      simp only [markCalls, Option.some.injEq] at hm
      subst hm
      exact ⟨rfl, fun _ _ _ => rfl, by simp [toExecute], fun _ _ => Or.inl rfl⟩
  | .Executed :: req, i, u, s₁, hm => by
      simp only [markCalls, ↓reduceIte] at hm
      split_ifs at hm with hu
      obtain ⟨hb, ho, he, hn⟩ := markCalls_spec req (i + 1) _ s₁ hm
      refine ⟨by simpa using hb, fun h' j hh => by simpa [hh] using ho h' j hh, ?_, ?_⟩
      · intro j hj
        rcases List.mem_cons.1 hj with rfl | hj
        · have hnot : j ∉ toExecute (j + 1) req := fun h' => by
            have := toExecute_ge h'; omega
          refine ⟨hu, ?_⟩
          rcases hn j hnot with h1 | ⟨h1, _⟩ <;> simp_all
        · have hji : j ≠ i := by have := toExecute_ge hj; omega
          obtain ⟨h1, h2⟩ := he j hj
          exact ⟨by simpa [hji] using h1, h2⟩
      · intro j hj
        have hji : j ≠ i := fun h' => hj (h' ▸ List.mem_cons_self)
        have hj' : j ∉ toExecute (i + 1) req := fun h' => hj (List.mem_cons_of_mem _ h')
        simpa [hji] using hn j hj'
  | .Cancelled :: req, i, u, s₁, hm => by
      simp only [markCalls] at hm
      split_ifs at hm with hx hu
      · obtain ⟨hb, ho, he, hn⟩ := markCalls_spec req (i + 1) _ s₁ hm
        refine ⟨by simpa using hb, fun h' j hh => by simpa [hh] using ho h' j hh, ?_, ?_⟩
        · intro j hj
          have hji : j ≠ i := by have := toExecute_ge (i := i + 1) (req := req) hj; omega
          obtain ⟨h1, h2⟩ := he j hj
          exact ⟨by simpa [hji] using h1, h2⟩
        · intro j hj
          by_cases hji : j = i
          · subst hji
            have hnot : j ∉ toExecute (j + 1) req := fun h' => by
              have := toExecute_ge h'; omega
            rcases hn j hnot with h1 | ⟨h1, _⟩ <;> simp_all
          · simpa [hji] using hn j hj
      · exact markCalls_spec req (i + 1) u s₁ hm
  | .Unprocessed :: req, i, u, s₁, hm => by
      simp only [markCalls] at hm
      exact markCalls_spec req (i + 1) u s₁ hm

/-! ## The invariant -/

/-- What every committed frame satisfies, for an entry point or a target that went from `s` to
`s'` committing `l`. -/
structure Good (s s' : State) (l : List Effect) : Prop where
  spentMono : ∀ e, Spent s e → Spent s' e
  recMono : ∀ e, Recorded s e → Recorded s' e
  fresh : ∀ e ∈ l, ¬ Spent s e
  spent : ∀ e ∈ l, Spent s' e
  recorded : ∀ e ∈ l, Recorded s' e
  nodup : l.Nodup
  logged : ∀ e, Recorded s' e → Recorded s e ∨ e ∈ l
  reach : ∀ h, Reach (s.bundle h) (s'.bundle h)
  calls : CallsClosed s → CallsClosed s' ∧ ∀ h i, CallReach (s.call h i) (s'.call h i)

/-- What a committed call loop of bundle `h` over calls `is` satisfies. Its own deliveries are
spent from its start (its entry point wrote them first), so they are not fresh; everything
else is as in `Good`. -/
structure LoopGood (h : BundleHash) (is : List ℕ) (s s' : State) (l : List Effect) : Prop where
  spentMono : ∀ e, Spent s e → Spent s' e
  recMono : ∀ e, Recorded s e → Recorded s' e
  fresh : ∀ e ∈ l, ¬ Spent s e ∨ ∃ j ∈ is, e = .delivered h j
  spent : (∀ j ∈ is, Spent s (.delivered h j)) → ∀ e ∈ l, Spent s' e
  recorded : (∀ j ∈ is, Recorded s (.delivered h j)) → ∀ e ∈ l, Recorded s' e
  nodup : (∀ j ∈ is, Spent s (.delivered h j)) → is.Nodup → l.Nodup
  logged : ∀ e, Recorded s' e → Recorded s e ∨ e ∈ l
  own : ∀ j ∈ is, Effect.delivered h j ∈ l
  only : s.bundle h = .FullyExecuted →
    l.filter (fun e => e.bundleHash = h) = is.map (Effect.delivered h)
  reach : ∀ h', Reach (s.bundle h') (s'.bundle h')
  calls : CallsClosed s → CallsClosed s' ∧ ∀ h' i, CallReach (s.call h' i) (s'.call h' i)

lemma spent_of_fullyExecuted {s : State} {h : BundleHash} (hfe : s.bundle h = .FullyExecuted) :
    ∀ e : Effect, e.bundleHash = h → Spent s e
  | .delivered _ _, rfl => Or.inl hfe
  | .executed _, rfl => hfe

lemma Good.refl (s : State) : Good s s [] where
  spentMono _ h := h
  recMono _ h := h
  fresh _ h := by simp at h
  spent _ h := by simp at h
  recorded _ h := by simp at h
  nodup := List.nodup_nil
  logged _ h := Or.inl h
  reach _ := .refl _
  calls hc := ⟨hc, fun _ _ => .refl _⟩

lemma Good.append {s s₁ s₂ : State} {l₁ l₂ : List Effect} (g₁ : Good s s₁ l₁)
    (g₂ : Good s₁ s₂ l₂) : Good s s₂ (l₁ ++ l₂) where
  spentMono e he := g₂.spentMono e (g₁.spentMono e he)
  recMono e he := g₂.recMono e (g₁.recMono e he)
  fresh e he := by
    rcases List.mem_append.1 he with h | h
    · exact g₁.fresh e h
    · exact fun hs => g₂.fresh e h (g₁.spentMono e hs)
  spent e he := by
    rcases List.mem_append.1 he with h | h
    · exact g₂.spentMono e (g₁.spent e h)
    · exact g₂.spent e h
  recorded e he := by
    rcases List.mem_append.1 he with h | h
    · exact g₂.recMono e (g₁.recorded e h)
    · exact g₂.recorded e h
  nodup := by
    refine List.nodup_append.2 ⟨g₁.nodup, g₂.nodup, ?_⟩
    rintro a ha b hb rfl
    exact g₂.fresh a hb (g₁.spent a ha)
  logged e he := by
    rcases g₂.logged e he with h | h
    · rcases g₁.logged e h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_append_left _ h')
    · exact Or.inr (List.mem_append_right _ h)
  reach h := reach_trans (g₁.reach h) (g₂.reach h)
  calls hc := by
    obtain ⟨hc₁, hr₁⟩ := g₁.calls hc
    obtain ⟨hc₂, hr₂⟩ := g₂.calls hc₁
    exact ⟨hc₂, fun h i => callReach_trans (hr₁ h i) (hr₂ h i)⟩

lemma LoopGood.nil (h : BundleHash) (s : State) : LoopGood h [] s s [] where
  spentMono _ h := h
  recMono _ h := h
  fresh _ h := by simp at h
  spent _ _ h := by simp at h
  recorded _ _ h := by simp at h
  nodup _ _ := List.nodup_nil
  logged _ h := Or.inl h
  own _ h := by simp at h
  only _ := rfl
  reach _ := .refl _
  calls hc := ⟨hc, fun _ _ => .refl _⟩

/-- One more delivery: call `i`'s target ran from `s` to `s₁`, then the rest of the loop. -/
lemma LoopGood.cons {h : BundleHash} {i : ℕ} {is : List ℕ} {s s₁ s₂ : State}
    {l₁ l₂ : List Effect} (g₁ : Good s s₁ l₁) (g₂ : LoopGood h is s₁ s₂ l₂) :
    LoopGood h (i :: is) s s₂ (.delivered h i :: (l₁ ++ l₂)) where
  spentMono e he := g₂.spentMono e (g₁.spentMono e he)
  recMono e he := g₂.recMono e (g₁.recMono e he)
  fresh e he := by
    rcases List.mem_cons.1 he with rfl | he
    · exact Or.inr ⟨i, List.mem_cons_self, rfl⟩
    rcases List.mem_append.1 he with he | he
    · exact Or.inl (g₁.fresh e he)
    · rcases g₂.fresh e he with h' | ⟨j, hj, rfl⟩
      · exact Or.inl fun hs => h' (g₁.spentMono _ hs)
      · exact Or.inr ⟨j, List.mem_cons_of_mem _ hj, rfl⟩
  spent hown e he := by
    have hown₁ : ∀ j ∈ is, Spent s₁ (.delivered h j) :=
      fun j hj => g₁.spentMono _ (hown j (List.mem_cons_of_mem _ hj))
    rcases List.mem_cons.1 he with rfl | he
    · exact g₂.spentMono _ (g₁.spentMono _ (hown i List.mem_cons_self))
    rcases List.mem_append.1 he with he | he
    · exact g₂.spentMono e (g₁.spent e he)
    · exact g₂.spent hown₁ e he
  recorded hown e he := by
    have hown₁ : ∀ j ∈ is, Recorded s₁ (.delivered h j) :=
      fun j hj => g₁.recMono _ (hown j (List.mem_cons_of_mem _ hj))
    rcases List.mem_cons.1 he with rfl | he
    · exact g₂.recMono _ (g₁.recMono _ (hown i List.mem_cons_self))
    rcases List.mem_append.1 he with he | he
    · exact g₂.recMono e (g₁.recorded e he)
    · exact g₂.recorded hown₁ e he
  nodup hown hnd := by
    have hown₁ : ∀ j ∈ is, Spent s₁ (.delivered h j) :=
      fun j hj => g₁.spentMono _ (hown j (List.mem_cons_of_mem _ hj))
    have hi := hown i List.mem_cons_self
    obtain ⟨hni, hnd'⟩ := List.nodup_cons.1 hnd
    refine List.Nodup.cons ?_ (List.nodup_append.2 ⟨g₁.nodup, g₂.nodup hown₁ hnd', ?_⟩)
    · intro hmem
      rcases List.mem_append.1 hmem with hm | hm
      · exact g₁.fresh _ hm hi
      · rcases g₂.fresh _ hm with h' | ⟨j, hj, hji⟩
        · exact h' (g₁.spentMono _ hi)
        · cases hji; exact hni hj
    · rintro a ha b hb rfl
      rcases g₂.fresh a hb with h' | ⟨j, hj, rfl⟩
      · exact h' (g₁.spent a ha)
      · exact g₁.fresh _ ha (hown j (List.mem_cons_of_mem _ hj))
  logged e he := by
    rcases g₂.logged e he with h' | h'
    · rcases g₁.logged e h' with h'' | h''
      · exact Or.inl h''
      · exact Or.inr (List.mem_cons_of_mem _ (List.mem_append_left _ h''))
    · exact Or.inr (List.mem_cons_of_mem _ (List.mem_append_right _ h'))
  own j hj := by
    rcases List.mem_cons.1 hj with rfl | hj
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (g₂.own j hj))
  only hfe := by
    have hfe₁ : s₁.bundle h = .FullyExecuted := g₁.spentMono (.executed h) hfe
    have hl₁ : l₁.filter (fun e => e.bundleHash = h) = [] := by
      refine List.filter_eq_nil_iff.2 fun e he hp => ?_
      exact g₁.fresh e he (spent_of_fullyExecuted hfe e (by simpa using hp))
    have hhd : decide ((Effect.delivered h i).bundleHash = h) = true := by
      simp [Effect.bundleHash]
    rw [List.filter_cons]
    simp only [hhd, ↓reduceIte]
    rw [List.filter_append, hl₁, g₂.only hfe₁]
    simp
  reach h' := reach_trans (g₁.reach h') (g₂.reach h')
  calls hc := by
    obtain ⟨hc₁, hr₁⟩ := g₁.calls hc
    obtain ⟨hc₂, hr₂⟩ := g₂.calls hc₁
    exact ⟨hc₂, fun h' i => callReach_trans (hr₁ h' i) (hr₂ h' i)⟩

/-! ## The entry points, deployed order -/

/-- `verifyBundle`, and `executeBundle`'s `_verifyBundle` on an `Unreceived` bundle. -/
lemma good_verify {s : State} {h : BundleHash} (hu : s.bundle h = .Unreceived) :
    Good s (s.setBundle h .Verified) [] where
  spentMono e he := by
    cases e with
    | delivered h' i =>
      by_cases hh : h' = h
      · subst hh; simp [Spent, hu] at he
      · simpa [Spent, hh] using he
    | executed h' =>
      by_cases hh : h' = h
      · subst hh; simp [Spent, hu] at he
      · simpa [Spent, hh] using he
  recMono e he := by
    cases e with
    | delivered h' i => simpa [Recorded] using he
    | executed h' =>
      by_cases hh : h' = h
      · subst hh; simp [Recorded, hu] at he
      · simpa [Recorded, hh] using he
  fresh _ h := by simp at h
  spent _ h := by simp at h
  recorded _ h := by simp at h
  nodup := List.nodup_nil
  logged e he := by
    left
    cases e with
    | delivered h' i => simpa [Recorded] using he
    | executed h' =>
      by_cases hh : h' = h
      · subst hh; simp [Recorded] at he
      · simpa [Recorded, hh] using he
  reach h' := by
    by_cases hh : h' = h
    · subst hh; simpa [hu] using reach_of_step Step.verify
    · simpa [hh] using Reach.refl (s.bundle h')
  calls hc := by
    refine ⟨fun h' i hi => ?_, fun _ _ => by simpa using CallReach.refl _⟩
    by_cases hh : h' = h
    · subst hh
      rcases hc h' i (by simpa using hi) with h1 | h1 <;> simp [hu] at h1
    · simpa [hh] using hc h' i (by simpa using hi)

/-- `verifyIfUnreceived` on a bundle `executeBundle` admits. -/
lemma good_verifyIfUnreceived {s : State} {h : BundleHash}
    (hopen : s.bundle h = .Unreceived ∨ s.bundle h = .Verified) :
    Good s (s.verifyIfUnreceived h) [] ∧ (s.verifyIfUnreceived h).bundle h = .Verified := by
  unfold State.verifyIfUnreceived
  by_cases hu : s.bundle h = .Unreceived
  · simp only [hu, ↓reduceIte]
    exact ⟨good_verify hu, by simp⟩
  · have hv : s.bundle h = .Verified := hopen.resolve_left hu
    simp only [hu, ↓reduceIte]
    exact ⟨Good.refl s, hv⟩

/-- `executeBundle` and `executeAtomicBundle` after their checks: the writes before the calls,
then the call loop. -/
lemma good_whole {b : Bundle} {s s₂ : State} {l : List Effect}
    (hopen : s.bundle b.hash = .Unreceived ∨ s.bundle b.hash = .Verified)
    (g : LoopGood b.hash (List.range b.calls) (beforeCalls .deployed b s) s₂ l) :
    Good s s₂ (l ++ [.executed b.hash]) := by
  have hne1 : s.bundle b.hash ≠ .FullyExecuted := by rcases hopen with h | h <;> simp [h]
  have hne2 : s.bundle b.hash ≠ .Unbundled := by rcases hopen with h | h <;> simp [h]
  have spent_t : ∀ e, Spent s e → Spent (beforeCalls .deployed b s) e := by
    intro e he
    cases e with
    | delivered h' i =>
      by_cases hh : h' = b.hash
      · subst hh; simp [Spent, hne1, hne2] at he
      · simpa [Spent, hh] using he
    | executed h' =>
      by_cases hh : h' = b.hash
      · subst hh; simp [Spent, hne1] at he
      · simpa [Spent, hh] using he
  have rec_t : ∀ e, Recorded s e → Recorded (beforeCalls .deployed b s) e := by
    intro e he
    cases e with
    | delivered h' i =>
      simp only [Recorded, beforeCalls_deployed, executeAll_call, setBundle_call] at he ⊢
      split_ifs <;> simp_all
    | executed h' =>
      by_cases hh : h' = b.hash
      · subst hh; simp [Recorded, hne1] at he
      · simpa [Recorded, hh] using he
  have rec_t_inv : ∀ e, Recorded (beforeCalls .deployed b s) e →
      Recorded s e ∨ e = .executed b.hash ∨
        ∃ j ∈ List.range b.calls, e = .delivered b.hash j := by
    intro e he
    cases e with
    | delivered h' i =>
      simp only [Recorded, beforeCalls_deployed, executeAll_call, setBundle_call] at he
      split_ifs at he with hc
      · obtain ⟨rfl, hi⟩ := hc
        exact Or.inr (Or.inr ⟨i, List.mem_range.2 hi, rfl⟩)
      · exact Or.inl he
    | executed h' =>
      by_cases hh : h' = b.hash
      · subst hh; exact Or.inr (Or.inl rfl)
      · left; simpa [Recorded, hh] using he
  have hownSpent : ∀ j ∈ List.range b.calls,
      Spent (beforeCalls .deployed b s) (.delivered b.hash j) := fun j _ => Or.inl (by simp)
  have hownRec : ∀ j ∈ List.range b.calls,
      Recorded (beforeCalls .deployed b s) (.delivered b.hash j) :=
    fun j hj => by simp [Recorded, List.mem_range.1 hj]
  have htfe : Spent (beforeCalls .deployed b s) (.executed b.hash) := by simp [Spent]
  exact {
    spentMono := fun e he => g.spentMono e (spent_t e he)
    recMono := fun e he => g.recMono e (rec_t e he)
    fresh := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · rcases g.fresh e he with h' | ⟨j, _, rfl⟩
        · exact fun hs => h' (spent_t e hs)
        · simp [Spent, hne1, hne2]
      · rw [List.mem_singleton.1 he]; exact hne1
    spent := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact g.spent hownSpent e he
      · rw [List.mem_singleton.1 he]; exact g.spentMono _ htfe
    recorded := by
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact g.recorded hownRec e he
      · rw [List.mem_singleton.1 he]; exact g.recMono _ htfe
    nodup := by
      refine List.nodup_append.2
        ⟨g.nodup hownSpent List.nodup_range, List.nodup_singleton _, ?_⟩
      rintro a ha c hc rfl
      rw [List.mem_singleton.1 hc] at ha
      rcases g.fresh _ ha with h' | ⟨j, _, hj⟩
      · exact h' htfe
      · cases hj
    logged := by
      intro e he
      rcases g.logged e he with h' | h'
      · rcases rec_t_inv e h' with h'' | rfl | ⟨j, hj, rfl⟩
        · exact Or.inl h''
        · exact Or.inr (List.mem_append_right _ (List.mem_singleton_self _))
        · exact Or.inr (List.mem_append_left _ (g.own j hj))
      · exact Or.inr (List.mem_append_left _ h')
    reach := by
      intro h'
      refine reach_trans ?_ (g.reach h')
      by_cases hh : h' = b.hash
      · subst hh
        rcases hopen with hu | hv
        · simpa [hu] using reach_of_step Step.executeFresh
        · simpa [hv] using reach_of_step Step.executeVerified
      · simpa [hh] using Reach.refl (s.bundle h')
    calls := by
      intro hc
      refine (g.calls ?_).imp id fun hr h' i => callReach_trans ?_ (hr h' i)
      · intro h' i hi
        by_cases hh : h' = b.hash
        · subst hh; simp
        · simp only [beforeCalls_deployed, executeAll_call, hh, false_and, ↓reduceIte,
            setBundle_call, executeAll_bundle, setBundle_bundle] at hi ⊢
          exact hc h' i hi
      · simp only [beforeCalls_deployed, executeAll_call, setBundle_call]
        split_ifs with hx
        · obtain ⟨rfl, _⟩ := hx
          have hu : s.call b.hash i = .Unprocessed := by
            by_contra hne
            rcases hc b.hash i hne with h1 | h1
            · exact hne1 h1
            · exact hne2 h1
          rw [hu]; exact callReach_of_step CallStep.execute
        · exact CallReach.refl _ }

/-- `unbundleBundle` after its checks: the status write, the first loop, then the call loop. -/
lemma good_unbundle {b : Bundle} {req : List CallStatus} {s s₁ s₂ : State} {l : List Effect}
    (hg : s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled)
    (hm : markCalls true b.hash 0 req (s.setBundle b.hash .Unbundled) = some s₁)
    (g : LoopGood b.hash (toExecute 0 req) s₁ s₂ l) : Good s s₂ l := by
  obtain ⟨hb, ho, he, hn⟩ := markCalls_spec req 0 _ s₁ hm
  simp only [setBundle_call] at ho he hn
  have hne1 : s.bundle b.hash ≠ .FullyExecuted := by rcases hg with h | h <;> simp [h]
  have hb' : ∀ h', s₁.bundle h' = if h' = b.hash then .Unbundled else s.bundle h' := by
    intro h'; rw [hb]; rfl
  have spent_1 : ∀ e, Spent s e → Spent s₁ e := by
    intro e hs
    cases e with
    | delivered h' j =>
      by_cases hh : h' = b.hash
      · subst hh
        simp only [Spent, hne1, false_or] at hs
        obtain ⟨_, hx⟩ := hs
        refine Or.inr ⟨by simp [hb'], ?_⟩
        by_cases hj : j ∈ toExecute 0 req
        · exact (he j hj).2
        · rcases hn j hj with h1 | ⟨h1, _⟩
          · rw [h1, hx]
          · rw [hx] at h1; cases h1
      · simpa [Spent, hb', hh, ho h' j hh] using hs
    | executed h' =>
      by_cases hh : h' = b.hash
      · subst hh; exact absurd hs hne1
      · simpa [Spent, hb', hh] using hs
  have rec_1 : ∀ e, Recorded s e → Recorded s₁ e := by
    intro e hr
    cases e with
    | delivered h' j =>
      simp only [Recorded] at hr ⊢
      by_cases hh : h' = b.hash
      · subst hh
        by_cases hj : j ∈ toExecute 0 req
        · exact (he j hj).2
        · rcases hn j hj with h1 | ⟨h1, _⟩
          · rw [h1, hr]
          · rw [hr] at h1; cases h1
      · rw [ho h' j hh, hr]
    | executed h' =>
      by_cases hh : h' = b.hash
      · subst hh; exact absurd hr hne1
      · simpa [Recorded, hb', hh] using hr
  have rec_1_inv : ∀ e, Recorded s₁ e →
      Recorded s e ∨ ∃ j ∈ toExecute 0 req, e = .delivered b.hash j := by
    intro e hr
    cases e with
    | delivered h' j =>
      simp only [Recorded] at hr
      by_cases hh : h' = b.hash
      · subst hh
        by_cases hj : j ∈ toExecute 0 req
        · exact Or.inr ⟨j, hj, rfl⟩
        · rcases hn j hj with h1 | ⟨_, h1⟩
          · left; simp only [Recorded]; rw [← h1, hr]
          · rw [hr] at h1; cases h1
      · left; simp only [Recorded]; rw [← ho h' j hh, hr]
    | executed h' =>
      left
      by_cases hh : h' = b.hash
      · subst hh; simp [Recorded, hb'] at hr
      · simpa [Recorded, hb', hh] using hr
  have hownSpent : ∀ j ∈ toExecute 0 req, Spent s₁ (.delivered b.hash j) :=
    fun j hj => Or.inr ⟨by simp [hb'], (he j hj).2⟩
  have hownRec : ∀ j ∈ toExecute 0 req, Recorded s₁ (.delivered b.hash j) :=
    fun j hj => (he j hj).2
  exact {
    spentMono := fun e hs => g.spentMono e (spent_1 e hs)
    recMono := fun e hr => g.recMono e (rec_1 e hr)
    fresh := by
      intro e hel
      rcases g.fresh e hel with h' | ⟨j, hj, rfl⟩
      · exact fun hs => h' (spent_1 e hs)
      · have hu := (he j hj).1
        simp [Spent, hne1, hu]
    spent := g.spent hownSpent
    recorded := g.recorded hownRec
    nodup := g.nodup hownSpent (toExecute_nodup 0 req)
    logged := by
      intro e hr
      rcases g.logged e hr with h' | h'
      · rcases rec_1_inv e h' with h'' | ⟨j, hj, rfl⟩
        · exact Or.inl h''
        · exact Or.inr (g.own j hj)
      · exact Or.inr h'
    reach := by
      intro h'
      refine reach_trans ?_ (g.reach h')
      by_cases hh : h' = b.hash
      · subst hh
        rcases hg with hv | hu
        · simpa [hb', hv] using reach_of_step Step.unbundleFirst
        · simpa [hb', hu] using reach_of_step Step.unbundleAgain
      · simpa [hb', hh] using Reach.refl (s.bundle h')
    calls := by
      intro hc
      refine (g.calls ?_).imp id fun hr h' i => callReach_trans ?_ (hr h' i)
      · intro h' i hi
        by_cases hh : h' = b.hash
        · subst hh; simp [hb']
        · rw [ho h' i hh] at hi
          simpa [hb', hh] using hc h' i hi
      · by_cases hh : h' = b.hash
        · subst hh
          by_cases hj : i ∈ toExecute 0 req
          · obtain ⟨h1, h2⟩ := he i hj
            rw [h1, h2]; exact callReach_of_step CallStep.execute
          · rcases hn i hj with h1 | ⟨h1, h2⟩
            · rw [h1]; exact CallReach.refl _
            · rw [h1, h2]; exact callReach_of_step CallStep.cancel
        · rw [ho h' i hh]; exact CallReach.refl _ }

/-! ## Every committed frame is `Good` -/

/-- The invariant a frame of each kind satisfies. -/
def FrameGood : Frame → State → State → List Effect → Prop
  | .entry _ _, s, s', l => Good s s' l
  | .calls h is _, s, s', l => LoopGood h is s s' l
  | .target _, s, s', l => Good s s' l

/-- **The invariant.** Every frame that commits in the deployed order, at every budget, is
`Good` (an entry point or a target) or `LoopGood` (a call loop). -/
theorem exec_good : ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
    exec .deployed n f s = some (s', l) → FrameGood f s s' l := by
  intro n
  induction n with
  | zero => intro f s s' l h; simp [exec] at h
  | succ n ih =>
    intro f s s' l h
    match f with
    | .entry (.executeBundle b ok) cs =>
      simp only [exec] at h
      split_ifs at h with hG
      split at h
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hopen : s.bundle b.hash = .Unreceived ∨ s.bundle b.hash = .Verified := by
          rcases hG with hv | ⟨hu, _⟩
          · exact Or.inr hv
          · exact Or.inl hu
        obtain ⟨g₀, hv⟩ := good_verifyIfUnreceived hopen
        have g := g₀.append (good_whole (Or.inr hv) (ih _ _ _ _ heq))
        rw [List.nil_append] at g
        exact g
      · simp at h
    | .entry (.executeAtomicBundle b ok) cs =>
      simp only [exec] at h
      split_ifs at h with hG
      split at h
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact good_whole (Or.inl hG.1) (ih _ _ _ _ heq)
      · simp at h
    | .entry (.verifyBundle b ok) cs =>
      simp only [exec] at h
      split_ifs at h with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact good_verify hG.1
    | .entry (.unbundleBundle b req) cs =>
      simp only [exec, writesCallsFirst_deployed] at h
      split_ifs at h with hG
      split at h
      · rename_i s₁ hm
        split at h
        · rename_i s₂ l₂ heq
          simp only [afterUnbundle_deployed, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact good_unbundle hG.2 hm (ih _ _ _ _ heq)
        · simp at h
      · simp at h
    | .calls hb [] cs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact LoopGood.nil hb s
    | .calls hb (i :: is) cs =>
      simp only [exec] at h
      split at h
      · rename_i s₁ l₁ heq₁
        split at h
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact LoopGood.cons (ih _ _ _ _ heq₁) (ih _ _ _ _ heq₂)
        · simp at h
      · simp at h
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Good.refl s
    | .target .reverts => simp [exec] at h
    | .target (.calls e inner caught next) =>
      simp only [exec] at h
      split at h
      · rename_i s₁ l₁ heq₁
        split at h
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact (ih _ _ _ _ heq₁).append (ih _ _ _ _ heq₂)
        · simp at h
      · split_ifs at h
        exact (ih (.target next) s s' l h : Good s s' l)

/-! ## Transactions and sequences of them -/

lemma submit_good (s : State) (t : Tx) :
    Good s (submit .deployed s t).1 (submit .deployed s t).2 := by
  unfold submit
  cases hx : exec .deployed t.fuel (.entry t.entry t.callees) s with
  | none => exact Good.refl s
  | some r =>
    obtain ⟨s', l⟩ := r
    exact exec_good _ _ _ _ _ hx

lemma submitAll_good : ∀ (s : State) (txs : List Tx),
    Good s (submitAll .deployed s txs).1 (submitAll .deployed s txs).2
  | s, [] => Good.refl s
  | s, t :: ts => (submit_good s t).append (submitAll_good _ ts)

/-! ## (a) Nothing runs twice -/

theorem NoEffectCommittedTwice : Properties.NoEffectCommittedTwice :=
  fun s txs => (submitAll_good s txs).nodup

theorem CommittedEffectsWereOpen : Properties.CommittedEffectsWereOpen :=
  fun s txs e he => ⟨(submitAll_good s txs).fresh e he, (submitAll_good s txs).spent e he⟩

/-- A whole-bundle execution's own effects, from its call loop. -/
lemma whole_of_loop {b : Bundle} {t s₂ : State} {l₂ : List Effect}
    (ht : t.bundle b.hash = .FullyExecuted) (g : LoopGood b.hash (List.range b.calls) t s₂ l₂) :
    (l₂ ++ [Effect.executed b.hash]).filter (fun e => e.bundleHash = b.hash) =
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash] ∧
      s₂.bundle b.hash = .FullyExecuted := by
  refine ⟨?_, g.spentMono (.executed b.hash) ht⟩
  rw [List.filter_append, g.only ht]
  simp [Effect.bundleHash]

theorem WholeBundleExecutionRunsEachCallOnce :
    Properties.WholeBundleExecutionRunsEachCallOnce := by
  intro n b ok cs s s' l h
  rcases n with _ | n
  · rcases h with h | h <;> simp [exec] at h
  rcases h with h | h
  · simp only [exec] at h
    split_ifs at h with hG
    split at h
    · rename_i s₂ l₂ heq
      simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact whole_of_loop (by simp) (exec_good _ _ _ _ _ heq)
    · simp at h
  · simp only [exec] at h
    split_ifs at h with hG
    split at h
    · rename_i s₂ l₂ heq
      simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact whole_of_loop (by simp) (exec_good _ _ _ _ _ heq)
    · simp at h

theorem StatusRecordsExactlyTheCommittedEffects :
    Properties.StatusRecordsExactlyTheCommittedEffects := by
  intro txs h i
  have g := submitAll_good init txs
  refine ⟨⟨fun hc => ?_, fun hm => g.recorded _ hm⟩,
    ⟨fun hc => ?_, fun hm => g.recorded _ hm⟩⟩
  · rcases g.logged (.delivered h i) hc with h' | h'
    · simp [Recorded, init] at h'
    · exact h'
  · rcases g.logged (.executed h) hc with h' | h'
    · simp [Recorded, init] at h'
    · exact h'

theorem NestedExecutionFollowsTheStatusMachine :
    Properties.NestedExecutionFollowsTheStatusMachine := by
  refine ⟨fun _ _ h => absurd rfl h, fun s txs hc => ?_⟩
  have g := submitAll_good s txs
  obtain ⟨hc', hr⟩ := g.calls hc
  exact ⟨hc', g.reach, hr⟩

/-- `FullyExecuted` persists along every committed frame. -/
lemma exec_keeps_fullyExecuted {n : ℕ} {f : Frame} {h : BundleHash} {s s' : State}
    {l : List Effect} (hfe : s.bundle h = .FullyExecuted)
    (hx : exec .deployed n f s = some (s', l)) : s'.bundle h = .FullyExecuted := by
  have g := exec_good n f s s' l hx
  cases f with
  | entry _ _ => exact Good.spentMono g (.executed h) hfe
  | calls _ _ _ => exact LoopGood.spentMono g (.executed h) hfe
  | target _ => exact Good.spentMono g (.executed h) hfe

/-- Every entry point refuses a fully executed bundle. -/
lemma exec_entry_of_fullyExecuted {n : ℕ} {e : Entry} {cs : List Callee} {s : State}
    (hfe : s.bundle e.bundle.hash = .FullyExecuted) : exec .deployed n (.entry e cs) s = none := by
  cases n with
  | zero => simp [exec]
  | succ n =>
    cases e with
    | executeBundle b ok => simp only [Entry.bundle] at hfe; simp [exec, hfe]
    | verifyBundle b ok => simp only [Entry.bundle] at hfe; simp [exec, hfe]
    | unbundleBundle b req => simp only [Entry.bundle] at hfe; simp [exec, hfe]
    | executeAtomicBundle b ok => simp only [Entry.bundle] at hfe; simp [exec, hfe]

theorem ReentryForAnExecutingBundleReverts : Properties.ReentryForAnExecutingBundleReverts :=
  ⟨fun _ _ => by simp, fun _ _ _ _ _ _ hfe hx => exec_keeps_fullyExecuted hfe hx,
    fun _ _ _ _ hfe => exec_entry_of_fullyExecuted hfe⟩

theorem ReentrantExecutionWitness : Properties.ReentrantExecutionWitness := by
  unfold Properties.ReentrantExecutionWitness; decide

/-! ## (b) A failing call rolls the execution back -/

/-- A call loop in which some target reverts reverts, in every order. -/
lemma exec_calls_reverts (v : Variant) (h : BundleHash) :
    ∀ (is : List ℕ) (cs : List Callee) (m : ℕ) (s : State),
      Callee.reverts ∈ cs.take is.length → exec v m (.calls h is cs) s = none
  | [], _, _, _, hr => by simp at hr
  | _ :: _, _, 0, _, _ => by simp [exec]
  | _ :: _, [], _ + 1, _, hr => by simp at hr
  | i :: is, c :: cs, m + 1, s, hr => by
      simp only [List.length_cons, List.take_succ_cons, List.mem_cons] at hr
      simp only [exec, List.headD_cons, List.tail_cons]
      rcases hr with rfl | hr
      · cases m with
        | zero => simp [exec]
        | succ m => simp [exec]
      · split
        · rename_i s₁ l₁ _
          rw [exec_calls_reverts v h is cs m s₁ hr]
        · rfl

/-- A call loop whose targets all return delivers every call and changes nothing, in every
order. -/
lemma exec_calls_returns (v : Variant) (h : BundleHash) :
    ∀ (is : List ℕ) (cs : List Callee) (m : ℕ) (s : State),
      (∀ c ∈ cs, c = .returns) → is.length < m →
      exec v m (.calls h is cs) s = some (s, is.map (Effect.delivered h))
  | [], _, 0, _, _, hm => absurd hm (by simp)
  | _ :: _, _, 0, _, _, hm => absurd hm (by simp)
  | [], _, _ + 1, _, _, _ => by simp [exec]
  | i :: is, cs, m + 1, s, hc, hm => by
      have hhd : cs.headD .returns = .returns := by
        cases cs with
        | nil => rfl
        | cons c cs => exact hc c List.mem_cons_self
      have htl : ∀ c ∈ cs.tail, c = .returns := fun c h => hc c (List.mem_of_mem_tail h)
      simp only [List.length_cons] at hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [exec, hhd]
      rw [exec_calls_returns v h is cs.tail (k + 1) s htl (by omega)]
      simp

theorem RevertingCallRevertsTheExecution : Properties.RevertingCallRevertsTheExecution := by
  intro v n b ok cs s hr
  have hr' : Callee.reverts ∈ cs.take (List.range b.calls).length := by simpa using hr
  refine ⟨?_, ?_⟩
  · cases n with
    | zero => simp [exec]
    | succ n =>
      simp only [exec]
      split_ifs
      · rw [exec_calls_reverts v b.hash _ cs n _ hr']
      · rfl
  · cases n with
    | zero => simp [exec]
    | succ n =>
      simp only [exec]
      split_ifs
      · rw [exec_calls_reverts v b.hash _ cs n _ hr']
      · rfl

/-- From an `Unreceived` state, atomic execution whose targets return succeeds. -/
lemma exec_atomic_returns {s : State} {b : Bundle} (hu : s.bundle b.hash = .Unreceived) :
    exec .deployed (b.calls + 2)
        (.entry (.executeAtomicBundle b true) (List.replicate b.calls .returns)) s =
      some (beforeCalls .deployed b s,
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]) := by
  show exec .deployed (b.calls + 1 + 1) _ s = _
  simp only [exec, hu, and_self, ↓reduceIte]
  rw [exec_calls_returns .deployed b.hash _ _ _ _ (fun c hc => (List.mem_replicate.1 hc).2)
    (by simp)]
  rfl

theorem FailedAttemptCanBeRetried : Properties.FailedAttemptCanBeRetried := by
  intro s b fuel cs hu hr
  refine ⟨?_, ?_⟩
  · simp only [submit]
    rw [(RevertingCallRevertsTheExecution .deployed fuel b true cs s hr).1]
    rfl
  · simp only [submit]
    rw [exec_atomic_returns hu]
    rfl

theorem FailedAttemptRetryWitness : Properties.FailedAttemptRetryWitness := by
  unfold Properties.FailedAttemptRetryWitness; decide

theorem CaughtReentrantRevertWitness : Properties.CaughtReentrantRevertWitness := by
  unfold Properties.CaughtReentrantRevertWitness; decide

/-! ## (c) The order of the writes is load-bearing -/

theorem StatusWriteAfterCallsRunsTwice : Properties.StatusWriteAfterCallsRunsTwice := by
  unfold Properties.StatusWriteAfterCallsRunsTwice; decide

theorem CallWriteAfterCallsRunsTwice : Properties.CallWriteAfterCallsRunsTwice := by
  unfold Properties.CallWriteAfterCallsRunsTwice; decide

/-! ### The general countermodels

The same transactions for every bundle and every admitting state, computed symbolically: the
first call's target re-enters, every other target returns. -/

/-- A target that calls `e` and then returns, where `e` commits. -/
lemma exec_reenter {v : Variant} {e : Entry} {caught : Bool} {m : ℕ} {s s₁ : State}
    {l₁ : List Effect} (he : exec v m (.entry e []) s = some (s₁, l₁)) :
    exec v (m + 1) (.target (reenter e caught)) s = some (s₁, l₁) := by
  have hm : ∃ m', m = m' + 1 := by
    cases m with
    | zero => simp [exec] at he
    | succ m' => exact ⟨m', rfl⟩
  obtain ⟨m', rfl⟩ := hm
  simp only [reenter, exec, he, List.append_nil]

/-- A target that calls `e`, where `e` reverts, and does not catch the failure. -/
lemma exec_reenter_uncaught {v : Variant} {e : Entry} {m : ℕ} {s : State}
    (he : exec v m (.entry e []) s = none) :
    exec v (m + 1) (.target (reenter e false)) s = none := by
  simp only [reenter, exec, he]
  rfl

/-- A call loop over calls `0, …, k` whose first target re-enters `e`, which commits, and whose
other targets return. -/
lemma loop_reenter_first {v : Variant} {h : BundleHash} {k c : ℕ} (hc : k < c + 2) {e : Entry}
    {t u : State} {l : List Effect} (he : exec v (c + 1) (.entry e []) t = some (u, l)) :
    exec v (c + 3) (.calls h (List.range (k + 1)) [reenter e false]) t =
      some (u, Effect.delivered h 0 ::
        (l ++ ((List.range k).map Nat.succ).map (Effect.delivered h))) := by
  have e3 : exec v (c + 2) (.target (reenter e false)) t = some (u, l) := exec_reenter he
  have e4 : exec v (c + 2) (.calls h ((List.range k).map Nat.succ) []) u =
      some (u, ((List.range k).map Nat.succ).map (Effect.delivered h)) :=
    exec_calls_returns _ _ _ _ _ _ (by simp) (by simpa using hc)
  conv_lhs => rw [List.range_succ_eq_map]
  simp only [exec, List.headD_cons, List.tail_cons, e3, e4]

/-- A call loop whose first target reverts reverts. -/
lemma loop_first_fails {v : Variant} {h : BundleHash} {i : ℕ} {is : List ℕ} {c₀ : Callee}
    {cs : List Callee} {m : ℕ} {t : State} (h₀ : exec v m (.target c₀) t = none) :
    exec v (m + 1) (.calls h (i :: is) (c₀ :: cs)) t = none := by
  simp only [exec, List.headD_cons, h₀]

lemma late_atomic_twice (s : State) (b : Bundle) (hpos : 0 < b.calls)
    (hu : s.bundle b.hash = .Unreceived) :
    ¬ (submit .statusWriteAfterCalls s ⟨b.calls + 5, .executeAtomicBundle b true,
          [reenter (.executeAtomicBundle b true) false]⟩).2.Nodup := by
  obtain ⟨h, n⟩ := b
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hpos; omega⟩
  simp only at hu
  set b : Bundle := ⟨h, k + 1⟩ with hb
  set t := beforeCalls .statusWriteAfterCalls b s with ht
  have htu : t.bundle h = .Unreceived := by simpa [ht, beforeCalls] using hu
  -- the re-entrant execution, from the state the outer calls run against
  have e2 : exec .statusWriteAfterCalls (k + 2 + 1) (.entry (.executeAtomicBundle b true) []) t =
      some (afterCalls .statusWriteAfterCalls b (beforeCalls .statusWriteAfterCalls b t),
        (List.range (k + 1)).map (Effect.delivered h) ++ [Effect.executed h]) := by
    simp only [exec, hb, htu, and_self, ↓reduceIte]
    rw [exec_calls_returns _ _ _ _ _ _ (by simp) (by simp)]
  have e5 := loop_reenter_first (h := h) (k := k) (by omega) e2
  have e6 : exec .statusWriteAfterCalls (b.calls + 5) (.entry (.executeAtomicBundle b true)
      [reenter (.executeAtomicBundle b true) false]) s = some (afterCalls .statusWriteAfterCalls b
        (afterCalls .statusWriteAfterCalls b (beforeCalls .statusWriteAfterCalls b t)),
        (Effect.delivered h 0 :: (((List.range (k + 1)).map (Effect.delivered h) ++
          [Effect.executed h]) ++ ((List.range k).map Nat.succ).map (Effect.delivered h))) ++
          [Effect.executed h]) := by
    show exec .statusWriteAfterCalls (k + 1 + 4 + 1) _ s = _
    simp only [exec, hb, hu, and_self, ↓reduceIte]
    rw [← hb, ← ht, e5]
  simp only [submit, e6, commit]
  intro hnd
  rw [List.cons_append, List.nodup_cons] at hnd
  exact hnd.1 (by simp)

lemma late_public_twice (s : State) (b : Bundle) (hpos : 0 < b.calls)
    (hopen : s.bundle b.hash = .Unreceived ∨ s.bundle b.hash = .Verified) :
    ¬ (submit .statusWriteAfterCalls s ⟨b.calls + 5, .executeBundle b true,
          [reenter (.executeBundle b false) false]⟩).2.Nodup := by
  obtain ⟨h, n⟩ := b
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at hpos; omega⟩
  simp only at hopen
  set b : Bundle := ⟨h, k + 1⟩ with hb
  set t := beforeCalls .statusWriteAfterCalls b (s.verifyIfUnreceived h) with ht
  have htv : t.bundle h = .Verified := by
    rcases hopen with hu | hv
    · simp [ht, beforeCalls, State.verifyIfUnreceived, hu]
    · simp [ht, beforeCalls, State.verifyIfUnreceived, hv]
  have htv' : t.verifyIfUnreceived h = t := by simp [State.verifyIfUnreceived, htv]
  -- the re-entrant execution needs no proof: the outer call already wrote `Verified`
  have e2 : exec .statusWriteAfterCalls (k + 2 + 1) (.entry (.executeBundle b false) []) t =
      some (afterCalls .statusWriteAfterCalls b (beforeCalls .statusWriteAfterCalls b t),
        (List.range (k + 1)).map (Effect.delivered h) ++ [Effect.executed h]) := by
    simp only [exec, hb, htv, true_or, ↓reduceIte, htv']
    rw [exec_calls_returns _ _ _ _ _ _ (by simp) (by simp)]
  have e5 := loop_reenter_first (h := h) (k := k) (by omega) e2
  have hg : s.bundle h = .Verified ∨ (s.bundle h = .Unreceived ∧ True) := by
    rcases hopen with hu | hv
    · exact Or.inr ⟨hu, trivial⟩
    · exact Or.inl hv
  have e6 : exec .statusWriteAfterCalls (b.calls + 5) (.entry (.executeBundle b true)
      [reenter (.executeBundle b false) false]) s = some (afterCalls .statusWriteAfterCalls b
        (afterCalls .statusWriteAfterCalls b (beforeCalls .statusWriteAfterCalls b t)),
        (Effect.delivered h 0 :: (((List.range (k + 1)).map (Effect.delivered h) ++
          [Effect.executed h]) ++ ((List.range k).map Nat.succ).map (Effect.delivered h))) ++
          [Effect.executed h]) := by
    show exec .statusWriteAfterCalls (k + 1 + 4 + 1) _ s = _
    simp only [exec, hb, hg, ↓reduceIte]
    rw [← hb, ← ht, e5]
  simp only [submit, e6, commit]
  intro hnd
  rw [List.cons_append, List.nodup_cons] at hnd
  exact hnd.1 (by simp)

lemma deployed_atomic_reverts (s : State) (b : Bundle) (hpos : 0 < b.calls)
    (hu : s.bundle b.hash = .Unreceived) :
    submit .deployed s ⟨b.calls + 5, .executeAtomicBundle b true,
          [reenter (.executeAtomicBundle b true) false]⟩ = (s, []) := by
  have hfe : (beforeCalls .deployed b s).bundle b.hash = .FullyExecuted := by simp
  have hnested : ∀ m, exec .deployed m (.entry (.executeAtomicBundle b true) [])
      (beforeCalls .deployed b s) = none := by
    intro m
    cases m with
    | zero => simp [exec]
    | succ m => simp only [exec, hfe]; simp
  obtain ⟨k, hk⟩ : ∃ k, b.calls = k + 1 := ⟨b.calls - 1, by omega⟩
  have hloop : exec .deployed (b.calls + 4) (.calls b.hash (List.range b.calls)
      [reenter (.executeAtomicBundle b true) false]) (beforeCalls .deployed b s) = none := by
    rw [hk, List.range_succ_eq_map]
    exact loop_first_fails (exec_reenter_uncaught (hnested _))
  simp only [submit]
  show commit s (exec .deployed (b.calls + 4 + 1) _ s) = _
  simp only [exec, hu, and_self, ↓reduceIte, hloop]
  rfl

theorem StatusWriteAfterCallsRunsAnyBundleTwice :
    Properties.StatusWriteAfterCallsRunsAnyBundleTwice :=
  fun s b hpos =>
    ⟨fun hu => ⟨late_atomic_twice s b hpos hu, deployed_atomic_reverts s b hpos hu⟩,
      late_public_twice s b hpos⟩

lemma markCalls_skip (w : Bool) (h : BundleHash) :
    ∀ (j i : ℕ) (u : State), markCalls w h i (List.replicate j .Unprocessed) u = some u
  | 0, _, _ => rfl
  | j + 1, i, u => by
      simp only [List.replicate_succ, markCalls]
      exact markCalls_skip w h j (i + 1) u

lemma toExecute_skip : ∀ (j i : ℕ), toExecute i (List.replicate j .Unprocessed) = []
  | 0, _ => rfl
  | j + 1, i => by
      simp only [List.replicate_succ, toExecute]
      exact toExecute_skip j (i + 1)

lemma markCalls_requestFirst (w : Bool) (h : BundleHash) (n : ℕ) (u : State)
    (hu : u.call h 0 = .Unprocessed) :
    markCalls w h 0 (requestFirst n) u = some (if w then u.setCall h 0 .Executed else u) := by
  simp only [requestFirst, markCalls, hu, ↓reduceIte, zero_add]
  exact markCalls_skip w h _ 1 _

lemma markCalls_requestFirst_executed (h : BundleHash) (n : ℕ) (u : State)
    (hx : u.call h 0 = .Executed) : markCalls true h 0 (requestFirst n) u = none := by
  simp [requestFirst, markCalls, hx]

lemma requestFirst_length {n : ℕ} (hpos : 0 < n) : (requestFirst n).length = n := by
  simp [requestFirst]; omega

lemma toExecute_requestFirst (n : ℕ) : toExecute 0 (requestFirst n) = [0] := by
  simp [requestFirst, toExecute, toExecute_skip]

lemma late_unbundle_twice (s : State) (b : Bundle) (hpos : 0 < b.calls)
    (hg : s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled)
    (hc : s.call b.hash 0 = .Unprocessed) :
    (submit .callWriteAfterCalls s ⟨6, .unbundleBundle b (requestFirst b.calls),
        [reenter (.unbundleBundle b (requestFirst b.calls)) false]⟩).2 =
      [.delivered b.hash 0, .delivered b.hash 0] := by
  have hm₁ := markCalls_requestFirst false b.hash b.calls (s.setBundle b.hash .Unbundled)
    (by simpa using hc)
  have hm₂ := markCalls_requestFirst false b.hash b.calls
    ((s.setBundle b.hash .Unbundled).setBundle b.hash .Unbundled) (by simpa using hc)
  simp only [Bool.false_eq_true, ↓reduceIte] at hm₁ hm₂
  simp [submit, exec, reenter, requestFirst_length hpos, hg, toExecute_requestFirst, hm₁, hm₂,
    writesCallsFirst, commit]

lemma deployed_unbundle_reverts (s : State) (b : Bundle) (hpos : 0 < b.calls)
    (hg : s.bundle b.hash = .Verified ∨ s.bundle b.hash = .Unbundled)
    (hc : s.call b.hash 0 = .Unprocessed) :
    submit .deployed s ⟨6, .unbundleBundle b (requestFirst b.calls),
        [reenter (.unbundleBundle b (requestFirst b.calls)) false]⟩ = (s, []) := by
  have hm₁ := markCalls_requestFirst true b.hash b.calls (s.setBundle b.hash .Unbundled)
    (by simpa using hc)
  have hm₂ := markCalls_requestFirst_executed b.hash b.calls
    (((s.setBundle b.hash .Unbundled).setCall b.hash 0 .Executed).setBundle b.hash .Unbundled)
    (by simp)
  simp only [↓reduceIte] at hm₁
  simp [submit, exec, reenter, requestFirst_length hpos, hg, toExecute_requestFirst, hm₁, hm₂,
    writesCallsFirst, commit]

theorem CallWriteAfterCallsRunsAnyCallTwice : Properties.CallWriteAfterCallsRunsAnyCallTwice :=
  fun s b hpos hg hc =>
    ⟨late_unbundle_twice s b hpos hg hc, deployed_unbundle_reverts s b hpos hg hc⟩

end Contracts.InteropHandler
