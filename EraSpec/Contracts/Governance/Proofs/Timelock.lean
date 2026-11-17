import EraSpec.Contracts.Governance.Properties.Timelock
import Mathlib.Tactic

/-!
# Proofs: what the `Governance` timelock guarantees, across re-entrant execution

Three invariants of committed frames, proved together by induction on the budget
(`exec_inv`), in the deployed order:

* `Track` holds for every frame kind and composes along a frame's sub-frames and along a
  sequence of transactions (`Track.append`). It says that `Done` is permanent and, when it
  newly holds, is explained by a logged execution or a logged sentinel schedule. Every pending
  timestamp is explained by the last logged schedule, or is unchanged. Every logged execution
  had its predecessor done, and was admitted by a pending, and on the delayed path ready,
  timestamp, explained the same way. Every logged cancel is followed by a schedule, or leaves
  the id `Unset`.
* `Once` (entry points and targets) and `LoopOnce` (call loops) carry the once-only argument
  of `InteropHandlerBase/Reentrancy`. Every delivery or execution an entry point commits was
  open where it started and is `Done` where it ended. Inside a call loop that ends with its
  own id still open, which the re-check requires, nothing nested touched that id.
* `TimeOk`, `CfgOk` and `Followed`: schedules carry the transaction's time; only executions
  change the configuration; every delivery is followed by its execution.

The run results lift them along `submitAll`. `Done` is permanent in either order by a
separate induction (`exec_doneMono`). The concrete witnesses and countermodels are evaluated
by `decide`; the general countermodel `WithoutRecheckAnyOpRunsTwice` is the same computation
done symbolically, from a loop lemma (`exec_loop_returns`).
-/

namespace Contracts.Governance

/-! ## State updates and the operation state -/

@[simp] lemma EXECUTED_eq : EXECUTED = 1 := rfl

@[simp] lemma setTs_ts (s : State) (x y : OpId) (t : ℕ) :
    (s.setTs x t).ts y = if y = x then t else s.ts y := rfl

@[simp] lemma setTs_owner (s : State) (x : OpId) (t : ℕ) : (s.setTs x t).owner = s.owner := rfl

@[simp] lemma setTs_pendingOwner (s : State) (x : OpId) (t : ℕ) :
    (s.setTs x t).pendingOwner = s.pendingOwner := rfl

@[simp] lemma setTs_council (s : State) (x : OpId) (t : ℕ) :
    (s.setTs x t).council = s.council := rfl

@[simp] lemma setTs_minDelay (s : State) (x : OpId) (t : ℕ) :
    (s.setTs x t).minDelay = s.minDelay := rfl

lemma opState_Unset {s : State} {τ : ℕ} {x : OpId} : s.opState τ x = .Unset ↔ s.ts x = 0 := by
  unfold State.opState; split_ifs <;> simp_all

lemma opState_Done {s : State} {τ : ℕ} {x : OpId} : s.opState τ x = .Done ↔ s.ts x = 1 := by
  unfold State.opState; split_ifs <;> simp_all

lemma opState_Ready {s : State} {τ : ℕ} {x : OpId} :
    s.opState τ x = .Ready ↔ s.ts x ≠ 0 ∧ s.ts x ≠ 1 ∧ s.ts x ≤ τ := by
  unfold State.opState; split_ifs <;> simp_all

lemma isPending_iff {s : State} {τ : ℕ} {x : OpId} :
    s.isPending τ x ↔ s.ts x ≠ 0 ∧ s.ts x ≠ 1 := by
  unfold State.isPending State.opState; split_ifs <;> simp_all

lemma predecessorDone_iff {s : State} {τ : ℕ} {p : OpId} :
    s.predecessorDone τ p ↔ p = 0 ∨ s.ts p = 1 := by
  unfold State.predecessorDone; rw [opState_Done]

lemma schedule_eq_some {τ : ℕ} {s : State} {x : OpId} {d : ℕ} {o : Option Operation}
    {s' : State} {l : List Effect} :
    schedule τ s x d o = some (s', l) ↔
      s.ts x = 0 ∧ s.minDelay ≤ d ∧ τ + d < UInt256.size ∧ s' = s.setTs x (τ + d) ∧
        l = [.scheduled x τ d s.minDelay o] := by
  unfold schedule
  simp only [opState_Unset]
  constructor
  · intro h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hc.1, hc.2.1, hc.2.2, h.1.symm, h.2.symm⟩
  · rintro ⟨h1, h2, h3, rfl, rfl⟩
    simp only [h1, h2, h3, and_self, ↓reduceIte]

/-! ## Reading the log -/

lemma lastSchedule_append (x : OpId) (l₁ l₂ : List Effect) :
    lastSchedule x (l₁ ++ l₂) = (lastSchedule x l₂).or (lastSchedule x l₁) := by
  unfold lastSchedule; rw [List.filterMap_append, List.getLast?_append]

lemma lastSchedule_append_of_none {x : OpId} {l₁ l₂ : List Effect}
    (h : lastSchedule x l₂ = none) : lastSchedule x (l₁ ++ l₂) = lastSchedule x l₁ := by
  rw [lastSchedule_append, h]; rfl

lemma lastSchedule_append_of_some {x : OpId} {l₁ l₂ : List Effect} {r : SchedRec}
    (h : lastSchedule x l₂ = some r) : lastSchedule x (l₁ ++ l₂) = some r := by
  rw [lastSchedule_append, h]; rfl

@[simp] lemma lastSchedule_nil (x : OpId) : lastSchedule x [] = none := rfl

lemma lastSchedule_cons_of_none {x : OpId} {e : Effect} {l : List Effect}
    (h : e.schedOf x = none) : lastSchedule x (e :: l) = lastSchedule x l := by
  unfold lastSchedule; rw [List.filterMap_cons, h]

lemma lastSchedule_of_quiet {x : OpId} {l : List Effect}
    (h : ∀ e ∈ l, e.schedOf x = none) : lastSchedule x l = none := by
  unfold lastSchedule
  rw [List.getLast?_eq_none_iff, List.filterMap_eq_nil_iff]
  intro e he; exact h e he

lemma mem_of_lastSchedule {x : OpId} {l : List Effect} {r : SchedRec}
    (h : lastSchedule x l = some r) : Effect.scheduled x r.time r.delay r.minDelay r.op ∈ l := by
  unfold lastSchedule at h
  obtain ⟨e, he, hs⟩ := List.mem_filterMap.1 (List.mem_of_getLast? h)
  cases e with
  | scheduled y t d m o =>
    simp only [Effect.schedOf] at hs
    split_ifs at hs with hy
    simp only [Option.some.injEq] at hs
    subst hy; subst hs; exact he
  | _ => simp [Effect.schedOf] at hs

lemma lastSchedule_scheduled_self (x : OpId) (t d m : ℕ) (o : Option Operation) :
    lastSchedule x [.scheduled x t d m o] = some ⟨t, d, m, o⟩ := by
  simp [lastSchedule, Effect.schedOf]

lemma lastSchedule_scheduled_other {x y : OpId} (t d m : ℕ) (o : Option Operation)
    (h : y ≠ x) : lastSchedule y [.scheduled x t d m o] = none := by
  simp [lastSchedule, Effect.schedOf, Ne.symm h]

/-- Where an entry sits in a concatenation. -/
private lemma append_eq_append_cons {α : Type} {l₁ l₂ a b : List α} {e : α}
    (h : l₁ ++ l₂ = a ++ e :: b) :
    (∃ b', l₁ = a ++ e :: b' ∧ b = b' ++ l₂) ∨ (∃ a', l₂ = a' ++ e :: b ∧ a = l₁ ++ a') := by
  rcases List.append_eq_append_iff.1 h with ⟨as, h1, h2⟩ | ⟨bs, h1, h2⟩
  · exact Or.inr ⟨as, h2, h1⟩
  · rcases bs with _ | ⟨e', bs⟩
    · simp only [List.append_nil, List.nil_append] at h1 h2
      exact Or.inr ⟨[], by simpa using h2.symm, by simp [h1]⟩
    · simp only [List.cons_append, List.cons.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact Or.inl ⟨bs, h1, rfl⟩

/-- Where an entry sits in a list with a head. -/
private lemma cons_eq_append_cons {α : Type} {x : α} {l a b : List α} {e : α}
    (h : x :: l = a ++ e :: b) :
    (a = [] ∧ x = e ∧ l = b) ∨ ∃ a', a = x :: a' ∧ l = a' ++ e :: b := by
  rcases a with _ | ⟨y, a'⟩
  · simp only [List.nil_append, List.cons.injEq] at h
    exact Or.inl ⟨rfl, h.1, h.2⟩
  · simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    exact Or.inr ⟨a', rfl, h⟩

/-! ## The `Track` invariant -/

/-- A schedule entry for `y` that respects the delay rule and, if transparent, has id `y`. -/
def SchedGood (E : Env) (y : OpId) (r : SchedRec) : Prop :=
  r.minDelay ≤ r.delay ∧ ∀ op₀, r.op = some op₀ → E.H op₀ = y

/-- What every committed frame satisfies, from `s` to `s'` committing `l`. -/
structure Track (E : Env) (s s' : State) (l : List Effect) : Prop where
  doneMono : ∀ y, s.ts y = 1 → s'.ts y = 1
  doneLogged : ∀ y, s'.ts y = 1 → s.ts y = 1 ∨ (∃ op t b, Effect.executed y op t b ∈ l) ∨
    ∃ t d m o, Effect.scheduled y t d m o ∈ l ∧ t + d = 1
  predOk : ∀ l₁ l₂ y op t b, l = l₁ ++ .executed y op t b :: l₂ → op.predecessor ≠ 0 →
    s.ts op.predecessor = 1 ∨ (∃ op' t' b', Effect.executed op.predecessor op' t' b' ∈ l₁) ∨
    ∃ t d m o, Effect.scheduled op.predecessor t d m o ∈ l₁ ∧ t + d = 1
  schedTrack : ∀ y, s'.ts y ≠ 0 → s'.ts y ≠ 1 →
    (s'.ts y = s.ts y ∧ lastSchedule y l = none) ∨
    ∃ r, lastSchedule y l = some r ∧ SchedGood E y r ∧ r.time + r.delay = s'.ts y
  execWitness : ∀ l₁ l₂ y op t b, l = l₁ ++ .executed y op t b :: l₂ →
    y = E.H op ∧
    ((s.ts y ≠ 0 ∧ s.ts y ≠ 1 ∧ lastSchedule y l₁ = none ∧ (b = false → s.ts y ≤ t)) ∨
     ∃ r, lastSchedule y l₁ = some r ∧ SchedGood E y r ∧ (b = false → r.time + r.delay ≤ t))
  cancelTrack : ∀ l₁ l₂ y, l = l₁ ++ .cancelled y :: l₂ →
    s'.ts y = 0 ∨ ∃ t d m o, Effect.scheduled y t d m o ∈ l₂

lemma Track.refl (E : Env) (s : State) : Track E s s [] where
  doneMono _ h := h
  doneLogged _ h := Or.inl h
  predOk l₁ l₂ _ _ _ _ h := by simp at h
  schedTrack y h0 h1 := Or.inl ⟨rfl, rfl⟩
  execWitness l₁ l₂ _ _ _ _ h := by simp at h
  cancelTrack l₁ l₂ _ h := by simp at h

/-- A frame that started with `y` unset either leaves it unset or logged a schedule of it. -/
lemma Track.unset {E : Env} {s s' : State} {l : List Effect} (g : Track E s s' l) {y : OpId}
    (h0 : s.ts y = 0) : s'.ts y = 0 ∨ ∃ t d m o, Effect.scheduled y t d m o ∈ l := by
  by_cases hz : s'.ts y = 0
  · exact Or.inl hz
  right
  by_cases h1 : s'.ts y = 1
  · rcases g.doneLogged y h1 with h | ⟨op, t, b, he⟩ | ⟨t, d, m, o, hm, _⟩
    · omega
    · obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem he
      rcases (g.execWitness l₁ l₂ y op t b rfl).2 with ⟨h, _⟩ | ⟨r, hr, _⟩
      · exact absurd h0 h
      · exact ⟨_, _, _, _, List.mem_append_left _ (mem_of_lastSchedule hr)⟩
    · exact ⟨t, d, m, o, hm⟩
  · rcases g.schedTrack y hz h1 with ⟨h, _⟩ | ⟨r, hr, _⟩
    · exact absurd (h.trans h0) hz
    · exact ⟨_, _, _, _, mem_of_lastSchedule hr⟩

lemma Track.append {E : Env} {s s₁ s₂ : State} {l₁ l₂ : List Effect} (g₁ : Track E s s₁ l₁)
    (g₂ : Track E s₁ s₂ l₂) : Track E s s₂ (l₁ ++ l₂) where
  doneMono y h := g₂.doneMono y (g₁.doneMono y h)
  doneLogged y h := by
    rcases g₂.doneLogged y h with h' | ⟨op, t, b, he⟩ | ⟨t, d, m, o, hm, ht⟩
    · rcases g₁.doneLogged y h' with h'' | ⟨op, t, b, he⟩ | ⟨t, d, m, o, hm, ht⟩
      · exact Or.inl h''
      · exact Or.inr (Or.inl ⟨op, t, b, List.mem_append_left _ he⟩)
      · exact Or.inr (Or.inr ⟨t, d, m, o, List.mem_append_left _ hm, ht⟩)
    · exact Or.inr (Or.inl ⟨op, t, b, List.mem_append_right _ he⟩)
    · exact Or.inr (Or.inr ⟨t, d, m, o, List.mem_append_right _ hm, ht⟩)
  predOk a c y op t b h hp := by
    rcases append_eq_append_cons h with ⟨c', h1, _⟩ | ⟨a', h1, rfl⟩
    · exact g₁.predOk a c' y op t b h1 hp
    · rcases g₂.predOk a' c y op t b h1 hp with h' | ⟨op', t', b', he⟩ | ⟨t₀, d, m, o, hm, ht⟩
      · rcases g₁.doneLogged _ h' with h'' | ⟨op', t', b', he⟩ | ⟨t₀, d, m, o, hm, ht⟩
        · exact Or.inl h''
        · exact Or.inr (Or.inl ⟨op', t', b', List.mem_append_left _ he⟩)
        · exact Or.inr (Or.inr ⟨t₀, d, m, o, List.mem_append_left _ hm, ht⟩)
      · exact Or.inr (Or.inl ⟨op', t', b', List.mem_append_right _ he⟩)
      · exact Or.inr (Or.inr ⟨t₀, d, m, o, List.mem_append_right _ hm, ht⟩)
  schedTrack y h0 h1 := by
    rcases g₂.schedTrack y h0 h1 with ⟨he, hn⟩ | ⟨r, hr, hg, ht⟩
    · rw [lastSchedule_append_of_none hn]
      rcases g₁.schedTrack y (he ▸ h0) (he ▸ h1) with ⟨he', hn'⟩ | ⟨r, hr, hg, ht⟩
      · exact Or.inl ⟨he.trans he', hn'⟩
      · exact Or.inr ⟨r, hr, hg, ht.trans he.symm⟩
    · exact Or.inr ⟨r, lastSchedule_append_of_some hr, hg, ht⟩
  execWitness a c y op t b h := by
    rcases append_eq_append_cons h with ⟨c', h1, _⟩ | ⟨a', h1, rfl⟩
    · exact g₁.execWitness a c' y op t b h1
    · obtain ⟨hy, hw⟩ := g₂.execWitness a' c y op t b h1
      refine ⟨hy, ?_⟩
      rcases hw with ⟨hp0, hp1, hn, hle⟩ | ⟨r, hr, hg, ht⟩
      · rw [lastSchedule_append_of_none hn]
        rcases g₁.schedTrack y hp0 hp1 with ⟨he, hn'⟩ | ⟨r, hr, hg, ht⟩
        · exact Or.inl ⟨he ▸ hp0, he ▸ hp1, hn', fun hb => he ▸ hle hb⟩
        · exact Or.inr ⟨r, hr, hg, fun hb => ht ▸ hle hb⟩
      · exact Or.inr ⟨r, lastSchedule_append_of_some hr, hg, ht⟩
  cancelTrack a c y h := by
    rcases append_eq_append_cons h with ⟨c', h1, rfl⟩ | ⟨a', h1, rfl⟩
    · rcases g₁.cancelTrack a c' y h1 with h0 | ⟨t, d, m, o, hm⟩
      · rcases g₂.unset h0 with h0' | ⟨t, d, m, o, hm⟩
        · exact Or.inl h0'
        · exact Or.inr ⟨t, d, m, o, List.mem_append_right _ hm⟩
      · exact Or.inr ⟨t, d, m, o, List.mem_append_left _ hm⟩
    · exact g₂.cancelTrack a' c y h1

/-- A delivery entry in front changes nothing the invariant reads. -/
lemma Track.cons_delivered {E : Env} {s s' : State} {l : List Effect} (g : Track E s s' l)
    (x : OpId) (i : ℕ) : Track E s s' (.delivered x i :: l) where
  doneMono := g.doneMono
  doneLogged y h := by
    rcases g.doneLogged y h with h' | ⟨op, t, b, he⟩ | ⟨t, d, m, o, hm, ht⟩
    · exact Or.inl h'
    · exact Or.inr (Or.inl ⟨op, t, b, List.mem_cons_of_mem _ he⟩)
    · exact Or.inr (Or.inr ⟨t, d, m, o, List.mem_cons_of_mem _ hm, ht⟩)
  predOk a c y op t b h hp := by
    rcases cons_eq_append_cons h with ⟨_, h', _⟩ | ⟨a', rfl, h1⟩
    · cases h'
    · rcases g.predOk a' c y op t b h1 hp with h' | ⟨op', t', b', he⟩ | ⟨t₀, d, m, o, hm, ht⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl ⟨op', t', b', List.mem_cons_of_mem _ he⟩)
      · exact Or.inr (Or.inr ⟨t₀, d, m, o, List.mem_cons_of_mem _ hm, ht⟩)
  schedTrack y h0 h1 := by
    rw [lastSchedule_cons_of_none (by simp [Effect.schedOf])]
    exact g.schedTrack y h0 h1
  execWitness a c y op t b h := by
    rcases cons_eq_append_cons h with ⟨_, h', _⟩ | ⟨a', rfl, h1⟩
    · cases h'
    · rw [lastSchedule_cons_of_none (by simp [Effect.schedOf])]
      exact g.execWitness a' c y op t b h1
  cancelTrack a c y h := by
    rcases cons_eq_append_cons h with ⟨_, h', _⟩ | ⟨a', rfl, h1⟩
    · cases h'
    · exact g.cancelTrack a' c y h1

/-! ## `Track` for each entry point -/

/-- A one-entry log has its entry at the front. -/
private lemma singleton_eq_append_cons {α : Type} {e e' : α} {a b : List α}
    (h : [e] = a ++ e' :: b) :
    a = [] ∧ e = e' ∧ b = [] := by
  rcases a with _ | ⟨y, a'⟩
  · simp only [List.nil_append, List.cons.injEq] at h
    exact ⟨rfl, h.1, h.2.symm⟩
  · simp only [List.cons_append, List.cons.injEq] at h
    exact absurd h.2.symm (by simp)

lemma track_schedule {E : Env} {τ : ℕ} {s s' : State} {x : OpId} {d : ℕ}
    {o : Option Operation} {l : List Effect} (h : schedule τ s x d o = some (s', l))
    (ho : ∀ op₀, o = some op₀ → E.H op₀ = x) : Track E s s' l := by
  obtain ⟨h0, hm, _, rfl, rfl⟩ := schedule_eq_some.1 h
  exact {
    doneMono := fun y hy => by
      by_cases hyx : y = x
      · subst hyx; omega
      · simpa [hyx] using hy
    doneLogged := fun y hy => by
      by_cases hyx : y = x
      · subst hyx
        simp only [setTs_ts, ↓reduceIte] at hy
        exact Or.inr (Or.inr ⟨τ, d, s.minDelay, o, List.mem_singleton_self _, hy⟩)
      · exact Or.inl (by simpa [hyx] using hy)
    predOk := fun a c y op t b h _ => by
      obtain ⟨_, he, _⟩ := singleton_eq_append_cons h; cases he
    schedTrack := fun y h0' h1' => by
      by_cases hyx : y = x
      · subst hyx
        refine Or.inr ⟨⟨τ, d, s.minDelay, o⟩, lastSchedule_scheduled_self _ _ _ _ _,
          ⟨hm, ho⟩, by simp⟩
      · exact Or.inl ⟨by simp [hyx], lastSchedule_scheduled_other _ _ _ _ hyx⟩
    execWitness := fun a c y op t b h => by
      obtain ⟨_, he, _⟩ := singleton_eq_append_cons h; cases he
    cancelTrack := fun a c y h => by
      obtain ⟨_, he, _⟩ := singleton_eq_append_cons h; cases he }

lemma track_cancel {E : Env} {s : State} {x : OpId} (hp : s.ts x ≠ 0 ∧ s.ts x ≠ 1) :
    Track E s (s.setTs x 0) [.cancelled x] where
  doneMono y hy := by
    by_cases hyx : y = x
    · subst hyx; exact absurd hy hp.2
    · simpa [hyx] using hy
  doneLogged y hy := by
    by_cases hyx : y = x
    · subst hyx; simp at hy
    · exact Or.inl (by simpa [hyx] using hy)
  predOk a c y op t b h _ := by
    obtain ⟨_, he, _⟩ := singleton_eq_append_cons h; cases he
  schedTrack y h0 h1 := by
    by_cases hyx : y = x
    · subst hyx; simp at h0
    · exact Or.inl ⟨by simp [hyx], rfl⟩
  execWitness a c y op t b h := by
    obtain ⟨_, he, _⟩ := singleton_eq_append_cons h; cases he
  cancelTrack a c y h := by
    obtain ⟨_, he, _⟩ := singleton_eq_append_cons h
    cases he; exact Or.inl (by simp)

/-- The entries that carry no operation: configuration and ownership events. -/
def Effect.Quiet : Effect → Prop
  | .minDelayChanged _ _ => True
  | .councilChanged _ _ => True
  | .ownershipTransferStarted _ => True
  | .ownershipTransferred _ => True
  | _ => False

lemma track_quiet {E : Env} {s s' : State} {l : List Effect} (hts : s'.ts = s.ts)
    (hq : ∀ e ∈ l, e.Quiet) : Track E s s' l where
  doneMono y hy := by rw [hts]; exact hy
  doneLogged y hy := Or.inl (by rw [← hts]; exact hy)
  predOk a c y op t b h _ := by
    have := hq _ (h ▸ List.mem_append_right _ List.mem_cons_self); exact this.elim
  schedTrack y _ _ := Or.inl ⟨by rw [hts], lastSchedule_of_quiet fun e he => by
    have := hq e he
    cases e <;> simp_all [Effect.Quiet, Effect.schedOf]⟩
  execWitness a c y op t b h := by
    have := hq _ (h ▸ List.mem_append_right _ List.mem_cons_self); exact this.elim
  cancelTrack a c y h := by
    have := hq _ (h ▸ List.mem_append_right _ List.mem_cons_self); exact this.elim

/-- An execution entry: admitted at `s`, its loop committed to `s₂`, re-checked there, and
`Done` written. -/
lemma track_exec {E : Env} {s s₂ : State} {lc : List Effect} {x : OpId} {op : Operation}
    {τ : ℕ} {b : Bool} (g : Track E s s₂ lc) (hx : x = E.H op)
    (hpred : op.predecessor = 0 ∨ s.ts op.predecessor = 1)
    (hp : s.ts x ≠ 0 ∧ s.ts x ≠ 1) (hr : b = false → s.ts x ≤ τ)
    (hp₂ : s₂.ts x ≠ 0 ∧ s₂.ts x ≠ 1) (hr₂ : b = false → s₂.ts x ≤ τ) :
    Track E s (s₂.setTs x 1) (lc ++ [.executed x op τ b]) where
  doneMono y hy := by
    have := g.doneMono y hy
    by_cases hyx : y = x <;> simp [hyx, this]
  doneLogged y hy := by
    by_cases hyx : y = x
    · subst hyx
      exact Or.inr (Or.inl ⟨op, τ, b, List.mem_append_right _ (List.mem_singleton_self _)⟩)
    · have hy₂ : s₂.ts y = 1 := by simpa [hyx] using hy
      rcases g.doneLogged y hy₂ with h' | ⟨op', t, b', he⟩ | ⟨t, d, m, o, hm, ht⟩
      · exact Or.inl h'
      · exact Or.inr (Or.inl ⟨op', t, b', List.mem_append_left _ he⟩)
      · exact Or.inr (Or.inr ⟨t, d, m, o, List.mem_append_left _ hm, ht⟩)
  predOk a c y op' t b' h hp' := by
    rcases append_eq_append_cons h with ⟨c', h1, _⟩ | ⟨a', h1, rfl⟩
    · exact g.predOk a c' y op' t b' h1 hp'
    · obtain ⟨_, he, _⟩ := singleton_eq_append_cons h1
      simp only [Effect.executed.injEq] at he
      obtain ⟨_, rfl, _, _⟩ := he
      exact Or.inl (hpred.resolve_left hp')
  schedTrack y h0 h1 := by
    have hyx : y ≠ x := by rintro rfl; simp at h1
    have hq : lastSchedule y [Effect.executed x op τ b] = none := by
      simp [lastSchedule, Effect.schedOf]
    rw [lastSchedule_append_of_none hq]
    simp only [setTs_ts, hyx, ↓reduceIte] at h0 h1 ⊢
    exact g.schedTrack y h0 h1
  execWitness a c y op' t b' h := by
    rcases append_eq_append_cons h with ⟨c', h1, _⟩ | ⟨a', h1, rfl⟩
    · exact g.execWitness a c' y op' t b' h1
    · obtain ⟨rfl, he, _⟩ := singleton_eq_append_cons h1
      simp only [Effect.executed.injEq] at he
      obtain ⟨rfl, rfl, rfl, rfl⟩ := he
      refine ⟨hx, ?_⟩
      rw [List.append_nil]
      rcases g.schedTrack x hp₂.1 hp₂.2 with ⟨he, hn⟩ | ⟨r, hr', hg, ht⟩
      · exact Or.inl ⟨hp.1, hp.2, hn, hr⟩
      · exact Or.inr ⟨r, hr', hg, fun hb => ht ▸ hr₂ hb⟩
  cancelTrack a c y h := by
    rcases append_eq_append_cons h with ⟨c', h1, rfl⟩ | ⟨a', h1, rfl⟩
    · rcases g.cancelTrack a c' y h1 with h0 | ⟨t, d, m, o, hm⟩
      · have hyx : y ≠ x := by rintro rfl; exact hp₂.1 h0
        exact Or.inl (by simp [hyx, h0])
      · exact Or.inr ⟨t, d, m, o, List.mem_append_left _ hm⟩
    · obtain ⟨_, he, _⟩ := singleton_eq_append_cons h1; cases he

/-! ## The once-only invariants -/

lemma runId_of_runKey {e : Effect} {k : RunKey} (h : e.runKey = some k) : e.runId = some k.id := by
  simp [Effect.runId, h]

/-- What an entry point or a target that committed satisfies. -/
structure Once (s s' : State) (l : List Effect) : Prop where
  fresh : ∀ e ∈ l, ∀ y, e.runId = some y → s.ts y ≠ 1
  spent : ∀ e ∈ l, ∀ y, e.runId = some y → s'.ts y = 1
  nodup : (l.filterMap Effect.runKey).Nodup

lemma Once.refl (s : State) : Once s s [] where
  fresh _ h := by simp at h
  spent _ h := by simp at h
  nodup := List.nodup_nil

lemma once_quiet {s s' : State} {l : List Effect} (hq : ∀ e ∈ l, e.runKey = none) :
    Once s s' l where
  fresh e he y hy := by simp [Effect.runId, hq e he] at hy
  spent e he y hy := by simp [Effect.runId, hq e he] at hy
  nodup := by rw [List.filterMap_eq_nil_iff.2 hq]; exact List.nodup_nil

lemma Once.append {s s₁ s₂ : State} {l₁ l₂ : List Effect} (g₁ : Once s s₁ l₁)
    (dm₁ : ∀ y, s.ts y = 1 → s₁.ts y = 1) (g₂ : Once s₁ s₂ l₂)
    (dm₂ : ∀ y, s₁.ts y = 1 → s₂.ts y = 1) : Once s s₂ (l₁ ++ l₂) where
  fresh e he y hy := by
    rcases List.mem_append.1 he with he | he
    · exact g₁.fresh e he y hy
    · exact fun h => g₂.fresh e he y hy (dm₁ y h)
  spent e he y hy := by
    rcases List.mem_append.1 he with he | he
    · exact dm₂ y (g₁.spent e he y hy)
    · exact g₂.spent e he y hy
  nodup := by
    rw [List.filterMap_append]
    refine List.nodup_append.2 ⟨g₁.nodup, g₂.nodup, ?_⟩
    rintro k hk₁ k' hk₂ rfl
    obtain ⟨e₁, he₁, hk₁⟩ := List.mem_filterMap.1 hk₁
    obtain ⟨e₂, he₂, hk₂⟩ := List.mem_filterMap.1 hk₂
    exact g₂.fresh e₂ he₂ _ (runId_of_runKey hk₂) (g₁.spent e₁ he₁ _ (runId_of_runKey hk₁))

/-- What a call loop of operation `x` over `n` calls numbered from `i` satisfies. Its own
deliveries are not yet `Done` at its end; when its id is still open there, nothing nested
touched that id. -/
structure LoopOnce (x : OpId) (i n : ℕ) (s s' : State) (l : List Effect) : Prop where
  fresh : s'.ts x ≠ 1 → ∀ e ∈ l, ∀ y, e.runId = some y → s.ts y ≠ 1
  spent : ∀ e ∈ l, ∀ y, e.runId = some y → y ≠ x → s'.ts y = 1
  own : s'.ts x ≠ 1 →
    l.filter (fun e => e.runId = some x) = (List.range' i n).map (Effect.delivered x)
  nodup : s'.ts x ≠ 1 → (l.filterMap Effect.runKey).Nodup

lemma LoopOnce.nil (x : OpId) (i : ℕ) (s : State) : LoopOnce x i 0 s s [] where
  fresh _ _ h := by simp at h
  spent _ h := by simp at h
  own _ := by simp
  nodup _ := List.nodup_nil

lemma LoopOnce.cons {x : OpId} {i n : ℕ} {s s₁ s₂ : State} {l₁ l₂ : List Effect}
    (g₁ : Once s s₁ l₁) (dm₁ : ∀ y, s.ts y = 1 → s₁.ts y = 1)
    (g₂ : LoopOnce x (i + 1) n s₁ s₂ l₂) (dm₂ : ∀ y, s₁.ts y = 1 → s₂.ts y = 1) :
    LoopOnce x i (n + 1) s s₂ (.delivered x i :: (l₁ ++ l₂)) := by
  have hl₁ : ∀ e ∈ l₁, e.runId = some x → s₁.ts x = 1 := fun e he hx => g₁.spent e he x hx
  exact {
    fresh := fun h₂ e he y hy => by
      have hs₁ : s₁.ts x ≠ 1 := fun h => h₂ (dm₂ x h)
      have hs : s.ts x ≠ 1 := fun h => hs₁ (dm₁ x h)
      rcases List.mem_cons.1 he with rfl | he
      · simp only [Effect.runId, Effect.runKey, Option.map_some, RunKey.id,
          Option.some.injEq] at hy
        exact hy ▸ hs
      rcases List.mem_append.1 he with he | he
      · exact g₁.fresh e he y hy
      · exact fun h => g₂.fresh h₂ e he y hy (dm₁ y h)
    spent := fun e he y hy hne => by
      rcases List.mem_cons.1 he with rfl | he
      · simp only [Effect.runId, Effect.runKey, Option.map_some, RunKey.id,
          Option.some.injEq] at hy
        exact absurd hy.symm hne
      rcases List.mem_append.1 he with he | he
      · exact dm₂ y (g₁.spent e he y hy)
      · exact g₂.spent e he y hy hne
    own := fun h₂ => by
      have hs₁ : s₁.ts x ≠ 1 := fun h => h₂ (dm₂ x h)
      have hf₁ : l₁.filter (fun e => e.runId = some x) = [] := by
        refine List.filter_eq_nil_iff.2 fun e he hp => ?_
        exact hs₁ (hl₁ e he (by simpa using hp))
      rw [List.filter_cons, List.filter_append, hf₁, g₂.own h₂, List.range'_succ]
      simp [Effect.runId, Effect.runKey, RunKey.id]
    nodup := fun h₂ => by
      have hs₁ : s₁.ts x ≠ 1 := fun h => h₂ (dm₂ x h)
      simp only [List.filterMap_cons, Effect.runKey, List.filterMap_append]
      refine List.Nodup.cons ?_ ?_
      · intro hk
        rcases List.mem_append.1 hk with hk | hk
        · obtain ⟨e, he, hk⟩ := List.mem_filterMap.1 hk
          exact hs₁ (hl₁ e he (by simpa [RunKey.id] using runId_of_runKey hk))
        · obtain ⟨e, he, hk⟩ := List.mem_filterMap.1 hk
          have hx : e.runId = some x := by simpa [RunKey.id] using runId_of_runKey hk
          have hmem : e ∈ l₂.filter (fun e => e.runId = some x) :=
            List.mem_filter.2 ⟨he, by simpa using hx⟩
          rw [g₂.own h₂] at hmem
          obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hmem
          simp only [Effect.runKey, Option.some.injEq, RunKey.delivered.injEq] at hk
          have := (List.mem_range'_1.1 hj).1
          omega
      · refine List.nodup_append.2 ⟨g₁.nodup, g₂.nodup h₂, ?_⟩
        rintro k hk₁ k' hk₂ rfl
        obtain ⟨e₁, he₁, hk₁⟩ := List.mem_filterMap.1 hk₁
        obtain ⟨e₂, he₂, hk₂⟩ := List.mem_filterMap.1 hk₂
        exact g₂.fresh h₂ e₂ he₂ _ (runId_of_runKey hk₂)
          (g₁.spent e₁ he₁ _ (runId_of_runKey hk₁)) }

/-- An execution entry from its loop: the loop ended with the id still open (the re-check),
and the id was open at the start (the first check). -/
lemma once_exec {x : OpId} {n : ℕ} {s s₂ : State} {lc : List Effect} {op : Operation} {τ : ℕ}
    {b : Bool} (g : LoopOnce x 0 n s s₂ lc) (hs : s.ts x ≠ 1) (hs₂ : s₂.ts x ≠ 1) :
    Once s (s₂.setTs x 1) (lc ++ [.executed x op τ b]) where
  fresh e he y hy := by
    rcases List.mem_append.1 he with he | he
    · exact g.fresh hs₂ e he y hy
    · rw [List.mem_singleton] at he; subst he
      simp only [Effect.runId, Effect.runKey, Option.map_some, RunKey.id,
        Option.some.injEq] at hy
      exact hy ▸ hs
  spent e he y hy := by
    rcases List.mem_append.1 he with he | he
    · by_cases hyx : y = x
      · simp [hyx]
      · simp [hyx, g.spent e he y hy hyx]
    · rw [List.mem_singleton] at he; subst he
      simp only [Effect.runId, Effect.runKey, Option.map_some, RunKey.id,
        Option.some.injEq] at hy
      simp [hy]
  nodup := by
    rw [List.filterMap_append]
    refine List.nodup_append.2 ⟨g.nodup hs₂, by simp [Effect.runKey], ?_⟩
    rintro k hk k' hk' rfl
    simp only [Effect.runKey, List.filterMap_cons, List.filterMap_nil,
      List.mem_singleton] at hk'
    subst hk'
    obtain ⟨e, he, hk⟩ := List.mem_filterMap.1 hk
    have hx : e.runId = some x := by simpa [RunKey.id] using runId_of_runKey hk
    have hmem : e ∈ lc.filter (fun e => e.runId = some x) :=
      List.mem_filter.2 ⟨he, by simpa using hx⟩
    rw [g.own hs₂] at hmem
    obtain ⟨j, _, rfl⟩ := List.mem_map.1 hmem
    simp [Effect.runKey] at hk

/-! ## Times, configuration and deliveries -/

/-- Every schedule in the log carries the transaction's time. -/
def TimeOk (τ : ℕ) (l : List Effect) : Prop :=
  ∀ e ∈ l, ∀ y t d m o, e = .scheduled y t d m o → t = τ

/-- A change of `minDelay` or the council comes with a logged execution. -/
def CfgOk (s s' : State) (l : List Effect) : Prop :=
  (s'.minDelay ≠ s.minDelay ∨ s'.council ≠ s.council) → ∃ x op t b, Effect.executed x op t b ∈ l

/-- Every delivery is followed by the execution of its operation. -/
def Followed (l : List Effect) : Prop :=
  ∀ l₁ l₂ y j, l = l₁ ++ .delivered y j :: l₂ → ∃ op t b, Effect.executed y op t b ∈ l₂

/-- In a call loop of `x`: every delivery is of `x`, or is followed by its execution. -/
def LoopFollowed (x : OpId) (l : List Effect) : Prop :=
  ∀ l₁ l₂ y j, l = l₁ ++ .delivered y j :: l₂ → y = x ∨ ∃ op t b, Effect.executed y op t b ∈ l₂

lemma TimeOk.append {τ : ℕ} {l₁ l₂ : List Effect} (h₁ : TimeOk τ l₁) (h₂ : TimeOk τ l₂) :
    TimeOk τ (l₁ ++ l₂) := fun e he => by
  rcases List.mem_append.1 he with he | he
  · exact h₁ e he
  · exact h₂ e he

lemma TimeOk.nil (τ : ℕ) : TimeOk τ [] := fun _ h => by simp at h

lemma CfgOk.append {s s₁ s₂ : State} {l₁ l₂ : List Effect} (h₁ : CfgOk s s₁ l₁)
    (h₂ : CfgOk s₁ s₂ l₂) : CfgOk s s₂ (l₁ ++ l₂) := fun h => by
  by_cases h' : s₁.minDelay ≠ s.minDelay ∨ s₁.council ≠ s.council
  · obtain ⟨x, op, t, b, he⟩ := h₁ h'
    exact ⟨x, op, t, b, List.mem_append_left _ he⟩
  · push Not at h'
    have : s₂.minDelay ≠ s₁.minDelay ∨ s₂.council ≠ s₁.council := by
      rw [h'.1, h'.2]; exact h
    obtain ⟨x, op, t, b, he⟩ := h₂ this
    exact ⟨x, op, t, b, List.mem_append_right _ he⟩

lemma CfgOk.refl (s : State) : CfgOk s s [] := fun h => by simp at h

lemma Followed.append {l₁ l₂ : List Effect} (h₁ : Followed l₁) (h₂ : Followed l₂) :
    Followed (l₁ ++ l₂) := fun a c y j h => by
  rcases append_eq_append_cons h with ⟨c', h1, rfl⟩ | ⟨a', h1, rfl⟩
  · obtain ⟨op, t, b, he⟩ := h₁ a c' y j h1
    exact ⟨op, t, b, List.mem_append_left _ he⟩
  · exact h₂ a' c y j h1

lemma Followed.nil : Followed [] := fun a c y j h => by simp at h

lemma followed_quiet {l : List Effect} (hq : ∀ e ∈ l, e.runKey = none) : Followed l :=
  fun a c y j h => by
    have := hq _ (h ▸ List.mem_append_right _ List.mem_cons_self)
    simp [Effect.runKey] at this

/-! ## Every committed frame satisfies the invariants -/

/-- The invariants a committed frame of each kind satisfies, in the deployed order at block
time `τ`. -/
def FrameInv (E : Env) (τ : ℕ) : Frame → State → State → List Effect → Prop
  | .entry c _ _, s, s', l =>
      Track E s s' l ∧ TimeOk τ l ∧ Once s s' l ∧ (c ≠ E.self → CfgOk s s' l) ∧ Followed l
  | .calls x i cs _, s, s', l =>
      Track E s s' l ∧ TimeOk τ l ∧ LoopOnce x i cs.length s s' l ∧ LoopFollowed x l
  | .target _, s, s', l =>
      Track E s s' l ∧ TimeOk τ l ∧ Once s s' l ∧ CfgOk s s' l ∧ Followed l

lemma frameInv_callFrame {E : Env} {τ : ℕ} {c : Call} {t : Callee} {s s' : State}
    {l : List Effect} (h : FrameInv E τ (callFrame E c t) s s' l) :
    Track E s s' l ∧ TimeOk τ l ∧ Once s s' l ∧ Followed l := by
  unfold callFrame at h
  by_cases hc : c.target = E.self
  · simp only [hc, ↓reduceIte] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩
  · simp only [hc, ↓reduceIte] at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

lemma timeOk_quiet {τ : ℕ} {l : List Effect} (hq : ∀ e ∈ l, ∀ y t d m o, e ≠ .scheduled y t d m o) :
    TimeOk τ l := fun e he y t d m o h => absurd h (hq e he y t d m o)

/-- The parts an execution entry adds to its loop's invariants. -/
lemma frameInv_exec {E : Env} {τ : ℕ} {c : Address} {e : GovEntry} {cbs : List Callee}
    {s s₂ : State} {lc : List Effect} {op : Operation} {b : Bool}
    (gT : Track E s s₂ lc) (gTime : TimeOk τ lc) (gO : LoopOnce (E.H op) 0 op.calls.length s s₂ lc)
    (gF : LoopFollowed (E.H op) lc)
    (hpred : op.predecessor = 0 ∨ s.ts op.predecessor = 1)
    (hp : s.ts (E.H op) ≠ 0 ∧ s.ts (E.H op) ≠ 1) (hr : b = false → s.ts (E.H op) ≤ τ)
    (hp₂ : s₂.ts (E.H op) ≠ 0 ∧ s₂.ts (E.H op) ≠ 1) (hr₂ : b = false → s₂.ts (E.H op) ≤ τ) :
    FrameInv E τ (.entry c e cbs) s (s₂.setTs (E.H op) EXECUTED)
      (lc ++ [.executed (E.H op) op τ b]) := by
  refine ⟨track_exec gT rfl hpred hp hr hp₂ hr₂,
    gTime.append (timeOk_quiet (by simp)), once_exec gO hp.2 hp₂.2,
    fun _ _ => ⟨E.H op, op, τ, b, List.mem_append_right _ (List.mem_singleton_self _)⟩, ?_⟩
  intro a c' y j h
  rcases append_eq_append_cons h with ⟨c'', h1, rfl⟩ | ⟨a', h1, _⟩
  · rcases gF a c'' y j h1 with rfl | ⟨op', t, b', he⟩
    · exact ⟨op, τ, b, List.mem_append_right _ (List.mem_singleton_self _)⟩
    · exact ⟨op', t, b', List.mem_append_left _ he⟩
  · obtain ⟨_, he, _⟩ := singleton_eq_append_cons h1; cases he

/-- The parts a quiet entry (one that calls nothing and writes no operation state) has. -/
lemma frameInv_quiet {E : Env} {τ : ℕ} {c : Address} {e : GovEntry} {cbs : List Callee}
    {s s' : State} {l : List Effect} (hts : s'.ts = s.ts) (hq : ∀ e ∈ l, e.Quiet)
    (hcfg : c ≠ E.self → CfgOk s s' l) : FrameInv E τ (.entry c e cbs) s s' l := by
  have hk : ∀ e ∈ l, e.runKey = none := fun e he => by
    have := hq e he; cases e <;> simp_all [Effect.Quiet, Effect.runKey]
  exact ⟨track_quiet hts hq,
    timeOk_quiet fun e he y t d m o h => by have := hq e he; subst h; exact this,
    once_quiet hk, hcfg, followed_quiet hk⟩

/-- A schedule entry's invariants. -/
lemma frameInv_schedule {E : Env} {τ : ℕ} {c : Address} {e : GovEntry} {cbs : List Callee}
    {s s' : State} {l : List Effect} {x : OpId} {d : ℕ} {o : Option Operation}
    (h : schedule τ s x d o = some (s', l)) (ho : ∀ op₀, o = some op₀ → E.H op₀ = x) :
    FrameInv E τ (.entry c e cbs) s s' l := by
  have g := track_schedule h ho
  obtain ⟨_, _, _, rfl, rfl⟩ := schedule_eq_some.1 h
  exact ⟨g, fun e he y t d' m o' h => by
      rw [List.mem_singleton] at he; subst he
      simp only [Effect.scheduled.injEq] at h; exact h.2.1.symm,
    once_quiet (by simp [Effect.runKey]), fun _ h => by simp at h,
    followed_quiet (by simp [Effect.runKey])⟩

/-- **The invariants.** Every frame that commits in the deployed order, at every time and
budget, satisfies `FrameInv`. -/
theorem exec_inv (E : Env) (τ : ℕ) : ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
    exec .deployed E τ n f s = some (s', l) → FrameInv E τ f s s' l := by
  intro n
  induction n with
  | zero => intro f s s' l h; simp [exec] at h
  | succ n ih =>
    intro f s s' l h
    match f with
    | .entry c (.scheduleTransparent op d) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      exact frameInv_schedule h (fun op₀ ho => by cases ho; rfl)
    | .entry c (.scheduleShadow x d) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      exact frameInv_schedule h (fun op₀ ho => by cases ho)
    | .entry c (.cancel x) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨track_cancel (isPending_iff.1 hc.2), timeOk_quiet (by simp),
        once_quiet (by simp [Effect.runKey]), fun _ h => by simp at h,
        followed_quiet (by simp [Effect.runKey])⟩
    | .entry c (.execute op) cbs =>
      simp only [exec] at h
      split_ifs at h with hG
      split at h
      · rename_i s₂ lc heq
        split_ifs at h with hR
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨gT, gTime, gO, gF⟩ := ih _ _ _ _ heq
        obtain ⟨r0, r1, r2⟩ := opState_Ready.1 hG.2.2
        obtain ⟨q0, q1, q2⟩ := opState_Ready.1 (hR.resolve_left (by simp))
        exact frameInv_exec gT gTime gO gF (predecessorDone_iff.1 hG.2.1) ⟨r0, r1⟩
          (fun _ => r2) ⟨q0, q1⟩ (fun _ => q2)
      · simp at h
    | .entry c (.executeInstant op) cbs =>
      simp only [exec] at h
      split_ifs at h with hG
      split at h
      · rename_i s₂ lc heq
        split_ifs at h with hR
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨gT, gTime, gO, gF⟩ := ih _ _ _ _ heq
        exact frameInv_exec gT gTime gO gF (predecessorDone_iff.1 hG.2.1)
          (isPending_iff.1 hG.2.2) (fun h => by cases h)
          (isPending_iff.1 (hR.resolve_left (by simp))) (fun h => by cases h)
      · simp at h
    | .entry c (.updateDelay d) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact frameInv_quiet rfl (by simp [Effect.Quiet]) (fun hne => absurd hc hne)
    | .entry c (.updateSecurityCouncil a) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact frameInv_quiet rfl (by simp [Effect.Quiet]) (fun hne => absurd hc hne)
    | .entry c (.transferOwnership a) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact frameInv_quiet rfl (by simp [Effect.Quiet]) (fun _ h => by simp at h)
    | .entry c .acceptOwnership cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact frameInv_quiet rfl (by simp [Effect.Quiet]) (fun _ h => by simp at h)
    | .entry c .renounceOwnership cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact frameInv_quiet rfl (by simp [Effect.Quiet]) (fun _ h => by simp at h)
    | .entry c .noop cbs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact frameInv_quiet rfl (by simp) (fun _ h => by simp at h)
    | .entry c .invalid cbs => simp [exec] at h
    | .calls x i [] cbs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Track.refl E s, TimeOk.nil τ, LoopOnce.nil x i s, fun a c y j h => by simp at h⟩
    | .calls x i (c :: cs) cbs =>
      simp only [exec] at h
      split at h
      · rename_i s₁ l₁ heq₁
        split at h
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨t₁, tm₁, o₁, f₁⟩ := frameInv_callFrame (ih _ _ _ _ heq₁)
          obtain ⟨t₂, tm₂, o₂, f₂⟩ := ih _ _ _ _ heq₂
          refine ⟨(t₁.append t₂).cons_delivered x i, ?_,
            LoopOnce.cons o₁ t₁.doneMono o₂ t₂.doneMono, ?_⟩
          · intro e he y t d m o hy
            rcases List.mem_cons.1 he with rfl | he
            · cases hy
            · exact (tm₁.append tm₂) e he y t d m o hy
          · intro a c' y j h
            rcases cons_eq_append_cons h with ⟨_, he, _⟩ | ⟨a', rfl, h1⟩
            · simp only [Effect.delivered.injEq] at he
              exact Or.inl he.1.symm
            · rcases append_eq_append_cons h1 with ⟨c'', h2, rfl⟩ | ⟨a'', h2, rfl⟩
              · obtain ⟨op, t, b, hm⟩ := f₁ a' c'' y j h2
                exact Or.inr ⟨op, t, b, List.mem_append_left _ hm⟩
              · exact f₂ a'' c' y j h2
        · simp at h
      · simp at h
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Track.refl E s, TimeOk.nil τ, Once.refl s, CfgOk.refl s, Followed.nil⟩
    | .target .reverts => simp [exec] at h
    | .target (.selfCall _) =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨Track.refl E s, TimeOk.nil τ, Once.refl s, CfgOk.refl s, Followed.nil⟩
    | .target (.calls c e inner caught next) =>
      simp only [exec] at h
      by_cases hc : c = E.self
      · simp [hc] at h
      simp only [hc, ↓reduceIte] at h
      split at h
      · rename_i s₁ l₁ heq₁
        split at h
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨t₁, tm₁, o₁, c₁, f₁⟩ := ih _ _ _ _ heq₁
          obtain ⟨t₂, tm₂, o₂, c₂, f₂⟩ := ih _ _ _ _ heq₂
          exact ⟨t₁.append t₂, tm₁.append tm₂, o₁.append t₁.doneMono o₂ t₂.doneMono,
            (c₁ hc).append c₂, f₁.append f₂⟩
        · simp at h
      · by_cases hcaught : caught = true
        · simp only [hcaught, ↓reduceIte] at h
          exact ih (.target next) _ _ _ h
        · simp [hcaught] at h

/-! ## Transactions and sequences of them -/

lemma submit_inv (E : Env) (s : State) (t : Tx) :
    Track E s (submit .deployed E s t).1 (submit .deployed E s t).2 ∧
    TimeOk t.time (submit .deployed E s t).2 ∧
    Once s (submit .deployed E s t).1 (submit .deployed E s t).2 ∧
    CfgOk s (submit .deployed E s t).1 (submit .deployed E s t).2 ∧
    Followed (submit .deployed E s t).2 := by
  unfold submit
  split_ifs with hc
  · exact ⟨Track.refl E s, TimeOk.nil _, Once.refl s, CfgOk.refl s, Followed.nil⟩
  · cases hx : exec .deployed E t.time t.fuel (.entry t.caller t.entry t.callees) s with
    | none => exact ⟨Track.refl E s, TimeOk.nil _, Once.refl s, CfgOk.refl s, Followed.nil⟩
    | some r =>
      obtain ⟨s', l⟩ := r
      obtain ⟨g1, g2, g3, g4, g5⟩ := exec_inv E t.time _ _ _ _ _ hx
      exact ⟨g1, g2, g3, g4 hc, g5⟩

lemma submitAll_inv (E : Env) : ∀ (s : State) (txs : List Tx),
    Track E s (submitAll .deployed E s txs).1 (submitAll .deployed E s txs).2 ∧
    Once s (submitAll .deployed E s txs).1 (submitAll .deployed E s txs).2 ∧
    Followed (submitAll .deployed E s txs).2 ∧
    ∀ e ∈ (submitAll .deployed E s txs).2, ∀ y t d m o, e = .scheduled y t d m o →
      ∃ tx ∈ txs, tx.time = t
  | s, [] => ⟨Track.refl E s, Once.refl s, Followed.nil, fun _ h => by simp [submitAll] at h⟩
  | s, t :: ts => by
      obtain ⟨g1, g2, g3, _, g5⟩ := submit_inv E s t
      obtain ⟨h1, h2, h3, h4⟩ := submitAll_inv E (submit .deployed E s t).1 ts
      refine ⟨g1.append h1, g3.append g1.doneMono h2 h1.doneMono, g5.append h3, ?_⟩
      intro e he y tm d m o hy
      rcases List.mem_append.1 he with he | he
      · exact ⟨t, List.mem_cons_self, (g2 e he y tm d m o hy).symm⟩
      · obtain ⟨tx, htx, ht⟩ := h4 e he y tm d m o hy
        exact ⟨tx, List.mem_cons_of_mem _ htx, ht⟩

/-! ## `Done` is permanent, in either order -/

lemma exec_doneMono (v : Variant) (E : Env) (τ : ℕ) : ∀ (n : ℕ) (f : Frame) (s s' : State)
    (l : List Effect), exec v E τ n f s = some (s', l) → ∀ y, s.ts y = 1 → s'.ts y = 1 := by
  intro n
  induction n with
  | zero => intro f s s' l h; simp [exec] at h
  | succ n ih =>
    intro f s s' l h y hy
    match f with
    | .entry c (.scheduleTransparent op d) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      obtain ⟨h0, _, _, rfl, rfl⟩ := schedule_eq_some.1 h
      by_cases hyx : y = E.H op
      · subst hyx; omega
      · simpa [hyx] using hy
    | .entry c (.scheduleShadow x d) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      obtain ⟨h0, _, _, rfl, rfl⟩ := schedule_eq_some.1 h
      by_cases hyx : y = x
      · subst hyx; omega
      · simpa [hyx] using hy
    | .entry c (.cancel x) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hp := isPending_iff.1 hc.2
      by_cases hyx : y = x
      · subst hyx; exact absurd hy hp.2
      · simpa [hyx] using hy
    | .entry c (.execute op) cbs =>
      simp only [exec] at h
      split_ifs at h with hG
      split at h
      · rename_i s₂ lc heq
        split_ifs at h with hR
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := ih _ _ _ _ heq y hy
        by_cases hyx : y = E.H op <;> simp [hyx, this]
      · simp at h
    | .entry c (.executeInstant op) cbs =>
      simp only [exec] at h
      split_ifs at h with hG
      split at h
      · rename_i s₂ lc heq
        split_ifs at h with hR
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have := ih _ _ _ _ heq y hy
        by_cases hyx : y = E.H op <;> simp [hyx, this]
      · simp at h
    | .entry c (.updateDelay d) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hy
    | .entry c (.updateSecurityCouncil a) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hy
    | .entry c (.transferOwnership a) cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hy
    | .entry c .acceptOwnership cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hy
    | .entry c .renounceOwnership cbs =>
      simp only [exec] at h
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hy
    | .entry c .noop cbs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hy
    | .entry c .invalid cbs => simp [exec] at h
    | .calls x i [] cbs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hy
    | .calls x i (c :: cs) cbs =>
      simp only [exec] at h
      split at h
      · rename_i s₁ l₁ heq₁
        split at h
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ih _ _ _ _ heq₂ y (ih _ _ _ _ heq₁ y hy)
        · simp at h
      · simp at h
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hy
    | .target .reverts => simp [exec] at h
    | .target (.selfCall _) =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h; exact hy
    | .target (.calls c e inner caught next) =>
      simp only [exec] at h
      by_cases hc : c = E.self
      · simp [hc] at h
      simp only [hc, ↓reduceIte] at h
      split at h
      · rename_i s₁ l₁ heq₁
        split at h
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ih _ _ _ _ heq₂ y (ih _ _ _ _ heq₁ y hy)
        · simp at h
      · by_cases hcaught : caught = true
        · simp only [hcaught, ↓reduceIte] at h
          exact ih _ _ _ _ h y hy
        · simp [hcaught] at h

/-! ## The guards -/

theorem EntryGuards : Properties.EntryGuards := by
  intro v E τ n c cbs s s' l
  rcases n with _ | n
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [exec]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro op d h
    simp only [exec] at h
    split_ifs at h with hc
    obtain ⟨h0, hm, hov, rfl, rfl⟩ := schedule_eq_some.1 h
    exact ⟨hc, h0, hm, hov, rfl, rfl⟩
  · intro x d h
    simp only [exec] at h
    split_ifs at h with hc
    obtain ⟨h0, hm, hov, rfl, rfl⟩ := schedule_eq_some.1 h
    exact ⟨hc, h0, hm, hov, rfl, rfl⟩
  · intro x h
    simp only [exec] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hc.1, (isPending_iff.1 hc.2).1, (isPending_iff.1 hc.2).2, rfl, rfl⟩
  · intro op h
    simp only [exec] at h
    split_ifs at h with hG
    split at h
    · split_ifs at h with hR
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨r0, r1, r2⟩ := opState_Ready.1 hG.2.2
      exact ⟨hG.1, predecessorDone_iff.1 hG.2.1, r0, r1, r2, by simp⟩
    · simp at h
  · intro op h
    simp only [exec] at h
    split_ifs at h with hG
    split at h
    · split_ifs at h with hR
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨r0, r1⟩ := isPending_iff.1 hG.2.2
      exact ⟨hG.1, predecessorDone_iff.1 hG.2.1, r0, r1, by simp⟩
    · simp at h
  · intro d h
    simp only [exec] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hc, h.1.symm⟩
  · intro a h
    simp only [exec] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hc, h.1.symm⟩
  · intro a h
    simp only [exec] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hc, h.1.symm⟩
  · intro h
    simp only [exec] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hc, h.1.symm⟩
  · intro h
    simp only [exec] at h
    split_ifs at h with hc
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨hc, h.1.symm⟩

theorem EntryGuardsWitness : Properties.EntryGuardsWitness := by
  unfold Properties.EntryGuardsWitness; decide

/-! ## (a) Once only -/

theorem DoneIsPermanent : Properties.DoneIsPermanent :=
  ⟨fun v E τ n f s s' l x hx h => exec_doneMono v E τ n f s s' l h x hx,
    fun E s txs x hx => (submitAll_inv E s txs).1.doneMono x hx⟩

theorem DoneIsPermanentWitness : Properties.DoneIsPermanentWitness := by
  unfold Properties.DoneIsPermanentWitness; decide

theorem OnceOnly : Properties.OnceOnly :=
  fun E s txs => (submitAll_inv E s txs).2.1.nodup

theorem CommittedRunsWereOpen : Properties.CommittedRunsWereOpen :=
  fun E s txs e x he hx =>
    ⟨(submitAll_inv E s txs).2.1.fresh e he x hx, (submitAll_inv E s txs).2.1.spent e he x hx⟩

/-- The execution entry, unfolded: its loop committed and the re-check passed. -/
lemma exec_execution_some {E : Env} {τ n : ℕ} {c : Address} {op : Operation} {instant : Bool}
    {cbs : List Callee} {s s' : State} {l : List Effect}
    (h : exec .deployed E τ n (.entry c (GovEntry.execution op instant) cbs) s = some (s', l)) :
    ∃ m s₂ lc, n = m + 1 ∧
      exec .deployed E τ m (.calls (E.H op) 0 op.calls cbs) s = some (s₂, lc) ∧
      s₂.ts (E.H op) ≠ 1 ∧ s' = s₂.setTs (E.H op) EXECUTED ∧
      l = lc ++ [.executed (E.H op) op τ instant] := by
  rcases n with _ | m
  · simp [exec] at h
  cases instant with
  | false =>
    simp only [GovEntry.execution, Bool.false_eq_true, ↓reduceIte, exec] at h
    split_ifs at h with hG
    split at h
    · rename_i s₂ lc heq
      split_ifs at h with hR
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m, s₂, lc, rfl, heq, (opState_Ready.1 (hR.resolve_left (by simp))).2.1, rfl, rfl⟩
    · simp at h
  | true =>
    simp only [GovEntry.execution, ↓reduceIte, exec] at h
    split_ifs at h with hG
    split at h
    · rename_i s₂ lc heq
      split_ifs at h with hR
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m, s₂, lc, rfl, heq, (isPending_iff.1 (hR.resolve_left (by simp))).2, rfl, rfl⟩
    · simp at h

theorem ExecutionRunsEachCallOnce : Properties.ExecutionRunsEachCallOnce := by
  intro E τ n c op instant cbs s s' l h
  obtain ⟨m, s₂, lc, rfl, heq, hs₂, rfl, rfl⟩ := exec_execution_some h
  obtain ⟨_, _, gO, _⟩ := exec_inv E τ _ _ _ _ _ heq
  refine ⟨?_, by simp⟩
  rw [List.filter_append, gO.own hs₂, List.range_eq_range']
  simp [Effect.runId, Effect.runKey, RunKey.id]

/-! ## (e) The re-check -/

theorem ReentrantReexecutionReverts : Properties.ReentrantReexecutionReverts := by
  intro E τ n c op instant cbs s s₂ l hl ⟨op', τ', b, hmem⟩
  obtain ⟨_, _, gO, _⟩ := exec_inv E τ _ _ _ _ _ hl
  have hdone : s₂.ts (E.H op) = 1 := by
    by_contra hne
    have hf : Effect.executed (E.H op) op' τ' b ∈ l.filter (fun e => e.runId = some (E.H op)) :=
      List.mem_filter.2 ⟨hmem, by simp [Effect.runId, Effect.runKey, RunKey.id]⟩
    rw [gO.own hne] at hf
    obtain ⟨j, _, hj⟩ := List.mem_map.1 hf
    cases hj
  cases instant with
  | false =>
    simp only [GovEntry.execution, Bool.false_eq_true, ↓reduceIte, exec, hl]
    split_ifs with hG hR
    · exact absurd (opState_Ready.1 (hR.resolve_left (by simp))).2.1 (by simp [hdone])
    · rfl
    · rfl
  | true =>
    simp only [GovEntry.execution, ↓reduceIte, exec, hl]
    split_ifs with hG hR
    · exact absurd (isPending_iff.1 (hR.resolve_left (by simp))).2 (by simp [hdone])
    · rfl
    · rfl

theorem ReentrantReexecutionWitness : Properties.ReentrantReexecutionWitness := by
  unfold Properties.ReentrantReexecutionWitness; decide

theorem WithoutRecheckReexecutes : Properties.WithoutRecheckReexecutes := by
  unfold Properties.WithoutRecheckReexecutes; decide

/-- A call loop over foreign targets whose behaviours are all missing (so they return)
delivers every call, in order, and changes nothing, in either variant. -/
lemma exec_loop_returns (v : Variant) (E : Env) (τ : ℕ) (x : OpId) :
    ∀ (cs : List Call) (i m : ℕ) (s : State), (∀ c ∈ cs, c.target ≠ E.self) →
      cs.length + 1 ≤ m →
      exec v E τ m (.calls x i cs []) s =
        some (s, (List.range' i cs.length).map (Effect.delivered x))
  | [], i, m, s, _, hm => by
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by simp at hm; omega⟩
      simp [exec]
  | c :: cs, i, m, s, hc, hm => by
      simp only [List.length_cons] at hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hct : c.target ≠ E.self := hc c List.mem_cons_self
      have ih := exec_loop_returns v E τ x cs (i + 1) m' s
        (fun c' hc' => hc c' (List.mem_cons_of_mem _ hc')) (by omega)
      obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
      have ht : exec v E τ (m'' + 1) (callFrame E c (([] : List Callee).headD .returns)) s =
          some (s, []) := by
        simp only [List.headD_nil, callFrame, hct, ↓reduceIte, exec]
      simp only [exec]
      rw [ht]
      simp only [List.tail_nil]
      rw [ih]
      simp [List.range'_succ]

theorem WithoutRecheckAnyOpRunsTwice : Properties.WithoutRecheckAnyOpRunsTwice := by
  intro E s op τ hne hcs hown hpred hready
  obtain ⟨c₀, rest, hop⟩ := List.exists_cons_of_ne_nil hne
  have hc₀ : c₀.target ≠ E.self := hcs c₀ (hop ▸ List.mem_cons_self)
  have hrest : ∀ c ∈ rest, c.target ≠ E.self :=
    fun c hc => hcs c (hop ▸ List.mem_cons_of_mem _ hc)
  have hlen : op.calls.length = rest.length + 1 := by rw [hop]; rfl
  -- the inner, re-entrant execution: its loop delivers every call and changes nothing
  have hinner : ∀ v : Variant, exec v E τ (rest.length + 3) (.entry s.owner (.execute op) []) s =
      some (s.setTs (E.H op) EXECUTED,
        (List.range' 0 (rest.length + 1)).map (Effect.delivered (E.H op)) ++
          [.executed (E.H op) op τ false]) := by
    intro v
    have hl := exec_loop_returns v E τ (E.H op) op.calls 0 (rest.length + 2) s hcs (by omega)
    rw [hlen] at hl
    rw [exec]
    simp only [hpred, hready, true_or, and_self, ↓reduceIte, hl, or_true]
  -- the first call's target: it runs the inner execution, then returns
  have htarget : ∀ v : Variant,
      exec v E τ (rest.length + 4)
          (callFrame E c₀ ([timelockCallback s.owner (.execute op)].headD .returns)) s =
        some (s.setTs (E.H op) EXECUTED,
          (List.range' 0 (rest.length + 1)).map (Effect.delivered (E.H op)) ++
            [.executed (E.H op) op τ false]) := by
    intro v
    simp only [List.headD_cons, callFrame, hc₀, ↓reduceIte, timelockCallback]
    rw [exec]
    simp only [hown, ↓reduceIte, hinner v]
    simp [exec]
  -- the rest of the outer loop
  have hrestLoop : ∀ v : Variant,
      exec v E τ (rest.length + 4) (.calls (E.H op) 1 rest [])
          (s.setTs (E.H op) EXECUTED) =
        some (s.setTs (E.H op) EXECUTED,
          (List.range' 1 rest.length).map (Effect.delivered (E.H op))) :=
    fun v => exec_loop_returns v E τ (E.H op) rest 1 (rest.length + 4) _ hrest (by omega)
  have hloop : ∀ v : Variant,
      exec v E τ (rest.length + 5)
          (.calls (E.H op) 0 op.calls [timelockCallback s.owner (.execute op)]) s =
        some (s.setTs (E.H op) EXECUTED, .delivered (E.H op) 0 ::
          (((List.range' 0 (rest.length + 1)).map (Effect.delivered (E.H op)) ++
            [.executed (E.H op) op τ false]) ++
            (List.range' 1 rest.length).map (Effect.delivered (E.H op)))) := by
    intro v
    rw [hop, exec, htarget v]
    simp only [List.tail_cons, Nat.zero_add]
    rw [hrestLoop v]
  have hfuel : op.calls.length + 5 = rest.length + 5 + 1 := by omega
  constructor
  · simp only [submit, hown, ↓reduceIte, hfuel]
    rw [exec]
    simp only [hpred, hready, true_or, and_self, ↓reduceIte, hloop .noRecheck, commit]
    intro hnd
    rw [List.filterMap_append] at hnd
    have hdis := (List.nodup_append.1 hnd).2.2
    refine hdis (.executed (E.H op)) ?_ (.executed (E.H op)) (by simp [Effect.runKey]) rfl
    rw [List.mem_filterMap]
    exact ⟨.executed (E.H op) op τ false, by simp, rfl⟩
  · simp only [submit, hown, ↓reduceIte, hfuel]
    rw [exec]
    simp only [hpred, hready, true_or, and_self, ↓reduceIte, hloop .deployed]
    simp [opState_Ready, commit]

theorem WithoutRecheckAnyOpRunsTwiceWitness : Properties.WithoutRecheckAnyOpRunsTwiceWitness := by
  unfold Properties.WithoutRecheckAnyOpRunsTwiceWitness; decide

/-! ## (b) The delay, and (h) the published payload -/

theorem OwnerPathWaited : Properties.OwnerPathWaited := by
  intro E s txs hnp l₁ l₂ x op τ h
  obtain ⟨_, hw⟩ := (submitAll_inv E s txs).1.execWitness l₁ l₂ x op τ false h
  rcases hw with ⟨h0, h1, _, _⟩ | ⟨r, hr, ⟨hm, _⟩, ht⟩
  · rcases hnp x with h' | h'
    · exact absurd h' h0
    · exact absurd h' h1
  · exact ⟨r, hr, hm, ht rfl⟩

theorem EarlyExecutionIsInstant : Properties.EarlyExecutionIsInstant := by
  intro E s txs hnp l₁ l₂ x op τ b r h hr hlt
  cases b with
  | true => rfl
  | false =>
    obtain ⟨r', hr', _, hle⟩ := OwnerPathWaited E s txs hnp l₁ l₂ x op τ h
    rw [hr] at hr'
    cases hr'
    omega

theorem EarlyExecutionIsInstantWitness : Properties.EarlyExecutionIsInstantWitness := by
  unfold Properties.EarlyExecutionIsInstantWitness; decide

theorem OwnerPathWaitedWitness : Properties.OwnerPathWaitedWitness :=
  ⟨fun _ => Or.inl rfl, by decide, by decide⟩

theorem TransparentBinding : Properties.TransparentBinding := by
  intro E s txs hnp l₁ l₂ x op τ b h
  obtain ⟨hx, hw⟩ := (submitAll_inv E s txs).1.execWitness l₁ l₂ x op τ b h
  refine ⟨hx, ?_⟩
  rcases hw with ⟨h0, h1, _, _⟩ | ⟨r, hr, ⟨hm, hop⟩, _⟩
  · rcases hnp x with h' | h'
    · exact absurd h' h0
    · exact absurd h' h1
  · refine ⟨r, hr, hm, fun op₀ ho => ?_⟩
    by_cases heq : op₀ = op
    · exact Or.inl heq
    · exact Or.inr ⟨heq, (hop op₀ ho).trans hx⟩

theorem TransparentBindingWitness : Properties.TransparentBindingWitness := by
  unfold Properties.TransparentBindingWitness; decide

theorem TransparentCollisionExecutesAnotherOp :
    Properties.TransparentCollisionExecutesAnotherOp := by
  unfold Properties.TransparentCollisionExecutesAnotherOp; decide

/-! ## (c) Predecessors, and (d) the sentinel -/

theorem PredecessorDoneOrSentinel : Properties.PredecessorDoneOrSentinel := by
  intro E s txs l₁ l₂ x op τ b h hp
  exact (submitAll_inv E s txs).1.predOk l₁ l₂ x op τ b h hp

theorem PredecessorDone : Properties.PredecessorDone := by
  intro E s txs htimes l₁ l₂ x op τ b h hp
  obtain ⟨g, _, _, hsched⟩ := submitAll_inv E s txs
  rcases g.predOk l₁ l₂ x op τ b h hp with h' | h' | ⟨t, d, m, o, hm, ht⟩
  · exact Or.inl h'
  · exact Or.inr h'
  · exfalso
    have hmem : Effect.scheduled op.predecessor t d m o ∈ (submitAll .deployed E s txs).2 := by
      rw [h]; exact List.mem_append_left _ hm
    obtain ⟨tx, htx, hte⟩ := hsched _ hmem _ _ _ _ _ rfl
    have := htimes tx htx
    omega

theorem PredecessorDoneWitness : Properties.PredecessorDoneWitness := by
  unfold Properties.PredecessorDoneWitness; decide

theorem SentinelCollision : Properties.SentinelCollision := by
  refine ⟨fun τ s x d o s' l h h1 => ?_, fun τ s x d o s' l h h0 => ?_,
    by decide, by decide, by decide, by decide, by decide⟩
  · obtain ⟨_, _, _, rfl, rfl⟩ := schedule_eq_some.1 h
    rw [opState_Done]; simpa using h1
  · obtain ⟨_, _, _, rfl, rfl⟩ := schedule_eq_some.1 h
    rw [opState_Unset]; simpa using h0

/-! ## (f) Cancelling an operation while it runs -/

theorem InFlightCancelNeedsReschedule : Properties.InFlightCancelNeedsReschedule := by
  intro E τ n c op instant cbs s s' l h l₁ l₂ hl
  have hdone := (ExecutionRunsEachCallOnce E τ n c op instant cbs s s' l h).2
  obtain ⟨gT, _⟩ := exec_inv E τ n _ s s' l h
  rcases gT.cancelTrack l₁ l₂ _ hl with h0 | h'
  · simp only [EXECUTED_eq] at hdone; omega
  · exact h'

theorem InFlightCancelIneffective : Properties.InFlightCancelIneffective := by
  unfold Properties.InFlightCancelIneffective; decide

/-! ## (g) Raising the delay -/

theorem MinDelayChangeKeepsTimestamps : Properties.MinDelayChangeKeepsTimestamps := by
  refine ⟨fun v E τ n c d cbs s s' l h => ?_, fun s m τ x => rfl⟩
  rcases n with _ | n
  · simp [exec] at h
  simp only [exec] at h
  split_ifs at h with hc
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

theorem DelayRaiseNotRetroactive : Properties.DelayRaiseNotRetroactive := by
  unfold Properties.DelayRaiseNotRetroactive TimesMonotone; decide

/-! ## Authority -/

theorem ConfigChangesNeedExecution : Properties.ConfigChangesNeedExecution :=
  fun E s t h => (submit_inv E s t).2.2.2.1 h

theorem DeliveriesBelongToExecutions : Properties.DeliveriesBelongToExecutions :=
  fun E s txs l₁ l₂ x i h => (submitAll_inv E s txs).2.2.1 l₁ l₂ x i h

end Contracts.Governance
