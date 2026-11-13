import EraSpec.Contracts.InteropHandlerBase.Properties.ReentrancyAtHead
import EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy

/-!
# Proofs: the pinned re-entrancy results, re-checked at head

One lemma carries the general results: `exec_toPinned`, by induction on the budget. A head frame and
its `toPinned` image in the pinned model's deployed order revert together or commit the same state
and the same effects. The head `executeAtomicBundle` is the pinned `executeBundle`
(`beforeCalls_verifyIfUnreceived`: writing `Verified` and then `FullyExecuted` is writing
`FullyExecuted`), and the head log's flow-gate events are dropped by `effects`.

Each `…AtHead` result about `effects` is then the pinned theorem of
`EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy` read through that lemma. The retry result
states the whole head log, gate events included, so its loop lemma (`exec_calls_returns`) is proved on
the head model directly. The two witnesses are evaluated by `decide`.
-/

namespace Contracts.InteropHandlerAtHead

open AttackVectors.BundleStatusMachine
open Contracts.InteropHandler (BundleHash Bundle State Effect Spent CallsClosed init wA wB
  markCalls toExecute)

/-! ## The effects of a head log -/

@[simp] lemma effects_nil : effects [] = [] := rfl

@[simp] lemma effects_append (l₁ l₂ : List Event) :
    effects (l₁ ++ l₂) = effects l₁ ++ effects l₂ := by
  simp [effects, List.filterMap_append]

@[simp] lemma effects_effect_cons (e : Effect) (l : List Event) :
    effects (.effect e :: l) = e :: effects l := rfl

@[simp] lemma effects_gated_cons (h : BundleHash) (l : List Event) :
    effects (.gated h :: l) = effects l := rfl

@[simp] lemma effects_verified_cons (h : BundleHash) (l : List Event) :
    effects (.verified h :: l) = effects l := rfl

@[simp] lemma effects_gateLog (s : State) (h : BundleHash) : effects (gateLog s h) = [] := by
  unfold gateLog
  split_ifs <;> rfl

/-- The effects of a head log are its `Event.effect` entries. -/
lemma mem_effects {e : Effect} : ∀ {l : List Event}, e ∈ effects l ↔ Event.effect e ∈ l
  | [] => by simp
  | .effect e' :: l => by
      rw [effects_effect_cons, List.mem_cons, List.mem_cons, mem_effects (l := l)]
      constructor
      · rintro (rfl | h)
        · exact Or.inl rfl
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (Event.effect.inj h)
        · exact Or.inr h
  | .gated h :: l => by
      rw [effects_gated_cons, List.mem_cons, mem_effects (l := l)]
      simp
  | .verified h :: l => by
      rw [effects_verified_cons, List.mem_cons, mem_effects (l := l)]
      simp

/-! ## The translation -/

@[simp] lemma listToPinned_nil : Callee.listToPinned [] = [] := by
  rw [Callee.listToPinned]

@[simp] lemma listToPinned_cons (c : Callee) (cs : List Callee) :
    Callee.listToPinned (c :: cs) = c.toPinned :: Callee.listToPinned cs := by
  rw [Callee.listToPinned]

@[simp] lemma toPinned_returns : Callee.toPinned .returns = .returns := by
  rw [Callee.toPinned]

@[simp] lemma toPinned_reverts : Callee.toPinned .reverts = .reverts := by
  rw [Callee.toPinned]

@[simp] lemma toPinned_calls (e : Entry) (inner : List Callee) (caught : Bool) (next : Callee) :
    Callee.toPinned (.calls e inner caught next) =
      .calls e.toPinned (Callee.listToPinned inner) caught next.toPinned := by
  rw [Callee.toPinned]

lemma listToPinned_eq_map : ∀ cs : List Callee, Callee.listToPinned cs = cs.map Callee.toPinned
  | [] => by simp
  | c :: cs => by simp [listToPinned_eq_map cs]

@[simp] lemma listToPinned_headD (cs : List Callee) :
    (Callee.listToPinned cs).headD .returns = (cs.headD .returns).toPinned := by
  cases cs <;> simp

@[simp] lemma listToPinned_tail (cs : List Callee) :
    (Callee.listToPinned cs).tail = Callee.listToPinned cs.tail := by
  cases cs <;> simp

@[simp] lemma toPinned_bundle (e : Entry) : e.toPinned.bundle = e.bundle := by
  cases e <;> rfl

/-- The pinned `executeBundle` verifies an `Unreceived` bundle and then writes `FullyExecuted` over
it: the head write. -/
lemma beforeCalls_verifyIfUnreceived (b : Bundle) (s : State) :
    InteropHandler.beforeCalls .deployed b (s.verifyIfUnreceived b.hash) =
      markFullyExecuted b s := by
  unfold InteropHandler.State.verifyIfUnreceived markFullyExecuted
  split_ifs with hu
  · simp only [InteropHandler.beforeCalls, InteropHandler.State.setBundle,
      InteropHandler.State.executeAll]
    congr 1
    funext h'
    split_ifs <;> rfl
  · rfl

/-- **The correspondence.** A head frame and its pinned image revert together, or commit the same
state and the same effects. -/
theorem exec_toPinned : ∀ (n : ℕ) (f : Frame) (s : State),
    (exec n f s).map (fun r => (r.1, effects r.2)) =
      InteropHandler.exec .deployed n f.toPinned s := by
  intro n
  induction n with
  | zero => intro f s; simp [exec, InteropHandler.exec]
  | succ n ih =>
    intro f s
    match f with
    | .entry (.executeAtomicBundle b ok) cs =>
      have h := ih (.calls b.hash (List.range b.calls) cs) (markFullyExecuted b s)
      simp only [Frame.toPinned] at h
      simp only [Frame.toPinned, Entry.toPinned, exec, InteropHandler.exec]
      split_ifs with hG
      · rw [beforeCalls_verifyIfUnreceived, ← h]
        cases exec n (.calls b.hash (List.range b.calls) cs) (markFullyExecuted b s) with
        | none => rfl
        | some r => simp [InteropHandler.afterCalls]
      · rfl
    | .entry (.verifyAtomicBundle b ok) cs =>
      simp only [Frame.toPinned, Entry.toPinned, exec, InteropHandler.exec]
      split_ifs with hG
      · rfl
      · rfl
    | .entry (.unbundleBundle b req) cs =>
      simp only [Frame.toPinned, Entry.toPinned, exec, InteropHandler.exec,
        InteropHandler.writesCallsFirst]
      split_ifs with hG
      · cases hm : markCalls true b.hash 0 req (s.setBundle b.hash .Unbundled) with
        | none => rfl
        | some s₁ =>
          have h := ih (.calls b.hash (toExecute 0 req) cs) s₁
          simp only [Frame.toPinned] at h
          simp only []
          rw [← h]
          cases exec n (.calls b.hash (toExecute 0 req) cs) s₁ with
          | none => rfl
          | some r => simp [InteropHandler.afterUnbundle]
      · rfl
    | .calls hb [] cs =>
      simp [Frame.toPinned, exec, InteropHandler.exec]
    | .calls hb (i :: is) cs =>
      have h₁ := ih (.target (cs.headD .returns)) s
      simp only [Frame.toPinned] at h₁
      simp only [Frame.toPinned, exec, InteropHandler.exec, listToPinned_headD, listToPinned_tail]
      rw [← h₁]
      cases exec n (.target (cs.headD .returns)) s with
      | none => rfl
      | some r₁ =>
        obtain ⟨s₁, l₁⟩ := r₁
        have h₂ := ih (.calls hb is cs.tail) s₁
        simp only [Frame.toPinned] at h₂
        simp only [Option.map_some]
        rw [← h₂]
        cases exec n (.calls hb is cs.tail) s₁ with
        | none => rfl
        | some r₂ => simp
    | .target .returns =>
      simp [Frame.toPinned, exec, InteropHandler.exec]
    | .target .reverts =>
      simp [Frame.toPinned, exec, InteropHandler.exec]
    | .target (.calls e inner caught next) =>
      have h₁ := ih (.entry e inner) s
      simp only [Frame.toPinned] at h₁
      simp only [Frame.toPinned, toPinned_calls, exec, InteropHandler.exec]
      rw [← h₁]
      cases exec n (.entry e inner) s with
      | none =>
        simp only [Option.map_none]
        split_ifs
        · exact ih (.target next) s
        · rfl
      | some r₁ =>
        obtain ⟨s₁, l₁⟩ := r₁
        have h₂ := ih (.target next) s₁
        simp only [Frame.toPinned] at h₂
        simp only [Option.map_some]
        rw [← h₂]
        cases exec n (.target next) s₁ with
        | none => rfl
        | some r₂ => simp

/-- A committed head frame commits in the pinned model, with the same state and effects. -/
lemma exec_toPinned_some {n : ℕ} {f : Frame} {s s' : State} {l : List Event}
    (hx : exec n f s = some (s', l)) :
    InteropHandler.exec .deployed n f.toPinned s = some (s', effects l) := by
  rw [← exec_toPinned, hx]
  rfl

/-- A head frame reverts when its pinned image does. -/
lemma exec_none_of_toPinned {n : ℕ} {f : Frame} {s : State}
    (hx : InteropHandler.exec .deployed n f.toPinned s = none) : exec n f s = none := by
  rw [← exec_toPinned] at hx
  exact Option.map_eq_none_iff.1 hx

lemma submit_toPinned (s : State) (t : Tx) :
    (submit s t).1 = (InteropHandler.submit .deployed s t.toPinned).1 ∧
      effects (submit s t).2 = (InteropHandler.submit .deployed s t.toPinned).2 := by
  have h := exec_toPinned t.fuel (.entry t.entry t.callees) s
  simp only [Frame.toPinned] at h
  simp only [submit, InteropHandler.submit, Tx.toPinned]
  rw [← h]
  cases exec t.fuel (.entry t.entry t.callees) s with
  | none => exact ⟨rfl, rfl⟩
  | some r => exact ⟨rfl, rfl⟩

lemma submitAll_toPinned : ∀ (s : State) (txs : List Tx),
    (submitAll s txs).1 = (InteropHandler.submitAll .deployed s (txs.map Tx.toPinned)).1 ∧
      effects (submitAll s txs).2 =
        (InteropHandler.submitAll .deployed s (txs.map Tx.toPinned)).2
  | s, [] => ⟨rfl, rfl⟩
  | s, t :: ts => by
      obtain ⟨h₁, h₂⟩ := submit_toPinned s t
      obtain ⟨h₃, h₄⟩ := submitAll_toPinned (submit s t).1 ts
      simp only [submitAll, InteropHandler.submitAll, List.map_cons, effects_append]
      rw [← h₁, ← h₂, ← h₃, ← h₄]
      exact ⟨rfl, rfl⟩

theorem HeadHandlerRunsThePinnedPublicRoute : Properties.HeadHandlerRunsThePinnedPublicRoute :=
  ⟨exec_toPinned, submitAll_toPinned⟩

/-- The pinned invariant, for a head sequence of transactions. -/
lemma submitAll_good (s : State) (txs : List Tx) :
    InteropHandler.Good s (submitAll s txs).1 (effects (submitAll s txs).2) := by
  rw [(submitAll_toPinned s txs).1, (submitAll_toPinned s txs).2]
  exact InteropHandler.submitAll_good s _

/-! ## Nothing runs twice -/

theorem NoEffectCommittedTwiceAtHead : Properties.NoEffectCommittedTwiceAtHead :=
  fun s txs => (submitAll_good s txs).nodup

theorem CommittedEffectsWereOpenAtHead : Properties.CommittedEffectsWereOpenAtHead :=
  fun s txs e he => ⟨(submitAll_good s txs).fresh e he, (submitAll_good s txs).spent e he⟩

theorem WholeAtomicExecutionRunsEachCallOnceAtHead :
    Properties.WholeAtomicExecutionRunsEachCallOnceAtHead := by
  intro n b ok cs s s' l hx
  exact InteropHandler.WholeBundleExecutionRunsEachCallOnce n b ok (Callee.listToPinned cs) s s'
    (effects l) (Or.inr (exec_toPinned_some hx))

theorem StatusRecordsExactlyTheCommittedEffectsAtHead :
    Properties.StatusRecordsExactlyTheCommittedEffectsAtHead := by
  intro txs h i
  rw [(submitAll_toPinned init txs).1, (submitAll_toPinned init txs).2]
  exact InteropHandler.StatusRecordsExactlyTheCommittedEffects _ h i

theorem NestedExecutionFollowsTheStatusMachineAtHead :
    Properties.NestedExecutionFollowsTheStatusMachineAtHead := by
  refine ⟨InteropHandler.NestedExecutionFollowsTheStatusMachine.1, fun s txs hc => ?_⟩
  rw [(submitAll_toPinned s txs).1]
  exact InteropHandler.NestedExecutionFollowsTheStatusMachine.2 s _ hc

theorem ReentryForAnExecutingBundleRevertsAtHead :
    Properties.ReentryForAnExecutingBundleRevertsAtHead := by
  refine ⟨fun b s => by simp [markFullyExecuted], fun n f h s s' l hfe hx => ?_,
    fun n e cs s hfe => ?_⟩
  · exact InteropHandler.exec_keeps_fullyExecuted hfe (exec_toPinned_some hx)
  · refine exec_none_of_toPinned (f := .entry e cs) ?_
    exact InteropHandler.exec_entry_of_fullyExecuted (e := e.toPinned) (by simpa using hfe)

theorem ReentrantExecutionWitnessAtHead : Properties.ReentrantExecutionWitnessAtHead := by
  unfold Properties.ReentrantExecutionWitnessAtHead; decide

theorem NestedVerifyAndUnbundleWitnessAtHead :
    Properties.NestedVerifyAndUnbundleWitnessAtHead := by
  unfold Properties.NestedVerifyAndUnbundleWitnessAtHead; decide

/-! ## A failing call rolls the execution back -/

theorem RevertingCallRevertsAtomicExecutionAtHead :
    Properties.RevertingCallRevertsAtomicExecutionAtHead := by
  intro n b ok cs s hr
  refine exec_none_of_toPinned (f := .entry (.executeAtomicBundle b ok) cs) ?_
  refine (InteropHandler.RevertingCallRevertsTheExecution .deployed n b ok
    (Callee.listToPinned cs) s ?_).2
  rw [listToPinned_eq_map, ← List.map_take]
  exact List.mem_map.2 ⟨.reverts, hr, by simp⟩

/-- A head call loop whose targets all return delivers every call and changes nothing. -/
lemma exec_calls_returns (h : BundleHash) :
    ∀ (is : List ℕ) (cs : List Callee) (m : ℕ) (s : State),
      (∀ c ∈ cs, c = .returns) → is.length < m →
      exec m (.calls h is cs) s = some (s, is.map fun i => Event.effect (.delivered h i))
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
      rw [exec_calls_returns h is cs.tail (k + 1) s htl (by omega)]
      simp

theorem FailedAtomicAttemptCanBeRetriedAtHead :
    Properties.FailedAtomicAttemptCanBeRetriedAtHead := by
  intro s b fuel ok cs hopen hr
  refine ⟨?_, ?_⟩
  · simp only [submit]
    rw [RevertingCallRevertsAtomicExecutionAtHead fuel b ok cs s hr]
    rfl
  · simp only [submit]
    show commit s (exec (b.calls + 1 + 1) _ s) = _
    simp only [exec]
    split_ifs with hG
    · rw [exec_calls_returns b.hash _ _ _ _ (fun c hc => (List.mem_replicate.1 hc).2) (by simp)]
      rfl
    · refine (hG ?_).elim
      rcases hopen with hu | hv
      · exact Or.inr ⟨hu, trivial⟩
      · exact Or.inl hv

end Contracts.InteropHandlerAtHead
