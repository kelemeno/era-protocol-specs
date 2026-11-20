import EraSpec.Contracts.InteropHandlerBase.Properties.ReentrancyAtV35
import EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy
import EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyStrong
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineFaithful
import Mathlib.Tactic

/-!
# Proofs: re-entrant execution in the v35 handlers

The deployed results are transported from the engine. `execAtV35_eq_exec` shows, by induction
on the budget, that a v35 frame runs as its translation (`FrameAtV35.toPin`) in
`Contracts.InteropHandler.exec`, whenever the layer is L1 or the order writes the bundle status
before the calls. The one place the two semantics differ is L2's `execute`, which skips the engine
`executeBundle`'s `Verified` write; `beforeCalls` overwrites the bundle status in those orders
(`beforeCalls_proofWriteAtV35`). Lifted to transactions (`submitAllAtV35_eq_submitAll`), it turns
the engine theorems of `Reentrancy` and `BundleStatusMachineFaithful` used here into their v35
forms.

The rollback results hold in every order, including L2's `statusWriteAfterCalls`, where the
translation fails, so they are proved on `execAtV35` directly, by the engine's loop lemmas redone for
v35 (`execAtV35_calls_alwaysReverts`, `execAtV35_calls_append`). The concrete witnesses and
countermodels are evaluated by `decide`.
-/

namespace Contracts.InteropHandlerAtV35

open AttackVectors.BundleStatusMachine (Status CallStatus)
open Contracts.InteropHandler

/-! ## The translation -/

@[simp] private lemma listToPin_eq_map {ℓ : LayerAtV35} :
    ∀ cs : List (CalleeAtV35 ℓ), CalleeAtV35.listToPin cs = cs.map CalleeAtV35.toPin
  | [] => by simp [CalleeAtV35.listToPin]
  | c :: cs => by simp [CalleeAtV35.listToPin, listToPin_eq_map cs]

@[simp] lemma toPin_returns {ℓ : LayerAtV35} :
    (CalleeAtV35.returns : CalleeAtV35 ℓ).toPin = .returns := by
  simp [CalleeAtV35.toPin]

@[simp] lemma toPin_reverts {ℓ : LayerAtV35} :
    (CalleeAtV35.reverts : CalleeAtV35 ℓ).toPin = .reverts := by
  simp [CalleeAtV35.toPin]

@[simp] lemma toPin_calls {ℓ : LayerAtV35} (e : EntryAtV35 ℓ) (inner : List (CalleeAtV35 ℓ))
    (caught : Bool) (next : CalleeAtV35 ℓ) :
    (CalleeAtV35.calls e inner caught next).toPin =
      .calls e.toPin (inner.map CalleeAtV35.toPin) caught next.toPin := by
  simp [CalleeAtV35.toPin]

lemma toPin_headD {ℓ : LayerAtV35} (cs : List (CalleeAtV35 ℓ)) :
    (cs.headD .returns).toPin = (cs.map CalleeAtV35.toPin).headD .returns := by
  cases cs <;> simp

lemma setBundle_overwrite_v35 (s : State) (h : BundleHash) (a b : Status) :
    (s.setBundle h a).setBundle h b = s.setBundle h b := by
  cases s
  simp only [State.setBundle, State.mk.injEq, and_true]
  funext h'
  split_ifs <;> rfl

lemma verifyIfUnreceived_overwrite_v35 (s : State) (h : BundleHash) (st : Status) :
    (s.verifyIfUnreceived h).setBundle h st = s.setBundle h st := by
  unfold State.verifyIfUnreceived
  split_ifs
  · exact setBundle_overwrite_v35 s h _ _
  · rfl

/-- The pin's `Verified` write is overwritten before the calls, in every order but
`statusWriteAfterCalls`; on L1 it is not skipped in the first place. -/
lemma beforeCalls_proofWriteAtV35 {ℓ : LayerAtV35} {v : Variant}
    (hv : ℓ = .l1 ∨ v ≠ .statusWriteAfterCalls) (b : Bundle) (s : State) :
    beforeCalls v b (proofWriteAtV35 ℓ b.hash s) =
      beforeCalls v b (s.verifyIfUnreceived b.hash) := by
  cases ℓ with
  | l1 => rfl
  | l2 =>
    have hv' : v ≠ .statusWriteAfterCalls := by
      rcases hv with h | h
      · cases h
      · exact h
    cases v with
    | deployed => simp [beforeCalls, proofWriteAtV35, verifyIfUnreceived_overwrite_v35]
    | statusWriteAfterCalls => exact absurd rfl hv'
    | callWriteAfterCalls =>
      simp [beforeCalls, proofWriteAtV35, verifyIfUnreceived_overwrite_v35]

/-- **The bisimulation.** -/
theorem execAtV35_eq_exec {ℓ : LayerAtV35} {v : Variant}
    (hv : ℓ = .l1 ∨ v ≠ .statusWriteAfterCalls) :
    ∀ (n : ℕ) (f : FrameAtV35 ℓ) (s : State), execAtV35 ℓ v n f s = exec v n f.toPin s := by
  intro n
  induction n with
  | zero => intro f s; simp [execAtV35, exec]
  | succ n ih =>
    intro f s
    match f with
    | .entry (.execute b ok) cs =>
      simp only [execAtV35, exec, FrameAtV35.toPin, EntryAtV35.toPin, ih,
        beforeCalls_proofWriteAtV35 hv, listToPin_eq_map]
      split_ifs
      · generalize exec v n (Frame.calls b.hash (List.range b.calls) (cs.map CalleeAtV35.toPin))
          (beforeCalls v b (s.verifyIfUnreceived b.hash)) = r
        rcases r with _ | ⟨s₂, l⟩ <;> rfl
      · rfl
    | .entry (.verify b ok) cs =>
      simp only [execAtV35, exec, FrameAtV35.toPin, EntryAtV35.toPin]
    | .entry (.unbundleBundle b req) cs =>
      simp only [execAtV35, exec, FrameAtV35.toPin, EntryAtV35.toPin, ih, listToPin_eq_map]
      split_ifs
      · generalize markCalls (writesCallsFirst v) b.hash 0 req (s.setBundle b.hash .Unbundled) = r₁
        rcases r₁ with _ | s₁
        · rfl
        · generalize exec v n (Frame.calls b.hash (toExecute 0 req) (cs.map CalleeAtV35.toPin))
            s₁ = r
          rcases r with _ | ⟨s₂, l⟩ <;> rfl
      · rfl
    | .calls h [] cs =>
      simp only [execAtV35, exec, FrameAtV35.toPin]
    | .calls h (i :: is) cs =>
      simp only [execAtV35, exec, FrameAtV35.toPin, ih, listToPin_eq_map, toPin_headD,
        List.map_tail]
      generalize exec v n (Frame.target ((cs.map CalleeAtV35.toPin).headD .returns)) s = r
      rcases r with _ | ⟨s₁, l₁⟩
      · rfl
      · generalize exec v n (Frame.calls h is (cs.map CalleeAtV35.toPin).tail) s₁ = r
        rcases r with _ | ⟨s₂, l₂⟩ <;> rfl
    | .target .returns => simp only [execAtV35, exec, FrameAtV35.toPin, toPin_returns]
    | .target .reverts => simp only [execAtV35, exec, FrameAtV35.toPin, toPin_reverts]
    | .target (.calls e inner caught next) =>
      simp only [execAtV35, exec, FrameAtV35.toPin, toPin_calls, ih, listToPin_eq_map]
      generalize exec v n (Frame.entry e.toPin (inner.map CalleeAtV35.toPin)) s = r
      rcases r with _ | ⟨s₁, l₁⟩
      · rfl
      · generalize exec v n (Frame.target next.toPin) s₁ = r
        rcases r with _ | ⟨s₂, l₂⟩ <;> rfl

lemma submitAtV35_eq_submit {ℓ : LayerAtV35} {v : Variant}
    (hv : ℓ = .l1 ∨ v ≠ .statusWriteAfterCalls) (s : State) (t : TxAtV35 ℓ) :
    submitAtV35 ℓ v s t = submit v s t.toPin := by
  unfold submitAtV35 submit
  rw [execAtV35_eq_exec hv]
  rfl

lemma submitAllAtV35_eq_submitAll {ℓ : LayerAtV35} {v : Variant}
    (hv : ℓ = .l1 ∨ v ≠ .statusWriteAfterCalls) :
    ∀ (s : State) (txs : List (TxAtV35 ℓ)),
      submitAllAtV35 ℓ v s txs = submitAll v s (txs.map TxAtV35.toPin)
  | s, [] => rfl
  | s, t :: ts => by
    simp only [submitAllAtV35, submitAll, List.map_cons, submitAtV35_eq_submit hv,
      submitAllAtV35_eq_submitAll hv _ ts]

/-- The deployed order satisfies the translation's condition on both layers. -/
lemma deployed_translatesAtV35 (ℓ : LayerAtV35) :
    ℓ = .l1 ∨ Variant.deployed ≠ .statusWriteAfterCalls :=
  Or.inr (by decide)

/-! ## (a) The translation -/

theorem ExecMatchesPinAtV35 : Properties.ExecMatchesPinAtV35 :=
  fun _ _ hv => execAtV35_eq_exec hv

theorem SubmitAllMatchesPinAtV35 : Properties.SubmitAllMatchesPinAtV35 :=
  fun _ _ hv => submitAllAtV35_eq_submitAll hv

theorem LateStatusWriteSeparatesL2FromPinAtV35 :
    Properties.LateStatusWriteSeparatesL2FromPinAtV35 := by
  unfold Properties.LateStatusWriteSeparatesL2FromPinAtV35; decide

theorem PinMatchWitnessAtV35 : Properties.PinMatchWitnessAtV35 := by
  have h₁ := submitAtV35_eq_submit (deployed_translatesAtV35 .l2) init wNestedAtV35
  have h₂ := submitAtV35_eq_submit (ℓ := .l1) (v := .statusWriteAfterCalls) (Or.inl rfl) init
    wReenterL1AtV35
  refine ⟨h₁, by decide, h₂, by decide⟩

/-! ## (b) Nothing runs twice -/

theorem NoEffectCommittedTwiceAtV35 : Properties.NoEffectCommittedTwiceAtV35 := by
  intro ℓ s txs
  rw [submitAllAtV35_eq_submitAll (deployed_translatesAtV35 ℓ)]
  exact NoEffectCommittedTwice s _

theorem CommittedEffectsWereOpenAtV35 : Properties.CommittedEffectsWereOpenAtV35 := by
  intro ℓ s txs e he
  rw [submitAllAtV35_eq_submitAll (deployed_translatesAtV35 ℓ)] at he ⊢
  exact CommittedEffectsWereOpen s _ e he

theorem WholeBundleExecutionRunsEachCallOnceAtV35 :
    Properties.WholeBundleExecutionRunsEachCallOnceAtV35 := by
  intro ℓ n b ok cs s s' l hx
  rw [execAtV35_eq_exec (deployed_translatesAtV35 ℓ)] at hx
  exact WholeBundleExecutionRunsEachCallOnce n b ok _ s s' l (Or.inr hx)

theorem StatusRecordsExactlyTheCommittedEffectsAtV35 :
    Properties.StatusRecordsExactlyTheCommittedEffectsAtV35 := by
  intro ℓ txs h i
  rw [submitAllAtV35_eq_submitAll (deployed_translatesAtV35 ℓ)]
  exact StatusRecordsExactlyTheCommittedEffects _ h i

theorem NestedExecutionFollowsTheStatusMachineAtV35 :
    Properties.NestedExecutionFollowsTheStatusMachineAtV35 := by
  refine ⟨NestedExecutionFollowsTheStatusMachine.1, fun ℓ s txs hc => ?_⟩
  rw [submitAllAtV35_eq_submitAll (deployed_translatesAtV35 ℓ)]
  exact NestedExecutionFollowsTheStatusMachine.2 s _ hc

private lemma toPin_bundle {ℓ : LayerAtV35} (e : EntryAtV35 ℓ) : e.toPin.bundle = e.bundle := by
  cases e <;> rfl

theorem ReentryForAnExecutingBundleRevertsAtV35 :
    Properties.ReentryForAnExecutingBundleRevertsAtV35 := by
  refine ⟨fun ℓ b s => by simp, fun ℓ n f h s s' l hfe hx => ?_, fun ℓ n e cs s hfe => ?_⟩
  · rw [execAtV35_eq_exec (deployed_translatesAtV35 ℓ)] at hx
    exact ReentryForAnExecutingBundleReverts.2.1 n _ h s s' l hfe hx
  · rw [execAtV35_eq_exec (deployed_translatesAtV35 ℓ)]
    exact ReentryForAnExecutingBundleReverts.2.2 n e.toPin _ s ((toPin_bundle e).symm ▸ hfe)

theorem ReentrantExecutionWitnessAtV35 : Properties.ReentrantExecutionWitnessAtV35 := by
  unfold Properties.ReentrantExecutionWitnessAtV35; decide

/-! ## (c) A failing call rolls the execution back -/

/-- A call loop in which some target always reverts reverts, in every order, on both layers. -/
lemma execAtV35_calls_alwaysReverts (ℓ : LayerAtV35) (v : Variant) (h : BundleHash) :
    ∀ (is : List ℕ) (cs : List (CalleeAtV35 ℓ)) (m : ℕ) (s : State),
      (∃ c ∈ cs.take is.length, AlwaysRevertsAtV35 ℓ v c) →
      execAtV35 ℓ v m (.calls h is cs) s = none
  | [], _, _, _, ⟨_, hc, _⟩ => by simp at hc
  | _ :: _, _, 0, _, _ => by simp [execAtV35]
  | _ :: _, [], _ + 1, _, ⟨_, hc, _⟩ => by simp at hc
  | i :: is, c :: cs, m + 1, s, ⟨c', hc', hr⟩ => by
      simp only [List.length_cons, List.take_succ_cons, List.mem_cons] at hc'
      simp only [execAtV35, List.headD_cons, List.tail_cons]
      rcases hc' with rfl | hc'
      · rw [hr m s]
      · split
        · rename_i s₁ l₁ _
          rw [execAtV35_calls_alwaysReverts ℓ v h is cs m s₁ ⟨c', hc', hr⟩]
        · rfl

theorem AlwaysRevertingTargetRevertsTheExecutionAtV35 :
    Properties.AlwaysRevertingTargetRevertsTheExecutionAtV35 := by
  intro ℓ v n b ok cs s hr
  have hr' : ∃ c ∈ cs.take (List.range b.calls).length, AlwaysRevertsAtV35 ℓ v c := by
    simpa using hr
  cases n with
  | zero => simp [execAtV35]
  | succ n =>
    simp only [execAtV35]
    split_ifs
    · rw [execAtV35_calls_alwaysReverts ℓ v b.hash _ cs n _ hr']
    · rfl

/-- **Splitting a call loop**, as `ReentrancyStrong.exec_calls_append`. -/
lemma execAtV35_calls_append (ℓ : LayerAtV35) (v : Variant) (h : BundleHash) (m : ℕ)
    (is₂ : List ℕ) (cs₂ : List (CalleeAtV35 ℓ)) :
    ∀ (is₁ : List ℕ) (cs₁ : List (CalleeAtV35 ℓ)) (t t' : State) (l : List Effect),
      is₁.length = cs₁.length →
      execAtV35 ℓ v (m + 1 + is₁.length) (.calls h is₁ cs₁) t = some (t', l) →
      execAtV35 ℓ v (m + 1 + is₁.length) (.calls h (is₁ ++ is₂) (cs₁ ++ cs₂)) t =
        (execAtV35 ℓ v (m + 1) (.calls h is₂ cs₂) t').map (fun r => (r.1, l ++ r.2))
  | [], [], t, t', l, _, hx => by
      simp only [List.length_nil, Nat.add_zero, execAtV35, Option.some.injEq,
        Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      rcases hX : execAtV35 ℓ v (m + 1) (.calls h is₂ cs₂) t with _ | ⟨s₃, l₃⟩
      · simp [hX]
      · simp [hX]
  | [], _ :: _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _ => by simp at hlen
  | i :: is₁, c :: cs₁, t, t', l, hlen, hx => by
      have hlen' : is₁.length = cs₁.length := by simpa using hlen
      have hf : m + 1 + (i :: is₁).length = (m + 1 + is₁.length) + 1 := by
        simp only [List.length_cons]; omega
      rw [hf] at hx ⊢
      simp only [execAtV35, List.headD_cons, List.tail_cons, List.cons_append] at hx ⊢
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          rw [execAtV35_calls_append ℓ v h m is₂ cs₂ is₁ cs₁ s₁ s₂ l₂ hlen' heq₂]
          rcases hX : execAtV35 ℓ v (m + 1) (.calls h is₂ cs₂) s₂ with _ | ⟨s₃, l₃⟩
          · simp
          · simp
        · simp at hx
      · simp at hx

/-- The targets, split at `k < cs.length`. -/
lemma targets_split_at_v35 {α : Type} {cs : List α} {k : ℕ} (hk : k < cs.length) :
    cs = cs.take k ++ cs[k] :: cs.drop (k + 1) := by
  rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]

/-- The call loop of a bundle with `n` calls reverts when its first `k` targets commit to `t` and
the target of call `k` reverts from `t`. -/
lemma loop_reverts_where_reached_v35 {ℓ : LayerAtV35} {v : Variant} {m : ℕ} {h : BundleHash}
    {n : ℕ} {cs : List (CalleeAtV35 ℓ)} {k : ℕ} (hk : k < cs.length) (hkn : k < n) {u t : State}
    {l : List Effect}
    (hpre : execAtV35 ℓ v (m + 1 + k) (.calls h (List.range k) (cs.take k)) u = some (t, l))
    (htgt : execAtV35 ℓ v m (.target cs[k]) t = none) :
    execAtV35 ℓ v (m + 1 + k) (.calls h (List.range n) cs) u = none := by
  obtain ⟨rest, hr⟩ := range_split_at hkn
  have hlen : (List.range k).length = (cs.take k).length := by
    simp only [List.length_range, List.length_take]; omega
  have hpre' : execAtV35 ℓ v (m + 1 + (List.range k).length)
      (.calls h (List.range k) (cs.take k)) u = some (t, l) := by
    simpa only [List.length_range] using hpre
  have happ := execAtV35_calls_append ℓ v h m (k :: rest) (cs[k] :: cs.drop (k + 1))
    (List.range k) (cs.take k) u t l hlen hpre'
  have hrest : execAtV35 ℓ v (m + 1) (.calls h (k :: rest) (cs[k] :: cs.drop (k + 1))) t =
      none := by
    simp only [execAtV35, List.headD_cons, htgt]
  rw [hrest, Option.map_none, List.length_range, ← hr, ← targets_split_at_v35 hk] at happ
  exact happ

theorem TargetRevertingWhereReachedRevertsTheExecutionAtV35 :
    Properties.TargetRevertingWhereReachedRevertsTheExecutionAtV35 := by
  intro ℓ v m b ok cs s k hk t l hkb hpre htgt
  have hfuel : m + 2 + k = (m + 1 + k) + 1 := by omega
  rw [hfuel]
  simp only [execAtV35]
  split_ifs
  · rw [loop_reverts_where_reached_v35 hk hkb hpre htgt]
  · rfl

/-- `execute` of an admitted bundle whose targets return, in the deployed order, on both
layers. -/
lemma submitAtV35_execute_returns {ℓ : LayerAtV35} {s : State} {b : Bundle} {ok : Bool}
    (hadm : s.bundle b.hash = .Verified ∨ (s.bundle b.hash = .Unreceived ∧ ok = true)) :
    submitAtV35 ℓ .deployed s ⟨b.calls + 2, .execute b ok, List.replicate b.calls .returns⟩ =
      ((s.setBundle b.hash .FullyExecuted).executeAll b.hash b.calls,
        (List.range b.calls).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]) := by
  unfold submitAtV35
  show commit s (execAtV35 ℓ .deployed (b.calls + 1 + 1) _ s) = _
  rw [execAtV35_eq_exec (deployed_translatesAtV35 ℓ)]
  simp only [FrameAtV35.toPin, EntryAtV35.toPin, listToPin_eq_map, List.map_replicate,
    toPin_returns, exec]
  rw [ite_eq_left hadm, exec_calls_returns .deployed b.hash _ _ _ _
    (fun c hc => (List.mem_replicate.1 hc).2) (by simp)]
  simp [commit, verifyIfUnreceived_overwrite_v35]

theorem FailedAttemptCanBeRetriedAtV35 : Properties.FailedAttemptCanBeRetriedAtV35 := by
  intro ℓ s b fuel cs hu hr
  refine ⟨?_, submitAtV35_execute_returns (Or.inr ⟨hu, rfl⟩)⟩
  simp only [submitAtV35]
  rw [AlwaysRevertingTargetRevertsTheExecutionAtV35 ℓ .deployed fuel b true cs s hr]
  rfl

/-- The non-leaf target `wRevertsAfterWorkAtV35` reverts from every state, in every order. -/
lemma wRevertsAfterWorkAtV35_alwaysReverts (v : Variant) :
    AlwaysRevertsAtV35 .l2 v wRevertsAfterWorkAtV35 := by
  intro m t
  have hrev : ∀ k (u : State), execAtV35 .l2 v k (.target .reverts) u = none := by
    intro k u; cases k <;> simp [execAtV35]
  cases m with
  | zero => simp [execAtV35]
  | succ m =>
    simp only [wRevertsAfterWorkAtV35, execAtV35]
    split
    · rename_i s₁ l₁ _
      rw [hrev m s₁]
    · rfl

theorem RevertingTargetWitnessAtV35 : Properties.RevertingTargetWitnessAtV35 := by
  have hA := wRevertsAfterWorkAtV35_alwaysReverts
  have hsub : submitAtV35 .l2 .deployed init wAttemptAfterWorkAtV35 = (init, []) :=
    (FailedAttemptCanBeRetriedAtV35 .l2 init wA 8 [wRevertsAfterWorkAtV35, .returns] rfl
      ⟨wRevertsAfterWorkAtV35, by simp [wA], hA .deployed⟩).1
  have hlate : ∃ (t : State) (l : List Effect),
      execAtV35 .l2 .deployed (5 + 1 + 1)
          (.calls wA.hash (List.range 1) (wLateReentryAtV35.callees.take 1))
          (beforeCalls .deployed wA (proofWriteAtV35 .l2 wA.hash init)) = some (t, l) ∧
        t.bundle wA.hash = .FullyExecuted ∧
        execAtV35 .l2 .deployed 5
          (.target (reenterAtV35 (executeAtomicBundleAtV35 wA true) false)) t = none := by
    have hcomp : (match execAtV35 .l2 .deployed (5 + 1 + 1)
        (.calls wA.hash (List.range 1) (wLateReentryAtV35.callees.take 1))
        (beforeCalls .deployed wA (proofWriteAtV35 .l2 wA.hash init)) with
        | some (t, _) => decide (t.bundle wA.hash = .FullyExecuted) && (execAtV35 .l2 .deployed 5
            (.target (reenterAtV35 (executeAtomicBundleAtV35 wA true) false)) t).isNone
        | none => false) = true := by decide
    split at hcomp
    · rename_i t l heq
      rw [Bool.and_eq_true, decide_eq_true_iff] at hcomp
      exact ⟨t, l, heq, hcomp.1, Option.isNone_iff_eq_none.mp hcomp.2⟩
    · exact absurd hcomp (by decide)
  have hnone : execAtV35 .l2 .deployed 8
      (.entry (executeAtomicBundleAtV35 wA true) wLateReentryAtV35.callees) init = none := by
    obtain ⟨t, l, hpre, -, htgt⟩ := hlate
    exact TargetRevertingWhereReachedRevertsTheExecutionAtV35 .l2 .deployed 5 wA true
      wLateReentryAtV35.callees init 1 (by decide) t l (by decide) hpre htgt
  have hsubL : submitAtV35 .l2 .deployed init wLateReentryAtV35 = (init, []) := by
    show commit init (execAtV35 .l2 .deployed 8 (.entry (executeAtomicBundleAtV35 wA true)
      wLateReentryAtV35.callees) init) = (init, [])
    rw [hnone]
    rfl
  refine ⟨hA, by decide, by rw [hsub], by rw [hsub]; rfl, by rw [hsub]; rfl, by decide, hlate,
    by decide, by rw [hsubL], by rw [hsubL]; rfl⟩

theorem CaughtReentrantRevertWitnessAtV35 : Properties.CaughtReentrantRevertWitnessAtV35 := by
  unfold Properties.CaughtReentrantRevertWitnessAtV35; decide

/-! ## (d) What changed at v35: the gate -/

theorem VerifiedBundleExecutesWithoutTheGateAtV35 :
    Properties.VerifiedBundleExecutesWithoutTheGateAtV35 := by
  intro ℓ s b hv
  refine ⟨fun fuel ok cs => ?_, submitAtV35_execute_returns (Or.inl hv)⟩
  cases fuel with
  | zero => simp [submitAtV35, execAtV35, commit]
  | succ n => simp [submitAtV35, execAtV35, hv, commit]

/-- A v35 target all of whose entry-point calls satisfy `P` translates to an engine target all of whose
entry-point calls satisfy `Q`, when `P e` gives `Q e.toPin`. -/
private lemma calleeAll_toPin {ℓ : LayerAtV35} {P : EntryAtV35 ℓ → Prop} {Q : Entry → Prop}
    (hPQ : ∀ e, P e → Q e.toPin) {c : CalleeAtV35 ℓ} (hc : CalleeAllAtV35 P c) :
    Faithful.CalleeAll Q c.toPin := by
  induction hc with
  | returns => rw [toPin_returns]; exact .returns
  | reverts => rw [toPin_reverts]; exact .reverts
  | calls hpe _ _ ihi ihn =>
    rw [toPin_calls]
    exact .calls (hPQ _ hpe) (fun c hc => by
      obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
      exact ihi c₀ hc₀) ihn

private lemma txAll_toPin {ℓ : LayerAtV35} {P : EntryAtV35 ℓ → Prop} {Q : Entry → Prop}
    (hPQ : ∀ e, P e → Q e.toPin) {t : TxAtV35 ℓ} (ht : TxAllAtV35 P t) :
    Faithful.TxAll Q t.toPin := by
  refine ⟨hPQ _ ht.1, fun c hc => ?_⟩
  simp only [TxAtV35.toPin, listToPin_eq_map] at hc
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 hc
  exact calleeAll_toPin hPQ (ht.2 c₀ hc₀)

/-- No passing verdict for `h`: neither an accepted inclusion proof nor a passing flow gate for
`h` in the translation. -/
lemma notPassesGate_toPin {ℓ : LayerAtV35} (h : BundleHash) (e : EntryAtV35 ℓ)
    (he : ¬ PassesGateAtV35 h e) :
    ¬ Faithful.ProvesInclusion h e.toPin ∧ ¬ Faithful.PassesFlowGate h e.toPin := by
  cases e with
  | execute b ok => exact ⟨he, fun h => h⟩
  | verify b ok => exact ⟨he, fun h => h⟩
  | unbundleBundle b req => exact ⟨fun h => h, fun h => h⟩

theorem DeliveryNeedsTheGateAtV35 : Properties.DeliveryNeedsTheGateAtV35 := by
  intro ℓ s h txs hu ht
  rw [submitAllAtV35_eq_submitAll (deployed_translatesAtV35 ℓ)]
  refine Faithful.DeliveryNeedsInclusionOrFlowGate s h _ hu (fun t ht' => ?_)
  obtain ⟨t₀, ht₀, rfl⟩ := List.mem_map.1 ht'
  exact txAll_toPin (notPassesGate_toPin h) (ht t₀ ht₀)

theorem GateRoutesWitnessAtV35 : Properties.GateRoutesWitnessAtV35 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_,
    by decide⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact ⟨fun h => Bool.false_ne_true h.2, fun c hc => by cases hc⟩
  · exact ⟨fun h => absurd h.1 (by decide), fun c hc => by cases hc⟩

lemma gateVerdictAtV35_deregister {self : ℕ} {p : ℕ → Bool} {legs : List ℕ} {c : ℕ}
    (hc : c ∈ legs) (hne : c ≠ self) (proofsOk : Bool) :
    gateVerdictAtV35 self (deregisterAtV35 p c) legs proofsOk = false := by
  have hf : legSourceAllowedAtV35 self (deregisterAtV35 p c) c = false := by
    simp [legSourceAllowedAtV35, deregisterAtV35, hne]
  have hall : legs.all (legSourceAllowedAtV35 self (deregisterAtV35 p c)) = false := by
    rw [Bool.eq_false_iff]
    intro h
    rw [List.all_eq_true] at h
    rw [h c hc] at hf
    exact absurd hf (by decide)
  simp [gateVerdictAtV35, hall]

lemma gateVerdictAtV35_allow_again {self : ℕ} {p : ℕ → Bool} {legs : List ℕ} {c : ℕ}
    (hall : legs.all (legSourceAllowedAtV35 self p) = true) :
    gateVerdictAtV35 self (allowAtV35 (deregisterAtV35 p c) c) legs true = true := by
  simp only [gateVerdictAtV35, Bool.true_and, List.all_eq_true] at hall ⊢
  intro x hx
  have hpx := hall x hx
  by_cases hxc : x = c
  · subst hxc; simp [legSourceAllowedAtV35, allowAtV35]
  · simpa [legSourceAllowedAtV35, allowAtV35, deregisterAtV35, hxc] using hpx

theorem ReceiveFilterIsReadAtTheGateAtV35 : Properties.ReceiveFilterIsReadAtTheGateAtV35 := by
  intro self p legs c hall hc hne
  have hoff := gateVerdictAtV35_deregister (p := p) hc hne
  have hon : gateVerdictAtV35 self p legs true = true := by simp [gateVerdictAtV35, hall]
  refine ⟨hoff, gateVerdictAtV35_allow_again hall, fun s b hu => ⟨fun fuel proofsOk cs => ?_, ?_, ?_⟩⟩
  · rw [hoff proofsOk]
    constructor
    · cases fuel with
      | zero => simp [submitAtV35, execAtV35, commit]
      | succ n => simp [submitAtV35, execAtV35, hu, commit]
    · cases fuel with
      | zero => simp [submitAtV35, execAtV35, commit]
      | succ n => simp [submitAtV35, execAtV35, commit]
  · rw [gateVerdictAtV35_allow_again hall]
    exact congrArg Prod.snd (submitAtV35_execute_returns (ℓ := .l2) (Or.inr ⟨hu, rfl⟩))
  · rw [hon, hoff true]
    have h₁ : submitAtV35 .l2 .deployed s (verifyAtomicTxAtV35 b true) =
        (s.setBundle b.hash .Verified, []) := by
      simp [submitAtV35, verifyAtomicTxAtV35, execAtV35, hu, commit]
    have h₂ := submitAtV35_execute_returns (ℓ := .l2) (s := s.setBundle b.hash .Verified) (b := b)
      (ok := false) (Or.inl (by simp))
    simp only [submitAllAtV35, h₁, runAtomicAtV35, executeAtomicBundleAtV35, h₂]
    simp

theorem ReceiveFilterWitnessAtV35 : Properties.ReceiveFilterWitnessAtV35 := by
  unfold Properties.ReceiveFilterWitnessAtV35; decide

/-! ## (e) The order of the writes is load-bearing -/

theorem StatusWriteAfterCallsRunsTwiceAtV35 : Properties.StatusWriteAfterCallsRunsTwiceAtV35 := by
  unfold Properties.StatusWriteAfterCallsRunsTwiceAtV35; decide

theorem CallWriteAfterCallsRunsTwiceAtV35 : Properties.CallWriteAfterCallsRunsTwiceAtV35 := by
  unfold Properties.CallWriteAfterCallsRunsTwiceAtV35; decide

/-! ### The general countermodel for `statusWriteAfterCalls`

On L2 this order is outside the translation, so the run is computed on `execAtV35` directly, as
`Reentrancy.late_atomic_twice` computes it on `exec`: the first call's target re-enters, every
other target returns. -/

/-- A call loop whose targets all return delivers every call and changes nothing, in every order,
on both layers. -/
lemma execAtV35_calls_returns (ℓ : LayerAtV35) (v : Variant) (h : BundleHash) :
    ∀ (is : List ℕ) (cs : List (CalleeAtV35 ℓ)) (m : ℕ) (s : State),
      (∀ c ∈ cs, c = .returns) → is.length < m →
      execAtV35 ℓ v m (.calls h is cs) s = some (s, is.map (Effect.delivered h))
  | [], _, 0, _, _, hm => absurd hm (by simp)
  | _ :: _, _, 0, _, _, hm => absurd hm (by simp)
  | [], _, _ + 1, _, _, _ => by simp [execAtV35]
  | i :: is, cs, m + 1, s, hc, hm => by
      have hhd : cs.headD .returns = .returns := by
        cases cs with
        | nil => rfl
        | cons c cs => exact hc c List.mem_cons_self
      have htl : ∀ c ∈ cs.tail, c = .returns := fun c h => hc c (List.mem_of_mem_tail h)
      simp only [List.length_cons] at hm
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      simp only [execAtV35, hhd]
      rw [execAtV35_calls_returns ℓ v h is cs.tail (k + 1) s htl (by omega)]
      simp

/-- A target that calls `e` and then returns, where `e` commits. -/
lemma execAtV35_reenter {ℓ : LayerAtV35} {v : Variant} {e : EntryAtV35 ℓ} {caught : Bool}
    {m : ℕ} {s s₁ : State} {l₁ : List Effect}
    (he : execAtV35 ℓ v m (.entry e []) s = some (s₁, l₁)) :
    execAtV35 ℓ v (m + 1) (.target (reenterAtV35 e caught)) s = some (s₁, l₁) := by
  have hm : ∃ m', m = m' + 1 := by
    cases m with
    | zero => simp [execAtV35] at he
    | succ m' => exact ⟨m', rfl⟩
  obtain ⟨m', rfl⟩ := hm
  simp only [reenterAtV35, execAtV35, he, List.append_nil]

/-- A call loop over calls `0, …, k` whose first target re-enters `e`, which commits, and whose
other targets return. -/
lemma loop_reenter_first_v35 {ℓ : LayerAtV35} {v : Variant} {h : BundleHash} {k c : ℕ}
    (hc : k < c + 2) {e : EntryAtV35 ℓ} {t u : State} {l : List Effect}
    (he : execAtV35 ℓ v (c + 1) (.entry e []) t = some (u, l)) :
    execAtV35 ℓ v (c + 3) (.calls h (List.range (k + 1)) [reenterAtV35 e false]) t =
      some (u, Effect.delivered h 0 ::
        (l ++ ((List.range k).map Nat.succ).map (Effect.delivered h))) := by
  have e3 : execAtV35 ℓ v (c + 2) (.target (reenterAtV35 e false)) t = some (u, l) :=
    execAtV35_reenter he
  have e4 : execAtV35 ℓ v (c + 2) (.calls h ((List.range k).map Nat.succ) []) u =
      some (u, ((List.range k).map Nat.succ).map (Effect.delivered h)) :=
    execAtV35_calls_returns _ _ _ _ _ _ _ (by simp) (by simpa using hc)
  conv_lhs => rw [List.range_succ_eq_map]
  simp only [execAtV35, List.headD_cons, List.tail_cons, e3, e4]

lemma late_execute_twice_v35 (ℓ : LayerAtV35) (s : State) (b : Bundle) (hpos : 0 < b.calls)
    (hopen : s.bundle b.hash = .Unreceived ∨ s.bundle b.hash = .Verified) :
    ¬ (submitAtV35 ℓ .statusWriteAfterCalls s ⟨b.calls + 5, .execute b true,
        [reenterAtV35 (.execute b true) false]⟩).2.Nodup := by
  obtain ⟨k, hk⟩ : ∃ k, b.calls = k + 1 := ⟨b.calls - 1, by omega⟩
  -- the state the outer calls run against: the bundle is still open
  have hto : (beforeCalls .statusWriteAfterCalls b (proofWriteAtV35 ℓ b.hash s)).bundle b.hash =
        .Unreceived ∨
      (beforeCalls .statusWriteAfterCalls b (proofWriteAtV35 ℓ b.hash s)).bundle b.hash =
        .Verified := by
    cases ℓ with
    | l1 =>
      right
      rcases hopen with hu | hv
      · simp [beforeCalls, proofWriteAtV35, State.verifyIfUnreceived, hu]
      · simp [beforeCalls, proofWriteAtV35, State.verifyIfUnreceived, hv]
    | l2 => simpa [beforeCalls, proofWriteAtV35] using hopen
  set t := beforeCalls .statusWriteAfterCalls b (proofWriteAtV35 ℓ b.hash s) with ht
  -- the re-entrant execution, admitted because the status write has not happened yet
  have e2 : execAtV35 ℓ .statusWriteAfterCalls (k + 2 + 1) (.entry (.execute b true) []) t =
      some (afterCalls .statusWriteAfterCalls b
          (beforeCalls .statusWriteAfterCalls b (proofWriteAtV35 ℓ b.hash t)),
        (List.range (k + 1)).map (Effect.delivered b.hash) ++ [Effect.executed b.hash]) := by
    simp only [execAtV35, and_true]
    rw [ite_eq_left hto.symm, hk,
      execAtV35_calls_returns _ _ _ _ _ _ _ (by simp) (by simp)]
  have e5 := loop_reenter_first_v35 (h := b.hash) (k := k) (by omega) e2
  unfold submitAtV35
  rw [show b.calls + 5 = (k + 2 + 3) + 1 by omega]
  simp only [execAtV35, and_true]
  rw [ite_eq_left hopen.symm, hk, ← ht, e5]
  simp only [commit]
  intro hnd
  rw [List.cons_append, List.nodup_cons] at hnd
  exact hnd.1 (by simp)

lemma deployed_execute_reenter_reverts_v35 (ℓ : LayerAtV35) (s : State) (b : Bundle)
    (hpos : 0 < b.calls) :
    submitAtV35 ℓ .deployed s ⟨b.calls + 5, .execute b true,
      [reenterAtV35 (.execute b true) false]⟩ = (s, []) := by
  have hfe := ReentryForAnExecutingBundleRevertsAtV35.1 ℓ b s
  set t := beforeCalls .deployed b (proofWriteAtV35 ℓ b.hash s) with ht
  have hpre : execAtV35 ℓ .deployed (b.calls + 3 + 1 + 0)
      (.calls b.hash (List.range 0)
        (([reenterAtV35 (.execute b true) false] : List (CalleeAtV35 ℓ)).take 0)) t =
      some (t, []) := by
    simp [execAtV35]
  have htgt : execAtV35 ℓ .deployed (b.calls + 3)
      (.target (([reenterAtV35 (.execute b true) false] : List (CalleeAtV35 ℓ))[0]'(by simp)))
      t = none := by
    show execAtV35 ℓ .deployed ((b.calls + 2) + 1)
      (.target (reenterAtV35 (.execute b true) false)) t = none
    simp [reenterAtV35, execAtV35, hfe]
  have hx := TargetRevertingWhereReachedRevertsTheExecutionAtV35 ℓ .deployed (b.calls + 3) b true
    [reenterAtV35 (.execute b true) false] s 0 (by simp) t [] hpos hpre htgt
  unfold submitAtV35
  show commit s (execAtV35 ℓ .deployed (b.calls + 3 + 2 + 0) _ s) = _
  rw [hx]
  rfl

theorem StatusWriteAfterCallsRunsAnyBundleTwiceAtV35 :
    Properties.StatusWriteAfterCallsRunsAnyBundleTwiceAtV35 :=
  fun ℓ s b hpos hopen =>
    ⟨late_execute_twice_v35 ℓ s b hpos hopen, deployed_execute_reenter_reverts_v35 ℓ s b hpos⟩

theorem CallWriteAfterCallsRunsAnyCallTwiceAtV35 :
    Properties.CallWriteAfterCallsRunsAnyCallTwiceAtV35 := by
  intro ℓ s b hpos hg hc
  have hcw : ℓ = .l1 ∨ Variant.callWriteAfterCalls ≠ .statusWriteAfterCalls := Or.inr (by decide)
  rw [submitAtV35_eq_submit hcw, submitAtV35_eq_submit (deployed_translatesAtV35 ℓ)]
  exact CallWriteAfterCallsRunsAnyCallTwice s b hpos hg hc

end Contracts.InteropHandlerAtV35
