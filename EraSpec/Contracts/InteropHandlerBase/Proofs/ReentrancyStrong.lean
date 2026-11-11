import EraSpec.Contracts.InteropHandlerBase.Properties.ReentrancyStrong
import EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy
import Mathlib.Tactic

/-!
# Proofs: a target that reverts — not only the leaf `reverts` — rolls the execution back

Two loop lemmas, valid in every write order. `exec_calls_alwaysReverts` generalises
`exec_calls_reverts` (topic `Reentrancy`) from the leaf `Callee.reverts` to any target that
reverts from every state. `exec_calls_append` splits a call loop at the same point in its calls
and its targets: the loop over `is₁ ++ is₂` is the loop over `is₁`, then the loop over `is₂` from
the state where the first ended, with the budget the first one left. Splitting the deployed loop
`List.range b.calls` at call `k` and failing its first target there (`loop_first_fails`) gives
the state-dependent form.
-/

namespace Contracts.InteropHandler

/-- A call loop in which some target always reverts reverts, in every order. -/
lemma exec_calls_alwaysReverts (v : Variant) (h : BundleHash) :
    ∀ (is : List ℕ) (cs : List Callee) (m : ℕ) (s : State),
      (∃ c ∈ cs.take is.length, AlwaysReverts v c) → exec v m (.calls h is cs) s = none
  | [], _, _, _, ⟨_, hc, _⟩ => by simp at hc
  | _ :: _, _, 0, _, _ => by simp [exec]
  | _ :: _, [], _ + 1, _, ⟨_, hc, _⟩ => by simp at hc
  | i :: is, c :: cs, m + 1, s, ⟨c', hc', hr⟩ => by
      simp only [List.length_cons, List.take_succ_cons, List.mem_cons] at hc'
      simp only [exec, List.headD_cons, List.tail_cons]
      rcases hc' with rfl | hc'
      · rw [hr m s]
      · split
        · rename_i s₁ l₁ _
          rw [exec_calls_alwaysReverts v h is cs m s₁ ⟨c', hc', hr⟩]
        · rfl

theorem AlwaysRevertingTargetRevertsTheExecution :
    Properties.AlwaysRevertingTargetRevertsTheExecution := by
  intro v n b ok cs s hr
  have hr' : ∃ c ∈ cs.take (List.range b.calls).length, AlwaysReverts v c := by simpa using hr
  refine ⟨?_, ?_⟩
  · cases n with
    | zero => simp [exec]
    | succ n =>
      simp only [exec]
      split_ifs
      · rw [exec_calls_alwaysReverts v b.hash _ cs n _ hr']
      · rfl
  · cases n with
    | zero => simp [exec]
    | succ n =>
      simp only [exec]
      split_ifs
      · rw [exec_calls_alwaysReverts v b.hash _ cs n _ hr']
      · rfl

/-- **Splitting a call loop.** When the calls and the targets are split at the same point, the
loop over `is₁ ++ is₂` runs the loop over `is₁`, then the loop over `is₂` from the state where
the first ended, with the budget the first one left; its log is the two logs in order. -/
lemma exec_calls_append (v : Variant) (h : BundleHash) (m : ℕ) (is₂ : List ℕ)
    (cs₂ : List Callee) :
    ∀ (is₁ : List ℕ) (cs₁ : List Callee) (t t' : State) (l : List Effect),
      is₁.length = cs₁.length →
      exec v (m + 1 + is₁.length) (.calls h is₁ cs₁) t = some (t', l) →
      exec v (m + 1 + is₁.length) (.calls h (is₁ ++ is₂) (cs₁ ++ cs₂)) t =
        (exec v (m + 1) (.calls h is₂ cs₂) t').map (fun r => (r.1, l ++ r.2))
  | [], [], t, t', l, _, hx => by
      simp only [List.length_nil, Nat.add_zero, exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      rcases hX : exec v (m + 1) (.calls h is₂ cs₂) t with _ | ⟨s₃, l₃⟩
      · simp [hX]
      · simp [hX]
  | [], _ :: _, _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, _, hlen, _ => by simp at hlen
  | i :: is₁, c :: cs₁, t, t', l, hlen, hx => by
      have hlen' : is₁.length = cs₁.length := by simpa using hlen
      have hf : m + 1 + (i :: is₁).length = (m + 1 + is₁.length) + 1 := by
        simp only [List.length_cons]; omega
      rw [hf] at hx ⊢
      simp only [exec, List.headD_cons, List.tail_cons, List.cons_append] at hx ⊢
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          rw [exec_calls_append v h m is₂ cs₂ is₁ cs₁ s₁ s₂ l₂ hlen' heq₂]
          rcases hX : exec v (m + 1) (.calls h is₂ cs₂) s₂ with _ | ⟨s₃, l₃⟩
          · simp
          · simp
        · simp at hx
      · simp at hx

/-- `List.range n`, split at `k < n`. -/
lemma range_split_at {k n : ℕ} (hk : k < n) :
    ∃ rest, List.range n = List.range k ++ k :: rest := by
  refine ⟨(List.range (n - k - 1)).map (fun x => k + (x + 1)), ?_⟩
  have hn : n = k + ((n - k - 1) + 1) := by omega
  conv_lhs => rw [hn, List.range_add, List.range_succ_eq_map]
  simp [Function.comp_def]

/-- The targets, split at `k < cs.length`. -/
lemma targets_split_at {cs : List Callee} {k : ℕ} (hk : k < cs.length) :
    cs = cs.take k ++ cs[k] :: cs.drop (k + 1) := by
  rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]

/-- The call loop of a bundle with `n` calls reverts when its first `k` targets commit to `t`
and the target of call `k` reverts from `t`. -/
lemma loop_reverts_where_reached {v : Variant} {m : ℕ} {h : BundleHash} {n : ℕ}
    {cs : List Callee} {k : ℕ} (hk : k < cs.length) (hkn : k < n) {u t : State}
    {l : List Effect}
    (hpre : exec v (m + 1 + k) (.calls h (List.range k) (cs.take k)) u = some (t, l))
    (htgt : exec v m (.target cs[k]) t = none) :
    exec v (m + 1 + k) (.calls h (List.range n) cs) u = none := by
  obtain ⟨rest, hr⟩ := range_split_at hkn
  have hlen : (List.range k).length = (cs.take k).length := by
    simp only [List.length_range, List.length_take]; omega
  have hpre' : exec v (m + 1 + (List.range k).length) (.calls h (List.range k) (cs.take k)) u =
      some (t, l) := by
    simpa only [List.length_range] using hpre
  have happ := exec_calls_append v h m (k :: rest) (cs[k] :: cs.drop (k + 1)) (List.range k)
    (cs.take k) u t l hlen hpre'
  have hrest : exec v (m + 1) (.calls h (k :: rest) (cs[k] :: cs.drop (k + 1))) t = none :=
    loop_first_fails htgt
  rw [hrest, Option.map_none, List.length_range, ← hr, ← targets_split_at hk] at happ
  exact happ

theorem TargetRevertingWhereReachedRevertsTheExecution :
    Properties.TargetRevertingWhereReachedRevertsTheExecution := by
  intro v m b ok cs s k hk t l hkb
  have hfuel : m + 2 + k = (m + 1 + k) + 1 := by omega
  refine ⟨fun hpre htgt => ?_, fun hpre htgt => ?_⟩
  · rw [hfuel]
    simp only [exec]
    split_ifs
    · rw [loop_reverts_where_reached hk hkb hpre htgt]
    · rfl
  · rw [hfuel]
    simp only [exec]
    split_ifs
    · rw [loop_reverts_where_reached hk hkb hpre htgt]
    · rfl

theorem FailedAttemptWithAlwaysRevertingTargetCanBeRetried :
    Properties.FailedAttemptWithAlwaysRevertingTargetCanBeRetried := by
  intro s b fuel cs hu hr
  refine ⟨?_, ?_⟩
  · simp only [submit]
    rw [(AlwaysRevertingTargetRevertsTheExecution .deployed fuel b true cs s hr).1]
    rfl
  · simp only [submit]
    rw [exec_atomic_returns hu]
    rfl

/-- By recursion on the continuation `next`: whatever the call before it does, the target goes
on as `next` (or reverts, when the call fails uncaught). -/
lemma endsInRevert_alwaysReverts (v : Variant) :
    ∀ c : Callee, c.endsInRevert = true → AlwaysReverts v c
  | .returns, h, _, _ => by simp [Callee.endsInRevert] at h
  | .reverts, _, m, t => by cases m <;> simp [exec]
  | .calls e inner caught next, h, m, t => by
      have ih := endsInRevert_alwaysReverts v next h
      cases m with
      | zero => simp [exec]
      | succ m =>
        simp only [exec]
        split
        · rename_i s₁ l₁ _
          rw [ih m s₁]
        · cases caught
          · rfl
          · simp [ih m t]

theorem EndsInRevertAlwaysReverts : Properties.EndsInRevertAlwaysReverts :=
  endsInRevert_alwaysReverts

theorem RevertingTargetBeyondTheLeafWitness : Properties.RevertingTargetBeyondTheLeafWitness := by
  have hA : ∀ v, AlwaysReverts v wRevertsAfterWork :=
    fun v => EndsInRevertAlwaysReverts v _ rfl
  have hsub : submit .deployed init wAttemptAfterWork = (init, []) :=
    (FailedAttemptWithAlwaysRevertingTargetCanBeRetried init wA 8
      [wRevertsAfterWork, .returns] rfl
      ⟨wRevertsAfterWork, by simp [wA], hA .deployed⟩).1
  have hsome : (exec .deployed 6 (.target wReenterOuterUncaught) init).isSome = true := by
    decide
  -- `wLateReentry`: the prefix over call 0 commits, and call 1's target reverts where reached.
  have hlate : ∃ (t : State) (l : List Effect),
      exec .deployed (5 + 1 + 1) (.calls wA.hash (List.range 1) (wLateReentry.callees.take 1))
          (beforeCalls .deployed wA init) = some (t, l) ∧
        exec .deployed 5 (.target wReenterOuter) t = none := by
    have hcomp : (match exec .deployed (5 + 1 + 1) (.calls wA.hash (List.range 1)
        (wLateReentry.callees.take 1)) (beforeCalls .deployed wA init) with
        | some (t, _) => (exec .deployed 5 (.target wReenterOuter) t).isNone
        | none => false) = true := by decide
    split at hcomp
    · rename_i t l heq
      exact ⟨t, l, heq, Option.isNone_iff_eq_none.mp hcomp⟩
    · exact absurd hcomp (by decide)
  have hnone : exec .deployed 8 (.entry (.executeAtomicBundle wA true) wLateReentry.callees)
      init = none := by
    obtain ⟨t, l, hpre, htgt⟩ := hlate
    exact (TargetRevertingWhereReachedRevertsTheExecution .deployed 5 wA true
      wLateReentry.callees init 1 (by decide) t l (by decide)).1 hpre htgt
  have hsubL : submit .deployed init wLateReentry = (init, []) := by
    show commit init (exec .deployed 8 (.entry (.executeAtomicBundle wA true)
      wLateReentry.callees) init) = (init, [])
    rw [hnone]
    rfl
  refine ⟨hA, ?_, by rw [hsub], by rw [hsub]; rfl, by rw [hsub]; rfl, by decide, ?_,
    Option.isNone_iff_eq_none.mp (by decide), hsome, ?_, by decide, ?_, hlate, by decide,
    by rw [hsubL], by rw [hsubL]; rfl⟩
  · simp [wAttemptAfterWork, wRevertsAfterWork, wA]
  · simp [wNestedUncaught, reenter, wA]
  · intro hall
    rw [hall 6 init] at hsome
    exact absurd hsome (by decide)
  · simp [wLateReentry, wWorkThenReturn, wReenterOuter, reenter, wA]

end Contracts.InteropHandler
