import EraSpec.Contracts.InteropHandlerBase.Properties.ValueLedgerFaithful
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineFaithful
import Mathlib.Tactic

/-!
# Proofs: no inflation, for the handler's own ledger

Two frame invariants, by induction on the budget under the binding premise:

* `exec_bounded`: every delivery of `b.hash` a committed frame logs is of a call below `b.calls`
  (whole-bundle loops run `List.range b.calls`, unbundled loops `toExecute 0 req` with
  `req.length = b.calls`);
* `exec_fullyExecutedHasAllCalls`: a `FullyExecuted` `b.hash` has every call of `b` recorded
  `Executed` (the status write and the call loop of `:126-132` happen together, and nothing
  committed changes either afterwards).

The link is then counting: the committed log has no repeated entry
(`Reentrancy.NoEffectCommittedTwice`), so the delivered indices of `b.hash` are a duplicate-free
sublist of `0, …, b.calls - 1`, and from fresh storage they are exactly the calls recorded
`Executed` (`Reentrancy.StatusRecordsExactlyTheCommittedEffects`).
-/

namespace Contracts.InteropHandler.Faithful

open AttackVectors.BundleStatusMachine

/-! ## Delivered indices -/

lemma toExecute_lt : ∀ {i j : ℕ} {req : List CallStatus}, j ∈ toExecute i req → j < i + req.length
  | _, _, [], h => by simp [toExecute] at h
  | i, j, .Executed :: req, h => by
      rcases List.mem_cons.1 h with h | h
      · simp; omega
      · have := toExecute_lt h; simp; omega
  | i, j, .Cancelled :: req, h => by have := toExecute_lt (i := i + 1) h; simp; omega
  | i, j, .Unprocessed :: req, h => by have := toExecute_lt (i := i + 1) h; simp; omega

/-- The frame's own call loop is over calls of `b`, when it is a loop of `b.hash`. -/
def LoopBounded (b : Bundle) : Frame → Prop
  | .calls h is _ => h = b.hash → ∀ i ∈ is, i < b.calls
  | .entry _ _ => True
  | .target _ => True

theorem exec_bounded (b : Bundle) : ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
    exec .deployed n f s = some (s', l) → FrameAll (NamesOnly b) f → LoopBounded b f →
    ∀ i, Effect.delivered b.hash i ∈ l → i < b.calls := by
  intro n
  induction n with
  | zero => intro f s s' l hx; simp [exec] at hx
  | succ n ih =>
    intro f s s' l hx hf hlb
    match f with
    | .entry (.executeBundle b' ok) cs =>
      obtain ⟨hnb, hcs⟩ := hf
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have hl : LoopBounded b (.calls b'.hash (List.range b'.calls) cs) := by
          intro hh i hi
          have := hnb hh
          simp only [Entry.bundle] at this
          subst this
          exact List.mem_range.1 hi
        intro i hi
        rcases List.mem_append.1 hi with hi | hi
        · exact ih _ _ _ _ heq hcs hl i hi
        · simp at hi
      · simp at hx
    | .entry (.executeAtomicBundle b' ok) cs =>
      obtain ⟨hnb, hcs⟩ := hf
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        have hl : LoopBounded b (.calls b'.hash (List.range b'.calls) cs) := by
          intro hh i hi
          have := hnb hh
          simp only [Entry.bundle] at this
          subst this
          exact List.mem_range.1 hi
        intro i hi
        rcases List.mem_append.1 hi with hi | hi
        · exact ih _ _ _ _ heq hcs hl i hi
        · simp at hi
      · simp at hx
    | .entry (.verifyBundle b' ok) cs =>
      simp only [exec] at hx
      split_ifs at hx with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      intro i hi; simp at hi
    | .entry (.unbundleBundle b' req) cs =>
      obtain ⟨hnb, hcs⟩ := hf
      simp only [exec, writesCallsFirst_deployed] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₁ hm
        split at hx
        · rename_i s₂ l₂ heq
          simp only [afterUnbundle_deployed, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          have hl : LoopBounded b (.calls b'.hash (toExecute 0 req) cs) := by
            intro hh i hi
            have := hnb hh
            simp only [Entry.bundle] at this
            subst this
            have := toExecute_lt hi
            omega
          exact ih _ _ _ _ heq hcs hl
        · simp at hx
      · simp at hx
    | .calls hb [] cs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      intro i hi; simp at hi
    | .calls hb (j :: is) cs =>
      simp only [exec] at hx
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          have hl : LoopBounded b (.calls hb is cs.tail) :=
            fun hh i hi => hlb hh i (List.mem_cons_of_mem _ hi)
          intro i hi
          rcases List.mem_cons.1 hi with hi | hi
          · simp only [Effect.delivered.injEq] at hi
            obtain ⟨rfl, rfl⟩ := hi
            exact hlb rfl _ List.mem_cons_self
          rcases List.mem_append.1 hi with hi | hi
          · exact ih _ _ _ _ heq₁ (calleeAll_headD hf) trivial i hi
          · exact ih _ _ _ _ heq₂ (calleeAll_tail hf) hl i hi
        · simp at hx
      · simp at hx
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      intro i hi; simp at hi
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
            intro i hi
            rcases List.mem_append.1 hi with hi | hi
            · exact ih _ _ _ _ heq₁ ⟨hpe, hinner⟩ trivial i hi
            · exact ih _ _ _ _ heq₂ hnext trivial i hi
          · simp at hx
        · split_ifs at hx
          exact ih _ _ _ _ hx hnext trivial

/-- A `FullyExecuted` `b.hash` has all of `b`'s calls recorded `Executed`. -/
def AllCallsRecorded (b : Bundle) (s : State) : Prop :=
  s.bundle b.hash = .FullyExecuted → ∀ i < b.calls, s.call b.hash i = .Executed

theorem exec_fullyExecutedHasAllCalls (b : Bundle) :
    ∀ (n : ℕ) (f : Frame) (s s' : State) (l : List Effect),
      exec .deployed n f s = some (s', l) → FrameAll (NamesOnly b) f →
      AllCallsRecorded b s → AllCallsRecorded b s' := by
  intro n
  induction n with
  | zero => intro f s s' l hx; simp [exec] at hx
  | succ n ih =>
    intro f s s' l hx hf hinv
    match f with
    | .entry (.executeBundle b' ok) cs =>
      obtain ⟨hnb, hcs⟩ := hf
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        refine ih _ _ _ _ heq hcs ?_
        by_cases hh : b'.hash = b.hash
        · have := hnb hh
          simp only [Entry.bundle] at this
          subst this
          intro _ i hi
          simp [hi]
        · intro hfe i hi
          have hne : b.hash ≠ b'.hash := fun h => hh h.symm
          simp only [beforeCalls_deployed, executeAll_bundle, setBundle_bundle, ite_eq_right hne,
            verifyIfUnreceived_bundle_ne hne] at hfe
          simp only [beforeCalls_deployed, executeAll_call, setBundle_call,
            verifyIfUnreceived_call, hne, false_and, ↓reduceIte]
          exact hinv hfe i hi
      · simp at hx
    | .entry (.executeAtomicBundle b' ok) cs =>
      obtain ⟨hnb, hcs⟩ := hf
      simp only [exec] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₂ l₂ heq
        simp only [afterCalls_deployed, Option.some.injEq, Prod.mk.injEq] at hx
        obtain ⟨rfl, rfl⟩ := hx
        refine ih _ _ _ _ heq hcs ?_
        by_cases hh : b'.hash = b.hash
        · have := hnb hh
          simp only [Entry.bundle] at this
          subst this
          intro _ i hi
          simp [hi]
        · intro hfe i hi
          have hne : b.hash ≠ b'.hash := fun h => hh h.symm
          simp only [beforeCalls_deployed, executeAll_bundle, setBundle_bundle, ite_eq_right hne] at hfe
          simp only [beforeCalls_deployed, executeAll_call, setBundle_call, hne, false_and,
            ↓reduceIte]
          exact hinv hfe i hi
      · simp at hx
    | .entry (.verifyBundle b' ok) cs =>
      simp only [exec] at hx
      split_ifs at hx with hG
      simp only [Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      intro hfe i hi
      by_cases hh : b.hash = b'.hash
      · simp [hh] at hfe
      · simp only [setBundle_bundle, ite_eq_right hh] at hfe
        exact hinv hfe i hi
    | .entry (.unbundleBundle b' req) cs =>
      obtain ⟨-, hcs⟩ := hf
      simp only [exec, writesCallsFirst_deployed] at hx
      split_ifs at hx with hG
      split at hx
      · rename_i s₁ hm
        split at hx
        · rename_i s₂ l₂ heq
          simp only [afterUnbundle_deployed, Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          refine ih _ _ _ _ heq hcs ?_
          obtain ⟨hmb, hmo, -, -⟩ := markCalls_spec req 0 _ s₁ hm
          intro hfe i hi
          rw [hmb] at hfe
          by_cases hh : b.hash = b'.hash
          · simp [hh] at hfe
          · simp only [setBundle_bundle, ite_eq_right hh] at hfe
            rw [hmo _ _ hh]
            exact hinv hfe i hi
        · simp at hx
      · simp at hx
    | .calls hb [] cs =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hinv
    | .calls hb (j :: is) cs =>
      simp only [exec] at hx
      split at hx
      · rename_i s₁ l₁ heq₁
        split at hx
        · rename_i s₂ l₂ heq₂
          simp only [Option.some.injEq, Prod.mk.injEq] at hx
          obtain ⟨rfl, rfl⟩ := hx
          exact ih _ _ _ _ heq₂ (calleeAll_tail hf) (ih _ _ _ _ heq₁ (calleeAll_headD hf) hinv)
        · simp at hx
      · simp at hx
    | .target .returns =>
      simp only [exec, Option.some.injEq, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact hinv
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
            exact ih _ _ _ _ heq₂ hnext (ih _ _ _ _ heq₁ ⟨hpe, hinner⟩ hinv)
          · simp at hx
        · split_ifs at hx
          exact ih _ _ _ _ hx hnext hinv

/-! ## Transactions -/

lemma submitAll_bounded (b : Bundle) : ∀ (s : State) (txs : List Tx),
    (∀ t ∈ txs, TxAll (NamesOnly b) t) →
    ∀ i, Effect.delivered b.hash i ∈ (submitAll .deployed s txs).2 → i < b.calls
  | s, [], _, i, hi => by simp [submitAll] at hi
  | s, t :: ts, ht, i, hi => by
    simp only [submitAll, List.mem_append] at hi
    rcases hi with hi | hi
    · revert hi
      unfold submit
      cases hx : exec .deployed t.fuel (.entry t.entry t.callees) s with
      | none => simp [commit]
      | some r =>
        obtain ⟨s', l⟩ := r
        exact exec_bounded b _ _ _ _ _ hx (ht t List.mem_cons_self) trivial i
    · exact submitAll_bounded b _ ts (fun t' ht' => ht t' (List.mem_cons_of_mem _ ht')) i hi

lemma submitAll_fullyExecutedHasAllCalls (b : Bundle) : ∀ (s : State) (txs : List Tx),
    (∀ t ∈ txs, TxAll (NamesOnly b) t) → AllCallsRecorded b s →
    AllCallsRecorded b (submitAll .deployed s txs).1
  | s, [], _, hinv => hinv
  | s, t :: ts, ht, hinv => by
    have h1 : AllCallsRecorded b (submit .deployed s t).1 := by
      unfold submit
      cases hx : exec .deployed t.fuel (.entry t.entry t.callees) s with
      | none => exact hinv
      | some r =>
        obtain ⟨s', l⟩ := r
        exact exec_fullyExecutedHasAllCalls b _ _ _ _ _ hx (ht t List.mem_cons_self) hinv
    exact submitAll_fullyExecutedHasAllCalls b _ ts
      (fun t' ht' => ht t' (List.mem_cons_of_mem _ ht')) h1

theorem ReleasesAreTheBundlesCalls : Properties.ReleasesAreTheBundlesCalls :=
  fun s b txs ht => submitAll_bounded b s txs ht

/-! ## Counting -/

/-- The indices of `h`'s deliveries in a log, in order. -/
def deliveredIdx (h : BundleHash) : List Effect → List ℕ :=
  List.filterMap fun e => match e with
    | .delivered h' i => if h' = h then some i else none
    | .executed _ => none

lemma releasedFor_eq (val : CallValues) (h : BundleHash) :
    ∀ l : List Effect, releasedFor val h l = ((deliveredIdx h l).map val).sum
  | [] => rfl
  | .delivered h' i :: l => by
      by_cases hh : h' = h
      · simp [releasedFor, deliveredIdx, hh, releasedFor_eq val h l]
      · simp [releasedFor, deliveredIdx, hh, releasedFor_eq val h l]
  | .executed _ :: l => by simp [releasedFor, deliveredIdx, releasedFor_eq val h l]

lemma mem_deliveredIdx {h : BundleHash} {l : List Effect} {i : ℕ} :
    i ∈ deliveredIdx h l ↔ Effect.delivered h i ∈ l := by
  unfold deliveredIdx
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hm⟩
    cases e with
    | delivered h' j =>
      simp only at hm
      split_ifs at hm with hh
      cases hm; subst hh; exact he
    | executed _ => simp at hm
  · intro he
    exact ⟨_, he, by simp⟩

lemma deliveredIdx_nodup {h : BundleHash} {l : List Effect} (hl : l.Nodup) :
    (deliveredIdx h l).Nodup := by
  refine List.Nodup.filterMap ?_ hl
  intro a a' i ha ha'
  cases a with
  | executed _ => simp at ha
  | delivered h₁ j₁ =>
    cases a' with
    | executed _ => simp at ha'
    | delivered h₂ j₂ =>
      simp only [Option.mem_def] at ha ha'
      split_ifs at ha ha' with e₁ e₂
      cases ha; cases ha'; subst e₁; subst e₂; rfl

lemma sum_filter_map (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ) :
    ∀ L : List ℕ, ((L.filter fun i => decide (p i)).map f).sum =
      (L.map fun i => if p i then f i else 0).sum
  | [] => rfl
  | a :: L => by
      by_cases ha : p a
      · simp [ha, sum_filter_map p f L]
      · simp [ha, sum_filter_map p f L]

/-- A duplicate-free list of indices below `n` sums like its indicator over `0, …, n-1`. -/
lemma sum_nodup_bounded (f : ℕ → ℕ) {D : List ℕ} {n : ℕ} (hd : D.Nodup) (hb : ∀ i ∈ D, i < n) :
    (D.map f).sum = ((List.range n).map fun i => if i ∈ D then f i else 0).sum := by
  have hperm : D.Perm ((List.range n).filter fun i => decide (i ∈ D)) := by
    rw [List.perm_ext_iff_of_nodup hd (List.nodup_range.filter _)]
    intro i
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨fun hi => ⟨hb i hi, hi⟩, fun hi => hi.2⟩
  rw [(hperm.map f).sum_eq, sum_filter_map]

lemma releasedSum_map (val : CallValues) (st : ℕ → CallStatus) :
    ∀ L : List ℕ, releasedSum (L.map fun i => (val i, st i)) =
      (L.map fun i => if st i = .Executed then val i else 0).sum
  | [] => rfl
  | a :: L => by simp [releasedSum, releasedSum_map val st L]

lemma collectedSum_map (val : CallValues) (st : ℕ → CallStatus) :
    ∀ L : List ℕ, collectedSum (L.map fun i => (val i, st i)) = (L.map val).sum
  | [] => rfl
  | a :: L => by simp [collectedSum, collectedSum_map val st L]

theorem ReleaseIsTheHandlerLedger : Properties.ReleaseIsTheHandlerLedger := by
  intro val b txs ht
  refine ⟨?_, collectedSum_map val _ _⟩
  have hnd := deliveredIdx_nodup (h := b.hash) (NoEffectCommittedTwice init txs)
  have hbd : ∀ i ∈ deliveredIdx b.hash (submitAll .deployed init txs).2, i < b.calls :=
    fun i hi => submitAll_bounded b init txs ht i (mem_deliveredIdx.1 hi)
  rw [releasedFor_eq, sum_nodup_bounded val hnd hbd, handlerLedger, releasedSum_map]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  have hrec := (StatusRecordsExactlyTheCommittedEffects txs b.hash i).1
  by_cases hi : Effect.delivered b.hash i ∈ (submitAll .deployed init txs).2
  · rw [ite_eq_left (mem_deliveredIdx.2 hi), ite_eq_left (hrec.2 hi)]
  · rw [ite_eq_right (fun h => hi (mem_deliveredIdx.1 h)), ite_eq_right (fun h => hi (hrec.1 h))]

theorem HandlerReleasesAtMostCollected : Properties.HandlerReleasesAtMostCollected := by
  intro val b txs ht
  obtain ⟨h1, h2⟩ := ReleaseIsTheHandlerLedger val b txs ht
  rw [h1, ← h2]
  exact released_le_collected _

theorem ExecutedBundleReleasesAllCollected : Properties.ExecutedBundleReleasesAllCollected := by
  intro val b txs ht he
  obtain ⟨h1, h2⟩ := ReleaseIsTheHandlerLedger val b txs ht
  have hfe := (StatusRecordsExactlyTheCommittedEffects txs b.hash 0).2.2 he
  have hall := submitAll_fullyExecutedHasAllCalls b init txs ht (fun h => absurd h (by
    simp [init])) hfe
  rw [h1, ← h2]
  refine released_eq_collected_of_all_executed _ fun p hp => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  exact hall i (List.mem_range.1 hi)

/-! ## Witnesses -/

lemma txAll_nil_callees {P : Entry → Prop} {t : Tx} (he : P t.entry) (hc : t.callees = []) :
    TxAll P t :=
  ⟨he, fun c h => by rw [hc] at h; cases h⟩

theorem SharedHashBreaksTheLedger : Properties.SharedHashBreaksTheLedger := by
  refine ⟨rfl, by decide, fun h => absurd (h.1 rfl) (by decide), by decide, by decide⟩

theorem LedgerWitness : Properties.LedgerWitness := by
  refine ⟨?_, by decide, by decide, by decide, by decide,
    txAll_nil_callees (fun _ => rfl) rfl, by decide⟩
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl
  · exact txAll_nil_callees (fun _ => rfl) rfl
  · exact txAll_nil_callees (fun _ => rfl) rfl

end Contracts.InteropHandler.Faithful
