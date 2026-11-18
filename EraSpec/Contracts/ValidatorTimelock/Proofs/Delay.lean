import EraSpec.Contracts.ValidatorTimelock.Properties.Delay
import EraSpec.Contracts.ValidatorTimelock.Proofs.Model

/-!
# Proofs: the execution delay

The headline is three facts chained: the commit stores `now % 2^32 = now`
(`post_committedAt_of_commits`), the calls in between leave that slot alone
(`run_committedAt_frame`), and the execute's check reads it with the enforced delay of its own
state. The commit-time form adds that the enforced delay never falls along calls that are not
owner setters (`step_enforced_mono`). The witnesses are computed with `decide` on `exec`.
-/

namespace Contracts.ValidatorTimelock

/-! ## The enforced delay along calls -/

lemma enforcedDelay_after_increase {s : State} {c : Address} {d : ℕ} (h : enforcedDelay s c < d) :
    enforcedDelay { s with chainDelay := upd s.chainDelay c d } c = d := by
  rw [enforcedDelay_eq_max] at h ⊢
  simp only [upd_same]
  exact max_eq_left (le_of_lt (lt_of_le_of_lt (le_max_right _ _) h))

lemma step_enforced_mono {k : Call} {s s' : State} (h : step k s = some s')
    (hk : ¬ k.action.mayLowerDelay) (c : Address) : enforcedDelay s c ≤ enforcedDelay s' c := by
  rcases k with ⟨e, x, a⟩
  cases a with
  | increaseChainExecutionDelay c₀ d =>
    obtain ⟨_, _, hlt, rfl⟩ := increaseChainExecutionDelay_eq_some.mp h
    by_cases hc : c = c₀
    · subst hc
      rw [enforcedDelay_after_increase hlt]
      exact le_of_lt hlt
    · rw [enforcedDelay_eq_max, enforcedDelay_eq_max]
      simp only [upd_other _ _ hc, le_refl]
  | initializeTimelock o d => exact (hk trivial).elim
  | setExecutionDelay d => exact (hk trivial).elim
  | setChainExecutionDelay c₀ d => exact (hk trivial).elim
  | _ => rw [step_post h]; exact le_rfl

lemma run_enforced_mono :
    ∀ {s s' : State} {ks : List Call}, Run s ks s' → (∀ k ∈ ks, ¬ k.action.mayLowerDelay) →
      ∀ c, enforcedDelay s c ≤ enforcedDelay s' c
  | _, _, _, .nil _, _, _ => le_rfl
  | _, _, _, .cons (k := k) h1 h2, hno, c =>
      le_trans (step_enforced_mono h1 (hno k List.mem_cons_self) c)
        (run_enforced_mono h2 (fun k' hk' => hno k' (List.mem_cons_of_mem _ hk')) c)

/-! ## The delay after a commit -/

/-- The core of both headline forms: the stored timestamp of `i` when the execute runs is the
commit's own time. -/
lemma committedAt_at_execute {s s₁ s₂ : State} {kc : Call} {mid : List Call} {c : Address}
    {i : ℕ} (hc : step kc s = some s₁) (hmid : Run s₁ mid s₂) (hcom : kc.action.commits c i)
    (hno : ∀ k ∈ mid, ¬ k.action.commits c i) (hnow : kc.env.now < UINT32) :
    s₂.committedAt c i = kc.env.now := by
  rw [run_committedAt_frame hmid hno, step_post hc, post_committedAt_of_commits hcom,
    Nat.mod_eq_of_lt hnow]

/-- What a successful execute's check gives for one batch of its range. -/
lemma execute_check {ke : Call} {s₂ s₃ : State} {c : Address} {lo hi i : ℕ}
    (he : step ke s₂ = some s₃) (hea : ke.action = .executeBatches c lo hi) (hlo : lo ≤ i)
    (hhi : i ≤ hi) : s₂.committedAt c i + enforcedDelay s₂ c ≤ ke.env.now := by
  rw [step_eq_of_action hea] at he
  exact (executeBatches_eq_some.mp he).2.2.1 i hhi hlo

theorem ExecutionWaitsForTheDelay : Properties.ExecutionWaitsForTheDelay := by
  intro s s₁ s₂ s₃ kc ke mid c i lo hi hc hmid he hcom hno hea hlo hhi hnow
  have h1 := committedAt_at_execute hc hmid hcom hno hnow
  have h2 := execute_check he hea hlo hhi
  rw [h1] at h2
  exact h2

/-- Re-commits at clocks between `t` and `2^32` keep the stored timestamp at least `t`. -/
lemma run_committedAt_ge {c : Address} {i t : ℕ} :
    ∀ {s s' : State} {ks : List Call}, Run s ks s' → t ≤ s.committedAt c i →
      (∀ k ∈ ks, k.action.commits c i → t ≤ k.env.now ∧ k.env.now < UINT32) →
      t ≤ s'.committedAt c i
  | _, _, _, .nil _, h, _ => h
  | _, _, _, .cons (k := k) h1 h2, h, hall => by
      apply run_committedAt_ge h2 _ (fun k' hk' => hall k' (List.mem_cons_of_mem _ hk'))
      rw [step_post h1]
      by_cases hk : k.action.commits c i
      · rw [post_committedAt_of_commits hk]
        obtain ⟨h3, h4⟩ := hall k List.mem_cons_self hk
        rw [Nat.mod_eq_of_lt h4]; exact h3
      · rw [post_committedAt_of_not_commits hk]; exact h

theorem ExecutionWaitsForEveryEarlierCommit : Properties.ExecutionWaitsForEveryEarlierCommit := by
  intro s s₁ s₂ s₃ kc ke mid c i lo hi hc hmid he hcom hre hea hlo hhi hnow
  have h1 : s₁.committedAt c i = kc.env.now := by
    rw [step_post hc, post_committedAt_of_commits hcom, Nat.mod_eq_of_lt hnow]
  have h2 := run_committedAt_ge hmid (le_of_eq h1.symm) hre
  have h3 := execute_check he hea hlo hhi
  omega

/-- A commit leaves both delays alone. -/
lemma commit_enforced {kc : Call} {s s₁ : State} {c c' : Address} {i : ℕ}
    (hc : step kc s = some s₁) (hcom : kc.action.commits c i) :
    enforcedDelay s₁ c' = enforcedDelay s c' := by
  rcases kc with ⟨e, x, a⟩
  cases a with
  | commitBatches c₀ lo hi =>
    obtain ⟨_, _, _, rfl⟩ := commitBatches_eq_some.mp hc
    rfl
  | _ => simp only [Action.commits] at hcom

theorem ExecutionWaitsForTheCommitTimeDelay : Properties.ExecutionWaitsForTheCommitTimeDelay := by
  intro s s₁ s₂ s₃ kc ke mid c i lo hi hc hmid he hcom hno hlow hea hlo hhi hnow
  have h1 := ExecutionWaitsForTheDelay s s₁ s₂ s₃ kc ke mid c i lo hi hc hmid he hcom hno hea hlo
    hhi hnow
  have h2 := run_enforced_mono hmid hlow c
  rw [commit_enforced hc hcom] at h2
  omega

theorem OnlyCommitsWriteTimestamps : Properties.OnlyCommitsWriteTimestamps := by
  intro k s s' c i h
  rw [step_post h]
  exact ⟨post_committedAt_of_not_commits, post_committedAt_of_commits⟩

/-! ## Who moves the delay -/

theorem EnforcedDelayGrowsWithoutAnOwnerSetter :
    Properties.EnforcedDelayGrowsWithoutAnOwnerSetter := by
  intro s s' ks h hno c
  exact run_enforced_mono h hno c

theorem IncreaseStrictlyRaisesItsChain : Properties.IncreaseStrictlyRaisesItsChain := by
  intro e x c d s s' h
  obtain ⟨hadm, _, hlt, rfl⟩ := increaseChainExecutionDelay_eq_some.mp h
  refine ⟨hadm, ?_, enforcedDelay_after_increase hlt, rfl, fun c' hc' => upd_other _ _ hc'⟩
  rw [enforcedDelay_after_increase hlt]
  exact hlt

theorem DelayWriters : Properties.DelayWriters := by
  intro k s s' h
  have hs := step_post h
  rcases k with ⟨e, x, a⟩
  refine ⟨fun hne => ?_, fun c hne => ?_⟩
  · cases a with
    | initializeTimelock o d => exact Or.inr ⟨o, d, rfl, (initializeTimelock_eq_some.mp h).1⟩
    | setExecutionDelay d => exact Or.inl ⟨d, rfl, (setExecutionDelay_eq_some.mp h).1⟩
    | _ => exact absurd (by rw [hs]; rfl) hne
  · cases a with
    | setChainExecutionDelay c₀ d =>
      by_cases hc : c = c₀
      · subst hc
        exact Or.inl ⟨d, rfl, (setChainExecutionDelay_eq_some.mp h).1⟩
      · exact absurd (by rw [hs]; exact upd_other _ _ hc) hne
    | increaseChainExecutionDelay c₀ d =>
      by_cases hc : c = c₀
      · subst hc
        obtain ⟨hadm, _, hlt, _⟩ := increaseChainExecutionDelay_eq_some.mp h
        exact Or.inr ⟨d, rfl, hadm, hlt⟩
      · exact absurd (by rw [hs]; exact upd_other _ _ hc) hne
    | _ => exact absurd (by rw [hs]; rfl) hne

/-! ## The 30-day bound -/

lemma step_bounded {k : Call} {s s' : State} (hb : Bounded s) (h : step k s = some s') :
    Bounded s' := by
  obtain ⟨h1, h2, h3⟩ := hb
  rcases k with ⟨e, x, a⟩
  cases a with
  | initializeTimelock o d =>
    obtain ⟨_, hd, rfl⟩ := initializeTimelock_eq_some.mp h; exact ⟨hd, h2, h3⟩
  | setExecutionDelay d =>
    obtain ⟨_, hd, rfl⟩ := setExecutionDelay_eq_some.mp h; exact ⟨hd, h2, h3⟩
  | setChainExecutionDelay c d =>
    obtain ⟨_, hd, rfl⟩ := setChainExecutionDelay_eq_some.mp h
    refine ⟨h1, fun c' => ?_, h3⟩
    by_cases hc : c' = c
    · subst hc; simp only [upd_same]; exact hd
    · simp only [upd_other _ _ hc]; exact h2 c'
  | increaseChainExecutionDelay c d =>
    obtain ⟨_, hd, _, rfl⟩ := increaseChainExecutionDelay_eq_some.mp h
    refine ⟨h1, fun c' => ?_, h3⟩
    by_cases hc : c' = c
    · subst hc; simp only [upd_same]; exact hd
    · simp only [upd_other _ _ hc]; exact h2 c'
  | commitBatches c lo hi =>
    obtain ⟨_, _, _, rfl⟩ := commitBatches_eq_some.mp h
    refine ⟨h1, h2, fun c' i => ?_⟩
    simp only [recordCommit]
    split_ifs
    · exact Nat.mod_lt _ (by decide)
    · exact h3 c' i
  | _ => rw [step_post h]; exact ⟨h1, h2, h3⟩

lemma run_bounded : ∀ {s s' : State} {ks : List Call}, Bounded s → Run s ks s' → Bounded s'
  | _, _, _, hb, .nil _ => hb
  | _, _, _, hb, .cons h1 h2 => run_bounded (step_bounded hb h1) h2

lemma bounded_init : Bounded init :=
  ⟨Nat.zero_le _, fun _ => Nat.zero_le _, fun _ _ => show (0 : ℕ) < UINT32 by decide⟩

theorem BoundedRuns : Properties.BoundedRuns :=
  ⟨bounded_init, fun _ _ _ hb h => run_bounded hb h⟩

lemma enforcedDelay_le_max {s : State} (hb : Bounded s) (c : Address) :
    enforcedDelay s c ≤ MAX_EXECUTION_DELAY := by
  rw [enforcedDelay_eq_max]; exact max_le (hb.2.1 c) hb.1

theorem ExecuteNotBlockedAfterMaxDelay : Properties.ExecuteNotBlockedAfterMaxDelay := by
  intro s e x c lo hi hb hm hv hf hall
  show executeBatches e x c lo hi s = some s
  refine executeBatches_eq_some.mpr ⟨hm, hv, fun i hhi hlo => ?_, hf, rfl⟩
  have h1 := enforcedDelay_le_max hb c
  have h2 := hall i hlo hhi
  omega

/-! ## Boundaries -/

theorem OwnerCanShortenAPendingDelay : Properties.OwnerCanShortenAPendingDelay := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1000 vtValidator (.commitBatches vtChain 1 1)])
    (by rw [← exec_split e0]; decide)
  obtain ⟨s₂, h2, e2⟩ := exists_run_of_isSome (s := s₁)
    (ks := [vtCall 1000 vtOwner (.setExecutionDelay 0)])
    (by rw [← exec_split e1, ← exec_split e0]; decide)
  obtain ⟨s₃, _, e3⟩ := exists_run_of_isSome (s := s₂)
    (ks := [vtCall 1000 vtValidator (.executeBatches vtChain 1 1)])
    (by rw [← exec_split e2, ← exec_split e1, ← exec_split e0]; decide)
  refine ⟨s₀, s₁, s₂, s₃, h0, step_of_exec e1, h2, step_of_exec e3, trivial, ?_⟩
  rw [map_of_exec e0 (fun s => enforcedDelay s vtChain) (b := 100) (by decide)]
  decide

theorem ClockPast2106SkipsTheDelay : Properties.ClockPast2106SkipsTheDelay := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall (UINT32 + 1000) vtValidator (.commitBatches vtChain 1 1)])
    (by rw [← exec_split e0]; decide)
  obtain ⟨s₂, _, e2⟩ := exists_run_of_isSome (s := s₁)
    (ks := [vtCall (UINT32 + 1000) vtValidator (.executeBatches vtChain 1 1)])
    (by rw [← exec_split e1, ← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  refine ⟨s₀, s₁, s₂, h0, step_of_exec e1, step_of_exec e2,
    map_of_exec e01 (fun s => s.committedAt vtChain 1) (by decide), ?_⟩
  rw [map_of_exec e01 (fun s => enforcedDelay s vtChain) (b := 100) (by decide)]
  decide

theorem RecommitAtAnEarlierClock : Properties.RecommitAtAnEarlierClock := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1000 vtValidator (.commitBatches vtChain 1 1)])
    (by rw [← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  obtain ⟨s₂, h2, e2⟩ := exists_run_of_isSome (s := s₁)
    (ks := [vtCall 500 vtValidator (.commitBatches vtChain 1 1)])
    (by rw [← exec_split e01]; decide)
  have e012 := exec_snoc_of e01 e2
  obtain ⟨s₃, _, e3⟩ := exists_run_of_isSome (s := s₂)
    (ks := [vtCall 600 vtValidator (.executeBatches vtChain 1 1)])
    (by rw [← exec_split e012]; decide)
  have hd : enforcedDelay s₂ vtChain = 100 :=
    map_of_exec e012 (fun s => enforcedDelay s vtChain) (by decide)
  exact ⟨s₀, s₁, s₂, s₃, h0, step_of_exec e1, h2, step_of_exec e3, hd, by rw [hd]; decide⟩

theorem UnrecordedBatchIsNotDelayed : Properties.UnrecordedBatchIsNotDelayed := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 100 vtValidator (.executeBatches vtChain 7 7)])
    (by rw [← exec_split e0]; decide)
  exact ⟨s₀, s₁, h0, map_of_exec e0 (fun s => s.committedAt vtChain 7) (by decide),
    map_of_exec e0 (fun s => enforcedDelay s vtChain) (by decide), step_of_exec e1⟩

/-! ## The checks are load-bearing -/

theorem UncheckedExecuteRunsEarly : Properties.UncheckedExecuteRunsEarly := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1000 vtValidator (.commitBatches vtChain 1 1)])
    (by rw [← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  refine ⟨s₀, s₁, h0, step_of_exec e1, ?_, ?_,
    map_of_exec e01 (fun s => enforcedDelay s vtChain) (by decide)⟩
  · have hm : s₁.members vtChain EXECUTOR_ROLE vtValidator = true :=
      map_of_exec e01 (fun s => s.members vtChain EXECUTOR_ROLE vtValidator) (by decide)
    unfold executeBatchesUnchecked
    rw [hasRole_of_ne executor_ne, hm, ite_eq_right (by simp), ite_eq_right (by decide),
      ite_eq_right (by decide)]
  · apply step_none_of_exec
    rw [← exec_split e01]
    decide

theorem UncheckedIncreaseLowersTheDelay : Properties.UncheckedIncreaseLowersTheDelay := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1 vtAdmin (.increaseChainExecutionDelay vtChain 300)])
    (by rw [← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  have hd1 : enforcedDelay s₁ vtChain = 300 :=
    map_of_exec e01 (fun s => enforcedDelay s vtChain) (by decide)
  have hadm : chainAdmin (vtEnv 2) vtChain = some vtAdmin := by decide
  refine ⟨s₀, s₁, { s₁ with chainDelay := upd s₁.chainDelay vtChain 150 }, h0, step_of_exec e1, ?_,
    hd1, ?_, ?_⟩
  · unfold increaseChainExecutionDelayUnchecked
    rw [ite_eq_right (by rw [not_ne_some, hasRole_default_iff]; exact hadm)]
    rw [ite_eq_right (by decide)]
  · rw [enforcedDelay_eq_max]
    simp only [upd_same]
    have he : s₁.executionDelay = 100 :=
      map_of_exec e01 (fun s => s.executionDelay) (by decide)
    rw [he]; decide
  · apply step_none_of_exec
    rw [← exec_split e01]
    decide

theorem StoredComparisonAdmitsNoRaise : Properties.StoredComparisonAdmitsNoRaise := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  have hadm : chainAdmin (vtEnv 1) vtChain = some vtAdmin := by decide
  have hcd : s₀.chainDelay vtChain = 0 := map_of_exec e0 (fun s => s.chainDelay vtChain) (by decide)
  have hed : s₀.executionDelay = 100 := map_of_exec e0 (fun s => s.executionDelay) (by decide)
  have hd0 : enforcedDelay s₀ vtChain = 100 := by rw [enforcedDelay_eq_max, hcd, hed]; decide
  refine ⟨s₀, { s₀ with chainDelay := upd s₀.chainDelay vtChain 50 }, h0, ?_, by simp, hd0,
    ?_, ?_⟩
  · unfold increaseChainExecutionDelayStored
    rw [ite_eq_right (by rw [not_ne_some, hasRole_default_iff]; exact hadm), ite_eq_right (by decide),
      ite_eq_right (by rw [hcd]; decide)]
  · rw [enforcedDelay_eq_max]
    simp only [upd_same]
    rw [hed]; decide
  · apply step_none_of_exec
    rw [← exec_split e0]
    decide

/-! ## Witnesses -/

theorem ExecutionWaitsForTheDelayWitness : Properties.ExecutionWaitsForTheDelayWitness := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀) (ks := [vtDelayCommit])
    (by rw [← exec_split e0]; decide)
  obtain ⟨s₂, h2, e2⟩ := exists_run_of_isSome (s := s₁) (ks := vtDelayMid)
    (by rw [← exec_split e1, ← exec_split e0]; decide)
  obtain ⟨s₃, _, e3⟩ := exists_run_of_isSome (s := s₂) (ks := [vtDelayExecute])
    (by rw [← exec_split e2, ← exec_split e1, ← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  have e012 := exec_snoc_of e01 e2
  refine ⟨s₀, s₁, s₂, s₃, h0, step_of_exec e1, h2, step_of_exec e3, ?_, ?_, ?_, rfl, ?_,
    map_of_exec e0 (fun s => enforcedDelay s vtChain) (by decide),
    map_of_exec e01 (fun s => enforcedDelay s vtChain) (by decide),
    map_of_exec e012 (fun s => enforcedDelay s vtChain) (by decide), ?_⟩
  · simp only [vtDelayCommit, vtCall, Action.commits]; decide
  · simp only [vtDelayMid, vtCall, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Action.commits]
    decide
  · simp only [vtDelayMid, vtCall, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, Action.mayLowerDelay]
    decide
  · decide
  · rw [map_of_exec e012 (fun s => enforcedDelay s vtChain) (b := 200) (by decide)]; rfl

theorem RecommitWitness : Properties.RecommitWitness := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1000 vtValidator (.commitBatches vtChain 1 3)])
    (by rw [← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  obtain ⟨s₂, h2, e2⟩ := exists_run_of_isSome (s := s₁)
    (ks := [vtCall 1010 vtValidator (.revertBatches vtChain),
            vtCall 1020 vtValidator (.commitBatches vtChain 1 3)])
    (by rw [← exec_split e01]; decide)
  have e012 := exec_snoc_of e01 e2
  obtain ⟨s₃, _, e3⟩ := exists_run_of_isSome (s := s₂)
    (ks := [vtCall 1120 vtValidator (.executeBatches vtChain 1 3)])
    (by rw [← exec_split e012]; decide)
  exact ⟨s₀, s₁, s₂, s₃, h0, step_of_exec e1, h2, step_of_exec e3,
    ⟨rfl, by decide, by decide⟩, by decide, by decide, by decide,
    map_of_exec e012 (fun s => enforcedDelay s vtChain) (by decide),
    map_of_exec e012 (fun s => s.committedAt vtChain 2) (by decide)⟩

theorem DelayBoundIsTight : Properties.DelayBoundIsTight := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀) (ks := [vtDelayCommit])
    (by rw [← exec_split e0]; decide)
  obtain ⟨s₂, h2, e2⟩ := exists_run_of_isSome (s := s₁) (ks := vtDelayMid)
    (by rw [← exec_split e1, ← exec_split e0]; decide)
  refine ⟨s₀, s₁, s₂, h0, step_of_exec e1, h2, ?_, by decide⟩
  apply step_none_of_exec
  rw [← exec_split e2, ← exec_split e1, ← exec_split e0]
  decide

theorem DelayWritersWitness : Properties.DelayWritersWitness := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1 vtOwner (.setExecutionDelay 50)]) (by rw [← exec_split e0]; decide)
  obtain ⟨s₂, _, e2⟩ := exists_run_of_isSome (s := s₁)
    (ks := [vtCall 2 vtAdmin (.increaseChainExecutionDelay vtChain 200)])
    (by rw [← exec_split e1, ← exec_split e0]; decide)
  obtain ⟨s₃, _, e3⟩ := exists_run_of_isSome (s := s₂)
    (ks := [vtCall 3 vtOwner (.setChainExecutionDelay vtChain 10)])
    (by rw [← exec_split e2, ← exec_split e1, ← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  have e012 := exec_snoc_of e01 e2
  have e0123 := exec_snoc_of e012 e3
  exact ⟨s₀, s₁, s₂, s₃, h0, map_of_exec e0 (fun s => s.executionDelay) (by decide),
    step_of_exec e1, step_of_exec e2, step_of_exec e3,
    map_of_exec e01 (fun s => s.executionDelay) (by decide),
    map_of_exec e012 (fun s => s.chainDelay vtChain) (by decide),
    map_of_exec e0123 (fun s => s.chainDelay vtChain) (by decide),
    map_of_exec e0 (fun s => enforcedDelay s vtChain) (by decide),
    map_of_exec e01 (fun s => enforcedDelay s vtChain) (by decide),
    map_of_exec e012 (fun s => enforcedDelay s vtChain) (by decide),
    map_of_exec e0123 (fun s => enforcedDelay s vtChain) (by decide)⟩

theorem MaxDelayIsAttained : Properties.MaxDelayIsAttained := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, h1, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1 vtAdmin (.increaseChainExecutionDelay vtChain MAX_EXECUTION_DELAY),
            vtCall 1000 vtValidator (.commitBatches vtChain 1 1)])
    (by rw [← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  have hb : Bounded s₁ := run_bounded bounded_init (run_append h0 h1)
  have hm : s₁.members vtChain EXECUTOR_ROLE vtValidator = true :=
    map_of_exec e01 (fun s => s.members vtChain EXECUTOR_ROLE vtValidator) (by decide)
  have hc : s₁.committedAt vtChain 1 = 1000 :=
    map_of_exec e01 (fun s => s.committedAt vtChain 1) (by decide)
  refine ⟨s₀, s₁, h0, h1, hb, map_of_exec e01 (fun s => enforcedDelay s vtChain) (by decide),
    hm, hc, ?_, ?_⟩
  · exact ExecuteNotBlockedAfterMaxDelay s₁ _ _ _ 1 1 hb hm (by decide) rfl
      (fun i h1 h2 => by
        have : i = 1 := le_antisymm h2 h1
        subst this; rw [hc]; rfl)
  · apply step_none_of_exec
    rw [← exec_split e01]
    decide

end Contracts.ValidatorTimelock
