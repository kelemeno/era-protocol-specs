import EraSpec.Contracts.ValidatorTimelock.Properties.Ownership
import EraSpec.Contracts.ValidatorTimelock.Proofs.Delay

/-!
# Proofs: initialization and the owner

`initialized` only goes from `false` to `true`, and only by `initialize`
(`step_initialized`). With owner and pending owner `0` and no call from `0`, every
owner-gated call reverts (`step_renounced`), so no call that may lower a delay succeeds and
`step_enforced_mono` applies.
-/

namespace Contracts.ValidatorTimelock

lemma step_initialized {k : Call} {s s' : State} (h : step k s = some s') :
    (k.action.isInitialize = true → s.initialized = false ∧ s'.initialized = true) ∧
    (k.action.isInitialize = false → s'.initialized = s.initialized) := by
  rcases k with ⟨e, x, a⟩
  cases a with
  | initializeTimelock o d =>
    obtain ⟨h1, _, rfl⟩ := initializeTimelock_eq_some.mp h
    exact ⟨fun _ => ⟨h1, rfl⟩, fun h' => absurd h' (by simp [Action.isInitialize])⟩
  | _ =>
    rw [step_post h]
    exact ⟨fun h' => absurd h' (by simp [Action.isInitialize]), fun _ => rfl⟩

lemma run_initialize_once :
    ∀ {s s' : State} {ks : List Call}, Run s ks s' →
      (ks.filter (fun k => k.action.isInitialize)).length ≤ 1 ∧
      (s.initialized = true → ks.filter (fun k => k.action.isInitialize) = []) ∧
      (ks.filter (fun k => k.action.isInitialize) ≠ [] → s'.initialized = true) ∧
      (s.initialized = true → s'.initialized = true)
  | _, _, _, .nil _ => ⟨by simp, fun _ => rfl, fun h => absurd rfl h, id⟩
  | s, _, _, .cons (k := k) (s₁ := s₁) h1 h2 => by
      obtain ⟨ih1, ih2, ih3, ih4⟩ := run_initialize_once h2
      obtain ⟨hi1, hi2⟩ := step_initialized h1
      cases hk : k.action.isInitialize
      · have hs₁ := hi2 hk
        rw [List.filter_cons_of_neg (by simp [hk])]
        exact ⟨ih1, fun h => ih2 (hs₁.trans h), ih3, fun h => ih4 (hs₁.trans h)⟩
      · obtain ⟨hs, hs₁⟩ := hi1 hk
        rw [List.filter_cons_of_pos (by simp [hk]), ih2 hs₁]
        exact ⟨by simp, fun h => absurd (hs.symm.trans h) (by simp), fun _ => ih4 hs₁,
          fun h => absurd (hs.symm.trans h) (by simp)⟩

theorem InitializeAtMostOnce : Properties.InitializeAtMostOnce := by
  intro s s' ks h
  obtain ⟨h1, h2, h3, _⟩ := run_initialize_once h
  exact ⟨h1, h2, h3⟩

theorem OwnerChangesOnlyByHandover : Properties.OwnerChangesOnlyByHandover := by
  intro k s s' h
  have hs := step_post h
  rcases k with ⟨e, x, a⟩
  cases a with
  | initializeTimelock o d =>
    obtain ⟨h1, _, rfl⟩ := initializeTimelock_eq_some.mp h
    exact ⟨fun _ => Or.inl ⟨d, rfl, h1⟩, fun _ => Or.inr rfl⟩
  | transferOwnership n =>
    obtain ⟨h1, rfl⟩ := transferOwnership_eq_some.mp h
    exact ⟨fun hne => absurd rfl hne, fun _ => Or.inl ⟨n, rfl, h1, rfl⟩⟩
  | acceptOwnership =>
    obtain ⟨h1, rfl⟩ := acceptOwnership_eq_some.mp h
    exact ⟨fun _ => Or.inr (Or.inl ⟨rfl, h1, rfl⟩), fun _ => Or.inr rfl⟩
  | renounceOwnership =>
    obtain ⟨h1, rfl⟩ := renounceOwnership_eq_some.mp h
    exact ⟨fun _ => Or.inr (Or.inr ⟨rfl, h1, rfl⟩), fun _ => Or.inr rfl⟩
  | _ => rw [hs]; exact ⟨fun hne => absurd rfl hne, fun hne => absurd rfl hne⟩

theorem OwnerOnlyCalls : Properties.OwnerOnlyCalls := by
  rintro ⟨e, x, a⟩ s s' h hk
  cases a with
  | renounceOwnership => exact (renounceOwnership_eq_some.mp h).1
  | transferOwnership n => exact (transferOwnership_eq_some.mp h).1
  | setExecutionDelay d => exact (setExecutionDelay_eq_some.mp h).1
  | setChainExecutionDelay c d => exact (setChainExecutionDelay_eq_some.mp h).1
  | _ => simp at hk

lemma step_renounced {k : Call} {s s' : State} (h : step k s = some s')
    (hi : s.initialized = true) (ho : s.owner = 0) (hp : s.pendingOwner = 0) (hx : k.sender ≠ 0) :
    s'.initialized = true ∧ s'.owner = 0 ∧ s'.pendingOwner = 0 ∧
      s'.executionDelay = s.executionDelay ∧ ¬ k.action.mayLowerDelay := by
  rcases k with ⟨e, x, a⟩
  simp only at hx
  cases a with
  | initializeTimelock o d =>
    have := (initializeTimelock_eq_some.mp h).1
    rw [hi] at this; exact absurd this (by simp)
  | transferOwnership n => exact absurd ((transferOwnership_eq_some.mp h).1.trans ho) hx
  | acceptOwnership => exact absurd ((acceptOwnership_eq_some.mp h).1.trans hp) hx
  | renounceOwnership => exact absurd ((renounceOwnership_eq_some.mp h).1.trans ho) hx
  | setExecutionDelay d => exact absurd ((setExecutionDelay_eq_some.mp h).1.trans ho) hx
  | setChainExecutionDelay c d => exact absurd ((setChainExecutionDelay_eq_some.mp h).1.trans ho) hx
  | _ => rw [step_post h]; exact ⟨hi, ho, hp, rfl, fun h' => h'⟩

lemma run_renounced :
    ∀ {s s' : State} {ks : List Call}, Run s ks s' → s.initialized = true → s.owner = 0 →
      s.pendingOwner = 0 → (∀ k ∈ ks, k.sender ≠ 0) →
      s'.initialized = true ∧ s'.owner = 0 ∧ s'.pendingOwner = 0 ∧
        s'.executionDelay = s.executionDelay ∧ ∀ c, enforcedDelay s c ≤ enforcedDelay s' c
  | _, _, _, .nil _, hi, ho, hp, _ => ⟨hi, ho, hp, rfl, fun _ => le_rfl⟩
  | _, _, _, .cons (k := k) h1 h2, hi, ho, hp, hx => by
      obtain ⟨hi₁, ho₁, hp₁, he₁, hk⟩ := step_renounced h1 hi ho hp (hx k List.mem_cons_self)
      obtain ⟨hi₂, ho₂, hp₂, he₂, hm⟩ := run_renounced h2 hi₁ ho₁ hp₁
        (fun k' hk' => hx k' (List.mem_cons_of_mem _ hk'))
      exact ⟨hi₂, ho₂, hp₂, he₂.trans he₁, fun c => le_trans (step_enforced_mono h1 hk c) (hm c)⟩

theorem RenouncedTimelockOnlyRaisesDelays : Properties.RenouncedTimelockOnlyRaisesDelays := by
  intro s s' ks hi ho hp hx h
  obtain ⟨_, h2, h3, h4, h5⟩ := run_renounced h hi ho hp hx
  exact ⟨h2, h3, h4, h5⟩

/-! ## The countermodel and the witnesses -/

theorem ZeroSenderActsAsRenouncedOwner : Properties.ZeroSenderActsAsRenouncedOwner := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1 vtOwner .renounceOwnership]) (by rw [← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  obtain ⟨s₂, _, e2⟩ := exists_run_of_isSome (s := s₁)
    (ks := [vtCall 2 0 (.setExecutionDelay 0)]) (by rw [← exec_split e01]; decide)
  have e012 := exec_snoc_of e01 e2
  exact ⟨s₀, s₁, s₂, h0, step_of_exec e1, map_of_exec e01 (fun s => s.owner) (by decide),
    map_of_exec e01 (fun s => s.executionDelay) (by decide), step_of_exec e2,
    map_of_exec e012 (fun s => s.executionDelay) (by decide)⟩

theorem HandoverWitness : Properties.HandoverWitness := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1 vtOwner (.transferOwnership 7)]) (by rw [← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  obtain ⟨s₂, _, e2⟩ := exists_run_of_isSome (s := s₁)
    (ks := [vtCall 2 7 .acceptOwnership]) (by rw [← exec_split e01]; decide)
  have e012 := exec_snoc_of e01 e2
  refine ⟨s₀, s₁, s₂, h0, map_of_exec e0 (fun s => s.owner) (by decide),
    map_of_exec e0 (fun s => s.initialized) (by decide), step_of_exec e1,
    map_of_exec e01 (fun s => s.pendingOwner) (by decide), step_of_exec e2,
    map_of_exec e012 (fun s => s.owner) (by decide),
    map_of_exec e012 (fun s => s.pendingOwner) (by decide), ?_⟩
  apply step_none_of_exec
  rw [← exec_split e012]
  decide

theorem RenounceWitness : Properties.RenounceWitness := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1 vtOwner .renounceOwnership]) (by rw [← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  obtain ⟨s₂, h2, e2⟩ := exists_run_of_isSome (s := s₁)
    (ks := [vtCall 2 vtAdmin (.increaseChainExecutionDelay vtChain 200)])
    (by rw [← exec_split e01]; decide)
  have e012 := exec_snoc_of e01 e2
  refine ⟨s₀, s₁, s₂, h0, step_of_exec e1,
    map_of_exec e01 (fun s => s.initialized) (by decide),
    map_of_exec e01 (fun s => s.owner) (by decide),
    map_of_exec e01 (fun s => s.pendingOwner) (by decide), h2, by decide,
    map_of_exec e01 (fun s => enforcedDelay s vtChain) (by decide),
    map_of_exec e012 (fun s => enforcedDelay s vtChain) (by decide), ?_⟩
  apply step_none_of_exec
  rw [← exec_split e012]
  decide

end Contracts.ValidatorTimelock
