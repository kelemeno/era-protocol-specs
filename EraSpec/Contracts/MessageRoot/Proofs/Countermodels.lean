import EraSpec.Contracts.MessageRoot.Properties.Countermodels
import EraSpec.Contracts.MessageRoot.Proofs.Model

/-!
# Proofs: load-bearing checks, a redundant check, and the witness run

The concrete facts are computed by the kernel (`decide`) on the instances `wH`, `wCfg`,
`wEnv` of `Specs/Countermodels.lean`.  Reachability of the concrete storages comes from
`reachable_runFrom`.
-/

namespace Contracts.MessageRoot

theorem reachable_runFrom {H : Hashes} {cfg : Config} :
    ∀ {s t : State} {calls : List (Env × Call)}, Reachable H cfg s →
      runFrom H cfg s calls = some t → Reachable H cfg t
  | s, t, [], hs, h => by cases h; exact hs
  | s, t, (e, c) :: rest, hs, h => by
    simp only [runFrom, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, hr⟩ := h
    exact reachable_runFrom (.step hs hu) hr

theorem reachable_runFrom_init {H : Hashes} {cfg : Config} {e : Env} {t : State}
    {rest : List (Env × Call)} (h : runFrom H cfg fresh ((e, .initialize) :: rest) = some t) :
    Reachable H cfg t := by
  simp only [runFrom, Option.bind_eq_some_iff] at h
  obtain ⟨u, hu, hr⟩ := h
  exact reachable_runFrom (.init hu) hr

/-- Read a computed fact off a successful computation. -/
theorem fact_of_map {α : Type} {o : Option α} {a : α} {P : α → Bool} (ho : o = some a)
    (h : o.map P = some true) : P a = true := by
  rw [ho] at h; simpa using h

/-- Initialize and add chain 5 at batch 0. -/
def twoCalls : List (Env × Call) := witnessCalls.take 2

theorem RegisteredCheckLoadBearing : Properties.RegisteredCheckLoadBearing := by
  obtain ⟨s, hs⟩ : ∃ s, runFrom wH wCfg fresh twoCalls = some s :=
    Option.isSome_iff_exists.1 (by decide)
  have hreach : Reachable wH wCfg s := reachable_runFrom_init hs
  have hreg : chainRegistered wCfg s 5 = true :=
    fact_of_map hs (P := fun s => chainRegistered wCfg s 5) (by decide)
  obtain ⟨t, ht⟩ : ∃ t, execNoRegisteredCheck wH wCfg (wEnv 10 3) s (.addNewChain 5 0) = some t := by
    apply Option.isSome_iff_exists.1
    have := fact_of_map hs
      (P := fun s => (execNoRegisteredCheck wH wCfg (wEnv 10 3) s (.addNewChain 5 0)).isSome)
      (by decide)
    exact this
  have hfacts := fact_of_map hs (P := fun s =>
      ((execNoRegisteredCheck wH wCfg (wEnv 10 3) s (.addNewChain 5 0)).map fun t =>
        decide (t.chainCount = 3 ∧ t.chainIndexToId 1 = 5 ∧ t.chainIndexToId 2 = 5))
      == some true) (by decide)
  rw [ht] at hfacts
  simp only [Option.map_some, beq_iff_eq, Option.some.injEq, decide_eq_true_eq] at hfacts
  obtain ⟨h3, h1, h2⟩ := hfacts
  exact ⟨wH, wCfg, s, t, wEnv 10 3, 5, 0, hreach,
    (ChainAddedOnce wH wCfg s (wEnv 10 3) 5 0 hreach).1 hreg, ht,
    1, 2, by omega, by omega, by omega, h1, h2⟩

theorem ConsecutiveCheckLoadBearing : Properties.ConsecutiveCheckLoadBearing := by
  obtain ⟨s, hs⟩ : ∃ s, runFrom wH wCfg fresh twoCalls = some s :=
    Option.isSome_iff_exists.1 (by decide)
  have hreach : Reachable wH wCfg s := reachable_runFrom_init hs
  have hnone : (exec wH wCfg (wEnv 55 3) s (.addChainBatchRootV32 5 3 103)).isNone = true :=
    fact_of_map hs (P := fun s => (exec wH wCfg (wEnv 55 3) s (.addChainBatchRootV32 5 3 103)).isNone)
      (by decide)
  obtain ⟨t, ht⟩ : ∃ t, execNoConsecutiveCheck wH wCfg (wEnv 55 3) s
      (.addChainBatchRootV32 5 3 103) = some t := by
    apply Option.isSome_iff_exists.1
    exact fact_of_map hs (P := fun s =>
      (execNoConsecutiveCheck wH wCfg (wEnv 55 3) s (.addChainBatchRootV32 5 3 103)).isSome)
      (by decide)
  have hfacts := fact_of_map hs (P := fun s =>
      ((execNoConsecutiveCheck wH wCfg (wEnv 55 3) s (.addChainBatchRootV32 5 3 103)).map fun t =>
        decide (t.currentChainBatchNumber 5 = 1 ∧ t.chainBatchRoots 5 3 = 103)) == some true)
      (by decide)
  rw [ht] at hfacts
  simp only [Option.map_some, beq_iff_eq, Option.some.injEq, decide_eq_true_eq] at hfacts
  obtain ⟨h1, h2⟩ := hfacts
  exact ⟨wH, wCfg, s, t, wEnv 55 3, 5, 3, 103, hreach, Option.isNone_iff_eq_none.1 hnone, ht,
    by omega, by rw [h2]; decide⟩

/-- Read two successive results and a computed fact about them off a successful chain. -/
theorem exists_of_bind_map {α β : Type} {o : Option α} {f : α → Option β} {P : α → β → Bool}
    (h : (o.bind fun a => (f a).map (P a)) = some true) :
    ∃ a b, o = some a ∧ f a = some b ∧ P a b = true := by
  cases o with
  | none => simp at h
  | some a =>
    cases hf : f a with
    | none => simp [hf] at h
    | some b => exact ⟨a, b, rfl, hf, by simpa [hf] using h⟩

theorem MigratingCheckLoadBearing : Properties.MigratingCheckLoadBearing := by
  obtain ⟨s, hs⟩ : ∃ s, runFrom wH wCfg fresh witnessCalls = some s :=
    Option.isSome_iff_exists.1 (by decide)
  have hreach : Reachable wH wCfg s := reachable_runFrom_init hs
  have hnone : (exec wH wCfg (wEnv 11 7) s (.setMigratingChainBatchNumber 5 2)).isNone = true :=
    fact_of_map hs
      (P := fun s => (exec wH wCfg (wEnv 11 7) s (.setMigratingChainBatchNumber 5 2)).isNone)
      (by decide)
  have hfacts := fact_of_map hs (P := fun s =>
      ((execNoMigratingCheck wH wCfg (wEnv 11 7) s (.setMigratingChainBatchNumber 5 2)).bind
        fun t => (exec wH wCfg (wEnv 55 8) t (.addChainBatchRootV32 5 (2 + 1) 103)).map
          fun u => decide (t.currentChainBatchNumber 5 = 2 ∧ t.chainBatchRoots 5 6 = 106
            ∧ u.chainLeaves 5 = [0, 1, 6, 3].map (batchLeafOf wH u 5))) == some true)
    (by decide)
  rw [beq_iff_eq] at hfacts
  obtain ⟨t, u, ht, hu, hP⟩ := exists_of_bind_map hfacts
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3⟩ := hP
  exact ⟨wH, wCfg, s, t, u, wEnv 11 7, wEnv 55 8, 5, 2, 103, hreach,
    Option.isNone_iff_eq_none.1 hnone, ht, ⟨6, by omega, by rw [h2]; decide⟩, hu, h3⟩

theorem recordNoRegisteredCheck_setups {c n : ℕ} {r : Bytes32} {s t : State}
    (h : recordNoRegisteredCheck c n r s = some t) : t.chainTreeSetups = s.chainTreeSetups := by
  unfold recordNoRegisteredCheck at h
  split_ifs at h
  cases h
  rfl

theorem RecordRegisteredCheckLoadBearing : Properties.RecordRegisteredCheckLoadBearing := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, hs⟩ : ∃ s, runFrom wH wCfg fresh (witnessCalls.take 1) = some s :=
      Option.isSome_iff_exists.1 (by decide)
    have hreach : Reachable wH wCfg s := reachable_runFrom_init hs
    have hunreg : chainRegistered wCfg s 5 = false := by
      simpa using fact_of_map hs (P := fun s => !chainRegistered wCfg s 5) (by decide)
    have hnone : (exec wH wCfg (wEnv 55 2) s (.addChainBatchRoot 5 1 101)).isNone = true :=
      fact_of_map hs (P := fun s => (exec wH wCfg (wEnv 55 2) s (.addChainBatchRoot 5 1 101)).isNone)
        (by decide)
    obtain ⟨t, ht⟩ : ∃ t, execNoRecordRegisteredCheck wH wCfg (wEnv 55 2) s
        (.addChainBatchRoot 5 1 101) = some t :=
      Option.isSome_iff_exists.1 (fact_of_map hs (P := fun s =>
        (execNoRecordRegisteredCheck wH wCfg (wEnv 55 2) s (.addChainBatchRoot 5 1 101)).isSome)
        (by decide))
    have hfacts := fact_of_map hs (P := fun s =>
        ((execNoRecordRegisteredCheck wH wCfg (wEnv 55 2) s (.addChainBatchRoot 5 1 101)).map
          fun t => decide (chainRegistered wCfg t 5 = false ∧ t.chainBatchRoots 5 1 = 101))
        == some true) (by decide)
    rw [ht] at hfacts
    simp only [Option.map_some, beq_iff_eq, Option.some.injEq, decide_eq_true_eq] at hfacts
    obtain ⟨h1, h2⟩ := hfacts
    exact ⟨wH, wCfg, s, t, wEnv 55 2, 5, 1, 101, hreach, hunreg,
      Option.isNone_iff_eq_none.1 hnone, ht, h1, by rw [h2]; decide⟩
  · intro H cfg s env c n r hs hc
    have hI := inv_reachable hs
    have h0 : s.chainTreeSetups c = 0 := by simp [hI.setups c, hc]
    simp only [execNoRecordRegisteredCheck]
    split_ifs
    · rfl
    · cases hrec : recordNoRegisteredCheck c n r s with
      | none => rfl
      | some s₁ =>
        have h1 : s₁.chainTreeSetups c = 0 := by rw [recordNoRegisteredCheck_setups hrec]; exact h0
        simp [pushChainBatchRoot, h1]

theorem ExistsCheckRedundant : Properties.ExistsCheckRedundant := by
  intro H cfg s c n r hs
  have hI := inv_reachable hs
  unfold recordChainBatchRoot recordNoExistsCheck
  by_cases h0 : s.chainBatchRoots c n = 0
  · simp [h0]
  · have hn : n ≠ s.currentChainBatchNumber c + 1 := by
      intro hn; exact h0 (hI.beyond_zero c n (by omega))
    simp [h0, hn]

theorem WitnessRun : Properties.WitnessRun := by
  obtain ⟨s, hs⟩ : ∃ s, runFrom wH wCfg fresh witnessCalls = some s :=
    Option.isSome_iff_exists.1 (by decide)
  have hreach : Reachable wH wCfg s := reachable_runFrom_init hs
  have h := fact_of_map hs (P := fun s =>
    decide (s.chainCount = 2 ∧ s.chainIndex 5 = 1 ∧ s.currentChainBatchNumber 5 = 6
      ∧ s.chainLeaves 5 = [0, 1, 6].map (batchLeafOf wH s 5)
      ∧ s.chainBatchRoots 5 2 = 102 ∧ s.interopEnabled 5 = true
      ∧ finalNodeAccepts wCfg (wEnv 0 7) s 5 6 106 = some true
      ∧ finalNodeAccepts wCfg (wEnv 0 7) s 5 2 102 = some true
      ∧ finalNodeAccepts wCfg (wEnv 0 7) s 5 3 0 = some false
      ∧ finalNodeAccepts wCfg (wEnv 0 7) s 5 0 77 = none)) (by decide)
  simp only [decide_eq_true_eq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  exact ⟨s, hs, hreach, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10,
    HistoricalRootIsAggregated wH wCfg s hreach⟩

theorem BridgehubNotOnlyRegistrar : Properties.BridgehubNotOnlyRegistrar := by
  obtain ⟨s, hs⟩ : ∃ s, runFrom wH wCfg fresh (witnessCalls.take 1) = some s :=
    Option.isSome_iff_exists.1 (by decide)
  have hreach : Reachable wH wCfg s := reachable_runFrom_init hs
  have hunreg : chainRegistered wCfg s 6 = false :=
    by simpa using fact_of_map hs (P := fun s => !chainRegistered wCfg s 6) (by decide)
  obtain ⟨t, ht⟩ : ∃ t, exec wH wCfg (wEnv 11 2) s (.addNewChain 6 0) = some t :=
    Option.isSome_iff_exists.1 (fact_of_map hs
      (P := fun s => (exec wH wCfg (wEnv 11 2) s (.addNewChain 6 0)).isSome) (by decide))
  obtain ⟨_, _, hreg, _⟩ := (ChainAddedOnce wH wCfg s (wEnv 11 2) 6 0 hreach).2 t ht
  exact ⟨wH, wCfg, s, t, wEnv 11 2, 6, 0, hreach, by decide, rfl, hunreg, ht, hreg⟩

theorem RecordOnlyDoesNotPush : Properties.RecordOnlyDoesNotPush := by
  obtain ⟨s, hs⟩ : ∃ s, runFrom wH wCfg fresh (witnessCalls.take 4) = some s :=
    Option.isSome_iff_exists.1 (by decide)
  have hreach : Reachable wH wCfg s := reachable_runFrom_init hs
  obtain ⟨t, ht⟩ : ∃ t, exec wH wCfg (wEnv 55 3) s (.addChainBatchRoot 5 2 102) = some t :=
    Option.isSome_iff_exists.1 (fact_of_map hs
      (P := fun s => (exec wH wCfg (wEnv 55 3) s (.addChainBatchRoot 5 2 102)).isSome) (by decide))
  obtain ⟨_, _, hr, _, hroot, _, hleaves, _⟩ :=
    (AppendExact wH wCfg s (wEnv 55 3) 5 2 102 hreach).2 t ht
  exact ⟨wH, wCfg, s, t, wEnv 55 3, 5, 2, 102, hreach, ht, hr, hroot, by rw [hleaves]⟩

end Contracts.MessageRoot
