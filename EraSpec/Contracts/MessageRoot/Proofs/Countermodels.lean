import EraSpec.Contracts.MessageRoot.Properties.Countermodels
import EraSpec.Contracts.MessageRoot.Proofs.Model

/-!
# Proofs: witnesses, countermodels, and the checks the guarantees rest on

The concrete facts are computed by the kernel (`decide`) on the instances `mrHashes`,
`mrConfig`, `mrConfigPreV31` and `mrEnv` of `Specs/Countermodels.lean`.  Each witness reads the
storages it needs off one successful computation (`exists_of_map`, `exists_of_bind_map`,
`exists_of_bind3`, `exists_of_bind4`); reachability and runs of the concrete call lists come
from `reachable_execCalls` and `run_of_execCalls`.  Facts that quantify over all chains or all
environments are derived from the theorems of `Proofs/Model.lean`.
-/

namespace Contracts.MessageRoot

open AttackVectors.CapacityInvariant (TreeDims)

/-! ## Concrete call lists as runs -/

theorem reachable_execCalls {H : Hashes} {cfg : Config} :
    ∀ {s t : State} {calls : List (Env × Call)}, Reachable H cfg s →
      execCalls H cfg s calls = some t → Reachable H cfg t
  | s, t, [], hs, h => by cases h; exact hs
  | s, t, (e, c) :: rest, hs, h => by
    simp only [execCalls, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, hr⟩ := h
    exact reachable_execCalls (.step hs hu) hr

theorem reachable_execCalls_init {H : Hashes} {cfg : Config} {e : Env} {t : State}
    {rest : List (Env × Call)} (h : execCalls H cfg fresh ((e, .initialize) :: rest) = some t) :
    Reachable H cfg t := by
  simp only [execCalls, Option.bind_eq_some_iff] at h
  obtain ⟨u, hu, hr⟩ := h
  exact reachable_execCalls (.init hu) hr

theorem run_cons {H : Hashes} {cfg : Config} {s t u : State} {e : Env} {c : Call}
    {tr : List (Env × Call)} (h : exec H cfg e s c = some t) (hr : Run H cfg t tr u) :
    Run H cfg s ((e, c) :: tr) u := by
  induction hr with
  | nil => exact .snoc (.nil s) h
  | snoc _ hx ih => exact .snoc ih hx

theorem run_of_execCalls {H : Hashes} {cfg : Config} :
    ∀ {s t : State} {tr : List (Env × Call)}, execCalls H cfg s tr = some t → Run H cfg s tr t
  | s, t, [], h => by cases h; exact .nil s
  | s, t, (e, c) :: rest, h => by
    simp only [execCalls, Option.bind_eq_some_iff] at h
    obtain ⟨u, hu, hr⟩ := h
    exact run_cons hu (run_of_execCalls hr)

theorem run_append {H : Hashes} {cfg : Config} {s t u : State} {tr₁ tr₂ : List (Env × Call)}
    (h₁ : Run H cfg s tr₁ t) (h₂ : Run H cfg t tr₂ u) : Run H cfg s (tr₁ ++ tr₂) u := by
  induction h₂ with
  | nil => simpa using h₁
  | snoc _ hx ih => rw [← List.append_assoc]; exact .snoc ih hx

/-! ## Reading computed facts off successful computations -/

private theorem exists_of_map {α : Type} {o : Option α} {P : α → Bool}
    (h : o.map P = some true) : ∃ a, o = some a ∧ P a = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some a => exact ⟨a, rfl, by simpa [ho] using h⟩

private theorem exists_of_bind_map {α β : Type} {o : Option α} {f : α → Option β}
    {P : α → β → Bool} (h : (o.bind fun a => (f a).map (P a)) = some true) :
    ∃ a b, o = some a ∧ f a = some b ∧ P a b = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some a =>
    cases hf : f a with
    | none => simp [ho, hf] at h
    | some b => exact ⟨a, b, rfl, hf, by simpa [ho, hf] using h⟩

private theorem exists_of_bind3 {α β γ : Type} {o : Option α} {f : α → Option β}
    {g : α → β → Option γ} {P : α → β → γ → Bool}
    (h : (o.bind fun a => (f a).bind fun b => (g a b).map (P a b)) = some true) :
    ∃ a b c, o = some a ∧ f a = some b ∧ g a b = some c ∧ P a b c = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some a =>
    cases hf : f a with
    | none => simp [ho, hf] at h
    | some b =>
      cases hg : g a b with
      | none => simp [ho, hf, hg] at h
      | some c => exact ⟨a, b, c, rfl, hf, hg, by simpa [ho, hf, hg] using h⟩

private theorem exists_of_bind4 {α β γ δ : Type} {o : Option α} {f : α → Option β}
    {g : α → β → Option γ} {k : α → β → γ → Option δ} {P : α → β → γ → δ → Bool}
    (h : (o.bind fun a => (f a).bind fun b => (g a b).bind fun c => (k a b c).map (P a b c))
      = some true) :
    ∃ a b c d, o = some a ∧ f a = some b ∧ g a b = some c ∧ k a b c = some d
      ∧ P a b c d = true := by
  cases ho : o with
  | none => simp [ho] at h
  | some a =>
    cases hf : f a with
    | none => simp [ho, hf] at h
    | some b =>
      cases hg : g a b with
      | none => simp [ho, hf, hg] at h
      | some c =>
        cases hk : k a b c with
        | none => simp [ho, hf, hg, hk] at h
        | some d => exact ⟨a, b, c, d, rfl, hf, hg, hk, by simpa [ho, hf, hg, hk] using h⟩

/-! ## Witnesses -/

theorem EveryEntryPointRun : Properties.EveryEntryPointRun := by
  obtain ⟨s, hs, hP⟩ := exists_of_map (o := execCalls mrHashes mrConfig fresh mrCalls)
    (P := fun s => decide (s.chainCount = 3 ∧ s.chainIndex 5 = 1 ∧ s.chainIndex 6 = 2
      ∧ s.currentChainBatchNumber 5 = 6
      ∧ s.chainLeaves 5 = [0, 1, 6].map (batchLeafOf mrHashes s 5)
      ∧ s.chainLeaves 6 = [1].map (batchLeafOf mrHashes s 6)
      ∧ s.chainBatchRoots 5 2 = 102 ∧ s.interopEnabled 5 = true
      ∧ finalNodeAccepts mrConfig (mrEnv 0 8) s 5 6 106 = some true
      ∧ finalNodeAccepts mrConfig (mrEnv 0 8) s 5 2 102 = some true
      ∧ s.chainBatchRoots 5 3 = 0)) (by decide)
  have hreach : Reachable mrHashes mrConfig s := reachable_execCalls_init hs
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hP
  refine ⟨s, hs, hreach, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, fun env proven => ?_,
    fun env proven => ?_, HistoricalRootIsAggregated mrHashes mrConfig s hreach⟩
  · simp [finalNodeAccepts, getChainBatchRoot, h11, mrConfig]
  · simp [finalNodeAccepts, getChainBatchRoot]

theorem RegistrationPremisesHold : Properties.RegistrationPremisesHold := by
  obtain ⟨s, t, t', hs, ht, ht', hP⟩ := exists_of_bind3
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 1))
    (f := fun s => exec mrHashes mrConfig (mrEnv 10 2) s (.addNewChain 5 0))
    (g := fun s _ => exec mrHashes mrConfig (mrEnv 11 2) s (.addNewChain 6 0))
    (P := fun s t _ => decide (chainRegistered mrConfig s 5 = false
      ∧ chainRegistered mrConfig s 6 = false
      ∧ s.chainCount + 1 < UInt256.size ∧ s.interopRootLogId + 1 < UInt256.size
      ∧ chainRegistered mrConfig t 5 = true)) (by decide)
  have hreach : Reachable mrHashes mrConfig s := reachable_execCalls_init hs
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4, h5⟩ := hP
  exact ⟨s, t, t', hreach, h1, h2, h3, h4, rfl, ht, rfl, by decide, ht', .step hreach ht, h5⟩

theorem AppendPremisesHold : Properties.AppendPremisesHold := by
  obtain ⟨s₂, s₃, s₄, s₅, hs₂, hs₃, hs₄, hs₅, hP⟩ := exists_of_bind4
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 2))
    (f := fun s => exec mrHashes mrConfig (mrEnv 10 2) s (.seedGenesisRoot 5))
    (g := fun _ s => exec mrHashes mrConfig (mrEnv 55 3) s (.addChainBatchRootV32 5 1 101))
    (k := fun _ _ s => exec mrHashes mrConfig (mrEnv 55 3) s (.addChainBatchRoot 5 2 102))
    (P := fun _ s₃ s₄ s₅ => decide (chainRegistered mrConfig s₃ 5 = true
      ∧ s₃.currentChainBatchNumber 5 = 0
      ∧ s₃.currentChainBatchNumber 5 + 1 < UInt256.size
      ∧ s₃.interopRootLogId + 1 < UInt256.size
      ∧ s₄.currentChainBatchNumber 5 = 1
      ∧ s₅.chainBatchRoots 5 2 = 102 ∧ s₅.chainLeaves 5 = s₄.chainLeaves 5
      ∧ s₄.chainLeaves 5 = [0, 1].map (batchLeafOf mrHashes s₄ 5))) (by decide)
  have hreach₂ : Reachable mrHashes mrConfig s₂ := reachable_execCalls_init hs₂
  have hreach₃ : Reachable mrHashes mrConfig s₃ := .step hreach₂ hs₃
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hP
  exact ⟨s₂, s₃, s₄, s₅, hreach₂, hs₃, by decide, hreach₃, inv_reachable hreach₃, rfl, h1,
    by decide, h2, h3, h4, hs₄, h5, hs₅, h6, h7, h8⟩

theorem MigrationPremisesHold : Properties.MigrationPremisesHold := by
  obtain ⟨s, t, u, hs, ht, hu, hP⟩ := exists_of_bind3
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 5))
    (f := fun s => exec mrHashes mrConfig (mrEnv 11 4) s (.setMigratingChainBatchNumber 5 5))
    (g := fun _ t => execCalls mrHashes mrConfig t (mrCalls.drop 6))
    (P := fun s _ u => decide (chainRegistered mrConfig s 5 = true
      ∧ s.currentChainBatchNumber 5 = 2
      ∧ u.currentChainBatchNumber 5 = 6 ∧ u.chainBatchRoots 5 6 ≠ 0)) (by decide)
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4⟩ := hP
  exact ⟨s, t, u, mrCalls.drop 6, reachable_execCalls_init hs, h1, h2, ht, run_of_execCalls hu,
    by decide, h3, h4⟩

theorem RunPremisesHold : Properties.RunPremisesHold := by
  obtain ⟨s, t, hs, ht, hP⟩ := exists_of_bind_map
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 5))
    (f := fun s => execCalls mrHashes mrConfig s (mrCalls.drop 5))
    (P := fun s t => decide (chainRegistered mrConfig s 5 = true
      ∧ s.currentChainBatchNumber 5 = 2
      ∧ s.chainBatchRoots 5 0 ≠ 0 ∧ s.chainBatchRoots 5 1 ≠ 0 ∧ s.chainBatchRoots 5 2 ≠ 0
      ∧ t.chainBatchRoots 5 6 ≠ s.chainBatchRoots 5 6 ∧ t.chainLeaves 5 ≠ s.chainLeaves 5
      ∧ t.currentChainBatchNumber 5 = 6 ∧ s.chainCount = 2 ∧ t.chainCount = 3)) (by decide)
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hP
  exact ⟨s, t, mrCalls.drop 5, reachable_execCalls_init hs, run_of_execCalls ht, by decide,
    h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem WritersOnlyPremisesHold : Properties.WritersOnlyPremisesHold := by
  obtain ⟨s, s', t, hs, hs', ht, hP⟩ := exists_of_bind3
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 5))
    (f := fun s => execCalls mrHashes mrConfig s mrWritersOnlyFirst)
    (g := fun _ s' => execCalls mrHashes mrConfig s' mrWritersOnlySecond)
    (P := fun s s' t => decide (s'.currentChainBatchNumber 5 ≠ s.currentChainBatchNumber 5
      ∧ getAggregatedRoot mrConfig t ≠ getAggregatedRoot mrConfig s')) (by decide)
  simp only [decide_eq_true_eq] at hP
  have h₁ := run_of_execCalls hs'
  have h₂ := run_of_execCalls ht
  exact ⟨s, s', t, reachable_execCalls_init hs, h₁, h₂, run_append h₁ h₂, by decide, by decide,
    by decide, hP.1, hP.2⟩

theorem LogIdPremisesHold : Properties.LogIdPremisesHold := by
  obtain ⟨s₁, s₂, s₃, hs₁, hs₂, hs₃, hP⟩ := exists_of_bind3
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 1))
    (f := fun s => exec mrHashes mrConfig (mrEnv 10 2) s (.addNewChain 5 0))
    (g := fun _ s => exec mrHashes mrConfig (mrEnv 10 2) s (.seedGenesisRoot 5))
    (P := fun s₁ s₂ s₃ => decide (s₁.lastEmitBlock ≠ 2
      ∧ s₃.interopRootLogId = s₁.interopRootLogId + 1
      ∧ s₂.lastEmitBlock = 2 ∧ s₃.interopRootLogId = s₂.interopRootLogId
      ∧ getAggregatedRoot mrConfig s₁ ≠ getAggregatedRoot mrConfig s₂
      ∧ getAggregatedRoot mrConfig s₂ ≠ getAggregatedRoot mrConfig s₃)) (by decide)
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  exact ⟨s₁, s₂, s₃, reachable_execCalls_init hs₁, run_cons hs₂ (run_cons hs₃ (.nil s₃)), hs₂,
    run_cons hs₃ (.nil s₃), h1, h2, h3, h4, h5, h6⟩

theorem InteropPremisesHold : Properties.InteropPremisesHold := by
  obtain ⟨s, t, u, hs, ht, hu, hP⟩ := exists_of_bind3
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 7))
    (f := fun s => exec mrHashes mrConfig (mrEnv 12 6) s (.enableInterop 5 false))
    (g := fun _ t => execCalls mrHashes mrConfig t
      [(mrEnv 11 7, .addNewChain 6 0), (mrEnv 66 7, .addChainBatchRootV32 6 1 201)])
    (P := fun s t u => decide (s.interopEnabled 5 = false ∧ t.interopEnabled 5 = true
      ∧ (exec mrHashes mrConfig (mrEnv 12 8) t (.enableInterop 5 false)).isNone = true
      ∧ u.interopEnabled 5 = true)) (by decide)
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4⟩ := hP
  exact ⟨s, t, u, run_cons ht (.nil t), h1, h2, Option.isNone_iff_eq_none.1 h3,
    run_of_execCalls hu, h4⟩

theorem SameTreesPremisesHold : Properties.SameTreesPremisesHold := by
  obtain ⟨s, s', hs, hs', hP⟩ := exists_of_bind_map
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 4))
    (f := fun s => exec mrHashes mrConfig (mrEnv 55 3) s (.addChainBatchRoot 5 2 102))
    (P := fun s s' => decide (chainRegistered mrConfig s 5 = true
      ∧ s.currentChainBatchNumber 5 ≠ s'.currentChainBatchNumber 5
      ∧ s.chainBatchRoots 5 2 ≠ s'.chainBatchRoots 5 2)) (by decide)
  have hreach : Reachable mrHashes mrConfig s := reachable_execCalls_init hs
  have hreach' : Reachable mrHashes mrConfig s' := .step hreach hs'
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3⟩ := hP
  have hx := hs'
  simp only [exec] at hx
  split_ifs at hx
  obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some hx
  exact ⟨s, _, hreach, hreach', rfl, fun _ _ => rfl, fun _ _ => rfl, h1,
    ((inv_reachable hreach).reg_slot h1).2, rfl, h2, h3⟩

theorem AggregatedRootCollisionFires : Properties.AggregatedRootCollisionFires := by
  obtain ⟨s, s', hs, hs', hP⟩ := exists_of_bind_map
    (o := execCalls mrHashes mrConfig fresh (mrCollisionCalls 101 201))
    (f := fun _ => execCalls mrHashes mrConfig fresh (mrCollisionCalls 102 200))
    (P := fun s s' => decide (s.chainCount = s'.chainCount
      ∧ chainRegistered mrConfig s 5 = true
      ∧ s'.chainIndexToId (s.chainIndex 5) = 5
      ∧ getAggregatedRoot mrConfig s = getAggregatedRoot mrConfig s'
      ∧ chainRootOf mrHashes (s.chainLeaves 5) ≠ chainRootOf mrHashes (s'.chainLeaves 5)
      ∧ mrHashes.chainIdLeaf (chainRootOf mrHashes (s.chainLeaves 5)) 5
          ≠ mrHashes.chainIdLeaf (chainRootOf mrHashes (s'.chainLeaves 5)) 5)) (by decide)
  have hreach : Reachable mrHashes mrConfig s := reachable_execCalls_init hs
  have hreach' : Reachable mrHashes mrConfig s' := reachable_execCalls_init hs'
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  refine ⟨s, s', hs, hs', hreach, hreach', h1, h2, h3, h4, h5, h6, ?_⟩
  rcases AggregatedRootPinsChainRootOrCollision mrHashes mrConfig s s' 5 hreach hreach' h1 h2 h3
      h4 with h | ⟨_, h⟩ | h
  · exact absurd h h5
  · exact absurd h h6
  · exact h

theorem FinalNodeFallbackFollowsTheChain : Properties.FinalNodeFallbackFollowsTheChain := by
  obtain ⟨s, t, u, hs, ht, hu, hP⟩ := exists_of_bind3
    (o := execCalls mrHashes mrConfigPreV31 fresh (mrMigrationCalls.take 4))
    (f := fun s => exec mrHashes mrConfigPreV31 (mrEnv 11 4) s
      (.setMigratingChainBatchNumber 5 5))
    (g := fun _ t => exec mrHashes mrConfigPreV31 (mrEnv 55 5) t (.addChainBatchRootV32 5 6 106))
    (P := fun s _ u => decide (chainRegistered mrConfigPreV31 s 5 = true
      ∧ s.currentChainBatchNumber 5 = 1
      ∧ chainRegistered mrConfigPreV31 u 5 = true
      ∧ u.currentChainBatchNumber 5 = 6 ∧ u.chainBatchRoots 5 3 = 0
      ∧ 3 < mrConfigPreV31.v31Upgrade 5 ∧ (mrEnv 0 8).l2LogsRootHash 5 3 ≠ 0
      ∧ finalNodeAccepts mrConfigPreV31 (mrEnv 0 8) u 5 3 ((mrEnv 0 8).l2LogsRootHash 5 3)
          = some true
      ∧ finalNodeAccepts mrConfigPreV31 { mrEnv 0 8 with l2LogsRootHash := fun _ _ => 0 } u 5 3
          ((mrEnv 0 8).l2LogsRootHash 5 3) = some false)) (by decide)
  have hreach : Reachable mrHashes mrConfigPreV31 s := reachable_execCalls_init hs
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hP
  exact ⟨s, t, u, hreach, h1, h2, ht, run_cons hu (.nil u), .step (.step hreach ht) hu, h3, h4,
    h5, h6, h7, h8, h9⟩

/-! ## Countermodels for dropped premises -/

theorem MigrationBeforeRegistrationIsOverwritten :
    Properties.MigrationBeforeRegistrationIsOverwritten := by
  obtain ⟨s, t, u, hs, ht, hu, hP⟩ := exists_of_bind3
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 1))
    (f := fun s => exec mrHashes mrConfig (mrEnv 11 2) s (.setMigratingChainBatchNumber 5 5))
    (g := fun _ t => execCalls mrHashes mrConfig t mrReregistrationCalls)
    (P := fun s _ u => decide (chainRegistered mrConfig s 5 = false
      ∧ s.currentChainBatchNumber 5 = 0
      ∧ u.currentChainBatchNumber 5 < 5 ∧ mrConfig.v31Upgrade 5 ≤ 1
      ∧ u.chainBatchRoots 5 1 ≠ 0
      ∧ finalNodeAccepts mrConfig (mrEnv 0 8) u 5 1 (u.chainBatchRoots 5 1) = some true))
    (by decide)
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hP
  exact ⟨s, t, u, reachable_execCalls_init hs, h1, h2, ht, run_of_execCalls hu, h3, h4, h5, h6⟩

theorem ChainTreePositionIsNotBatchNumber : Properties.ChainTreePositionIsNotBatchNumber := by
  obtain ⟨s, hs, hP⟩ := exists_of_map (o := execCalls mrHashes mrConfig fresh mrMigrationCalls)
    (P := fun s => decide (chainRegistered mrConfig s 5 = true
      ∧ s.currentChainBatchNumber 5 = 6
      ∧ s.chainLeaves 5 = [0, 1, 6].map (batchLeafOf mrHashes s 5)
      ∧ ∀ n ∈ ([2, 3, 4, 5] : List ℕ), s.chainBatchRoots 5 n = 0)) (by decide)
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h1, h2, h3, h4⟩ := hP
  refine ⟨s, hs, reachable_execCalls_init hs, h1, h2, h3, fun n hn h5 => h4 n ?_⟩
  simp only [List.mem_cons, List.mem_nil_iff, or_false]
  omega

/-! ## The source checks the guarantees rest on -/

theorem RegisteredCheckLoadBearing : Properties.RegisteredCheckLoadBearing := by
  obtain ⟨s, t, hs, ht, hP⟩ := exists_of_bind_map
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 2))
    (f := fun s => execNoRegisteredCheck mrHashes mrConfig (mrEnv 10 3) s (.addNewChain 5 0))
    (P := fun s t => decide (chainRegistered mrConfig s 5 = true ∧ t.chainCount = 3
      ∧ t.chainIndexToId 1 = 5 ∧ t.chainIndexToId 2 = 5)) (by decide)
  have hreach : Reachable mrHashes mrConfig s := reachable_execCalls_init hs
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h0, h3, h1, h2⟩ := hP
  exact ⟨mrHashes, mrConfig, s, t, mrEnv 10 3, 5, 0, hreach,
    (ChainAddedOnce mrHashes mrConfig s (mrEnv 10 3) 5 0 hreach).1 h0, ht,
    1, 2, by omega, by omega, by omega, h1, h2⟩

theorem ConsecutiveCheckLoadBearing : Properties.ConsecutiveCheckLoadBearing := by
  obtain ⟨s, t, hs, ht, hP⟩ := exists_of_bind_map
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 2))
    (f := fun s => execNoConsecutiveCheck mrHashes mrConfig (mrEnv 55 3) s
      (.addChainBatchRootV32 5 3 103))
    (P := fun s t => decide
      ((exec mrHashes mrConfig (mrEnv 55 3) s (.addChainBatchRootV32 5 3 103)).isNone = true
        ∧ t.currentChainBatchNumber 5 = 1 ∧ t.chainBatchRoots 5 3 = 103)) (by decide)
  have hreach : Reachable mrHashes mrConfig s := reachable_execCalls_init hs
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h0, h1, h2⟩ := hP
  exact ⟨mrHashes, mrConfig, s, t, mrEnv 55 3, 5, 3, 103, hreach,
    Option.isNone_iff_eq_none.1 h0, ht, by omega, by rw [h2]; decide⟩

theorem MigratingCheckLoadBearing : Properties.MigratingCheckLoadBearing := by
  obtain ⟨s, t, u, hs, ht, hu, hP⟩ := exists_of_bind3
    (o := execCalls mrHashes mrConfig fresh (mrCalls.take 8))
    (f := fun s => execNoMigratingCheck mrHashes mrConfig (mrEnv 11 7) s
      (.setMigratingChainBatchNumber 5 2))
    (g := fun _ t => exec mrHashes mrConfig (mrEnv 55 8) t (.addChainBatchRootV32 5 (2 + 1) 103))
    (P := fun s t u => decide
      ((exec mrHashes mrConfig (mrEnv 11 7) s (.setMigratingChainBatchNumber 5 2)).isNone = true
        ∧ t.currentChainBatchNumber 5 = 2 ∧ t.chainBatchRoots 5 6 = 106
        ∧ u.chainLeaves 5 = [0, 1, 6, 3].map (batchLeafOf mrHashes u 5))) (by decide)
  have hreach : Reachable mrHashes mrConfig s := reachable_execCalls_init hs
  simp only [decide_eq_true_eq] at hP
  obtain ⟨h0, h1, h2, h3⟩ := hP
  exact ⟨mrHashes, mrConfig, s, t, u, mrEnv 11 7, mrEnv 55 8, 5, 2, 103, hreach,
    Option.isNone_iff_eq_none.1 h0, ht, ⟨6, by omega, by rw [h2]; decide⟩, hu, h3⟩

private theorem recordNoRegisteredCheck_setups {c n : ℕ} {r : Bytes32} {s t : State}
    (h : recordNoRegisteredCheck c n r s = some t) : t.chainTreeSetups = s.chainTreeSetups := by
  unfold recordNoRegisteredCheck at h
  split_ifs at h
  cases h
  rfl

theorem RecordRegisteredCheckLoadBearing : Properties.RecordRegisteredCheckLoadBearing := by
  refine ⟨?_, ?_⟩
  · obtain ⟨s, t, hs, ht, hP⟩ := exists_of_bind_map
      (o := execCalls mrHashes mrConfig fresh (mrCalls.take 1))
      (f := fun s => execNoRecordRegisteredCheck mrHashes mrConfig (mrEnv 55 2) s
        (.addChainBatchRoot 5 1 101))
      (P := fun s t => decide (chainRegistered mrConfig s 5 = false
        ∧ (exec mrHashes mrConfig (mrEnv 55 2) s (.addChainBatchRoot 5 1 101)).isNone = true
        ∧ chainRegistered mrConfig t 5 = false ∧ t.chainBatchRoots 5 1 = 101)) (by decide)
    have hreach : Reachable mrHashes mrConfig s := reachable_execCalls_init hs
    simp only [decide_eq_true_eq] at hP
    obtain ⟨h0, h1, h2, h3⟩ := hP
    exact ⟨mrHashes, mrConfig, s, t, mrEnv 55 2, 5, 1, 101, hreach, h0,
      Option.isNone_iff_eq_none.1 h1, ht, h2, by rw [h3]; decide⟩
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

end Contracts.MessageRoot
