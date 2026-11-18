import EraSpec.Contracts.MessageRoot.Proofs.Invariant

/-!
# Auxiliary: what one successful call does to one chain

`step_facts`: on storage satisfying `Inv`, any successful call keeps nonzero batch roots and
their timestamps, extends each chain tree, keeps registrations, indices and slots, does not
lower a registered chain's counter, and touches chain `c`'s roots, timestamps and tree only
when sent by `getZKChain(c)` or the Bridgehub (its counter also by the chain asset handler).
`exec_logId` and `exec_interop` describe the two bookkeeping fields on any storage.
-/

namespace Contracts.MessageRoot

variable {H : Hashes} {cfg : Config}

/-- The per-chain facts of one step. -/
structure StepFacts (cfg : Config) (env : Env) (s t : State) (c : ℕ) : Prop where
  roots_once : ∀ n, s.chainBatchRoots c n ≠ 0 →
    t.chainBatchRoots c n = s.chainBatchRoots c n
      ∧ t.chainBatchRootTimestamp c n = s.chainBatchRootTimestamp c n
  leaves_prefix : s.chainLeaves c <+: t.chainLeaves c
  reg_keep : chainRegistered cfg s c = true →
    chainRegistered cfg t c = true ∧ t.chainIndex c = s.chainIndex c
      ∧ s.currentChainBatchNumber c ≤ t.currentChainBatchNumber c
  writers : env.sender ≠ env.zkChain c → env.sender ≠ cfg.bridgehub →
    t.chainBatchRoots c = s.chainBatchRoots c
      ∧ t.chainBatchRootTimestamp c = s.chainBatchRootTimestamp c
      ∧ t.chainLeaves c = s.chainLeaves c
      ∧ (env.sender ≠ cfg.chainAssetHandler →
          t.currentChainBatchNumber c = s.currentChainBatchNumber c)
  count_le : s.chainCount ≤ t.chainCount
  slots_keep : ∀ i, i < s.chainCount → t.chainIndexToId i = s.chainIndexToId i

/-- The push half of a batch append, as one `StepFacts`-shaped fact about chain `c`. -/
theorem push_facts {env : Env} {c0 n : ℕ} {r : Bytes32} {s t : State} (c : ℕ)
    (h : pushChainBatchRoot H env c0 n r s = some t) :
    t.chainBatchRoots = s.chainBatchRoots
      ∧ t.currentChainBatchNumber = s.currentChainBatchNumber
      ∧ t.chainIndex = s.chainIndex ∧ t.chainCount = s.chainCount
      ∧ t.chainIndexToId = s.chainIndexToId
      ∧ t.chainBatchRootTimestamp = upd2 s.chainBatchRootTimestamp c0 n env.timestamp
      ∧ t.chainLeaves c = (if c = c0 then s.chainLeaves c ++ [H.batchLeaf r n env.timestamp]
          else s.chainLeaves c) := by
  obtain ⟨S', R, k, _, _, _, rfl⟩ := pushChainBatchRoot_some h
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  by_cases hc : c = c0
  · subst hc; simp
  · simp [Function.update_of_ne hc, hc]

theorem step_facts {env : Env} {call : Call} {s t : State} (hI : Inv H cfg s)
    (h : exec H cfg env s call = some t) (c : ℕ) : StepFacts cfg env s t c := by
  cases call with
  | «initialize» =>
    have := hI.initialized
    simp [exec, show ¬ s.initialized < 2 by omega] at h
  | addNewChain c0 start =>
    simp only [exec] at h
    split_ifs at h with h1 h2
    have hc0 : chainRegistered cfg s c0 = false := by simpa using h2
    obtain ⟨hcs, hidx⟩ := chainRegistered_false.1 hc0
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h
    have hk0 : s.chainCount ≠ 0 := by have := hI.count_pos; omega
    have hleaves : (Function.update s.chainLeaves c0 [] c) = s.chainLeaves c := by
      by_cases hcc : c = c0
      · subst hcc; rw [Function.update_self, (hI.unreg_empty c hc0).1]
      · rw [Function.update_of_ne hcc]
    refine ⟨fun _ _ => ⟨rfl, rfl⟩, by simp only [hleaves]; exact List.prefix_refl _, ?_, ?_,
      by simp, ?_⟩
    · intro hc
      have hcc : c ≠ c0 := by rintro rfl; rw [hc] at hc0; cases hc0
      refine ⟨?_, by simp [Function.update_of_ne hcc], by simp [Function.update_of_ne hcc]⟩
      simp only [chainRegistered, Function.update_of_ne hcc]; exact hc
    · intro _ hbh
      refine ⟨rfl, rfl, hleaves, fun hcah => ?_⟩
      push Not at h1
      exact absurd (h1 hbh) hcah
    · intro i hi
      simp [Function.update_of_ne (Nat.ne_of_lt hi)]
  | setMigratingChainBatchNumber c0 n =>
    simp only [exec] at h
    split_ifs at h with h1 h2
    cases h
    push Not at h1
    refine ⟨fun _ _ => ⟨rfl, rfl⟩, List.prefix_refl _, fun hc => ⟨hc, rfl, ?_⟩,
      fun _ _ => ⟨rfl, rfl, rfl, fun hcah => absurd h1 hcah⟩, le_rfl, fun _ _ => rfl⟩
    by_cases hcc : c = c0
    · subst hcc; simpa using h2
    · simp [Function.update_of_ne hcc]
  | addChainBatchRoot c0 n r =>
    simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    obtain ⟨hc0, hr, h0, _, hn, rfl⟩ := recordChainBatchRoot_some h
    refine ⟨fun m hm => ⟨?_, rfl⟩, List.prefix_refl _, fun hc => ⟨hc, rfl, ?_⟩, ?_, le_rfl,
      fun _ _ => rfl⟩
    · simp only [upd2_apply]; split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h0 hm
      · rfl
    · by_cases hcc : c = c0
      · subst hcc; simp; omega
      · simp [Function.update_of_ne hcc]
    · intro hz _
      have hcc : c ≠ c0 := by rintro rfl; exact hz h1
      refine ⟨?_, rfl, rfl, fun _ => by simp [Function.update_of_ne hcc]⟩
      funext m; simp [upd2_apply, hcc]
  | addChainBatchRootV32 c0 n r =>
    simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c0 n r s = some s₁
        ∧ pushChainBatchRoot H env c0 n r s₁ = some t := by
      cases hrec : recordChainBatchRoot cfg c0 n r s with
      | none => rw [hrec] at h; cases h
      | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
    obtain ⟨hc0, hr, h0, _, hn, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨er, ec, ei, ek, eto, ets, el⟩ := push_facts c h₂
    simp only at er ec ei ek eto
    refine ⟨fun m hm => ⟨?_, ?_⟩, ?_, fun hc => ⟨?_, by rw [ei], ?_⟩, ?_, by rw [ek],
      fun _ _ => by rw [eto]⟩
    · rw [er]; simp only [upd2_apply]; split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h0 hm
      · rfl
    · rw [ets]; simp only [upd2_apply]; split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h0 hm
      · rfl
    · rw [el]; split_ifs
      · exact List.prefix_append _ _
      · exact List.prefix_refl _
    · simp only [chainRegistered, ei]; simpa [chainRegistered] using hc
    · rw [ec]; by_cases hcc : c = c0
      · subst hcc; simp; omega
      · simp [Function.update_of_ne hcc]
    · intro hz _
      have hcc : c ≠ c0 := by rintro rfl; exact hz h1
      refine ⟨?_, ?_, by rw [el]; simp [hcc], fun _ => by rw [ec]; simp [Function.update_of_ne hcc]⟩
      · rw [er]; funext m; simp [upd2_apply, hcc]
      · rw [ets]; funext m; simp [upd2_apply, hcc]
  | seedGenesisRoot c0 =>
    simp only [exec] at h
    split_ifs at h with h1 h2 h3 h4 h5
    push Not at h1 h2 h4 h5
    obtain ⟨er, ec, ei, ek, eto, ets, el⟩ := push_facts c h
    simp only at er ec ei ek eto
    refine ⟨fun m hm => ⟨?_, ?_⟩, ?_, fun hc => ⟨?_, by rw [ei], by rw [ec]⟩,
      fun _ hbh => absurd h1 hbh, by rw [ek], fun _ _ => by rw [eto]⟩
    · rw [er]; simp only [upd2_apply]; split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h5 hm
      · rfl
    · rw [ets]; simp only [upd2_apply]; split_ifs with hcm
      · obtain ⟨rfl, rfl⟩ := hcm; exact absurd h5 hm
      · rfl
    · rw [el]; split_ifs
      · exact List.prefix_append _ _
      · exact List.prefix_refl _
    · simp only [chainRegistered, ei]; simpa [chainRegistered] using hc
  | enableInterop c0 req =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact ⟨fun _ _ => ⟨rfl, rfl⟩, List.prefix_refl _, fun hc => ⟨hc, rfl, le_rfl⟩,
      fun _ _ => ⟨rfl, rfl, rfl, fun _ => rfl⟩, le_rfl, fun _ _ => rfl⟩

/-- One successful call either leaves chain `c`'s batch roots, timestamps and tree alone, or is
an append for `c` sent by `getZKChain(c)`, or is `seedGenesisRoot(c)` sent by the Bridgehub. -/
theorem step_writer {env : Env} {call : Call} {s t : State} (hI : Inv H cfg s)
    (h : exec H cfg env s call = some t) (c : ℕ) :
    (t.chainBatchRoots c = s.chainBatchRoots c
        ∧ t.chainBatchRootTimestamp c = s.chainBatchRootTimestamp c
        ∧ t.chainLeaves c = s.chainLeaves c)
      ∨ (env.sender = env.zkChain c
          ∧ ∃ n r, call = .addChainBatchRoot c n r ∨ call = .addChainBatchRootV32 c n r)
      ∨ (env.sender = cfg.bridgehub ∧ call = .seedGenesisRoot c) := by
  cases call with
  | «initialize» =>
    have := hI.initialized
    simp [exec, show ¬ s.initialized < 2 by omega] at h
  | addNewChain c0 start =>
    simp only [exec] at h
    split_ifs at h with h1 h2
    have hc0 : chainRegistered cfg s c0 = false := by simpa using h2
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h
    refine Or.inl ⟨rfl, rfl, ?_⟩
    by_cases hcc : c = c0
    · subst hcc; simp [(hI.unreg_empty c hc0).1]
    · simp [Function.update_of_ne hcc]
  | setMigratingChainBatchNumber c0 n =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl ⟨rfl, rfl, rfl⟩
  | addChainBatchRoot c0 n r =>
    simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h
    by_cases hcc : c = c0
    · subst hcc; exact Or.inr (Or.inl ⟨h1, n, r, Or.inl rfl⟩)
    · refine Or.inl ⟨?_, rfl, rfl⟩
      funext m; simp [upd2_apply, hcc]
  | addChainBatchRootV32 c0 n r =>
    simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    by_cases hcc : c = c0
    · subst hcc; exact Or.inr (Or.inl ⟨h1, n, r, Or.inr rfl⟩)
    · obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c0 n r s = some s₁
          ∧ pushChainBatchRoot H env c0 n r s₁ = some t := by
        cases hrec : recordChainBatchRoot cfg c0 n r s with
        | none => rw [hrec] at h; cases h
        | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
      obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h₁
      obtain ⟨er, _, _, _, _, ets, el⟩ := push_facts c h₂
      refine Or.inl ⟨?_, ?_, by rw [el]; simp [hcc]⟩
      · rw [er]; funext m; simp [upd2_apply, hcc]
      · rw [ets]; funext m; simp [upd2_apply, hcc]
  | seedGenesisRoot c0 =>
    simp only [exec] at h
    split_ifs at h with h1
    push Not at h1
    by_cases hcc : c = c0
    · subst hcc; exact Or.inr (Or.inr ⟨h1, rfl⟩)
    · obtain ⟨er, _, _, _, _, ets, el⟩ := push_facts c h
      refine Or.inl ⟨?_, ?_, by rw [el]; simp [hcc]⟩
      · rw [er]; funext m; simp [upd2_apply, hcc]
      · rw [ets]; funext m; simp [upd2_apply, hcc]
  | enableInterop c0 req =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl ⟨rfl, rfl, rfl⟩

/-- One successful call does not change `chainBatchRoots[c][n]` for `n` at or below the chain's
counter, once the counter is positive or the genesis root is recorded. -/
theorem step_frozen {env : Env} {call : Call} {s t : State} (hI : Inv H cfg s)
    (h : exec H cfg env s call = some t) (c n : ℕ) (hn : n ≤ s.currentChainBatchNumber c)
    (h0 : 0 < s.currentChainBatchNumber c ∨ s.chainBatchRoots c 0 ≠ 0) :
    t.chainBatchRoots c n = s.chainBatchRoots c n := by
  cases call with
  | «initialize» =>
    have := hI.initialized
    simp [exec, show ¬ s.initialized < 2 by omega] at h
  | addNewChain c0 start =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h
    rfl
  | setMigratingChainBatchNumber c0 m =>
    simp only [exec] at h
    split_ifs at h
    cases h
    rfl
  | addChainBatchRoot c0 m r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨_, _, _, _, hm, rfl⟩ := recordChainBatchRoot_some h
    simp only [upd2_apply]
    split_ifs with hcm
    · obtain ⟨rfl, rfl⟩ := hcm; omega
    · rfl
  | addChainBatchRootV32 c0 m r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c0 m r s = some s₁
        ∧ pushChainBatchRoot H env c0 m r s₁ = some t := by
      cases hrec : recordChainBatchRoot cfg c0 m r s with
      | none => rw [hrec] at h; cases h
      | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
    obtain ⟨_, _, _, _, hm, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨er, _⟩ := push_facts c h₂
    rw [er]
    simp only [upd2_apply]
    split_ifs with hcm
    · obtain ⟨rfl, rfl⟩ := hcm; omega
    · rfl
  | seedGenesisRoot c0 =>
    simp only [exec] at h
    split_ifs at h with h1 h2 h3 h4 h5
    push Not at h4 h5
    obtain ⟨er, _⟩ := push_facts c h
    rw [er]
    simp only [upd2_apply]
    split_ifs with hcm
    · obtain ⟨rfl, rfl⟩ := hcm
      rcases h0 with h0 | h0
      · omega
      · exact absurd h5 h0
    · rfl
  | enableInterop c0 req =>
    simp only [exec] at h
    split_ifs at h
    cases h
    rfl

/-! ## The two bookkeeping fields, on any storage -/

theorem exec_logId {env : Env} {call : Call} {s t : State} (h : exec H cfg env s call = some t) :
    (t.interopRootLogId = s.interopRootLogId ∧ t.lastEmitBlock = s.lastEmitBlock)
      ∨ (t.lastEmitBlock = env.blockNumber
        ∧ (env.blockNumber = s.lastEmitBlock → t.interopRootLogId = s.interopRootLogId)
        ∧ (t.interopRootLogId = s.interopRootLogId
          ∨ t.interopRootLogId = s.interopRootLogId + 1)) := by
  cases call with
  | «initialize» =>
    simp only [exec, Option.bind_eq_bind] at h
    split_ifs at h
    all_goals try (simp at h; done)
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.1 h
    cases h₃
    obtain ⟨S', R, k, _, _, hk1, hk2, rfl⟩ := addNewChainInternal_some h₂
    exact Or.inr ⟨rfl, hk1, hk2⟩
  | addNewChain c0 start =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨S', R, k, _, _, hk1, hk2, rfl⟩ := addNewChainInternal_some h
    exact Or.inr ⟨rfl, hk1, hk2⟩
  | setMigratingChainBatchNumber c0 n =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl ⟨rfl, rfl⟩
  | addChainBatchRoot c0 n r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h
    exact Or.inl ⟨rfl, rfl⟩
  | addChainBatchRootV32 c0 n r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c0 n r s = some s₁
        ∧ pushChainBatchRoot H env c0 n r s₁ = some t := by
      cases hrec : recordChainBatchRoot cfg c0 n r s with
      | none => rw [hrec] at h; cases h
      | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
    obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨S', R, k, _, hk1, hk2, rfl⟩ := pushChainBatchRoot_some h₂
    exact Or.inr ⟨rfl, hk1, hk2⟩
  | seedGenesisRoot c0 =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨S', R, k, _, hk1, hk2, rfl⟩ := pushChainBatchRoot_some h
    exact Or.inr ⟨rfl, hk1, hk2⟩
  | enableInterop c0 req =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl ⟨rfl, rfl⟩

theorem exec_interop {env : Env} {call : Call} {s t : State}
    (h : exec H cfg env s call = some t) :
    t.interopEnabled = s.interopEnabled
      ∨ ∃ c0 req, call = .enableInterop c0 req ∧ env.sender = env.bridgehubOwner
        ∧ env.zkChain c0 ≠ 0 ∧ s.interopEnabled c0 = false ∧ env.backfillPending c0 = false
        ∧ t.interopEnabled = Function.update s.interopEnabled c0 true := by
  cases call with
  | «initialize» =>
    simp only [exec, Option.bind_eq_bind] at h
    split_ifs at h
    all_goals try (simp at h; done)
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.1 h
    cases h₃
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h₂
    exact Or.inl rfl
  | addNewChain c0 start =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨S', R, k, _, _, _, _, rfl⟩ := addNewChainInternal_some h
    exact Or.inl rfl
  | setMigratingChainBatchNumber c0 n =>
    simp only [exec] at h
    split_ifs at h
    cases h
    exact Or.inl rfl
  | addChainBatchRoot c0 n r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h
    exact Or.inl rfl
  | addChainBatchRootV32 c0 n r =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨s₁, h₁, h₂⟩ : ∃ s₁, recordChainBatchRoot cfg c0 n r s = some s₁
        ∧ pushChainBatchRoot H env c0 n r s₁ = some t := by
      cases hrec : recordChainBatchRoot cfg c0 n r s with
      | none => rw [hrec] at h; cases h
      | some s₁ => rw [hrec] at h; exact ⟨s₁, rfl, h⟩
    obtain ⟨_, _, _, _, _, rfl⟩ := recordChainBatchRoot_some h₁
    obtain ⟨S', R, k, _, _, _, rfl⟩ := pushChainBatchRoot_some h₂
    exact Or.inl rfl
  | seedGenesisRoot c0 =>
    simp only [exec] at h
    split_ifs at h
    obtain ⟨S', R, k, _, _, _, rfl⟩ := pushChainBatchRoot_some h
    exact Or.inl rfl
  | enableInterop c0 req =>
    simp only [exec] at h
    split_ifs at h with h1 h2 h3 h4
    cases h
    push Not at h1 h2
    refine Or.inr ⟨c0, req, rfl, h1, h2, by simpa using h3, by simpa using h4, rfl⟩

end Contracts.MessageRoot
