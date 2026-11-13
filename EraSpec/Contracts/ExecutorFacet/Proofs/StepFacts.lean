import EraSpec.Contracts.ExecutorFacet.Proofs.Invariant

/-!
# Auxiliary: what one call, and a run of calls, does to the counters and the logs

Facts that need no invariant (what each call writes), and their lifts to `Steps`. No
property is stated here; `Proofs/Pipeline.lean` reads the named guarantees off these and
`Proofs/Invariant.lean`.
-/

namespace Contracts.ExecutorFacet

/-! ## Bounds -/

theorem boundsOk_spec {nums : List Nat} {a b : Nat} (h : boundsOk nums a b = true) :
    nums.head? = some a ∧ nums.getLast? = some b := by
  simpa [boundsOk] using h

theorem head?_range'_pos {a n : Nat} (h : 0 < n) : (List.range' a n).head? = some a := by
  cases n with
  | zero => omega
  | succ n => simp [List.range'_succ]

theorem getLast?_range'_pos {a n : Nat} (h : 0 < n) :
    (List.range' a n).getLast? = some (a + n - 1) := by
  rw [List.getLast?_eq_getElem?, List.length_range', List.getElem?_range' (by omega)]
  congr 1
  simp; omega

/-! ## Execute, without the invariant -/

theorem processBatch_basic {env : Env} {s s1 : State} {ops : PriorityOpsBatchInfo}
    (h : processBatch env s ops = some s1) : ∃ X, s1 = pbState s ops X := by
  unfold processBatch at h
  split at h
  · split at h
    · simp at h
    · injection h with h; subst h; exact ⟨_, rfl⟩
  · rename_i hlen
    injection h with h; subst h
    have h0 : ops.itemHashes = [] := List.eq_nil_of_length_eq_zero (by omega)
    exact ⟨[], by simp [pbState, h0]⟩

theorem executeOne_basic {env : Env} {s s' : State} {i : Nat} {b : ExecBatch}
    (h : executeOne env s i b = some s') :
    b.ops.itemHashes.length = b.info.numberOfLayer1Txs ∧
    b.info.batchNumber = s.totalBatchesExecuted + i + 1 ∧
    s.storedBatchHashes b.info.batchNumber = env.hashStored b.info ∧
    env.rollingHash b.ops.itemHashes = b.info.priorityOperationsHash ∧
    b.depRootsHash = some b.info.dependencyRootsRollingHash ∧
    ∃ X, s' = { pbState s b.ops X with
      l2LogsRootHashes := Function.update s.l2LogsRootHashes b.info.batchNumber
        b.info.l2LogsTreeRoot
      executed := s.executed ++ [b.record]
      hashBreaks := s.hashBreaks ++ logHash s b.info.batchNumber b.info } := by
  unfold executeOne at h
  split at h
  · simp at h
  rename_i h1
  split at h
  · simp at h
  rename_i depHash hdep
  split at h
  · simp at h
  rename_i h2
  split at h
  · simp at h
  rename_i h3
  split at h
  · simp at h
  rename_i h4
  split at h
  · simp at h
  rename_i h5
  split at h
  · simp at h
  rename_i s1 hpb
  injection h with h
  subst h
  obtain ⟨X, rfl⟩ := processBatch_basic hpb
  have h5' : depHash = b.info.dependencyRootsRollingHash := by simpa using h5
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
    by rw [hdep, h5'], X, rfl⟩

theorem executeLoop_basic {env : Env} :
    ∀ {bs : List ExecBatch} {s s1 : State} {i : Nat}, executeLoop env s i bs = some s1 →
    s1.totalBatchesExecuted = s.totalBatchesExecuted ∧
    s1.totalBatchesVerified = s.totalBatchesVerified ∧
    s1.totalBatchesCommitted = s.totalBatchesCommitted ∧
    s1.l2SystemContractsUpgradeBatchNumber = s.l2SystemContractsUpgradeBatchNumber ∧
    bs.map (·.info.batchNumber) = List.range' (s.totalBatchesExecuted + i + 1) bs.length ∧
    s1.executed = s.executed ++ bs.map ExecBatch.record ∧
    s1.ptUnprocessedIndex = s.ptUnprocessedIndex + (bs.map (·.info.numberOfLayer1Txs)).sum ∧
    (∀ b ∈ bs, b.ops.itemHashes.length = b.info.numberOfLayer1Txs ∧
      env.rollingHash b.ops.itemHashes = b.info.priorityOperationsHash ∧
      b.depRootsHash = some b.info.dependencyRootsRollingHash)
  | [], s, s1, i, h => by
    simp only [executeLoop, Option.some.injEq] at h; subst h; simp
  | b :: bs, s, s1, i, h => by
    simp only [executeLoop] at h
    split at h
    · simp at h
    · rename_i s2 h2
      obtain ⟨a1, a2, a3, a4, a5, X, rfl⟩ := executeOne_basic h2
      obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := executeLoop_basic h
      dsimp only [pbState] at b1 b2 b3 b4 b5 b6 b7
      refine ⟨b1, b2, b3, b4, ?_, ?_, ?_, ?_⟩
      · rw [List.map_cons, List.length_cons, List.range'_succ, a2, b5]
        congr 2
      · rw [b6, List.map_cons, List.append_assoc]; rfl
      · rw [b7, List.map_cons, List.sum_cons, a1]; omega
      · intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact ⟨a1, a4, a5⟩
        · exact b8 x hx

theorem executeWith_bounds {ab : Bool} {env : Env} {s s' : State} {c : ExecuteCall}
    (h : executeWith ab env s c = some s') :
    boundsOk (c.batches.map (·.info.batchNumber)) c.processFrom c.processTo = true := by
  unfold executeWith at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i h3
  simpa using h3

/-- What a successful `executeBatchesSharedBridge` does to the counters and the logs. -/
theorem execute_basic {env : Env} {s s' : State} {c : ExecuteCall}
    (h : execute env s c = some s') :
    c.batches ≠ [] ∧
    c.processFrom = s.totalBatchesExecuted + 1 ∧
    c.processTo = s.totalBatchesExecuted + c.batches.length ∧
    c.batches.map (·.info.batchNumber) =
      List.range' (s.totalBatchesExecuted + 1) c.batches.length ∧
    s'.totalBatchesExecuted = s.totalBatchesExecuted + c.batches.length ∧
    s.totalBatchesExecuted + c.batches.length ≤ s.totalBatchesVerified ∧
    s'.totalBatchesVerified = s.totalBatchesVerified ∧
    s'.totalBatchesCommitted = s.totalBatchesCommitted ∧
    s'.executed = s.executed ++ c.batches.map ExecBatch.record ∧
    s'.ptUnprocessedIndex =
      s.ptUnprocessedIndex + (c.batches.map (·.info.numberOfLayer1Txs)).sum ∧
    (∀ b ∈ c.batches, b.ops.itemHashes.length = b.info.numberOfLayer1Txs ∧
      env.rollingHash b.ops.itemHashes = b.info.priorityOperationsHash ∧
      b.depRootsHash = some b.info.dependencyRootsRollingHash) := by
  have hb := boundsOk_spec (executeWith_bounds h)
  obtain ⟨-, -, hne, s1, hloop, hle, rfl⟩ := executeWith_some h
  have hle := hle rfl
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := executeLoop_basic hloop
  rw [Nat.add_zero] at b5
  have hpos : 0 < c.batches.length := List.length_pos_iff.2 hne
  rw [b5, head?_range'_pos hpos, getLast?_range'_pos hpos] at hb
  rw [b2] at hle
  refine ⟨hne, ?_, ?_, b5, rfl, hle, b2, b3, b6, b7, b8⟩
  · have := hb.1; simp only [Option.some.injEq] at this; omega
  · have := hb.2; simp only [Option.some.injEq] at this; omega

/-! ## Prove and commit bounds -/

theorem proveWith_bounds {ab : Bool} {env : Env} {s s' : State} {c : ProveCall}
    (h : proveWith ab env s c = some s') :
    boundsOk (c.batches.map (·.batchNumber)) c.processFrom c.processTo = true := by
  unfold proveWith at h
  split_ifs at h with h1 h2 h3
  simpa using h3

theorem commit_bounds {env : Env} {s s' : State} {c : CommitCall}
    (h : commit env s c = some s') :
    boundsOk (c.newBatches.map (·.batchNumber)) c.processFrom c.processTo = true := by
  unfold commit at h
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · simp at h
  rename_i h3
  simpa using h3

/-! ## One call -/

/-- What one call appends to the executed log, and what that does to the executed count and
to the priority tree's unprocessed index. Only `execute` appends. -/
theorem step_executed {env : Env} {s s' : State} {c : Call} (h : step env s c = some s') :
    ∃ X, s'.executed = s.executed ++ X ∧
      s'.totalBatchesExecuted = s.totalBatchesExecuted + X.length ∧
      (X ≠ [] → ∃ ec, c = .execute ec) ∧
      (s'.ptUnprocessedIndex ≠ s.ptUnprocessedIndex → ∃ ec, c = .execute ec) ∧
      s.ptUnprocessedIndex ≤ s'.ptUnprocessedIndex := by
  cases c with
  | commit cc =>
    obtain ⟨b, -, -, -, -, -, -, rfl⟩ := commit_some h
    exact ⟨[], by simp [commitState], by simp [commitState], by simp, by simp [commitState],
      by simp [commitState]⟩
  | prove pc =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := proveWith_some h
    exact ⟨[], by simp, by simp, by simp, by simp, by simp⟩
  | execute ec =>
    obtain ⟨-, -, -, -, a5, -, -, -, a9, a10, -⟩ := execute_basic h
    exact ⟨_, a9, by rw [a5, List.length_map], fun _ => ⟨ec, rfl⟩, fun _ => ⟨ec, rfl⟩,
      by rw [a10]; omega⟩
  | revert caller n =>
    obtain ⟨-, -, -, h⟩ := revertShared_some h
    obtain ⟨-, -, rfl⟩ := revertBatches_some h
    exact ⟨[], by simp, by simp, by simp, by simp, by simp⟩
  | activatePriorityMode =>
    obtain ⟨-, -, h⟩ := activate_some h
    obtain ⟨-, -, rfl⟩ := revertBatches_some h
    exact ⟨[], by simp, by simp, by simp, by simp, by simp⟩
  | deactivatePriorityMode caller =>
    rw [deactivate_some h]; exact ⟨[], by simp, by simp, by simp, by simp, by simp⟩
  | pushPriorityOp hv =>
    simp only [step, stepWith, pushPriorityOp, Option.some.injEq] at h
    subst h; exact ⟨[], by simp, by simp, by simp, by simp, by simp⟩
  | setUpgradeTx hv =>
    rw [setUpgradeTx_some (s := s) h]; exact ⟨[], by simp, by simp, by simp, by simp, by simp⟩

/-- Only `revert` and `activatePriorityMode` lower the committed or the verified count. -/
theorem step_counters {env : Env} {s s' : State} {c : Call} (h : step env s c = some s') :
    (∃ caller n, c = .revert caller n) ∨ c = .activatePriorityMode ∨
    (s.totalBatchesCommitted ≤ s'.totalBatchesCommitted ∧
      s.totalBatchesVerified ≤ s'.totalBatchesVerified) := by
  cases c with
  | commit cc =>
    obtain ⟨b, -, -, -, -, -, -, rfl⟩ := commit_some h
    exact Or.inr (Or.inr ⟨by simp [commitState], by simp [commitState]⟩)
  | prove pc =>
    obtain ⟨-, -, -, -, -, -, rfl⟩ := proveWith_some h
    exact Or.inr (Or.inr ⟨le_rfl, by simp⟩)
  | execute ec =>
    obtain ⟨-, -, -, -, -, -, a7, a8, -⟩ := execute_basic h
    exact Or.inr (Or.inr ⟨by rw [a8], by rw [a7]⟩)
  | revert caller n => exact Or.inl ⟨caller, n, rfl⟩
  | activatePriorityMode => exact Or.inr (Or.inl rfl)
  | deactivatePriorityMode caller =>
    rw [deactivate_some h]; exact Or.inr (Or.inr ⟨le_rfl, le_rfl⟩)
  | pushPriorityOp hv =>
    simp only [step, stepWith, pushPriorityOp, Option.some.injEq] at h
    subst h; exact Or.inr (Or.inr ⟨le_rfl, le_rfl⟩)
  | setUpgradeTx hv =>
    rw [setUpgradeTx_some (s := s) h]; exact Or.inr (Or.inr ⟨le_rfl, le_rfl⟩)

/-- One call from a state satisfying `Inv` leaves the log roots of executed batches (and of
genesis) alone, whether or not a hash break is logged. -/
theorem step_logRoots {env : Env} {s s' : State} {c : Call} (hi : Inv env s)
    (h : step env s c = some s') :
    ∀ n ≤ s.totalBatchesExecuted, s'.l2LogsRootHashes n = s.l2LogsRootHashes n := by
  cases c with
  | commit cc => obtain ⟨b, -, -, -, -, -, -, rfl⟩ := commit_some h; exact fun _ _ => rfl
  | prove pc => obtain ⟨-, -, -, -, -, -, rfl⟩ := proveWith_some h; exact fun _ _ => rfl
  | execute ec => exact (inv_execute hi h).2.1
  | revert caller n =>
    obtain ⟨-, -, -, h⟩ := revertShared_some h
    obtain ⟨-, -, rfl⟩ := revertBatches_some h; exact fun _ _ => rfl
  | activatePriorityMode =>
    obtain ⟨-, -, h⟩ := activate_some h
    obtain ⟨-, -, rfl⟩ := revertBatches_some h; exact fun _ _ => rfl
  | deactivatePriorityMode caller => rw [deactivate_some h]; exact fun _ _ => rfl
  | pushPriorityOp hv =>
    simp only [step, stepWith, pushPriorityOp, Option.some.injEq] at h
    subst h; exact fun _ _ => rfl
  | setUpgradeTx hv => rw [setUpgradeTx_some (s := s) h]; exact fun _ _ => rfl

/-! ## Runs -/

/-- A run only appends to the executed log, and never lowers the executed count or the
unprocessed index. -/
theorem steps_executed {env : Env} {s s' : State} (h : Steps env s s') :
    s.executed <+: s'.executed ∧ s.totalBatchesExecuted ≤ s'.totalBatchesExecuted ∧
    s.ptUnprocessedIndex ≤ s'.ptUnprocessedIndex := by
  induction h with
  | refl => exact ⟨List.prefix_refl _, le_rfl, le_rfl⟩
  | tail _ hs ih =>
    obtain ⟨c, hc⟩ := hs
    obtain ⟨X, hX, hE, -, -, hU⟩ := step_executed hc
    exact ⟨ih.1.trans ⟨X, hX.symm⟩, by omega, by omega⟩

/-- A run only appends to the hash-break log. -/
theorem steps_hashBreaks {env : Env} {s s' : State} (h : Steps env s s') :
    ∃ X, s'.hashBreaks = s.hashBreaks ++ X := by
  induction h with
  | refl => exact ⟨[], by simp⟩
  | tail _ hs ih =>
    obtain ⟨c, hc⟩ := hs
    obtain ⟨X, hX⟩ := step_hashBreaks hc
    obtain ⟨Y, hY⟩ := ih
    exact ⟨Y ++ X, by rw [hX, hY, List.append_assoc]⟩

/-- Across a run from a reachable state, the log roots of the batches executed at its start
(and of genesis) do not change. -/
theorem steps_logRoots {env : Env} {s s' : State} (hr : Reach env s) (h : Steps env s s') :
    ∀ n ≤ s.totalBatchesExecuted, s'.l2LogsRootHashes n = s.l2LogsRootHashes n := by
  induction h with
  | refl => exact fun _ _ => rfl
  | tail hsm hs ih =>
    obtain ⟨c, hc⟩ := hs
    intro n hn
    have hmid := (steps_executed hsm).2.1
    rw [step_logRoots (inv_reach (reach_steps hr hsm)) hc n (by omega)]
    exact ih n hn

/-- Across a run from a reachable state that ends with no hash break logged, the stored
hashes and ghost preimages of the batches executed at its start do not change. -/
theorem steps_frozen {env : Env} {s s' : State} (hr : Reach env s) (h : Steps env s s')
    (hc' : s'.hashBreaks = []) :
    ∀ n ≤ s.totalBatchesExecuted,
      s'.storedBatchHashes n = s.storedBatchHashes n ∧ s'.preimage n = s.preimage n := by
  induction h with
  | refl => exact fun _ _ => ⟨rfl, rfl⟩
  | tail hsm hs ih =>
    obtain ⟨c, hc⟩ := hs
    intro n hn
    obtain ⟨X, hX⟩ := step_hashBreaks hc
    have hmidClean : _ = [] := (List.append_eq_nil_iff.1 (hX ▸ hc')).1
    have hmid := (steps_executed hsm).2.1
    obtain ⟨f1, f2, -⟩ :=
      (step_frozen (inv_reach (reach_steps hr hsm)) hc).2 hc' n (by omega)
    obtain ⟨g1, g2⟩ := ih hmidClean n hn
    exact ⟨f1.trans g1, f2.trans g2⟩

end Contracts.ExecutorFacet
