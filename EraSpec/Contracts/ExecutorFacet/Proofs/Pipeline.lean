import EraSpec.Contracts.ExecutorFacet.Properties.Pipeline
import EraSpec.Contracts.ExecutorFacet.Proofs.StepFacts

/-!
# Proofs: the batch pipeline

Each theorem proves the property of the same name in
`EraSpec.Contracts.ExecutorFacet.Properties.Pipeline`. The run-level statements are read
off the reachable-state invariant `Inv` (`Proofs/Invariant.lean`); the one-call statements
off the step lemmas (`Proofs/StepFacts.lean`).
-/

namespace Contracts.ExecutorFacet

/-! ## Reading the break disjuncts off the invariant -/

/-- A non-empty hash-break log of a state satisfying `Inv` has a genuine first entry. -/
theorem hashBreakLogged_of_ne_nil {env : Env} {s : State} (hi : Inv env s)
    (h : s.hashBreaks ≠ []) : HashBreakLogged env s := by
  obtain ⟨br, l, hl⟩ := List.exists_cons_of_ne_nil h
  exact ⟨br, by simp [hl], hi.firstBreak br (by simp [hl])⟩

/-- A non-empty Merkle-break log of a state satisfying `Inv` has a genuine entry. -/
theorem merkleBreakLogged_of_ne_nil {env : Env} {s : State} (hi : Inv env s)
    (h : s.merkleBreaks ≠ []) : MerkleBreakLogged env s := by
  obtain ⟨br, l, hl⟩ := List.exists_cons_of_ne_nil h
  exact ⟨br, by simp [hl], hi.merkleGenuine br (by simp [hl])⟩

/-- Either a hash break is logged, or the log is empty and the clean invariant holds. -/
theorem hashBreakLogged_or_clean {env : Env} {s : State} (hi : Inv env s) :
    HashBreakLogged env s ∨ (s.hashBreaks = [] ∧ CleanInv env s) := by
  by_cases h : s.hashBreaks = []
  · exact Or.inr ⟨h, hi.clean h⟩
  · exact Or.inl (hashBreakLogged_of_ne_nil hi h)

/-! ## The three counters -/

theorem CountersOrdered : Properties.CountersOrdered := by
  intro env s hr
  have hi := inv_reach hr
  exact ⟨hi.ev, hi.vc⟩

theorem OnlyRevertMovesCountersBack : Properties.OnlyRevertMovesCountersBack := by
  intro env s s' c h
  obtain ⟨X, -, hE, -⟩ := step_executed h
  exact ⟨by omega, step_counters h⟩

private theorem min_eq_ite (n v : Nat) : min n v = if n < v then n else v := by
  split <;> omega

theorem RevertBatchesEffect : Properties.RevertBatchesEffect := by
  intro s s' n
  constructor
  · intro h
    obtain ⟨h1, h2, rfl⟩ := revertBatches_some h
    exact ⟨h1, h2, by rw [min_eq_ite]⟩
  · rintro ⟨h1, h2, rfl⟩
    have h3 : ¬ s.totalBatchesCommitted < n := by omega
    have h4 : ¬ n < s.totalBatchesExecuted := by omega
    unfold revertBatches revertBatchesWith
    simp only [h3, h4, and_false, ↓reduceIte, min_eq_ite, gt_iff_lt]

theorem RevertEntryPoints : Properties.RevertEntryPoints := by
  refine ⟨fun s s' caller n h => revertShared_some h, fun s s' h => ?_,
    fun env s s' c hpm h => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := activate_some h
    obtain ⟨-, -, rfl⟩ := revertBatches_some h3
    refine ⟨h2, h1, h3, rfl, rfl, fun hev => ?_⟩
    dsimp only
    split <;> omega
  · rcases step_counters h with ⟨caller, n, rfl⟩ | rfl | h'
    · have := (revertShared_some h).2.1
      rw [hpm] at this
      exact absurd this (by decide)
    · have := (activate_some h).2.1
      rw [hpm] at this
      exact absurd this (by decide)
    · exact h'

theorem OnlySettlersSettle : Properties.OnlySettlersSettle := by
  refine ⟨fun env s s' c h => ?_, fun env s s' c h => ?_, fun env s s' c h => ?_⟩
  · obtain ⟨b, hb, h1, h2, -, -, h5, -⟩ := commit_some h
    refine ⟨h1, h2, fun hpm x hx => ?_⟩
    rw [hb, List.mem_singleton] at hx
    subst hx
    exact ⟨by_contra fun h => h5 ⟨hpm, Or.inl h⟩, fun h => h5 ⟨hpm, Or.inr h⟩⟩
  · obtain ⟨h1, h2, -⟩ := proveWith_some h
    exact ⟨h1, h2⟩
  · obtain ⟨h1, h2, -⟩ := executeWith_some h
    exact ⟨h1, h2⟩

/-! ## Executed batches -/

theorem ExecutedExactlyOnceInOrder : Properties.ExecutedExactlyOnceInOrder := by
  intro env s hr
  have h := (inv_reach hr).execNums
  refine ⟨h, by rw [h]; exact List.nodup_range', ?_, fun n => ?_⟩
  · simpa using congrArg List.length h
  · rw [h, List.mem_range'_1]
    exact ⟨fun ⟨a, b⟩ => ⟨a, by omega⟩, fun ⟨a, b⟩ => ⟨a, by omega⟩⟩

theorem ExecutedIsFinal : Properties.ExecutedIsFinal := by
  intro env s s' hr hs
  obtain ⟨h1, h2, -⟩ := steps_executed hs
  exact ⟨h1, h2, steps_logRoots hr hs⟩

theorem ExecutedLogRootsRecorded : Properties.ExecutedLogRootsRecorded :=
  fun _ _ hr => (inv_reach hr).logRoots

theorem ExecutedStoredHashesFinal : Properties.ExecutedStoredHashesFinal := by
  intro env s s' hr hs
  by_cases hc : s'.hashBreaks = []
  · exact Or.inr fun n hn => (steps_frozen hr hs hc n hn).1
  · exact Or.inl (hashBreakLogged_of_ne_nil (inv_reach (reach_steps hr hs)) hc)

theorem ExecutedBatchesWereCommittedAndProved :
    Properties.ExecutedBatchesWereCommittedAndProved := by
  intro env s hr
  have hi := inv_reach hr
  rcases hashBreakLogged_or_clean hi with h | ⟨-, c⟩
  · exact Or.inl h
  · refine Or.inr fun r hr' => ⟨c.execInfo r hr', ?_, c.execProved r hr'⟩
    have hb := (mem_executed_bounds hi.execNums hr').2
    have hev := hi.ev
    have hvc := hi.vc
    rw [c.hashes _ (by omega), ← c.execInfo r hr']

/-! ## Committed and verified batches -/

theorem StoredHashesChain : Properties.StoredHashesChain := by
  intro env s hr
  rcases hashBreakLogged_or_clean (inv_reach hr) with h | ⟨-, c⟩
  · exact Or.inl h
  · refine Or.inr ⟨fun n hn => ⟨c.hashes n hn, c.numbers n hn⟩, fun n h1 hn => ?_⟩
    obtain ⟨a, ha, h2, h3⟩ := c.chain n h1 hn
    exact ⟨a, ha, h2, h3, c.fees n h1 hn a ha⟩

theorem VerifiedBatchesHaveAcceptedProofs : Properties.VerifiedBatchesHaveAcceptedProofs := by
  intro env s hr
  have hi := inv_reach hr
  refine ⟨hi.verifiedOk, ?_⟩
  rcases hashBreakLogged_or_clean hi with h | ⟨-, c⟩
  · exact Or.inl h
  · exact Or.inr c.proved

/-! ## What each call processes -/

theorem ExecuteTakesTheNextBatches : Properties.ExecuteTakesTheNextBatches := by
  intro env s s' c h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -, a11⟩ := execute_basic h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a11⟩

theorem ProveTakesTheNextBatches : Properties.ProveTakesTheNextBatches := by
  intro env s s' c hr h
  have hi := inv_reach hr
  have hb := boundsOk_spec (proveWith_bounds h)
  have hi' := inv_prove hi h
  obtain ⟨-, -, hne, -, hle, hver, rfl⟩ := proveWith_some h
  have hle := hle rfl
  refine ⟨hne, hle, hver, rfl, rfl, rfl, ?_⟩
  by_cases hc : s.hashBreaks ++ proveBreaks s s.totalBatchesVerified c.batches = []
  · obtain ⟨hc0, hl⟩ := List.append_eq_nil_iff.1 hc
    have c0 := hi.clean hc0
    have hpre := proveBreaks_nil hl
    have hpos : 0 < c.batches.length := List.length_pos_iff.2 hne
    refine Or.inr ⟨hpre, ?_, ?_⟩
    · have hget : c.batches[0]? = some (c.batches[0]'hpos) := List.getElem?_eq_getElem hpos
      have h0 := hpre 0 _ hget
      have hn0 := c0.numbers (s.totalBatchesVerified + 1 + 0) (by omega)
      have hh := hb.1
      rw [List.head?_eq_getElem?, List.getElem?_map, hget] at hh
      simp only [Option.map_some, Option.some.injEq] at hh
      rw [← hh, h0, hn0]
    · have hk : c.batches.length - 1 < c.batches.length := by omega
      have hget : c.batches[c.batches.length - 1]? = some (c.batches[c.batches.length - 1]'hk) :=
        List.getElem?_eq_getElem hk
      have h1 := hpre _ _ hget
      have hn1 := c0.numbers (s.totalBatchesVerified + 1 + (c.batches.length - 1)) (by omega)
      have hl' := hb.2
      rw [List.getLast?_eq_getElem?, List.length_map, List.getElem?_map, hget] at hl'
      simp only [Option.map_some, Option.some.injEq] at hl'
      rw [← hl', h1, hn1]
      omega
  · exact Or.inl (hashBreakLogged_of_ne_nil hi' hc)

theorem CommitTakesTheNextBatch : Properties.CommitTakesTheNextBatch := by
  intro env s s' c hr h
  have hi := inv_reach hr
  have hb := boundsOk_spec (commit_bounds h)
  have hi' := inv_commit hi h
  obtain ⟨b, hbs, -, -, -, hnum, -, rfl⟩ := commit_some h
  refine ⟨b, hbs, rfl, rfl, rfl, ?_⟩
  by_cases hc : (commitState env s c.lastCommitted b).hashBreaks = []
  · have hc' := hc
    simp only [commitState, List.append_eq_nil_iff] at hc'
    obtain ⟨hc0, hl⟩ := hc'
    have c0 := hi.clean hc0
    have hlast := logHash_eq_nil.1 hl
    have hN : b.batchNumber = s.totalBatchesCommitted + 1 := by
      rw [hnum, hlast, c0.numbers _ le_rfl]
    rw [hbs] at hb
    simp only [List.map_cons, List.map_nil, List.head?_cons, Option.some.injEq,
      List.getLast?_singleton] at hb
    refine Or.inr ⟨hlast, hN, by omega, by omega, ?_⟩
    simp only [commitState]
    rw [← hN]
    exact ⟨_, Function.update_self _ _ _, rfl, by rw [hlast], by rw [Function.update_self]⟩
  · exact Or.inl (hashBreakLogged_of_ne_nil hi' hc)

/-! ## Honest progress -/

theorem HonestCommitEnabled : Properties.HonestCommitEnabled := by
  intro env s caller b hr hc hsl hset hb hpm
  have c := (inv_reach hr).clean hc
  have h1 : s.storedBatchHashes s.totalBatchesCommitted =
      env.hashStored (s.preimage s.totalBatchesCommitted) := c.hashes _ le_rfl
  have h2 : (s.preimage s.totalBatchesCommitted).batchNumber + 1 = b.batchNumber := by
    rw [c.numbers _ le_rfl, hb]
  have h3 : ¬ (s.priorityModeActivated = true ∧
      (b.numberOfLayer2Txs ≠ 0 ∨ b.numberOfLayer1Txs = 0)) := by
    rintro ⟨hp, h | h⟩
    · exact h (hpm hp).1
    · exact (hpm hp).2 h
  unfold commit
  simp [hset, hsl, h1, h2, h3, boundsOk]

/-- The converse of `proveChecks_spec`: the loop's checks pass when every listed batch hashes
to its slot. -/
theorem proveChecks_of {env : Env} {s : State} :
    ∀ {n : Nat} {bs : List StoredBatchInfo},
    (∀ j b, bs[j]? = some b → s.storedBatchHashes (n + 1 + j) = env.hashStored b) →
    proveChecks env s n bs = true
  | _, [], _ => rfl
  | n, b :: bs, h => by
    simp only [proveChecks, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨by simpa using h 0 b rfl, proveChecks_of fun j b' hb' => ?_⟩
    have := h (j + 1) b' (by simpa using hb')
    rwa [show n + 1 + (j + 1) = n + 1 + 1 + j by omega] at this

theorem HonestProveEnabledIff : Properties.HonestProveEnabledIff := by
  intro env s caller k proof hr hc hsl hset hk hle
  have c := (inv_reach hr).clean hc
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have hnums : ((List.range (k' + 1)).map
      (fun j => s.preimage (s.totalBatchesVerified + 1 + j))).map (·.batchNumber) =
      (List.range (k' + 1)).map (fun j => s.totalBatchesVerified + 1 + j) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    exact c.numbers _ (by omega)
  have hhead : ((List.range (k' + 1)).map (fun j => s.totalBatchesVerified + 1 + j)).head? =
      some (s.totalBatchesVerified + 1) := by
    rw [List.range_succ_eq_map]
    simp
  have hlast : ((List.range (k' + 1)).map (fun j => s.totalBatchesVerified + 1 + j)).getLast? =
      some (s.totalBatchesVerified + (k' + 1)) := by
    rw [List.range_succ, List.map_append]
    simp
    omega
  have hprev : s.storedBatchHashes s.totalBatchesVerified =
      env.hashStored (s.preimage s.totalBatchesVerified) := c.hashes _ (by omega)
  have hchecks : proveChecks env s s.totalBatchesVerified ((List.range (k' + 1)).map
      (fun j => s.preimage (s.totalBatchesVerified + 1 + j))) = true := by
    apply proveChecks_of
    intro j b hb
    obtain ⟨hj, hbj⟩ := List.getElem?_eq_some_iff.1 hb
    simp only [List.length_map, List.length_range] at hj
    simp only [List.getElem_map, List.getElem_range] at hbj
    subst hbj
    exact c.hashes _ (by omega)
  unfold prove proveWith
  simp only [hset, hsl, boundsOk, hnums, hhead, hlast, hprev, hchecks]
  cases env.verify (((List.range (k' + 1)).map
      (fun j => s.preimage (s.totalBatchesVerified + 1 + j))).map (·.commitment)) proof <;>
    simp [hle]

/-! ## Priority operations -/

theorem PriorityOpsConsumedInOrder : Properties.PriorityOpsConsumedInOrder := by
  intro env s hr
  have hi := inv_reach hr
  refine ⟨hi.unproc, hi.execPrio, ?_⟩
  by_cases hm : s.merkleBreaks = []
  · obtain ⟨h1, h2⟩ := hi.prefixOk hm
    exact Or.inr ⟨h2, h1⟩
  · exact Or.inl (merkleBreakLogged_of_ne_nil hi hm)

theorem PriorityOpsConsumedOnlyByExecute : Properties.PriorityOpsConsumedOnlyByExecute := by
  intro env s s' c h
  obtain ⟨X, -, -, -, h4, h5⟩ := step_executed h
  refine ⟨h5, h4, fun ec hec => ?_⟩
  subst hec
  exact (execute_basic h).2.2.2.2.2.2.2.2.2.1

/-! ## The upgrade transaction -/

theorem UpgradeTxInFirstUnexecutedBatch : Properties.UpgradeTxInFirstUnexecutedBatch := by
  intro env s hr
  rcases hashBreakLogged_or_clean (inv_reach hr) with h | ⟨-, c⟩
  · exact Or.inl h
  · exact Or.inr ⟨c.upPending, c.upWaiting, c.upOthers⟩

/-! ## The break logs -/

theorem LoggedHashBreaksAreCollisions : Properties.LoggedHashBreaksAreCollisions := by
  intro env s hr
  have hi := inv_reach hr
  exact ⟨hi.firstBreak, hashBreakLogged_of_ne_nil hi⟩

theorem LoggedMerkleBreaksAreForgeries : Properties.LoggedMerkleBreaksAreForgeries := by
  intro env s hr
  have hi := inv_reach hr
  exact ⟨hi.merkleGenuine, merkleBreakLogged_of_ne_nil hi⟩

end Contracts.ExecutorFacet
