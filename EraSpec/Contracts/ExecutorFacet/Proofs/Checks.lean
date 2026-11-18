import EraSpec.Contracts.ExecutorFacet.Properties.Checks
import EraSpec.Contracts.ExecutorFacet.Proofs.Invariant

/-!
# Proofs: what each check and each break disjunct does, on concrete runs

Each theorem proves the property of the same name in
`EraSpec.Contracts.ExecutorFacet.Properties.Checks`. The runs are evaluated by `decide` and
`rfl`; reachability comes from `reach_runCalls` (`Proofs/Invariant.lean`).
-/

namespace Contracts.ExecutorFacet

/-- Every `wInitOf env` is an initialized chain. -/
theorem wInitOf_init (env : Env) : Init env (wInitOf env) where
  executed0 := rfl
  verified0 := rfl
  committed0 := rfl
  genesisHash := rfl
  genesisNumber := rfl
  noUpgradeTx := rfl
  noUpgradeBatch := rfl
  unprocessed0 := rfl
  leaves0 := rfl
  roots0 := fun _ h => of_decide_eq_true h
  executedLog0 := rfl
  verifiedLog0 := rfl
  hashBreaks0 := rfl
  merkleBreaks0 := rfl

/-- `ProvedAt` with the position solved for, which `decide` can evaluate. -/
theorem provedAt_iff {s : State} {n : Nat} {b : StoredBatchInfo} :
    ProvedAt s n b ↔
      ∃ call ∈ s.verified, call.first ≤ n ∧ call.batches[n - call.first]? = some b := by
  constructor
  · rintro ⟨call, hmem, j, hj, hb⟩
    exact ⟨call, hmem, by omega, by rw [show n - call.first = j by omega]; exact hb⟩
  · rintro ⟨call, hmem, hle, hb⟩
    exact ⟨call, hmem, n - call.first, by omega, hb⟩

/-! ## Each check is load-bearing -/

theorem WithoutCommittedCheckProofsOutrunCommits :
    Properties.WithoutCommittedCheckProofsOutrunCommits :=
  ⟨wInitOf_init wEnv, by decide, rfl, _, rfl, by decide⟩

theorem WithoutProvenCheckExecutionOutrunsProofs :
    Properties.WithoutProvenCheckExecutionOutrunsProofs :=
  ⟨by decide, rfl, _, rfl, by decide⟩

theorem WithoutExecutedCheckRevertRewritesAnExecutedBatch :
    Properties.WithoutExecutedCheckRevertRewritesAnExecutedBatch :=
  ⟨by decide, rfl, ⟨_, rfl, by decide⟩, _, rfl, by decide⟩

theorem UpgradeWithoutExecutedCheckSkipsABatch :
    Properties.UpgradeWithoutExecutedCheckSkipsABatch :=
  ⟨by decide, rfl, _, rfl, by decide⟩

/-! ## The break disjuncts are needed -/

theorem CollisionRewritesAnExecutedBatch : Properties.CollisionRewritesAnExecutedBatch := by
  have hinit := wInitOf_init wCollEnv
  refine ⟨hinit, _, _, rfl, rfl, reach_runCalls (cs := wCollRun) (Reach.init hinit) rfl,
    Relation.ReflTransGen.single ⟨wCollCommit, rfl⟩, by decide, by decide, by decide,
    by decide, _, rfl, by unfold HashBreak.Genuine; decide⟩

theorem MerkleBreakConsumesAnUnpushedOp : Properties.MerkleBreakConsumesAnUnpushedOp := by
  have hinit := wInitOf_init wMerkleEnv
  refine ⟨hinit, _, rfl, reach_runCalls (cs := wMerkleRun) (Reach.init hinit) rfl, by decide,
    by decide, by decide,
    by decide, ⟨⟨0, ⟨[], [], [77]⟩, []⟩, by decide, by decide, 0, Nat.zero_le _, rfl⟩,
    by decide⟩

/-! ## The unchecked increment -/

private theorem uncheckedIncN_val (v : UInt256) :
    ∀ k, v.val + k < UInt256.size → (uncheckedIncN v k).val = v.val + k
  | 0, _ => rfl
  | k + 1, h => by
    have ih := uncheckedIncN_val v k (by omega)
    have h1 : (1 : UInt256).val = 1 := rfl
    rw [uncheckedIncN, Fin.val_add, ih, h1, Nat.mod_eq_of_lt (by omega)]
    omega

theorem UncheckedIncExactBelowWrap : Properties.UncheckedIncExactBelowWrap := by
  refine ⟨uncheckedIncN_val, by decide, fun env s s' c h hC => ?_⟩
  obtain ⟨-, -, -, -, hle, -, rfl⟩ := proveWith_some h
  have hle := hle rfl
  have hV : ((s.totalBatchesVerified : UInt256)).val = s.totalBatchesVerified :=
    Nat.mod_eq_of_lt (by omega)
  rw [uncheckedIncN_val _ _ (by rw [hV]; omega), hV]

/-! ## Witnesses -/

/-- A successful run of calls is a `Steps` run. -/
theorem steps_runCalls {env : Env} :
    ∀ {cs : List Call} {s s' : State}, runCalls env s cs = some s' → Steps env s s'
  | [], s, s', h => by
    simp only [runCalls, Option.some.injEq] at h
    subst h
    exact Relation.ReflTransGen.refl
  | c :: cs, s, s', h => by
    simp only [runCalls] at h
    split at h
    · simp at h
    · rename_i s2 h2
      exact Relation.ReflTransGen.head ⟨c, h2⟩ (steps_runCalls h)

theorem PipelineWitness : Properties.PipelineWitness := by
  have hinit := wInitOf_init wEnv
  refine ⟨hinit, ⟨_, rfl, reach_runCalls (cs := wRunA.take 7) (Reach.init hinit) rfl, by decide⟩,
    _, _, rfl, rfl, reach_runCalls (cs := wRunA) (Reach.init hinit) rfl,
    steps_runCalls (cs := wRunB) rfl, ?_⟩
  simp only [provedAt_iff]
  decide

theorem RevertRecommitWitness : Properties.RevertRecommitWitness := by
  have hinit := wInitOf_init wEnv
  refine ⟨_, rfl, reach_runCalls (cs := wRecommitRun) (Reach.init hinit) rfl, ?_⟩
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by rw [provedAt_iff]; decide, by rw [provedAt_iff]; decide, rfl, _, rfl, by decide, ?_⟩
  rw [provedAt_iff]
  decide

theorem PriorityModeWitness : Properties.PriorityModeWitness := by
  have hinit := wInitOf_init wEnv
  refine ⟨_, _, rfl, rfl,
    Reach.step (reach_runCalls (cs := wRunA.take 8) (Reach.init hinit) rfl)
      ⟨.activatePriorityMode, rfl⟩,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    rfl, rfl, rfl, _, rfl, by decide⟩

theorem HonestProgressWitness : Properties.HonestProgressWitness := by
  have hinit := wInitOf_init wEnv
  exact ⟨⟨_, rfl, reach_runCalls (cs := wRunA.take 7) (Reach.init hinit) rfl, by decide⟩,
    _, rfl, reach_runCalls (cs := wRunA.take 8 ++ [.activatePriorityMode]) (Reach.init hinit) rfl,
    by decide⟩

theorem AdminWitness : Properties.AdminWitness := by
  have hinit := wInitOf_init wEnv
  refine ⟨_, rfl, by decide, ⟨_, rfl, by decide, rfl⟩, _, rfl,
    reach_runCalls (cs := wAdminRun) (reach_runCalls (cs := wRun) (Reach.init hinit) rfl) rfl,
    by decide, rfl, _, rfl, by decide⟩

end Contracts.ExecutorFacet
