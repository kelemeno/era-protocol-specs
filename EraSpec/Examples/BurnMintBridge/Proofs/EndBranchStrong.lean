import EraSpec.Examples.BurnMintBridge.Properties.EndBranchStrong
import EraSpec.Examples.BurnMintBridge.Proofs.EndBranch

/-!
# Proofs: the END-branch witnesses, pinned to the transfer and the branch

The pinned witnesses reuse the instances of `Proofs/EndBranch.lean` unchanged: the halted
history for the END form, the committed history for execution and the late history for the
BEGIN branch, all on `demoFlow` and `sampleTransfer`.  Those instances already resolve
`sampleTransfer` itself on the intended branch.  The added work is to say so: the record, the
single-branch evidence the same run satisfies, and, for the BEGIN branch, that the late
history's root has no END-branch timeout for the leg (its last batch, `1`, settled at time `1`,
after the deadline `0`).

The gaps run a second one-unit transfer, `gapTransfer`, from the same starting balance.
-/

namespace Applications.BurnMintBridge.EndBranch

open IMTAbstract Properties.PreparedBridge

/-! ## Pinned witnesses -/

/-- Every run of `endFormEvidence` is a run of `evidenceEither`. -/
theorem endFormEvidence_run_either {H : History} {flow : Transfer → List Leg} {s t : State}
    (h : Run (endFormEvidence H flow) s t) : Run (evidenceEither H flow) s t := by
  refine run_monotone (E := endFormEvidence H flow) (E' := evidenceEither H flow)
    (fun _ hf => hf) ?_ h
  rintro i ⟨l, hl, hm⟩
  exact ⟨l, hl, Or.inr hm⟩

/-- The halted chain's END-form timeout: batch `1` in time, every later batch at time `2`. -/
theorem halted_missingEnd : MissingEnd haltedHistory demoLeg := by
  refine ⟨1, 1, by decide, by decide, ?_, genesis_gap_one⟩
  intro n hn
  show (1 : UInt256) ≤ demoTime n
  rw [demoTime_gt hn]
  decide

theorem end_branch_refund_witness_pinned : Properties.EndBranchRefundWitnessPinned := by
  have hrun : Run (endFormEvidence haltedHistory demoFlow) (initial 1 0)
      (restore (burn (initial 1 0) sampleTransfer) sampleTransfer) :=
    demo_refund_run ⟨demoLeg, List.mem_singleton_self _, halted_missingEnd⟩
  exact ⟨haltedHistory, demoFlow, sampleTransfer, _, haltedHistory_valid,
    ⟨demoLeg, List.mem_singleton_self _, halted_missingEnd⟩, hrun,
    endFormEvidence_run_either hrun, rfl, rfl, rfl⟩

theorem onTime_leg_executes_witness_pinned : Properties.OnTimeLegExecutesWitnessPinned := by
  have hall : ∀ l ∈ demoFlow sampleTransfer, OnTime committedHistory l := by
    intro l hl
    rw [mem_demoFlow hl]
    exact committed_onTime
  exact ⟨committedHistory, demoFlow, sampleTransfer, _, committedHistory_valid,
    List.cons_ne_nil _ _, hall,
    .tail (.tail .refl (.prepare demo_prepare)) (.execute hall demo_execute), rfl, rfl, rfl, rfl⟩

/-- The late history's root has no END-branch timeout for the demo leg: the root's last batch,
`1`, settled at time `1`, after the deadline `0`. -/
theorem late_no_endVia (k : ℕ) : ¬ EndVia lateHistory (demoRoots k) demoLeg := by
  intro h
  obtain ⟨-, hon, -⟩ := endVia_iff_endLastVia.mp h
  have hlate : ¬ lateHistory.settledAt demoLeg.sourceChain 1 ≤ demoLeg.deadline := by decide
  exact hlate hon

theorem begin_branch_refund_witness_pinned : Properties.BeginBranchRefundWitnessPinned := by
  refine ⟨lateHistory, demoRoots, demoFlow, sampleTransfer, _, lateHistory_valid,
    fun _ => late_aggregates, ⟨demoLeg, List.mem_singleton_self _, 0, late_beginVia⟩, ?_,
    demo_refund_run ⟨demoLeg, List.mem_singleton_self _, 0, late_beginVia⟩,
    demo_refund_run ⟨demoLeg, List.mem_singleton_self _, 0, Or.inl late_beginVia⟩,
    rfl, rfl, rfl⟩
  intro l hl k
  rw [mem_demoFlow hl]
  exact late_no_endVia k

/-! ## The gaps -/

theorem gapTransfer_ne_sample : gapTransfer ≠ sampleTransfer := by decide

theorem gap_prepare : Prepare (initial 1 0) gapTransfer (burn (initial 1 0) gapTransfer) := by
  simp [Prepare, initial, gapTransfer, burn]

theorem gap_execute : Execute (burn (initial 1 0) gapTransfer) gapTransfer gapTransfer
    (mint (burn (initial 1 0) gapTransfer) gapTransfer) := by
  simp [Execute, Ready, burn, initial]

theorem gap_recover : Recover (burn (initial 1 0) gapTransfer) gapTransfer
    (restore (burn (initial 1 0) gapTransfer) gapTransfer) := by
  simp [Recover, burn, initial]

/-- Prepare `gapTransfer`, then recover it. -/
theorem gap_refund_run {E : Evidence} (hr : E.recover gapTransfer) :
    Run E (initial 1 0) (restore (burn (initial 1 0) gapTransfer) gapTransfer) :=
  .tail (.tail .refl (.prepare gap_prepare)) (.recover hr gap_recover)

/-- Prepare `gapTransfer`, then execute it. -/
theorem gap_execute_run {E : Evidence} (hf : E.finalize gapTransfer) :
    Run E (initial 1 0) (mint (burn (initial 1 0) gapTransfer) gapTransfer) :=
  .tail (.tail .refl (.prepare gap_prepare)) (.execute hf gap_execute)

theorem end_branch_refund_witness_gap : Properties.EndBranchRefundWitnessGap :=
  ⟨haltedHistory, demoFlow, sampleTransfer, _,
    ⟨haltedHistory_valid, ⟨demoLeg, List.mem_singleton_self _, halted_missingEnd⟩,
      gap_refund_run ⟨demoLeg, List.mem_singleton_self _, Or.inr halted_missingEnd⟩, rfl, rfl⟩,
    by decide⟩

theorem onTime_leg_executes_witness_gap : Properties.OnTimeLegExecutesWitnessGap := by
  have hnone : ∀ l ∈ ([] : List Leg), OnTime haltedHistory l := by
    intro l hl
    simp at hl
  refine ⟨haltedHistory, fun _ => [], sampleTransfer, _,
    ⟨haltedHistory_valid, hnone, gap_execute_run hnone, rfl, rfl⟩, rfl, by decide, ?_⟩
  rintro l hv ⟨n, -, hmem⟩
  exact halted_never_on_time hv n hmem

/-! ### The two-chain world for the BEGIN gap -/

theorem splitHistory_valid : splitHistory.Valid where
  guarded := fun _ _ => Or.inl rfl
  genesis := fun _ => rfl
  monotone_time := by
    intro c
    by_cases hc : c = 0
    · simpa [splitHistory, hc] using lateTime_monotone
    · simpa [splitHistory, hc] using demoTime_monotone

theorem split_aggregates : RootAggregates splitHistory Contracts.Timeout.demoRoot := by
  intro c n hn
  by_cases hc : c = 0
  · subst hc
    exact late_aggregates 0 n hn
  · have ht : splitHistory.settledAt c n = demoTime n := by simp [splitHistory, hc]
    rw [ht] at hn
    exact demoTime_aggregates (H := haltedHistory) (fun _ _ => rfl) c n hn

/-- Chain `0` settles batch `1` late, inside the root: the demo leg's BEGIN-branch timeout. -/
theorem split_beginVia : BeginVia splitHistory Contracts.Timeout.demoRoot demoLeg :=
  ⟨by decide, 1, le_refl 1, by decide, genesis_gap_one⟩

/-- Chain `1`'s last batch in the root, `1`, is in time: `chainOneLeg`'s END-branch timeout. -/
theorem split_endVia : EndVia splitHistory Contracts.Timeout.demoRoot chainOneLeg :=
  endVia_iff_endLastVia.mpr ⟨by decide, by decide, genesis_gap_one⟩

/-- Chain `1` settles every batch inside the root in time: no BEGIN-branch timeout for
`chainOneLeg`. -/
theorem split_no_beginVia : ¬ BeginVia splitHistory Contracts.Timeout.demoRoot chainOneLeg := by
  rintro ⟨-, L, hL, hlate, -⟩
  have hL1 : L ≤ 1 := hL
  have hc : chainOneLeg.sourceChain ≠ 0 := by decide
  have ht : splitHistory.settledAt chainOneLeg.sourceChain L = 0 := by
    simp only [splitHistory, hc, ite_false]
    exact demoTime_le hL1
  rw [ht] at hlate
  exact absurd hlate (by decide)

theorem splitFlow_sample : splitFlow sampleTransfer = [demoLeg] := by
  simp [splitFlow]

theorem splitFlow_gap : splitFlow gapTransfer = [chainOneLeg] := by
  simp [splitFlow, gapTransfer_ne_sample]

theorem begin_branch_refund_witness_gap : Properties.BeginBranchRefundWitnessGap := by
  have hrec : (checkedEvidence splitHistory demoRoots splitFlow).recover gapTransfer :=
    ⟨chainOneLeg, by simp [splitFlow_gap], 0, Or.inr split_endVia⟩
  refine ⟨splitHistory, demoRoots, splitFlow, sampleTransfer, _,
    ⟨splitHistory_valid, fun _ => split_aggregates,
      ⟨demoLeg, by simp [splitFlow_sample], 0, split_beginVia⟩, gap_refund_run hrec, rfl, rfl⟩,
    by decide, ?_⟩
  intro j hj l hl k
  have hj' : some gapTransfer = some j := hj
  obtain rfl := Option.some.inj hj'
  rw [splitFlow_gap, List.mem_singleton] at hl
  subst hl
  exact split_no_beginVia

end Applications.BurnMintBridge.EndBranch

/-! ## Certificates -/

namespace Applications.BurnMintBridge.EndBranch

theorem EndBranchRefundWitnessPinned : Properties.EndBranchRefundWitnessPinned :=
  end_branch_refund_witness_pinned
theorem OnTimeLegExecutesWitnessPinned : Properties.OnTimeLegExecutesWitnessPinned :=
  onTime_leg_executes_witness_pinned
theorem BeginBranchRefundWitnessPinned : Properties.BeginBranchRefundWitnessPinned :=
  begin_branch_refund_witness_pinned
theorem ReachableResolutionAuthorizedByRecord :
    Properties.ReachableResolutionAuthorizedByRecord :=
  fun E source destination _ h => run_authorized (initial_authorized E source destination) h

theorem EndBranchRefundWitnessGap : Properties.EndBranchRefundWitnessGap :=
  end_branch_refund_witness_gap
theorem OnTimeLegExecutesWitnessGap : Properties.OnTimeLegExecutesWitnessGap :=
  onTime_leg_executes_witness_gap
theorem BeginBranchRefundWitnessGap : Properties.BeginBranchRefundWitnessGap :=
  begin_branch_refund_witness_gap

end Applications.BurnMintBridge.EndBranch
