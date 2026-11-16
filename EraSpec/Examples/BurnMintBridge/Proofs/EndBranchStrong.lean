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
after the deadline `0`).  The two stronger forms of older witnesses reuse those witnesses'
instances too: the committed history for `CheckedExecutionWitnessPinned`, and the halted
history with the honest END submission for `PinnedBridgeRefundWitnessLinked`.

The per-world statements need one invariant of runs from `initial a b`: a recorded transfer
has an amount between `1` and `a` (`run_record_bound`).  A refunded or delivered run from
`initial i.amount 0` therefore has `0 < i.amount`, and preparing `i` itself, then recovering or
executing it, is then a run of any evidence that accepts `i`.

The three gaps that resolve another transfer run a second one-unit transfer, `gapTransfer`,
from the same starting balance.  The branch gap refunds `sampleTransfer` itself, on
`twoRootHistory` with `twoRoots`: its leg has a BEGIN-branch timeout against `laterRoot` and an
END-branch timeout against `earlyRoot`.  Both roots aggregate (`twoRoots_aggregate`), and every
batch inside a root settled by its creation (`twoRoots_physical`).  The single-root gap refunds
`sampleTransfer` itself on `splitHistory` with `demoRoots`, every root of which is
`Contracts.Timeout.demoRoot`, through `twoLegFlow`: `demoLeg` has a BEGIN-branch timeout and
`chainOneLeg` an END-branch timeout against that root.

The two checked-execution gaps run on the halted history, with no prerequisite and with the
zero-valued `zeroLeg`.  The §3 gap refunds `sampleTransfer` on the BEGIN branch on
`splitHistory`, next to the honest END submission `chainOneSubmission`, whose leg is not a
prerequisite of `sampleTransfer`.
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
  have hall : ∀ l ∈ demoFlow sampleTransfer,
      l.commitValue ≠ 0 ∧ OnTime committedHistory l := by
    intro l hl
    rw [mem_demoFlow hl]
    exact ⟨by decide, committed_onTime⟩
  exact ⟨committedHistory, demoFlow, sampleTransfer, _, committedHistory_valid,
    List.cons_ne_nil _ _, hall,
    .tail (.tail .refl (.prepare demo_prepare))
      (.execute (fun l hl => (hall l hl).2) demo_execute),
    rfl, rfl, rfl, rfl⟩

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

/-! ## Per world -/

/-- On a run from `initial a b`: while nothing is recorded the source balance is at most `a`,
and a recorded transfer has a positive amount of at most `a`. -/
theorem run_record_bound {E : Evidence} {a b : ℕ} {s : State} (h : Run E (initial a b) s) :
    (s.record = none → s.sourceBalance ≤ a) ∧
      (∀ j, s.record = some j → 0 < j.amount ∧ j.amount ≤ a) := by
  induction h with
  | refl => exact ⟨fun _ => le_refl _, fun j hj => by simp [initial] at hj⟩
  | tail _ hstep ih =>
    obtain ⟨ih1, ih2⟩ := ih
    cases hstep with
    | prepare hp =>
      obtain ⟨hnone, -, -, hpos, hle, rfl⟩ := hp
      refine ⟨fun h => by simp [burn] at h, fun j hj => ?_⟩
      have hj' : some _ = some j := hj
      obtain rfl := Option.some.inj hj'
      exact ⟨hpos, le_trans hle (ih1 hnone)⟩
    | interfere hi =>
      cases hi with
      | source hn => exact ⟨fun h => le_trans (Nat.sub_le _ _) (ih1 h), ih2⟩
      | destination hn => exact ⟨ih1, ih2⟩
    | execute _ he =>
      obtain ⟨-, -, rfl⟩ := he
      exact ⟨ih1, ih2⟩
    | recover _ hr =>
      obtain ⟨hrecord, -, rfl⟩ := hr
      exact ⟨fun h => absurd (hrecord.symm.trans h) (by simp), ih2⟩

/-- A run from `initial a 0` that ends refunded started with a positive balance. -/
theorem refunded_run_pos {E : Evidence} {a : ℕ} {s : State} (h : Run E (initial a 0) s)
    (hr : s.refunded = true) : 0 < a := by
  obtain ⟨j, hj, -⟩ := (run_authorized (initial_authorized E a 0) h).2 hr
  have := (run_record_bound h).2 j hj
  omega

/-- A run from `initial a 0` that ends delivered started with a positive balance. -/
theorem delivered_run_pos {E : Evidence} {a : ℕ} {s : State} (h : Run E (initial a 0) s)
    (hd : s.delivered = true) : 0 < a := by
  obtain ⟨j, hj, -⟩ := (run_authorized (initial_authorized E a 0) h).1 hd
  have := (run_record_bound h).2 j hj
  omega

theorem own_prepare {i : Transfer} (hpos : 0 < i.amount) :
    Prepare (initial i.amount 0) i (burn (initial i.amount 0) i) :=
  ⟨rfl, rfl, rfl, hpos, le_refl _, rfl⟩

/-- Prepare `i` itself, then recover it. -/
theorem own_refund_run {E : Evidence} {i : Transfer} (hpos : 0 < i.amount) (hr : E.recover i) :
    Run E (initial i.amount 0) (restore (burn (initial i.amount 0) i) i) :=
  .tail (.tail .refl (.prepare (own_prepare hpos))) (.recover hr ⟨rfl, rfl, rfl⟩)

/-- Prepare `i` itself, then execute it. -/
theorem own_execute_run {E : Evidence} {i : Transfer} (hpos : 0 < i.amount)
    (hf : E.finalize i) :
    Run E (initial i.amount 0) (mint (burn (initial i.amount 0) i) i) :=
  .tail (.tail .refl (.prepare (own_prepare hpos))) (.execute hf ⟨⟨rfl, rfl⟩, rfl, rfl⟩)

theorem own_refund_balance (i : Transfer) :
    (restore (burn (initial i.amount 0) i) i).sourceBalance = i.amount := by
  simp [restore, burn, initial]

theorem own_execute_balance (i : Transfer) :
    (mint (burn (initial i.amount 0) i) i).destinationBalance = i.amount := by
  simp [mint, burn, initial]

theorem end_branch_refund_witness_record_pin_free :
    Properties.EndBranchRefundWitnessRecordPinFree := by
  intro H flow i
  constructor
  · rintro ⟨s, hv, hm, hrun, hr, -⟩
    have hpos := refunded_run_pos hrun hr
    have hE : Run (endFormEvidence H flow) (initial i.amount 0)
        (restore (burn (initial i.amount 0) i) i) := own_refund_run hpos hm
    exact ⟨_, hv, hm, hE, endFormEvidence_run_either hE, rfl, rfl, own_refund_balance i⟩
  · rintro ⟨s, hv, hm, -, hrun, -, hr, hb⟩
    exact ⟨s, hv, hm, hrun, hr, hb⟩

theorem onTime_leg_executes_witness_record_pin_free :
    Properties.OnTimeLegExecutesWitnessRecordPinFree := by
  intro H flow i
  constructor
  · rintro ⟨s, hv, hon, hrun, hd, -⟩
    have hpos := delivered_run_pos hrun hd
    exact ⟨_, ⟨hv, hon, own_execute_run (E := evidenceEither H flow) hpos hon, rfl,
      own_execute_balance i⟩, rfl, rfl⟩
  · rintro ⟨s, h, -, -⟩
    exact ⟨s, h⟩

theorem begin_branch_refund_witness_record_pin_free :
    Properties.BeginBranchRefundWitnessRecordPinFree := by
  intro H roots flow i
  constructor
  · rintro ⟨s, hv, hagg, ⟨l, hl, k, hb⟩, hrun, hr, -⟩
    have hpos := refunded_run_pos hrun hr
    exact ⟨_, ⟨hv, hagg, ⟨l, hl, k, hb⟩,
      own_refund_run (E := checkedEvidence H roots flow) hpos ⟨l, hl, k, Or.inl hb⟩, rfl,
      own_refund_balance i⟩,
      own_refund_run (E := beginOnlyEvidence H roots flow) hpos ⟨l, hl, k, hb⟩, rfl⟩
  · rintro ⟨s, h, -, -⟩
    exact ⟨s, h⟩

/-! ## Stronger forms of two older witnesses -/

theorem checked_execution_witness_pinned : Properties.CheckedExecutionWitnessPinned := by
  have hall : (checkedEvidence committedHistory demoRoots demoFlow).finalize sampleTransfer := by
    intro l hl
    rw [mem_demoFlow hl]
    exact committed_onTime
  exact ⟨committedHistory, demoRoots, demoFlow, _, _, sampleTransfer,
    ⟨committedHistory_valid, fun _ => committed_aggregates, demo_prepare, hall, _, hall,
      demo_execute⟩,
    List.cons_ne_nil _ _, fun l hl => by rw [mem_demoFlow hl]; decide⟩

theorem pinned_bridge_refund_witness_linked : Properties.PinnedBridgeRefundWitnessLinked := by
  have ha : EndAcceptedBy haltedHistory demoRoots (fun _ => Contracts.Timeout.demoBacking)
      honestSubmission :=
    ⟨by decide, by decide, Contracts.Timeout.demo_endBranchAccepted.lastBatch, genesis_gap_one⟩
  have hnb : ¬ EndBreak (roots := demoRoots) (fun _ => Contracts.Timeout.demoBacking)
      honestSubmission := by
    rintro (hpb | hpc)
    · rcases hpb with ⟨_, _, hlt, _⟩ | ⟨hlt, _⟩ <;> exact absurd hlt (by decide)
    · exact MerkleSpec.Verifier.honest_walk_no_collision MerkleSpec.LastLeaf.demoHash 0
        [5, 7] 2 1 hpc
  refine ⟨MerkleSpec.LastLeaf.demoHash, 0, haltedHistory, demoRoots,
    fun _ => Contracts.Timeout.demoBacking, demoFlow, fun _ => honestSubmission, sampleTransfer, _,
    ⟨haltedHistory_valid, fun _ => halted_aggregates,
      demo_refund_run (Or.inr ⟨List.mem_singleton_self _, ha⟩), rfl, rfl, ha, hnb,
      MerkleSpec.LastLeaf.demo_collides⟩, List.mem_singleton_self _, ?_⟩
  intro l hl k
  rw [mem_demoFlow hl]
  exact no_begin_demoRoot (fun _ _ => rfl) rfl

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

/-! ### Two imported roots for the branch gap -/

theorem twoRootTime_monotone : Monotone twoRootTime := by
  intro a b hab
  unfold twoRootTime
  by_cases ha0 : a = 0
  · subst ha0
    by_cases hb0 : b = 0
    · simp [hb0]
    · by_cases hb1 : b = 1
      · simp [hb1]
      · simp [hb0, hb1]
  · by_cases ha1 : a = 1
    · subst ha1
      by_cases hb1 : b = 1
      · simp [hb1]
      · have hb0 : b ≠ 0 := by omega
        simp [hb0, hb1]
    · have hb0 : b ≠ 0 := by omega
      have hb1 : b ≠ 1 := by omega
      simp [ha0, ha1, hb0, hb1]

theorem twoRootHistory_valid : twoRootHistory.Valid where
  guarded := fun _ _ => Or.inl rfl
  genesis := fun _ => rfl
  monotone_time := fun _ => twoRootTime_monotone

theorem earlyRoot_aggregates : RootAggregates twoRootHistory earlyRoot := by
  intro c n hn
  show n ≤ 0
  by_contra hc
  have hn0 : n ≠ 0 := by omega
  by_cases hn1 : n = 1
  · subst hn1
    have h2 : twoRootHistory.settledAt c 1 = 2 := rfl
    rw [h2] at hn
    exact absurd hn (by decide)
  · have h5 : twoRootHistory.settledAt c n = 5 := by
      show twoRootTime n = 5
      simp [twoRootTime, hn0, hn1]
    rw [h5] at hn
    exact absurd hn (by decide)

theorem laterRoot_aggregates : RootAggregates twoRootHistory laterRoot := by
  intro c n hn
  show n ≤ 1
  by_contra hc
  have hn0 : n ≠ 0 := by omega
  have hn1 : n ≠ 1 := by omega
  have h5 : twoRootHistory.settledAt c n = 5 := by
    show twoRootTime n = 5
    simp [twoRootTime, hn0, hn1]
  rw [h5] at hn
  exact absurd hn (by decide)

theorem twoRoots_aggregate : ∀ k, RootAggregates twoRootHistory (twoRoots k) := by
  intro k
  by_cases hk : k = 0
  · simpa [twoRoots, hk] using earlyRoot_aggregates
  · simpa [twoRoots, hk] using laterRoot_aggregates

/-- Every batch inside either root settled by that root's creation. -/
theorem twoRoots_physical : ∀ k c n, n ≤ (twoRoots k).upTo c →
    (twoRootHistory.settledAt c n).val ≤ (twoRoots k).created := by
  intro k c n hn
  by_cases hk : k = 0
  · have hn0 : n = 0 := by simpa [twoRoots, hk, earlyRoot] using hn
    subst hn0
    simp [twoRoots, hk, earlyRoot, twoRootHistory, twoRootTime]
  · have hn1 : n ≤ 1 := by simpa [twoRoots, hk, laterRoot] using hn
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn1 with rfl | rfl
    · simp [twoRoots, hk, laterRoot, twoRootHistory, twoRootTime]
    · simp [twoRoots, hk, laterRoot, twoRootHistory, twoRootTime]

/-- Against one root, on a valid history, a BEGIN-branch timeout excludes an END-branch timeout
for the same leg: the root's last batch is no earlier than the late batch inside it. -/
theorem beginVia_not_endVia {H : History} (hH : H.Valid) {R : Contracts.Timeout.SlRoot}
    {l : Leg} (hb : BeginVia H R l) : ¬ EndVia H R l := by
  intro he
  obtain ⟨-, hon, -⟩ := endVia_iff_endLastVia.mp he
  obtain ⟨-, L, hL, hlate, -⟩ := hb
  have hmono := hH.monotone_time l.sourceChain hL
  exact absurd (lt_of_lt_of_le hlate (le_trans hmono hon)) (lt_irrefl _)

/-- Batch `1` settled at time `2`, after the deadline `0`, inside `laterRoot`. -/
theorem twoRoots_beginVia : BeginVia twoRootHistory (twoRoots 1) demoLeg := by
  show BeginVia twoRootHistory laterRoot demoLeg
  exact ⟨by decide, 1, le_refl 1, by decide, genesis_gap_one⟩

/-- `earlyRoot`'s last batch, `0`, settled at time `0`, by the deadline. -/
theorem twoRoots_endVia : EndVia twoRootHistory (twoRoots 0) demoLeg := by
  show EndVia twoRootHistory earlyRoot demoLeg
  exact endVia_iff_endLastVia.mpr ⟨by decide, by decide, genesis_gap_one⟩

theorem begin_branch_refund_witness_branch_gap :
    Properties.BeginBranchRefundWitnessBranchGap :=
  ⟨twoRootHistory, twoRoots, demoFlow, sampleTransfer, _,
    ⟨twoRootHistory_valid, twoRoots_aggregate,
      ⟨demoLeg, List.mem_singleton_self _, 1, twoRoots_beginVia⟩,
      demo_refund_run ⟨demoLeg, List.mem_singleton_self _, 1, Or.inl twoRoots_beginVia⟩,
      rfl, rfl⟩,
    demo_refund_run ⟨demoLeg, List.mem_singleton_self _, 1, twoRoots_beginVia⟩, rfl,
    demoLeg, List.mem_singleton_self _, ⟨1, twoRoots_beginVia⟩, 0, twoRoots_endVia⟩

/-! ### One imported root, a second leg -/

theorem chainOneLeg_ne_demoLeg : chainOneLeg ≠ demoLeg := fun h =>
  absurd (congrArg Leg.sourceChain h) (by decide)

theorem begin_branch_refund_witness_single_root_gap :
    Properties.BeginBranchRefundWitnessSingleRootGap := by
  have hb : BeginVia splitHistory (demoRoots 0) demoLeg := split_beginVia
  have he : EndVia splitHistory (demoRoots 0) chainOneLeg := split_endVia
  have hmem0 : demoLeg ∈ twoLegFlow sampleTransfer := by simp [twoLegFlow]
  have hmem1 : chainOneLeg ∈ twoLegFlow sampleTransfer := by simp [twoLegFlow]
  exact ⟨splitHistory, demoRoots, twoLegFlow, sampleTransfer, _,
    ⟨splitHistory_valid, fun _ => split_aggregates, ⟨demoLeg, hmem0, 0, hb⟩,
      demo_refund_run ⟨demoLeg, hmem0, 0, Or.inl hb⟩, rfl, rfl⟩,
    fun _ => rfl, demo_refund_run ⟨demoLeg, hmem0, 0, hb⟩, rfl,
    demoLeg, hmem0, chainOneLeg, hmem1, chainOneLeg_ne_demoLeg, hb, he⟩

/-! ### The gaps of two older witnesses -/

theorem checked_execution_witness_gap : Properties.CheckedExecutionWitnessGap := by
  have hnone : (checkedEvidence haltedHistory demoRoots (fun _ => [])).finalize
      sampleTransfer := by
    intro l hl
    simp at hl
  refine ⟨haltedHistory, demoRoots, fun _ => [], _, _, sampleTransfer,
    ⟨haltedHistory_valid, fun _ => halted_aggregates, demo_prepare, hnone, _, hnone,
      demo_execute⟩, rfl, ?_⟩
  rintro l hv ⟨n, -, hmem⟩
  exact halted_never_on_time hv n hmem

/-- The sentinel `0` is in the halted chain's genesis snapshot, settled at time `0`. -/
theorem zeroLeg_onTime : OnTime haltedHistory zeroLeg :=
  ⟨0, le_refl _, Finset.mem_image.mpr ⟨⟨0, 0⟩, Finset.mem_singleton_self _, rfl⟩⟩

theorem checked_execution_witness_zero_value_gap :
    Properties.CheckedExecutionWitnessZeroValueGap := by
  have hfin : (checkedEvidence haltedHistory demoRoots (fun _ => [zeroLeg])).finalize
      sampleTransfer := by
    intro l hl
    rw [List.mem_singleton.mp hl]
    exact zeroLeg_onTime
  refine ⟨haltedHistory, demoRoots, fun _ => [zeroLeg], _, _, sampleTransfer,
    ⟨haltedHistory_valid, fun _ => halted_aggregates, demo_prepare, hfin, _, hfin,
      demo_execute⟩, List.cons_ne_nil _ _, ?_, ?_⟩
  · intro l hl
    rw [List.mem_singleton.mp hl]
    rfl
  · rintro l hv ⟨n, -, hmem⟩
    exact halted_never_on_time hv n hmem

/-- `chainOneSubmission`'s path passes `_verifyLastBatchInRoot` (`LastBatchAccepted`, batch 1)
against the tree of chain `chainOneLeg.sourceChain` in `demoBacking`.  The fields are those of
`Contracts.Timeout.demo_endBranchAccepted`, stated for chain 0: every chain's tree in
`demoBacking` is `[5, 7]` at height 2. -/
theorem chainOne_lastBatch :
    Contracts.Timeout.LastBatchAccepted Contracts.Timeout.demoBacking chainOneLeg.sourceChain 1
      chainOneSubmission.sibs chainOneSubmission.leaf :=
  ⟨Contracts.Timeout.demo_endBranchAccepted.lastBatch.inRange,
    Contracts.Timeout.demo_endBranchAccepted.lastBatch.authenticated,
    Contracts.Timeout.demo_endBranchAccepted.lastBatch.zeroRightSiblings⟩

theorem pinned_bridge_refund_witness_gap : Properties.PinnedBridgeRefundWitnessGap := by
  have ha : EndAcceptedBy splitHistory demoRoots (fun _ => Contracts.Timeout.demoBacking)
      chainOneSubmission :=
    ⟨by decide, by decide, chainOne_lastBatch, genesis_gap_one⟩
  have hnb : ¬ EndBreak (roots := demoRoots) (fun _ => Contracts.Timeout.demoBacking)
      chainOneSubmission := by
    rintro (hpb | hpc)
    · rcases hpb with ⟨_, _, hlt, _⟩ | ⟨hlt, _⟩ <;> exact absurd hlt (by decide)
    · exact MerkleSpec.Verifier.honest_walk_no_collision MerkleSpec.LastLeaf.demoHash 0
        [5, 7] 2 1 hpc
  refine ⟨MerkleSpec.LastLeaf.demoHash, 0, splitHistory, demoRoots,
    fun _ => Contracts.Timeout.demoBacking, demoFlow, fun _ => chainOneSubmission,
    sampleTransfer, _,
    ⟨splitHistory_valid, fun _ => split_aggregates,
      demo_refund_run (Or.inl ⟨demoLeg, List.mem_singleton_self _, 0, split_beginVia⟩),
      rfl, rfl, ha, hnb, MerkleSpec.LastLeaf.demo_collides⟩,
    ?_, ⟨demoLeg, List.mem_singleton_self _, 0, split_beginVia⟩, ?_⟩
  · intro hmem
    exact chainOneLeg_ne_demoLeg (mem_demoFlow hmem)
  · intro l hl k
    rw [mem_demoFlow hl]
    exact beginVia_not_endVia splitHistory_valid split_beginVia

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

theorem EndBranchRefundWitnessRecordPinFree : Properties.EndBranchRefundWitnessRecordPinFree :=
  end_branch_refund_witness_record_pin_free
theorem OnTimeLegExecutesWitnessRecordPinFree :
    Properties.OnTimeLegExecutesWitnessRecordPinFree :=
  onTime_leg_executes_witness_record_pin_free
theorem BeginBranchRefundWitnessRecordPinFree :
    Properties.BeginBranchRefundWitnessRecordPinFree :=
  begin_branch_refund_witness_record_pin_free

theorem CheckedExecutionWitnessPinned : Properties.CheckedExecutionWitnessPinned :=
  checked_execution_witness_pinned
theorem PinnedBridgeRefundWitnessLinked : Properties.PinnedBridgeRefundWitnessLinked :=
  pinned_bridge_refund_witness_linked

theorem EndBranchRefundWitnessGap : Properties.EndBranchRefundWitnessGap :=
  end_branch_refund_witness_gap
theorem OnTimeLegExecutesWitnessGap : Properties.OnTimeLegExecutesWitnessGap :=
  onTime_leg_executes_witness_gap
theorem BeginBranchRefundWitnessGap : Properties.BeginBranchRefundWitnessGap :=
  begin_branch_refund_witness_gap
theorem BeginBranchRefundWitnessBranchGap : Properties.BeginBranchRefundWitnessBranchGap :=
  begin_branch_refund_witness_branch_gap
theorem BeginBranchRefundWitnessSingleRootGap :
    Properties.BeginBranchRefundWitnessSingleRootGap :=
  begin_branch_refund_witness_single_root_gap
theorem CheckedExecutionWitnessGap : Properties.CheckedExecutionWitnessGap :=
  checked_execution_witness_gap
theorem CheckedExecutionWitnessZeroValueGap : Properties.CheckedExecutionWitnessZeroValueGap :=
  checked_execution_witness_zero_value_gap
theorem PinnedBridgeRefundWitnessGap : Properties.PinnedBridgeRefundWitnessGap :=
  pinned_bridge_refund_witness_gap

end Applications.BurnMintBridge.EndBranch
