import EraSpec.Protocol.InteropAtomicity.Properties.RefundFaithful
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund

/-!
# Proofs: one outcome per obligation, with `authorizeRefund` as deployed

Certificates for `EraSpec.Protocol.InteropAtomicity.Properties.RefundFaithful`.

The structure is `Contracts.Refund.executed_freezes_flow_or_break`'s: an induction finds the
logged iteration that wrote a refunded obligation (`deployed_refund_logged`), and
`_checkFlowId` makes that iteration's flow the executed one or a pinned clash.  What changes
is the last step.  The iteration's timeout evidence is the contract's, so before
`Atomicity.executed_excludes_any_refund_or_break` applies, the END branch has to be turned
into `IsLastOnTime`, which needs the root to aggregate the missing leg's chain
(`isLastOnTime_of_chain_aggregates`) and the last-batch path to carry no collision
(`Timeout.endBranch_of_accepted_pinned`).  Each failure is a case of `DeployedRefundBreak`.
-/

namespace Contracts.RefundFaithful

open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree
open Contracts.Atomicity Contracts.Timeout Contracts.AtomicFlowManager Contracts.Refund

/-! ## The deployed run's bookkeeping -/

/-- **A REFUNDED OBLIGATION WAS WRITTEN BY A LOGGED, VERIFIED ITERATION.** -/
theorem deployed_refund_logged {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {ze : UInt256} {Ms : Managers} {plog : List Obligation}
    {alog : List (DeployedAuthCall h ze)}
    (hr : DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog) :
    ∀ (o : Obligation), Refunded Ms o → ∃ a ∈ alog, a.Verified h z0 hl cv fh S ∧ a.marks = o := by
  induction hr with
  | refl =>
    intro o hrf
    exfalso
    simp only [Refunded, stateOf_emptyManagers] at hrf
    simp [rank] at hrf
  | @append Ns plog alog c f b _ _ ih =>
    intro o hrf
    by_cases heq : o = ⟨f, b, c⟩
    · exfalso
      subst heq
      simp only [Refunded, stateOf_setAt_self] at hrf
      simp [rank] at hrf
    · exact ih o (by simpa only [Refunded, stateOf_setAt_other heq] using hrf)
  | @authorize Ns plog alog a _ hv _ ih =>
    intro o hrf
    by_cases heq : o = ⟨a.flow.flowId, a.bundle, a.chain⟩
    · exact ⟨a, List.mem_cons_self, hv, heq.symm⟩
    · obtain ⟨a', ha', hv', hm⟩ :=
        ih o (by simpa only [Refunded, stateOf_setAt_other heq] using hrf)
      exact ⟨a', List.mem_cons_of_mem _ ha', hv', hm⟩
  | @claim Ns plog alog c f b _ hg ih =>
    intro o hrf
    by_cases heq : o = ⟨f, b, c⟩
    · subst heq
      refine ih _ ?_
      simp only [Refunded, stateOf]
      rw [show (Ns c).legState f b = LegState.Revertable from hg]
      simp [rank]
    · exact ih o (by simpa only [Refunded, stateOf_setAt_other heq] using hrf)

/-- The run's bookkeeping: a slot is past `Unset` exactly when its obligation was appended,
nothing is appended twice, and every logged iteration wrote an appended obligation. -/
theorem deployed_run_bookkeeping {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {ze : UInt256} {Ms : Managers} {plog : List Obligation}
    {alog : List (DeployedAuthCall h ze)}
    (hr : DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog) :
    (∀ o, stateOf Ms o ≠ .Unset ↔ o ∈ plog) ∧ plog.Nodup ∧ (∀ a ∈ alog, a.marks ∈ plog) := by
  induction hr with
  | refl =>
    refine ⟨fun o => ?_, List.nodup_nil, fun a ha => absurd ha List.not_mem_nil⟩
    simp
  | @append Ns plog alog c f b _ hg ih =>
    obtain ⟨hI, hN, hA⟩ := ih
    have hnot : (⟨f, b, c⟩ : Obligation) ∉ plog := fun hm => (hI ⟨f, b, c⟩).mpr hm hg
    refine ⟨fun o => ?_, List.nodup_cons.mpr ⟨hnot, hN⟩,
      fun a ha => List.mem_cons_of_mem _ (hA a ha)⟩
    by_cases heq : o = ⟨f, b, c⟩
    · subst heq
      rw [stateOf_setAt_self]
      exact ⟨fun _ => List.mem_cons_self, fun _ => by decide⟩
    · rw [stateOf_setAt_other heq, hI o]
      constructor
      · exact fun hm => List.mem_cons_of_mem _ hm
      · intro hm
        rcases List.mem_cons.mp hm with he | hm
        · exact absurd he heq
        · exact hm
  | @authorize Ns plog alog a _ _ hg ih =>
    obtain ⟨hI, hN, hA⟩ := ih
    have hin : a.marks ∈ plog := by
      apply (hI a.marks).mp
      show (Ns a.chain).legState a.flow.flowId a.bundle ≠ .Unset
      rw [hg]; decide
    refine ⟨fun o => ?_, hN, fun a' ha' => ?_⟩
    · by_cases heq : o = ⟨a.flow.flowId, a.bundle, a.chain⟩
      · subst heq
        rw [stateOf_setAt_self]
        exact ⟨fun _ => hin, fun _ => by decide⟩
      · rw [stateOf_setAt_other heq]
        exact hI o
    · rcases List.mem_cons.mp ha' with rfl | ha'
      · exact hin
      · exact hA a' ha'
  | @claim Ns plog alog c f b _ hg ih =>
    obtain ⟨hI, hN, hA⟩ := ih
    refine ⟨fun o => ?_, hN, hA⟩
    by_cases heq : o = ⟨f, b, c⟩
    · subst heq
      rw [stateOf_setAt_self]
      have hin : (⟨f, b, c⟩ : Obligation) ∈ plog := by
        apply (hI _).mp
        show (Ns c).legState f b ≠ .Unset
        rw [hg]; decide
      exact ⟨fun _ => hin, fun _ => by decide⟩
    · rw [stateOf_setAt_other heq]
      exact hI o

theorem deployed_run_appends_once {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {ze : UInt256} {Ms : Managers} {plog : List Obligation}
    {alog : List (DeployedAuthCall h ze)}
    (hr : DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog) :
    plog.Nodup ∧ (∀ a ∈ alog, a.marks ∈ plog)
      ∧ ∀ (o : Obligation), Refunded Ms o → plog.count o = 1 := by
  obtain ⟨hI, hN, hA⟩ := deployed_run_bookkeeping hr
  refine ⟨hN, hA, fun o hrf => ?_⟩
  have hne : stateOf Ms o ≠ .Unset := by
    intro hu
    simp only [Refunded, hu] at hrf
    simp [rank] at hrf
  exact List.count_eq_one_of_mem hN ((hI o).mp hne)

/-! ## From the END branch as run to `IsLastOnTime` -/

/-- **`Timeout.isLastOnTime_of_verified` WITH ONLY THE ONE CHAIN'S AGGREGATION.**  The END
branch's argument uses `Aggregates` only for the chain whose batch is proven. -/
lemma isLastOnTime_of_chain_aggregates {S : System} {R : SlRoot} {c : Chain} {D N : ℕ}
    (hagg : ∀ m, S.time c m ≤ R.created → m ≤ R.upTo c) (he : EndBranchVerified S R c D N) :
    IsLastOnTime S c D N := by
  refine ⟨he.onTime, ?_⟩
  intro m hm
  by_contra hcon
  have hle : S.time c m ≤ D := not_lt.mp hcon
  have hin : m ≤ R.upTo c := hagg m (le_trans hle (le_of_lt he.rootAfterDeadline))
  rw [← he.lastInRoot] at hin
  omega

lemma chain_aggregates_of_not_stale {S : System} {R : SlRoot} {c : Chain}
    (hst : ¬ StaleRootFor S R c) : ∀ m, S.time c m ≤ R.created → m ≤ R.upTo c :=
  fun m hm => not_lt.mp (fun hlt => hst ⟨m, hm, hlt⟩)

lemma not_stale_of_aggregates {S : System} {R : SlRoot} (hagg : Aggregates S R) (c : Chain) :
    ¬ StaleRootFor S R c :=
  fun ⟨m, hm, hlt⟩ => absurd (hagg c m hm) (not_le.mpr hlt)

/-! ## The milestone -/

/-- **AN EXECUTED FLOW IS FROZEN ON EVERY CHAIN, OR A LOCATED BREAK.** -/
theorem deployed_executed_flow_frozen_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {ze : UInt256} {F : Flow}
    {ev : GateEvidence} {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg)
    {Ms : Managers} {plog : List Obligation} {alog : List (DeployedAuthCall h ze)}
    (hr : DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog)
    (o : Obligation) (ho : o.flowId = F.flowId) :
    ¬ Refunded Ms o ∨ DeployedRefundBreak h z0 hl fh S ze F ev o alog := by
  by_cases hrf : Refunded Ms o
  · refine Or.inr ?_
    obtain ⟨a, ha, ⟨hchk', _, hmiss, hacc⟩, hmarks⟩ := deployed_refund_logged hr o hrf
    have hid : F.flowId = a.flow.flowId := by
      rw [← ho, ← hmarks]; rfl
    rcases flowId_check_pins_legList_or_collision hex.2.1 hchk' hid with heq | hcl
    · have hmiss' : a.missing ∈ F.legs := by rw [heq]; exact hmiss
      have hacc' : LegRefundableAcceptedBy h z0 hl cv S a.backing F a.missing a.batch a.proof
          a.pathSibs a.pathLeaf := by rw [heq]; exact hacc
      -- the old gate's form of the evidence, where the contract's checks give it
      have hold : LegRefundableBy h z0 hl cv S F a.missing a.batch a.proof →
          DeployedRefundBreak h z0 hl fh S ze F ev o alog := by
        intro hr'
        rcases executed_excludes_any_refund_or_break hS hex a.missing hmiss' a.batch a.proof
          with hn | hbi | hba
        · exact absurd hr' hn
        · exact DeployedRefundBreak.inclusion a ha hmarks heq.symm hbi
        · exact DeployedRefundBreak.absence a ha hmarks heq.symm hba
      rcases hacc' with ⟨hb, habs⟩ | ⟨he, habs⟩
      · exact hold (Or.inl ⟨hb.late, habs⟩)
      · by_cases hst : StaleRootFor S a.root a.missing.chain
        · exact DeployedRefundBreak.staleRoot a ha hmarks heq.symm he hst
        · rcases endBranch_of_accepted_pinned he with hver | hpc
          · exact hold (Or.inr ⟨isLastOnTime_of_chain_aggregates
              (chain_aggregates_of_not_stale hst) hver, habs⟩)
          · exact DeployedRefundBreak.lastBatch a ha hmarks heq.symm he hpc
    · exact DeployedRefundBreak.flowIdClash a ha hmarks hcl
  · exact Or.inl hrf

theorem deployed_executed_flow_frozen_or_break_under_honest_roots {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {ze : UInt256}
    {F : Flow} {ev : GateEvidence} {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg)
    {Ms : Managers} {plog : List Obligation} {alog : List (DeployedAuthCall h ze)}
    (hr : DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog)
    (hroots : ∀ a ∈ alog, Aggregates S a.root) (o : Obligation) (ho : o.flowId = F.flowId) :
    ¬ Refunded Ms o
      ∨ ∃ a ∈ alog, a.marks = o
          ∧ (FlowIdClash fh F a.flow
            ∨ (a.flow = F
              ∧ (InclusionBreak h z0 hl S a.missing.chain (ev a.missing).1 (ev a.missing).2
                ∨ AbsenceBreak h z0 hl S F.deadline a.missing.chain a.batch a.proof
                ∨ (EndBranchAccepted a.backing S a.missing.chain F.deadline a.batch
                      a.pathSibs a.pathLeaf
                    ∧ (PinnedBreak h ze (a.backing.leaves a.missing.chain) a.batch
                      ∨ PathCollision h ze (a.backing.leaves a.missing.chain) a.pathSibs 0
                          (a.backing.height a.missing.chain) a.batch a.pathLeaf))))) := by
  rcases deployed_executed_flow_frozen_or_break hS hex hr o ho with hn | hb
  · exact Or.inl hn
  · refine Or.inr ?_
    cases hb with
    | flowIdClash a ha hm hcl => exact ⟨a, ha, hm, Or.inl hcl⟩
    | inclusion a ha hm hf hbi => exact ⟨a, ha, hm, Or.inr ⟨hf, Or.inl hbi⟩⟩
    | absence a ha hm hf hba => exact ⟨a, ha, hm, Or.inr ⟨hf, Or.inr (Or.inl hba)⟩⟩
    | lastBatch a ha hm hf he hpc => exact ⟨a, ha, hm, Or.inr ⟨hf, Or.inr (Or.inr ⟨he, hpc⟩)⟩⟩
    | staleRoot a ha _ _ _ hst => exact absurd hst (not_stale_of_aggregates (hroots a ha) _)

theorem deployed_refund_implies_own_accepted_timeout_or_logged_clash {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} {ze : UInt256} {F : Flow}
    (hchk : FlowIdChecked fh F) {Ms : Managers} {plog : List Obligation}
    {alog : List (DeployedAuthCall h ze)}
    (hr : DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog)
    (o : Obligation) (ho : o.flowId = F.flowId) (hrf : Refunded Ms o) :
    (∃ a ∈ alog, a.marks = o ∧ a.flow = F ∧ a.missing ∈ F.legs
        ∧ LegRefundableAcceptedBy h z0 hl cv S a.backing F a.missing a.batch a.proof
            a.pathSibs a.pathLeaf)
      ∨ ∃ a ∈ alog, a.marks = o ∧ FlowIdClash fh F a.flow := by
  obtain ⟨a, ha, ⟨hchk', _, hmiss, hacc⟩, hmarks⟩ := deployed_refund_logged hr o hrf
  have hid : F.flowId = a.flow.flowId := by
    rw [← ho, ← hmarks]; rfl
  rcases flowId_check_pins_legList_or_collision hchk hchk' hid with heq | hcl
  · refine Or.inl ⟨a, ha, hmarks, heq.symm, ?_, ?_⟩
    · rw [heq]; exact hmiss
    · rw [heq]; exact hacc
  · exact Or.inr ⟨a, ha, hmarks, hcl⟩

/-! ## The transitions the old model leaves out -/

/-- In a `ReachLog` run under `honestFlowHash F`, a refunded obligation carrying `F`'s id was
written by a call on a DECLARED leg of `F`, with `F`'s own old-gate timeout. -/
lemma old_run_refund_is_declared_leg {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {F : Flow} {Ms : Managers} {log : List AuthCall}
    (hr : ReachLog h z0 hl cv (honestFlowHash F) S emptyManagers Ms log) {o : Obligation}
    (ho : o.flowId = F.flowId) (hrf : Refunded Ms o) :
    ∃ b ∈ log, b.flow = F ∧ b.leg ∈ F.legs ∧ obligationOf F b.leg = o
      ∧ b.missing ∈ F.legs ∧ LegRefundableBy h z0 hl cv S F b.missing b.batch b.proof := by
  obtain ⟨b, hb, ⟨hchk', hleg, hmiss, href⟩, hobl⟩ := refund_logged hr o hrf
  have hid : F.flowId = b.flow.flowId := by
    rw [← ho, ← hobl]; rfl
  rcases flowId_check_pins_legList_or_collision (honest_flowHash_no_clash F).1 hchk' hid
    with heq | hcl
  · subst heq
    exact ⟨b, hb, rfl, hleg, hobl, hmiss, href⟩
  · exact absurd hcl ((honest_flowHash_no_clash F).2 _)

theorem misdeclared_leg_refunded_only_in_deployed_model (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (ze : UInt256) :
    ∃ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      Wf (mixedSystem 1)
        ∧ FlowIdChecked (honestFlowHash misdeclaredFlow) misdeclaredFlow
        ∧ misdeclaredObligation.flowId = misdeclaredFlow.flowId
        ∧ (∀ leg ∈ misdeclaredFlow.legs, obligationOf misdeclaredFlow leg ≠ misdeclaredObligation)
        ∧ (fun _ _ => (1 : UInt256)) misdeclaredObligation.flowId misdeclaredObligation.bundleHash
            ∈ keys (toAbs ((mixedSystem 1).tree 0 0))
        ∧ (∀ n, (fun _ _ => (1 : UInt256)) misdeclaredObligation.flowId
              misdeclaredObligation.bundleHash ∉ keys (toAbs ((mixedSystem 1).tree 1 n)))
        ∧ DeployedRun h z0 hl (fun _ _ => 1) (honestFlowHash misdeclaredFlow) (mixedSystem 1) ze
            emptyManagers Ms plog alog
        ∧ Refunded Ms misdeclaredObligation
        ∧ ∀ (Ms' : Managers) (log' : List AuthCall),
            ReachLog h z0 hl (fun _ _ => 1) (honestFlowHash misdeclaredFlow) (mixedSystem 1)
                emptyManagers Ms' log' →
              ¬ Refunded Ms' misdeclaredObligation := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  let q : ImtProof := ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩
  let a : DeployedAuthCall h ze :=
    ⟨0, misdeclaredFlow, 2, ⟨1, 2⟩, 1, q, timeOneRoot, trivialBacking h ze, fun _ => 0, 0⟩
  let M1 : Managers := setAt emptyManagers 0 ((emptyManagers 0).set 1 2 .Committed)
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  have hchk : FlowIdChecked (honestFlowHash misdeclaredFlow) misdeclaredFlow :=
    (honest_flowHash_no_clash misdeclaredFlow).1
  have hv : a.Verified h z0 hl (fun _ _ => 1) (honestFlowHash misdeclaredFlow) (mixedSystem 1) := by
    refine ⟨hchk, by simp [a, misdeclaredFlow], by simp [a, misdeclaredFlow], Or.inl ⟨⟨?_, ?_⟩, ?_⟩⟩
    · show (0 : ℕ) < 1
      norm_num
    · show (0 : ℕ) < 1
      norm_num
    · show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
        (beginHeight (mixedSystem 1) 1 1) 1 q
      rw [hbegin, hbeginH]
      exact setup_absence_accepted h z0 hl h1
  have happ : DeployedRun h z0 hl (fun _ _ => 1) (honestFlowHash misdeclaredFlow) (mixedSystem 1) ze
      emptyManagers M1 [⟨1, 2, 0⟩] [] :=
    DeployedRun.append (c := 0) (f := 1) (b := 2) DeployedRun.refl rfl
  have hguard : AuthorizeGuard (M1 a.chain) a.flow.flowId a.bundle := by
    show (M1 0).legState 1 2 = .Committed
    simp [M1, setAt, Manager.set]
  refine ⟨_, _, _, mixedSystem_wf h1, hchk, rfl, ?_, ?_, ?_,
    DeployedRun.authorize a happ hv hguard, ?_, ?_⟩
  · intro leg hleg he
    obtain rfl : leg = ⟨1, 2⟩ := List.mem_singleton.mp hleg
    exact absurd (congrArg Obligation.chain he) (by decide)
  · show (1 : UInt256) ∈ keys (toAbs ((mixedSystem 1).tree 0 0))
    rw [mixedSystem_tree_zero]
    exact mem_insertSetup h1
  · intro n hm
    rw [mixedSystem_tree_other hne] at hm
    exact not_mem_setup h1 hm
  · show 2 ≤ rank (stateOf (setAt M1 0 ((M1 0).set 1 2 .Revertable)) ⟨1, 2, 0⟩)
    rw [stateOf_setAt_self]
    simp [rank]
  · intro Ms' log' hr' hrf
    obtain ⟨b, _, _, hleg, hobl, _, _⟩ := old_run_refund_is_declared_leg hr' rfl hrf
    obtain hbl : b.leg = ⟨1, 2⟩ := List.mem_singleton.mp hleg
    have hc := congrArg Obligation.chain hobl
    rw [hbl] at hc
    exact absurd hc (by decide)

lemma staleSystem_rejects_old_gate {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    (N : ℕ) (p : ImtProof) : ¬ LegRefundableBy h z0 hl cv (staleSystem 1) staleFlow ⟨0, 0⟩ N p := by
  rintro (⟨hlate, _⟩ | ⟨⟨_, hlast⟩, _⟩)
  · exact absurd hlate (by simp [staleFlow])
  · have := hlast (N + 1) (Nat.lt_succ_self N)
    exact absurd this (by simp [staleFlow])

theorem stale_root_end_refund_of_delivered_leg_is_deployed (h : Hash) (z0 : UInt256)
    (hl : LeafHash) (ze : UInt256) :
    ∃ (ev : GateEvidence) (leg : FlowLeg) (Ms : Managers) (plog : List Obligation)
      (alog : List (DeployedAuthCall h ze)),
      Wf (staleSystem 1)
        ∧ ExecutedViaBy h z0 hl (fun _ _ => 1) (honestFlowHash staleFlow) (staleSystem 1)
            staleFlow ev leg
        ∧ ¬ InclusionBreak h z0 hl (staleSystem 1) leg.chain (ev leg).1 (ev leg).2
        ∧ DeployedRun h z0 hl (fun _ _ => 1) (honestFlowHash staleFlow) (staleSystem 1) ze
            emptyManagers Ms plog alog
        ∧ Refunded Ms (obligationOf staleFlow leg)
        ∧ (∀ (N : ℕ) (p : ImtProof),
            ¬ LegRefundableBy h z0 hl (fun _ _ => 1) (staleSystem 1) staleFlow leg N p)
        ∧ (∀ (Ms' : Managers) (log' : List AuthCall),
            ReachLog h z0 hl (fun _ _ => 1) (honestFlowHash staleFlow) (staleSystem 1)
                emptyManagers Ms' log' →
              ¬ Refunded Ms' (obligationOf staleFlow leg))
        ∧ DeployedRefundBreak h z0 hl (honestFlowHash staleFlow) (staleSystem 1) ze staleFlow ev
            (obligationOf staleFlow leg) alog
        ∧ ∀ a ∈ alog, a.flow = staleFlow
            ∧ ¬ FlowIdClash (honestFlowHash staleFlow) staleFlow a.flow
            ∧ ¬ InclusionBreak h z0 hl (staleSystem 1) a.missing.chain (ev a.missing).1
                (ev a.missing).2
            ∧ ¬ AbsenceBreak h z0 hl (staleSystem 1) staleFlow.deadline a.missing.chain a.batch
                a.proof
            ∧ ¬ PinnedBreak h ze (a.backing.leaves a.missing.chain) a.batch
            ∧ ¬ PathCollision h ze (a.backing.leaves a.missing.chain) a.pathSibs 0
                (a.backing.height a.missing.chain) a.batch a.pathLeaf
            ∧ StaleRootFor (staleSystem 1) a.root a.missing.chain := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hS : Wf (staleSystem 1) := staleSystem_wf h1
  let p : ImtProof := honestProof h z0 hl (staleSystem 1) 0 1 1
  let ev : GateEvidence := fun _ => (1, p)
  let q : ImtProof := ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩
  let a : DeployedAuthCall h ze :=
    ⟨0, staleFlow, 0, ⟨0, 0⟩, 0, q, staleRoot, staleBacking h ze, fun _ => 0, ze + 1⟩
  let M1 : Managers := setAt emptyManagers 0 ((emptyManagers 0).set 0 0 .Committed)
  have hcount : ((staleSystem 1).tree 0 1).leafCount = 2 := by
    rw [staleSystem_tree_succ]; rfl
  have hacc : Accepts h z0 hl (staleSystem 1) 0 1 1 p := by
    have := inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := (staleSystem 1).tree 0 1)
      (height := (staleSystem 1).height 0 1) (hS.capacity 0 1) (i := 1)
      (by rw [hcount]; norm_num)
    have hval : (((staleSystem 1).tree 0 1).leaf 1).value = 1 := by
      rw [staleSystem_tree_succ, insertSetup_leaf_one_value]
    rw [hval] at this
    exact this
  have hnb : ¬ InclusionBreak h z0 hl (staleSystem 1) 0 1 p :=
    honestProof_no_break h z0 hl (staleSystem 1) 0 1 1 (by rw [hcount]; norm_num)
  have hchk : FlowIdChecked (honestFlowHash staleFlow) staleFlow :=
    (honest_flowHash_no_clash staleFlow).1
  have hmem : (⟨0, 0⟩ : FlowLeg) ∈ staleFlow.legs := List.mem_singleton_self _
  have hex : ExecutedViaBy h z0 hl (fun _ _ => 1) (honestFlowHash staleFlow) (staleSystem 1)
      staleFlow ev ⟨0, 0⟩ := by
    refine ⟨hmem, hchk, ?_⟩
    intro l hl'
    obtain rfl : l = ⟨0, 0⟩ := List.mem_singleton.mp hl'
    exact ⟨by simp [staleFlow], hacc⟩
  have hend : EndBranchAccepted (staleBacking h ze) (staleSystem 1) 0 staleFlow.deadline 0
      (fun _ => 0) (ze + 1) :=
    ⟨by norm_num [staleFlow, staleRoot], by simp [staleFlow],
      ⟨by simp [staleBacking], rfl, fun l hl => absurd hl (Nat.not_lt_zero l)⟩⟩
  have habs : AbsenceAccepted h z0 hl ((staleSystem 1).tree 0 0) ((staleSystem 1).height 0 0) 1 q := by
    rw [staleSystem_tree_zero, staleSystem_height_zero]
    exact setup_absence_accepted h z0 hl h1
  have hv : a.Verified h z0 hl (fun _ _ => 1) (honestFlowHash staleFlow) (staleSystem 1) :=
    ⟨hchk, by simp [a, staleFlow], hmem, Or.inr ⟨hend, habs⟩⟩
  have happ : DeployedRun h z0 hl (fun _ _ => 1) (honestFlowHash staleFlow) (staleSystem 1) ze
      emptyManagers M1 [⟨0, 0, 0⟩] [] :=
    DeployedRun.append (c := 0) (f := 0) (b := 0) DeployedRun.refl rfl
  have hguard : AuthorizeGuard (M1 a.chain) a.flow.flowId a.bundle := by
    show (M1 0).legState 0 0 = .Committed
    simp [M1, setAt, Manager.set]
  have hstale : StaleRootFor (staleSystem 1) staleRoot 0 :=
    ⟨1, by simp [staleRoot], by simp [staleRoot]⟩
  refine ⟨ev, ⟨0, 0⟩, _, _, [a], hS, hex, hnb, DeployedRun.authorize a happ hv hguard, ?_,
    staleSystem_rejects_old_gate, ?_,
    DeployedRefundBreak.staleRoot a (List.mem_singleton_self _) rfl rfl hend hstale, ?_⟩
  · show 2 ≤ rank (stateOf (setAt M1 0 ((M1 0).set 0 0 .Revertable)) ⟨0, 0, 0⟩)
    rw [stateOf_setAt_self]
    simp [rank]
  · intro Ms' log' hr' hrf
    obtain ⟨b, _, _, hleg, _, hmiss, href⟩ := old_run_refund_is_declared_leg hr' rfl hrf
    obtain hbm : b.missing = ⟨0, 0⟩ := List.mem_singleton.mp hmiss
    rw [hbm] at href
    exact staleSystem_rejects_old_gate _ _ href
  · intro a' ha'
    rw [List.mem_singleton] at ha'
    subst ha'
    refine ⟨rfl, fun hcl => hcl.1 rfl, hnb, ?_, ?_, ?_, hstale⟩
    · rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
      · exact absurd hlate (by simp [staleFlow])
      · unfold ImtProofBreak at hb
        rw [staleSystem_tree_zero, staleSystem_height_zero] at hb
        exact honest_proof_no_break h z0 hl setup 0 0 (by norm_num [setup]) hb
    · intro hpb
      cases hpb with
      | nodeCollision l m hlt _ _ _ => exact absurd hlt (by simp [a, staleBacking])
      | entryIsEmpty hlt _ => exact absurd hlt (by simp [a, staleBacking])
    · rintro ⟨i, hi, _⟩
      exact absurd hi (Nat.not_lt_zero i)

/-! ## Anti-vacuity -/

theorem deployed_executed_flow_frozen_or_break_witness (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (ze : UInt256) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg) (Ms : Managers) (plog : List Obligation)
      (alog : List (DeployedAuthCall h ze)),
      Wf S ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog ∧ alog ≠ []
        ∧ (∀ a ∈ alog, Aggregates S a.root)
        ∧ ∀ c : Chain,
            ¬ DeployedRefundBreak h z0 hl fh S ze F ev ⟨F.flowId, leg.bundleHash, c⟩ alog
              ∧ ¬ Refunded Ms ⟨F.flowId, leg.bundleHash, c⟩ := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  let q : ImtProof := ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩
  let a : DeployedAuthCall h ze :=
    ⟨1, mixedFlow 1 1 2, 2, ⟨1, 2⟩, 1, q, timeOneRoot, trivialBacking h ze, fun _ => 0, 0⟩
  let M1 : Managers := setAt emptyManagers 1 ((emptyManagers 1).set 1 2 .Committed)
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  have hv : a.Verified h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) := by
    refine ⟨lengthFlowHash_checks_mixed, by simp [a, mixedFlow], by simp [a, mixedFlow],
      Or.inl ⟨⟨?_, ?_⟩, ?_⟩⟩
    · show (0 : ℕ) < 1
      norm_num
    · show (0 : ℕ) < 1
      norm_num
    · show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
        (beginHeight (mixedSystem 1) 1 1) 1 q
      rw [hbegin, hbeginH]
      exact setup_absence_accepted h z0 hl h1
  have happ : DeployedRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) ze
      emptyManagers M1 [⟨1, 2, 1⟩] [] :=
    DeployedRun.append (c := 1) (f := 1) (b := 2) DeployedRun.refl rfl
  have hguard : AuthorizeGuard (M1 a.chain) a.flow.flowId a.bundle := by
    show (M1 1).legState 1 2 = .Committed
    simp [M1, setAt, Manager.set]
  obtain ⟨hex, _⟩ := subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset
  refine ⟨fun _ _ => 1, lengthFlowHash, mixedSystem 1, subsetFlow 0 1, _, ⟨0, 1⟩, _, _, [a],
    mixedSystem_wf h1, hex, DeployedRun.authorize a happ hv hguard, List.cons_ne_nil _ _, ?_, ?_⟩
  · intro a' ha'
    rw [List.mem_singleton] at ha'
    subst ha'
    exact timeOneRoot_aggregates_mixed 1
  · intro c
    have hneq : a.marks ≠ ⟨(subsetFlow 0 1).flowId, (⟨0, 1⟩ : FlowLeg).bundleHash, c⟩ := by
      intro he
      have h10 : (1 : UInt256) = 0 := congrArg Obligation.flowId he
      exact absurd h10 (by decide)
    refine ⟨?_, ?_⟩
    · intro hb
      cases hb with
      | flowIdClash a' ha' hm _ =>
          rw [List.mem_singleton] at ha'; subst ha'; exact hneq hm
      | inclusion a' ha' hm _ _ =>
          rw [List.mem_singleton] at ha'; subst ha'; exact hneq hm
      | absence a' ha' hm _ _ =>
          rw [List.mem_singleton] at ha'; subst ha'; exact hneq hm
      | lastBatch a' ha' hm _ _ _ =>
          rw [List.mem_singleton] at ha'; subst ha'; exact hneq hm
      | staleRoot a' ha' hm _ _ _ =>
          rw [List.mem_singleton] at ha'; subst ha'; exact hneq hm
    · have hne' : (⟨0, 1, c⟩ : Obligation) ≠ ⟨1, 2, 1⟩ := by
        intro he
        have h01 : (0 : UInt256) = 1 := congrArg Obligation.flowId he
        exact absurd h01 (by decide)
      show ¬ 2 ≤ rank (stateOf (setAt M1 1 ((M1 1).set 1 2 .Revertable)) ⟨0, 1, c⟩)
      rw [stateOf_setAt_other hne']
      show ¬ 2 ≤ rank (stateOf (setAt emptyManagers 1 ((emptyManagers 1).set 1 2 .Committed))
        ⟨0, 1, c⟩)
      rw [stateOf_setAt_other hne', stateOf_emptyManagers]
      simp [rank]

end Contracts.RefundFaithful

/-! ## Certificates -/

namespace Contracts.RefundFaithful

theorem DeployedRefundNeedsLoggedIteration : Properties.DeployedRefundNeedsLoggedIteration :=
  fun _ _ _ _ _ _ _ _ _ _ hr o hrf => deployed_refund_logged hr o hrf
theorem DeployedRunAppendsOnce : Properties.DeployedRunAppendsOnce :=
  fun _ _ _ _ _ _ _ _ _ _ hr => deployed_run_appends_once hr
theorem DeployedExecutedFlowFrozenOrBreak : Properties.DeployedExecutedFlowFrozenOrBreak :=
  fun _ _ _ _ _ _ hS _ _ _ _ hex _ _ _ hr o ho => deployed_executed_flow_frozen_or_break hS hex hr o ho
theorem DeployedExecutedObligationNeverRefundedOrBreak :
    Properties.DeployedExecutedObligationNeverRefundedOrBreak :=
  fun _ _ _ _ _ _ hS _ _ _ _ hex _ _ _ hr => deployed_executed_flow_frozen_or_break hS hex hr _ rfl
theorem DeployedOneExecutionFreezesTheFlowOrBreak :
    Properties.DeployedOneExecutionFreezesTheFlowOrBreak :=
  fun _ _ _ _ _ _ hS _ _ _ _ hex _ _ _ hr _ _ _ =>
    deployed_executed_flow_frozen_or_break hS hex hr _ rfl
theorem DeployedExecutedFlowFrozenOrBreakUnderHonestRoots :
    Properties.DeployedExecutedFlowFrozenOrBreakUnderHonestRoots :=
  fun _ _ _ _ _ _ hS _ _ _ _ hex _ _ _ hr hroots o ho =>
    deployed_executed_flow_frozen_or_break_under_honest_roots hS hex hr hroots o ho
theorem DeployedRefundImpliesOwnAcceptedTimeoutOrLoggedClash :
    Properties.DeployedRefundImpliesOwnAcceptedTimeoutOrLoggedClash :=
  fun _ _ _ _ _ _ _ _ hchk _ _ _ hr o ho hrf =>
    deployed_refund_implies_own_accepted_timeout_or_logged_clash hchk hr o ho hrf
theorem MisdeclaredLegRefundedOnlyInDeployedModel :
    Properties.MisdeclaredLegRefundedOnlyInDeployedModel :=
  misdeclared_leg_refunded_only_in_deployed_model
theorem StaleRootEndRefundOfDeliveredLegIsDeployed :
    Properties.StaleRootEndRefundOfDeliveredLegIsDeployed :=
  stale_root_end_refund_of_delivered_leg_is_deployed
theorem DeployedExecutedFlowFrozenOrBreakWitness :
    Properties.DeployedExecutedFlowFrozenOrBreakWitness :=
  deployed_executed_flow_frozen_or_break_witness

end Contracts.RefundFaithful
