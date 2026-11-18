import EraSpec.Protocol.InteropAtomicity.Properties.RefundFaithful
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeafFaithful

/-!
# Proofs: one outcome per obligation, with `authorizeRefund` as it runs

Certificates for `EraSpec.Protocol.InteropAtomicity.Properties.RefundFaithful`.

The structure is `Contracts.Refund.executed_freezes_flow_or_break`'s: an induction finds the
logged iteration that wrote a refunded slot (`deployed_refund_logged`), and `_checkFlowId`
makes that iteration's flow the executed one or a pinned clash.  What changes is the last
step.  The iteration's timeout evidence is the contract's, so before
`Atomicity.executed_excludes_any_refund_or_break` applies, the END branch has to be turned
into `IsLastOnTime`.  That needs the batch-leaf path to be the last leaf at the chain
tree's height (`MerkleSpec.LastLeafFaithful.accepted_last_leaf_any_length_or_break`) and
the root to aggregate the missing leg's chain (`isLastOnTime_of_chain_aggregates`).  Each
failure is a case of `DeployedRefundBreak`.
-/

namespace Contracts.RefundFaithful

open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.LastLeafFaithful MerkleSpec.Verifier IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager Contracts.Refund

/-! ## The deployed timeout check against the repository's -/

/-- `Timeout.LastBatchAccepted` is `LastBatchPathAccepted` at the chain tree's height. -/
theorem lastBatchPathAccepted_of_lastBatchAccepted {h : Hash} {ze : UInt256} {R : SlRoot}
    {B : RootBacking h ze R} {c : Chain} {N : ℕ} {sibs : ℕ → UInt256} {x : UInt256}
    (hacc : LastBatchAccepted B c N sibs x) :
    LastBatchPathAccepted h ze (B.leaves c) (B.height c) sibs (B.height c) N x :=
  ⟨lt_of_lt_of_le hacc.inRange (B.capacity c), hacc.authenticated, hacc.zeroRightSiblings⟩

theorem acceptedBy_is_deployed_timeout {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof} {sibs : ℕ → UInt256} {x : UInt256}
    (hacc : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    DeployedTimeoutAccepted h z0 hl cv S B F leg N p (B.height leg.chain) sibs x := by
  rcases hacc with hb | ⟨he, habs⟩
  · exact Or.inl hb
  · exact Or.inr ⟨⟨he.rootAfterDeadline, he.onTime,
      lastBatchPathAccepted_of_lastBatchAccepted he.lastBatch⟩, habs⟩

/-! ## The deployed run's bookkeeping -/

/-- **A SLOT PAST `Committed` WAS WRITTEN BY A LOGGED, VERIFIED ITERATION.** -/
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

/-- The run's bookkeeping: a slot is past `Unset` exactly when it was appended, nothing is
appended twice, and every logged iteration wrote an appended slot. -/
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

/-- **THE DEPLOYED END BRANCH IS `EndBranchVerified`, OR A LOCATED LAST-LEAF BREAK.**  If the
batch-leaf path passes `_verifyLastBatchInRoot` as run, either it is the last leaf at the
chain tree's height, so the batch is the root's last batch of the chain, or the path
exhibits a `LastLeafAnyLengthBreak`. -/
theorem endBranchVerified_of_deployed_or_break {h : Hash} {ze : UInt256} {R : SlRoot}
    {B : RootBacking h ze R} {S : System} {c : Chain} {D N k : ℕ} {sibs : ℕ → UInt256}
    {x : UInt256} (he : DeployedEndBranch B S c D N k sibs x) :
    EndBranchVerified S R c D N
      ∨ LastLeafAnyLengthBreak h ze (B.leaves c) sibs k (B.height c) N x := by
  rcases accepted_last_leaf_any_length_or_break h ze (B.leaves c) sibs k (B.height c) N x
      (B.capacity c) he.lastBatch with ⟨_, hlast, _⟩ | hb
  · have hup := B.upToLast c
    exact Or.inl ⟨he.rootAfterDeadline, he.onTime, by omega⟩
  · exact Or.inr hb

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
      have hacc' : DeployedTimeoutAccepted h z0 hl cv S a.backing F a.missing a.batch a.proof
          a.pathLen a.pathSibs a.pathLeaf := by rw [heq]; exact hacc
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
        · rcases endBranchVerified_of_deployed_or_break he with hver | hlb
          · exact hold (Or.inr ⟨isLastOnTime_of_chain_aggregates
              (chain_aggregates_of_not_stale hst) hver, habs⟩)
          · exact DeployedRefundBreak.lastBatch a ha hmarks heq.symm he hlb
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
                ∨ (DeployedEndBranch a.backing S a.missing.chain F.deadline a.batch a.pathLen
                      a.pathSibs a.pathLeaf
                    ∧ LastLeafAnyLengthBreak h ze (a.backing.leaves a.missing.chain)
                        a.pathSibs a.pathLen (a.backing.height a.missing.chain) a.batch
                        a.pathLeaf)))) := by
  rcases deployed_executed_flow_frozen_or_break hS hex hr o ho with hn | hb
  · exact Or.inl hn
  · refine Or.inr ?_
    cases hb with
    | flowIdClash a ha hm hcl => exact ⟨a, ha, hm, Or.inl hcl⟩
    | inclusion a ha hm hf hbi => exact ⟨a, ha, hm, Or.inr ⟨hf, Or.inl hbi⟩⟩
    | absence a ha hm hf hba => exact ⟨a, ha, hm, Or.inr ⟨hf, Or.inr (Or.inl hba)⟩⟩
    | lastBatch a ha hm hf he hlb => exact ⟨a, ha, hm, Or.inr ⟨hf, Or.inr (Or.inr ⟨he, hlb⟩)⟩⟩
    | staleRoot a ha _ _ _ hst => exact absurd hst (not_stale_of_aggregates (hroots a ha) _)

theorem deployed_refund_implies_own_accepted_timeout_or_logged_clash {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} {ze : UInt256} {F : Flow}
    (hchk : FlowIdChecked fh F) {Ms : Managers} {plog : List Obligation}
    {alog : List (DeployedAuthCall h ze)}
    (hr : DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog)
    (o : Obligation) (ho : o.flowId = F.flowId) (hrf : Refunded Ms o) :
    (∃ a ∈ alog, a.marks = o ∧ a.flow = F ∧ a.missing ∈ F.legs
        ∧ DeployedTimeoutAccepted h z0 hl cv S a.backing F a.missing a.batch a.proof
            a.pathLen a.pathSibs a.pathLeaf)
      ∨ ∃ a ∈ alog, a.marks = o ∧ FlowIdClash fh F a.flow := by
  obtain ⟨a, ha, ⟨hchk', _, hmiss, hacc⟩, hmarks⟩ := deployed_refund_logged hr o hrf
  have hid : F.flowId = a.flow.flowId := by
    rw [← ho, ← hmarks]; rfl
  rcases flowId_check_pins_legList_or_collision hchk hchk' hid with heq | hcl
  · refine Or.inl ⟨a, ha, hmarks, heq.symm, ?_, ?_⟩
    · rw [heq]; exact hmiss
    · rw [heq]; exact hacc
  · exact Or.inr ⟨a, ha, hmarks, hcl⟩

/-! ## The runs `Refund.ReachLog` leaves out -/

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

/-- The misdeclared iteration: on chain `0`, flow `misdeclaredFlow`, writing bundle `2`, with
the declared leg `⟨1, 2⟩` missing, on the BEGIN branch at batch 1 with the honest absence
proof against chain `1`'s `setup` tree, resolved against `timeOneRoot`. -/
def misdeclaredCall (h : Hash) (z0 : UInt256) (hl : LeafHash) (ze : UInt256) :
    DeployedAuthCall h ze :=
  ⟨0, misdeclaredFlow, 2, ⟨1, 2⟩, 1, ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩,
    timeOneRoot, trivialBacking h ze, 0, fun _ => 0, 0⟩

/-- Chain `0`'s manager after `append(1, 2)`. -/
def misdeclaredCommitted : Managers :=
  setAt emptyManagers 0 ((emptyManagers 0).set 1 2 .Committed)

/-- ... and after the misdeclared iteration. -/
def misdeclaredRevertable : Managers :=
  setAt misdeclaredCommitted 0 ((misdeclaredCommitted 0).set 1 2 .Revertable)

lemma misdeclaredCall_verified (h : Hash) (z0 : UInt256) (hl : LeafHash) (ze : UInt256) :
    (misdeclaredCall h z0 hl ze).Verified h z0 hl (fun _ _ => 1)
      (honestFlowHash misdeclaredFlow) (mixedSystem 1) := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  refine ⟨(honest_flowHash_no_clash misdeclaredFlow).1, by simp [misdeclaredCall, misdeclaredFlow],
    by simp [misdeclaredCall, misdeclaredFlow], Or.inl ⟨⟨?_, ?_⟩, ?_⟩⟩
  · show (0 : ℕ) < 1
    norm_num
  · show (0 : ℕ) < 1
    norm_num
  · show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
      (beginHeight (mixedSystem 1) 1 1) 1 ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩
    rw [hbegin, hbeginH]
    exact setup_absence_accepted h z0 hl h1

lemma misdeclared_run (h : Hash) (z0 : UInt256) (hl : LeafHash) (ze : UInt256) :
    DeployedRun h z0 hl (fun _ _ => 1) (honestFlowHash misdeclaredFlow) (mixedSystem 1) ze
      emptyManagers misdeclaredRevertable [misdeclaredObligation] [misdeclaredCall h z0 hl ze] := by
  have happ : DeployedRun h z0 hl (fun _ _ => 1) (honestFlowHash misdeclaredFlow) (mixedSystem 1)
      ze emptyManagers misdeclaredCommitted [⟨1, 2, 0⟩] [] :=
    DeployedRun.append (c := 0) (f := 1) (b := 2) DeployedRun.refl rfl
  have hguard : AuthorizeGuard (misdeclaredCommitted (misdeclaredCall h z0 hl ze).chain)
      (misdeclaredCall h z0 hl ze).flow.flowId (misdeclaredCall h z0 hl ze).bundle := by
    show (misdeclaredCommitted 0).legState 1 2 = .Committed
    simp [misdeclaredCommitted, setAt, Manager.set]
  exact DeployedRun.authorize _ happ (misdeclaredCall_verified h z0 hl ze) hguard

lemma misdeclared_refunded : Refunded misdeclaredRevertable misdeclaredObligation := by
  show 2 ≤ rank (stateOf (setAt misdeclaredCommitted 0
    ((misdeclaredCommitted 0).set 1 2 .Revertable)) ⟨1, 2, 0⟩)
  rw [stateOf_setAt_self]
  simp [rank]

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
  refine ⟨_, _, _, mixedSystem_wf h1, (honest_flowHash_no_clash misdeclaredFlow).1, rfl, ?_, ?_,
    ?_, misdeclared_run h z0 hl ze, misdeclared_refunded, ?_⟩
  · intro leg hleg he
    obtain rfl : leg = ⟨1, 2⟩ := List.mem_singleton.mp hleg
    exact absurd (congrArg Obligation.chain he) (by decide)
  · show (1 : UInt256) ∈ keys (toAbs ((mixedSystem 1).tree 0 0))
    rw [mixedSystem_tree_zero]
    exact mem_insertSetup h1
  · intro n hm
    rw [mixedSystem_tree_other hne] at hm
    exact not_mem_setup h1 hm
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

/-- No `LastLeafAnyLengthBreak` on the one-leaf batch tree at height 0, for the empty path
at position 0. -/
lemma staleBacking_no_lastLeaf_break (h : Hash) (ze : UInt256) (sibs : ℕ → UInt256)
    (x : UInt256) : ¬ LastLeafAnyLengthBreak h ze [ze + 1] sibs 0 0 0 x := by
  intro hb
  cases hb with
  | wrongLength hh => exact heightBreak_not_tautology.1 _ _ _ _ _ _ _ hh
  | paddedEntry _ hle _ => exact absurd hle (by simp)
  | pinned _ hpb =>
    cases hpb with
    | nodeCollision l m hlt _ _ _ => exact absurd hlt (by simp)
    | entryIsEmpty hlt _ => exact absurd hlt (by simp)
  | pathCollision _ hpc =>
    obtain ⟨i, hi, _⟩ := hpc
    exact absurd hi (Nat.not_lt_zero i)

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
            ∧ ¬ LastLeafAnyLengthBreak h ze (a.backing.leaves a.missing.chain) a.pathSibs
                a.pathLen (a.backing.height a.missing.chain) a.batch a.pathLeaf
            ∧ StaleRootFor (staleSystem 1) a.root a.missing.chain := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hS : Wf (staleSystem 1) := staleSystem_wf h1
  let p : ImtProof := honestProof h z0 hl (staleSystem 1) 0 1 1
  let ev : GateEvidence := fun _ => (1, p)
  let q : ImtProof := ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩
  let a : DeployedAuthCall h ze :=
    ⟨0, staleFlow, 0, ⟨0, 0⟩, 0, q, staleRoot, staleBacking h ze, 0, fun _ => 0, ze + 1⟩
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
  have hend : DeployedEndBranch (staleBacking h ze) (staleSystem 1) 0 staleFlow.deadline 0 0
      (fun _ => 0) (ze + 1) :=
    ⟨by norm_num [staleFlow, staleRoot], by simp [staleFlow],
      ⟨by norm_num, rfl, fun l hl => absurd hl (Nat.not_lt_zero l)⟩⟩
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
    refine ⟨rfl, fun hcl => hcl.1 rfl, hnb, ?_, staleBacking_no_lastLeaf_break h ze _ _, hstale⟩
    rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
    · exact absurd hlate (by simp [staleFlow])
    · unfold ImtProofBreak at hb
      rw [staleSystem_tree_zero, staleSystem_height_zero] at hb
      exact honest_proof_no_break h z0 hl setup 0 0 (by norm_num [setup]) hb

theorem deployed_padding_refund_locates_absence_break (h : Hash) (hl : LeafHash)
    (ze a b : UInt256) (ha : 0 < a) (hab : a < b) :
    ∃ (ev : GateEvidence) (Ms : Managers) (plog : List Obligation)
      (alog : List (DeployedAuthCall h ze)),
      Wf (paddedSystem a b)
        ∧ ExecutedViaBy h (hl ⟨0, 0, 0⟩) hl (fun _ _ => a) (honestFlowHash (subsetFlow 0 0))
            (paddedSystem a b) (subsetFlow 0 0) ev ⟨0, 0⟩
        ∧ DeployedRun h (hl ⟨0, 0, 0⟩) hl (fun _ _ => a) (honestFlowHash (subsetFlow 0 0))
            (paddedSystem a b) ze emptyManagers Ms plog alog
        ∧ alog ≠ [] ∧ (∀ x ∈ alog, Aggregates (paddedSystem a b) x.root)
        ∧ Refunded Ms (obligationOf (subsetFlow 0 0) ⟨0, 0⟩)
        ∧ ∀ x ∈ alog, x.marks = obligationOf (subsetFlow 0 0) ⟨0, 0⟩
            ∧ x.flow = subsetFlow 0 0
            ∧ ¬ FlowIdClash (honestFlowHash (subsetFlow 0 0)) (subsetFlow 0 0) x.flow
            ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) x.missing.chain
                (ev x.missing).1 (ev x.missing).2
            ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) (subsetFlow 0 0).deadline
                x.missing.chain x.batch x.proof
            ∧ TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl
                (beginTree (paddedSystem a b) x.missing.chain x.batch)
                (beginHeight (paddedSystem a b) x.missing.chain x.batch)
                x.proof.sibs x.proof.pathLen x.proof.index x.proof.leaf .paddingHit := by
  let z0 := hl ⟨0, 0, 0⟩
  let T := threeLeafTree a b
  let F : Flow := subsetFlow 0 0
  let p : ImtProof := ⟨T.leaf 1, 1, honestSibs h z0 (leafHashes hl T) 1, 2⟩
  let q : ImtProof := ⟨⟨0, 0, 0⟩, 3, honestSibs h z0 (leafHashes hl T) 3, 2⟩
  let x : DeployedAuthCall h ze :=
    ⟨0, F, 0, ⟨0, 0⟩, 1, q, timeOneRoot, trivialBacking h ze, 0, fun _ => 0, 0⟩
  let M1 : Managers := setAt emptyManagers 0 ((emptyManagers 0).set 0 0 .Committed)
  obtain ⟨_, hI, hN⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  obtain ⟨hnb, hpad⟩ := padding_countermodel_locates_padding_hit h hl a b
  have hchk : FlowIdChecked (honestFlowHash F) F := (honest_flowHash_no_clash F).1
  have hmem : (⟨0, 0⟩ : FlowLeg) ∈ F.legs := List.mem_singleton_self _
  have hbegin : beginTree (paddedSystem a b) 0 1 = T := paddedSystem_tree_zero a b 0
  have hbeginH : beginHeight (paddedSystem a b) 0 1 = 2 := paddedSystem_height_zero a b 0
  have hv : x.Verified h z0 hl (fun _ _ => a) (honestFlowHash F) (paddedSystem a b) := by
    refine ⟨hchk, by simp [x, F, subsetFlow], hmem, Or.inl ⟨⟨?_, ?_⟩, ?_⟩⟩
    · show (0 : ℕ) < 1
      norm_num
    · show (0 : ℕ) < 1
      norm_num
    · show AbsenceAccepted h z0 hl (beginTree (paddedSystem a b) 0 1)
        (beginHeight (paddedSystem a b) 0 1) a q
      rw [hbegin, hbeginH]
      exact hN
  have hab' : AbsenceBreak h z0 hl (paddedSystem a b) F.deadline (0 : Chain) 1 q := by
    refine Or.inl ⟨by show (0 : ℕ) < 1; norm_num, ?_⟩
    show TreeRootBreak h z0 hl (beginTree (paddedSystem a b) 0 1)
      (beginHeight (paddedSystem a b) 0 1) q.sibs q.pathLen q.index q.leaf
    rw [hbegin, hbeginH]
    exact hpad
  have happ : DeployedRun h z0 hl (fun _ _ => a) (honestFlowHash F) (paddedSystem a b) ze
      emptyManagers M1 [⟨0, 0, 0⟩] [] :=
    DeployedRun.append (c := 0) (f := 0) (b := 0) DeployedRun.refl rfl
  have hguard : AuthorizeGuard (M1 x.chain) x.flow.flowId x.bundle := by
    show (M1 0).legState 0 0 = .Committed
    simp [M1, setAt, Manager.set]
  refine ⟨fun _ => (0, p), _, _, [x], paddedSystem_wf ha hab, ⟨hmem, hchk, ?_⟩,
    DeployedRun.authorize x happ hv hguard, List.cons_ne_nil _ _, ?_, ?_, ?_⟩
  · intro l hl'
    obtain rfl : l = ⟨0, 0⟩ := List.mem_singleton.mp hl'
    exact ⟨le_refl 0, hI⟩
  · intro x' hx'
    rw [List.mem_singleton] at hx'
    subst hx'
    exact timeOneRoot_aggregates_padded a b
  · show 2 ≤ rank (stateOf (setAt M1 0 ((M1 0).set 0 0 .Revertable)) ⟨0, 0, 0⟩)
    rw [stateOf_setAt_self]
    simp [rank]
  · intro x' hx'
    rw [List.mem_singleton] at hx'
    subst hx'
    refine ⟨rfl, rfl, fun hcl => hcl.1 rfl, hnb, hab', ?_⟩
    show TreeRootBreakExactly h z0 hl (beginTree (paddedSystem a b) 0 1)
      (beginHeight (paddedSystem a b) 0 1) q.sibs q.pathLen q.index q.leaf .paddingHit
    rw [hbegin, hbeginH]
    exact padding_countermodel_exactly_padding_hit h hl a b

/-! ## Witnesses -/

/-- The witness run's managers: `append(0, 1)` on chain `0`, `append(1, 2)` on chain `1`,
then the iteration writing `(1, 2)` on chain `1`. -/
def frozenWitnessManagers : Managers :=
  let M1 : Managers := setAt emptyManagers 0 ((emptyManagers 0).set 0 1 .Committed)
  let M2 : Managers := setAt M1 1 ((M1 1).set 1 2 .Committed)
  setAt M2 1 ((M2 1).set 1 2 .Revertable)

/-- The witness iteration: on chain `1`, flow `mixedFlow 1 1 2`, writing bundle `2`, with leg
`⟨1, 2⟩` missing, on the BEGIN branch at batch 1 against `timeOneRoot`. -/
def frozenWitnessCall (h : Hash) (z0 : UInt256) (hl : LeafHash) (ze : UInt256) :
    DeployedAuthCall h ze :=
  ⟨1, mixedFlow 1 1 2, 2, ⟨1, 2⟩, 1, ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩,
    timeOneRoot, trivialBacking h ze, 0, fun _ => 0, 0⟩

theorem deployed_executed_flow_frozen_or_break_witness (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (ze : UInt256) :
    ∃ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze))
      (ev : GateEvidence),
      Wf (mixedSystem 1)
        ∧ ExecutedViaBy h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) (subsetFlow 0 1) ev
            ⟨0, 1⟩
        ∧ DeployedRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) ze emptyManagers Ms
            plog alog
        ∧ plog = [⟨1, 2, 1⟩, ⟨0, 1, 0⟩] ∧ alog ≠ []
        ∧ (∀ a ∈ alog, a.chain = 1 ∧ a.flow = mixedFlow 1 1 2 ∧ a.marks = ⟨1, 2, 1⟩
            ∧ FlowIdChecked lengthFlowHash a.flow ∧ Aggregates (mixedSystem 1) a.root)
        ∧ Refunded Ms ⟨1, 2, 1⟩
        ∧ stateOf Ms ⟨0, 1, 0⟩ = .Committed
        ∧ ∀ c : Chain,
            ¬ DeployedRefundBreak h z0 hl lengthFlowHash (mixedSystem 1) ze (subsetFlow 0 1) ev
                ⟨0, 1, c⟩ alog
              ∧ ¬ Refunded Ms ⟨0, 1, c⟩ := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  let a := frozenWitnessCall h z0 hl ze
  let M1 : Managers := setAt emptyManagers 0 ((emptyManagers 0).set 0 1 .Committed)
  let M2 : Managers := setAt M1 1 ((M1 1).set 1 2 .Committed)
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  have hv : a.Verified h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) := by
    refine ⟨lengthFlowHash_checks_mixed, by simp [a, frozenWitnessCall, mixedFlow],
      by simp [a, frozenWitnessCall, mixedFlow], Or.inl ⟨⟨?_, ?_⟩, ?_⟩⟩
    · show (0 : ℕ) < 1
      norm_num
    · show (0 : ℕ) < 1
      norm_num
    · show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
        (beginHeight (mixedSystem 1) 1 1) 1
        ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩
      rw [hbegin, hbeginH]
      exact setup_absence_accepted h z0 hl h1
  have hrun1 : DeployedRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) ze
      emptyManagers M1 [⟨0, 1, 0⟩] [] :=
    DeployedRun.append (c := 0) (f := 0) (b := 1) DeployedRun.refl rfl
  have hrun2 : DeployedRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) ze
      emptyManagers M2 [⟨1, 2, 1⟩, ⟨0, 1, 0⟩] [] := by
    refine DeployedRun.append (c := 1) (f := 1) (b := 2) hrun1 ?_
    show (M1 1).legState 1 2 = .Unset
    simp [M1, setAt, Manager.set, emptyManagers, Contracts.AtomicFlowManager.empty]
  have hguard : AuthorizeGuard (M2 a.chain) a.flow.flowId a.bundle := by
    show (M2 1).legState 1 2 = .Committed
    simp [M2, setAt, Manager.set]
  have hrun : DeployedRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) ze
      emptyManagers frozenWitnessManagers [⟨1, 2, 1⟩, ⟨0, 1, 0⟩] [a] :=
    DeployedRun.authorize a hrun2 hv hguard
  obtain ⟨hex, _⟩ := subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset
  -- the written slot carries flow id `1`, the executed flow's slots flow id `0`
  have hneq : ∀ c : Chain, (⟨0, 1, c⟩ : Obligation) ≠ ⟨1, 2, 1⟩ := by
    intro c he
    have h01 : (0 : UInt256) = 1 := congrArg Obligation.flowId he
    exact absurd h01 (by decide)
  have hstate : ∀ c : Chain, stateOf frozenWitnessManagers ⟨0, 1, c⟩
      = stateOf M1 ⟨0, 1, c⟩ := by
    intro c
    show stateOf (setAt M2 1 ((M2 1).set 1 2 .Revertable)) ⟨0, 1, c⟩ = _
    rw [stateOf_setAt_other (hneq c)]
    show stateOf (setAt M1 1 ((M1 1).set 1 2 .Committed)) ⟨0, 1, c⟩ = _
    rw [stateOf_setAt_other (hneq c)]
  refine ⟨frozenWitnessManagers, _, [a], _, mixedSystem_wf h1, hex, hrun, rfl,
    List.cons_ne_nil _ _, ?_, ?_, ?_, ?_⟩
  · intro a' ha'
    rw [List.mem_singleton] at ha'
    subst ha'
    exact ⟨rfl, rfl, rfl, lengthFlowHash_checks_mixed, timeOneRoot_aggregates_mixed 1⟩
  · show 2 ≤ rank (stateOf (setAt M2 1 ((M2 1).set 1 2 .Revertable)) ⟨1, 2, 1⟩)
    rw [stateOf_setAt_self]
    simp [rank]
  · rw [hstate]
    exact stateOf_setAt_self _ _ _ _ _
  · intro c
    have hmk : a.marks ≠ ⟨(subsetFlow 0 1).flowId, (⟨0, 1⟩ : FlowLeg).bundleHash, c⟩ :=
      fun he => hneq c he.symm
    refine ⟨?_, ?_⟩
    · intro hb
      cases hb with
      | flowIdClash a' ha' hm _ =>
          rw [List.mem_singleton] at ha'; subst ha'; exact hmk hm
      | inclusion a' ha' hm _ _ =>
          rw [List.mem_singleton] at ha'; subst ha'; exact hmk hm
      | absence a' ha' hm _ _ =>
          rw [List.mem_singleton] at ha'; subst ha'; exact hmk hm
      | lastBatch a' ha' hm _ _ _ =>
          rw [List.mem_singleton] at ha'; subst ha'; exact hmk hm
      | staleRoot a' ha' hm _ _ _ =>
          rw [List.mem_singleton] at ha'; subst ha'; exact hmk hm
    · show ¬ 2 ≤ rank (stateOf frozenWitnessManagers ⟨0, 1, c⟩)
      rw [hstate]
      by_cases hc : c = 0
      · subst hc
        rw [stateOf_setAt_self]
        simp [rank]
      · have hne0 : (⟨0, 1, c⟩ : Obligation) ≠ ⟨0, 1, 0⟩ := fun he =>
          hc (congrArg Obligation.chain he)
        rw [stateOf_setAt_other hne0, stateOf_emptyManagers]
        simp [rank]

theorem deployed_refund_own_timeout_witness (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (ze : UInt256) :
    ∃ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      FlowIdChecked (honestFlowHash misdeclaredFlow) misdeclaredFlow
        ∧ DeployedRun h z0 hl (fun _ _ => 1) (honestFlowHash misdeclaredFlow) (mixedSystem 1) ze
            emptyManagers Ms plog alog
        ∧ misdeclaredObligation.flowId = misdeclaredFlow.flowId
        ∧ Refunded Ms misdeclaredObligation
        ∧ alog ≠ [] ∧ plog.count misdeclaredObligation = 1
        ∧ (∃ a ∈ alog, a.marks = misdeclaredObligation ∧ a.flow = misdeclaredFlow
            ∧ a.missing ∈ misdeclaredFlow.legs
            ∧ DeployedTimeoutAccepted h z0 hl (fun _ _ => 1) (mixedSystem 1) a.backing
                misdeclaredFlow a.missing a.batch a.proof a.pathLen a.pathSibs a.pathLeaf)
        ∧ ¬ ∃ a ∈ alog, a.marks = misdeclaredObligation
            ∧ FlowIdClash (honestFlowHash misdeclaredFlow) misdeclaredFlow a.flow := by
  obtain ⟨hchk, _, hmiss, hacc⟩ := misdeclaredCall_verified h z0 hl ze
  refine ⟨_, _, _, hchk, misdeclared_run h z0 hl ze, rfl, misdeclared_refunded,
    List.cons_ne_nil _ _, by simp, ⟨misdeclaredCall h z0 hl ze, List.mem_singleton_self _, rfl,
      rfl, hmiss, hacc⟩, ?_⟩
  rintro ⟨a, ha, _, hcl⟩
  rw [List.mem_singleton] at ha
  subst ha
  exact (honest_flowHash_no_clash misdeclaredFlow).2 _ hcl

end Contracts.RefundFaithful

/-! ## Certificates -/

namespace Contracts.RefundFaithful

theorem AcceptedByIsDeployedTimeout : Properties.AcceptedByIsDeployedTimeout :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ hacc => acceptedBy_is_deployed_timeout hacc
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
theorem DeployedPaddingRefundLocatesAbsenceBreak :
    Properties.DeployedPaddingRefundLocatesAbsenceBreak :=
  deployed_padding_refund_locates_absence_break
theorem DeployedExecutedFlowFrozenOrBreakWitness :
    Properties.DeployedExecutedFlowFrozenOrBreakWitness :=
  deployed_executed_flow_frozen_or_break_witness
theorem DeployedRefundOwnTimeoutWitness : Properties.DeployedRefundOwnTimeoutWitness :=
  deployed_refund_own_timeout_witness

end Contracts.RefundFaithful
