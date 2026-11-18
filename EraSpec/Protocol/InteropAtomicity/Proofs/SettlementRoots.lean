import EraSpec.Protocol.InteropAtomicity.Properties.SettlementRoots
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund
import EraSpec.Protocol.InteropAtomicity.Proofs.Operational
import EraSpec.Contracts.MessageRoot.Proofs.Aggregation
import EraSpec.Contracts.L2InteropRootStorage.Proofs.Model

/-!
# Proofs: the timeout and refund headlines from the settlement layer's own roots

(a) re-runs the existing proofs (`Proofs/Timeout.lean`, `Proofs/Refund.lean`) with
`Contracts.InteropOperational.refundableBy_of_verifiedBy_before`, the END branch from the strict
aggregation form, in place of `refundableBy_of_verifiedBy`. (c) takes the strict form from
`Contracts.MessageRoot.Aggregation.aggregatesStrictAt_reach` and `Wf.timeOrdered` from
`leafTime_mono`. (b) chains `L2InteropRootStorage.EntriesAreAdmittedImports` with the Executor's
check. The witnesses are concrete MessageRoot runs, checked by `decide`, under the systems and
flows of `Proofs/Timeout.lean` and `Proofs/Refund.lean`.
-/

namespace Contracts.SettlementRoots

open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.Refund Contracts.AtomicFlowManager
open Contracts.InteropOperational (AggregatesBefore isLastOnTime_of_aggregatesBefore
  refundableBy_of_verifiedBy_before)

/-! ## (a) The strict form suffices -/

theorem verified_implies_refundable_before {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {R : SlRoot} (hagg : AggregatesBefore S R)
    {F : Flow} {leg : FlowLeg} (hv : LegRefundableVerified h z0 hl cv S R F leg) :
    LegRefundable h z0 hl cv S F leg := by
  obtain ⟨N, p, hbr⟩ := hv
  refine ⟨N, p, ?_⟩
  rcases hbr with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact Or.inl ⟨hb.late, habs⟩
  · exact Or.inr ⟨isLastOnTime_of_aggregatesBefore hagg he, habs⟩

theorem timeout_means_missed_deadline_or_break_before {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {R : SlRoot} (hagg : AggregatesBefore S R)
    {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    (hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p) :
    (∀ n, S.time leg.chain n ≤ F.deadline →
        legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
      ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p := by
  by_cases hb : AbsenceBreak h z0 hl S F.deadline leg.chain N p
  · exact Or.inr hb
  · refine Or.inl fun n hon hmem => ?_
    rcases member_not_refundable_or_break hS hon hmem N p with hn | hb'
    · exact hn (refundableBy_of_verifiedBy_before hagg hv)
    · exact hb hb'

theorem timeout_excludes_finality_or_break_before {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {R : SlRoot} (hagg : AggregatesBefore S R)
    {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    (hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p) (n : ℕ) (p' : ImtProof) :
    ¬ LegFinalizedBy h z0 hl cv S F leg n p'
      ∨ InclusionBreak h z0 hl S leg.chain n p'
      ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p := by
  by_cases hfin : LegFinalizedBy h z0 hl cv S F leg n p'
  · obtain ⟨hon, hacc⟩ := hfin
    rcases finality_means_membership_or_break hacc with hmem | hb
    · rcases member_not_refundable_or_break hS hon hmem N p with hn | hb'
      · exact absurd (refundableBy_of_verifiedBy_before hagg hv) hn
      · exact Or.inr (Or.inr hb')
    · exact Or.inr (Or.inl hb)
  · exact Or.inl hfin

theorem accepted_timeout_means_missed_deadline_or_break_before {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {S : System} (hS : Wf S) {ze : UInt256} {R : SlRoot}
    {B : RootBacking h ze R} (hagg : AggregatesBefore S R) {F : Flow} {leg : FlowLeg} {N : ℕ}
    {p : ImtProof} {sibs : ℕ → UInt256} {x : UInt256}
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    (∀ n, S.time leg.chain n ≤ F.deadline →
        legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
      ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p
      ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
  have hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p
      ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
    rcases ha with ⟨hb, habs⟩ | ⟨he, habs⟩
    · exact Or.inl (Or.inl ⟨hb, habs⟩)
    · rcases endBranch_of_accepted_pinned he with hver | hrest
      · exact Or.inl (Or.inr ⟨hver, habs⟩)
      · exact Or.inr ⟨he, hrest⟩
  rcases hv with hv | hrest
  · rcases timeout_means_missed_deadline_or_break_before hS hagg hv with hm | hb
    · exact Or.inl hm
    · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hrest)

theorem accepted_implies_refundable_pinned_before {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : AggregatesBefore S R) {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    {sibs : ℕ → UInt256} {x : UInt256}
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    LegRefundable h z0 hl cv S F leg ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
  rcases ha with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact Or.inl (verified_implies_refundable_before hagg ⟨N, p, Or.inl ⟨hb, habs⟩⟩)
  · rcases endBranch_of_accepted_pinned he with hv | hrest
    · exact Or.inl (verified_implies_refundable_before hagg ⟨N, p, Or.inr ⟨hv, habs⟩⟩)
    · exact Or.inr ⟨he, hrest⟩

theorem accepted_implies_refundable_on_before {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : AggregatesBefore S R) {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    {sibs : ℕ → UInt256} {x : UInt256}
    (hsep : EntriesNotEmpty ze (B.leaves leg.chain))
    (hinj : PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
      ∨ VerifiedPair h sibs (B.height leg.chain) N x q))
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    LegRefundable h z0 hl cv S F leg := by
  rcases ha with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact verified_implies_refundable_before hagg ⟨N, p, Or.inl ⟨hb, habs⟩⟩
  · exact verified_implies_refundable_before hagg
      ⟨N, p, Or.inr ⟨endBranch_of_accepted_on hsep hinj he, habs⟩⟩

theorem verified_timeout_authorizes_before {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {R : SlRoot} (hagg : AggregatesBefore S R)
    {F : Flow} {leg : FlowLeg} (hmem : leg ∈ F.legs)
    (hv : LegRefundableVerified h z0 hl cv S R F leg) : RefundAuthorized h z0 hl cv S F :=
  ⟨leg, hmem, verified_implies_refundable_before hagg hv⟩

theorem accepted_timeout_authorizes_pinned_before {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : AggregatesBefore S R) {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    {sibs : ℕ → UInt256} {x : UInt256} (hmem : leg ∈ F.legs)
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    RefundAuthorized h z0 hl cv S F ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
  rcases accepted_implies_refundable_pinned_before hagg ha with hr | hrest
  · exact Or.inl ⟨leg, hmem, hr⟩
  · exact Or.inr hrest

theorem executed_excludes_accepted_refund_or_break_before {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {ze : UInt256}
    {R : SlRoot} {B : RootBacking h ze R} (hagg : AggregatesBefore S R) {F : Flow}
    {ev : GateEvidence} {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg)
    (other : FlowLeg) (hother : other ∈ F.legs) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256)
    (x : UInt256) :
    ¬ LegRefundableAcceptedBy h z0 hl cv S B F other N p sibs x
      ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2
      ∨ AbsenceBreak h z0 hl S F.deadline other.chain N p
      ∨ (EndBranchAccepted B S other.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves other.chain) N
            ∨ PathCollision h ze (B.leaves other.chain) sibs 0 (B.height other.chain) N x)) := by
  by_cases ha : LegRefundableAcceptedBy h z0 hl cv S B F other N p sibs x
  · refine Or.inr ?_
    have hv : LegRefundableBy h z0 hl cv S F other N p
        ∨ (EndBranchAccepted B S other.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves other.chain) N
            ∨ PathCollision h ze (B.leaves other.chain) sibs 0 (B.height other.chain) N x)) := by
      rcases ha with ⟨hb, habs⟩ | ⟨he, habs⟩
      · exact Or.inl (refundableBy_of_verifiedBy_before hagg (Or.inl ⟨hb, habs⟩))
      · rcases endBranch_of_accepted_pinned he with hver | hrest
        · exact Or.inl (refundableBy_of_verifiedBy_before hagg (Or.inr ⟨hver, habs⟩))
        · exact Or.inr ⟨he, hrest⟩
    rcases hv with hr | hrest
    · rcases executed_excludes_any_refund_or_break hS hex other hother N p with hn | hb | hb
      · exact absurd hr hn
      · exact Or.inl hb
      · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hrest)
  · exact Or.inl ha

theorem reachLog_of_reachLogAt {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {roots : SlRoot → Prop}
    (hroots : ∀ R, roots R → AggregatesBefore S R)
    {Ms Ns : Managers} {log : List AuthCall} (hr : ReachLogAt h z0 hl cv fh S roots Ms Ns log) :
    ReachLog h z0 hl cv fh S Ms Ns log := by
  induction hr with
  | refl => exact ReachLog.refl
  | append _ hg ih => exact ReachLog.append ih hg
  | authorize a R _ hR hv hg ih =>
    obtain ⟨hchk, hleg, hmiss, href⟩ := hv
    exact ReachLog.authorize a ih
      ⟨hchk, hleg, hmiss, refundableBy_of_verifiedBy_before (hroots R hR) href⟩ hg
  | claim _ hg ih => exact ReachLog.claim ih hg

/-! ## (c) The settlement layer supplies the strict form -/

theorem historicalRoot_aggregatesBefore {P : MessageRoot.Aggregation.Params}
    {r : MessageRoot.Aggregation.TsRule} {stF : MessageRoot.Aggregation.State} {R : SlRoot}
    {S : System} (hR : HistoricalRootOf P r stF R) (hclk : ClockedBy S stF) :
    AggregatesBefore S R := by
  obtain ⟨st, b, e, h1, h2, he, rfl⟩ := hR
  intro c n hlt
  simp only [slRootOfEntry] at hlt ⊢
  rw [hclk] at hlt
  have := MessageRoot.Aggregation.aggregatesStrictAt_reach h1 h2 he c n hlt
  omega

theorem historicalRoot_aggregates_strictTs {P : MessageRoot.Aggregation.Params}
    {st : MessageRoot.Aggregation.State} {b : ℕ} {e : MessageRoot.Aggregation.HistEntry}
    {S : System} (hr : MessageRoot.Aggregation.Reachable P .strict st) (he : st.hist b = some e)
    (hclk : ClockedBy S st) : Aggregates S (slRootOfEntry e) := by
  intro c n hle
  simp only [slRootOfEntry] at hle ⊢
  rw [hclk] at hle
  have := MessageRoot.Aggregation.aggregatesAt_strict hr he c n hle
  omega

theorem uncounted_chain_has_no_endBranch {P : MessageRoot.Aggregation.Params}
    {r : MessageRoot.Aggregation.TsRule} {st stF : MessageRoot.Aggregation.State} {b : ℕ}
    {e : MessageRoot.Aggregation.HistEntry} {c : Chain} {S : System} {D N : ℕ}
    (h1 : MessageRoot.Aggregation.Reachable P r st) (h2 : MessageRoot.Aggregation.Reach P r st stF)
    (he : st.hist b = some e) (h0 : e.count c = 0) (hclk : ClockedBy S stF) :
    ¬ EndBranchVerified S (slRootOfEntry e) c D N := by
  intro hEnd
  have hlast := hEnd.lastInRoot
  have hon := hEnd.onTime
  have hafter := hEnd.rootAfterDeadline
  simp only [slRootOfEntry, h0, Nat.zero_sub] at hlast hafter
  subst hlast
  rw [hclk] at hon
  have := MessageRoot.Aggregation.aggregatesStrictAt_reach h1 h2 he c 0 (by omega)
  omega

theorem wf_of_messageRoot {P : MessageRoot.Aggregation.Params}
    {r : MessageRoot.Aggregation.TsRule} {stF : MessageRoot.Aggregation.State} {S : System}
    (hr : MessageRoot.Aggregation.Reachable P r stF) (hclk : ClockedBy S stF) (hT : WfTrees S) :
    Wf S where
  start := hT.start
  batch := hT.batch
  timeOrdered := fun c => by
    rw [hclk]
    exact MessageRoot.Aggregation.leafTime_mono (MessageRoot.Aggregation.aggInv_reachable hr) c
  capacity := hT.capacity

/-! ## (b) Imported roots are historical -/

theorem imported_roots_are_historical {P : MessageRoot.Aggregation.Params}
    {r : MessageRoot.Aggregation.TsRule} {stF : MessageRoot.Aggregation.State}
    {st : L2InteropRootStorage.State}
    (hrun : L2InteropRootStorage.Reach (AcceptedInRun P r stF) L2InteropRootStorage.empty st)
    {c : Chain} {n : ℕ} (hts : (st.entries c n).ts ≠ 0) :
    c = P.self ∧ ∃ (mst : MessageRoot.Aggregation.State) (e : MessageRoot.Aggregation.HistEntry),
      MessageRoot.Aggregation.Reachable P r mst ∧ MessageRoot.Aggregation.Reach P r mst stF
        ∧ mst.hist n = some e ∧ st.entries c n = ⟨e.root, e.ts⟩ := by
  have hroot : (st.entries c n).root ≠ 0 := fun h0 =>
    hts ((L2InteropRootStorage.ZeroTimestampIffAbsent _ _ hrun c n).mpr h0)
  obtain ⟨x, rx, hok, hc, hn, hsides, hst⟩ :=
    L2InteropRootStorage.EntriesAreAdmittedImports _ _ hrun c n hroot
  obtain ⟨mst, h1, h2, hself, e, he, -, hxs, hxts⟩ := hok
  refine ⟨hc ▸ hself, mst, e, h1, h2, hn ▸ he, ?_⟩
  have hre : rx = e.root := by
    rw [hsides] at hxs
    exact List.singleton_injective hxs
  rw [hst, hre, hxts]

/-! ## Witnesses

### The END branch, where `Aggregates` fails

The MessageRoot run continues `Contracts.MessageRoot.Aggregation.aggRunA4` (deployment on chain
`0`; chain `1` registered and seeded at time 1 in block 0, its batch 1 pushed at time 2 in block 1).
Block 2, at time 5: chain `2` is registered, which writes `historicalRoots[2]` counting chain 1's
two leaves; then, in the same block, chain 1 pushes its batch 2, at time 5. The root read
between the two is the witness root. -/

/-- Block 2 at time 5, after `addNewChain(2, 0)`. -/
def settleEndRead : MessageRoot.Aggregation.State :=
  (MessageRoot.Aggregation.aggRunA4.advance 5).addChain MessageRoot.Aggregation.aggWitnessParams 2 0

/-- … then chain 1's batch 2 pushed, in the same block. -/
def settleEndFinal : MessageRoot.Aggregation.State :=
  (settleEndRead.record 1 2 11).push MessageRoot.Aggregation.aggWitnessParams 1 2 11

/-- `historicalRoots[2]` as it stood in `settleEndRead`: timestamp 5, two leaves of chain 1. -/
def settleEndEntry : MessageRoot.Aggregation.HistEntry :=
  match settleEndRead.hist 2 with
  | some e => e
  | none => ⟨0, 0, fun _ => 0⟩

/-- Every tree `setup`, clocked by `settleEndFinal`. -/
def settleEndSystem : System := ⟨fun _ _ => setup, settleEndFinal.leafTime, fun _ _ => 0⟩

/-- One leg on chain 1, deadline 3. -/
def settleEndFlow : Flow := ⟨0, [⟨1, 2⟩], 3⟩

theorem settleEndRead_reach :
    MessageRoot.Aggregation.Reach MessageRoot.Aggregation.aggWitnessParams .strict
      MessageRoot.Aggregation.aggRunA4 settleEndRead := by
  refine MessageRoot.Aggregation.Reach.tail (MessageRoot.Aggregation.Reach.tail
    MessageRoot.Aggregation.Reach.refl (MessageRoot.Aggregation.Step.nextBlock 5 (by decide)))
    (MessageRoot.Aggregation.Step.addNewChain 2 0 ?_)
  unfold MessageRoot.Aggregation.State.Registered
  decide

theorem settleEndFinal_reach :
    MessageRoot.Aggregation.Reach MessageRoot.Aggregation.aggWitnessParams .strict
      settleEndRead settleEndFinal :=
  MessageRoot.Aggregation.Reach.tail MessageRoot.Aggregation.Reach.refl
    (MessageRoot.Aggregation.aggWitness_v32 2 11 (Or.inr (by decide)) (by decide) rfl rfl)

theorem settleEndRead_reachable :
    MessageRoot.Aggregation.Reachable MessageRoot.Aggregation.aggWitnessParams .strict
      settleEndRead :=
  MessageRoot.Aggregation.reachable_tail ⟨0, 1, MessageRoot.Aggregation.aggRunA4_reach⟩
    settleEndRead_reach

theorem settleEndFinal_reachable :
    MessageRoot.Aggregation.Reachable MessageRoot.Aggregation.aggWitnessParams .strict
      settleEndFinal :=
  MessageRoot.Aggregation.reachable_tail settleEndRead_reachable settleEndFinal_reach

theorem settleEnd_historical :
    HistoricalRootOf MessageRoot.Aggregation.aggWitnessParams .strict settleEndFinal
      (slRootOfEntry settleEndEntry) :=
  ⟨settleEndRead, 2, settleEndEntry, settleEndRead_reachable, settleEndFinal_reach, rfl, rfl⟩

theorem settleEndSystem_wfTrees : WfTrees settleEndSystem :=
  ⟨fun _ => Reaches.refl, fun _ _ => Reaches.refl,
    fun _ _ => by norm_num [settleEndSystem, setup]⟩

theorem settleEndSystem_not_aggregates :
    ¬ Aggregates settleEndSystem (slRootOfEntry settleEndEntry) := by
  intro hagg
  have := hagg 1 2 (by decide)
  revert this
  decide

theorem settleEnd_endBranch :
    EndBranchVerified settleEndSystem (slRootOfEntry settleEndEntry) 1 3 1 :=
  ⟨by decide, by decide, by decide⟩

theorem settleEnd_no_absenceBreak (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ¬ AbsenceBreak h z0 hl settleEndSystem 3 1 1
      ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩ := by
  rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
  · exact absurd hlate (by decide)
  · exact honest_proof_no_break h z0 hl setup 0 0 (by norm_num [setup]) hb

theorem settlement_roots_end_branch_witness : Properties.SettlementRootsEndBranchWitness := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  have hT := settleEndSystem_wfTrees
  have hR := settleEnd_historical
  refine ⟨MessageRoot.Aggregation.aggWitnessParams, settleEndFinal, settleEndSystem,
    slRootOfEntry settleEndEntry, fun _ _ => 1, settleEndFlow, ⟨1, 2⟩, 1,
    ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩, settleEndFinal_reachable, rfl,
    hT, wf_of_messageRoot settleEndFinal_reachable rfl hT, hR,
    historicalRoot_aggregatesBefore hR rfl, settleEndSystem_not_aggregates,
    List.mem_singleton_self _, settleEnd_endBranch, by decide,
    Or.inr ⟨settleEnd_endBranch, ?_⟩, settleEnd_no_absenceBreak h z0 hl, ?_,
    ⟨settleEndRead, 2, settleEndEntry, 2, settleEndRead_reachable, settleEndFinal_reach, rfl, rfl,
      by decide, Or.inr (by decide), by decide⟩⟩
  · show AbsenceAccepted h z0 hl setup 0 1 _
    exact setup_absence_accepted h z0 hl h1
  · intro n _ hmem
    exact not_mem_setup h1 hmem

/-! ### The same run, with a `RootBacking` and the honest last-batch path -/

/-- A `RootBacking` of the witness root under `demoHash`: chain 1's two leaves are `[5, 7]` at
height 2, as in `demoBacking`; every other chain gets the `count - 1 + 1` leaves the root's
`upTo` placeholder asks for. -/
def settleEndBacking : RootBacking demoHash 0 (slRootOfEntry settleEndEntry) where
  leaves := fun c => if c = 1 then [5, 7] else List.replicate (settleEndEntry.count c - 1 + 1) 5
  height := fun c => if c = 1 then 2 else settleEndEntry.count c
  upToLast := by
    intro c
    by_cases hc : c = 1
    · subst hc
      show [(5 : UInt256), 7].length = settleEndEntry.count 1 - 1 + 1
      decide
    · simp [hc, slRootOfEntry]
  capacity := by
    intro c
    by_cases hc : c = 1
    · subst hc
      decide
    · simp only [hc, ite_false, List.length_replicate]
      rcases Nat.eq_zero_or_pos (settleEndEntry.count c) with h0 | hpos
      · rw [h0]
        decide
      · have := (Nat.lt_two_pow_self (n := settleEndEntry.count c))
        omega

theorem settleEndBacking_leaves_one : settleEndBacking.leaves 1 = [5, 7] := by decide

theorem settleEndBacking_height_one : settleEndBacking.height 1 = 2 := by decide

theorem settleEnd_lastBatch :
    LastBatchAccepted settleEndBacking 1 1 (honestSibs demoHash 0 [5, 7] 1) 7 := by
  have d := demo_endBranchAccepted.lastBatch
  refine ⟨?_, ?_, ?_⟩
  · rw [settleEndBacking_leaves_one]; exact d.inRange
  · rw [settleEndBacking_leaves_one, settleEndBacking_height_one]; exact d.authenticated
  · rw [settleEndBacking_height_one]; exact d.zeroRightSiblings

theorem settleEnd_endBranchAccepted :
    EndBranchAccepted settleEndBacking settleEndSystem 1 3 1 (honestSibs demoHash 0 [5, 7] 1) 7 :=
  ⟨by decide, by decide, settleEnd_lastBatch⟩

theorem settlement_roots_accepted_witness : Properties.SettlementRootsAcceptedWitness := by
  intro z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  refine ⟨demoHash, MessageRoot.Aggregation.aggWitnessParams, settleEndFinal, settleEndSystem, 0,
    slRootOfEntry settleEndEntry, settleEndBacking, fun _ _ => 1, settleEndFlow, ⟨1, 2⟩, 1,
    ⟨⟨0, 0, 0⟩, 0, honestSibs demoHash z0 (leafHashes hl setup) 0, 0⟩,
    honestSibs demoHash 0 [5, 7] 1, 7, settleEndFinal_reachable, rfl, settleEndSystem_wfTrees,
    wf_of_messageRoot settleEndFinal_reachable rfl settleEndSystem_wfTrees, settleEnd_historical,
    historicalRoot_aggregatesBefore settleEnd_historical rfl, settleEndSystem_not_aggregates,
    List.mem_singleton_self _,
    Or.inr ⟨settleEnd_endBranchAccepted, ?_⟩, settleEnd_endBranchAccepted, ?_, ?_,
    settleEnd_no_absenceBreak demoHash z0 hl, ?_, ?_, ?_⟩
  · show AbsenceAccepted demoHash z0 hl setup 0 1 _
    exact setup_absence_accepted demoHash z0 hl h1
  · show EntriesNotEmpty 0 (settleEndBacking.leaves 1)
    rw [settleEndBacking_leaves_one]
    exact demo_entriesNotEmpty
  · show PairInjOn demoHash (fun q => TreePair demoHash 0 (settleEndBacking.leaves 1)
        (settleEndBacking.height 1) q
      ∨ VerifiedPair demoHash (honestSibs demoHash 0 [5, 7] 1) (settleEndBacking.height 1) 1 7 q)
    rw [settleEndBacking_leaves_one, settleEndBacking_height_one]
    exact demo_pairInjOn
  · show ¬ PinnedBreak demoHash 0 (settleEndBacking.leaves 1) 1
    rw [settleEndBacking_leaves_one]
    exact demo_no_pinned_break_any 1
  · show ¬ PathCollision demoHash 0 (settleEndBacking.leaves 1) (honestSibs demoHash 0 [5, 7] 1) 0
      (settleEndBacking.height 1) 1 7
    rw [settleEndBacking_leaves_one, settleEndBacking_height_one]
    exact honest_walk_no_collision demoHash 0 [5, 7] 2 1
  · intro n _ hmem
    exact not_mem_setup h1 hmem

/-! ### A run with an execution and a root-verified refund of another flow

A deployment on chain `5`, so chains `0` and `1` are registered by `addNewChain`. Block 0 at time 0:
both registered and seeded (so each has a leaf at time 0). Block 1 at time 1: chain 1's batch 1
pushed. The system has `mixedSystem 1`'s trees, clocked by the run. -/

/-- A deployment on chain `5`, shared root `1`, every other hash `0`. -/
def settleRefundParams : MessageRoot.Aggregation.Params :=
  ⟨5, ⟨fun _ _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 1⟩⟩

/-- Block 0 at time 0: chains 0 and 1 registered at start 0. -/
def settleRefundRegistered : MessageRoot.Aggregation.State :=
  ((MessageRoot.Aggregation.init settleRefundParams 0 0).addChain settleRefundParams 0 0).addChain
    settleRefundParams 1 0

/-- … both seeded with genesis root `7`. -/
def settleRefundSeeded : MessageRoot.Aggregation.State :=
  (settleRefundRegistered.seed settleRefundParams 0 7).seed settleRefundParams 1 7

/-- Block 1 at time 1: chain 1's batch 1 pushed. -/
def settleRefundFinal : MessageRoot.Aggregation.State :=
  ((settleRefundSeeded.advance 1).record 1 1 9).push settleRefundParams 1 1 9

/-- `historicalRoots[1]` of `settleRefundFinal`: timestamp 1. -/
def settleRefundEntry : MessageRoot.Aggregation.HistEntry :=
  match settleRefundFinal.hist 1 with
  | some e => e
  | none => ⟨0, 0, fun _ => 0⟩

theorem settleRefundFinal_reach :
    MessageRoot.Aggregation.Reach settleRefundParams .strict
      (MessageRoot.Aggregation.init settleRefundParams 0 0) settleRefundFinal := by
  have s1 : MessageRoot.Aggregation.Step settleRefundParams .strict
      (MessageRoot.Aggregation.init settleRefundParams 0 0)
      ((MessageRoot.Aggregation.init settleRefundParams 0 0).addChain settleRefundParams 0 0) :=
    MessageRoot.Aggregation.Step.addNewChain 0 0
      (by rw [MessageRoot.Aggregation.registered_init_iff]; decide)
  have s2 : MessageRoot.Aggregation.Step settleRefundParams .strict
      ((MessageRoot.Aggregation.init settleRefundParams 0 0).addChain settleRefundParams 0 0)
      settleRefundRegistered :=
    MessageRoot.Aggregation.Step.addNewChain 1 0
      (by unfold MessageRoot.Aggregation.State.Registered; decide)
  have s3 : MessageRoot.Aggregation.Step settleRefundParams .strict settleRefundRegistered
      (settleRefundRegistered.seed settleRefundParams 0 7) :=
    MessageRoot.Aggregation.Step.seedGenesisRoot 0 7 ⟨by decide, Or.inr (by decide), rfl, rfl⟩
  have s4 : MessageRoot.Aggregation.Step settleRefundParams .strict
      (settleRefundRegistered.seed settleRefundParams 0 7) settleRefundSeeded :=
    MessageRoot.Aggregation.Step.seedGenesisRoot 1 7 ⟨by decide, Or.inr (by decide), rfl, rfl⟩
  have s5 : MessageRoot.Aggregation.Step settleRefundParams .strict settleRefundSeeded
      (settleRefundSeeded.advance 1) :=
    MessageRoot.Aggregation.Step.nextBlock 1 (by decide)
  have s6 : MessageRoot.Aggregation.Step settleRefundParams .strict (settleRefundSeeded.advance 1)
      settleRefundFinal :=
    MessageRoot.Aggregation.Step.addChainBatchRootV32 1 1 9
      ⟨Or.inr (by decide), by decide, rfl, rfl⟩
  exact MessageRoot.Aggregation.Reach.tail (MessageRoot.Aggregation.Reach.tail
    (MessageRoot.Aggregation.Reach.tail (MessageRoot.Aggregation.Reach.tail
      (MessageRoot.Aggregation.Reach.tail (MessageRoot.Aggregation.Reach.tail
        MessageRoot.Aggregation.Reach.refl s1) s2) s3) s4) s5) s6

/-- `mixedSystem 1`'s trees, clocked by `settleRefundFinal`. -/
def settleRefundSystem : System := { mixedSystem 1 with time := settleRefundFinal.leafTime }

/-- Some `RootBacking` exists for every root: `upTo c + 1` copies of `0`, at height
`upTo c + 1`. -/
def settleReplicaBacking (h : Hash) (ze : UInt256) (R : SlRoot) : RootBacking h ze R where
  leaves := fun c => List.replicate (R.upTo c + 1) 0
  height := fun c => R.upTo c + 1
  upToLast := fun _ => List.length_replicate
  capacity := fun c => by
    rw [List.length_replicate]
    exact Nat.lt_two_pow_self.le

/-- The two-flow run of `Proofs/Refund.lean`, with its refund verified against `R`. -/
theorem settle_twoFlow_runAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (roots : SlRoot → Prop) (R : SlRoot) (hR : roots R)
    (href : LegRefundableVerifiedBy h z0 hl (fun _ _ => 1) S R (mixedFlow 1 1 2) ⟨1, 2⟩ 1
      ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩) :
    ReachLogAt h z0 hl (fun _ _ => 1) lengthFlowHash S roots emptyManagers twoFlowMs
      [twoFlowCall h z0 hl] := by
  have hmem : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs := by simp [mixedFlow]
  have happ : ReachLogAt h z0 hl (fun _ _ => 1) lengthFlowHash S roots emptyManagers twoFlowM1 [] :=
    ReachLogAt.append (c := 1) (f := 1) (b := 2) ReachLogAt.refl rfl
  have hguard : AuthorizeGuard (twoFlowM1 1) 1 2 := by
    show (twoFlowM1 1).legState 1 2 = .Committed
    simp [twoFlowM1, setAt, Manager.set]
  exact ReachLogAt.authorize (twoFlowCall h z0 hl) R happ hR
    ⟨lengthFlowHash_checks_mixed, hmem, hmem, href⟩ hguard

/-- The logged call of the two-flow run marks an obligation other than `subsetFlow 0 1`'s, so no
`RefundBreak` names `subsetFlow 0 1`'s obligation, in any system. -/
theorem settle_twoFlow_no_refundBreak (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (ev : GateEvidence) :
    ¬ RefundBreak h z0 hl lengthFlowHash S (subsetFlow 0 1) ev
      (obligationOf (subsetFlow 0 1) ⟨0, 1⟩) [twoFlowCall h z0 hl] := by
  have hneq : obligationOf (twoFlowCall h z0 hl).flow (twoFlowCall h z0 hl).leg
      ≠ obligationOf (subsetFlow 0 1) ⟨0, 1⟩ := by
    intro he
    have hid : (1 : UInt256) = 0 := congrArg Obligation.flowId he
    exact absurd hid (by decide)
  intro hb
  cases hb with
  | flowIdClash a ha hobl _ =>
    rw [List.mem_singleton] at ha; subst ha; exact hneq hobl
  | inclusion a ha hobl _ _ =>
    rw [List.mem_singleton] at ha; subst ha; exact hneq hobl
  | absence a ha hobl _ _ =>
    rw [List.mem_singleton] at ha; subst ha; exact hneq hobl

theorem settle_twoFlow_not_refunded :
    ¬ Refunded twoFlowMs (obligationOf (subsetFlow 0 1) ⟨0, 1⟩) := by
  show ¬ 2 ≤ rank (stateOf (setAt twoFlowM1 1 ((twoFlowM1 1).set 1 2 .Revertable)) ⟨0, 1, 0⟩)
  have hne : (⟨0, 1, 0⟩ : Obligation) ≠ ⟨1, 2, 1⟩ := by decide
  rw [stateOf_setAt_other hne]
  show ¬ 2 ≤ rank (stateOf (setAt emptyManagers 1 ((emptyManagers 1).set 1 2 .Committed))
    ⟨0, 1, 0⟩)
  rw [stateOf_setAt_other hne, stateOf_emptyManagers]
  simp [rank]

theorem settlement_roots_refund_run_witness : Properties.SettlementRootsRefundRunWitness := by
  intro h z0 hl
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  have hS := mixedSystem_wf h1
  have hr : MessageRoot.Aggregation.Reachable settleRefundParams .strict settleRefundFinal :=
    ⟨0, 0, settleRefundFinal_reach⟩
  have hT : WfTrees settleRefundSystem := ⟨hS.start, hS.batch, hS.capacity⟩
  obtain ⟨⟨hmem, hchk, hfin⟩, -⟩ :=
    subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset
  have hex : ExecutedViaBy h z0 hl (fun _ _ => 1) lengthFlowHash settleRefundSystem
      (subsetFlow 0 1) (fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1)) ⟨0, 1⟩ := by
    refine ⟨hmem, hchk, fun l hl' => ?_⟩
    obtain ⟨_, hacc⟩ := hfin l hl'
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    exact ⟨show settleRefundFinal.leafTime 0 0 ≤ 0 by decide, hacc⟩
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  have href : LegRefundableVerifiedBy h z0 hl (fun _ _ => 1) settleRefundSystem
      (slRootOfEntry settleRefundEntry) (mixedFlow 1 1 2) ⟨1, 2⟩ 1
      ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩ := by
    refine Or.inl ⟨⟨by decide, by decide⟩, ?_⟩
    show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
      (beginHeight (mixedSystem 1) 1 1) 1 _
    rw [hbegin, hbeginH]
    exact setup_absence_accepted h z0 hl h1
  have hR : HistoricalRootOf settleRefundParams .strict settleRefundFinal
      (slRootOfEntry settleRefundEntry) :=
    ⟨settleRefundFinal, 1, settleRefundEntry, hr, MessageRoot.Aggregation.Reach.refl, rfl, rfl⟩
  exact ⟨settleRefundParams, settleRefundFinal, 1, settleRefundEntry, fun _ _ => 1, lengthFlowHash,
    settleRefundSystem, subsetFlow 0 1, _, ⟨0, 1⟩, twoFlowMs, [twoFlowCall h z0 hl], hr, rfl, rfl,
    hT, wf_of_messageRoot hr rfl hT, hR,
    ⟨settleReplicaBacking h 0 (slRootOfEntry settleRefundEntry)⟩,
    fun _ hR' => historicalRoot_aggregatesBefore hR' rfl, hex,
    settle_twoFlow_runAt h z0 hl _ _ _ hR href, List.cons_ne_nil _ _,
    settle_twoFlow_no_refundBreak h z0 hl _ _, settle_twoFlow_not_refunded⟩

/-! ### An accepted import -/

/-- The import of `historicalRoots[1]` of `aggRunA4` (root `1`, timestamp `2`) on chain `0`. -/
def settleImport : L2InteropRootStorage.RootIn := ⟨0, 1, 2, [1]⟩

theorem settlement_roots_import_witness : Properties.SettlementRootsImportWitness := by
  have hr : MessageRoot.Aggregation.Reachable MessageRoot.Aggregation.aggWitnessParams .strict
      MessageRoot.Aggregation.aggRunA4 :=
    ⟨0, 1, MessageRoot.Aggregation.aggRunA4_reach⟩
  have hacc : AcceptedInRun MessageRoot.Aggregation.aggWitnessParams .strict
      MessageRoot.Aggregation.aggRunA4 settleImport :=
    ⟨MessageRoot.Aggregation.aggRunA4, hr, MessageRoot.Aggregation.Reach.refl, rfl, _, rfl,
      by decide, rfl, rfl⟩
  have hg : L2InteropRootStorage.AddGuard L2InteropRootStorage.empty settleImport 1 :=
    ⟨rfl, by decide, by decide, rfl⟩
  refine ⟨MessageRoot.Aggregation.aggWitnessParams, MessageRoot.Aggregation.aggRunA4,
    L2InteropRootStorage.empty.write settleImport 1, 1, 1, hr,
    L2InteropRootStorage.Reach.tail L2InteropRootStorage.Reach.refl
      (L2InteropRootStorage.Step.single settleImport 1 hacc hg), by decide, ?_⟩
  unfold L2InteropRootStorage.State.TimeoutRootPasses
  decide

/-! ## The property theorems -/

theorem VerifiedImpliesRefundableBefore : Properties.VerifiedImpliesRefundableBefore :=
  fun _ _ _ _ _ _ hagg _ _ hv => verified_implies_refundable_before hagg hv
theorem TimeoutMeansMissedDeadlineOrBreakBefore :
    Properties.TimeoutMeansMissedDeadlineOrBreakBefore :=
  fun _ _ _ _ _ hS _ hagg _ _ _ _ hv => timeout_means_missed_deadline_or_break_before hS hagg hv
theorem TimeoutExcludesFinalityOrBreakBefore : Properties.TimeoutExcludesFinalityOrBreakBefore :=
  fun _ _ _ _ _ hS _ hagg _ _ _ _ hv n p' =>
    timeout_excludes_finality_or_break_before hS hagg hv n p'
theorem AcceptedTimeoutMeansMissedDeadlineOrBreakBefore :
    Properties.AcceptedTimeoutMeansMissedDeadlineOrBreakBefore :=
  fun _ _ _ _ _ hS _ _ _ hagg _ _ _ _ _ _ ha =>
    accepted_timeout_means_missed_deadline_or_break_before hS hagg ha
theorem AcceptedImpliesRefundablePinnedBefore : Properties.AcceptedImpliesRefundablePinnedBefore :=
  fun _ _ _ _ _ _ _ _ hagg _ _ _ _ _ _ ha => accepted_implies_refundable_pinned_before hagg ha
theorem AcceptedImpliesRefundableOnBefore : Properties.AcceptedImpliesRefundableOnBefore :=
  fun _ _ _ _ _ _ _ _ hagg _ _ _ _ _ _ hsep hinj ha =>
    accepted_implies_refundable_on_before hagg hsep hinj ha
theorem VerifiedTimeoutAuthorizesBefore : Properties.VerifiedTimeoutAuthorizesBefore :=
  fun _ _ _ _ _ _ hagg _ _ hmem hv => verified_timeout_authorizes_before hagg hmem hv
theorem AcceptedTimeoutAuthorizesPinnedBefore : Properties.AcceptedTimeoutAuthorizesPinnedBefore :=
  fun _ _ _ _ _ _ _ _ hagg _ _ _ _ _ _ hmem ha => accepted_timeout_authorizes_pinned_before hagg hmem ha
theorem ExecutedExcludesAcceptedRefundOrBreakBefore :
    Properties.ExecutedExcludesAcceptedRefundOrBreakBefore :=
  fun _ _ _ _ _ _ hS _ _ _ hagg _ _ _ hex other hother N p sibs x =>
    executed_excludes_accepted_refund_or_break_before hS hagg hex other hother N p sibs x
theorem ReachLogAtProjects : Properties.ReachLogAtProjects :=
  fun _ _ _ _ _ _ _ hroots _ _ _ hr => reachLog_of_reachLogAt hroots hr
theorem ExecutedObligationNeverRefundedOrBreakAt :
    Properties.ExecutedObligationNeverRefundedOrBreakAt :=
  fun _ _ _ _ _ _ hS _ hroots _ _ _ hex _ _ hr =>
    executed_freezes_flow_or_break hS hex (reachLog_of_reachLogAt hroots hr) _ rfl
theorem OneExecutionFreezesTheFlowOrBreakAt : Properties.OneExecutionFreezesTheFlowOrBreakAt :=
  fun _ _ _ _ _ _ hS _ hroots _ _ _ hex _ _ hr _ _ =>
    executed_freezes_flow_or_break hS hex (reachLog_of_reachLogAt hroots hr) _ rfl

theorem ImportedRootsAreHistorical : Properties.ImportedRootsAreHistorical :=
  fun _ _ _ _ hrun _ _ hts => imported_roots_are_historical hrun hts

theorem ImportedTimeoutRootAggregatesBefore : Properties.ImportedTimeoutRootAggregatesBefore := by
  intro P r stF st hrun c n D hpass
  obtain ⟨-, mst, e, h1, h2, he, hst⟩ := imported_roots_are_historical hrun hpass.1
  have hR : HistoricalRootOf P r stF (slRootOfEntry e) := ⟨mst, n, e, h1, h2, he, rfl⟩
  have hts : (st.entries c n).ts = e.ts := by rw [hst]
  refine ⟨slRootOfEntry e, hR, hts.symm, ?_, fun S hclk => historicalRoot_aggregatesBefore hR hclk⟩
  have := hpass.2
  rw [hts] at this
  exact this

theorem HistoricalRootAggregatesBefore : Properties.HistoricalRootAggregatesBefore :=
  fun _ _ _ _ _ hR hclk => historicalRoot_aggregatesBefore hR hclk
theorem HistoricalRootAggregatesStrictTs : Properties.HistoricalRootAggregatesStrictTs :=
  fun _ _ _ _ _ hr he hclk => historicalRoot_aggregates_strictTs hr he hclk
theorem UncountedChainHasNoEndBranch : Properties.UncountedChainHasNoEndBranch :=
  fun _ _ _ _ _ _ _ _ _ _ h1 h2 he h0 hclk => uncounted_chain_has_no_endBranch h1 h2 he h0 hclk
theorem WfFromMessageRoot : Properties.WfFromMessageRoot :=
  fun _ _ _ _ hr hclk hT => wf_of_messageRoot hr hclk hT

theorem TimeoutMeansMissedDeadlineOrBreakFromMessageRoot :
    Properties.TimeoutMeansMissedDeadlineOrBreakFromMessageRoot :=
  fun _ _ _ _ _ _ _ _ hr hclk hT _ hR _ _ _ _ hv =>
    timeout_means_missed_deadline_or_break_before (wf_of_messageRoot hr hclk hT)
      (historicalRoot_aggregatesBefore hR hclk) hv
theorem TimeoutExcludesFinalityOrBreakFromMessageRoot :
    Properties.TimeoutExcludesFinalityOrBreakFromMessageRoot :=
  fun _ _ _ _ _ _ _ _ hr hclk hT _ hR _ _ _ _ hv n p' =>
    timeout_excludes_finality_or_break_before (wf_of_messageRoot hr hclk hT)
      (historicalRoot_aggregatesBefore hR hclk) hv n p'
theorem AcceptedTimeoutMeansMissedDeadlineOrBreakFromMessageRoot :
    Properties.AcceptedTimeoutMeansMissedDeadlineOrBreakFromMessageRoot :=
  fun _ _ _ _ _ _ _ _ hr hclk hT _ _ _ hR _ _ _ _ _ _ ha =>
    accepted_timeout_means_missed_deadline_or_break_before (wf_of_messageRoot hr hclk hT)
      (historicalRoot_aggregatesBefore hR hclk) ha
theorem ExecutedExcludesAcceptedRefundOrBreakFromMessageRoot :
    Properties.ExecutedExcludesAcceptedRefundOrBreakFromMessageRoot :=
  fun _ _ _ _ _ _ _ _ _ hr hclk hT _ _ _ hR _ _ _ hex other hother N p sibs x =>
    executed_excludes_accepted_refund_or_break_before (wf_of_messageRoot hr hclk hT)
      (historicalRoot_aggregatesBefore hR hclk) hex other hother N p sibs x
theorem ExecutedObligationNeverRefundedOrBreakFromMessageRoot :
    Properties.ExecutedObligationNeverRefundedOrBreakFromMessageRoot :=
  fun _ _ _ _ _ _ _ _ _ hr hclk hT _ _ _ hex _ _ hrun =>
    executed_freezes_flow_or_break (wf_of_messageRoot hr hclk hT) hex
      (reachLog_of_reachLogAt (fun _ hR => historicalRoot_aggregatesBefore hR hclk) hrun) _ rfl

theorem SettlementRootsEndBranchWitness : Properties.SettlementRootsEndBranchWitness :=
  settlement_roots_end_branch_witness
theorem SettlementRootsAcceptedWitness : Properties.SettlementRootsAcceptedWitness :=
  settlement_roots_accepted_witness
theorem SettlementRootsRefundRunWitness : Properties.SettlementRootsRefundRunWitness :=
  settlement_roots_refund_run_witness
theorem SettlementRootsImportWitness : Properties.SettlementRootsImportWitness :=
  settlement_roots_import_witness

end Contracts.SettlementRoots
