import EraSpec.Protocol.InteropAtomicity.Properties.AggregatesWeak
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund
import EraSpec.Contracts.MessageRoot.Proofs.Aggregation
import EraSpec.Contracts.L2InteropRootStorage.Proofs.Model

/-!
# Proofs: the timeout and refund headlines from the settlement layer's own roots

`isLastOnTime_of_verified_weak` is the only new step: the batch `m` after the proven one that
the END branch must show late is past the root's last batch, so weak aggregation puts it at or
after the root's creation, which is after the deadline. Everything else re-runs the existing
proofs (`Proofs/Timeout.lean`, `Proofs/Refund.lean`) through that step instead of
`isLastOnTime_of_verified`. The MessageRoot side is `Contracts.MessageRoot.aggregatesStrictAt_reach`.
-/

namespace Contracts.Timeout

open Contracts.InteropCommitmentTree Contracts.Atomicity MerkleSpec MerkleSpec.Verifier
open MerkleSpec.LastLeaf IMTAbstract

/-! ## (f) The weak form suffices -/

theorem aggregatesWeak_of_aggregates {S : System} {R : SlRoot} (hagg : Aggregates S R) :
    AggregatesWeak S R := by
  intro c n hlt
  by_contra hcon
  have := hagg c n (le_of_lt (Nat.lt_of_not_le hcon))
  omega

theorem aggregatesWeak_iff {S : System} {R : SlRoot} :
    AggregatesWeak S R ↔ ∀ c n, S.time c n < R.created → n ≤ R.upTo c := by
  constructor
  · intro h c n hlt
    by_contra hcon
    have := h c n (Nat.lt_of_not_le hcon)
    omega
  · intro h c n hlt
    by_contra hcon
    have := h c n (Nat.lt_of_not_le hcon)
    omega

/-- **"LAST BATCH IN THIS ROOT" MEANS "LAST BATCH IN TIME", FROM THE WEAK FORM.** -/
theorem isLastOnTime_of_verified_weak {S : System} {R : SlRoot} (hagg : AggregatesWeak S R)
    {c : Chain} {D N : ℕ} (he : EndBranchVerified S R c D N) : IsLastOnTime S c D N := by
  refine ⟨he.onTime, fun m hm => ?_⟩
  have h1 := hagg c m (by rw [← he.lastInRoot]; exact hm)
  have h2 := he.rootAfterDeadline
  omega

theorem verified_implies_refundable_weak {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {R : SlRoot} (hagg : AggregatesWeak S R)
    {F : Flow} {leg : FlowLeg} (hv : LegRefundableVerified h z0 hl cv S R F leg) :
    LegRefundable h z0 hl cv S F leg := by
  obtain ⟨N, p, hbr⟩ := hv
  refine ⟨N, p, ?_⟩
  rcases hbr with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact Or.inl ⟨hb.late, habs⟩
  · exact Or.inr ⟨isLastOnTime_of_verified_weak hagg he, habs⟩

theorem refundableBy_of_verifiedBy_weak {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {R : SlRoot} (hagg : AggregatesWeak S R)
    {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    (hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p) :
    LegRefundableBy h z0 hl cv S F leg N p := by
  rcases hv with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact Or.inl ⟨hb.late, habs⟩
  · exact Or.inr ⟨isLastOnTime_of_verified_weak hagg he, habs⟩

theorem timeout_means_missed_deadline_or_break_weak {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {R : SlRoot} (hagg : AggregatesWeak S R)
    {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    (hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p) :
    (∀ n, S.time leg.chain n ≤ F.deadline →
        legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
      ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p := by
  by_cases hb : AbsenceBreak h z0 hl S F.deadline leg.chain N p
  · exact Or.inr hb
  · refine Or.inl fun n hon hmem => ?_
    rcases member_not_refundable_or_break hS hon hmem N p with hn | hb'
    · exact hn (refundableBy_of_verifiedBy_weak hagg hv)
    · exact hb hb'

theorem timeout_excludes_finality_or_break_weak {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} (hS : Wf S) {R : SlRoot} (hagg : AggregatesWeak S R)
    {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    (hv : LegRefundableVerifiedBy h z0 hl cv S R F leg N p) (n : ℕ) (p' : ImtProof) :
    ¬ LegFinalizedBy h z0 hl cv S F leg n p'
      ∨ InclusionBreak h z0 hl S leg.chain n p'
      ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p := by
  by_cases hfin : LegFinalizedBy h z0 hl cv S F leg n p'
  · obtain ⟨hon, hacc⟩ := hfin
    rcases finality_means_membership_or_break hacc with hmem | hb
    · rcases member_not_refundable_or_break hS hon hmem N p with hn | hb'
      · exact absurd (refundableBy_of_verifiedBy_weak hagg hv) hn
      · exact Or.inr (Or.inr hb')
    · exact Or.inr (Or.inl hb)
  · exact Or.inl hfin

theorem accepted_timeout_means_missed_deadline_or_break_weak {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {S : System} (hS : Wf S) {ze : UInt256} {R : SlRoot}
    {B : RootBacking h ze R} (hagg : AggregatesWeak S R) {F : Flow} {leg : FlowLeg} {N : ℕ}
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
  · rcases timeout_means_missed_deadline_or_break_weak hS hagg hv with hm | hb
    · exact Or.inl hm
    · exact Or.inr (Or.inl hb)
  · exact Or.inr (Or.inr hrest)

theorem accepted_implies_refundable_pinned_weak {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : AggregatesWeak S R) {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    {sibs : ℕ → UInt256} {x : UInt256}
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    LegRefundable h z0 hl cv S F leg ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
  rcases ha with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact Or.inl (verified_implies_refundable_weak hagg ⟨N, p, Or.inl ⟨hb, habs⟩⟩)
  · rcases endBranch_of_accepted_pinned he with hv | hrest
    · exact Or.inl (verified_implies_refundable_weak hagg ⟨N, p, Or.inr ⟨hv, habs⟩⟩)
    · exact Or.inr ⟨he, hrest⟩

theorem accepted_implies_refundable_on_weak {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : AggregatesWeak S R) {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    {sibs : ℕ → UInt256} {x : UInt256}
    (hsep : EntriesNotEmpty ze (B.leaves leg.chain))
    (hinj : PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
      ∨ VerifiedPair h sibs (B.height leg.chain) N x q))
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    LegRefundable h z0 hl cv S F leg := by
  rcases ha with ⟨hb, habs⟩ | ⟨he, habs⟩
  · exact verified_implies_refundable_weak hagg ⟨N, p, Or.inl ⟨hb, habs⟩⟩
  · exact verified_implies_refundable_weak hagg
      ⟨N, p, Or.inr ⟨endBranch_of_accepted_on hsep hinj he, habs⟩⟩

/-! ## (j) The settlement layer supplies it -/

theorem historicalRoot_aggregatesWeak {P : MessageRoot.Params} {r : MessageRoot.TsRule}
    {stF : MessageRoot.State} {R : SlRoot} {S : System} (hR : HistoricalRootOf P r stF R)
    (hclk : ClockedBy S stF) : AggregatesWeak S R := by
  obtain ⟨st, b, e, h1, h2, he, rfl⟩ := hR
  have hstrict := MessageRoot.aggregatesStrictAt_reach h1 h2 he
  intro c n hlt
  simp only [slRootOfEntry] at hlt ⊢
  rw [hclk]
  by_contra hcon
  have := hstrict c n (Nat.lt_of_not_le hcon)
  omega

theorem historicalRoot_aggregates_strictTs {P : MessageRoot.Params} {st : MessageRoot.State}
    {b : ℕ} {e : MessageRoot.HistEntry} {S : System} (hr : MessageRoot.Reachable P .strict st)
    (he : st.hist b = some e) (hclk : ClockedBy S st) : Aggregates S (slRootOfEntry e) := by
  intro c n hle
  simp only [slRootOfEntry] at hle ⊢
  rw [hclk] at hle
  have := MessageRoot.aggregatesAt_strict hr he c n hle
  omega

theorem wf_of_messageRoot {P : MessageRoot.Params} {r : MessageRoot.TsRule}
    {stF : MessageRoot.State} {S : System} (hr : MessageRoot.Reachable P r stF)
    (hclk : ClockedBy S stF) (hT : WfTrees S) : Wf S where
  start := hT.start
  batch := hT.batch
  timeOrdered := fun c => by
    rw [hclk]; exact MessageRoot.leafTime_mono (MessageRoot.aggInv_reachable hr) c
  capacity := hT.capacity

/-! ## (i) Imported roots are historical -/

theorem imported_roots_are_historical {P : MessageRoot.Params} {r : MessageRoot.TsRule}
    {stF : MessageRoot.State} {st : L2InteropRootStorage.State}
    (hrun : L2InteropRootStorage.Reach (AcceptedInRun P r stF) L2InteropRootStorage.empty st)
    {c : Chain} {n : ℕ} (hts : (st.entries c n).ts ≠ 0) :
    c = P.self ∧ ∃ (mst : MessageRoot.State) (e : MessageRoot.HistEntry),
      MessageRoot.Reachable P r mst ∧ MessageRoot.Reach P r mst stF ∧ mst.hist n = some e
        ∧ st.entries c n = ⟨e.root, e.ts⟩ := by
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

end Contracts.Timeout

namespace Contracts.Refund

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager

/-! ## (f) The refund side -/

theorem verified_timeout_authorizes_weak {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {R : SlRoot} (hagg : AggregatesWeak S R)
    {F : Flow} {leg : FlowLeg} (hmem : leg ∈ F.legs)
    (hv : LegRefundableVerified h z0 hl cv S R F leg) : RefundAuthorized h z0 hl cv S F :=
  ⟨leg, hmem, verified_implies_refundable_weak hagg hv⟩

theorem accepted_timeout_authorizes_pinned_weak {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : AggregatesWeak S R) {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    {sibs : ℕ → UInt256} {x : UInt256} (hmem : leg ∈ F.legs)
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    RefundAuthorized h z0 hl cv S F ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
  rcases accepted_implies_refundable_pinned_weak hagg ha with hr | hrest
  · exact Or.inl ⟨leg, hmem, hr⟩
  · exact Or.inr hrest

theorem executed_excludes_accepted_refund_or_break_weak {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {ze : UInt256}
    {R : SlRoot} {B : RootBacking h ze R} (hagg : AggregatesWeak S R) {F : Flow}
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
      · exact Or.inl (refundableBy_of_verifiedBy_weak hagg (Or.inl ⟨hb, habs⟩))
      · rcases endBranch_of_accepted_pinned he with hver | hrest
        · exact Or.inl (refundableBy_of_verifiedBy_weak hagg (Or.inr ⟨hver, habs⟩))
        · exact Or.inr ⟨he, hrest⟩
    rcases hv with hr | hrest
    · rcases executed_excludes_any_refund_or_break hS hex other hother N p with hn | hb | hb
      · exact absurd hr hn
      · exact Or.inl hb
      · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hrest)
  · exact Or.inl ha

theorem reachLog_of_reachLogAt {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {roots : SlRoot → Prop} (hroots : ∀ R, roots R → AggregatesWeak S R)
    {Ms Ns : Managers} {log : List AuthCall} (hr : ReachLogAt h z0 hl cv fh S roots Ms Ns log) :
    ReachLog h z0 hl cv fh S Ms Ns log := by
  induction hr with
  | refl => exact ReachLog.refl
  | append _ hg ih => exact ReachLog.append ih hg
  | authorize a R _ hR hv hg ih =>
    obtain ⟨hchk, hleg, hmiss, href⟩ := hv
    exact ReachLog.authorize a ih
      ⟨hchk, hleg, hmiss, refundableBy_of_verifiedBy_weak (hroots R hR) href⟩ hg
  | claim _ hg ih => exact ReachLog.claim ih hg

end Contracts.Refund

/-! ## Witnesses -/

namespace Contracts.Timeout

open Contracts.InteropCommitmentTree Contracts.Atomicity MerkleSpec MerkleSpec.Verifier
open MerkleSpec.LastLeaf IMTAbstract

/-- A root created at time 1 holding only each chain's batch 0. -/
def aggWeakRoot : SlRoot := ⟨1, fun _ => 0⟩

theorem aggWeakRoot_weak (a : UInt256) : AggregatesWeak (mixedSystem a) aggWeakRoot := by
  intro c n hlt
  show 1 ≤ n
  simp only [aggWeakRoot] at hlt
  omega

theorem aggWeakRoot_not_strong (a : UInt256) : ¬ Aggregates (mixedSystem a) aggWeakRoot := by
  intro hagg
  have := hagg 0 1 (show (1 : ℕ) ≤ 1 from le_refl 1)
  simp [aggWeakRoot] at this

theorem timeout_or_break_weak_satisfiable (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (cv : CommitValue) (S : System) (R : SlRoot) (F : Flow) (leg : FlowLeg) (N : ℕ)
      (p : ImtProof),
      Wf S ∧ AggregatesWeak S R ∧ ¬ Aggregates S R
        ∧ LegRefundableVerifiedBy h z0 hl cv S R F leg N p
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∧ S.time leg.chain 0 ≤ F.deadline
        ∧ (∀ n, S.time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n))) := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  refine ⟨fun _ _ => 1, mixedSystem 1, aggWeakRoot, mixedFlow 0 1 2, ⟨1, 2⟩, 1,
    ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩,
    mixedSystem_wf h1, aggWeakRoot_weak 1, aggWeakRoot_not_strong 1, ?_, ?_,
    by show (0 : ℕ) ≤ 0; exact le_refl 0, ?_⟩
  · refine Or.inl ⟨⟨by norm_num [aggWeakRoot, mixedFlow], by norm_num [mixedFlow]⟩, ?_⟩
    show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
      (beginHeight (mixedSystem 1) 1 1) 1 _
    rw [hbegin, hbeginH]
    exact setup_absence_accepted h z0 hl h1
  · rintro (⟨_, hb⟩ | ⟨hon, _⟩)
    · unfold ImtProofBreak at hb
      rw [hbegin, hbeginH] at hb
      exact honest_proof_no_break h z0 hl setup 0 0 (by norm_num [setup]) hb
    · exact absurd hon (by norm_num [mixedFlow])
  · intro n _ hmem
    rw [mixedSystem_tree_other hne] at hmem
    exact not_mem_setup h1 hmem

/-! ### A MessageRoot run with equal timestamps across blocks -/

open Contracts.MessageRoot in
/-- Block 0 at time 3: chain 1 registered and seeded. Block 1 at time 5: its batch 1 pushed. -/
def aggFromMR4 : MessageRoot.State :=
  (((aggWitnessSeeded 0 3).advance 5).record 1 1 9).push aggWitnessParams 1 1 9

open Contracts.MessageRoot in
/-- Block 2, again at time 5: batch 2 pushed. -/
def aggFromMR6 : MessageRoot.State := ((aggFromMR4.advance 5).record 1 2 11).push aggWitnessParams 1 2 11

/-- `historicalRoots[1]` of `aggFromMR4`: count 2 for chain 1, timestamp 5. -/
def aggFromMREntry : MessageRoot.HistEntry :=
  match aggFromMR4.hist 1 with
  | some e => e
  | none => ⟨0, 0, fun _ => 0⟩

open Contracts.MessageRoot in
theorem aggFromMR4_reach :
    MessageRoot.Reach aggWitnessParams .mono (MessageRoot.init aggWitnessParams 0 3) aggFromMR4 :=
  Reach.tail (Reach.tail (aggWitnessSeeded_reach .mono 0 3) (Step.nextBlock 5 (by decide)))
    (aggWitness_v32 1 9 (Or.inr (by decide)) (by decide) rfl rfl)

open Contracts.MessageRoot in
theorem aggFromMR6_reach : MessageRoot.Reach aggWitnessParams .mono aggFromMR4 aggFromMR6 :=
  Reach.tail (Reach.tail Reach.refl (Step.nextBlock 5 (le_refl 5)))
    (aggWitness_v32 2 11 (Or.inr (by decide)) (by decide) rfl rfl)

/-- Every tree `setup`, clocked by `aggFromMR6`. -/
def aggFromMRSystem : System := ⟨fun _ _ => setup, aggFromMR6.leafTime, fun _ _ => 0⟩

theorem from_messageRoot_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (P : MessageRoot.Params) (stF : MessageRoot.State) (S : System) (R : SlRoot)
      (cv : CommitValue) (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      MessageRoot.Reachable P .mono stF ∧ ClockedBy S stF ∧ WfTrees S
        ∧ HistoricalRootOf P .mono stF R ∧ ¬ Aggregates S R
        ∧ LegRefundableVerifiedBy h z0 hl cv S R F leg N p
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∧ S.time leg.chain 0 ≤ F.deadline
        ∧ (∀ n, S.time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n))) := by
  have h1 : (0 : UInt256) < 1 := by decide
  have h4 : MessageRoot.Reachable MessageRoot.aggWitnessParams .mono aggFromMR4 :=
    ⟨0, 3, aggFromMR4_reach⟩
  have hT : WfTrees aggFromMRSystem :=
    ⟨fun _ => Reaches.refl, fun _ _ => Reaches.refl, fun _ _ => by norm_num [aggFromMRSystem, setup]⟩
  have hR : HistoricalRootOf MessageRoot.aggWitnessParams .mono aggFromMR6
      (slRootOfEntry aggFromMREntry) := ⟨aggFromMR4, 1, aggFromMREntry, h4, aggFromMR6_reach, rfl, rfl⟩
  refine ⟨MessageRoot.aggWitnessParams, aggFromMR6, aggFromMRSystem, slRootOfEntry aggFromMREntry,
    fun _ _ => 1, ⟨0, [⟨1, 2⟩], 4⟩, ⟨1, 2⟩, 1,
    ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩,
    MessageRoot.reachable_tail h4 aggFromMR6_reach, rfl, hT, hR, ?_, ?_, ?_, by decide, ?_⟩
  · intro hagg
    have := hagg 1 2 (by decide)
    revert this
    decide
  · refine Or.inl ⟨⟨by decide, by decide⟩, ?_⟩
    show AbsenceAccepted h z0 hl setup 0 1 _
    exact setup_absence_accepted h z0 hl h1
  · rintro (⟨_, hb⟩ | ⟨hon, _⟩)
    · exact honest_proof_no_break h z0 hl setup 0 0 (by norm_num [setup]) hb
    · exact absurd hon (by decide)
  · intro n _ hmem
    exact not_mem_setup h1 hmem

/-! ### An accepted import -/

/-- The import of `historicalRoots[1]` of `MessageRoot.aggRunA4` (root `1`, timestamp `2`). -/
def aggImport : L2InteropRootStorage.RootIn := ⟨0, 1, 2, [1]⟩

theorem import_witness :
    ∃ (P : MessageRoot.Params) (stF : MessageRoot.State) (st : L2InteropRootStorage.State)
      (n : ℕ), MessageRoot.Reachable P .strict stF
        ∧ L2InteropRootStorage.Reach (AcceptedInRun P .strict stF) L2InteropRootStorage.empty st
        ∧ st.TimeoutRootPasses P.self n 0 := by
  have hr : MessageRoot.Reachable MessageRoot.aggWitnessParams .strict MessageRoot.aggRunA4 :=
    ⟨0, 1, MessageRoot.aggRunA4_reach⟩
  have hacc : AcceptedInRun MessageRoot.aggWitnessParams .strict MessageRoot.aggRunA4 aggImport :=
    ⟨MessageRoot.aggRunA4, hr, MessageRoot.Reach.refl, rfl, _, rfl, by decide, rfl, rfl⟩
  have hg : L2InteropRootStorage.AddGuard L2InteropRootStorage.empty aggImport 1 :=
    ⟨rfl, by decide, by decide, rfl⟩
  refine ⟨MessageRoot.aggWitnessParams, MessageRoot.aggRunA4,
    L2InteropRootStorage.empty.write aggImport 1, 1, hr,
    L2InteropRootStorage.Reach.tail L2InteropRootStorage.Reach.refl
      (L2InteropRootStorage.Step.single aggImport 1 hacc hg), ?_⟩
  unfold L2InteropRootStorage.State.TimeoutRootPasses
  decide

/-! ### The property theorems -/

theorem AggregatesImpliesWeak : Properties.AggregatesImpliesWeak :=
  fun _ _ h => aggregatesWeak_of_aggregates h
theorem AggregatesWeakIsStrictAggregation : Properties.AggregatesWeakIsStrictAggregation :=
  fun _ _ => aggregatesWeak_iff
theorem AggregatesWeakStrictlyWeaker : Properties.AggregatesWeakStrictlyWeaker :=
  ⟨mixedSystem 1, aggWeakRoot, aggWeakRoot_weak 1, aggWeakRoot_not_strong 1⟩
theorem IsLastOnTimeDerivedWeak : Properties.IsLastOnTimeDerivedWeak :=
  fun _ _ hagg _ _ _ he => isLastOnTime_of_verified_weak hagg he
theorem VerifiedImpliesRefundableWeak : Properties.VerifiedImpliesRefundableWeak :=
  fun _ _ _ _ _ _ hagg _ _ hv => verified_implies_refundable_weak hagg hv
theorem TimeoutMeansMissedDeadlineOrBreakWeak : Properties.TimeoutMeansMissedDeadlineOrBreakWeak :=
  fun _ _ _ _ _ hS _ hagg _ _ _ _ hv => timeout_means_missed_deadline_or_break_weak hS hagg hv
theorem TimeoutExcludesFinalityOrBreakWeak : Properties.TimeoutExcludesFinalityOrBreakWeak :=
  fun _ _ _ _ _ hS _ hagg _ _ _ _ hv n p' => timeout_excludes_finality_or_break_weak hS hagg hv n p'
theorem AcceptedTimeoutMeansMissedDeadlineOrBreakWeak :
    Properties.AcceptedTimeoutMeansMissedDeadlineOrBreakWeak :=
  fun _ _ _ _ _ hS _ _ _ hagg _ _ _ _ _ _ ha =>
    accepted_timeout_means_missed_deadline_or_break_weak hS hagg ha
theorem AcceptedImpliesRefundablePinnedWeak : Properties.AcceptedImpliesRefundablePinnedWeak :=
  fun _ _ _ _ _ _ _ _ hagg _ _ _ _ _ _ ha => accepted_implies_refundable_pinned_weak hagg ha
theorem AcceptedImpliesRefundableOnWeak : Properties.AcceptedImpliesRefundableOnWeak :=
  fun _ _ _ _ _ _ _ _ hagg _ _ _ _ _ _ hsep hinj ha =>
    accepted_implies_refundable_on_weak hagg hsep hinj ha
theorem TimeoutOrBreakWeakSatisfiable : Properties.TimeoutOrBreakWeakSatisfiable :=
  timeout_or_break_weak_satisfiable

theorem ImportedRootsAreHistorical : Properties.ImportedRootsAreHistorical :=
  fun _ _ _ _ hrun _ _ hts => imported_roots_are_historical hrun hts

theorem ImportedRootGateIsAggregating : Properties.ImportedRootGateIsAggregating := by
  intro P r stF st hrun c n D hpass
  obtain ⟨-, mst, e, h1, h2, he, hst⟩ := imported_roots_are_historical hrun hpass.1
  have hR : HistoricalRootOf P r stF (slRootOfEntry e) := ⟨mst, n, e, h1, h2, he, rfl⟩
  have hts : (st.entries c n).ts = e.ts := by rw [hst]
  refine ⟨slRootOfEntry e, hR, hts.symm, ?_, fun S hclk => historicalRoot_aggregatesWeak hR hclk⟩
  have := hpass.2
  rw [hts] at this
  exact this

theorem ImportWitness : Properties.ImportWitness := import_witness

theorem HistoricalRootAggregatesWeak : Properties.HistoricalRootAggregatesWeak :=
  fun _ _ _ _ _ hR hclk => historicalRoot_aggregatesWeak hR hclk
theorem HistoricalRootAggregatesStrictTs : Properties.HistoricalRootAggregatesStrictTs :=
  fun _ _ _ _ _ hr he hclk => historicalRoot_aggregates_strictTs hr he hclk
theorem WfFromMessageRoot : Properties.WfFromMessageRoot :=
  fun _ _ _ _ hr hclk hT => wf_of_messageRoot hr hclk hT

theorem TimeoutMeansMissedDeadlineOrBreakFromMessageRoot :
    Properties.TimeoutMeansMissedDeadlineOrBreakFromMessageRoot :=
  fun _ _ _ _ _ _ _ _ hr hclk hT _ hR _ _ _ _ hv =>
    timeout_means_missed_deadline_or_break_weak (wf_of_messageRoot hr hclk hT)
      (historicalRoot_aggregatesWeak hR hclk) hv
theorem TimeoutExcludesFinalityOrBreakFromMessageRoot :
    Properties.TimeoutExcludesFinalityOrBreakFromMessageRoot :=
  fun _ _ _ _ _ _ _ _ hr hclk hT _ hR _ _ _ _ hv n p' =>
    timeout_excludes_finality_or_break_weak (wf_of_messageRoot hr hclk hT)
      (historicalRoot_aggregatesWeak hR hclk) hv n p'
theorem AcceptedTimeoutMeansMissedDeadlineOrBreakFromMessageRoot :
    Properties.AcceptedTimeoutMeansMissedDeadlineOrBreakFromMessageRoot :=
  fun _ _ _ _ _ _ _ _ hr hclk hT _ _ _ hR _ _ _ _ _ _ ha =>
    accepted_timeout_means_missed_deadline_or_break_weak (wf_of_messageRoot hr hclk hT)
      (historicalRoot_aggregatesWeak hR hclk) ha
theorem FromMessageRootWitness : Properties.FromMessageRootWitness :=
  from_messageRoot_witness

end Contracts.Timeout

namespace Contracts.Refund

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager

/-! ### The two-flow run, with the refund verified against a root -/

theorem twoFlow_runAt (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ReachLogAt h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) (· = timeOneRoot)
      emptyManagers twoFlowMs [twoFlowCall h z0 hl] := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  have hmem : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs := by simp [mixedFlow]
  have href : LegRefundableVerifiedBy h z0 hl (fun _ _ => 1) (mixedSystem 1) timeOneRoot
      (mixedFlow 1 1 2) ⟨1, 2⟩ 1 ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩ := by
    refine Or.inl ⟨⟨by norm_num [timeOneRoot, mixedFlow], by norm_num [mixedFlow]⟩, ?_⟩
    show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
      (beginHeight (mixedSystem 1) 1 1) 1 _
    rw [hbegin, hbeginH]
    exact setup_absence_accepted h z0 hl h1
  have happ : ReachLogAt h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) (· = timeOneRoot)
      emptyManagers twoFlowM1 [] := ReachLogAt.append (c := 1) (f := 1) (b := 2) ReachLogAt.refl rfl
  have hguard : AuthorizeGuard (twoFlowM1 1) 1 2 := by
    show (twoFlowM1 1).legState 1 2 = .Committed
    simp [twoFlowM1, setAt, Manager.set]
  exact ReachLogAt.authorize (twoFlowCall h z0 hl) timeOneRoot happ rfl
    ⟨lengthFlowHash_checks_mixed, hmem, hmem, href⟩ hguard

/-- The logged call of the two-flow run marks an obligation other than `subsetFlow 0 1`'s, so no
`RefundBreak` names `subsetFlow 0 1`'s obligation, in any system. -/
theorem twoFlow_no_refundBreak (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System)
    (ev : GateEvidence) :
    ¬ RefundBreak h z0 hl lengthFlowHash S (subsetFlow 0 1) ev (obligationOf (subsetFlow 0 1) ⟨0, 1⟩)
      [twoFlowCall h z0 hl] := by
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

theorem twoFlow_not_refunded : ¬ Refunded twoFlowMs (obligationOf (subsetFlow 0 1) ⟨0, 1⟩) := by
  show ¬ 2 ≤ rank (stateOf (setAt twoFlowM1 1 ((twoFlowM1 1).set 1 2 .Revertable)) ⟨0, 1, 0⟩)
  have hne : (⟨0, 1, 0⟩ : Obligation) ≠ ⟨1, 2, 1⟩ := by decide
  rw [stateOf_setAt_other hne]
  show ¬ 2 ≤ rank (stateOf (setAt emptyManagers 1 ((emptyManagers 1).set 1 2 .Committed))
    ⟨0, 1, 0⟩)
  rw [stateOf_setAt_other hne, stateOf_emptyManagers]
  simp [rank]

theorem executed_obligation_never_refunded_or_break_at_witness (h : Hash) (z0 : UInt256)
    (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (roots : SlRoot → Prop) (F : Flow)
      (ev : GateEvidence) (leg : FlowLeg) (Ms : Managers) (log : List AuthCall),
      Wf S ∧ (∀ R, roots R → AggregatesWeak S R) ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ReachLogAt h z0 hl cv fh S roots emptyManagers Ms log ∧ log ≠ []
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log
        ∧ ¬ Refunded Ms (obligationOf F leg) := by
  have h1 : (0 : UInt256) < 1 := by decide
  refine ⟨fun _ _ => 1, lengthFlowHash, mixedSystem 1, (· = timeOneRoot), subsetFlow 0 1,
    fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1), ⟨0, 1⟩, twoFlowMs,
    [twoFlowCall h z0 hl], mixedSystem_wf h1, ?_,
    (subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset).1,
    twoFlow_runAt h z0 hl, List.cons_ne_nil _ _, twoFlow_no_refundBreak h z0 hl _ _,
    twoFlow_not_refunded⟩
  rintro R rfl
  exact aggregatesWeak_of_aggregates (timeOneRoot_aggregates_mixed 1)

/-! ### The same run, clocked by a MessageRoot run -/

/-- A deployment on chain `5`, shared root `1`, every other hash `0`. -/
def aggRefundParams : MessageRoot.Params :=
  ⟨5, ⟨fun _ _ _ => 0, fun _ _ => 0, fun _ => 0, fun _ => 1⟩⟩

/-- Block 0 at time 0: chains 0 and 1 registered at start 0. -/
def aggRefundV2 : MessageRoot.State :=
  ((MessageRoot.init aggRefundParams 0 0).addChain aggRefundParams 0 0).addChain aggRefundParams 1 0

/-- ... both seeded with genesis root `7` (so each has a leaf at time 0). -/
def aggRefundV4 : MessageRoot.State := (aggRefundV2.seed aggRefundParams 0 7).seed aggRefundParams 1 7

/-- Block 1 at time 1: chain 1's batch 1 pushed. -/
def aggRefundV6 : MessageRoot.State := ((aggRefundV4.advance 1).record 1 1 9).push aggRefundParams 1 1 9

/-- `historicalRoots[1]` of `aggRefundV6`: timestamp 1. -/
def aggRefundEntry : MessageRoot.HistEntry :=
  match aggRefundV6.hist 1 with
  | some e => e
  | none => ⟨0, 0, fun _ => 0⟩

theorem aggRefundV6_reach :
    MessageRoot.Reach aggRefundParams .strict (MessageRoot.init aggRefundParams 0 0) aggRefundV6 := by
  have s1 : MessageRoot.Step aggRefundParams .strict (MessageRoot.init aggRefundParams 0 0)
      ((MessageRoot.init aggRefundParams 0 0).addChain aggRefundParams 0 0) :=
    MessageRoot.Step.addNewChain 0 0 (by rw [MessageRoot.registered_init_iff]; decide)
  have s2 : MessageRoot.Step aggRefundParams .strict
      ((MessageRoot.init aggRefundParams 0 0).addChain aggRefundParams 0 0) aggRefundV2 :=
    MessageRoot.Step.addNewChain 1 0 (by unfold MessageRoot.State.Registered; decide)
  have s3 : MessageRoot.Step aggRefundParams .strict aggRefundV2
      (aggRefundV2.seed aggRefundParams 0 7) :=
    MessageRoot.Step.seedGenesisRoot 0 7 ⟨by decide, Or.inr (by decide), rfl, rfl⟩
  have s4 : MessageRoot.Step aggRefundParams .strict (aggRefundV2.seed aggRefundParams 0 7)
      aggRefundV4 :=
    MessageRoot.Step.seedGenesisRoot 1 7 ⟨by decide, Or.inr (by decide), rfl, rfl⟩
  have s5 : MessageRoot.Step aggRefundParams .strict aggRefundV4 (aggRefundV4.advance 1) :=
    MessageRoot.Step.nextBlock 1 (by decide)
  have s6 : MessageRoot.Step aggRefundParams .strict (aggRefundV4.advance 1) aggRefundV6 :=
    MessageRoot.Step.addChainBatchRootV32 1 1 9 ⟨Or.inr (by decide), by decide, rfl, rfl⟩
  exact MessageRoot.Reach.tail (MessageRoot.Reach.tail (MessageRoot.Reach.tail
    (MessageRoot.Reach.tail (MessageRoot.Reach.tail (MessageRoot.Reach.tail MessageRoot.Reach.refl
      s1) s2) s3) s4) s5) s6

/-- `mixedSystem 1`'s trees, clocked by `aggRefundV6`. -/
def aggRefundSystem : System := { mixedSystem 1 with time := aggRefundV6.leafTime }

theorem from_messageRoot_refund_witness (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ∃ (P : MessageRoot.Params) (stF : MessageRoot.State) (cv : CommitValue) (fh : FlowHash)
      (S : System) (F : Flow) (ev : GateEvidence) (leg : FlowLeg) (Ms : Managers)
      (log : List AuthCall),
      MessageRoot.Reachable P .strict stF ∧ ClockedBy S stF ∧ WfTrees S
        ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ReachLogAt h z0 hl cv fh S (HistoricalRootOf P .strict stF) emptyManagers Ms log
        ∧ log ≠ [] ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log
        ∧ ¬ Refunded Ms (obligationOf F leg) := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  have hS := mixedSystem_wf h1
  have hr : MessageRoot.Reachable aggRefundParams .strict aggRefundV6 := ⟨0, 0, aggRefundV6_reach⟩
  have hT : WfTrees aggRefundSystem := ⟨hS.start, hS.batch, hS.capacity⟩
  obtain ⟨⟨hmem, hchk, hfin⟩, -⟩ :=
    subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset
  have hex : ExecutedViaBy h z0 hl (fun _ _ => 1) lengthFlowHash aggRefundSystem (subsetFlow 0 1)
      (fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1)) ⟨0, 1⟩ := by
    refine ⟨hmem, hchk, fun l hl' => ?_⟩
    obtain ⟨_, hacc⟩ := hfin l hl'
    obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
    exact ⟨show aggRefundV6.leafTime 0 0 ≤ 0 by decide, hacc⟩
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  have hmem2 : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs := by simp [mixedFlow]
  have href : LegRefundableVerifiedBy h z0 hl (fun _ _ => 1) aggRefundSystem
      (slRootOfEntry aggRefundEntry) (mixedFlow 1 1 2) ⟨1, 2⟩ 1
      ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩ := by
    refine Or.inl ⟨⟨by decide, by decide⟩, ?_⟩
    show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
      (beginHeight (mixedSystem 1) 1 1) 1 _
    rw [hbegin, hbeginH]
    exact setup_absence_accepted h z0 hl h1
  have hR : HistoricalRootOf aggRefundParams .strict aggRefundV6 (slRootOfEntry aggRefundEntry) :=
    ⟨aggRefundV6, 1, aggRefundEntry, hr, MessageRoot.Reach.refl, rfl, rfl⟩
  have happ : ReachLogAt h z0 hl (fun _ _ => 1) lengthFlowHash aggRefundSystem
      (HistoricalRootOf aggRefundParams .strict aggRefundV6) emptyManagers twoFlowM1 [] :=
    ReachLogAt.append (c := 1) (f := 1) (b := 2) ReachLogAt.refl rfl
  have hguard : AuthorizeGuard (twoFlowM1 1) 1 2 := by
    show (twoFlowM1 1).legState 1 2 = .Committed
    simp [twoFlowM1, setAt, Manager.set]
  have hrun : ReachLogAt h z0 hl (fun _ _ => 1) lengthFlowHash aggRefundSystem
      (HistoricalRootOf aggRefundParams .strict aggRefundV6) emptyManagers twoFlowMs
      [twoFlowCall h z0 hl] :=
    ReachLogAt.authorize (twoFlowCall h z0 hl) _ happ hR
      ⟨lengthFlowHash_checks_mixed, hmem2, hmem2, href⟩ hguard
  exact ⟨aggRefundParams, aggRefundV6, fun _ _ => 1, lengthFlowHash, aggRefundSystem,
    subsetFlow 0 1, _, ⟨0, 1⟩, twoFlowMs, [twoFlowCall h z0 hl], hr, rfl, hT, hex, hrun,
    List.cons_ne_nil _ _, twoFlow_no_refundBreak h z0 hl _ _, twoFlow_not_refunded⟩

/-! ### The property theorems -/

theorem VerifiedTimeoutAuthorizesWeak : Properties.VerifiedTimeoutAuthorizesWeak :=
  fun _ _ _ _ _ _ hagg _ _ hmem hv => verified_timeout_authorizes_weak hagg hmem hv
theorem RefundedFlowMissedDeadlineOrBreakWeak : Properties.RefundedFlowMissedDeadlineOrBreakWeak :=
  fun _ _ _ _ _ hS _ hagg _ _ _ _ hv => timeout_means_missed_deadline_or_break_weak hS hagg hv
theorem AcceptedTimeoutAuthorizesPinnedWeak : Properties.AcceptedTimeoutAuthorizesPinnedWeak :=
  fun _ _ _ _ _ _ _ _ hagg _ _ _ _ _ _ hmem ha => accepted_timeout_authorizes_pinned_weak hagg hmem ha
theorem ExecutedExcludesAcceptedRefundOrBreakWeak :
    Properties.ExecutedExcludesAcceptedRefundOrBreakWeak :=
  fun _ _ _ _ _ _ hS _ _ _ hagg _ _ _ hex other hother N p sibs x =>
    executed_excludes_accepted_refund_or_break_weak hS hagg hex other hother N p sibs x
theorem ReachLogAtProjects : Properties.ReachLogAtProjects :=
  fun _ _ _ _ _ _ _ hroots _ _ _ hr => reachLog_of_reachLogAt hroots hr
theorem ExecutedObligationNeverRefundedOrBreakAt :
    Properties.ExecutedObligationNeverRefundedOrBreakAt :=
  fun _ _ _ _ _ _ hS _ hroots _ _ _ hex _ _ hr =>
    executed_freezes_flow_or_break hS hex (reachLog_of_reachLogAt hroots hr) _ rfl
theorem OneExecutionFreezesTheFlowOrBreakAt : Properties.OneExecutionFreezesTheFlowOrBreakAt :=
  fun _ _ _ _ _ _ hS _ hroots _ _ _ hex _ _ hr _ _ =>
    executed_freezes_flow_or_break hS hex (reachLog_of_reachLogAt hroots hr) _ rfl
theorem ExecutedObligationNeverRefundedOrBreakAtWitness :
    Properties.ExecutedObligationNeverRefundedOrBreakAtWitness :=
  executed_obligation_never_refunded_or_break_at_witness

theorem ExecutedExcludesAcceptedRefundOrBreakFromMessageRoot :
    Properties.ExecutedExcludesAcceptedRefundOrBreakFromMessageRoot :=
  fun _ _ _ _ _ _ _ _ _ hr hclk hT _ _ _ hR _ _ _ hex other hother N p sibs x =>
    executed_excludes_accepted_refund_or_break_weak (wf_of_messageRoot hr hclk hT)
      (historicalRoot_aggregatesWeak hR hclk) hex other hother N p sibs x
theorem ExecutedObligationNeverRefundedOrBreakFromMessageRoot :
    Properties.ExecutedObligationNeverRefundedOrBreakFromMessageRoot :=
  fun _ _ _ _ _ _ _ _ _ hr hclk hT _ _ _ hex _ _ hrun =>
    executed_freezes_flow_or_break (wf_of_messageRoot hr hclk hT) hex
      (reachLog_of_reachLogAt (fun _ hR => historicalRoot_aggregatesWeak hR hclk) hrun) _ rfl
theorem FromMessageRootRefundWitness : Properties.FromMessageRootRefundWitness :=
  from_messageRoot_refund_witness

end Contracts.Refund
