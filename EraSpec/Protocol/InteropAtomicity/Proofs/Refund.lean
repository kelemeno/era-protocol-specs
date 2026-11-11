import EraSpec.Protocol.InteropAtomicity.Properties.Refund
import EraSpec.Protocol.InteropAtomicity.Proofs.Timeout
import EraSpec.Contracts.Merkle.Proofs.PathCollision
import EraSpec.Contracts.AtomicFlowManager.Proofs.Model

/-!
# Proofs: one outcome per obligation

One induction and one substitution.

The induction (`refund_needs_own_flow_timeout`) walks an arbitrary interleaving of
arbitrary chains' calls and shows that whatever lifted an obligation past
`Committed` was an `authorize` carrying a timeout proof: `append` lands below it,
and `claim` needs to be above it already, so it inherits the witness rather than
creating one.

The substitution is `Atomicity.flowId_check_pins_legList`: the flow that authorized
and the flow that was executed are both checked and claim one id, so they are the
same flow — and then the tree side (`executed_excludes_any_refund`) closes it.
-/

namespace Contracts.Refund

open MerkleSpec MerkleSpec.LastLeaf Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.Timeout
open Contracts.AtomicFlowManager

/-! ## Reading the composed state -/

@[simp] lemma stateOf_emptyManagers (o : Obligation) : stateOf emptyManagers o = .Unset := rfl

lemma stateOf_setAt_self (Ms : Managers) (c : Chain) (f b : UInt256) (s : LegState) :
    stateOf (setAt Ms c ((Ms c).set f b s)) ⟨f, b, c⟩ = s := by
  simp [stateOf, setAt, Manager.set]

lemma stateOf_setAt_other {Ms : Managers} {c : Chain} {f b : UInt256} {s : LegState}
    {o : Obligation} (h : o ≠ ⟨f, b, c⟩) :
    stateOf (setAt Ms c ((Ms c).set f b s)) o = stateOf Ms o := by
  by_cases hc : o.chain = c
  · have hkey : ¬ (o.flowId = f ∧ o.bundleHash = b) := by
      rintro ⟨h1, h2⟩
      apply h
      cases o with | mk fid bh ch => simp_all
    show (setAt Ms c ((Ms c).set f b s) o.chain).legState o.flowId o.bundleHash
      = (Ms o.chain).legState o.flowId o.bundleHash
    simp only [setAt, ite_eq_left hc]
    rw [set_other hkey, hc]
  · show (setAt Ms c ((Ms c).set f b s) o.chain).legState o.flowId o.bundleHash
      = (Ms o.chain).legState o.flowId o.bundleHash
    simp only [setAt, ite_eq_right hc]

/-- The obligation an `authorize` step writes to. -/
lemma obligationOf_eq (F : Flow) (leg : FlowLeg) :
    obligationOf F leg = ⟨F.flowId, leg.bundleHash, leg.chain⟩ := rfl

/-! ## No refund without a timeout proof for this obligation's flow -/

/-- **A REFUNDED OBLIGATION HAS A TIMEOUT PROOF BEHIND IT.** -/
theorem refund_needs_own_flow_timeout {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} {Ms : Managers}
    (hr : Reach h z0 hl cv fh S emptyManagers Ms) :
    ∀ (o : Obligation), Refunded Ms o →
      ∃ F', FlowIdChecked fh F' ∧ ∃ leg ∈ F'.legs, obligationOf F' leg = o
        ∧ RefundAuthorized h z0 hl cv S F' := by
  induction hr with
  | refl =>
    intro o hrf
    exfalso
    simp only [Refunded, stateOf_emptyManagers] at hrf
    simp [rank] at hrf
  | @tail Ns Ps _ hs ih =>
    intro o hrf
    cases hs with
    | @append c f b hg =>
      by_cases heq : o = ⟨f, b, c⟩
      · exfalso
        subst heq
        simp only [Refunded, stateOf_setAt_self] at hrf
        simp [rank] at hrf
      · refine ih o ?_
        simpa only [Refunded, stateOf_setAt_other heq] using hrf
    | @authorize F leg hchk hmem hauth _ =>
      by_cases heq : o = obligationOf F leg
      · exact ⟨F, hchk, leg, hmem, heq.symm, hauth⟩
      · refine ih o ?_
        rw [obligationOf_eq] at heq
        simpa only [Refunded, stateOf_setAt_other heq] using hrf
    | @claim c f b hg =>
      by_cases heq : o = ⟨f, b, c⟩
      · -- `claim` needs `Revertable`, so the previous state was already past `Committed`
        subst heq
        refine ih _ ?_
        simp only [Refunded, stateOf]
        rw [show (Ns c).legState f b = LegState.Revertable from hg]
        simp [rank]
      · refine ih o ?_
        simpa only [Refunded, stateOf_setAt_other heq] using hrf

/-- **AND IT IS THE OBLIGATION'S OWN FLOW'S.** -/
theorem refund_implies_own_flow_timeout {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} (hinj : FlowHashInj fh) {S : System}
    {F : Flow} {leg : FlowLeg} (hchk : FlowIdChecked fh F) (_hmem : leg ∈ F.legs)
    {Ms : Managers} (hr : Reach h z0 hl cv fh S emptyManagers Ms)
    (hrf : Refunded Ms (obligationOf F leg)) : RefundAuthorized h z0 hl cv S F := by
  obtain ⟨F', hchk', leg', _, hobl, hauth⟩ := refund_needs_own_flow_timeout hr _ hrf
  have hid : F'.flowId = F.flowId := congrArg Obligation.flowId hobl
  obtain rfl : F' = F := flowId_check_pins_legList hinj hchk' hchk hid
  exact hauth

/-! ## The milestone -/

/-- **AN EXECUTED FLOW'S OBLIGATIONS ARE FROZEN.**  Stated for every obligation
carrying the flow's id, which covers the executed leg and its siblings alike. -/
theorem executed_freezes_flow {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash}
    (hinj : FlowHashInj fh) {S : System} (hS : Wf S) {F : Flow} {leg : FlowLeg}
    (hchk : FlowIdChecked fh F) (hex : ExecutedVia h z0 hl cv fh S F leg)
    {Ms : Managers} (hr : Reach h z0 hl cv fh S emptyManagers Ms)
    (o : Obligation) (ho : o.flowId = F.flowId) : ¬ Refunded Ms o := by
  intro hrf
  obtain ⟨F', hchk', leg', _, hobl, hauth⟩ := refund_needs_own_flow_timeout hr o hrf
  have h1 : F'.flowId = o.flowId := congrArg Obligation.flowId hobl
  have hid : F'.flowId = F.flowId := by rw [← ho]; exact h1
  obtain rfl : F' = F := flowId_check_pins_legList hinj hchk' hchk hid
  obtain ⟨other, hother, href⟩ := hauth
  exact executed_excludes_any_refund hA hS hex other hother href

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED.** -/
theorem executed_obligation_never_refunded {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash}
    (hinj : FlowHashInj fh) {S : System} (hS : Wf S) {F : Flow} {leg : FlowLeg}
    (hchk : FlowIdChecked fh F) (hex : ExecutedVia h z0 hl cv fh S F leg)
    {Ms : Managers} (hr : Reach h z0 hl cv fh S emptyManagers Ms) :
    ¬ Refunded Ms (obligationOf F leg) :=
  executed_freezes_flow hA hinj hS hchk hex hr _ rfl

/-! ## Timeout validity, derived -/

/-- **A VERIFIED TIMEOUT ENABLES THE REFUND.** -/
theorem verified_timeout_authorizes {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {R : SlRoot} (hagg : Aggregates S R)
    {F : Flow} {leg : FlowLeg} (hmem : leg ∈ F.legs)
    (hv : LegRefundableVerified h z0 hl cv S R F leg) : RefundAuthorized h z0 hl cv S F :=
  ⟨leg, hmem, verified_implies_refundable hagg hv⟩

/-! ## The chain, end to end -/

theorem accepted_timeout_authorizes {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {S : System} {ze : UInt256}
    {R : SlRoot} {B : RootBacking h ze R} (hagg : Aggregates S R) {F : Flow} {leg : FlowLeg}
    (hmem : leg ∈ F.legs) (ha : LegRefundableAccepted h z0 hl cv S B F leg) :
    RefundAuthorized h z0 hl cv S F ∨ HashBreak h ze (B.leaves leg.chain) := by
  rcases accepted_implies_refundable hA.nodeInj hagg ha with hr | hb
  · exact Or.inl ⟨leg, hmem, hr⟩
  · exact Or.inr hb

/-- **THE PUNCHLINE.**  An accepted timeout proof for a flow that delivered is a
hash break. -/
theorem accepted_timeout_for_delivered_flow_is_a_break {h : Hash} {z0 : UInt256}
    {hl : LeafHash} (hA : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash}
    {S : System} (hS : Wf S) {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : Aggregates S R) {F : Flow} {leg : FlowLeg}
    (hex : ExecutedVia h z0 hl cv fh S F leg) (other : FlowLeg) (hother : other ∈ F.legs)
    (ha : LegRefundableAccepted h z0 hl cv S B F other) :
    HashBreak h ze (B.leaves other.chain) := by
  rcases accepted_implies_refundable hA.nodeInj hagg ha with hr | hb
  · exact absurd hr (executed_excludes_any_refund hA hS hex other hother)
  · exact hb

/-! ## What a shared commitment means -/

theorem shared_commitment_yields_collision (cv : CommitValue) (o o' : Obligation)
    (heq : cv o.flowId o.bundleHash = cv o'.flowId o'.bundleHash) :
    (o.flowId = o'.flowId ∧ o.bundleHash = o'.bundleHash)
      ∨ ∃ f₁ b₁ f₂ b₂, (f₁, b₁) ≠ (f₂, b₂) ∧ cv f₁ b₁ = cv f₂ b₂ := by
  by_cases hsame : o.flowId = o'.flowId ∧ o.bundleHash = o'.bundleHash
  · exact Or.inl hsame
  · refine Or.inr ⟨o.flowId, o.bundleHash, o'.flowId, o'.bundleHash, ?_, heq⟩
    intro hpair
    exact hsame ⟨congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩

theorem commitment_pins_leg {cv : CommitValue} (hinj : CommitValueInj cv) (o o' : Obligation)
    (heq : cv o.flowId o.bundleHash = cv o'.flowId o'.bundleHash) :
    o.flowId = o'.flowId ∧ o.bundleHash = o'.bundleHash :=
  hinj _ _ _ _ heq

/-! ## The supporting cryptographic claim -/

/-- **A CROSS-FLOW REFUND EXHIBITS A HASH COLLISION.**  No injectivity hypothesis. -/
theorem cross_flow_refund_yields_collision {fh : FlowHash} {F F' : Flow}
    (hF : FlowIdChecked fh F) (hF' : FlowIdChecked fh F') (hid : F.flowId = F'.flowId)
    (hne : F ≠ F') :
    ∃ (l₁ : List FlowLeg) (d₁ : ℕ) (l₂ : List FlowLeg) (d₂ : ℕ),
      (l₁, d₁) ≠ (l₂, d₂) ∧ fh l₁ d₁ = fh l₂ d₂ := by
  refine ⟨F.legs, F.deadline, F'.legs, F'.deadline, ?_, ?_⟩
  · intro hpair
    apply hne
    have hl : F.legs = F'.legs := congrArg Prod.fst hpair
    have hd : F.deadline = F'.deadline := congrArg Prod.snd hpair
    cases F; cases F'; simp_all
  · rw [hF, hF']; exact hid

end Contracts.Refund

/-! ## Certificates -/

namespace Contracts.Refund

open Contracts.Refund

theorem RefundNeedsOwnFlowTimeout : Contracts.Refund.Properties.RefundNeedsOwnFlowTimeout :=
  fun _ _ _ _ _ _ _ hr o hrf => refund_needs_own_flow_timeout hr o hrf
theorem RefundImpliesOwnFlowTimeout : Contracts.Refund.Properties.RefundImpliesOwnFlowTimeout :=
  fun _ _ _ _ _ hinj _ _ _ hchk hmem _ hr hrf =>
    refund_implies_own_flow_timeout hinj hchk hmem hr hrf
theorem ExecutedObligationNeverRefunded : Contracts.Refund.Properties.ExecutedObligationNeverRefunded :=
  fun _ _ _ hA _ _ hinj _ hS _ _ _ hchk hex _ hr =>
    executed_obligation_never_refunded hA hinj hS hchk hex hr
theorem OneExecutionFreezesTheFlow : Contracts.Refund.Properties.OneExecutionFreezesTheFlow :=
  fun _ _ _ hA _ _ hinj _ hS _ _ _ hchk hex _ hr _ _ =>
    executed_freezes_flow hA hinj hS hchk hex hr _ rfl
theorem VerifiedTimeoutAuthorizes : Contracts.Refund.Properties.VerifiedTimeoutAuthorizes :=
  fun _ _ _ _ _ _ hagg _ _ hmem hv => verified_timeout_authorizes hagg hmem hv
theorem RefundedFlowMissedDeadline : Contracts.Refund.Properties.RefundedFlowMissedDeadline :=
  fun _ _ _ hA _ _ hS _ hagg _ _ hv n hon =>
    Contracts.Timeout.timeout_means_missed_deadline hA hS hagg hv n hon
theorem CrossFlowRefundYieldsCollision : Contracts.Refund.Properties.CrossFlowRefundYieldsCollision :=
  fun _ _ _ hF hF' hid hne => cross_flow_refund_yields_collision hF hF' hid hne
theorem AcceptedTimeoutAuthorizes : Contracts.Refund.Properties.AcceptedTimeoutAuthorizes :=
  fun _ _ _ hA _ _ _ _ _ hagg _ _ hmem ha => accepted_timeout_authorizes hA hagg hmem ha
theorem AcceptedTimeoutForDeliveredFlowIsABreak :
    Contracts.Refund.Properties.AcceptedTimeoutForDeliveredFlowIsABreak :=
  fun _ _ _ hA _ _ _ hS _ _ _ hagg _ _ hex other hother ha =>
    accepted_timeout_for_delivered_flow_is_a_break hA hS hagg hex other hother ha
theorem SharedCommitmentYieldsCollision : Contracts.Refund.Properties.SharedCommitmentYieldsCollision :=
  shared_commitment_yields_collision
theorem CommitmentPinsLeg : Contracts.Refund.Properties.CommitmentPinsLeg :=
  fun _ hinj o o' heq => commitment_pins_leg hinj o o' heq
theorem TimeoutProofRefundsCommittedLeg : Contracts.Refund.Properties.TimeoutProofRefundsCommittedLeg :=
  fun _ _ _ _ _ _ _ _ _ hchk hmem hauth hg => Step.authorize hchk hmem hauth hg


theorem CommitValueInjUnsatisfiable : Properties.CommitValueInjUnsatisfiable :=
  fun cv hinj => Contracts.InteropCommitmentTree.not_nodeInj cv hinj


theorem UnpinnedCollisionsAlwaysExist : Properties.UnpinnedCollisionsAlwaysExist := by
  refine ⟨fun fh => ?_, fun cv => MerkleSpec.Verifier.exists_pair_collision cv⟩
  by_contra hno
  push Not at hno
  have hinj : Contracts.Atomicity.FlowHashInj fh := by
    intro l₁ d₁ l₂ d₂ he
    by_contra hne
    exact hno l₁ d₁ l₂ d₂ (fun hp => hne (Prod.mk.inj hp)) he
  exact Contracts.Atomicity.FlowHashInjUnsatisfiable fh hinj

theorem CrossFlowIdClashIsPinnedCollision : Properties.CrossFlowIdClashIsPinnedCollision := by
  intro fh F F' hF hF' hid hne
  refine ⟨?_, hF.trans (hid.trans hF'.symm)⟩
  intro hp
  apply hne
  obtain ⟨hl, hd⟩ := Prod.mk.inj hp
  cases F; cases F'
  simp_all

end Contracts.Refund

/-! ## Repaired: pinned and bounded forms -/

namespace Contracts.Refund

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.AtomicFlowManager

/-- The flow-level pinned form: one use of `refund_needs_own_flow_timeout`, then a case
split on whether the authorizing flow is `F`. -/
theorem refund_of_flowId_implies_own_flow_timeout_or_collision {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} {F : Flow}
    (hchk : FlowIdChecked fh F) {Ms : Managers} (hr : Reach h z0 hl cv fh S emptyManagers Ms)
    (o : Obligation) (ho : o.flowId = F.flowId) (hrf : Refunded Ms o) :
    RefundAuthorized h z0 hl cv S F
      ∨ ∃ F', FlowIdChecked fh F' ∧ (∃ leg' ∈ F'.legs, obligationOf F' leg' = o)
          ∧ RefundAuthorized h z0 hl cv S F' ∧ FlowIdClash fh F F' := by
  obtain ⟨F', hchk', leg', hmem', hobl, hauth⟩ := refund_needs_own_flow_timeout hr o hrf
  have hid : F.flowId = F'.flowId := by
    rw [← ho]; exact (congrArg Obligation.flowId hobl).symm
  rcases flowId_check_pins_legList_or_collision hchk hchk' hid with rfl | hcl
  · exact Or.inl hauth
  · exact Or.inr ⟨F', hchk', ⟨leg', hmem', hobl⟩, hauth, hcl⟩

/-- A system whose every batch settles at time `0`: no deadline is ever missed, so no
timeout proof can verify on either branch, whatever the hashes. -/
def frozenSystem : System := ⟨fun _ _ => setup, fun _ _ => 0, fun _ _ => 0⟩

lemma frozenSystem_no_refund {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    (F : Flow) : ¬ RefundAuthorized h z0 hl cv frozenSystem F := by
  rintro ⟨leg, _, N, p, hbr⟩
  rcases hbr with ⟨hlate, _⟩ | ⟨⟨_, hlast⟩, _⟩
  · exact absurd hlate (Nat.not_lt_zero _)
  · exact absurd (hlast (N + 1) (Nat.lt_succ_self N)) (Nat.not_lt_zero _)

end Contracts.Refund

namespace Contracts.Refund

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.AtomicFlowManager

theorem RefundOfFlowIdImpliesOwnFlowTimeoutOrCollision :
    Properties.RefundOfFlowIdImpliesOwnFlowTimeoutOrCollision :=
  fun _ _ _ _ _ _ _ hchk _ hr o ho hrf =>
    refund_of_flowId_implies_own_flow_timeout_or_collision hchk hr o ho hrf

theorem RefundImpliesOwnFlowTimeoutOrCollision :
    Properties.RefundImpliesOwnFlowTimeoutOrCollision :=
  fun _ _ _ _ _ _ _ _ hchk _ _ hr hrf =>
    refund_of_flowId_implies_own_flow_timeout_or_collision hchk hr _ rfl hrf

theorem RefundOrCollisionNeedsReach : Properties.RefundOrCollisionNeedsReach := by
  let F : Flow := ⟨0, [⟨0, 0⟩], 0⟩
  refine ⟨fun _ _ => 0, 0, fun _ => 0, fun _ _ => 1, honestFlowHash F, frozenSystem, F, ⟨0, 0⟩,
    setAt emptyManagers 0 ((emptyManagers 0).set 0 0 .Revertable),
    (honest_flowHash_no_clash F).1, List.mem_singleton_self _, ?_, ?_⟩
  · show 2 ≤ rank (stateOf (setAt emptyManagers 0 ((emptyManagers 0).set 0 0 .Revertable))
      ⟨0, 0, 0⟩)
    rw [stateOf_setAt_self]; simp [rank]
  · rintro (hauth | ⟨F', _, _, hauth, _⟩)
    · exact frozenSystem_no_refund F hauth
    · exact frozenSystem_no_refund F' hauth

theorem RefundImpliesOwnFlowTimeoutOrCollisionWitness :
    Properties.RefundImpliesOwnFlowTimeoutOrCollisionWitness := by
  let h : Hash := fun _ _ => 0
  let hl : LeafHash := fun _ => 0
  let cv : CommitValue := fun _ _ => 1
  let F : Flow := mixedFlow 0 1 2
  let fh : FlowHash := honestFlowHash F
  let S : System := mixedSystem (cv 0 1)
  have hpos : (0 : UInt256) < 1 := by decide
  have hchk : FlowIdChecked fh F := (honest_flowHash_no_clash F).1
  have hmem : (⟨1, 2⟩ : FlowLeg) ∈ F.legs := by simp [F, mixedFlow]
  have hauth : RefundAuthorized h 0 hl cv S F :=
    ⟨⟨1, 2⟩, hmem,
      (subset_flow_passes_unchecked_gate (h := h) (z0 := 0) (hl := hl) (cv := cv)
        (id := 0) (hA := 1) (hB := 2) hpos hpos).2.2⟩
  let M1 : Managers := setAt emptyManagers 1 ((emptyManagers 1).set 0 2 .Committed)
  have happ : Step h 0 hl cv fh S emptyManagers M1 := Step.append (c := 1) (f := 0) (b := 2) rfl
  have hguard : AuthorizeGuard (M1 1) F.flowId (⟨1, 2⟩ : FlowLeg).bundleHash := by
    show (M1 1).legState 0 2 = .Committed
    simp [M1, setAt, Manager.set]
  have hstep := Step.authorize (h := h) (z0 := 0) (hl := hl) (cv := cv) (fh := fh) (S := S)
    (Ms := M1) hchk hmem hauth hguard
  refine ⟨h, 0, hl, cv, fh, S, F, ⟨1, 2⟩, _, hchk, hmem,
    Reach.tail (Reach.tail Reach.refl happ) hstep, ?_, ?_⟩
  · show 2 ≤ rank (stateOf (setAt M1 1 ((M1 1).set 0 2 .Revertable)) ⟨0, 2, 1⟩)
    rw [stateOf_setAt_self]; simp [rank]
  · rintro ⟨F', _, _, _, hcl⟩
    exact (honest_flowHash_no_clash F).2 F' hcl

theorem CommitmentPinsLegOrCollision : Properties.CommitmentPinsLegOrCollision := by
  intro cv o o' heq
  by_cases hp : (o.flowId, o.bundleHash) = (o'.flowId, o'.bundleHash)
  · exact Or.inl (Prod.mk.inj hp)
  · exact Or.inr ⟨hp, heq⟩

theorem CommitmentPinsLegOn : Properties.CommitmentPinsLegOn := by
  intro cv os hinj o ho o' ho' heq
  rcases CommitmentPinsLegOrCollision cv o o' heq with h | h
  · exact h
  · exact absurd h (hinj o ho o' ho')

theorem CommitValueInjOnSatisfiable : Properties.CommitValueInjOnSatisfiable := by
  intro os hlen
  let P : List (UInt256 × UInt256) := os.map (fun o => (o.flowId, o.bundleHash))
  have hPlen : P.length < UInt256.size := by
    show (os.map _).length < _
    rw [List.length_map]; exact hlen
  refine ⟨fun f b => indexHash P (f, b), ?_⟩
  rintro o ho o' ho' ⟨hne, heq⟩
  exact hne (indexHash_inj_on hPlen (List.mem_map_of_mem (f := fun o => (o.flowId, o.bundleHash)) ho)
    (List.mem_map_of_mem (f := fun o => (o.flowId, o.bundleHash)) ho') heq)

theorem HonestCommitValueNoClash : Properties.HonestCommitValueNoClash := by
  rintro o o' ⟨hne, heq⟩
  have hne' : ¬ (o'.flowId, o'.bundleHash) = (o.flowId, o.bundleHash) := fun h => hne h.symm
  simp only [honestCommitValue, ite_eq_right hne'] at heq
  exact absurd heq (by decide)

end Contracts.Refund

/-! ## The milestone without hash premises

`executed_freezes_flow` with `flowId_check_pins_legList hinj` replaced by
`flowId_check_pins_legList_or_collision` and `executed_excludes_any_refund hA` replaced
by `executed_excludes_any_refund_or_break`, over the logged run. -/

namespace Contracts.Refund

open MerkleSpec MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager

theorem reachLog_of_reach {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms Ns : Managers} (hr : Reach h z0 hl cv fh S Ms Ns) :
    ∃ log, ReachLog h z0 hl cv fh S Ms Ns log := by
  induction hr with
  | refl => exact ⟨[], ReachLog.refl⟩
  | tail _ hs ih =>
    obtain ⟨log, hlog⟩ := ih
    cases hs with
    | append hg => exact ⟨log, ReachLog.append hlog hg⟩
    | @authorize F leg hchk hmem hauth hg =>
      obtain ⟨m, hm, N, p, hr⟩ := hauth
      exact ⟨⟨F, leg, m, N, p⟩ :: log,
        ReachLog.authorize ⟨F, leg, m, N, p⟩ hlog ⟨hchk, hmem, hm, hr⟩ hg⟩
    | claim hg => exact ⟨log, ReachLog.claim hlog hg⟩

theorem reach_of_reachLog {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms Ns : Managers} {log : List AuthCall}
    (hr : ReachLog h z0 hl cv fh S Ms Ns log) : Reach h z0 hl cv fh S Ms Ns := by
  induction hr with
  | refl => exact Reach.refl
  | append _ hg ih => exact Reach.tail ih (Step.append hg)
  | authorize a _ hv hg ih =>
    exact Reach.tail ih
      (Step.authorize hv.1 hv.2.1 ⟨a.missing, hv.2.2.1, a.batch, a.proof, hv.2.2.2⟩ hg)
  | claim _ hg ih => exact Reach.tail ih (Step.claim hg)

theorem reach_iff_reachLog {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms Ns : Managers} :
    Reach h z0 hl cv fh S Ms Ns ↔ ∃ log, ReachLog h z0 hl cv fh S Ms Ns log :=
  ⟨reachLog_of_reach, fun ⟨_, hr⟩ => reach_of_reachLog hr⟩

/-- **A REFUNDED OBLIGATION WAS MARKED BY A LOGGED, VERIFIED CALL.** -/
theorem refund_logged {h : Hash} {z0 : UInt256} {hl : LeafHash} {cv : CommitValue}
    {fh : FlowHash} {S : System} {Ms : Managers} {log : List AuthCall}
    (hr : ReachLog h z0 hl cv fh S emptyManagers Ms log) :
    ∀ (o : Obligation), Refunded Ms o →
      ∃ a ∈ log, a.Verified h z0 hl cv fh S ∧ obligationOf a.flow a.leg = o := by
  induction hr with
  | refl =>
    intro o hrf
    exfalso
    simp only [Refunded, stateOf_emptyManagers] at hrf
    simp [rank] at hrf
  | @append Ns log c f b _ _ ih =>
    intro o hrf
    by_cases heq : o = ⟨f, b, c⟩
    · exfalso
      subst heq
      simp only [Refunded, stateOf_setAt_self] at hrf
      simp [rank] at hrf
    · exact ih o (by simpa only [Refunded, stateOf_setAt_other heq] using hrf)
  | @authorize Ns log a _ hv _ ih =>
    intro o hrf
    by_cases heq : o = obligationOf a.flow a.leg
    · exact ⟨a, List.mem_cons_self, hv, heq.symm⟩
    · rw [obligationOf_eq] at heq
      obtain ⟨a', ha', hv', hobl⟩ :=
        ih o (by simpa only [Refunded, stateOf_setAt_other heq] using hrf)
      exact ⟨a', List.mem_cons_of_mem _ ha', hv', hobl⟩
  | @claim Ns log c f b _ hg ih =>
    intro o hrf
    by_cases heq : o = ⟨f, b, c⟩
    · subst heq
      refine ih _ ?_
      simp only [Refunded, stateOf]
      rw [show (Ns c).legState f b = LegState.Revertable from hg]
      simp [rank]
    · exact ih o (by simpa only [Refunded, stateOf_setAt_other heq] using hrf)

theorem refund_implies_own_flow_timeout_or_logged_clash {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {cv : CommitValue} {fh : FlowHash} {S : System} {F : Flow} {leg : FlowLeg}
    (hchk : FlowIdChecked fh F) {Ms : Managers} {log : List AuthCall}
    (hr : ReachLog h z0 hl cv fh S emptyManagers Ms log) (hrf : Refunded Ms (obligationOf F leg)) :
    RefundAuthorized h z0 hl cv S F
      ∨ ∃ a ∈ log, obligationOf a.flow a.leg = obligationOf F leg ∧ FlowIdClash fh F a.flow := by
  obtain ⟨a, ha, ⟨hchk', _, hmiss, href⟩, hobl⟩ := refund_logged hr _ hrf
  have hid : F.flowId = a.flow.flowId := (congrArg Obligation.flowId hobl).symm
  rcases flowId_check_pins_legList_or_collision hchk hchk' hid with heq | hcl
  · subst heq
    exact Or.inl ⟨a.missing, hmiss, a.batch, a.proof, href⟩
  · exact Or.inr ⟨a, ha, hobl, hcl⟩

/-- **AN EXECUTED FLOW'S OBLIGATIONS ARE FROZEN, OR A LOCATED BREAK.** -/
theorem executed_freezes_flow_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {F : Flow} {ev : GateEvidence}
    {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg) {Ms : Managers}
    {log : List AuthCall} (hr : ReachLog h z0 hl cv fh S emptyManagers Ms log)
    (o : Obligation) (ho : o.flowId = F.flowId) :
    ¬ Refunded Ms o ∨ RefundBreak h z0 hl fh S F ev o log := by
  by_cases hrf : Refunded Ms o
  · refine Or.inr ?_
    obtain ⟨a, ha, ⟨hchk', _, hmiss, href⟩, hobl⟩ := refund_logged hr o hrf
    have hid : F.flowId = a.flow.flowId := by
      rw [← ho, ← hobl]; rfl
    rcases flowId_check_pins_legList_or_collision hex.2.1 hchk' hid with heq | hcl
    · have hmiss' : a.missing ∈ F.legs := by rw [heq]; exact hmiss
      have href' : LegRefundableBy h z0 hl cv S F a.missing a.batch a.proof := by
        rw [heq]; exact href
      rcases executed_excludes_any_refund_or_break hS hex a.missing hmiss' a.batch a.proof
        with hn | hb | hb
      · exact absurd href' hn
      · exact RefundBreak.inclusion a ha hobl heq.symm hb
      · exact RefundBreak.absence a ha hobl heq.symm hb
    · exact RefundBreak.flowIdClash a ha hobl hcl
  · exact Or.inl hrf

/-! ### Anti-vacuity witnesses -/

/-- `subsetFlow 0 1` executes in `mixedSystem 1` on the honest proof of leaf 1, whatever
flow hash checks it, and that proof carries no break. -/
theorem subsetFlow_executes (h : Hash) (z0 : UInt256) (hl : LeafHash) (fh : FlowHash)
    (hchk : FlowIdChecked fh (subsetFlow 0 1)) :
    ExecutedViaBy h z0 hl (fun _ _ => 1) fh (mixedSystem 1) (subsetFlow 0 1)
        (fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1)) ⟨0, 1⟩
      ∧ ¬ InclusionBreak h z0 hl (mixedSystem 1) 0 0 (honestProof h z0 hl (mixedSystem 1) 0 0 1) := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hS := mixedSystem_wf h1
  have hcount : ((mixedSystem 1).tree 0 0).leafCount = 2 := by
    rw [mixedSystem_tree_zero]; rfl
  have hacc : Accepts h z0 hl (mixedSystem 1) 0 0 1 (honestProof h z0 hl (mixedSystem 1) 0 0 1) := by
    have := inclusion_complete (h := h) (z0 := z0) (hl := hl) (T := (mixedSystem 1).tree 0 0)
      (height := (mixedSystem 1).height 0 0) (hS.capacity 0 0) (i := 1) (by rw [hcount]; norm_num)
    have hv : (((mixedSystem 1).tree 0 0).leaf 1).value = 1 := by
      rw [mixedSystem_tree_zero, insertSetup_leaf_one_value]
    rw [hv] at this
    exact this
  refine ⟨⟨List.mem_singleton_self _, hchk, ?_⟩,
    honestProof_no_break h z0 hl _ 0 0 1 (by rw [hcount]; norm_num)⟩
  intro l hl'
  obtain rfl : l = ⟨0, 1⟩ := List.mem_singleton.mp hl'
  exact ⟨by simp [subsetFlow], hacc⟩

/-- The two-flow run in `mixedSystem 1`: the obligation of leg `⟨1, 2⟩` of
`mixedFlow 1 1 2` is appended, then authorized for refund on the honest absence proof of
`setup` at batch 1 (its chain never commits). -/
def twoFlowCall (h : Hash) (z0 : UInt256) (hl : LeafHash) : AuthCall :=
  ⟨mixedFlow 1 1 2, ⟨1, 2⟩, ⟨1, 2⟩, 1, ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩⟩

def twoFlowM1 : Managers := setAt emptyManagers 1 ((emptyManagers 1).set 1 2 .Committed)

def twoFlowMs : Managers := setAt twoFlowM1 1 ((twoFlowM1 1).set 1 2 .Revertable)

theorem lengthFlowHash_checks_subset : FlowIdChecked lengthFlowHash (subsetFlow 0 1) := by
  simp [FlowIdChecked, lengthFlowHash, subsetFlow]

theorem lengthFlowHash_checks_mixed : FlowIdChecked lengthFlowHash (mixedFlow 1 1 2) := by
  simp [FlowIdChecked, lengthFlowHash, mixedFlow]

theorem twoFlow_run (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    ReachLog h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) emptyManagers twoFlowMs
      [twoFlowCall h z0 hl] := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hne : (1 : Chain) ≠ 0 := by decide
  have hbegin : beginTree (mixedSystem 1) 1 1 = setup := mixedSystem_tree_other hne 0
  have hbeginH : beginHeight (mixedSystem 1) 1 1 = 0 := mixedSystem_height_other hne 0
  have hmem : (⟨1, 2⟩ : FlowLeg) ∈ (mixedFlow 1 1 2).legs := by simp [mixedFlow]
  have href : LegRefundableBy h z0 hl (fun _ _ => 1) (mixedSystem 1) (mixedFlow 1 1 2) ⟨1, 2⟩ 1
      ⟨⟨0, 0, 0⟩, 0, honestSibs h z0 (leafHashes hl setup) 0, 0⟩ := by
    refine Or.inl ⟨by norm_num [mixedFlow], ?_⟩
    show AbsenceAccepted h z0 hl (beginTree (mixedSystem 1) 1 1)
      (beginHeight (mixedSystem 1) 1 1) 1 _
    rw [hbegin, hbeginH]
    exact setup_absence_accepted h z0 hl h1
  have happ : ReachLog h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) emptyManagers
      twoFlowM1 [] := ReachLog.append (c := 1) (f := 1) (b := 2) ReachLog.refl rfl
  have hguard : AuthorizeGuard (twoFlowM1 1) 1 2 := by
    show (twoFlowM1 1).legState 1 2 = .Committed
    simp [twoFlowM1, setAt, Manager.set]
  exact ReachLog.authorize (twoFlowCall h z0 hl) happ
    ⟨lengthFlowHash_checks_mixed, hmem, hmem, href⟩ hguard

theorem executed_obligation_never_refunded_or_break_witness (h : Hash) (z0 : UInt256)
    (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg) (Ms : Managers) (log : List AuthCall),
      Wf S ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ReachLog h z0 hl cv fh S emptyManagers Ms log ∧ log ≠ []
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log
        ∧ ¬ Refunded Ms (obligationOf F leg) := by
  have h1 : (0 : UInt256) < 1 := by decide
  refine ⟨fun _ _ => 1, lengthFlowHash, mixedSystem 1, subsetFlow 0 1,
    fun _ => (0, honestProof h z0 hl (mixedSystem 1) 0 0 1), ⟨0, 1⟩, twoFlowMs,
    [twoFlowCall h z0 hl], mixedSystem_wf h1,
    (subsetFlow_executes h z0 hl lengthFlowHash lengthFlowHash_checks_subset).1,
    twoFlow_run h z0 hl, List.cons_ne_nil _ _, ?_, ?_⟩
  · have hneq : obligationOf (twoFlowCall h z0 hl).flow (twoFlowCall h z0 hl).leg
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
  · show ¬ 2 ≤ rank (stateOf (setAt twoFlowM1 1 ((twoFlowM1 1).set 1 2 .Revertable)) ⟨0, 1, 0⟩)
    have hne : (⟨0, 1, 0⟩ : Obligation) ≠ ⟨1, 2, 1⟩ := by decide
    rw [stateOf_setAt_other hne]
    show ¬ 2 ≤ rank (stateOf (setAt emptyManagers 1 ((emptyManagers 1).set 1 2 .Committed))
      ⟨0, 1, 0⟩)
    rw [stateOf_setAt_other hne, stateOf_emptyManagers]
    simp [rank]

theorem refund_implies_own_flow_timeout_or_logged_clash_witness (h : Hash) (z0 : UInt256)
    (hl : LeafHash) :
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (leg : FlowLeg)
      (Ms : Managers) (log : List AuthCall),
      FlowIdChecked fh F ∧ leg ∈ F.legs ∧ ReachLog h z0 hl cv fh S emptyManagers Ms log
        ∧ Refunded Ms (obligationOf F leg)
        ∧ ¬ ∃ a ∈ log, obligationOf a.flow a.leg = obligationOf F leg ∧ FlowIdClash fh F a.flow := by
  refine ⟨fun _ _ => 1, lengthFlowHash, mixedSystem 1, mixedFlow 1 1 2, ⟨1, 2⟩, twoFlowMs,
    [twoFlowCall h z0 hl], lengthFlowHash_checks_mixed, by simp [mixedFlow],
    twoFlow_run h z0 hl, ?_, ?_⟩
  · show 2 ≤ rank (stateOf (setAt twoFlowM1 1 ((twoFlowM1 1).set 1 2 .Revertable)) ⟨1, 2, 1⟩)
    rw [stateOf_setAt_self]; simp [rank]
  · rintro ⟨a, ha, _, hcl⟩
    rw [List.mem_singleton] at ha
    subst ha
    exact hcl.1 rfl

theorem padding_refund_of_executed_obligation_locates_absence_break (h : Hash) (hl : LeafHash)
    (a b : UInt256) (ha : 0 < a) (hab : a < b) :
    ∃ (cv : CommitValue) (fh : FlowHash) (F : Flow) (ev : GateEvidence) (leg : FlowLeg)
      (Ms : Managers) (log : List AuthCall),
      Wf (paddedSystem a b) ∧ ExecutedViaBy h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) F ev leg
        ∧ ReachLog h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) emptyManagers Ms log
        ∧ Refunded Ms (obligationOf F leg)
        ∧ RefundBreak h (hl ⟨0, 0, 0⟩) hl fh (paddedSystem a b) F ev (obligationOf F leg) log
        ∧ ∀ c ∈ log, c.flow = F ∧ ¬ FlowIdClash fh F c.flow
            ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) c.missing.chain
                (ev c.missing).1 (ev c.missing).2
            ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) F.deadline c.missing.chain
                c.batch c.proof := by
  let z0 := hl ⟨0, 0, 0⟩
  let T := threeLeafTree a b
  let F : Flow := subsetFlow 0 0
  let p : ImtProof := ⟨T.leaf 1, 1, honestSibs h z0 (leafHashes hl T) 1, 2⟩
  let q : ImtProof := ⟨⟨0, 0, 0⟩, 3, honestSibs h z0 (leafHashes hl T) 3, 2⟩
  let call : AuthCall := ⟨F, ⟨0, 0⟩, ⟨0, 0⟩, 0, q⟩
  let M1 : Managers := setAt emptyManagers 0 ((emptyManagers 0).set 0 0 .Committed)
  obtain ⟨_, hI, hN⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  obtain ⟨hnb, hpad⟩ := padding_countermodel_locates_padding_hit h hl a b
  have hchk : FlowIdChecked (honestFlowHash F) F := (honest_flowHash_no_clash F).1
  have hmem : (⟨0, 0⟩ : FlowLeg) ∈ F.legs := List.mem_singleton_self _
  have href : LegRefundableBy h z0 hl (fun _ _ => a) (paddedSystem a b) F ⟨0, 0⟩ 0 q :=
    Or.inr ⟨⟨le_refl 0, fun m hm => hm⟩, hN⟩
  have hab' : AbsenceBreak h z0 hl (paddedSystem a b) F.deadline (0 : Chain) 0 q :=
    Or.inr ⟨le_refl 0, hpad⟩
  have happ : ReachLog h z0 hl (fun _ _ => a) (honestFlowHash F) (paddedSystem a b)
      emptyManagers M1 [] := ReachLog.append (c := 0) (f := 0) (b := 0) ReachLog.refl rfl
  have hguard : AuthorizeGuard (M1 0) 0 0 := by
    show (M1 0).legState 0 0 = .Committed
    simp [M1, setAt, Manager.set]
  have hrun := ReachLog.authorize call happ ⟨hchk, hmem, hmem, href⟩ hguard
  refine ⟨fun _ _ => a, honestFlowHash F, F, fun _ => (0, p), ⟨0, 0⟩, _, [call],
    paddedSystem_wf ha hab, ⟨hmem, hchk, ?_⟩, hrun, ?_,
    RefundBreak.absence call (List.mem_singleton_self _) rfl rfl hab', ?_⟩
  · intro l hl'
    obtain rfl : l = ⟨0, 0⟩ := List.mem_singleton.mp hl'
    exact ⟨le_refl 0, hI⟩
  · show 2 ≤ rank (stateOf (setAt M1 0 ((M1 0).set 0 0 .Revertable)) ⟨0, 0, 0⟩)
    rw [stateOf_setAt_self]; simp [rank]
  · intro c hc
    rw [List.mem_singleton] at hc
    subst hc
    exact ⟨rfl, fun hcl => hcl.1 rfl, hnb, hab'⟩

end Contracts.Refund

namespace Contracts.Refund

theorem ReachIffReachLog : Properties.ReachIffReachLog :=
  fun _ _ _ _ _ _ _ _ => reach_iff_reachLog
theorem RefundNeedsLoggedAuthorize : Properties.RefundNeedsLoggedAuthorize :=
  fun _ _ _ _ _ _ _ _ hr o hrf => refund_logged hr o hrf
theorem RefundImpliesOwnFlowTimeoutOrLoggedClash :
    Properties.RefundImpliesOwnFlowTimeoutOrLoggedClash :=
  fun _ _ _ _ _ _ _ _ hchk _ _ _ hr hrf =>
    refund_implies_own_flow_timeout_or_logged_clash hchk hr hrf
theorem ExecutedObligationNeverRefundedOrBreak :
    Properties.ExecutedObligationNeverRefundedOrBreak :=
  fun _ _ _ _ _ _ hS _ _ _ hex _ _ hr => executed_freezes_flow_or_break hS hex hr _ rfl
theorem OneExecutionFreezesTheFlowOrBreak : Properties.OneExecutionFreezesTheFlowOrBreak :=
  fun _ _ _ _ _ _ hS _ _ _ hex _ _ hr _ _ => executed_freezes_flow_or_break hS hex hr _ rfl
theorem RefundedFlowMissedDeadlineOrBreak : Properties.RefundedFlowMissedDeadlineOrBreak :=
  fun _ _ _ _ _ hS _ hagg _ _ _ _ hv => Contracts.Timeout.timeout_means_missed_deadline_or_break hS hagg hv
theorem ExecutedObligationNeverRefundedOrBreakWitness :
    Properties.ExecutedObligationNeverRefundedOrBreakWitness :=
  executed_obligation_never_refunded_or_break_witness
theorem RefundImpliesOwnFlowTimeoutOrLoggedClashWitness :
    Properties.RefundImpliesOwnFlowTimeoutOrLoggedClashWitness :=
  refund_implies_own_flow_timeout_or_logged_clash_witness
theorem PaddingRefundOfExecutedObligationLocatesAbsenceBreak :
    Properties.PaddingRefundOfExecutedObligationLocatesAbsenceBreak :=
  padding_refund_of_executed_obligation_locates_absence_break

end Contracts.Refund

/-! ## The accepted-timeout chain without hash premises -/

namespace Contracts.Refund

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager

theorem accepted_timeout_authorizes_pinned {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {ze : UInt256} {R : SlRoot} {B : RootBacking h ze R}
    (hagg : Aggregates S R) {F : Flow} {leg : FlowLeg} {N : ℕ} {p : ImtProof}
    {sibs : ℕ → UInt256} {x : UInt256} (hmem : leg ∈ F.legs)
    (ha : LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x) :
    RefundAuthorized h z0 hl cv S F ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x)) := by
  rcases accepted_implies_refundable_pinned hagg ha with hr | hrest
  · exact Or.inl ⟨leg, hmem, hr⟩
  · exact Or.inr hrest

theorem executed_excludes_accepted_refund_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {fh : FlowHash} {S : System} (hS : Wf S) {ze : UInt256} {R : SlRoot}
    {B : RootBacking h ze R} (hagg : Aggregates S R) {F : Flow} {ev : GateEvidence}
    {leg : FlowLeg} (hex : ExecutedViaBy h z0 hl cv fh S F ev leg) (other : FlowLeg)
    (hother : other ∈ F.legs) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256) :
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
      · exact Or.inl (refundableBy_of_verifiedBy hagg (Or.inl ⟨hb, habs⟩))
      · rcases endBranch_of_accepted_pinned he with hver | hrest
        · exact Or.inl (refundableBy_of_verifiedBy hagg (Or.inr ⟨hver, habs⟩))
        · exact Or.inr ⟨he, hrest⟩
    rcases hv with hr | hrest
    · rcases executed_excludes_any_refund_or_break hS hex other hother N p with hn | hb | hb
      · exact absurd hr hn
      · exact Or.inl hb
      · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hrest)
  · exact Or.inl ha

/-! ### Anti-vacuity witnesses -/

theorem demo_no_pinned_break_any (N : ℕ) :
    ¬ PinnedBreak demoHash 0 (demoBacking.leaves 0) N :=
  no_pinned_break_bounded demoBacking 0 N demo_entriesNotEmpty
    (fun p q hp hq => demo_pairInjOn p q (Or.inl hp) (Or.inl hq))

theorem accepted_timeout_authorizes_pinned_witness :
    Properties.AcceptedTimeoutAuthorizesPinnedWitness := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hmem : (⟨0, 0⟩ : FlowLeg) ∈ (⟨0, [⟨0, 0⟩], 0⟩ : Flow).legs := List.mem_singleton_self _
  have habs : AbsenceAccepted demoHash 0 (fun _ => 0) (demoSystem.tree 0 1) (demoSystem.height 0 1)
      1 ⟨⟨0, 0, 0⟩, 0, honestSibs demoHash 0 (leafHashes (fun _ => 0) setup) 0, 0⟩ :=
    setup_absence_accepted demoHash 0 (fun _ => 0) h1
  have hacc : LegRefundableAcceptedBy demoHash 0 (fun _ => 0) (fun _ _ => 1) demoSystem demoBacking
      ⟨0, [⟨0, 0⟩], 0⟩ ⟨0, 0⟩ 1 ⟨⟨0, 0, 0⟩, 0, honestSibs demoHash 0 (leafHashes (fun _ => 0) setup) 0, 0⟩
      (honestSibs demoHash 0 [5, 7] 1) 7 :=
    Or.inr ⟨demo_endBranchAccepted, habs⟩
  refine ⟨demoHash, 0, fun _ => 0, fun _ _ => 1, demoSystem, 0, demoRoot, demoBacking,
    ⟨0, [⟨0, 0⟩], 0⟩, ⟨0, 0⟩, 1, _, honestSibs demoHash 0 [5, 7] 1, 7, demoSystem_aggregates,
    hmem, hacc, demo_endBranchAccepted, demo_no_pinned_break_any 1,
    honest_walk_no_collision demoHash 0 [5, 7] 2 1, ?_⟩
  rcases accepted_timeout_authorizes_pinned demoSystem_aggregates hmem hacc with hr | ⟨_, hb | hc⟩
  · exact hr
  · exact absurd hb (demo_no_pinned_break_any 1)
  · exact absurd hc (honest_walk_no_collision demoHash 0 [5, 7] 2 1)

theorem executed_excludes_accepted_refund_or_break_witness :
    Properties.ExecutedExcludesAcceptedRefundOrBreakWitness := by
  have h1 : (0 : UInt256) < 1 := by decide
  have hS := mixedSystem_wf h1
  have hagg : Aggregates (mixedSystem 1) demoRoot := fun _ _ hn => hn
  obtain ⟨hex, hnb⟩ := subsetFlow_executes demoHash 0 (fun _ => 0) lengthFlowHash
    lengthFlowHash_checks_subset
  have hnab : ¬ AbsenceBreak demoHash 0 (fun _ => 0) (mixedSystem 1) (subsetFlow 0 1).deadline 0 0
      (honestProof demoHash 0 (fun _ => 0) (mixedSystem 1) 0 0 1) := by
    rintro (⟨hlate, _⟩ | ⟨_, hb⟩)
    · exact absurd hlate (by simp [subsetFlow])
    · exact hnb hb
  have hnp := demo_no_pinned_break_any 0
  have hnc := honest_walk_no_collision demoHash 0 [5, 7] 2 0
  refine ⟨demoHash, 0, fun _ => 0, fun _ _ => 1, lengthFlowHash, mixedSystem 1, 0, demoRoot,
    demoBacking, subsetFlow 0 1, fun _ => (0, honestProof demoHash 0 (fun _ => 0) (mixedSystem 1) 0 0 1),
    ⟨0, 1⟩, 0, honestProof demoHash 0 (fun _ => 0) (mixedSystem 1) 0 0 1,
    honestSibs demoHash 0 [5, 7] 0, ([5, 7] : List UInt256).getD 0 0, hS, hagg, hex, hnb, hnab,
    hnp, hnc, ?_⟩
  rcases executed_excludes_accepted_refund_or_break hS hagg hex ⟨0, 1⟩ (List.mem_singleton_self _)
      0 (honestProof demoHash 0 (fun _ => 0) (mixedSystem 1) 0 0 1)
      (honestSibs demoHash 0 [5, 7] 0) (([5, 7] : List UInt256).getD 0 0) with hn | hb | hb | ⟨_, hb | hb⟩
  · exact hn
  · exact absurd hb hnb
  · exact absurd hb hnab
  · exact absurd hb hnp
  · exact absurd hb hnc

/-- A backing for `timeOneRoot` under any node hash: two batch leaves, height 1. -/
def trivialBacking (h : Hash) (ze : UInt256) : RootBacking h ze timeOneRoot where
  leaves := fun _ => [0, 0]
  height := fun _ => 1
  upToLast := fun _ => rfl
  capacity := fun _ => by norm_num

theorem padding_accepted_refund_locates_absence_break :
    Properties.PaddingAcceptedRefundLocatesAbsenceBreak := by
  intro h hl a b ha hab
  let z0 := hl ⟨0, 0, 0⟩
  let T := threeLeafTree a b
  let F : Flow := subsetFlow 0 0
  let p : ImtProof := ⟨T.leaf 1, 1, honestSibs h z0 (leafHashes hl T) 1, 2⟩
  have hbegin : beginTree (paddedSystem a b) 0 1 = T := paddedSystem_tree_zero a b 0
  have hbeginH : beginHeight (paddedSystem a b) 0 1 = 2 := paddedSystem_height_zero a b 0
  obtain ⟨_, hI, hN⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  obtain ⟨hnb, hpad⟩ := padding_countermodel_locates_padding_hit h hl a b
  refine ⟨0, trivialBacking h 0, fun _ _ => a, honestFlowHash F, F, fun _ => (0, p), ⟨0, 0⟩, 1,
    ⟨⟨0, 0, 0⟩, 3, honestSibs h z0 (leafHashes hl T) 3, 2⟩,
    paddedSystem_wf ha hab, timeOneRoot_aggregates_padded a b,
    ⟨List.mem_singleton_self _, (honest_flowHash_no_clash F).1, ?_⟩, ?_, hnb, ?_⟩
  · intro l hl'
    obtain rfl : l = ⟨0, 0⟩ := List.mem_singleton.mp hl'
    exact ⟨le_refl 0, hI⟩
  · intro sibs x
    refine Or.inl ⟨⟨by norm_num [F, timeOneRoot, subsetFlow], by norm_num [F, subsetFlow]⟩, ?_⟩
    show AbsenceAccepted h z0 hl (beginTree (paddedSystem a b) 0 1)
      (beginHeight (paddedSystem a b) 0 1) a _
    rw [hbegin, hbeginH]
    exact hN
  · refine Or.inl ⟨by norm_num [F, subsetFlow], ?_⟩
    unfold ImtProofBreak
    rw [hbegin, hbeginH]
    exact hpad

end Contracts.Refund

namespace Contracts.Refund

theorem AcceptedTimeoutAuthorizesPinned : Properties.AcceptedTimeoutAuthorizesPinned :=
  fun _ _ _ _ _ _ _ _ hagg _ _ _ _ _ _ hmem ha => accepted_timeout_authorizes_pinned hagg hmem ha
theorem AcceptedTimeoutAuthorizesPinnedWitness : Properties.AcceptedTimeoutAuthorizesPinnedWitness :=
  accepted_timeout_authorizes_pinned_witness
theorem ExecutedExcludesAcceptedRefundOrBreak : Properties.ExecutedExcludesAcceptedRefundOrBreak :=
  fun _ _ _ _ _ _ hS _ _ _ hagg _ _ _ hex other hother N p sibs x =>
    executed_excludes_accepted_refund_or_break hS hagg hex other hother N p sibs x
theorem ExecutedExcludesAcceptedRefundOrBreakWitness :
    Properties.ExecutedExcludesAcceptedRefundOrBreakWitness :=
  executed_excludes_accepted_refund_or_break_witness
theorem PaddingAcceptedRefundLocatesAbsenceBreak :
    Properties.PaddingAcceptedRefundLocatesAbsenceBreak :=
  padding_accepted_refund_locates_absence_break

end Contracts.Refund
