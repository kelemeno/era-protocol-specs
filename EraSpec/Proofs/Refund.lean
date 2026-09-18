import EraSpec.Properties.Refund
import EraSpec.Proofs.Timeout
import EraSpec.Proofs.AtomicFlowManager

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
    simp only [setAt, if_pos hc]
    rw [set_other hkey, hc]
  · show (setAt Ms c ((Ms c).set f b s) o.chain).legState o.flowId o.bundleHash
      = (Ms o.chain).legState o.flowId o.bundleHash
    simp only [setAt, if_neg hc]

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

namespace Proofs.Refund

open Contracts.Refund

theorem RefundNeedsOwnFlowTimeout : Properties.Refund.RefundNeedsOwnFlowTimeout :=
  fun _ _ _ _ _ _ _ hr o hrf => refund_needs_own_flow_timeout hr o hrf
theorem RefundImpliesOwnFlowTimeout : Properties.Refund.RefundImpliesOwnFlowTimeout :=
  fun _ _ _ _ _ hinj _ _ _ hchk hmem _ hr hrf =>
    refund_implies_own_flow_timeout hinj hchk hmem hr hrf
theorem ExecutedObligationNeverRefunded : Properties.Refund.ExecutedObligationNeverRefunded :=
  fun _ _ _ hA _ _ hinj _ hS _ _ _ hchk hex _ hr =>
    executed_obligation_never_refunded hA hinj hS hchk hex hr
theorem OneExecutionFreezesTheFlow : Properties.Refund.OneExecutionFreezesTheFlow :=
  fun _ _ _ hA _ _ hinj _ hS _ _ _ hchk hex _ hr _ _ =>
    executed_freezes_flow hA hinj hS hchk hex hr _ rfl
theorem VerifiedTimeoutAuthorizes : Properties.Refund.VerifiedTimeoutAuthorizes :=
  fun _ _ _ _ _ _ hagg _ _ hmem hv => verified_timeout_authorizes hagg hmem hv
theorem RefundedFlowMissedDeadline : Properties.Refund.RefundedFlowMissedDeadline :=
  fun _ _ _ hA _ _ hS _ hagg _ _ hv n hon =>
    Contracts.Timeout.timeout_means_missed_deadline hA hS hagg hv n hon
theorem CrossFlowRefundYieldsCollision : Properties.Refund.CrossFlowRefundYieldsCollision :=
  fun _ _ _ hF hF' hid hne => cross_flow_refund_yields_collision hF hF' hid hne
theorem AcceptedTimeoutAuthorizes : Properties.Refund.AcceptedTimeoutAuthorizes :=
  fun _ _ _ hA _ _ _ _ _ hagg _ _ hmem ha => accepted_timeout_authorizes hA hagg hmem ha
theorem AcceptedTimeoutForDeliveredFlowIsABreak :
    Properties.Refund.AcceptedTimeoutForDeliveredFlowIsABreak :=
  fun _ _ _ hA _ _ _ hS _ _ _ hagg _ _ hex other hother ha =>
    accepted_timeout_for_delivered_flow_is_a_break hA hS hagg hex other hother ha
theorem SharedCommitmentYieldsCollision : Properties.Refund.SharedCommitmentYieldsCollision :=
  shared_commitment_yields_collision
theorem CommitmentPinsLeg : Properties.Refund.CommitmentPinsLeg :=
  fun _ hinj o o' heq => commitment_pins_leg hinj o o' heq
theorem TimeoutProofRefundsCommittedLeg : Properties.Refund.TimeoutProofRefundsCommittedLeg :=
  fun _ _ _ _ _ _ _ _ _ hchk hmem hauth hg => Step.authorize hchk hmem hauth hg

end Proofs.Refund
