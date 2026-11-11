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
  push_neg at hno
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
  exact hne (indexHash_inj_on hPlen (List.mem_map_of_mem (fun o => (o.flowId, o.bundleHash)) ho)
    (List.mem_map_of_mem (fun o => (o.flowId, o.bundleHash)) ho') heq)

theorem HonestCommitValueNoClash : Properties.HonestCommitValueNoClash := by
  rintro o o' ⟨hne, heq⟩
  have hne' : ¬ (o'.flowId, o'.bundleHash) = (o.flowId, o.bundleHash) := fun h => hne h.symm
  simp only [honestCommitValue, if_pos rfl, if_neg hne'] at heq
  exact absurd heq (by decide)

end Contracts.Refund
