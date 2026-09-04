import EraSpec.Properties.Refund
import EraSpec.Proofs.Atomicity
import EraSpec.Proofs.AtomicFlowManager

/-!
# Proofs: the refund path, composed

The manager side is one induction over runs: only `authorize` can lift a leg to
rank 2, and it carries the timeout proof; `claim` needs rank 2 already, so it
inherits the witness.  The composition with the tree side is then a single
application of `Atomicity.executed_excludes_any_refund`.
-/

namespace Contracts.Refund

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.AtomicFlowManager

/-! ## The manager side -/

/-- **NO REFUND WITHOUT A TIMEOUT PROOF.** -/
theorem refund_needs_timeout_proof {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {F : Flow} {M N : Manager}
    (hreach : GuardedReach h z0 hl cv S F M N) (hM : NoRefundYet M) :
    SomeRefund N → RefundAuthorized h z0 hl cv S F := by
  induction hreach with
  | refl =>
    rintro ⟨f, b, hf⟩
    exact absurd hf (by have := hM f b; omega)
  | @tail N P hr hs ih =>
    rintro ⟨f, b, hf⟩
    cases hs with
    | @append f' b' hg =>
      -- `append` lands on rank 1, so the witness must be elsewhere
      by_cases he : f = f' ∧ b = b'
      · obtain ⟨rfl, rfl⟩ := he
        rw [set_same] at hf
        simp only [rank_committed] at hf
        omega
      · rw [set_other he] at hf
        exact ih ⟨f, b, hf⟩
    | @authorize f' b' _ hwit =>
      -- the step that authorizes carries the proof
      exact hwit
    | @claim f' b' hg =>
      -- `claim` needs `Revertable`, so the previous state already had rank 2
      refine ih ⟨f', b', ?_⟩
      rw [(hg : N.legState f' b' = .Revertable)]
      simp

theorem refund_from_empty_needs_timeout_proof {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {F : Flow} {N : Manager}
    (hreach : GuardedReach h z0 hl cv S F empty N) :
    SomeRefund N → RefundAuthorized h z0 hl cv S F :=
  refund_needs_timeout_proof hreach (fun _ _ => by simp [empty])

/-! ## The composition -/

/-- **ONCE A LEG EXECUTES, NO REFUND IS EVER AUTHORIZED.** -/
theorem executed_implies_no_refund_reachable {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash} {S : System}
    (hS : Wf S) {F : Flow} {leg : FlowLeg} (hex : ExecutedVia h z0 hl cv fh S F leg)
    {M N : Manager} (hreach : GuardedReach h z0 hl cv S F M N) (hM : NoRefundYet M) :
    NoRefundYet N := by
  intro f b
  by_contra hcon
  push_neg at hcon
  obtain ⟨other, hother, href⟩ :=
    refund_needs_timeout_proof hreach hM ⟨f, b, by omega⟩
  exact executed_excludes_any_refund hA hS hex other hother href

/-- **ALL OR NOTHING.**  No flow has both an executed leg and a refunded leg. -/
theorem no_executed_leg_and_refunded_leg {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {cv : CommitValue} {fh : FlowHash} {S : System}
    (hS : Wf S) {F : Flow} {N : Manager} (hreach : GuardedReach h z0 hl cv S F empty N) :
    ¬ ((∃ leg, ExecutedVia h z0 hl cv fh S F leg) ∧ SomeRefund N) := by
  rintro ⟨⟨leg, hex⟩, ⟨f, b, hf⟩⟩
  have hno := executed_implies_no_refund_reachable hA hS hex hreach
    (fun _ _ => by simp [empty])
  have := hno f b
  omega

/-- **THE REFUND BRANCH IS LIVE.** -/
theorem timeout_proof_refunds_every_committed_leg {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {cv : CommitValue} {S : System} {F : Flow} {M : Manager}
    (hwit : RefundAuthorized h z0 hl cv S F) (f b : UInt256) (hg : AuthorizeGuard M f b) :
    GuardedStep h z0 hl cv S F M (M.set f b .Revertable) :=
  GuardedStep.authorize hg hwit

end Contracts.Refund

/-! ## Certificates -/

namespace Proofs.Refund

open Contracts.Refund

theorem RefundNeedsTimeoutProof : Properties.Refund.RefundNeedsTimeoutProof :=
  fun _ _ _ _ _ _ _ _ hreach hM hsome => refund_needs_timeout_proof hreach hM hsome
theorem RefundFromEmptyNeedsTimeoutProof : Properties.Refund.RefundFromEmptyNeedsTimeoutProof :=
  fun _ _ _ _ _ _ _ hreach hsome => refund_from_empty_needs_timeout_proof hreach hsome
theorem ExecutedImpliesNoRefundReachable : Properties.Refund.ExecutedImpliesNoRefundReachable :=
  fun _ _ _ hA _ _ _ hS _ _ hex _ _ hreach hM =>
    executed_implies_no_refund_reachable hA hS hex hreach hM
theorem NoExecutedLegAndRefundedLeg : Properties.Refund.NoExecutedLegAndRefundedLeg :=
  fun _ _ _ hA _ _ _ hS _ _ hreach => no_executed_leg_and_refunded_leg hA hS hreach
theorem TimeoutProofRefundsEveryCommittedLeg :
    Properties.Refund.TimeoutProofRefundsEveryCommittedLeg :=
  fun _ _ _ _ _ _ _ hwit f b hg => timeout_proof_refunds_every_committed_leg hwit f b hg

end Proofs.Refund
