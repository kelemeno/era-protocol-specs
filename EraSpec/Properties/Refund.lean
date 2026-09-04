import EraSpec.Contracts.Refund

/-!
# Properties: the refund path, composed

Statements about `EraSpec.Contracts.Refund`.  Proofs are in
`EraSpec.Proofs.Refund`.

## What this layer adds

`Properties.AtomicFlowManager` says a refund cannot be *taken twice*.
`Properties.Atomicity` says an executed leg cannot be *proven absent*.  Neither
says a refund cannot happen after an execution, because neither knows about both
halves at once.  This file does:

* `RefundNeedsTimeoutProof` — no leg ever leaves `Committed` without a verified
  timeout proof for the flow.  This is the manager side, by induction over runs.
* `NoExecutedLegAndRefundedLeg` — **the capstone**: no flow has both a leg executed
  on its destination and a leg refunded on its source chain.  All-or-nothing at the
  outcome level, which is what "atomic" is supposed to mean.
* `ExecutedImpliesNoRefundReachable` — the operational form: once any leg has
  executed, `authorizeRefund` can never succeed for that flow, in any reachable
  manager state.
* `TimeoutProofRefundsEveryCommittedLeg` — the other branch is live: once a
  timeout proof exists, every leg still `Committed` on this chain can be moved to
  `Revertable`.  Nothing further is asked of the leg, which is why a timed-out flow
  refunds all of its committed legs rather than some of them.

Together with `Properties.Atomicity.NoneOrAll` this closes the dichotomy: either
every leg can be finalized, or nothing was executed and every committed leg can be
refunded.
-/

namespace Properties.Refund

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.AtomicFlowManager Contracts.Refund

/-- **NO REFUND WITHOUT A TIMEOUT PROOF.**  If a leg is past `Committed` in a
reachable manager state, then a timeout absence proof for some leg of the flow
verified along the way.

The `NoRefundYet` hypothesis on the starting state is what makes this a statement
about the run rather than about the start: from fresh storage it is free. -/
def RefundNeedsTimeoutProof : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (F : Flow)
    (M N : Manager),
    GuardedReach h z0 hl cv S F M N → NoRefundYet M → SomeRefund N →
      RefundAuthorized h z0 hl cv S F

/-- The same from fresh storage, where the hypothesis discharges itself. -/
def RefundFromEmptyNeedsTimeoutProof : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (F : Flow)
    (N : Manager),
    GuardedReach h z0 hl cv S F empty N → SomeRefund N → RefundAuthorized h z0 hl cv S F

/-- **ONCE A LEG EXECUTES, NO REFUND IS EVER AUTHORIZED.**  For a flow with an
executed leg, every reachable manager state on every source chain still has all its
legs `Unset` or `Committed`: `authorizeRefund` cannot succeed, so `claimRefund`
never opens. -/
def ExecutedImpliesNoRefundReachable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (S : System), Wf S →
    ∀ (F : Flow) (leg : FlowLeg), ExecutedVia h z0 hl cv fh S F leg →
    ∀ (M N : Manager), GuardedReach h z0 hl cv S F M N → NoRefundYet M → NoRefundYet N

/-- **THE CAPSTONE: ALL OR NOTHING.**  No flow has both a leg executed on its
destination and a leg refunded on its source chain.

This is the statement `Properties.AtomicFlowManager` and `Properties.Atomicity`
each half of.  The proof composes them: a refund implies a verified timeout proof
(manager side), and an executed leg makes every timeout proof of that flow
unverifiable (tree side). -/
def NoExecutedLegAndRefundedLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (S : System), Wf S → ∀ (F : Flow) (N : Manager),
      GuardedReach h z0 hl cv S F empty N →
      ¬ ((∃ leg, ExecutedVia h z0 hl cv fh S F leg) ∧ SomeRefund N)

/-- **THE REFUND BRANCH IS LIVE.**  Once a timeout proof for the flow exists, every
leg still `Committed` on this chain can be moved to `Revertable` — the contract's
loop does exactly this and asks nothing further of the leg.

So the "nothing" branch of the dichotomy is not merely the absence of execution: it
is a positive guarantee that each committed leg reaches the refund state. -/
def TimeoutProofRefundsEveryCommittedLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (F : Flow)
    (M : Manager),
    RefundAuthorized h z0 hl cv S F → ∀ (f b : UInt256), AuthorizeGuard M f b →
      GuardedStep h z0 hl cv S F M (M.set f b .Revertable)

end Properties.Refund
