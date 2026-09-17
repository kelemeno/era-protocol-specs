import EraSpec.Contracts.Timeout

/-!
# Properties: the timeout decision is justified

Statements about `EraSpec.Contracts.Timeout`.  Proofs are in
`EraSpec.Proofs.Timeout`.

## What this removes from the safety argument

`Contracts.Atomicity.LegRefundable` carries `IsLastOnTime` as a branch condition
with nothing behind it.  `IsLastOnTimeDerived` supplies the missing step: from the
three comparisons `verifyTimeoutAbsence` actually makes — the root post-dates the
deadline, the batch settled by the deadline, the batch is last in that root — plus
the settlement layer's `Aggregates`, the "last in-time batch" fact follows.

`VerifiedImpliesRefundable` is the consequence for everything already proved: a
timeout the contract really verifies is an instance of the looser `LegRefundable`
that `Properties.Atomicity` and `Properties.Refund` are stated over, so those
safety results cover the real path **without** assuming the aggregation fact
anywhere.  They are stated over the looser predicate, which admits more refunds,
so excluding them is the stronger claim.

## What it adds

`TimeoutMeansMissedDeadline` is the positive statement, and the one worth reading:
a leg with a verified timeout proof was absent from its own source chain's tree at
**every** batch that settled by the deadline.  The refund is not merely permitted,
it is deserved — the obligation was never committed in time.

## What remains assumed, and why it is the right place for it

`Aggregates` — a batch that had settled when a root was created is inside that
root — is a property of how the settlement layer builds roots, not of the interop
contracts, so it cannot be derived here.  `StaleRootRefundsDeliveredLeg` is the
countermodel: with a root that omits an already-settled batch, a leg delivered on
time passes the timeout gate.  That is the exchange this file makes — an
unexplained condition inside the refund gate for a named property of the layer
below it, with a countermodel showing the property is load-bearing.
-/

namespace Properties.Timeout

open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open MerkleSpec IMTAbstract

/-! ## The derivation -/

/-- **"LAST BATCH IN THIS ROOT" MEANS "LAST BATCH IN TIME".**  What the END branch
verifies, plus the settlement layer's aggregation guarantee, gives exactly the fact
the refund gate needs — so `IsLastOnTime` stops being an assumption. -/
def IsLastOnTimeDerived : Prop :=
  ∀ (S : System) (R : SlRoot), Aggregates S R → ∀ (c : Chain) (D N : ℕ),
    EndBranchVerified S R c D N → IsLastOnTime S c D N

/-- **A VERIFIED TIMEOUT IS A REFUNDABLE LEG.**  So every safety result stated over
`LegRefundable` — `Properties.Atomicity.ExecutedExcludesAnyRefund` and the
composition in `Properties.Refund` — applies to the path the contract actually
takes, with no aggregation fact assumed in their statements. -/
def VerifiedImpliesRefundable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (R : SlRoot),
    Aggregates S R → ∀ (F : Flow) (leg : FlowLeg),
      LegRefundableVerified h z0 hl cv S R F leg → LegRefundable h z0 hl cv S F leg

/-! ## The justification -/

/-- **A REFUNDED LEG REALLY MISSED ITS DEADLINE.**  If the timeout gate verifies for
a leg, then its commit value was absent from its declared source chain's tree at
every batch that settled by the deadline — so no inclusion proof against an on-time
root could ever have existed for it.

This is the statement that makes the refund *justified* rather than merely
permitted, and it holds on both branches: a late batch's begin state is an earlier
batch's end state, and the last in-time batch is at or after every in-time batch. -/
def TimeoutMeansMissedDeadline : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (S : System), Wf S → ∀ (R : SlRoot), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg), LegRefundableVerified h z0 hl cv S R F leg →
    ∀ n, S.time leg.chain n ≤ F.deadline →
      legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n))

/-- The same conclusion in the form the finality gate consumes: a leg with a
verified timeout has no on-time batch it could be finalized against. -/
def TimeoutExcludesFinality : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (S : System), Wf S → ∀ (R : SlRoot), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg), LegRefundableVerified h z0 hl cv S R F leg →
      ¬ LegFinalized h z0 hl cv S F leg

/-! ## What is load-bearing -/

/-- **A STALE ROOT REFUNDS A DELIVERED LEG.**  One chain, two batches, both settled
at time `0` and so both on time for deadline `0`; the commit value enters during the
second.  A root created after the deadline that nevertheless stops at the first
batch makes the END branch verify — the batch really is on time, and really is the
last one *in that root* — while the leg was committed in time.

`Aggregates` is exactly what excludes this, which is why it is a hypothesis of
everything above rather than a remark. -/
def StaleRootRefundsDeliveredLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (F : Flow) (leg : FlowLeg), F.deadline = 0 →
      0 < legValue cv F leg →
      Wf (staleSystem (legValue cv F leg))
        ∧ ¬ Aggregates (staleSystem (legValue cv F leg)) staleRoot
        ∧ (staleSystem (legValue cv F leg)).time leg.chain 1 ≤ F.deadline
        ∧ legValue cv F leg
            ∈ keys (toAbs ((staleSystem (legValue cv F leg)).tree leg.chain 1))
        ∧ LegRefundableVerified h z0 hl cv (staleSystem (legValue cv F leg)) staleRoot F leg

end Properties.Timeout
