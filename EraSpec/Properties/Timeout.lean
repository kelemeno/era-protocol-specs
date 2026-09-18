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

`VerifiedImpliesRefundable` carries that over to everything already proved: a
timeout the contract really verifies is an instance of the looser `LegRefundable`
that `Properties.Atomicity` and `Properties.Refund` are stated over, and those are
stated over the *looser* predicate, which admits more refunds — so excluding them
is the stronger claim.

Be precise about what that buys, because it is easy to overstate.  The safety
results' own statements do not mention `Aggregates`.  But a conclusion about a
**verified** refund goes through `VerifiedImpliesRefundable`, so it inherits
`Aggregates` — the real-path claim carries that hypothesis, and the only
assumption-free statements are the ones about the looser predicate itself.

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
open MerkleSpec MerkleSpec.LastLeaf IMTAbstract

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
takes.  Note the hypothesis: applying them to a verified refund goes through this
lemma, so that conclusion carries `Aggregates` even though their own statements do
not mention it. -/
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

/-! ## The last-batch proof itself

`EndBranchVerified.lastInRoot` was still a conclusion taken as given.  These close
that gap: the accepted proof identifies the last included batch, or exhibits a
concrete hash break. -/

/-- **AN ACCEPTED LAST-BATCH PROOF IDENTIFIES THE LAST INCLUDED BATCH.**  What
`_verifyLastBatchInRoot` checks — every left-child sibling on the batch leaf's
authenticated path is that level's empty-subtree hash — pins the leaf to the end of
the chain's batch tree, or yields a `HashBreak`. -/
def LastBatchProofIdentifiesLastBatch : Prop :=
  ∀ (h : Hash) (ze : UInt256), (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (R : SlRoot) (B : RootBacking h ze R) (c : Chain) (N : ℕ) (sibs : ℕ → UInt256)
      (x : UInt256), LastBatchAccepted B c N sibs x →
      N = R.upTo c ∨ HashBreak h ze (B.leaves c)

/-- So the END branch as the contract runs it implies the END branch as the safety
argument assumed it. -/
def EndBranchAcceptedImpliesVerified : Prop :=
  ∀ (h : Hash) (ze : UInt256), (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (R : SlRoot) (B : RootBacking h ze R) (S : System) (c : Chain) (D N : ℕ)
      (sibs : ℕ → UInt256) (x : UInt256), EndBranchAccepted B S c D N sibs x →
      EndBranchVerified S R c D N ∨ HashBreak h ze (B.leaves c)

/-- **THE COMPLETE CHAIN.**  Accepted proof → last included batch → no later in-time
batch → the obligation was absent at every batch that settled in time.

Every link is now a theorem.  What is left on the far side is `Aggregates`, which is
a property of the settlement layer, and the `HashBreak` escape, which
`NoBreakUnderIdealizations` closes for anyone willing to assume keccak behaves. -/
def AcceptedTimeoutMeansMissedDeadline : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (S : System), Wf S → ∀ (ze : UInt256) (R : SlRoot)
      (B : RootBacking h ze R), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg), LegRefundableAccepted h z0 hl cv S B F leg →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ HashBreak h ze (B.leaves leg.chain)

/-- The gate as run implies the looser predicate every safety result is stated over,
so `Properties.Refund`'s exclusivity covers the real path. -/
def AcceptedImpliesRefundable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (cv : CommitValue) (S : System) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R),
      Aggregates S R → ∀ (F : Flow) (leg : FlowLeg),
      LegRefundableAccepted h z0 hl cv S B F leg →
        LegRefundable h z0 hl cv S F leg ∨ HashBreak h ze (B.leaves leg.chain)

/-- With node injectivity and the chain tree's domain separation, the escape hatch
is empty — so the disjunctions above collapse. -/
def NoBreakUnderIdealizations : Prop :=
  ∀ (h : Hash) (ze : UInt256) (L : List UInt256),
    (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    EntriesNotEmpty ze L → ¬ HashBreak h ze L

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
