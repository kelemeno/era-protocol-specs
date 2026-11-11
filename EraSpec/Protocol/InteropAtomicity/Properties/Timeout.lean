import EraSpec.Protocol.InteropAtomicity.Specs.Timeout

/-!
# Properties: the timeout decision is justified

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.Timeout`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.Timeout`.

## What this removes from the safety argument

`Contracts.Atomicity.LegRefundable` carries `IsLastOnTime` as a branch condition
with nothing behind it.  `Properties.IsLastOnTimeDerived` supplies the missing step: from the
three comparisons `verifyTimeoutAbsence` actually makes — the root post-dates the
deadline, the batch settled by the deadline, the batch is last in that root — plus
the settlement layer's `Aggregates`, the "last in-time batch" fact follows.

`Properties.VerifiedImpliesRefundable` carries that over to everything already proved: a
timeout the contract really verifies is an instance of the looser `LegRefundable`
that `Protocol/InteropAtomicity/Properties/Atomicity.lean` and `Protocol/InteropAtomicity/Properties/Refund.lean` are stated over, and those are
stated over the *looser* predicate, which admits more refunds — so excluding them
is the stronger claim.

Be precise about what that buys, because it is easy to overstate.  The safety
results' own statements do not mention `Aggregates`.  But a conclusion about a
**verified** refund goes through `Properties.VerifiedImpliesRefundable`, so it inherits
`Aggregates` — the real-path claim carries that hypothesis, and the only
assumption-free statements are the ones about the looser predicate itself.

## What it adds

`Properties.TimeoutMeansMissedDeadline` is the positive statement, and the one worth reading:
a leg with a verified timeout proof was absent from its own source chain's tree at
**every** batch that settled by the deadline.  The refund is not merely permitted,
it is deserved — the obligation was never committed in time.

## What remains assumed, and why it is the right place for it

`Aggregates` — a batch that had settled when a root was created is inside that
root — is a property of how the settlement layer builds roots, not of the interop
contracts, so it cannot be derived here.  `Properties.StaleRootRefundsDeliveredLeg` is the
countermodel: with a root that omits an already-settled batch, a leg delivered on
time passes the timeout gate.  That is the exchange this file makes — an
unexplained condition inside the refund gate for a named property of the layer
below it, with a countermodel showing the property is load-bearing.
-/

namespace Contracts.Timeout

open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier IMTAbstract

/-! ## The derivation -/

/-- **"LAST BATCH IN THIS ROOT" MEANS "LAST BATCH IN TIME".**  What the END branch
verifies, plus the settlement layer's aggregation guarantee, gives exactly the fact
the refund gate needs — so `IsLastOnTime` stops being an assumption. -/
def Properties.IsLastOnTimeDerived : Prop :=
  ∀ (S : System) (R : SlRoot), Aggregates S R → ∀ (c : Chain) (D N : ℕ),
    EndBranchVerified S R c D N → IsLastOnTime S c D N

/-- **A VERIFIED TIMEOUT IS A REFUNDABLE LEG.**  So every safety result stated over
`LegRefundable` — `Contracts.Atomicity.Properties.ExecutedExcludesAnyRefund` and the
composition in `Protocol/InteropAtomicity/Properties/Refund.lean` — applies to the path the contract actually
takes.  Note the hypothesis: applying them to a verified refund goes through this
lemma, so that conclusion carries `Aggregates` even though their own statements do
not mention it. -/
def Properties.VerifiedImpliesRefundable : Prop :=
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
def Properties.TimeoutMeansMissedDeadline : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (S : System), Wf S → ∀ (R : SlRoot), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg), LegRefundableVerified h z0 hl cv S R F leg →
    ∀ n, S.time leg.chain n ≤ F.deadline →
      legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n))

/-- The same conclusion in the form the finality gate consumes: a leg with a
verified timeout has no on-time batch it could be finalized against. -/
def Properties.TimeoutExcludesFinality : Prop :=
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
def Properties.LastBatchProofIdentifiesLastBatch : Prop :=
  ∀ (h : Hash) (ze : UInt256), (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (R : SlRoot) (B : RootBacking h ze R) (c : Chain) (N : ℕ) (sibs : ℕ → UInt256)
      (x : UInt256), LastBatchAccepted B c N sibs x →
      N = R.upTo c ∨ HashBreak h ze (B.leaves c)

/-- So the END branch as the contract runs it implies the END branch as the safety
argument assumed it. -/
def Properties.EndBranchAcceptedImpliesVerified : Prop :=
  ∀ (h : Hash) (ze : UInt256), (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (R : SlRoot) (B : RootBacking h ze R) (S : System) (c : Chain) (D N : ℕ)
      (sibs : ℕ → UInt256) (x : UInt256), EndBranchAccepted B S c D N sibs x →
      EndBranchVerified S R c D N ∨ HashBreak h ze (B.leaves c)

/-- **THE COMPLETE CHAIN.**  Accepted proof → last included batch → no later in-time
batch → the obligation was absent at every batch that settled in time.

Every link is now a theorem.  What is left on the far side is `Aggregates`, which is
a property of the settlement layer, and the `HashBreak` escape, which
`Properties.NoBreakUnderIdealizations` closes for anyone willing to assume keccak behaves. -/
def Properties.AcceptedTimeoutMeansMissedDeadline : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (S : System), Wf S → ∀ (ze : UInt256) (R : SlRoot)
      (B : RootBacking h ze R), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg), LegRefundableAccepted h z0 hl cv S B F leg →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ HashBreak h ze (B.leaves leg.chain)

/-- The gate as run implies the looser predicate every safety result is stated over,
so `Protocol/InteropAtomicity/Properties/Refund.lean`'s exclusivity covers the real path (but those
exclusivity results still take the unsatisfiable `HashAssumptions`). -/
def Properties.AcceptedImpliesRefundable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    ∀ (cv : CommitValue) (S : System) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R),
      Aggregates S R → ∀ (F : Flow) (leg : FlowLeg),
      LegRefundableAccepted h z0 hl cv S B F leg →
        LegRefundable h z0 hl cv S F leg ∨ HashBreak h ze (B.leaves leg.chain)

/-- With node injectivity and the chain tree's domain separation, the escape hatch
is empty — so the disjunctions above collapse. -/
def Properties.NoBreakUnderIdealizations : Prop :=
  ∀ (h : Hash) (ze : UInt256) (L : List UInt256),
    (∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) →
    EntriesNotEmpty ze L → ¬ HashBreak h ze L

/-! ## The last-batch chain, pinned

`LastBatchProofIdentifiesLastBatch`, `EndBranchAcceptedImpliesVerified`,
`AcceptedImpliesRefundable` and `NoBreakUnderIdealizations` above all take global
pair-injectivity, which no `UInt256` hash meets, and their `HashBreak` escape is
always inhabited.  The versions below take no hash premise and replace the escape by
a collision located on the submitted proof: a `PinnedBreak` on the chain tree's
subtree right after batch `N`, or a `PathCollision` at a named level of the
batch-leaf path `(sibs, x)`.  The `…On` versions collapse the escape under a
bounded premise: injectivity only on the finite set of pairs this chain tree and
this verification hash. -/

/-- Naming the gate's witnesses loses nothing. -/
def Properties.LegRefundableAcceptedIffBy : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R) (F : Flow) (leg : FlowLeg),
    LegRefundableAccepted h z0 hl cv S B F leg
      ↔ ∃ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
          LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x

/-- **AN ACCEPTED LAST-BATCH PROOF IDENTIFIES THE LAST BATCH, OR PINS A COLLISION.**
No hash premise. -/
def Properties.LastBatchProofIdentifiesLastBatchPinned : Prop :=
  ∀ (h : Hash) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (c : Chain) (N : ℕ)
    (sibs : ℕ → UInt256) (x : UInt256), LastBatchAccepted B c N sibs x →
      N = R.upTo c ∨ PinnedBreak h ze (B.leaves c) N
        ∨ PathCollision h ze (B.leaves c) sibs 0 (B.height c) N x

/-- **THE PINNED DISJUNCTS ARE NOT A TAUTOLOGY.**  An authenticated in-range batch
path (honest, under the colliding `demoHash`) for a batch that is NOT the last, with
neither a `PinnedBreak` nor a `PathCollision`: only `zeroRightSiblings` fails. -/
def Properties.LastBatchPinnedConclusionNotAlways : Prop :=
  ∃ (h : Hash) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (c : Chain) (N : ℕ)
    (sibs : ℕ → UInt256) (x : UInt256),
      N < (B.leaves c).length
      ∧ walkPure h sibs 0 (B.height c) N x = rootOf h ze (B.leaves c) (B.height c)
      ∧ ¬ (N = R.upTo c ∨ PinnedBreak h ze (B.leaves c) N
            ∨ PathCollision h ze (B.leaves c) sibs 0 (B.height c) N x)

/-- **UNDER A BOUNDED PREMISE, THE ACCEPTED PROOF IS THE LAST BATCH.**  Injectivity
only on this chain tree's pairs, its zero cascade, and the pairs this verification
hashed; domain separation only for this chain tree's leaves. -/
def Properties.LastBatchProofIdentifiesLastBatchOn : Prop :=
  ∀ (h : Hash) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (c : Chain) (N : ℕ)
    (sibs : ℕ → UInt256) (x : UInt256),
      EntriesNotEmpty ze (B.leaves c) →
      PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
        ∨ VerifiedPair h sibs (B.height c) N x p) →
      LastBatchAccepted B c N sibs x → N = R.upTo c

/-- The END branch as run implies the END branch as assumed, or pins a collision. -/
def Properties.EndBranchAcceptedImpliesVerifiedPinned : Prop :=
  ∀ (h : Hash) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (S : System) (c : Chain)
    (D N : ℕ) (sibs : ℕ → UInt256) (x : UInt256), EndBranchAccepted B S c D N sibs x →
      EndBranchVerified S R c D N ∨ PinnedBreak h ze (B.leaves c) N
        ∨ PathCollision h ze (B.leaves c) sibs 0 (B.height c) N x

/-- The same, collapsed under the bounded premise. -/
def Properties.EndBranchAcceptedImpliesVerifiedOn : Prop :=
  ∀ (h : Hash) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (S : System) (c : Chain)
    (D N : ℕ) (sibs : ℕ → UInt256) (x : UInt256),
      EntriesNotEmpty ze (B.leaves c) →
      PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
        ∨ VerifiedPair h sibs (B.height c) N x p) →
      EndBranchAccepted B S c D N sibs x → EndBranchVerified S R c D N

/-- **ITS PREMISES ARE SATISFIABLE, WITH THE ZERO CHECK EXERCISED.**  `demoBacking`,
batch 1 on time for deadline 0, the honest batch-leaf path, and the bounded
premises under the colliding `demoHash`. -/
def Properties.EndBranchAcceptedOnSatisfiable : Prop :=
  ∃ (h : Hash) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (S : System) (c : Chain)
    (D N : ℕ) (sibs : ℕ → UInt256) (x : UInt256),
      EndBranchAccepted B S c D N sibs x
      ∧ EntriesNotEmpty ze (B.leaves c)
      ∧ PairInjOn h (fun p => TreePair h ze (B.leaves c) (B.height c) p
          ∨ VerifiedPair h sibs (B.height c) N x p)
      ∧ (∃ l < B.height c, (N / 2 ^ l) % 2 = 0)
      ∧ (∃ a b c d : UInt256, (a, b) ≠ (c, d) ∧ h a b = h c d)

/-- **THE GATE AS RUN IMPLIES THE LOOSER PREDICATE, OR PINS A COLLISION ON THE
SUBMITTED PROOF.**  `AcceptedImpliesRefundable` without its global-injectivity
premise; the escape names the submitted batch `N` and batch-leaf path `(sibs, x)`. -/
def Properties.AcceptedImpliesRefundablePinned : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
        LegRefundable h z0 hl cv S F leg ∨ PinnedBreak h ze (B.leaves leg.chain) N
          ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x

/-- The same, collapsed under the bounded premise on the submitted proof.  The `Refund`
exclusivity results this feeds still take `HashAssumptions`, so they do not yet inherit
this bounded form. -/
def Properties.AcceptedImpliesRefundableOn : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R), Aggregates S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      EntriesNotEmpty ze (B.leaves leg.chain) →
      PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
        ∨ VerifiedPair h sibs (B.height leg.chain) N x q) →
      LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
        LegRefundable h z0 hl cv S F leg

/-- **ITS PREMISES ARE SATISFIABLE, ON THE END BRANCH.**  `demoSystem` with
`demoRoot`/`demoBacking` (`Aggregates` holds), a leg with commit value 1 and
deadline 0, an IMT absence proof against `setup`, and the honest batch-leaf path for
batch 1, with the bounded premises under the colliding `demoHash`. -/
def Properties.AcceptedImpliesRefundableOnSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R) (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof)
    (sibs : ℕ → UInt256) (x : UInt256),
      Aggregates S R
      ∧ EntriesNotEmpty ze (B.leaves leg.chain)
      ∧ PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
          ∨ VerifiedPair h sibs (B.height leg.chain) N x q)
      ∧ EndBranchAccepted B S leg.chain F.deadline N sibs x
      ∧ LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x

/-- **`NoBreakUnderIdealizations`, BOUNDED.**  On a chain tree, injectivity on its own
pairs and zero cascade, and domain separation for its own leaves, exclude a
`PinnedBreak` after any batch.  Premises satisfiable: `EndBranchAcceptedOnSatisfiable`
supplies them (its pair set contains `TreePair`). -/
def Properties.NoPinnedBreakUnderBoundedInjectivity : Prop :=
  ∀ (h : Hash) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (c : Chain) (N : ℕ),
    EntriesNotEmpty ze (B.leaves c) →
    PairInjOn h (TreePair h ze (B.leaves c) (B.height c)) →
    ¬ PinnedBreak h ze (B.leaves c) N

/-! ## What is load-bearing -/

/-- **A STALE ROOT REFUNDS A DELIVERED LEG.**  One chain, two batches, both settled
at time `0` and so both on time for deadline `0`; the commit value enters during the
second.  A root created after the deadline that nevertheless stops at the first
batch makes the END branch verify — the batch really is on time, and really is the
last one *in that root* — while the leg was committed in time.

`Aggregates` is exactly what excludes this, which is why it is a hypothesis of
everything above rather than a remark. -/
def Properties.StaleRootRefundsDeliveredLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∀ (cv : CommitValue) (F : Flow) (leg : FlowLeg), F.deadline = 0 →
      0 < legValue cv F leg →
      Wf (staleSystem (legValue cv F leg))
        ∧ ¬ Aggregates (staleSystem (legValue cv F leg)) staleRoot
        ∧ (staleSystem (legValue cv F leg)).time leg.chain 1 ≤ F.deadline
        ∧ legValue cv F leg
            ∈ keys (toAbs ((staleSystem (legValue cv F leg)).tree leg.chain 1))
        ∧ LegRefundableVerified h z0 hl cv (staleSystem (legValue cv F leg)) staleRoot F leg

end Contracts.Timeout
