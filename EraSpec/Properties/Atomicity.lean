import EraSpec.Contracts.Atomicity

/-!
# Properties: partial atomicity (none-or-all)

Statements about `EraSpec.Contracts.Atomicity`.  Proofs are in
`EraSpec.Proofs.Atomicity`.

## The property, in one line

**If any leg of a flow is executed, then every leg of that flow can be finalized —
provided the source chains' data is available.**  Equivalently: either all legs
are finalizable, or no leg executes.  Never one leg executed and a sibling
stranded.

## Why it holds, and what each ingredient does

The argument is four steps, and each is a property below:

1. **The gate is over all legs** (`GateRequiresEveryLeg`).  Executing any leg
   means `requireFlowFinalized` passed, and that loop demands finality evidence
   for every leg.  This is definitional in the model — it is the fact a reviewer
   should check against the Solidity, not a theorem.
2. **The finality signal means real membership**
   (`FinalitySignalMeansMembership`).  An accepted inclusion proof against a
   batch's root implies the commit value really is a key of that tree.  This is
   the IMT content, and it needs the hash assumptions.
3. **Membership is permanent** (`FinalitySignalPersists`).  The tree is
   append-only across batches, so the signal cannot be revoked.
4. **Membership plus DA yields a presentable proof** (`MemberIsFinalizable`).
   `FullMerkle.merklePath` exists for every occupied leaf and the verifier accepts
   it — but only a prover with the chain's data can produce it, which is exactly
   the DA hypothesis.

Then `ExecutedImpliesAllFinalizable` is 1 → 2 → 3 → 4, and `NoneOrAll` is its
dichotomy form.  `ExecutedExcludesAnyRefund` is the other half of atomicity: not
only can every leg finalize, no leg can be refunded once any leg has executed.

## What makes each hypothesis load-bearing

* Drop the all-legs loop and atomicity fails: `SelfOnlyGateAdmitsMixedOutcome`
  exhibits a well-formed two-chain system in which a self-only gate lets leg `a`
  execute while leg `b` is refundable — one leg delivered, its sibling refunded.
  `FullGateBlocksMixedOutcome` shows the real gate refuses in that same state.
  Together they answer the question `AttackVectors.FlowAtomicity` leaves open.
* Drop DA and atomicity fails differently: `WithoutDaCommittedLegIsStuck` exhibits
  a committed leg that can be neither finalized (no proof is presentable) nor
  refunded (it *is* in the tree, so no absence proof can exist).  Funds stranded.
  Note this is not a contract defect — no contract can conjure unavailable data —
  which is why DA appears as a named assumption rather than a proof obligation.
-/

namespace Properties.Atomicity

open IMTAbstract MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity

/-! ## The four ingredients -/

/-- **THE GATE IS OVER ALL LEGS.**  Executing any leg of a flow implies finality
evidence for *every* leg.  Definitional in the model: it is `requireFlowFinalized`'s
loop, and the thing to check against the source. -/
def GateRequiresEveryLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System) (F : Flow) (leg : FlowLeg),
    ExecutedVia h z0 hl S F leg → ∀ other ∈ F.legs, LegFinalized h z0 hl S F.deadline other

/-- **THE FINALITY SIGNAL MEANS MEMBERSHIP.**  An accepted inclusion proof against
chain `c`'s batch-`n` root implies the value is a key of that tree.  The bridge
from "the verifier said yes" to "the leg is committed". -/
def FinalitySignalMeansMembership : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (S : System) (c : Chain) (n : ℕ) (v : UInt256) (p : ImtProof),
      Accepts h z0 hl S c n v p → v ∈ keys (toAbs (S.tree c n))

/-- **THE FINALITY SIGNAL IS PERMANENT.**  A value committed by batch `n` is
committed at every later batch: the IMT is append-only across batch boundaries, so
no later batch can revoke a leg's commitment. -/
def FinalitySignalPersists : Prop :=
  ∀ (S : System), Wf S → ∀ (c : Chain) (n m : ℕ), n ≤ m →
    keys (toAbs (S.tree c n)) ⊆ keys (toAbs (S.tree c m))

/-- **MEMBERSHIP PLUS DA GIVES A PRESENTABLE, ACCEPTED PROOF.**  For a committed
value at an on-time batch, the honest `merklePath` proof is presentable (DA) and
the verifier accepts it (completeness).  This is the step DA is needed for, and
the only one. -/
def MemberIsFinalizable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System), Wf S →
    ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (D : ℕ) (leg : FlowLeg) (n : ℕ), S.time leg.chain n ≤ D →
      leg.commit ∈ keys (toAbs (S.tree leg.chain n)) →
      LegFinalizableBy h z0 hl S A D leg

/-! ## Partial atomicity -/

/-- **PARTIAL ATOMICITY.**  If any leg of the flow is executed, then every leg of
the flow can be finalized: for each one there is an on-time batch and a proof its
prover can both build and get accepted.

This is the none-or-all property.  The hypotheses are the hash idealizations, a
well-formed system, and data availability — nothing about honest chains or honest
provers. -/
def ExecutedImpliesAllFinalizable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (leg : FlowLeg), ExecutedVia h z0 hl S F leg →
      FlowFinalizableBy h z0 hl S A F

/-- **NONE OR ALL.**  For every flow: either every leg is finalizable, or no leg is
executed.  The dichotomy form of partial atomicity — a flow never gets stuck
half-executed. -/
def NoneOrAll : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A → ∀ (F : Flow),
      FlowFinalizableBy h z0 hl S A F ∨ ∀ leg, ¬ ExecutedVia h z0 hl S F leg

/-- **FINALIZABILITY DOES NOT DECAY.**  Once a leg of an executed flow is
finalizable, it stays finalizable at every later on-time batch: a destination that
imports a later settlement-layer root can still verify.

The `S.time other.chain m ≤ F.deadline` hypothesis is not decoration — the gate
compares the *batch's* timestamp to the deadline, so past the deadline a prover
must use the root of a batch that settled in time, not the newest one. -/
def ExecutedImpliesFinalityPersists : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (S : System), Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (leg : FlowLeg), ExecutedVia h z0 hl S F leg →
    ∀ other ∈ F.legs, ∃ n, S.time other.chain n ≤ F.deadline ∧
      ∀ m, n ≤ m → S.time other.chain m ≤ F.deadline →
        ∃ p, A other.chain m p ∧ Accepts h z0 hl S other.chain m other.commit p

/-- **EXECUTION EXCLUDES EVERY REFUND IN THE FLOW.**  If any leg is executed, then
no leg of the flow — not the executed one, not a sibling — can pass the timeout
gate, on either of its two branches.

This is the cross-leg no-double-spend, and it is the second half of atomicity: the
first says all legs *can* finalize, this says none *can* be unwound.  Both timeout
branches need the timestamp reasoning: a late batch comes after every on-time one,
and the last on-time batch comes after every on-time one. -/
def ExecutedExcludesAnyRefund : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (S : System), Wf S → ∀ (F : Flow) (leg : FlowLeg), ExecutedVia h z0 hl S F leg →
    ∀ other ∈ F.legs, ¬ LegRefundable h z0 hl S F.deadline other

/-! ## What is load-bearing -/

/-- **THE ALL-LEGS LOOP IS NECESSARY.**  In a well-formed two-chain system —
chain `0` commits leg `a` in its first batch, chain `1` never commits leg `b` — a
gate that checked only the executing leg would let `a` execute, while `b` is
refundable through the timeout gate.  One leg delivered, its sibling refunded: the
mixed outcome atomicity is supposed to exclude.

This is the answer to the open question in `AttackVectors.FlowAtomicity`'s header:
same-outcome is forced, and it is forced *here*, by the loop over all legs. -/
def SelfOnlyGateAdmitsMixedOutcome : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (a b : UInt256), 0 < a → 0 < b →
      Wf (mixedSystem a) ∧ FlowWf (mixedFlow a b)
        ∧ SelfOnlyGate h z0 hl (mixedSystem a) (mixedFlow a b) ⟨0, a⟩
        ∧ LegRefundable h z0 hl (mixedSystem a) (mixedFlow a b).deadline ⟨1, b⟩

/-- **THE REAL GATE REFUSES IN THAT STATE.**  On the same configuration, the
all-legs gate is unsatisfiable: leg `b` has no accepted inclusion proof at any
on-time batch, so no leg of the flow can execute at all.  Side by side with
`SelfOnlyGateAdmitsMixedOutcome`, this is the precise sense in which
`requireFlowFinalized`'s loop is what buys atomicity. -/
def FullGateBlocksMixedOutcome : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (a b : UInt256), 0 < a → 0 < b →
      ¬ FlowFinalized h z0 hl (mixedSystem a) (mixedFlow a b)
        ∧ ∀ leg, ¬ ExecutedVia h z0 hl (mixedSystem a) (mixedFlow a b) leg

/-- **DATA AVAILABILITY IS NECESSARY.**  Without it a committed leg is stuck: the
finality proof exists mathematically (`LegFinalized`) but no prover can present it
(`¬ LegFinalizableBy`), and the leg cannot be refunded either, because it really is
in the tree and so no absence proof can be accepted on either timeout branch.

So `ExecutedImpliesAllFinalizable` genuinely needs its DA hypothesis, and the
failure mode without it is stranded funds rather than a double spend.  No contract
change can fix this one — it is an assumption about the world. -/
def WithoutDaCommittedLegIsStuck : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ a : UInt256, 0 < a →
      Wf (mixedSystem a)
        ∧ ¬ DataAvailable h z0 hl (mixedSystem a) noAccess
        ∧ LegFinalized h z0 hl (mixedSystem a) 0 ⟨0, a⟩
        ∧ ¬ LegFinalizableBy h z0 hl (mixedSystem a) noAccess 0 ⟨0, a⟩
        ∧ ¬ LegRefundable h z0 hl (mixedSystem a) 0 ⟨0, a⟩

end Properties.Atomicity
