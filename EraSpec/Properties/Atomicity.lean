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

## Three hypotheses, three countermodels

* Drop the all-legs loop and atomicity fails: `SelfOnlyGateAdmitsMixedOutcome`
  exhibits a well-formed two-chain system in which a self-only gate lets one leg
  execute while its sibling is refundable.  `FullGateBlocksMixedOutcome` shows the
  real gate refuses in that same state.  Together they answer the question
  `AttackVectors.FlowAtomicity` leaves open.
* Drop `_checkFlowId` and atomicity fails differently:
  `SubsetFlowPassesUncheckedGate` shows the executing party can present the real
  flow's `flowId` with the uncommitted leg omitted — every remaining proof still
  verifies, because commit values are computed from the *claimed* id — and collect
  a mixed outcome.  `FlowIdCheckPinsLegList` and `SubsetFlowRejectedByCheck` show
  the recomputation excludes exactly that, and
  `ExecutedImpliesRealFlowFinalizable` is the atomicity guarantee restated over
  the real flow rather than the presented one.
* Drop DA and atomicity fails a third way: `WithoutDaCommittedLegIsStuck` exhibits
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
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (F : Flow) (leg : FlowLeg),
    ExecutedVia h z0 hl cv fh S F leg → ∀ other ∈ F.legs, LegFinalized h z0 hl cv S F other

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
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (leg : FlowLeg) (n : ℕ), S.time leg.chain n ≤ F.deadline →
      legValue cv F leg ∈ keys (toAbs (S.tree leg.chain n)) →
      LegFinalizableBy h z0 hl cv S A F leg

/-! ## Partial atomicity -/

/-- **PARTIAL ATOMICITY.**  If any leg of the flow is executed, then every leg of
the flow can be finalized: for each one there is an on-time batch and a proof its
prover can both build and get accepted.

This is the none-or-all property.  The hypotheses are the hash idealizations, a
well-formed system, and data availability — nothing about honest chains or honest
provers. -/
def ExecutedImpliesAllFinalizable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (S : System), Wf S →
    ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (leg : FlowLeg), ExecutedVia h z0 hl cv fh S F leg →
      FlowFinalizableBy h z0 hl cv S A F

/-- **NONE OR ALL.**  For every flow: either every leg is finalizable, or no leg is
executed.  The dichotomy form of partial atomicity — a flow never gets stuck
half-executed. -/
def NoneOrAll : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (S : System), Wf S →
    ∀ (A : Access), DataAvailable h z0 hl S A → ∀ (F : Flow),
      FlowFinalizableBy h z0 hl cv S A F ∨ ∀ leg, ¬ ExecutedVia h z0 hl cv fh S F leg

/-- **FINALIZABILITY DOES NOT DECAY.**  Once a leg of an executed flow is
finalizable, it stays finalizable at every later on-time batch: a destination that
imports a later settlement-layer root can still verify.

The `S.time other.chain m ≤ F.deadline` hypothesis is not decoration — the gate
compares the *batch's* timestamp to the deadline, so past the deadline a prover
must use the root of a batch that settled in time, not the newest one. -/
def ExecutedImpliesFinalityPersists : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (S : System), Wf S →
    ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (leg : FlowLeg), ExecutedVia h z0 hl cv fh S F leg →
    ∀ other ∈ F.legs, ∃ n, S.time other.chain n ≤ F.deadline ∧
      ∀ m, n ≤ m → S.time other.chain m ≤ F.deadline →
        ∃ p, A other.chain m p ∧ Accepts h z0 hl S other.chain m (legValue cv F other) p

/-- **EXECUTION EXCLUDES EVERY REFUND IN THE FLOW.**  If any leg is executed, then
no leg of the flow — not the executed one, not a sibling — can pass the timeout
gate, on either of its two branches.

This is the cross-leg no-double-spend, and it is the second half of atomicity: the
first says all legs *can* finalize, this says none *can* be unwound.  Both timeout
branches need the timestamp reasoning: a late batch comes after every on-time one,
and the last on-time batch comes after every on-time one. -/
def ExecutedExcludesAnyRefund : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (S : System), Wf S →
    ∀ (F : Flow) (leg : FlowLeg), ExecutedVia h z0 hl cv fh S F leg →
    ∀ other ∈ F.legs, ¬ LegRefundable h z0 hl cv S F other

/-! ## The flow-id check: which flow is "the" flow -/

/-- **`_checkFlowId` PINS THE LEG LIST.**  Two flows that both pass the
recomputation and claim the same `flowId` are the same flow.  So "the checked flow
with id `X`" is well defined, and an executing party cannot choose its own leg
list. -/
def FlowIdCheckPinsLegList : Prop :=
  ∀ (fh : FlowHash), FlowHashInj fh → ∀ (F F' : Flow),
    FlowIdChecked fh F → FlowIdChecked fh F' → F.flowId = F'.flowId → F = F'

/-- **WITHOUT `_checkFlowId`, A TRUNCATED FLOW PASSES THE GATE.**  The executing
party presents the real flow's `flowId` with the uncommitted leg omitted.  Commit
values are computed from the claimed id, so the remaining leg's value is exactly
the one that was inserted: every proof in the truncated flow verifies, the
unchecked gate passes, and the omitted leg of the real flow is refundable.

One leg executed, its sibling refunded — the mixed outcome atomicity excludes,
reached without breaking a single hash. -/
def SubsetFlowPassesUncheckedGate : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (id hA hB : UInt256), 0 < cv id hA → 0 < cv id hB →
      Wf (mixedSystem (cv id hA))
        ∧ ExecutedViaUncheckedFlowId h z0 hl cv (mixedSystem (cv id hA))
            (subsetFlow id hA) ⟨0, hA⟩
        ∧ LegRefundable h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨1, hB⟩

/-- **THE CHECK REJECTS IT.**  The truncated flow and the real flow claim the same
id, so under flow-hash injectivity at most one of them can pass the
recomputation — and it is the real one. -/
def SubsetFlowRejectedByCheck : Prop :=
  ∀ (fh : FlowHash), FlowHashInj fh → ∀ (id hA hB : UInt256),
    FlowIdChecked fh (mixedFlow id hA hB) → ¬ FlowIdChecked fh (subsetFlow id hA)

/-- **PARTIAL ATOMICITY OVER THE REAL FLOW.**  If a leg is executed through the
gate as deployed, then every leg of *any* flow that passes the check with the same
id can be finalized.  Since that flow is unique, this is the guarantee about the
flow the legs were actually committed under, rather than about whatever leg list
the executing party presented. -/
def ExecutedImpliesRealFlowFinalizable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash), FlowHashInj fh → ∀ (S : System), Wf S →
    ∀ (A : Access), DataAvailable h z0 hl S A → ∀ (F F' : Flow) (leg : FlowLeg),
      ExecutedVia h z0 hl cv fh S F leg → FlowIdChecked fh F' → F.flowId = F'.flowId →
      FlowFinalizableBy h z0 hl cv S A F'

/-! ## What else is load-bearing -/

/-- **THE ALL-LEGS LOOP IS NECESSARY.**  In a well-formed two-chain system —
chain `0` commits leg `hA` in its first batch, chain `1` never commits leg `hB` — a
gate that checked only the executing leg would let `hA` execute, while `hB` is
refundable through the timeout gate.  One leg delivered, its sibling refunded.

This is the answer to the open question in `AttackVectors.FlowAtomicity`'s header:
same-outcome is forced, and it is forced *here*, by the loop over all legs. -/
def SelfOnlyGateAdmitsMixedOutcome : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (id hA hB : UInt256), 0 < cv id hA → 0 < cv id hB →
      Wf (mixedSystem (cv id hA)) ∧ FlowWf cv (mixedFlow id hA hB)
        ∧ SelfOnlyGate h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩
        ∧ LegRefundable h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨1, hB⟩

/-- **THE REAL GATE REFUSES IN THAT STATE.**  On the same configuration, the
all-legs gate is unsatisfiable: leg `hB` has no accepted inclusion proof at any
on-time batch, so no leg of the flow can execute at all.  Side by side with
`SelfOnlyGateAdmitsMixedOutcome`, this is the precise sense in which
`requireFlowFinalized`'s loop is what buys atomicity. -/
def FullGateBlocksMixedOutcome : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (id hA hB : UInt256), 0 < cv id hA → 0 < cv id hB →
      ¬ FlowFinalized h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB)
        ∧ ∀ leg, ¬ ExecutedVia h z0 hl cv fh (mixedSystem (cv id hA)) (mixedFlow id hA hB) leg

/-- **DATA AVAILABILITY IS NECESSARY.**  Without it a committed leg is stuck: the
finality proof exists mathematically (`LegFinalized`) but no prover can present it
(`¬ LegFinalizableBy`), and the leg cannot be refunded either, because it really is
in the tree and so no absence proof can be accepted on either timeout branch.

So `ExecutedImpliesAllFinalizable` genuinely needs its DA hypothesis, and the
failure mode without it is stranded funds rather than a double spend.  No contract
change can fix this one — it is an assumption about the world. -/
def WithoutDaCommittedLegIsStuck : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (id hA hB : UInt256), 0 < cv id hA →
      Wf (mixedSystem (cv id hA))
        ∧ ¬ DataAvailable h z0 hl (mixedSystem (cv id hA)) noAccess
        ∧ LegFinalized h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩
        ∧ ¬ LegFinalizableBy h z0 hl cv (mixedSystem (cv id hA)) noAccess
              (mixedFlow id hA hB) ⟨0, hA⟩
        ∧ ¬ LegRefundable h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩

end Properties.Atomicity
