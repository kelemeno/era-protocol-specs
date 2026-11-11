import EraSpec.Protocol.InteropAtomicity.Specs.Atomicity

/-!
# Properties: partial atomicity (none-or-all)

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.Atomicity`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.Atomicity`.

## The property, in one line

**If any leg of a flow is executed, then every leg of that flow has an IMT proof a
prover can present and the verifier accepts against the true root — provided the
source chains' data is available.**  Equivalently: either all legs are finalizable in
that sense (`FlowFinalizableBy`), or no leg executes.

That is the source-side half of finalizability.  A destination must also hold an
imported settlement-layer root covering the batch, and nothing here assumes that it
does.  Without that premise, one leg can execute on its destination while a sibling's
destination cannot pass its gate and no leg can be refunded
(`Contracts.RootImport.Properties.WithoutImportFlowSitsHalfExecuted`).  The destination
form, with import availability as a named premise, is `Contracts.RootImport`
(`NoneOrAllAtOrBreak`, `NoneOrAllAtOrBreakPinned`).

## Why it holds, and what each ingredient does

The argument is four steps, and each is a property below:

1. **The gate is over all legs** (`Properties.GateRequiresEveryLeg`).  Executing any leg
   means `requireFlowFinalized` passed, and that loop demands finality evidence
   for every leg.  This is definitional in the model — it is the fact a reviewer
   should check against the Solidity, not a theorem.
2. **The finality signal means real membership**
   (`Properties.FinalitySignalMeansMembership`).  An accepted inclusion proof against a
   batch's root implies the commit value really is a key of that tree.  This is
   the IMT content, and it needs the hash assumptions.
3. **Membership is permanent** (`Properties.FinalitySignalPersists`).  The tree is
   append-only across batches, so the signal cannot be revoked.
4. **Membership plus DA yields a presentable IMT proof** (`Properties.MemberIsFinalizable`).
   `FullMerkle.merklePath` exists for every occupied leaf and the verifier accepts
   it — but only a prover with the chain's data can produce it, which is exactly
   the DA hypothesis.  The destination's settlement proof and imported root are
   `Contracts.RootImport.Properties.MemberIsFinalizableAt`.

Then `Properties.ExecutedImpliesAllFinalizable` is 1 → 2 → 3 → 4, and `Properties.NoneOrAll` is its
dichotomy form.  `Properties.ExecutedExcludesAnyRefund` is the other half of atomicity: not
only can every leg finalize, no leg can be refunded once any leg has executed.

## Three hypotheses, three countermodels

* Drop the all-legs loop and atomicity fails: `Properties.SelfOnlyGateAdmitsMixedOutcome`
  exhibits a well-formed two-chain system in which a self-only gate lets one leg
  execute while its sibling is refundable.  `Properties.FullGateBlocksMixedOutcome` shows the
  real gate refuses in that same state.  Together they answer the question
  `AttackVectors.FlowAtomicity` leaves open.
* Drop `_checkFlowId` and atomicity fails differently:
  `Properties.SubsetFlowPassesUncheckedGate` shows the executing party can present the real
  flow's `flowId` with the uncommitted leg omitted — every remaining proof still
  verifies, because commit values are computed from the *claimed* id — and collect
  a mixed outcome.  `Properties.FlowIdCheckPinsLegList` and `Properties.SubsetFlowRejectedByCheck` show
  the recomputation excludes exactly that, and
  `Properties.ExecutedImpliesRealFlowFinalizable` is the atomicity guarantee restated over
  the real flow rather than the presented one.
* Drop DA and atomicity fails a third way: `Properties.WithoutDaCommittedLegIsStuck` exhibits
  a committed leg that can be neither finalized (no proof is presentable) nor
  refunded (it *is* in the tree, so no absence proof can exist).  Funds stranded.
  Note this is not a contract defect — no contract can conjure unavailable data —
  which is why DA appears as a named assumption rather than a proof obligation.

A fourth premise lives in `Contracts.RootImport`: the destination's import of a
settlement-layer root covering the batch.  Without it the flow can sit half-executed
(`Contracts.RootImport.Properties.WithoutImportFlowSitsHalfExecuted`).  Like DA, it is
an assumption about the world, not a contract defect.
-/

namespace Contracts.Atomicity

open IMTAbstract MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity

/-! ## The four ingredients -/

/-- **THE GATE IS OVER ALL LEGS.**  Executing any leg of a flow implies finality
evidence for *every* leg.  Definitional in the model: it is `requireFlowFinalized`'s
loop, and the thing to check against the source. -/
def Properties.GateRequiresEveryLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (F : Flow) (leg : FlowLeg),
    ExecutedVia h z0 hl cv fh S F leg → ∀ other ∈ F.legs, LegFinalized h z0 hl cv S F other

/-- **THE FINALITY SIGNAL MEANS MEMBERSHIP.**  An accepted inclusion proof against
chain `c`'s batch-`n` root implies the value is a key of that tree.  The bridge
from "the verifier said yes" to "the leg is committed". -/
def Properties.FinalitySignalMeansMembership : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (S : System) (c : Chain) (n : ℕ) (v : UInt256) (p : ImtProof),
      Accepts h z0 hl S c n v p → v ∈ keys (toAbs (S.tree c n))

/-- **THE FINALITY SIGNAL IS PERMANENT.**  A value committed by batch `n` is
committed at every later batch: the IMT is append-only across batch boundaries, so
no later batch can revoke a leg's commitment. -/
def Properties.FinalitySignalPersists : Prop :=
  ∀ (S : System), Wf S → ∀ (c : Chain) (n m : ℕ), n ≤ m →
    keys (toAbs (S.tree c n)) ⊆ keys (toAbs (S.tree c m))

/-- **MEMBERSHIP PLUS DA GIVES A PRESENTABLE, ACCEPTED IMT PROOF.**  For a committed
value at an on-time batch, the honest `merklePath` proof is presentable (DA) and
the verifier accepts it against the batch's true END root (completeness).  This is
the step source DA is needed for, and the only one.

The conclusion `LegFinalizableBy` is the IMT half only.  A destination also needs an
imported settlement-layer root that covers the batch, and a presentable multi-hop
settlement proof to it, and source DA supplies neither.  With those two premises the
conclusion becomes finalizability on that destination:
`Contracts.RootImport.Properties.MemberIsFinalizableAt`. -/
def Properties.MemberIsFinalizable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (leg : FlowLeg) (n : ℕ), S.time leg.chain n ≤ F.deadline →
      legValue cv F leg ∈ keys (toAbs (S.tree leg.chain n)) →
      LegFinalizableBy h z0 hl cv S A F leg

/-! ## Partial atomicity -/

/-- **PARTIAL ATOMICITY, IMT HALF.**  If any leg of the flow is executed, then every
leg of the flow has a presentable IMT proof: for each one there is an on-time batch
and an IMT proof its prover can both build and get accepted against the true root.

This is the none-or-all property for the IMT half.  The hypotheses are the hash
idealizations, a well-formed system, and data availability — nothing about honest
chains or honest provers.  It does not say that every leg's destination can pass its
gate.  That also needs the destination's imported settlement-layer root
(`Contracts.RootImport.Properties.ExecutedAtImpliesAllFinalizableAtOrBreak`). -/
def Properties.ExecutedImpliesAllFinalizable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (S : System), Wf S →
    ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (leg : FlowLeg), ExecutedVia h z0 hl cv fh S F leg →
      FlowFinalizableBy h z0 hl cv S A F

/-- **NONE OR ALL.**  For every flow: either every leg is finalizable in the IMT sense
(`FlowFinalizableBy`), or no leg is executed.  The dichotomy form of partial atomicity.
It does not exclude a flow stuck half-executed on a destination that has not imported a
covering settlement-layer root
(`Contracts.RootImport.Properties.WithoutImportFlowSitsHalfExecuted`).  The destination
form is `Contracts.RootImport.Properties.NoneOrAllAtOrBreak`. -/
def Properties.NoneOrAll : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (S : System), Wf S →
    ∀ (A : Access), DataAvailable h z0 hl S A → ∀ (F : Flow),
      FlowFinalizableBy h z0 hl cv S A F ∨ ∀ leg, ¬ ExecutedVia h z0 hl cv fh S F leg

/-- **FINALIZABILITY DOES NOT DECAY.**  Once a leg of an executed flow is
finalizable, it stays finalizable at every later on-time batch: an IMT proof against
that batch's END root is presentable and accepted.  Whether a destination can use it
depends on the destination having imported a settlement-layer root covering that
batch, which is not modelled here.  The destination form, for a destination that
imports a later root, is
`Contracts.RootImport.Properties.ExecutedImpliesFinalityPersistsAtOrBreak`.

The `S.time other.chain m ≤ F.deadline` hypothesis is not decoration — the gate
compares the *batch's* timestamp to the deadline, so past the deadline a prover
must use the root of a batch that settled in time, not the newest one. -/
def Properties.ExecutedImpliesFinalityPersists : Prop :=
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
def Properties.ExecutedExcludesAnyRefund : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (S : System), Wf S →
    ∀ (F : Flow) (leg : FlowLeg), ExecutedVia h z0 hl cv fh S F leg →
    ∀ other ∈ F.legs, ¬ LegRefundable h z0 hl cv S F other

/-! ## The flow-id check: which flow is "the" flow -/

/-- **`_checkFlowId` PINS THE LEG LIST.**  Two flows that both pass the
recomputation and claim the same `flowId` are the same flow.  So "the checked flow
with id `X`" is well defined, and an executing party cannot choose its own leg
list. -/
def Properties.FlowIdCheckPinsLegList : Prop :=
  ∀ (fh : FlowHash), FlowHashInj fh → ∀ (F F' : Flow),
    FlowIdChecked fh F → FlowIdChecked fh F' → F.flowId = F'.flowId → F = F'

/-- **WITHOUT `_checkFlowId`, A TRUNCATED FLOW PASSES THE GATE.**  The executing
party presents the real flow's `flowId` with the uncommitted leg omitted.  Commit
values are computed from the claimed id, so the remaining leg's value is exactly
the one that was inserted: every proof in the truncated flow verifies, the
unchecked gate passes, and the omitted leg of the real flow is refundable.

One leg executed, its sibling refunded — the mixed outcome atomicity excludes,
reached without breaking a single hash. -/
def Properties.SubsetFlowPassesUncheckedGate : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∀ (cv : CommitValue) (id hA hB : UInt256), 0 < cv id hA → 0 < cv id hB →
      Wf (mixedSystem (cv id hA))
        ∧ ExecutedViaUncheckedFlowId h z0 hl cv (mixedSystem (cv id hA))
            (subsetFlow id hA) ⟨0, hA⟩
        ∧ LegRefundable h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨1, hB⟩

/-- **THE CHECK REJECTS IT.**  The truncated flow and the real flow claim the same
id, so under flow-hash injectivity at most one of them can pass the
recomputation — and it is the real one. -/
def Properties.SubsetFlowRejectedByCheck : Prop :=
  ∀ (fh : FlowHash), FlowHashInj fh → ∀ (id hA hB : UInt256),
    FlowIdChecked fh (mixedFlow id hA hB) → ¬ FlowIdChecked fh (subsetFlow id hA)

/-- **PARTIAL ATOMICITY OVER THE REAL FLOW.**  If a leg is executed through the
gate as deployed, then every leg of *any* flow that passes the check with the same
id can be finalized.  Since that flow is unique, this is the guarantee about the
flow the legs were actually committed under, rather than about whatever leg list
the executing party presented. -/
def Properties.ExecutedImpliesRealFlowFinalizable : Prop :=
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
def Properties.SelfOnlyGateAdmitsMixedOutcome : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∀ (cv : CommitValue) (id hA hB : UInt256), 0 < cv id hA → 0 < cv id hB →
      Wf (mixedSystem (cv id hA)) ∧ FlowWf cv (mixedFlow id hA hB)
        ∧ SelfOnlyGate h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩
        ∧ LegRefundable h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨1, hB⟩

/-- **THE REAL GATE REFUSES IN THAT STATE.**  On the same configuration, the
all-legs gate is unsatisfiable: leg `hB` has no accepted inclusion proof at any
on-time batch, so no leg of the flow can execute at all.  Side by side with
`Properties.SelfOnlyGateAdmitsMixedOutcome`, this is the precise sense in which
`requireFlowFinalized`'s loop is what buys atomicity. -/
def Properties.FullGateBlocksMixedOutcome : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (fh : FlowHash) (id hA hB : UInt256), 0 < cv id hA → 0 < cv id hB →
      ¬ FlowFinalized h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB)
        ∧ ∀ leg, ¬ ExecutedVia h z0 hl cv fh (mixedSystem (cv id hA)) (mixedFlow id hA hB) leg

/-- **DATA AVAILABILITY IS NECESSARY.**  Without it a committed leg is stuck: the
finality proof exists mathematically (`LegFinalized`) but no prover can present it
(`¬ LegFinalizableBy`), and the leg cannot be refunded either, because it really is
in the tree and so no absence proof can be accepted on either timeout branch.

So `Properties.ExecutedImpliesAllFinalizable` genuinely needs its DA hypothesis, and the
failure mode without it is stranded funds rather than a double spend.  No contract
change can fix this one — it is an assumption about the world. -/
def Properties.WithoutDaCommittedLegIsStuck : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (cv : CommitValue) (id hA hB : UInt256), 0 < cv id hA →
      Wf (mixedSystem (cv id hA))
        ∧ ¬ DataAvailable h z0 hl (mixedSystem (cv id hA)) noAccess
        ∧ LegFinalized h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩
        ∧ ¬ LegFinalizableBy h z0 hl cv (mixedSystem (cv id hA)) noAccess
              (mixedFlow id hA hB) ⟨0, hA⟩
        ∧ ¬ LegRefundable h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩


/-! ## `FlowHashInj` is unsatisfiable

Added during the consolidation.  `FlowHashInj` asks `fh : List FlowLeg → ℕ → UInt256`
to be injective; the deadline argument alone ranges over all of `ℕ`, so no such
`fh` exists, and every property here taking `FlowHashInj` is vacuously true.  The
collision form is `Contracts.Refund.Properties.CrossFlowRefundYieldsCollision`. -/
def Properties.FlowHashInjUnsatisfiable : Prop := ∀ fh : FlowHash, ¬ FlowHashInj fh

/-! ## The flow-id check, repaired: pinned and bounded forms

Added with the collision-form repair.  `Properties.FlowIdCheckPinsLegList` and
`Properties.SubsetFlowRejectedByCheck` take `FlowHashInj`, which cannot hold.  Their
replacements come in two shapes:

* **pinned** — the conclusion holds or `fh` collides on exactly the two flows'
  own `(legs, deadline)` preimages (`FlowIdClash`);
* **bounded** — the premise is injectivity on an explicit finite list of flows
  (`FlowHashInjOn`), which is satisfiable.

A reviewer should read the pinned forms here for what they are: given that both flows
pass `_checkFlowId` and claim one id, `F ≠ F'` and `FlowIdClash fh F F'` are
equivalent by unfolding.  So these two carry no protocol reasoning; they are the
honest statement that `_checkFlowId` reduces flow identity to a collision on these
two specific preimages.  The pinned form with protocol content is
`Contracts.Refund.Properties.RefundImpliesOwnFlowTimeoutOrCollision`. -/

/-- **`_checkFlowId` PINS THE LEG LIST, OR `fh` COLLIDES ON THESE TWO FLOWS.**  Two
checked flows claiming one id are the same flow, or their own preimages collide. -/
def Properties.FlowIdCheckPinsLegListOrCollision : Prop :=
  ∀ (fh : FlowHash) (F F' : Flow),
    FlowIdChecked fh F → FlowIdChecked fh F' → F.flowId = F'.flowId →
      F = F' ∨ FlowIdClash fh F F'

/-- **`_checkFlowId` PINS THE LEG LIST, BOUNDED.**  If `fh` has no collision among the
flows of a finite list `Fs`, two checked flows of `Fs` claiming one id are equal. -/
def Properties.FlowIdCheckPinsLegListOn : Prop :=
  ∀ (fh : FlowHash) (Fs : List Flow), FlowHashInjOn fh Fs →
    ∀ F ∈ Fs, ∀ F' ∈ Fs,
      FlowIdChecked fh F → FlowIdChecked fh F' → F.flowId = F'.flowId → F = F'

/-- **THE BOUNDED PREMISE IS SATISFIABLE.**  For every list of fewer than `2^256`
flows there is a flow hash with no collision among them. -/
def Properties.FlowHashInjOnSatisfiable : Prop :=
  ∀ Fs : List Flow, Fs.length < UInt256.size → ∃ fh : FlowHash, FlowHashInjOn fh Fs

/-- **THE PINNED DISJUNCT IS NOT A TAUTOLOGY.**  For every flow `F`, the flow hash
`honestFlowHash F` passes `F`'s check and has no `FlowIdClash` between `F` and any
flow at all. -/
def Properties.HonestFlowHashNoClash : Prop :=
  ∀ F : Flow, FlowIdChecked (honestFlowHash F) F ∧ ∀ F' : Flow, ¬ FlowIdClash (honestFlowHash F) F F'

/-- **THE TRUNCATED FLOW PASSES THE CHECK ONLY BY A COLLISION ON THESE TWO
PREIMAGES.**  If the real flow and the truncated one both pass `_checkFlowId`, then `fh`
collides on exactly `([⟨0, hA⟩, ⟨1, hB⟩], 0)` and `([⟨0, hA⟩], 0)`.  The pinned form of
`Properties.SubsetFlowRejectedByCheck`. -/
def Properties.SubsetFlowCheckedOnlyByCollision : Prop :=
  ∀ (fh : FlowHash) (id hA hB : UInt256),
    FlowIdChecked fh (mixedFlow id hA hB) → FlowIdChecked fh (subsetFlow id hA) →
      FlowIdClash fh (mixedFlow id hA hB) (subsetFlow id hA)

/-- **THE CHECK REJECTS IT, BOUNDED.**  If `fh` separates just the real and truncated
flows' preimages, the truncated flow fails `_checkFlowId` whenever the real one
passes.  The bounded form of `Properties.SubsetFlowRejectedByCheck`. -/
def Properties.SubsetFlowRejectedByCheckOn : Prop :=
  ∀ (fh : FlowHash) (id hA hB : UInt256),
    FlowHashInjOn fh [mixedFlow id hA hB, subsetFlow id hA] →
    FlowIdChecked fh (mixedFlow id hA hB) → ¬ FlowIdChecked fh (subsetFlow id hA)

/-- **ITS PREMISES ARE SATISFIABLE.**  For every `id hA hB`, the honest flow hash of
the real flow separates the two preimages and passes the real flow's check. -/
def Properties.SubsetFlowRejectedByCheckOnSatisfiable : Prop :=
  ∀ (id hA hB : UInt256),
    FlowHashInjOn (honestFlowHash (mixedFlow id hA hB)) [mixedFlow id hA hB, subsetFlow id hA]
      ∧ FlowIdChecked (honestFlowHash (mixedFlow id hA hB)) (mixedFlow id hA hB)

/-! ## The headlines without hash premises: the property, or a located break

`Properties.FinalitySignalMeansMembership`, `ExecutedImpliesAllFinalizable`, `NoneOrAll`,
`ExecutedImpliesFinalityPersists`, `ExecutedExcludesAnyRefund` and
`FullGateBlocksMixedOutcome` take `HashAssumptions`, which cannot hold.  Each is
restated below with no hash premise, over the NAMED evidence (`ExecutedViaBy`,
`LegRefundableBy`), concluding the original property or a `TreeRootBreak` located on
a specific submitted proof: the inclusion proof `ev other` submitted for a named leg
(`InclusionBreak`), or the absence proof `q` at batch `N` on the root its branch selects
(`AbsenceBreak`).  The only call to the hash side is the matching `…OrBreak` lemma of
`Contracts.InteropCommitmentTree` (`TreeRoot`).

Anti-vacuity: `Properties.ExecutedOrBreakSatisfiable` exhibits all the premises at
once (a well-formed system, data availability, an executed flow with its evidence)
with every break false and the original conclusions true, and
`Properties.PaddingRefundOfExecutedLegLocatesAbsenceBreak` exhibits the premises with a
refund proof accepted, where the theorem's break is the absence proof's `paddingHit`
and not the honest inclusion proof. -/

/-- **NAMING THE GATE'S EVIDENCE LOSES NOTHING.** -/
def Properties.ExecutedViaIffBy : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (F : Flow) (leg : FlowLeg),
    ExecutedVia h z0 hl cv fh S F leg ↔ ∃ ev : GateEvidence, ExecutedViaBy h z0 hl cv fh S F ev leg

/-- **NAMING THE REFUND PROOF LOSES NOTHING.** -/
def Properties.LegRefundableIffBy : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (F : Flow)
    (leg : FlowLeg),
    LegRefundable h z0 hl cv S F leg ↔ ∃ (N : ℕ) (p : ImtProof), LegRefundableBy h z0 hl cv S F leg N p

/-- **THE FINALITY SIGNAL MEANS MEMBERSHIP, OR THE PROOF CARRIES A BREAK.** -/
def Properties.FinalitySignalMeansMembershipOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System) (c : Chain) (n : ℕ) (v : UInt256)
    (p : ImtProof),
    Accepts h z0 hl S c n v p → v ∈ keys (toAbs (S.tree c n)) ∨ InclusionBreak h z0 hl S c n p

/-- **PARTIAL ATOMICITY, OR A LOCATED BREAK, PER LEG.**  If a leg executed on the
evidence `ev`, then every leg `other` of the flow is finalizable by a presentable
proof, or the inclusion proof `ev other` submitted for that very leg carries a
`TreeRootBreak` against `other`'s chain at the submitted batch.  Finalizable here is
`LegFinalizableBy`, the IMT half.  On a destination with import availability, see
`Contracts.RootImport.Properties.ExecutedImpliesAllFinalizableAtOrBreak`. -/
def Properties.ExecutedImpliesAllFinalizableOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs,
      LegFinalizableBy h z0 hl cv S A F other
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2

/-- **NONE OR ALL, OR A LOCATED BREAK.**  For every flow and every evidence `ev`
presented to the gate: every leg is finalizable, or `ev` executes no leg, or the
inclusion proof `ev` submits for one of the flow's own legs carries a break.
`Properties.NoneOrAllOrBreakPinned` names that leg: the first stranded one.
Finalizable here is `FlowFinalizableBy`, the IMT half.  The destination form is
`Contracts.RootImport.Properties.NoneOrAllAtOrBreak`. -/
def Properties.NoneOrAllOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A → ∀ (F : Flow) (ev : GateEvidence),
      FlowFinalizableBy h z0 hl cv S A F
        ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh S F ev leg)
        ∨ GateBreak h z0 hl S F ev

/-- **FINALIZABILITY DOES NOT DECAY, OR A LOCATED BREAK.** -/
def Properties.ExecutedImpliesFinalityPersistsOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs,
      (∃ n, S.time other.chain n ≤ F.deadline ∧
        ∀ m, n ≤ m → S.time other.chain m ≤ F.deadline →
          ∃ p, A other.chain m p ∧ Accepts h z0 hl S other.chain m (legValue cv F other) p)
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2

/-- **EXECUTION EXCLUDES EVERY REFUND IN THE FLOW, OR A LOCATED BREAK.**  If a leg
executed on the evidence `ev`, then for every leg `other` of the flow and every
submitted timeout evidence `(N, q)` for it: `(N, q)` does not pass the timeout gate,
or the inclusion proof `ev other` carries a break, or the absence proof `q` carries a
break on the batch-`N` root its branch selects. -/
def Properties.ExecutedExcludesAnyRefundOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs, ∀ (N : ℕ) (q : ImtProof),
      ¬ LegRefundableBy h z0 hl cv S F other N q
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2
        ∨ AbsenceBreak h z0 hl S F.deadline other.chain N q

/-- **THE REAL GATE REFUSES THE MIXED STATE, OR A LOCATED BREAK.**  On the mixed
configuration, no evidence passes the all-legs gate unless the inclusion proof it
submits for the never-committed leg `hB` carries a break against chain `1`. -/
def Properties.FullGateBlocksMixedOutcomeOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (id hA hB : UInt256),
    0 < cv id hB → ∀ ev : GateEvidence,
      ¬ FlowFinalizedBy h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ev
        ∨ InclusionBreak h z0 hl (mixedSystem (cv id hA)) 1 (ev ⟨1, hB⟩).1 (ev ⟨1, hB⟩).2

/-! ### Anti-vacuity -/

/-- **THE PREMISES ARE SATISFIABLE, THE BREAKS ARE NOT TAUTOLOGIES.**  For every node
hash, leaf hash and padding constant: the one-leg flow `subsetFlow 0 1` in
`mixedSystem 1`, checked by its honest flow hash, executes on honest evidence, with
full data availability; the evidence has no `GateBreak`, the submitted timeout
evidence (batch 0, the honest proof) has no `AbsenceBreak` and does not pass the gate,
and the original conclusions hold. -/
def Properties.ExecutedOrBreakSatisfiable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (F : Flow)
      (ev : GateEvidence) (leg : FlowLeg) (N : ℕ) (q : ImtProof),
      Wf S ∧ DataAvailable h z0 hl S A ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ¬ GateBreak h z0 hl S F ev
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N q
        ∧ FlowFinalizableBy h z0 hl cv S A F
        ∧ ¬ LegRefundableBy h z0 hl cv S F leg N q

/-- **ON THE MIXED STATE THE BREAK IS NOT A TAUTOLOGY.**  The honest proof for
chain `1`'s only leaf, submitted for leg `hB`, carries no break — and does not pass
the gate. -/
def Properties.FullGateOrBreakNotTautology : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (id hA hB : UInt256),
    0 < cv id hA → 0 < cv id hB →
    ∃ ev : GateEvidence,
      ¬ InclusionBreak h z0 hl (mixedSystem (cv id hA)) 1 (ev ⟨1, hB⟩).1 (ev ⟨1, hB⟩).2
        ∧ ¬ FlowFinalizedBy h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ev

/-- **THE BREAK FIRES WHERE THE BUG IS.**  With the extraction-pin padding
`z0 = hl ⟨0,0,0⟩`, in `paddedSystem a b` a one-leg flow whose commit value is `a`
executes on the honest inclusion proof, AND the forged padding absence proof at
batch 0 passes the timeout gate for that same leg.  `ExecutedExcludesAnyRefundOrBreak`
must then return a break, and it is located correctly: the inclusion proof carries
none, the absence proof carries one, and it is `paddingHit`. -/
def Properties.PaddingRefundOfExecutedLegLocatesAbsenceBreak : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    ∃ (cv : CommitValue) (fh : FlowHash) (F : Flow) (ev : GateEvidence) (leg : FlowLeg)
      (N : ℕ) (q : ImtProof),
      Wf (paddedSystem a b)
        ∧ ExecutedViaBy h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) F ev leg
        ∧ LegRefundableBy h (hl ⟨0, 0, 0⟩) hl cv (paddedSystem a b) F leg N q
        ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) leg.chain (ev leg).1 (ev leg).2
        ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) F.deadline leg.chain N q
        ∧ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2 q.sibs q.pathLen q.index q.leaf
        ∧ (threeLeafTree a b).leafCount ≤ q.index ∧ hl q.leaf = hl ⟨0, 0, 0⟩

/-- **DATA AVAILABILITY IS NECESSARY, WITHOUT HASH PREMISES.**  The countermodel of
`Properties.WithoutDaCommittedLegIsStuck` with its last conjunct repaired: the committed
leg is finalized but not finalizable without DA, and no timeout evidence `(N, q)` for it
passes the gate unless `q` carries a located break.  (The first four conjuncts never
needed a hash premise.) -/
def Properties.WithoutDaCommittedLegIsStuckOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (id hA hB : UInt256),
    0 < cv id hA →
      Wf (mixedSystem (cv id hA))
        ∧ ¬ DataAvailable h z0 hl (mixedSystem (cv id hA)) noAccess
        ∧ LegFinalized h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩
        ∧ ¬ LegFinalizableBy h z0 hl cv (mixedSystem (cv id hA)) noAccess
              (mixedFlow id hA hB) ⟨0, hA⟩
        ∧ ∀ (N : ℕ) (q : ImtProof),
            ¬ LegRefundableBy h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩ N q
              ∨ AbsenceBreak h z0 hl (mixedSystem (cv id hA)) (mixedFlow id hA hB).deadline 0 N q

/-- **ITS BREAK IS NOT A TAUTOLOGY.**  The honest proof of the committed leaf, submitted
as timeout evidence at batch 0, carries no `AbsenceBreak` and does not pass. -/
def Properties.WithoutDaOrBreakNotTautology : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (id hA hB : UInt256),
    0 < cv id hA → ∃ (N : ℕ) (q : ImtProof),
      ¬ AbsenceBreak h z0 hl (mixedSystem (cv id hA)) (mixedFlow id hA hB).deadline 0 N q
        ∧ ¬ LegRefundableBy h z0 hl cv (mixedSystem (cv id hA)) (mixedFlow id hA hB) ⟨0, hA⟩ N q

/-! ## None or all, with the break pinned to a leg

`Properties.NoneOrAllOrBreak` concludes `GateBreak`: SOME leg of the flow carries a
break on its submitted proof.  The proof of that result already knows more — for
every leg, finalizable or a break on that leg's own proof
(`Properties.ExecutedImpliesAllFinalizableOrBreak`) — so when the flow is not all
finalizable, the break sits on EVERY stranded leg, in particular on the first one.
`Properties.NoneOrAllOrBreakPinned` states that, naming the first stranded leg in list
order, which is unique and determined by the instance, not by the evidence. -/

/-- **THE FIRST STRANDED LEG IS UNIQUE.** -/
def Properties.FirstStrandedLegUnique : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (A : Access)
    (F : Flow) (l₁ l₂ : FlowLeg),
    FirstStrandedLeg h z0 hl cv S A F l₁ → FirstStrandedLeg h z0 hl cv S A F l₂ → l₁ = l₂

/-- **A FIRST STRANDED LEG EXISTS EXACTLY WHEN THE FLOW IS NOT ALL FINALIZABLE.** -/
def Properties.FirstStrandedLegIffNotFinalizable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (A : Access)
    (F : Flow),
    (∃ leg, FirstStrandedLeg h z0 hl cv S A F leg) ↔ ¬ FlowFinalizableBy h z0 hl cv S A F

/-- **THE PINNED BREAK IS A GATE BREAK.**  So `NoneOrAllOrBreakPinned` implies
`NoneOrAllOrBreak`. -/
def Properties.PinnedGateBreakImpliesGateBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (A : Access)
    (F : Flow) (ev : GateEvidence),
    PinnedGateBreak h z0 hl cv S A F ev → GateBreak h z0 hl S F ev

/-- **NONE OR ALL, OR A BREAK ON THE FIRST STRANDED LEG.**  For every flow and every
evidence `ev` presented to the gate: every leg is finalizable, or `ev` executes no leg,
or the inclusion proof `ev` submits for the first leg of the flow (in list order) that
is not finalizable carries a located `TreeRootBreak`.  Strengthens
`Properties.NoneOrAllOrBreak`, whose break may sit on any leg.  Finalizable here is the
IMT half.  The destination form is
`Contracts.RootImport.Properties.NoneOrAllAtOrBreakPinned`. -/
def Properties.NoneOrAllOrBreakPinned : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A → ∀ (F : Flow) (ev : GateEvidence),
      FlowFinalizableBy h z0 hl cv S A F
        ∨ (∀ leg, ¬ ExecutedViaBy h z0 hl cv fh S F ev leg)
        ∨ PinnedGateBreak h z0 hl cv S A F ev

/-- **ITS PREMISES ARE SATISFIABLE AND ITS BREAK IS NOT A TAUTOLOGY.**  For every node
hash, leaf hash and padding constant there is a well-formed system with data
availability and a flow executed on evidence `ev` for which `PinnedGateBreak` is
false.  Weak as non-triviality evidence: in this witness the flow is finalizable, and
`PinnedGateBreak` implies it is not, so no break is ever evaluated.  The witness with a
stranded leg on which the break is evaluated and false is
`Properties.NoneOrAllOrBreakPinnedStrandedNotTautology`. -/
def Properties.NoneOrAllOrBreakPinnedNotTautology : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (F : Flow)
      (ev : GateEvidence) (leg : FlowLeg),
      Wf S ∧ DataAvailable h z0 hl S A ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ¬ PinnedGateBreak h z0 hl cv S A F ev

/-- **THE PINNED BREAK FIRES, AND THE UNPINNED ONE CAN POINT ELSEWHERE.**  For every
node hash and padding constant, with the toy leaf hash (`value - nextValue`): in the
well-formed mixed system `mixedSystem 1`, where prover access is exactly the honest
proofs (so data availability holds), the two-leg flow `mixedFlow 0 1 2` executes leg
`legA = ⟨0, 1⟩` on evidence `ev` that includes a forged inclusion proof for the
never-committed leg `legB = ⟨1, 2⟩` (a leaf-hash collision with chain `1`'s
sentinel).  So the flow is NOT all finalizable and leg `legA` executed: the third
disjunct is the only one that holds.  The first stranded leg is `legB`, and its
submitted proof carries the break.  But `legA` — finalizable — ALSO carries a break
on its submitted proof (a second leaf-hash collision), so `GateBreak`'s existential
is met by a leg that is not the stranded one; `PinnedGateBreak` names `legB`. -/
def Properties.PinnedGateBreakFires : Prop :=
  ∀ (h : Hash) (z0 : UInt256),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (F : Flow)
      (ev : GateEvidence) (legA legB : FlowLeg),
      Wf S ∧ DataAvailable h z0 toyLeafHash S A
        ∧ ExecutedViaBy h z0 toyLeafHash cv fh S F ev legA
        ∧ ¬ FlowFinalizableBy h z0 toyLeafHash cv S A F
        ∧ FirstStrandedLeg h z0 toyLeafHash cv S A F legB
        ∧ InclusionBreak h z0 toyLeafHash S legB.chain (ev legB).1 (ev legB).2
        ∧ legA ∈ F.legs ∧ legA ≠ legB
        ∧ LegFinalizableBy h z0 toyLeafHash cv S A F legA
        ∧ InclusionBreak h z0 toyLeafHash S legA.chain (ev legA).1 (ev legA).2

/-! ### The pinned break, evaluated on a stranded leg

`Properties.NoneOrAllOrBreakPinnedNotTautology`'s witness has a finalizable flow, so its
`¬ PinnedGateBreak` holds without any leg being inspected.  The two properties below
use one world in which the flow is NOT all finalizable — the well-formed `mixedSystem 1`
(chain `0` commits `1`, chain `1` commits nothing), prover access exactly the honest
proofs, the flow `mixedFlow 0 1 2` with commit value `cv _ b = b`, so leg `⟨0, 1⟩` is
committed and leg `⟨1, 2⟩` never is — and vary only the evidence submitted for the
stranded leg `⟨1, 2⟩`. -/

/-- **HONEST ACCESS IS DATA AVAILABILITY.** -/
def Properties.HonestAccessDataAvailable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System),
    DataAvailable h z0 hl S (honestAccess h z0 hl S)

/-- **THE PINNED BREAK IS EVALUATED ON A STRANDED LEG, AND IS FALSE.**  For every node
hash, leaf hash and padding constant: `mixedSystem 1` is well formed, honest access gives
data availability, `mixedFlow 0 1 2` passes `_checkFlowId` under its honest flow hash,
the flow is not all finalizable, and its first stranded leg is `⟨1, 2⟩`.  And there is
evidence `ev` that submits, for `⟨1, 2⟩`, the honest proof of chain `1`'s only leaf at
batch 0, and for `⟨0, 1⟩` a proof that passes that leg's check; on `ev` no leg executes,
and `PinnedGateBreak` — which here inspects the proof submitted for `⟨1, 2⟩` — is false.
So all premises of `Properties.NoneOrAllOrBreakPinned` hold, its first disjunct fails,
its second holds, and its third is evaluated on a named leg and fails. -/
def Properties.NoneOrAllOrBreakPinnedStrandedNotTautology : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    Wf (mixedSystem 1)
      ∧ DataAvailable h z0 hl (mixedSystem 1) (honestAccess h z0 hl (mixedSystem 1))
      ∧ FlowIdChecked (honestFlowHash (mixedFlow 0 1 2)) (mixedFlow 0 1 2)
      ∧ ¬ FlowFinalizableBy h z0 hl (fun _ b => b) (mixedSystem 1)
            (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2)
      ∧ FirstStrandedLeg h z0 hl (fun _ b => b) (mixedSystem 1)
            (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ ∃ ev : GateEvidence,
          ev ⟨1, 2⟩ = (0, honestProof h z0 hl (mixedSystem 1) 1 0 0)
          ∧ LegFinalizedBy h z0 hl (fun _ b => b) (mixedSystem 1) (mixedFlow 0 1 2) ⟨0, 1⟩
              (ev ⟨0, 1⟩).1 (ev ⟨0, 1⟩).2
          ∧ (∀ leg, ¬ ExecutedViaBy h z0 hl (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
              (mixedSystem 1) (mixedFlow 0 1 2) ev leg)
          ∧ ¬ PinnedGateBreak h z0 hl (fun _ b => b) (mixedSystem 1)
              (honestAccess h z0 hl (mixedSystem 1)) (mixedFlow 0 1 2) ev

/-- **ON THE SAME WORLD, THE PINNED BREAK FIRES ON THE STRANDED LEG AND NOWHERE ELSE.**
For every node hash and padding constant, with the toy leaf hash (`value - nextValue`),
in the world of `Properties.NoneOrAllOrBreakPinnedStrandedNotTautology` (well formed,
data available, first stranded leg `⟨1, 2⟩`): there are two evidences `evH` and `evF`
that agree on leg `⟨0, 1⟩`, whose proof there carries no break.  On `evF` leg `⟨0, 1⟩`
executes, the proof `evF` submits for `⟨1, 2⟩` carries a break, and `PinnedGateBreak`
holds; on `evH` no leg executes and `PinnedGateBreak` is false.  So the third disjunct
of `Properties.NoneOrAllOrBreakPinned` is decided by the proof submitted for the
stranded leg, and when it fires, the leg it inspects is the only leg of the flow whose
submitted proof carries a break. -/
def Properties.PinnedGateBreakFiresOnlyOnStrandedLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256),
    Wf (mixedSystem 1)
      ∧ DataAvailable h z0 toyLeafHash (mixedSystem 1) (honestAccess h z0 toyLeafHash (mixedSystem 1))
      ∧ FirstStrandedLeg h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
          (honestAccess h z0 toyLeafHash (mixedSystem 1)) (mixedFlow 0 1 2) ⟨1, 2⟩
      ∧ ∃ evH evF : GateEvidence,
          evH ⟨0, 1⟩ = evF ⟨0, 1⟩
          ∧ ¬ InclusionBreak h z0 toyLeafHash (mixedSystem 1) 0 (evF ⟨0, 1⟩).1 (evF ⟨0, 1⟩).2
          ∧ ExecutedViaBy h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
              (mixedSystem 1) (mixedFlow 0 1 2) evF ⟨0, 1⟩
          ∧ InclusionBreak h z0 toyLeafHash (mixedSystem 1) 1 (evF ⟨1, 2⟩).1 (evF ⟨1, 2⟩).2
          ∧ PinnedGateBreak h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
              (honestAccess h z0 toyLeafHash (mixedSystem 1)) (mixedFlow 0 1 2) evF
          ∧ (∀ leg, ¬ ExecutedViaBy h z0 toyLeafHash (fun _ b => b)
              (honestFlowHash (mixedFlow 0 1 2)) (mixedSystem 1) (mixedFlow 0 1 2) evH leg)
          ∧ ¬ PinnedGateBreak h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
              (honestAccess h z0 toyLeafHash (mixedSystem 1)) (mixedFlow 0 1 2) evH

end Contracts.Atomicity
