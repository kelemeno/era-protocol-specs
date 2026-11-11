import EraSpec.Protocol.InteropAtomicity.Specs.FlowBinding

/-!
# Properties: the flow-id check binds every flow the run presents

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.FlowBinding`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.FlowBinding`.

## What this repairs

`Contracts.Atomicity.Properties.ExecutedImpliesRealFlowFinalizable` says: if a leg
executes through the deployed gate, every leg of any flow that passes `_checkFlowId`
with the same id is finalizable.  It takes `HashAssumptions` and `FlowHashInj`, and both
are unsatisfiable (`HashAssumptionsUnsatisfiable`, `FlowHashInjUnsatisfiable`).  So it is
vacuous.  `Refinement.lean` (O8, item 2) records the consequence: "the check's
sufficiency is not yet proved".

`Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClash` restates it with neither
premise, over a run in which every call that checks a flow id is logged.  When a leg
executes in the run, every flow that any call of the run presented under the same id
satisfies one of:

* every leg of it is finalizable;
* the gate evidence of the executing call carries a located `TreeRootBreak`, on the
  first leg of the executed flow that is not finalizable (`PinnedGateBreak`);
* `fh` collides on the preimages of the executed flow and that flow
  (`FlowIdClash`).

## Why "the real flow" is a logged flow

Only `requireFlowFinalized` and `authorizeRefund` ever see a flow preimage (see the
Specs header).  `append` sees the sender's opaque `flowId`.  So the flows that can be
"the real flow" are exactly the flows presented to those two calls, and the run logs
both.

Where the content is.  Given two flows that both pass `_checkFlowId` with one id,
`F ≠ F'` and `FlowIdClash fh F F'` are equivalent by unfolding.  That is why
`FlowIdCheckPinsLegListOrCollision` is excluded middle (ASSUMPTIONS.md, "Recorded but
without protocol content").  Taking `F'` from the log does not change that equivalence.
It changes which flows `F'` ranges over: `F'` is the flow of a call in the run's own
log, never a flow supplied from outside the run.  So the clash disjunct reads "the run
itself submitted two different preimages under one checked id", a collision extracted
from the run's own calldata.  The rest of the statement is protocol content:
`requireFlowFinalized`'s loop over all legs, the IMT soundness reduction, and data
availability.  `Properties.SubsetFlowAttackLandsInLoggedClash` shows that the attack
`_checkFlowId` exists to stop lands in the clash disjunct and in no other.

## The refund side

`Properties.LoggedExecutionExcludesLoggedRefundOrBreak` is the call-level form of
delivered-xor-refunded.  Take a logged execution and a logged `authorizeRefund` that
claim one flow id.  Then one of three things holds: the executing call's inclusion proof
for the refund's missing leg carries a break; the refund's absence proof carries a
break; or the two flows clash.  Each disjunct fires on its own in one of the witnesses.

## Witnesses

| Witness | Which disjunct holds |
|---|---|
| `ExecutedImpliesRealFlowFinalizableOrLoggedClashWitness` | finalizable: honest run, non-empty log, no break and no clash |
| `SubsetFlowAttackLandsInLoggedClash` | the logged clash, in both results |
| `ForgedSiblingProofLandsInPinnedBreak` | the pinned gate break; in the refund result, the inclusion break |
| `PaddingRefundLandsInAbsenceBreak` | in the refund result, the absence break |

The first witness also shows that the same-id premise is load-bearing.  It holds a
logged call with a different id for which all three disjuncts fail.
-/

namespace Contracts.FlowBinding

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Refund
open Contracts.AtomicFlowManager

/-! ## The logged run -/

/-- **EVERY LOGGED CALL PASSED ITS CHECKS.**  In particular, the flow of every logged
call passed `_checkFlowId`. -/
def Properties.LoggedCallsVerified : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Ms Ns : Managers) (log : List CheckedCall),
    RunLog h z0 hl cv fh S Ms Ns log →
      ∀ c ∈ log, c.Verified h z0 hl cv fh S ∧ FlowIdChecked fh c.flow

/-- **LOGGING THE EXECUTIONS CHANGES NOTHING ON THE MANAGER SIDE.**  The `authorizeRefund`
calls of a `RunLog` form a `ReachLog` between the same manager states.  So every
`Contracts.Refund` result over `ReachLog` applies to `authCalls log`. -/
def Properties.RunLogAuthCallsReachLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Ms Ns : Managers) (log : List CheckedCall),
    RunLog h z0 hl cv fh S Ms Ns log → ReachLog h z0 hl cv fh S Ms Ns (authCalls log)

/-- **AND NO MANAGER RUN IS LOST.**  Every `ReachLog` is a `RunLog` with no executions,
whose authorize log is the original one. -/
def Properties.ReachLogEmbedsInRunLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (Ms Ns : Managers) (alog : List AuthCall),
    ReachLog h z0 hl cv fh S Ms Ns alog →
      RunLog h z0 hl cv fh S Ms Ns (alog.map CheckedCall.authorize)
        ∧ authCalls (alog.map CheckedCall.authorize) = alog

/-! ## The real flow -/

/-- **PARTIAL ATOMICITY OVER THE REAL FLOW, OR A LOCATED BREAK, OR A LOGGED CLASH.**
The repaired form of `Contracts.Atomicity.Properties.ExecutedImpliesRealFlowFinalizable`.

Premises: a well-formed system and data availability.  Then take a logged run, any
execution `e` in its log, and any call `c` in the same log whose flow claims `e`'s flow
id.  One of three things holds:

* every leg of `c.flow` is finalizable by a presentable proof;
* the evidence `e` submitted carries a `TreeRootBreak` on the first leg of `e.flow`, in
  list order, that is not finalizable (`PinnedGateBreak`);
* `fh` collides on exactly the `(legs, deadline)` preimages of `e.flow` and `c.flow`,
  two flows the run itself presented (`FlowIdClash`).

There is no hash premise.  Unlike `FlowIdCheckPinsLegListOrCollision`, the other flow
comes from the run's log, not from outside it (see the module header). -/
def Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (Ms Ns : Managers) (log : List CheckedCall), RunLog h z0 hl cv fh S Ms Ns log →
    ∀ (e : ExecCall), CheckedCall.execute e ∈ log →
    ∀ c ∈ log, c.flow.flowId = e.flow.flowId →
      FlowFinalizableBy h z0 hl cv S A c.flow
        ∨ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
        ∨ FlowIdClash fh e.flow c.flow

/-- **THE SAME, PER LEG.**  For every leg `other` of a logged flow that claims the
executed flow's id: `other` is finalizable, or the inclusion proof the execution
submitted for `other` carries a break, or the two flows clash.  The logged counterpart
of `Contracts.Atomicity.Properties.ExecutedImpliesAllFinalizableOrBreak`. -/
def Properties.ExecutedImpliesRealFlowLegFinalizableOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (A : Access), DataAvailable h z0 hl S A →
    ∀ (Ms Ns : Managers) (log : List CheckedCall), RunLog h z0 hl cv fh S Ms Ns log →
    ∀ (e : ExecCall), CheckedCall.execute e ∈ log →
    ∀ c ∈ log, c.flow.flowId = e.flow.flowId →
    ∀ other ∈ c.flow.legs,
      LegFinalizableBy h z0 hl cv S A c.flow other
        ∨ InclusionBreak h z0 hl S other.chain (e.evidence other).1 (e.evidence other).2
        ∨ FlowIdClash fh e.flow c.flow

/-! ## The refund side -/

/-- **A LOGGED EXECUTION AND A LOGGED REFUND AUTHORIZATION OF ONE FLOW ID: A LOCATED
BREAK OR A LOGGED CLASH.**  Take a well-formed system and a logged run, with an
execution `e` and an `authorizeRefund` call `a` in its log whose flows claim one id.
Both calls succeeded, so one of three things holds:

* the inclusion proof `e` submitted for `a`'s missing leg carries a break;
* `a`'s own absence proof carries a break, on the root its timeout branch selects;
* `fh` collides on the two flows' preimages.

This is delivered-xor-refunded at the level of the calls, with every witness named by
the log. -/
def Properties.LoggedExecutionExcludesLoggedRefundOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (Ms Ns : Managers) (log : List CheckedCall), RunLog h z0 hl cv fh S Ms Ns log →
    ∀ (e : ExecCall), CheckedCall.execute e ∈ log →
    ∀ (a : AuthCall), CheckedCall.authorize a ∈ log → a.flow.flowId = e.flow.flowId →
      InclusionBreak h z0 hl S a.missing.chain (e.evidence a.missing).1 (e.evidence a.missing).2
        ∨ AbsenceBreak h z0 hl S a.flow.deadline a.missing.chain a.batch a.proof
        ∨ FlowIdClash fh e.flow a.flow

/-! ## Witnesses -/

/-- **THE PREMISES HOLD ON AN HONEST RUN WITH A NON-EMPTY LOG, AND THE SAME-ID PREMISE
IS LOAD-BEARING.**  For every node hash, leaf hash and padding constant there is a
well-formed system with data availability and a logged run from fresh managers whose
log holds:

* an execution `e`;
* a second execution `e'` of the same flow, for a different leg, presented as the call
  `c`;
* an `authorizeRefund` call `d` for a flow with a different id.

For `c` the first disjunct of `ExecutedImpliesRealFlowFinalizableOrLoggedClash` holds.
`e`'s evidence carries no pinned break, and `e.flow` clashes with no logged flow.  For
`d` all three disjuncts fail, so the conclusion cannot be drawn without the same-id
premise. -/
def Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClashWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (A : Access) (Ms : Managers)
      (log : List CheckedCall) (e e' : ExecCall) (c d : CheckedCall) (r : AuthCall),
      Wf S ∧ DataAvailable h z0 hl S A ∧ RunLog h z0 hl cv fh S emptyManagers Ms log
        ∧ CheckedCall.execute e ∈ log ∧ c ∈ log ∧ d ∈ log
        ∧ c = CheckedCall.execute e' ∧ e'.flow = e.flow ∧ e'.leg ≠ e.leg
        ∧ d = CheckedCall.authorize r
        ∧ c.flow.flowId = e.flow.flowId
        ∧ FlowFinalizableBy h z0 hl cv S A c.flow
        ∧ ¬ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
        ∧ (∀ c' ∈ log, ¬ FlowIdClash fh e.flow c'.flow)
        ∧ d.flow.flowId ≠ e.flow.flowId
        ∧ ¬ (FlowFinalizableBy h z0 hl cv S A d.flow
              ∨ PinnedGateBreak h z0 hl cv S A e.flow e.evidence
              ∨ FlowIdClash fh e.flow d.flow)

/-- **THE SUBSET-FLOW ATTACK LANDS IN THE LOGGED CLASH.**
`Contracts.Atomicity.Properties.SubsetFlowPassesUncheckedGate`, replayed against the
deployed gate.

The system is `mixedSystem (cv id hA)`: chain `0` commits leg `hA`, chain `1` never
commits leg `hB`.  Prover access is the honest proofs, so data availability holds.  The
run does three things:

1. it appends `hB`'s obligation on chain `1`;
2. it executes leg `⟨0, hA⟩` through the truncated flow `subsetFlow id hA`, on honest
   evidence;
3. it authorizes a refund of the real flow `mixedFlow id hA hB` on the honest absence
   proof for `hB`.

Both flows pass `_checkFlowId` under the constant flow hash `fun _ _ => id`, which
collides on their two preimages, as it must for the attack to pass.  The two calls claim
one id, and for that pair:

* in `ExecutedImpliesRealFlowFinalizableOrLoggedClash`, and in its per-leg form at the
  missing leg, the first two disjuncts fail and the clash holds;
* in `LoggedExecutionExcludesLoggedRefundOrBreak`, both breaks fail and the clash
  holds.

So this attack is exactly a collision on two preimages the run itself submitted. -/
def Properties.SubsetFlowAttackLandsInLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (id hA hB : UInt256),
    0 < cv id hA → 0 < cv id hB →
    ∃ (Ms : Managers) (log : List CheckedCall) (e : ExecCall) (a : AuthCall),
      Wf (mixedSystem (cv id hA))
        ∧ DataAvailable h z0 hl (mixedSystem (cv id hA))
            (honestAccess h z0 hl (mixedSystem (cv id hA)))
        ∧ RunLog h z0 hl cv (fun _ _ => id) (mixedSystem (cv id hA)) emptyManagers Ms log
        ∧ CheckedCall.execute e ∈ log ∧ CheckedCall.authorize a ∈ log
        ∧ e.flow = subsetFlow id hA ∧ e.leg = ⟨0, hA⟩
        ∧ a.flow = mixedFlow id hA hB ∧ a.missing = ⟨1, hB⟩
        ∧ a.flow.flowId = e.flow.flowId
        ∧ ¬ LegFinalizableBy h z0 hl cv (mixedSystem (cv id hA))
            (honestAccess h z0 hl (mixedSystem (cv id hA))) a.flow a.missing
        ∧ ¬ FlowFinalizableBy h z0 hl cv (mixedSystem (cv id hA))
            (honestAccess h z0 hl (mixedSystem (cv id hA))) a.flow
        ∧ ¬ PinnedGateBreak h z0 hl cv (mixedSystem (cv id hA))
            (honestAccess h z0 hl (mixedSystem (cv id hA))) e.flow e.evidence
        ∧ ¬ InclusionBreak h z0 hl (mixedSystem (cv id hA)) a.missing.chain
            (e.evidence a.missing).1 (e.evidence a.missing).2
        ∧ ¬ AbsenceBreak h z0 hl (mixedSystem (cv id hA)) a.flow.deadline a.missing.chain
            a.batch a.proof
        ∧ FlowIdClash (fun _ _ => id) e.flow a.flow

/-- **A FORGED PROOF FOR A STRANDED SIBLING LANDS IN THE PINNED BREAK.**  The setting is
`Contracts.Atomicity.Properties.PinnedGateBreakFiresOnlyOnStrandedLeg`'s world, as a
run.  It holds for every node hash and padding constant, with the toy leaf hash.

The system is `mixedSystem 1`: chain `0` commits `1`, chain `1` commits nothing.  Prover
access is the honest proofs, so data availability holds.  The flow is `mixedFlow 0 1 2`,
checked by its honest flow hash.  The run does three things:

1. it appends leg `⟨1, 2⟩`'s obligation;
2. it executes leg `⟨0, 1⟩`, on evidence whose proof for the never-committed leg
   `⟨1, 2⟩` is forged (a leaf-hash collision with chain `1`'s sentinel);
3. it authorizes a refund of the same flow on the honest absence proof for `⟨1, 2⟩`.

For the refund call:

* in `ExecutedImpliesRealFlowFinalizableOrLoggedClash`, the flow is not finalizable and
  there is no clash, so the pinned break is the disjunct that holds;
* the proof the execution submitted for its own leg carries no break, so the break sits
  on the stranded leg's proof;
* in `LoggedExecutionExcludesLoggedRefundOrBreak`, the inclusion break on the refund's
  missing leg holds, and the absence break and the clash fail. -/
def Properties.ForgedSiblingProofLandsInPinnedBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256),
    ∃ (Ms : Managers) (log : List CheckedCall) (e : ExecCall) (a : AuthCall),
      Wf (mixedSystem 1)
        ∧ DataAvailable h z0 toyLeafHash (mixedSystem 1)
            (honestAccess h z0 toyLeafHash (mixedSystem 1))
        ∧ RunLog h z0 toyLeafHash (fun _ b => b) (honestFlowHash (mixedFlow 0 1 2))
            (mixedSystem 1) emptyManagers Ms log
        ∧ CheckedCall.execute e ∈ log ∧ CheckedCall.authorize a ∈ log
        ∧ e.flow = mixedFlow 0 1 2 ∧ e.leg = ⟨0, 1⟩
        ∧ a.flow = mixedFlow 0 1 2 ∧ a.missing = ⟨1, 2⟩
        ∧ ¬ LegFinalizableBy h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
            (honestAccess h z0 toyLeafHash (mixedSystem 1)) a.flow a.missing
        ∧ ¬ FlowFinalizableBy h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
            (honestAccess h z0 toyLeafHash (mixedSystem 1)) a.flow
        ∧ PinnedGateBreak h z0 toyLeafHash (fun _ b => b) (mixedSystem 1)
            (honestAccess h z0 toyLeafHash (mixedSystem 1)) e.flow e.evidence
        ∧ ¬ FlowIdClash (honestFlowHash (mixedFlow 0 1 2)) e.flow a.flow
        ∧ ¬ InclusionBreak h z0 toyLeafHash (mixedSystem 1) e.leg.chain
            (e.evidence e.leg).1 (e.evidence e.leg).2
        ∧ InclusionBreak h z0 toyLeafHash (mixedSystem 1) a.missing.chain
            (e.evidence a.missing).1 (e.evidence a.missing).2
        ∧ ¬ AbsenceBreak h z0 toyLeafHash (mixedSystem 1) a.flow.deadline a.missing.chain
            a.batch a.proof

/-- **A FORGED PADDING ABSENCE PROOF LANDS IN THE ABSENCE BREAK.**  The padding is the
extraction pin's, `z0 = hl ⟨0,0,0⟩`.  The system is `paddedSystem a b`.  The run appends
the obligation of a one-leg flow and executes that leg on the honest inclusion proof.
It then authorizes a refund of the same flow on the forged padding absence proof.

In `LoggedExecutionExcludesLoggedRefundOrBreak` for that pair, the absence break holds,
and the inclusion break and the clash fail.  With
`Properties.ForgedSiblingProofLandsInPinnedBreak` and
`Properties.SubsetFlowAttackLandsInLoggedClash`, each of that result's three disjuncts
is shown to hold alone on some run. -/
def Properties.PaddingRefundLandsInAbsenceBreak : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    ∃ (cv : CommitValue) (fh : FlowHash) (Ms : Managers) (log : List CheckedCall)
      (e : ExecCall) (r : AuthCall),
      Wf (paddedSystem a b)
        ∧ RunLog h (hl ⟨0, 0, 0⟩) hl cv fh (paddedSystem a b) emptyManagers Ms log
        ∧ CheckedCall.execute e ∈ log ∧ CheckedCall.authorize r ∈ log
        ∧ r.flow = e.flow
        ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) r.missing.chain
            (e.evidence r.missing).1 (e.evidence r.missing).2
        ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) r.flow.deadline r.missing.chain
            r.batch r.proof
        ∧ ¬ FlowIdClash fh e.flow r.flow

end Contracts.FlowBinding
