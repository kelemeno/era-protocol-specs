import EraSpec.Protocol.InteropAtomicity.Specs.RefundFaithful

/-!
# Properties: one outcome per obligation, with `authorizeRefund` as it runs

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.RefundFaithful`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.RefundFaithful`.  Pin: era-contracts `c67894b9`.

## What `Refund.ReachLog` leaves out

`Contracts.Refund.ReachLog` writes an `authorize` step to the slot of the leg's declared
chain, and checks its END branch through `IsLastOnTime`.  The contract writes the calling
chain's slot and checks the END branch through `_verifyLastBatchInRoot`.  Each difference
leaves out runs of the deployed model:

* `Properties.MisdeclaredLegRefundedOnlyInDeployedModel`: a leg committed on chain `0`
  under a flow that declares it on chain `1` is moved past `Committed` on chain `0` by an
  `authorizeRefund` iteration on chain `0` (its declared chain never committed it, so an
  honest BEGIN-branch timeout passes), while no `ReachLog` run under the same flow hash
  moves that slot past `Committed`.
* `Properties.StaleRootEndRefundOfDeliveredLegIsDeployed`: against a root that omits a
  batch of the leg's chain that had settled before it (`Timeout.staleRoot`, which violates
  `Timeout.Aggregates`), the deployed END branch moves past `Committed` the slot of a leg
  that passed the execution gate, while the old gate `LegRefundableBy` rejects that leg
  for every batch and proof and no `ReachLog` run under the same flow hash moves the slot.
  The deployed headline below returns exactly the `staleRoot` break there.

So `Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreak`,
`OneExecutionFreezesTheFlowOrBreak`, `RefundImpliesOwnFlowTimeoutOrLoggedClash` and
`RefundNeedsLoggedAuthorize` range over `ReachLog` runs, which omit these two.
`FlowBinding.RunLog` and `AppendPath.SysSteps` runs project to `ReachLog` runs with the
same managers (`Contracts.FlowBinding.Properties.RunLogAuthCallsReachLog`,
`Contracts.AppendPath.Properties.SystemProjectsToReachLog`), so the results over them omit
these two as well.  The deployed END branch also admits every submission
`Timeout.LegRefundableAcceptedBy` admits (`Properties.AcceptedByIsDeployedTimeout`), plus
batch-leaf paths of another length or at an unoccupied position, which the contract does
not reject (`MerkleSpec.LastLeafFaithful.Properties.WrongLengthLastLeafAccepted`,
`PaddedIndexLastLeafAccepted`, at the level of the last-leaf check, with the claimed leaf
hash free).

## What holds over the deployed runs

* `Properties.DeployedExecutedFlowFrozenOrBreak`, with no hash premise and no premise on
  the settlement-layer roots: if any leg of `F` passed the execution gate on evidence `ev`,
  then every slot carrying `F`'s id, on every chain and for every bundle hash, never moves
  past `Committed`, or an iteration in the run's log that wrote it carries a
  `DeployedRefundBreak`: a flow-id clash, a break on the gate's or the timeout's IMT proof,
  a batch-leaf path that is not the last leaf at the chain tree's height in a located way,
  or a stale root for the missing leg's chain.
  `Properties.DeployedExecutedObligationNeverRefundedOrBreak` and
  `Properties.DeployedOneExecutionFreezesTheFlowOrBreak` are its per-leg forms.
* `Properties.DeployedExecutedFlowFrozenOrBreakUnderHonestRoots`: with the premise that
  every logged iteration's root satisfies `Timeout.Aggregates`, the `staleRoot` case is
  gone.
* These locate a refund of an executed flow's slot; at `c67894b9` they do not exclude it.
  The pinned padding `hashLeaf({0,0,0})` gives the `AbsenceBreak` case with no collision
  when the missing leg's tree has an empty slot below capacity, also under aggregating
  roots (`Properties.DeployedPaddingRefundLocatesAbsenceBreak`; the note at
  `Contracts.InteropCommitmentTree.HashAssumptions`).
* `Properties.DeployedRefundImpliesOwnAcceptedTimeoutOrLoggedClash`: a slot past
  `Committed` that carries a checked flow's id was written by a logged iteration whose flow
  is that flow and whose timeout evidence passes `DeployedTimeoutAccepted`, or by one whose
  flow clashes with it.
* `Properties.DeployedRunAppendsOnce`: no slot is appended twice, every logged iteration
  wrote an appended slot, and a slot past `Committed` occurs in the append log exactly
  once.  This is the manager half of `AppendPath.Properties.SystemRefundedWasAppendedOnce`
  and of the first conjunct of `SystemAuthorizedWereAppended`; the tree half (the commit
  value is a key of the chain's tree) stays with `AppendPath.SysSteps`, whose `authorize`
  still writes the declared chain.

## Witnesses

`Properties.DeployedExecutedFlowFrozenOrBreakWitness` meets every premise of the four
executed-flow statements with the executed leg's slot appended and still `Committed`, a
second flow's slot refunded on another chain against an honest root, and no break.
`Properties.DeployedRefundOwnTimeoutWitness` meets every premise of
`DeployedRefundNeedsLoggedIteration`, `DeployedRunAppendsOnce` and
`DeployedRefundImpliesOwnAcceptedTimeoutOrLoggedClash` with a refunded slot, its own
accepted timeout and no clash.  The premise of `AcceptedByIsDeployedTimeout` is met by
`Contracts.Refund.Properties.AcceptedTimeoutAuthorizesPinnedWitness` (END branch).

## Not covered

Model boundaries are listed in the Specs module docstring.  At the current heads `append`
binds the committed bundle to the committing chain (Specs, "Current heads"), which the
statements here do not model.
-/

namespace Contracts.RefundFaithful

open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.LastLeafFaithful MerkleSpec.Verifier IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager Contracts.Refund

/-! ## The deployed timeout check against the repository's -/

/-- **THE DEPLOYED TIMEOUT CHECK ADMITS EVERY SUBMISSION `LegRefundableAcceptedBy` ADMITS.**
A submission `(N, p, sibs, x)` accepted by `Timeout.LegRefundableAcceptedBy` is accepted by
`DeployedTimeoutAccepted` with the batch-leaf path's length set to the chain tree's
height. -/
def Properties.AcceptedByIsDeployedTimeout : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R) (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof)
    (sibs : ℕ → UInt256) (x : UInt256),
    LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
      DeployedTimeoutAccepted h z0 hl cv S B F leg N p (B.height leg.chain) sibs x

/-! ## The deployed run's bookkeeping -/

/-- **A SLOT PAST `Committed` WAS WRITTEN BY A LOGGED, VERIFIED ITERATION.**  The deployed
form of `Contracts.Refund.Properties.RefundNeedsLoggedAuthorize`: the iteration ran on the
slot's own chain, which need not be any declared chain of its flow. -/
def Properties.DeployedRefundNeedsLoggedIteration : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (ze : UInt256) (Ms : Managers) (plog : List Obligation)
    (alog : List (DeployedAuthCall h ze)),
    DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      ∀ (o : Obligation), Refunded Ms o →
        ∃ a ∈ alog, a.Verified h z0 hl cv fh S ∧ a.marks = o

/-- **APPENDED ONCE, AUTHORIZED ONLY AFTER APPEND.**  Over every deployed run from fresh
managers: the append log has no repeats, every logged iteration wrote a slot in it, and
every slot past `Committed` occurs in it exactly once. -/
def Properties.DeployedRunAppendsOnce : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (ze : UInt256) (Ms : Managers) (plog : List Obligation)
    (alog : List (DeployedAuthCall h ze)),
    DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      plog.Nodup ∧ (∀ a ∈ alog, a.marks ∈ plog)
        ∧ ∀ (o : Obligation), Refunded Ms o → plog.count o = 1

/-! ## The milestone over the deployed runs -/

/-- **AN EXECUTED FLOW IS FROZEN ON EVERY CHAIN, OR A LOCATED BREAK.**  No hash premise and
no premise on the settlement-layer roots.  If leg `leg` of `F` passed the execution gate on
evidence `ev`, then in every deployed run from fresh managers, every slot carrying `F`'s
id, on any chain and for any bundle hash, stays at `Committed` or below, or an iteration in
the run's log that wrote it carries a `DeployedRefundBreak`.  At `c67894b9` the `absence`
case needs no collision when the missing leg's tree has an empty slot below capacity
(`Properties.DeployedPaddingRefundLocatesAbsenceBreak`). -/
def Properties.DeployedExecutedFlowFrozenOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (ze : UInt256) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      ∀ (o : Obligation), o.flowId = F.flowId →
        ¬ Refunded Ms o ∨ DeployedRefundBreak h z0 hl fh S ze F ev o alog

/-- **AN EXECUTED LEG'S OWN SLOT IS NEVER REFUNDED, OR A LOCATED BREAK.**  The deployed form
of `Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreak`, for the slot of the
executed leg on its declared chain. -/
def Properties.DeployedExecutedObligationNeverRefundedOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (ze : UInt256) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
        ¬ Refunded Ms (obligationOf F leg)
          ∨ DeployedRefundBreak h z0 hl fh S ze F ev (obligationOf F leg) alog

/-- **ONE EXECUTION FREEZES EVERY LEG'S SLOT ON EVERY CHAIN, OR A LOCATED BREAK.**  The
deployed form of `Contracts.Refund.Properties.OneExecutionFreezesTheFlowOrBreak`, for each
leg's bundle hash on every chain `c`, not only on the leg's declared chain. -/
def Properties.DeployedOneExecutionFreezesTheFlowOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (ze : UInt256) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      ∀ other ∈ F.legs, ∀ c : Chain,
        ¬ Refunded Ms ⟨F.flowId, other.bundleHash, c⟩
          ∨ DeployedRefundBreak h z0 hl fh S ze F ev ⟨F.flowId, other.bundleHash, c⟩ alog

/-- **WITH AGGREGATING ROOTS, NO STALE-ROOT CASE.**  The added premise: every root a logged
iteration resolved against satisfies `Timeout.Aggregates` (ASSUMPTIONS.md
`PROTO-AGGREGATES`).  Then the iteration behind a refunded slot of an executed flow shows a
flow-id clash, a `TreeRootBreak` on the gate's or the timeout's IMT proof, or, on the END
branch, a `LastLeafAnyLengthBreak` on its batch-leaf path.  The premise is met with a
nonempty log by `Properties.DeployedExecutedFlowFrozenOrBreakWitness`; without it the
`staleRoot` case occurs (`Properties.StaleRootEndRefundOfDeliveredLegIsDeployed`).  At
`c67894b9` the `AbsenceBreak` case needs no collision when the missing leg's tree has an
empty slot below capacity (`Properties.DeployedPaddingRefundLocatesAbsenceBreak`), so this
locates the refund of an executed flow's slot; it does not exclude it at the pin. -/
def Properties.DeployedExecutedFlowFrozenOrBreakUnderHonestRoots : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (ze : UInt256) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      (∀ a ∈ alog, Aggregates S a.root) →
      ∀ (o : Obligation), o.flowId = F.flowId →
        ¬ Refunded Ms o
          ∨ ∃ a ∈ alog, a.marks = o
              ∧ (FlowIdClash fh F a.flow
                ∨ (a.flow = F
                  ∧ (InclusionBreak h z0 hl S a.missing.chain (ev a.missing).1 (ev a.missing).2
                    ∨ AbsenceBreak h z0 hl S F.deadline a.missing.chain a.batch a.proof
                    ∨ (DeployedEndBranch a.backing S a.missing.chain F.deadline a.batch a.pathLen
                          a.pathSibs a.pathLeaf
                        ∧ LastLeafAnyLengthBreak h ze (a.backing.leaves a.missing.chain)
                            a.pathSibs a.pathLen (a.backing.height a.missing.chain) a.batch
                            a.pathLeaf))))

/-- **A SLOT PAST `Committed` WITH A CHECKED FLOW'S ID HAS THAT FLOW'S OWN ACCEPTED TIMEOUT
BEHIND IT, OR A LOGGED CLASH.**  The deployed form of
`Contracts.Refund.Properties.RefundImpliesOwnFlowTimeoutOrLoggedClash`, for any slot with
`F`'s id on any chain: an iteration that wrote it has flow `F`, a missing leg of `F` and
timeout evidence accepted by `DeployedTimeoutAccepted`, or an iteration that wrote it has a
flow that clashes with `F`. -/
def Properties.DeployedRefundImpliesOwnAcceptedTimeoutOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (ze : UInt256) (F : Flow), FlowIdChecked fh F →
    ∀ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      ∀ (o : Obligation), o.flowId = F.flowId → Refunded Ms o →
        (∃ a ∈ alog, a.marks = o ∧ a.flow = F ∧ a.missing ∈ F.legs
            ∧ DeployedTimeoutAccepted h z0 hl cv S a.backing F a.missing a.batch a.proof
                a.pathLen a.pathSibs a.pathLeaf)
          ∨ ∃ a ∈ alog, a.marks = o ∧ FlowIdClash fh F a.flow

/-! ## The runs `Refund.ReachLog` leaves out -/

/-- **A MIS-DECLARED LEG REACHES `Revertable` ON ITS REAL CHAIN, IN THE DEPLOYED MODEL
ONLY.**  For every node hash, leaf hash, padding constant and chain-tree empty constant, in
`mixedSystem 1` (chain `0` commits the value `1` in batch 0, chain `1` never commits) with
commit value `1`: `misdeclaredFlow` declares bundle `2` on chain `1`, and chain `0`'s
manager holds the slot `⟨1, 2, 0⟩`, which is the slot of no declared leg.  Its commit value
is a key of chain `0`'s tree and of none of chain `1`'s.  A deployed run (append on chain
`0`, then an `authorizeRefund` iteration on chain `0` with an honest BEGIN-branch timeout
for the declared leg) moves it past `Committed`.  No `Contracts.Refund.ReachLog` run under
the same flow hash does.

What happens to the funds after `Revertable` (`claimRefund`) is not modelled here.  At
`c67894b9` the bundle in such a slot cannot execute (the Specs header, section 1): its hash binds
the sending chain and the finality check binds each proof to the declared chain, so, up to a
hash collision, the flow never finalizes and the refund returns the funds of a bundle that
does not execute. -/
def Properties.MisdeclaredLegRefundedOnlyInDeployedModel : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ze : UInt256),
    ∃ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      Wf (mixedSystem 1)
        ∧ FlowIdChecked (honestFlowHash misdeclaredFlow) misdeclaredFlow
        ∧ misdeclaredObligation.flowId = misdeclaredFlow.flowId
        ∧ (∀ leg ∈ misdeclaredFlow.legs, obligationOf misdeclaredFlow leg ≠ misdeclaredObligation)
        ∧ (fun _ _ => (1 : UInt256)) misdeclaredObligation.flowId misdeclaredObligation.bundleHash
            ∈ keys (toAbs ((mixedSystem 1).tree 0 0))
        ∧ (∀ n, (fun _ _ => (1 : UInt256)) misdeclaredObligation.flowId
              misdeclaredObligation.bundleHash ∉ keys (toAbs ((mixedSystem 1).tree 1 n)))
        ∧ DeployedRun h z0 hl (fun _ _ => 1) (honestFlowHash misdeclaredFlow) (mixedSystem 1) ze
            emptyManagers Ms plog alog
        ∧ Refunded Ms misdeclaredObligation
        ∧ ∀ (Ms' : Managers) (log' : List AuthCall),
            ReachLog h z0 hl (fun _ _ => 1) (honestFlowHash misdeclaredFlow) (mixedSystem 1)
                emptyManagers Ms' log' →
              ¬ Refunded Ms' misdeclaredObligation

/-- **A STALE-ROOT END-BRANCH REFUND OF AN EXECUTED LEG IS A DEPLOYED RUN, AND NO OLD RUN.**
For every node hash, leaf hash, padding constant and chain-tree empty constant: in
`Timeout.staleSystem 1` (every batch settles at time `0`; the value `1` is committed in
batch 1), `staleFlow`'s leg passes the execution gate on the honest inclusion proof at
batch 1.  Against `Timeout.staleRoot` (created after the deadline, but holding batch 0
only), the deployed END branch accepts the honest absence proof at batch 0, so a deployed
run moves the executed leg's slot past `Committed`.  The old gate `LegRefundableBy` rejects
this leg for every batch and proof, and no `ReachLog` run moves the slot.  The deployed
headline's break is `staleRoot`: every logged iteration is `staleFlow`'s own, with no
flow-id clash, no break on either IMT proof, no `LastLeafAnyLengthBreak` on its batch-leaf
path, and a root that is stale for the missing leg's chain. -/
def Properties.StaleRootEndRefundOfDeliveredLegIsDeployed : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ze : UInt256),
    ∃ (ev : GateEvidence) (leg : FlowLeg) (Ms : Managers) (plog : List Obligation)
      (alog : List (DeployedAuthCall h ze)),
      Wf (staleSystem 1)
        ∧ ExecutedViaBy h z0 hl (fun _ _ => 1) (honestFlowHash staleFlow) (staleSystem 1)
            staleFlow ev leg
        ∧ ¬ InclusionBreak h z0 hl (staleSystem 1) leg.chain (ev leg).1 (ev leg).2
        ∧ DeployedRun h z0 hl (fun _ _ => 1) (honestFlowHash staleFlow) (staleSystem 1) ze
            emptyManagers Ms plog alog
        ∧ Refunded Ms (obligationOf staleFlow leg)
        ∧ (∀ (N : ℕ) (p : ImtProof),
            ¬ LegRefundableBy h z0 hl (fun _ _ => 1) (staleSystem 1) staleFlow leg N p)
        ∧ (∀ (Ms' : Managers) (log' : List AuthCall),
            ReachLog h z0 hl (fun _ _ => 1) (honestFlowHash staleFlow) (staleSystem 1)
                emptyManagers Ms' log' →
              ¬ Refunded Ms' (obligationOf staleFlow leg))
        ∧ DeployedRefundBreak h z0 hl (honestFlowHash staleFlow) (staleSystem 1) ze staleFlow ev
            (obligationOf staleFlow leg) alog
        ∧ ∀ a ∈ alog, a.flow = staleFlow
            ∧ ¬ FlowIdClash (honestFlowHash staleFlow) staleFlow a.flow
            ∧ ¬ InclusionBreak h z0 hl (staleSystem 1) a.missing.chain (ev a.missing).1
                (ev a.missing).2
            ∧ ¬ AbsenceBreak h z0 hl (staleSystem 1) staleFlow.deadline a.missing.chain a.batch
                a.proof
            ∧ ¬ LastLeafAnyLengthBreak h ze (a.backing.leaves a.missing.chain) a.pathSibs
                a.pathLen (a.backing.height a.missing.chain) a.batch a.pathLeaf
            ∧ StaleRootFor (staleSystem 1) a.root a.missing.chain

/-- **AT `c67894b9` THE ABSENCE BREAK NEEDS NO COLLISION, ALSO UNDER AGGREGATING ROOTS.**  For
every node hash and leaf hash with the pinned padding `z0 = hl ⟨0,0,0⟩`, every chain-tree
empty constant and every `0 < a < b`: in `Atomicity.paddedSystem a b` (chain `0` holds
`threeLeafTree a b` from batch 0, whose slot 3 is empty; batch numbers are timestamps) the
one-leg flow `subsetFlow 0 0` with commit value `a` passes the execution gate on the honest
inclusion proof.  A deployed run appends its slot on chain `0` and moves it past `Committed`
with one iteration on chain `0` whose timeout evidence is the BEGIN branch at batch 1, with
the sentinel `{0,0,0}` at slot 3 as the absence proof, against a root that satisfies
`Aggregates`.  Every logged iteration wrote that slot with the executed flow itself: no
flow-id clash, no break on the gate's proof, and an `AbsenceBreak` on its own absence proof
whose `TreeRootBreak` on the BEGIN tree is exactly `paddingHit` (no collision case).  So
`DeployedExecutedFlowFrozenOrBreakUnderHonestRoots` returns the `AbsenceBreak` case here. -/
def Properties.DeployedPaddingRefundLocatesAbsenceBreak : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (ze a b : UInt256), 0 < a → a < b →
    ∃ (ev : GateEvidence) (Ms : Managers) (plog : List Obligation)
      (alog : List (DeployedAuthCall h ze)),
      Wf (paddedSystem a b)
        ∧ ExecutedViaBy h (hl ⟨0, 0, 0⟩) hl (fun _ _ => a) (honestFlowHash (subsetFlow 0 0))
            (paddedSystem a b) (subsetFlow 0 0) ev ⟨0, 0⟩
        ∧ DeployedRun h (hl ⟨0, 0, 0⟩) hl (fun _ _ => a) (honestFlowHash (subsetFlow 0 0))
            (paddedSystem a b) ze emptyManagers Ms plog alog
        ∧ alog ≠ [] ∧ (∀ x ∈ alog, Aggregates (paddedSystem a b) x.root)
        ∧ Refunded Ms (obligationOf (subsetFlow 0 0) ⟨0, 0⟩)
        ∧ ∀ x ∈ alog, x.marks = obligationOf (subsetFlow 0 0) ⟨0, 0⟩
            ∧ x.flow = subsetFlow 0 0
            ∧ ¬ FlowIdClash (honestFlowHash (subsetFlow 0 0)) (subsetFlow 0 0) x.flow
            ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) x.missing.chain
                (ev x.missing).1 (ev x.missing).2
            ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl (paddedSystem a b) (subsetFlow 0 0).deadline
                x.missing.chain x.batch x.proof
            ∧ TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl
                (beginTree (paddedSystem a b) x.missing.chain x.batch)
                (beginHeight (paddedSystem a b) x.missing.chain x.batch)
                x.proof.sibs x.proof.pathLen x.proof.index x.proof.leaf .paddingHit

/-! ## Witnesses -/

/-- **THE EXECUTED-FLOW STATEMENTS' PREMISES HOLD WITH A LIVE SLOT, A LIVE REFUND PATH AND
AGGREGATING ROOTS, AND NO BREAK.**  For every node hash, leaf hash, padding constant and
chain-tree empty constant, under `lengthFlowHash` with commit value `1`: in `mixedSystem 1`
the one-leg flow `subsetFlow 0 1` passes the execution gate on honest evidence.  In one
deployed run from fresh managers, the executed leg's slot `⟨0, 1, 0⟩` and the slot
`⟨1, 2, 1⟩` are appended, and the log's only iteration runs on chain `1` with the checked
flow `mixedFlow 1 1 2` (id `1`), writes `⟨1, 2, 1⟩`, and resolves against a root that
satisfies `Aggregates`; that slot is past `Committed`.  The executed leg's slot on chain
`0` is `Committed`, and for every chain `c` the executed leg's slot on `c` is not refunded
and carries no located break.  The iteration is on another flow id because it has to be: by
`DeployedExecutedFlowFrozenOrBreak`, a refunded slot under the executed flow's id comes with
a located break, so a break-free witness cannot refund under that id, and the "no break, not
refunded" conjuncts for the executed flow's slots hold because no iteration writes under its
id.  The `staleRoot` and `absence` break cases are exhibited at run level by
`StaleRootEndRefundOfDeliveredLegIsDeployed` and `DeployedPaddingRefundLocatesAbsenceBreak`;
the `flowIdClash` and `lastBatch` cases are not. -/
def Properties.DeployedExecutedFlowFrozenOrBreakWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ze : UInt256),
    ∃ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze))
      (ev : GateEvidence),
      Wf (mixedSystem 1)
        ∧ ExecutedViaBy h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) (subsetFlow 0 1) ev
            ⟨0, 1⟩
        ∧ DeployedRun h z0 hl (fun _ _ => 1) lengthFlowHash (mixedSystem 1) ze emptyManagers Ms
            plog alog
        ∧ plog = [⟨1, 2, 1⟩, ⟨0, 1, 0⟩] ∧ alog ≠ []
        ∧ (∀ a ∈ alog, a.chain = 1 ∧ a.flow = mixedFlow 1 1 2 ∧ a.marks = ⟨1, 2, 1⟩
            ∧ FlowIdChecked lengthFlowHash a.flow ∧ Aggregates (mixedSystem 1) a.root)
        ∧ Refunded Ms ⟨1, 2, 1⟩
        ∧ stateOf Ms ⟨0, 1, 0⟩ = .Committed
        ∧ ∀ c : Chain,
            ¬ DeployedRefundBreak h z0 hl lengthFlowHash (mixedSystem 1) ze (subsetFlow 0 1) ev
                ⟨0, 1, c⟩ alog
              ∧ ¬ Refunded Ms ⟨0, 1, c⟩

/-- **THE REFUND-SIDE STATEMENTS' PREMISES HOLD WITH A REFUNDED SLOT, AND THE OWN-TIMEOUT
DISJUNCT IS THE ONE THAT HOLDS.**  For every node hash, leaf hash, padding constant and
chain-tree empty constant, in `mixedSystem 1` with commit value `1` and the flow hash
`honestFlowHash misdeclaredFlow`: `misdeclaredFlow` is checked, and in one deployed run from
fresh managers the slot `misdeclaredObligation` carries its id and is past `Committed`, the
iteration log is nonempty and the slot occurs once in the append log, an iteration in the
log wrote it with flow `misdeclaredFlow` and timeout evidence accepted by
`DeployedTimeoutAccepted`, and no logged iteration that wrote it has a clashing flow. -/
def Properties.DeployedRefundOwnTimeoutWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ze : UInt256),
    ∃ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      FlowIdChecked (honestFlowHash misdeclaredFlow) misdeclaredFlow
        ∧ DeployedRun h z0 hl (fun _ _ => 1) (honestFlowHash misdeclaredFlow) (mixedSystem 1) ze
            emptyManagers Ms plog alog
        ∧ misdeclaredObligation.flowId = misdeclaredFlow.flowId
        ∧ Refunded Ms misdeclaredObligation
        ∧ alog ≠ [] ∧ plog.count misdeclaredObligation = 1
        ∧ (∃ a ∈ alog, a.marks = misdeclaredObligation ∧ a.flow = misdeclaredFlow
            ∧ a.missing ∈ misdeclaredFlow.legs
            ∧ DeployedTimeoutAccepted h z0 hl (fun _ _ => 1) (mixedSystem 1) a.backing
                misdeclaredFlow a.missing a.batch a.proof a.pathLen a.pathSibs a.pathLeaf)
        ∧ ¬ ∃ a ∈ alog, a.marks = misdeclaredObligation
            ∧ FlowIdClash (honestFlowHash misdeclaredFlow) misdeclaredFlow a.flow

end Contracts.RefundFaithful
