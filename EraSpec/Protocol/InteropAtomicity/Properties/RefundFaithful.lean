import EraSpec.Protocol.InteropAtomicity.Specs.RefundFaithful

/-!
# Properties: one outcome per obligation, with `authorizeRefund` as deployed

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.RefundFaithful`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.RefundFaithful`.

## What the old run model leaves out

`Contracts.Refund.ReachLog` writes an `authorize` step to the leg's declared chain, and
checks its END branch through `IsLastOnTime`.  Both differ from the contract, and each
difference removes real runs:

* `Properties.MisdeclaredLegRefundedOnlyInDeployedModel`: a leg committed on chain `0`
  under a flow that declares it on chain `1` is refunded on chain `0` by an
  `authorizeRefund` the contract accepts (its declared chain never committed it, so the
  timeout is honest), while no `ReachLog` run refunds it at all.  In the old model that
  obligation is stuck; in the contract its depositor gets the funds back.
* `Properties.StaleRootEndRefundOfDeliveredLegIsDeployed`: an END-branch refund the contract
  accepts against a stale settlement-layer root refunds a leg that EXECUTED, and no
  `ReachLog` run reaches it, because `IsLastOnTime` is false for every batch.  The
  deployed headline below returns exactly the `staleRoot` break on it.

So `ExecutedObligationNeverRefundedOrBreak`, `OneExecutionFreezesTheFlowOrBreak`,
`RefundImpliesOwnFlowTimeoutOrLoggedClash`, `RefundNeedsLoggedAuthorize`, and the
`FlowBinding` / `OncePerLeg` results built on the same `authorize` step, are statements
about fewer runs than the contract has.

## What holds over the deployed runs

* `Properties.DeployedExecutedFlowFrozenOrBreak`: no hash premise and no settlement-layer
  premise.  If any leg of `F` executed on gate evidence `ev`, then every obligation
  carrying `F`'s id, on EVERY chain and for every bundle hash, is never past `Committed`,
  or a logged iteration that wrote it carries a `DeployedRefundBreak`: a flow-id clash, a
  break on the gate's or the timeout's IMT proof, a collision on the END branch's
  last-batch path, or a stale settlement-layer root for the missing leg's chain.
  `Properties.DeployedExecutedObligationNeverRefundedOrBreak` and
  `Properties.DeployedOneExecutionFreezesTheFlowOrBreak` are its per-leg forms.
* `Properties.DeployedExecutedFlowFrozenOrBreakUnderHonestRoots`: with the explicit
  premise that every logged iteration's root satisfies `Timeout.Aggregates` (satisfiable:
  `Properties.DeployedExecutedFlowFrozenOrBreakWitness`), the stale-root case is gone.
* `Properties.DeployedRefundImpliesOwnAcceptedTimeoutOrLoggedClash`: a refunded obligation
  with a checked flow's id has an accepted timeout of THAT flow behind it, as the contract
  checks it, or a logged iteration's flow clashes with it.
* `Properties.DeployedRunAppendsOnce`: every logged iteration wrote an obligation that was
  appended, no obligation is appended twice, and a refunded obligation was appended exactly
  once.  This is the manager half of `AppendPath.Properties.SystemAuthorizedWereAppended` and
  `SystemRefundedWasAppendedOnce`; the tree half (the commit value is a key of the chain's
  tree) stays with `AppendPath.SysSteps`, whose `authorize` still writes the declared chain.
-/

namespace Contracts.RefundFaithful

open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree
open Contracts.Atomicity Contracts.Timeout Contracts.AtomicFlowManager Contracts.Refund

/-! ## The deployed run's bookkeeping -/

/-- **A REFUNDED OBLIGATION WAS WRITTEN BY A LOGGED, VERIFIED ITERATION.**  The deployed form
of `Contracts.Refund.Properties.RefundNeedsLoggedAuthorize`: the iteration ran on the
obligation's own chain, which need not be any declared chain of its flow. -/
def Properties.DeployedRefundNeedsLoggedIteration : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (ze : UInt256) (Ms : Managers) (plog : List Obligation)
    (alog : List (DeployedAuthCall h ze)),
    DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      ∀ (o : Obligation), Refunded Ms o →
        ∃ a ∈ alog, a.Verified h z0 hl cv fh S ∧ a.marks = o

/-- **APPENDED ONCE, AUTHORIZED ONLY AFTER APPEND.**  Over every deployed run from fresh
managers: the append log has no repeats, every logged `authorizeRefund` iteration wrote an
obligation in it, and every refunded obligation occurs in it exactly once. -/
def Properties.DeployedRunAppendsOnce : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (ze : UInt256) (Ms : Managers) (plog : List Obligation)
    (alog : List (DeployedAuthCall h ze)),
    DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      plog.Nodup ∧ (∀ a ∈ alog, a.marks ∈ plog)
        ∧ ∀ (o : Obligation), Refunded Ms o → plog.count o = 1

/-! ## The milestone over the deployed runs -/

/-- **AN EXECUTED FLOW IS FROZEN ON EVERY CHAIN, OR A LOCATED BREAK.**  No hash premise and
no settlement-layer premise.  If leg `leg` of `F` executed on gate evidence `ev`, then in
every deployed run every obligation carrying `F`'s id, on any chain and for any bundle hash,
stays at `Committed` or below, or an iteration in the run's authorize log that wrote it
carries a `DeployedRefundBreak`. -/
def Properties.DeployedExecutedFlowFrozenOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (ze : UInt256) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      ∀ (o : Obligation), o.flowId = F.flowId →
        ¬ Refunded Ms o ∨ DeployedRefundBreak h z0 hl fh S ze F ev o alog

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED, OR A LOCATED BREAK, IN A DEPLOYED RUN.**  The
deployed form of `Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreak`. -/
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
leg's bundle hash on any chain `c`, not only on the leg's declared chain. -/
def Properties.DeployedOneExecutionFreezesTheFlowOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (ze : UInt256) (F : Flow) (ev : GateEvidence) (leg : FlowLeg),
    ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      ∀ other ∈ F.legs, ∀ c : Chain,
        ¬ Refunded Ms ⟨F.flowId, other.bundleHash, c⟩
          ∨ DeployedRefundBreak h z0 hl fh S ze F ev ⟨F.flowId, other.bundleHash, c⟩ alog

/-- **WITH HONEST ROOTS, THE BREAK IS A HASH BREAK.**  The explicit settlement-layer premise:
every root a logged iteration resolved against satisfies `Timeout.Aggregates`.  Then the
iteration behind a refund of an executed flow's obligation shows a flow-id clash, a
`TreeRootBreak` on the gate's or the timeout's IMT proof, or a collision on its END-branch
last-batch path.  The premise is satisfiable with a nonempty log
(`Properties.DeployedExecutedFlowFrozenOrBreakWitness`), and it is load-bearing
(`Properties.StaleRootEndRefundOfDeliveredLegIsDeployed`). -/
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
                    ∨ (EndBranchAccepted a.backing S a.missing.chain F.deadline a.batch
                          a.pathSibs a.pathLeaf
                        ∧ (PinnedBreak h ze (a.backing.leaves a.missing.chain) a.batch
                          ∨ PathCollision h ze (a.backing.leaves a.missing.chain) a.pathSibs 0
                              (a.backing.height a.missing.chain) a.batch a.pathLeaf)))))

/-- **A REFUND OF A CHECKED FLOW'S OBLIGATION HAS THAT FLOW'S OWN ACCEPTED TIMEOUT BEHIND IT,
OR A LOGGED CLASH.**  The deployed form of
`Contracts.Refund.Properties.RefundImpliesOwnFlowTimeoutOrLoggedClash`, for any obligation
with `F`'s id on any chain: the writing iteration's flow is `F` and its timeout evidence
passes `verifyTimeoutAbsence` as run, or that flow and `F` collide on their preimages. -/
def Properties.DeployedRefundImpliesOwnAcceptedTimeoutOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (ze : UInt256) (F : Flow), FlowIdChecked fh F →
    ∀ (Ms : Managers) (plog : List Obligation) (alog : List (DeployedAuthCall h ze)),
      DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog →
      ∀ (o : Obligation), o.flowId = F.flowId → Refunded Ms o →
        (∃ a ∈ alog, a.marks = o ∧ a.flow = F ∧ a.missing ∈ F.legs
            ∧ LegRefundableAcceptedBy h z0 hl cv S a.backing F a.missing a.batch a.proof
                a.pathSibs a.pathLeaf)
          ∨ ∃ a ∈ alog, a.marks = o ∧ FlowIdClash fh F a.flow

/-! ## The transitions the old model leaves out -/

/-- **A MIS-DECLARED LEG IS REFUNDED ON ITS REAL CHAIN, IN THE DEPLOYED MODEL ONLY.**  For every
node hash, leaf hash, padding constant and chain-tree empty constant, in `mixedSystem 1`
(chain `0` commits the value `1` in batch 0, chain `1` never commits) with commit value
`1`: `misdeclaredFlow` declares bundle `2` on chain `1`, but chain `0`'s manager holds the
obligation `⟨1, 2, 0⟩`, which is not the obligation of any declared leg.  Its commit value
is a key of chain `0`'s tree and of none of chain `1`'s.  A deployed run (append on chain
`0`, then `authorizeRefund` on chain `0` with an honest BEGIN-branch timeout for the
declared leg) refunds it.  No `Contracts.Refund.ReachLog` run under the same flow hash
refunds it. -/
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

/-- **A STALE-ROOT END REFUND OF AN EXECUTED LEG IS A DEPLOYED RUN, AND NO OLD RUN.**  For every
node hash, leaf hash, padding constant and chain-tree empty constant: in
`Timeout.staleSystem 1` (every batch settles at time `0`; the value `1` is committed in batch
1), `staleFlow`'s leg executes on the honest inclusion proof at batch 1.  Against
`Timeout.staleRoot` (created after the deadline, but holding batch 0 only), the contract's END
branch accepts the honest absence proof at batch 0, so a deployed run refunds the executed
leg's obligation.  The old gate `LegRefundableBy` rejects this leg for every batch and proof,
and no `ReachLog` run refunds the obligation.  The deployed headline's break is `staleRoot`:
every logged iteration is `staleFlow`'s own, no flow-id clash, no break on either IMT proof,
no collision on the last-batch path, and its root is stale for the missing leg's chain. -/
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
            ∧ ¬ PinnedBreak h ze (a.backing.leaves a.missing.chain) a.batch
            ∧ ¬ PathCollision h ze (a.backing.leaves a.missing.chain) a.pathSibs 0
                (a.backing.height a.missing.chain) a.batch a.pathLeaf
            ∧ StaleRootFor (staleSystem 1) a.root a.missing.chain

/-! ## Anti-vacuity -/

/-- **THE HEADLINE'S PREMISES HOLD WITH A LIVE REFUND PATH, HONEST ROOTS, AND NO BREAK.**  For
every node hash, leaf hash, padding constant and chain-tree empty constant: in `mixedSystem 1`
the one-leg flow `subsetFlow 0 1` executes on honest evidence, while in the same deployed run a
different checked flow, `mixedFlow 1 1 2`, is appended and authorized for refund against
`timeOneRoot`, which aggregates honestly.  For every chain `c`, the executed leg's slot on `c`
has no break located and is not refunded. -/
def Properties.DeployedExecutedFlowFrozenOrBreakWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (ze : UInt256),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (F : Flow) (ev : GateEvidence)
      (leg : FlowLeg) (Ms : Managers) (plog : List Obligation)
      (alog : List (DeployedAuthCall h ze)),
      Wf S ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ DeployedRun h z0 hl cv fh S ze emptyManagers Ms plog alog ∧ alog ≠ []
        ∧ (∀ a ∈ alog, Aggregates S a.root)
        ∧ ∀ c : Chain,
            ¬ DeployedRefundBreak h z0 hl fh S ze F ev ⟨F.flowId, leg.bundleHash, c⟩ alog
              ∧ ¬ Refunded Ms ⟨F.flowId, leg.bundleHash, c⟩

end Contracts.RefundFaithful
