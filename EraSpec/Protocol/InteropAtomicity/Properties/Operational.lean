import EraSpec.Protocol.InteropAtomicity.Specs.Operational

/-!
# Properties: every operational run projects to a fixed history

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.Operational`.  Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.Operational`.

## What was open

`Protocol/InteropAtomicity/README.md`: "The tree side is a fixed multi-chain, multi-batch
history, and steps may cite evidence from anywhere in it. [...] An operational model (or a
projection theorem from one) is open."  Every `…OrBreak` headline of `Contracts.Atomicity`,
`Contracts.Timeout`, `Contracts.Refund`, `Contracts.FlowBinding` and `Contracts.AppendPath`
quantifies over a fixed history `S : System` and a run whose calls are checked against it.

## What is proved

Take any run of the operational model from `opGenesis` (`OpSteps`), for every node hash,
leaf hash, padding constant, commit value and flow hash, with no hash premise.

1. **Projection.**  The history the end state determines is well formed, with the source's
   heights (`OpRunHistoryWf`).  Every recorded root aggregates every batch that settled
   strictly before it (`OpRunRootsAggregateBefore`), and that strict form is all the END
   branch needs (`IsLastOnTimeDerivedBefore`).  Settled batches and recorded roots never
   change (`OpRunSettledHistoryIsFinal`), and every logged call cites settled batches only
   (`OpLoggedEvidenceIsSettled`).
2. **Embedding.**  The run's per-chain steps are a `Contracts.AppendPath.SysSteps` run, its
   manager steps and checked calls a `Contracts.FlowBinding.RunLog` run, and its
   authorizations a `Contracts.Refund.ReachLog` run, all over that history
   (`OpRunEmbedsInSysSteps`, `OpRunEmbedsInRunLog`, `OpRunEmbedsInReachLog`), and over the
   history of every later state (`OpPrefixEmbedsInLaterHistory`).
3. **Transfer.**  So the headlines hold for operational runs with no `Wf`, `Aggregates`
   or hash premise left: `OpExecutedObligationNeverRefundedOrBreak`,
   `OpOneExecutionFreezesTheFlowOrBreak`, `OpRefundImpliesOwnFlowTimeoutOrLoggedClash`,
   `OpExecutedImpliesAllFinalizableOrBreak`, `OpSiblingFinalizableNowOrBreak`,
   `OpNoneOrAllOrBreakPinned`, `OpLoggedExecutionExcludesLoggedRefundOrBreak`,
   `OpExecutedImpliesRealFlowFinalizableOrLoggedClash`,
   `OpRefundedLegMissedDeadlineOrBreak`, `OpRefundStaysDeserved`, `OpSystemOncePerLeg`,
   `OpRefundedWasAppendedOnce`.
4. **New: executions are escrowed.**  Because the history is built by the run's own
   `append`s, an executed leg was appended on its declared source chain, and stays
   `Committed` there, or a located break or a pinned collision holds
   (`OpExecutedLegWasAppendedOrBreak`, `OpExecutedLegEscrowedAndNotRefundedOrBreak`).  The
   fixed history cannot say this: it admits an execution of a leg no chain ever appended
   (`FixedHistoryAdmitsUnescrowedExecution`).
5. **New: the fate of a flow is decided by a post-deadline root.**  The source's
   COMPLETENESS claim (`AtomicInteropProof.sol:89-94`) as enabledness: once a root created
   after the deadline is recorded, a checked flow can be executed on every leg (if every
   leg is in an on-time settled batch), or refunded on every committed leg (if some leg is
   not), on the BEGIN or, for a halted chain, the END branch
   (`OpFinalizedFlowIsExecutable`, `OpTimedOutLegIsRefundable`,
   `OpFlowFateDecidedAfterRoot`); and from then on the on-time settled batches never change
   (`OpOnTimeBatchesFinalAfterRoot`).  This is enabledness, not eventual delivery: nobody
   is assumed to send the call, and presenting the honest proofs needs `PROTO-DA`.

## What `Aggregates` became

`Contracts.Timeout.Aggregates` (`PROTO-AGGREGATES`) was a premise about the settlement
layer.  In the operational model the roots are the run's own (`recordRoot`), and the
premise splits:

* the strict form `AggregatesBefore` (a batch that settled strictly before the root was
  created is inside it) is a theorem of every run, and it is what the timeout gate needs
  (`IsLastOnTimeDerivedBefore`);
* the non-strict `Aggregates` is not a theorem: a root recorded before a second settlement
  at the same timestamp misses that batch (`OpRootMayMissSameTimeBatch`).  The missed batch
  settled at the root's own creation time, so it is late for every deadline the root can
  serve (the gate needs `deadline < created`), which is why the strict form is enough.  On
  the honest run of `OpHonestRunWitness` the non-strict form holds too.

What stays assumed is the settlement layer's behaviour the steps encode: batches settle in
order with a non-decreasing clock, and a recorded root holds every batch settled so far
(`MessageRootBase.sol:76-78, 238-239, 251-252, 275-277`).

## Witnesses

| Witness | What it shows |
|---|---|
| `OpHonestRunWitness` | every premise above, on one run with an execution and a refund of another flow; every break and clash disjunct is false and every first disjunct holds |
| `OpPaddingRefundLocatesAbsenceBreak` | the padding bug as an operational run: an executed, appended leg is refunded on a forged END-branch proof; the located break is the absence proof's `paddingHit` |
| `OpRootMayMissSameTimeBatch` | the non-strict `Aggregates` fails for a recorded root, the strict form holds |
| `FixedHistoryAdmitsUnescrowedExecution` | over a fixed history, a leg executes although no chain appended it, with no break |
| `OpLivenessWitness` | the premises of both liveness results on one reachable state with a post-deadline root: one flow on the executable side, one on the refundable side |

Which witness meets which premises:

* a run from `opGenesis` with a logged execution and a logged authorization, and data
  availability: `OpHonestRunWitness` (honest access).  This covers every property whose
  premises are the run, log membership and data availability, and
  `OpRefundImpliesOwnFlowTimeoutOrLoggedClash` (its refunded obligation is a leg of a checked
  flow, and the clash disjunct is false there);
* a run split into a prefix and a nonempty continuation (`OpRunSettledHistoryIsFinal`,
  `OpPrefixEmbedsInLaterHistory`): `OpHonestRunWitness`, split at the state right after the
  execution.  `OpRefundStaysDeserved` needs the authorization in the prefix: take the whole
  run of `OpHonestRunWitness` as prefix and the empty continuation;
* a logged execution and a logged authorization claiming ONE flow id
  (`OpLoggedExecutionExcludesLoggedRefundOrBreak`): `OpPaddingRefundLocatesAbsenceBreak`,
  where its absence-break disjunct is the one that fires;
* `AggregatesBefore` together with `EndBranchVerified` (`IsLastOnTimeDerivedBefore`): the
  root and the END-branch call of `OpPaddingRefundLocatesAbsenceBreak`, with
  `OpRunRootsAggregateBefore`; `Aggregates` (`AggregatesImpliesAggregatesBefore`): the roots
  of `OpHonestRunWitness`;
* a reachable state with a recorded post-deadline root, a flow on either side, and a
  nonempty continuation (`OpFinalizedFlowIsExecutable`, `OpTimedOutLegIsRefundable`,
  `OpFlowFateDecidedAfterRoot`, `OpOnTimeBatchesFinalAfterRoot`): `OpLivenessWitness`.
-/

namespace Contracts.InteropOperational

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.Timeout Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath
open Contracts.FlowBinding

/-! ## The projection -/

/-- **THE HISTORY OF EVERY RUN IS WELL FORMED, WITH THE SOURCE'S HEIGHTS.**  For every run
from `opGenesis`, the history its end state determines (`OpState.history`) meets
`Contracts.Atomicity.Wf`: every chain starts at `setup`, consecutive batches are related by
guarded inserts, batch times are monotone, and every tree fits its height.  Its heights are
`FullMerkle._height` (`HeightsFromSource`), so `Wf.capacity` is derived. -/
def Properties.OpRunHistoryWf : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
      Wf Y.history ∧ HeightsFromSource Y.history

/-- **EVERY RECORDED ROOT AGGREGATES EVERY BATCH THAT SETTLED STRICTLY BEFORE IT.**  On every
run from `opGenesis`, every root the run recorded satisfies `AggregatesBefore` on the end
state's history.  No premise on the settlement layer: it follows from the steps. -/
def Properties.OpRunRootsAggregateBefore : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
      ∀ R ∈ Y.roots, AggregatesBefore Y.history R

/-- **SETTLED BATCHES AND RECORDED ROOTS ARE FINAL.**  Take a run from `opGenesis` to `X`
and any continuation from `X` to `Y`.  Every batch settled at `X` has, in `Y`'s history,
the tree, time and height it had in `X`'s; every root recorded at `X` is still recorded at
`Y`; no settled batch is ever unsettled.  So a check made at `X` against settled batches is
a check against the final history. -/
def Properties.OpRunSettledHistoryIsFinal : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (X Y : OpState) (logX log' : List Obligation) (clogX clog' : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis X logX clogX → OpSteps h z0 hl cv fh X Y log' clog' →
      (∀ c n, n < (X.batches c).settled →
          Y.history.tree c n = X.history.tree c n ∧ Y.history.time c n = X.history.time c n
            ∧ Y.history.height c n = X.history.height c n)
        ∧ (∀ R ∈ X.roots, R ∈ Y.roots)
        ∧ (∀ c, (X.batches c).settled ≤ (Y.batches c).settled)

/-- **EVERY LOGGED CALL CITES SETTLED BATCHES ONLY.**  On every run from `opGenesis`, the
batch each logged execution cites for each leg, and the batch each logged authorization's
absence proof is against, has settled on the cited chain.  So every `InclusionBreak` and
`AbsenceBreak` below is located on a final snapshot (`OpRunSettledHistoryIsFinal`). -/
def Properties.OpLoggedEvidenceIsSettled : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
      (∀ e, CheckedCall.execute e ∈ clog → ∀ ℓ ∈ e.flow.legs,
          (e.evidence ℓ).1 < (Y.batches ℓ.chain).settled)
        ∧ (∀ a, CheckedCall.authorize a ∈ clog → a.batch < (Y.batches a.missing.chain).settled)

/-! ## The aggregation fact -/

/-- **"LAST BATCH IN THIS ROOT" MEANS "LAST BATCH IN TIME", FROM THE STRICT FORM.**
`Contracts.Timeout.Properties.IsLastOnTimeDerived` with `Aggregates` weakened to
`AggregatesBefore`.  On any fixed history: if a root aggregates every batch that settled
strictly before it, the END branch's three checks give `IsLastOnTime`. -/
def Properties.IsLastOnTimeDerivedBefore : Prop :=
  ∀ (S : System) (R : SlRoot), AggregatesBefore S R → ∀ (c : Chain) (D N : ℕ),
    EndBranchVerified S R c D N → IsLastOnTime S c D N

/-- **THE STRICT FORM IS WEAKER.**  `Aggregates` implies `AggregatesBefore`; the converse
fails on an operational run (`OpRootMayMissSameTimeBatch`). -/
def Properties.AggregatesImpliesAggregatesBefore : Prop :=
  ∀ (S : System) (R : SlRoot), Aggregates S R → AggregatesBefore S R

/-- **COUNTERMODEL: A RECORDED ROOT NEED NOT MEET THE NON-STRICT `Aggregates`.**  For every
node hash, padding constant, leaf hash, commit value and flow hash there is a run from
`opGenesis`: record the root at time `0`, then end and settle chain `0`'s batch 1, also at
time `0`.  The root misses batch 1, which settled at its creation time, so `Aggregates`
fails for it, while `AggregatesBefore` holds.  The missed batch settled at the root's own
time, so it is late for every deadline the root can serve (the gate needs
`deadline < created`), which is why the strict form suffices. -/
def Properties.OpRootMayMissSameTimeBatch : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash),
    ∃ (Y : OpState) (log : List Obligation) (clog : List CheckedCall) (R : SlRoot),
      OpSteps h z0 hl cv fh opGenesis Y log clog ∧ R ∈ Y.roots
        ∧ AggregatesBefore Y.history R ∧ ¬ Aggregates Y.history R

/-! ## The embedding -/

/-- **THE PER-CHAIN STEPS ARE A `SysSteps` RUN OVER THE PROJECTED HISTORY.**  Every run
from `opGenesis` to `Y` is, step for step, a `Contracts.AppendPath.SysSteps` run from
`genesisAll` to `Y.chains` over the fixed history `Y.history`, with the same append log and
the run's authorizations as its authorize log.  So every result of
`Properties/OncePerLeg.lean` holds of it. -/
def Properties.OpRunEmbedsInSysSteps : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
      SysSteps h z0 hl cv fh Y.history genesisAll Y.chains log (authCalls clog)

/-- **THE MANAGER STEPS AND CHECKED CALLS ARE A `RunLog` RUN OVER THE PROJECTED HISTORY.**
The same run is a `Contracts.FlowBinding.RunLog` run from the empty managers to `Y`'s
managers over `Y.history`, with the same checked-call log.  So every result of
`Properties/FlowBinding.lean` holds of it. -/
def Properties.OpRunEmbedsInRunLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
      RunLog h z0 hl cv fh Y.history emptyManagers Y.chains.mgrs clog

/-- **THE LOGGED CALLS EMBED INTO THE FIXED-HISTORY `ReachLog`.**  The run's authorizations
are a `Contracts.Refund.ReachLog` run from the empty managers to `Y`'s managers over
`Y.history`.  So every result of `Properties/Refund.lean` holds of it. -/
def Properties.OpRunEmbedsInReachLog : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
      ReachLog h z0 hl cv fh Y.history emptyManagers Y.chains.mgrs (authCalls clog)

/-- **A PREFIX'S CALLS ARE VALID AGAINST EVERY LATER HISTORY.**  For a run from `opGenesis`
to `X` and any continuation to `Y`, the prefix's steps are a `SysSteps` and a `RunLog` run
over `Y.history`, not only over `X.history`.  Evidence is never revoked. -/
def Properties.OpPrefixEmbedsInLaterHistory : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (X Y : OpState) (logX log' : List Obligation) (clogX clog' : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis X logX clogX → OpSteps h z0 hl cv fh X Y log' clog' →
      SysSteps h z0 hl cv fh Y.history genesisAll X.chains logX (authCalls clogX)
        ∧ RunLog h z0 hl cv fh Y.history emptyManagers X.chains.mgrs clogX

/-! ## The headlines, transferred

Each has only the run as premise (and data availability where the original has it).  The
`Wf` and `Aggregates` premises of the fixed-history versions are discharged by the
projection. -/

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED, OR A LOCATED BREAK.**
`Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreak` for operational runs.
For every run from `opGenesis` and every execution `e` in its log, the executed leg's
obligation is at `Committed` or below in the end state, or an authorization in the run's own
log that marked it carries a `RefundBreak` (a `FlowIdClash` against `e.flow`, or a located
tree break on `e`'s inclusion proof for the call's missing leg or on the call's absence
proof). -/
def Properties.OpExecutedObligationNeverRefundedOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ e, CheckedCall.execute e ∈ clog →
      ¬ Refunded Y.chains.mgrs (obligationOf e.flow e.leg)
        ∨ RefundBreak h z0 hl fh Y.history e.flow e.evidence (obligationOf e.flow e.leg)
            (authCalls clog)

/-- **ONE EXECUTION FREEZES THE FLOW, OR A LOCATED BREAK.**  The same for every leg of the
executed flow. -/
def Properties.OpOneExecutionFreezesTheFlowOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ e, CheckedCall.execute e ∈ clog → ∀ other ∈ e.flow.legs,
      ¬ Refunded Y.chains.mgrs (obligationOf e.flow other)
        ∨ RefundBreak h z0 hl fh Y.history e.flow e.evidence (obligationOf e.flow other)
            (authCalls clog)

/-- **A REFUNDED OBLIGATION OF A CHECKED FLOW HAS THAT FLOW'S TIMEOUT BEHIND IT, OR A
LOGGED CLASH.**  `Contracts.Refund.Properties.RefundImpliesOwnFlowTimeoutOrLoggedClash` for
operational runs: if an obligation of a checked flow `F` is past `Committed` at the end
state, then `F` had a verified timeout against the run's history, or an authorization in
the run's log that marked that obligation presented a flow whose preimage collides with
`F`'s. -/
def Properties.OpRefundImpliesOwnFlowTimeoutOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ (F : Flow) (leg : FlowLeg), FlowIdChecked fh F → leg ∈ F.legs →
      Refunded Y.chains.mgrs (obligationOf F leg) →
        RefundAuthorized h z0 hl cv Y.history F
          ∨ ∃ a ∈ authCalls clog, obligationOf a.flow a.leg = obligationOf F leg
              ∧ FlowIdClash fh F a.flow

/-- **PARTIAL ATOMICITY, OR A LOCATED BREAK, PER LEG.**
`Contracts.Atomicity.Properties.ExecutedImpliesAllFinalizableOrBreak` for operational runs.
Premise beyond the run: prover access `A` meets data availability on the run's history.
Then every leg of every logged execution is finalizable by a presentable proof, or the
inclusion proof the execution submitted for that leg carries a located break. -/
def Properties.OpExecutedImpliesAllFinalizableOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ (A : Access), DataAvailable h z0 hl Y.history A →
    ∀ e, CheckedCall.execute e ∈ clog → ∀ other ∈ e.flow.legs,
      LegFinalizableBy h z0 hl cv Y.history A e.flow other
        ∨ InclusionBreak h z0 hl Y.history other.chain (e.evidence other).1 (e.evidence other).2

/-- **EVERY SIBLING CAN EXECUTE NOW, OR A LOCATED BREAK.**  The operational reading of
partial atomicity.  Premise beyond the run: prover access `A` meets data availability on the
run's history.  For every logged execution `e` and every leg `other` of `e.flow`, the batch
`e` cited for `other` has settled, and either a presentable proof for `other` is accepted
against that very batch (on time), so any destination can run the gate for `other` today
and at every later state (`OpRunSettledHistoryIsFinal`), or the proof `e` submitted for
`other` carries a located break. -/
def Properties.OpSiblingFinalizableNowOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ (A : Access), DataAvailable h z0 hl Y.history A →
    ∀ e, CheckedCall.execute e ∈ clog → ∀ other ∈ e.flow.legs,
      (e.evidence other).1 < (Y.batches other.chain).settled
        ∧ ((∃ p, A other.chain (e.evidence other).1 p
              ∧ LegFinalizedBy h z0 hl cv Y.history e.flow other (e.evidence other).1 p)
          ∨ InclusionBreak h z0 hl Y.history other.chain (e.evidence other).1
              (e.evidence other).2)

/-- **NONE OR ALL, OR A BREAK ON THE FIRST STRANDED LEG.**
`Contracts.Atomicity.Properties.NoneOrAllOrBreakPinned` for the executions of an operational
run, under data availability: every logged execution's flow is all finalizable, or its
evidence carries a located break on the flow's first stranded leg. -/
def Properties.OpNoneOrAllOrBreakPinned : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ (A : Access), DataAvailable h z0 hl Y.history A →
    ∀ e, CheckedCall.execute e ∈ clog →
      FlowFinalizableBy h z0 hl cv Y.history A e.flow
        ∨ PinnedGateBreak h z0 hl cv Y.history A e.flow e.evidence

/-- **A LOGGED EXECUTION AND A LOGGED REFUND OF ONE FLOW ID: A LOCATED BREAK OR A LOGGED
CLASH.**  `Contracts.FlowBinding.Properties.LoggedExecutionExcludesLoggedRefundOrBreak` for
operational runs. -/
def Properties.OpLoggedExecutionExcludesLoggedRefundOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ e, CheckedCall.execute e ∈ clog → ∀ a, CheckedCall.authorize a ∈ clog →
      a.flow.flowId = e.flow.flowId →
        InclusionBreak h z0 hl Y.history a.missing.chain (e.evidence a.missing).1
            (e.evidence a.missing).2
          ∨ AbsenceBreak h z0 hl Y.history a.flow.deadline a.missing.chain a.batch a.proof
          ∨ FlowIdClash fh e.flow a.flow

/-- **PARTIAL ATOMICITY OVER THE REAL FLOW, OR A LOCATED BREAK, OR A LOGGED CLASH.**
`Contracts.FlowBinding.Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClash` for
operational runs, under data availability. -/
def Properties.OpExecutedImpliesRealFlowFinalizableOrLoggedClash : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ (A : Access), DataAvailable h z0 hl Y.history A →
    ∀ e, CheckedCall.execute e ∈ clog → ∀ c ∈ clog, c.flow.flowId = e.flow.flowId →
      FlowFinalizableBy h z0 hl cv Y.history A c.flow
        ∨ PinnedGateBreak h z0 hl cv Y.history A e.flow e.evidence
        ∨ FlowIdClash fh e.flow c.flow

/-- **A REFUNDED LEG REALLY MISSED ITS DEADLINE, OR THE ABSENCE PROOF CARRIES A BREAK.**
`Contracts.Timeout.Properties.TimeoutMeansMissedDeadlineOrBreak` for the authorizations of
an operational run, with its `Aggregates` premise discharged: for every authorization in the
run's log, the missing leg's commit value is absent from its chain's tree at every batch of
the run's history that is on time, or the submitted absence proof carries a located break on
the root its branch selects. -/
def Properties.OpRefundedLegMissedDeadlineOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ a ∈ authCalls clog,
      (∀ n, Y.history.time a.missing.chain n ≤ a.flow.deadline →
          legValue cv a.flow a.missing ∉ keys (toAbs (Y.history.tree a.missing.chain n)))
        ∨ AbsenceBreak h z0 hl Y.history a.flow.deadline a.missing.chain a.batch a.proof

/-- **A REFUND STAYS DESERVED.**  Take a run from `opGenesis` to `X`, an authorization in its
log, and any continuation to `Y`.  At every batch of `Y`'s history that is on time —
including every batch that settled after the call — the missing leg's commit value is
absent from its chain's tree, or the call's absence proof carries a break.  The break is on
`X`'s history: it is fixed when the call is made. -/
def Properties.OpRefundStaysDeserved : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (X Y : OpState) (logX log' : List Obligation) (clogX clog' : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis X logX clogX → OpSteps h z0 hl cv fh X Y log' clog' →
    ∀ a ∈ authCalls clogX,
      (∀ n, Y.history.time a.missing.chain n ≤ a.flow.deadline →
          legValue cv a.flow a.missing ∉ keys (toAbs (Y.history.tree a.missing.chain n)))
        ∨ AbsenceBreak h z0 hl X.history a.flow.deadline a.missing.chain a.batch a.proof

/-- **ONCE PER LEG, FOR OPERATIONAL RUNS.**  `Contracts.AppendPath.Properties.SystemOncePerLeg`:
no obligation is appended twice, each appended obligation occupies exactly one index of its
chain's live tree, and two appended obligations on one chain with one commit value are the
same obligation. -/
def Properties.OpSystemOncePerLeg : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
      log.Nodup
        ∧ (∀ o ∈ log, ∃! i, i < (Y.chains o.chain).tree.leafCount
            ∧ ((Y.chains o.chain).tree.leaf i).value = commitOf cv o)
        ∧ (∀ o ∈ log, ∀ o' ∈ log, o.chain = o'.chain → commitOf cv o = commitOf cv o' → o = o')

/-- **A REFUNDED OBLIGATION WAS APPENDED EXACTLY ONCE.**
`Contracts.AppendPath.Properties.SystemRefundedWasAppendedOnce` for operational runs. -/
def Properties.OpRefundedWasAppendedOnce : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ o, Refunded Y.chains.mgrs o →
      log.count o = 1 ∧ commitOf cv o ∈ keys (toAbs (Y.chains o.chain).tree)

/-! ## New: an execution is backed by an escrow on every leg's own chain -/

/-- **AN EXECUTED LEG WAS APPENDED ON ITS DECLARED SOURCE CHAIN, OR A LOCATED BREAK.**  For
every run from `opGenesis`, every logged execution `e` and every leg `ℓ` of `e.flow`, one
of four holds:

* the leg's obligation `⟨e.flow.flowId, ℓ.bundleHash, ℓ.chain⟩` was appended on `ℓ.chain`
  (it is in the run's append log) and its manager state there is not `Unset`;
* its commit value collides with that of an obligation appended on `ℓ.chain`
  (`CommitClash`, pinned to the run's own log);
* its commit value is `0`, the tree's sentinel value, which every tree contains
  (`IndexedMerkleTree.verifyInclusion` does not reject `0`,
  `common/libraries/IndexedMerkleTree.sol:133-145`); for keccak this is a preimage of `0`;
* the inclusion proof `e` submitted for `ℓ` carries a located `TreeRootBreak`.

The center calls `append` (`interop/InteropCenter.sol:650`) in the same transaction as the
leg's source burn (`atomic-interop/README.md:30-35`), so the first disjunct says the leg's
funds were escrowed on its declared source chain.  No
fixed-history result can say this, because `S` is not tied to the trees the `append`s build
(`FixedHistoryAdmitsUnescrowedExecution`). -/
def Properties.OpExecutedLegWasAppendedOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ e, CheckedCall.execute e ∈ clog → ∀ ℓ ∈ e.flow.legs,
      (obligationOf e.flow ℓ ∈ log ∧ stateOf Y.chains.mgrs (obligationOf e.flow ℓ) ≠ .Unset)
        ∨ (∃ o ∈ log, o.chain = ℓ.chain ∧ CommitClash cv (obligationOf e.flow ℓ) o)
        ∨ legValue cv e.flow ℓ = 0
        ∨ InclusionBreak h z0 hl Y.history ℓ.chain (e.evidence ℓ).1 (e.evidence ℓ).2

/-- **CAPSTONE: EVERY LEG OF AN EXECUTED FLOW IS ESCROWED ON ITS OWN CHAIN AND NEVER
REFUNDED, OR A LOCATED BREAK.**  For every run from `opGenesis`, every logged execution `e`
and every leg `ℓ` of `e.flow`: the leg's obligation was appended on `ℓ.chain` and is
`Committed` there at the end state (escrowed, not refunded); or a `CommitClash` with an
obligation appended on `ℓ.chain`; or a zero commit value; or a located break on `e`'s
inclusion proof for `ℓ`; or a `RefundBreak` on an authorization in the run's own log that
marked that obligation.  No hash premise, no `Wf`, no `Aggregates`. -/
def Properties.OpExecutedLegEscrowedAndNotRefundedOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ e, CheckedCall.execute e ∈ clog → ∀ ℓ ∈ e.flow.legs,
      (obligationOf e.flow ℓ ∈ log ∧ stateOf Y.chains.mgrs (obligationOf e.flow ℓ) = .Committed)
        ∨ (∃ o ∈ log, o.chain = ℓ.chain ∧ CommitClash cv (obligationOf e.flow ℓ) o)
        ∨ legValue cv e.flow ℓ = 0
        ∨ InclusionBreak h z0 hl Y.history ℓ.chain (e.evidence ℓ).1 (e.evidence ℓ).2
        ∨ RefundBreak h z0 hl fh Y.history e.flow e.evidence (obligationOf e.flow ℓ)
            (authCalls clog)

/-- **COUNTERMODEL: THE FIXED HISTORY ADMITS AN EXECUTION NO CHAIN ESCROWED.**  For every
node hash, padding constant and leaf hash there is a well-formed fixed history and a
`Contracts.FlowBinding.RunLog` run from the empty managers with one logged execution, in
which every leg of the executed flow is `Unset` in every manager (no chain ever appended
it), has a nonzero commit value, and carries no inclusion break.  So
`OpExecutedLegWasAppendedOrBreak` cannot be stated over the fixed history: it needs the
operational model's tie between the history and the `append`s. -/
def Properties.FixedHistoryAdmitsUnescrowedExecution : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (Ms : Managers)
      (log : List CheckedCall) (e : ExecCall),
      Wf S ∧ RunLog h z0 hl cv fh S emptyManagers Ms log ∧ CheckedCall.execute e ∈ log
        ∧ ∀ ℓ ∈ e.flow.legs, stateOf Ms (obligationOf e.flow ℓ) = .Unset
            ∧ legValue cv e.flow ℓ ≠ 0
            ∧ ¬ InclusionBreak h z0 hl S ℓ.chain (e.evidence ℓ).1 (e.evidence ℓ).2

/-! ## Liveness: once a post-deadline root is recorded, the flow's fate is decided

The source's COMPLETENESS paragraph (`AtomicInteropProof.sol:89-94`): "if a leg has really
timed out [...] a valid timeout proof can always be produced from ANY aggregated root with
`T > deadline`".  The results below prove that, and its execution-side counterpart, as
enabledness of the operational steps: the evidence they exhibit is the honest proof
(`FullMerkle.merklePath`), so presenting it needs the chain's data (`PROTO-DA`), and the
`authorizeRefund` result also needs the marked leg to be `Committed` on its chain. -/

/-- **A FLOW EVERY LEG OF WHICH IS IN AN ON-TIME SETTLED BATCH CAN BE EXECUTED, ON ANY LEG,
NOW.**  On every run from `opGenesis` to `Y`: take a flow `F` that passes `_checkFlowId` and
in which every leg's commit value is a key of the tree of some batch of its declared chain
that has settled by the deadline.  Then for every leg `leg` of `F`,
`executeAtomicBundle`'s gate accepts an execution of `leg` at `Y` (a one-step continuation
with that call logged). -/
def Properties.OpFinalizedFlowIsExecutable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ (F : Flow), FlowIdChecked fh F →
      (∀ ℓ ∈ F.legs, ∃ n, n < (Y.batches ℓ.chain).settled
          ∧ Y.history.time ℓ.chain n ≤ F.deadline
          ∧ legValue cv F ℓ ∈ keys (toAbs (Y.history.tree ℓ.chain n))) →
      ∀ leg ∈ F.legs, ∃ e : ExecCall, e.flow = F ∧ e.leg = leg
        ∧ OpSteps h z0 hl cv fh Y Y [] [.execute e]

/-- **A TIMED-OUT LEG MAKES EVERY COMMITTED LEG OF ITS FLOW REFUNDABLE, NOW.**  On every run
from `opGenesis` to `Y`: take a flow `F` that passes `_checkFlowId`, a leg `missing` of `F`
with a nonzero commit value that is absent from the tree of every batch of its chain that
has settled by the deadline, and a recorded root `R` created after the deadline.  Then for
every leg `leg` of `F` that is `Committed` on its chain, `authorizeRefund` accepts a call
marking `leg` with `missing` as the missing leg, against `R`: on the BEGIN branch at the
first late batch inside `R` if there is one, else on the END branch at `R`'s last batch of
`missing`'s chain (a chain that halted before the deadline still gets its refund).  The
call is a one-step continuation of the run. -/
def Properties.OpTimedOutLegIsRefundable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ (F : Flow) (missing : FlowLeg) (R : SlRoot), FlowIdChecked fh F → missing ∈ F.legs →
      legValue cv F missing ≠ 0 → R ∈ Y.roots → F.deadline < R.created →
      (∀ n, n < (Y.batches missing.chain).settled → Y.history.time missing.chain n ≤ F.deadline →
          legValue cv F missing ∉ keys (toAbs (Y.history.tree missing.chain n))) →
      ∀ leg ∈ F.legs, AuthorizeGuard (Y.chains leg.chain).mgr F.flowId leg.bundleHash →
        ∃ a : AuthCall, a.flow = F ∧ a.leg = leg ∧ a.missing = missing
          ∧ OpSteps h z0 hl cv fh Y
              (Y.setChain leg.chain
                ⟨(Y.chains leg.chain).mgr.set F.flowId leg.bundleHash .Revertable,
                  (Y.chains leg.chain).tree⟩)
              [] [.authorize a]

/-- **AFTER A POST-DEADLINE ROOT, THE ON-TIME BATCHES ARE FINAL.**  Take a run from
`opGenesis` to `X` that has recorded a root `R`, a deadline `D < R.created`, and any
continuation to `Y`.  Every batch of `Y` that has settled by `D` had already settled at
`X`: a batch settled later carries a settlement time of at least `X`'s clock, which is at
least `R.created`.  With `OpRunSettledHistoryIsFinal`, the set of on-time settled batches,
their trees and their times never change again, so neither do the premises of
`OpFinalizedFlowIsExecutable` and `OpTimedOutLegIsRefundable`. -/
def Properties.OpOnTimeBatchesFinalAfterRoot : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (X Y : OpState) (logX log' : List Obligation) (clogX clog' : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis X logX clogX → OpSteps h z0 hl cv fh X Y log' clog' →
    ∀ R ∈ X.roots, ∀ (D : ℕ), D < R.created →
    ∀ (c : Chain) (n : ℕ), n < (Y.batches c).settled → Y.history.time c n ≤ D →
      n < (X.batches c).settled

/-- **THE FATE OF A FLOW IS DECIDED BY A POST-DEADLINE ROOT.**  On every run from
`opGenesis` to `Y`: take a flow `F` that passes `_checkFlowId`, whose legs have nonzero
commit values (`FlowWf`), and a recorded root created after its deadline.  Then one of two
holds:

* every leg of `F` can be executed now (`OpFinalizedFlowIsExecutable`'s conclusion);
* some leg `missing` of `F` makes every `Committed` leg of `F` refundable now
  (`OpTimedOutLegIsRefundable`'s conclusion).

By `OpOnTimeBatchesFinalAfterRoot` the case that holds never changes along any continuation
(the conclusion of each case is a statement about the state it is evaluated at).  This is
liveness as enabledness: it does not say anyone sends the call. -/
def Properties.OpFlowFateDecidedAfterRoot : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (Y : OpState) (log : List Obligation) (clog : List CheckedCall),
    OpSteps h z0 hl cv fh opGenesis Y log clog →
    ∀ (F : Flow) (R : SlRoot), FlowIdChecked fh F → FlowWf cv F → R ∈ Y.roots →
      F.deadline < R.created →
      (∀ leg ∈ F.legs, ∃ e : ExecCall, e.flow = F ∧ e.leg = leg
          ∧ OpSteps h z0 hl cv fh Y Y [] [.execute e])
        ∨ ∃ missing ∈ F.legs, ∀ leg ∈ F.legs,
            AuthorizeGuard (Y.chains leg.chain).mgr F.flowId leg.bundleHash →
              ∃ a : AuthCall, a.flow = F ∧ a.leg = leg ∧ a.missing = missing
                ∧ OpSteps h z0 hl cv fh Y
                    (Y.setChain leg.chain
                      ⟨(Y.chains leg.chain).mgr.set F.flowId leg.bundleHash .Revertable,
                        (Y.chains leg.chain).tree⟩)
                    [] [.authorize a]

/-- **THE LIVENESS PREMISES HOLD ON THE HONEST RUN, ON BOTH SIDES.**  For every node hash,
padding constant and leaf hash: the state `X` of the honest run right after the root is
recorded (and the clock has moved past it) is reachable, the root `R` it recorded was
created after deadline `0`, and

* `subsetFlow 0 1` passes `_checkFlowId`, has nonzero commit values, and its only leg's
  value is a key of an on-time settled batch of chain `0` (the premises of
  `OpFinalizedFlowIsExecutable`);
* `mixedFlow 1 1 2` passes `_checkFlowId`, has nonzero commit values, its leg `⟨1, 2⟩` is
  absent from every on-time settled batch of chain `1`, and that leg is `Committed` there
  (the premises of `OpTimedOutLegIsRefundable`);
* the run continues from `X` to the honest run's end state `Y` with a nonempty log (the
  premises of `OpOnTimeBatchesFinalAfterRoot`). -/
def Properties.OpLivenessWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (X Y : OpState) (logX log' : List Obligation)
      (clogX clog' : List CheckedCall) (R : SlRoot),
      OpSteps h z0 hl cv fh opGenesis X logX clogX ∧ OpSteps h z0 hl cv fh X Y log' clog'
        ∧ clog' ≠ [] ∧ R ∈ X.roots ∧ (0 : ℕ) < R.created
        ∧ FlowIdChecked fh (subsetFlow 0 1) ∧ FlowWf cv (subsetFlow 0 1)
        ∧ (∀ ℓ ∈ (subsetFlow 0 1).legs, ∃ n, n < (X.batches ℓ.chain).settled
            ∧ X.history.time ℓ.chain n ≤ (subsetFlow 0 1).deadline
            ∧ legValue cv (subsetFlow 0 1) ℓ ∈ keys (toAbs (X.history.tree ℓ.chain n)))
        ∧ FlowIdChecked fh (mixedFlow 1 1 2) ∧ FlowWf cv (mixedFlow 1 1 2)
        ∧ (∀ n, n < (X.batches 1).settled → X.history.time 1 n ≤ (mixedFlow 1 1 2).deadline →
            legValue cv (mixedFlow 1 1 2) ⟨1, 2⟩ ∉ keys (toAbs (X.history.tree 1 n)))
        ∧ AuthorizeGuard (X.chains 1).mgr 1 2

/-! ## Witnesses -/

/-- **AN HONEST RUN THAT USES EVERY STEP: THE PREMISES HOLD, THE BREAKS ARE FALSE.**  For
every node hash, padding constant and leaf hash there is an operational run from
`opGenesis`, split at a state `X` into two segments with nonempty checked-call logs, with an
execution `e` in the first segment and a refund authorization `a` of a flow with another id
in the second.  On it:

* the executed leg was appended, is `Committed`, clashes with no appended obligation, has a
  nonzero commit value, and carries no inclusion break and no `RefundBreak`; the executed
  flow is all finalizable under honest access, which meets data availability;
* the refunded leg was authorized on a checked flow, is `Reverted`, its absence proof
  carries no break, it really missed its deadline, and no logged call clashes with its
  flow;
* the run recorded a root, and every recorded root meets even the non-strict `Aggregates`.

So the premises of every property above hold together, with nonempty logs, and on this run
each property's first disjunct holds while its break and clash disjuncts fail. -/
def Properties.OpHonestRunWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (X Y : OpState) (logX log' : List Obligation)
      (clogX clog' : List CheckedCall) (e : ExecCall) (a : AuthCall),
      OpSteps h z0 hl cv fh opGenesis X logX clogX ∧ OpSteps h z0 hl cv fh X Y log' clog'
        ∧ OpSteps h z0 hl cv fh opGenesis Y (log' ++ logX) (clog' ++ clogX)
        ∧ CheckedCall.execute e ∈ clogX ∧ CheckedCall.authorize a ∈ clog'
        ∧ a.flow.flowId ≠ e.flow.flowId
        ∧ DataAvailable h z0 hl Y.history (honestAccess h z0 hl Y.history)
        ∧ (∀ ℓ ∈ e.flow.legs, obligationOf e.flow ℓ ∈ log' ++ logX
            ∧ stateOf Y.chains.mgrs (obligationOf e.flow ℓ) = .Committed
            ∧ (¬ ∃ o ∈ log' ++ logX, o.chain = ℓ.chain ∧ CommitClash cv (obligationOf e.flow ℓ) o)
            ∧ legValue cv e.flow ℓ ≠ 0
            ∧ ¬ InclusionBreak h z0 hl Y.history ℓ.chain (e.evidence ℓ).1 (e.evidence ℓ).2
            ∧ ¬ RefundBreak h z0 hl fh Y.history e.flow e.evidence (obligationOf e.flow ℓ)
                (authCalls (clog' ++ clogX)))
        ∧ FlowFinalizableBy h z0 hl cv Y.history (honestAccess h z0 hl Y.history) e.flow
        ∧ FlowIdChecked fh a.flow ∧ a.leg ∈ a.flow.legs
        ∧ stateOf Y.chains.mgrs (obligationOf a.flow a.leg) = .Reverted
        ∧ ¬ AbsenceBreak h z0 hl Y.history a.flow.deadline a.missing.chain a.batch a.proof
        ∧ (∀ n, Y.history.time a.missing.chain n ≤ a.flow.deadline →
            legValue cv a.flow a.missing ∉ keys (toAbs (Y.history.tree a.missing.chain n)))
        ∧ (¬ ∃ a' ∈ authCalls (clog' ++ clogX), obligationOf a'.flow a'.leg
              = obligationOf a.flow a.leg ∧ FlowIdClash fh a.flow a'.flow)
        ∧ Y.roots ≠ [] ∧ ∀ R ∈ Y.roots, Aggregates Y.history R

/-- **THE PADDING BUG AS AN OPERATIONAL RUN: THE BREAK FIRES WHERE THE BUG IS.**  With the
extraction pin's padding `z0 = hl ⟨0,0,0⟩` and `0 < a < b`: chain `0` appends two legs with
commit values `a` and `b` (its tree becomes `threeLeafTree a b`, height 2, slot 3 empty),
ends and settles that batch at time `0`; a one-leg flow whose commit value is `a` executes
on the honest inclusion proof against the settled batch; the clock moves to `1`, a root is
recorded, and the same leg is authorized for refund on the END branch (the batch is on time
and is the root's last batch) with the forged padding absence proof.  The executed, appended
leg IS refunded, so `OpExecutedObligationNeverRefundedOrBreak` must return a `RefundBreak`.
It is located correctly: the inclusion proof carries none, the flows do not clash, and the
absence proof carries a `paddingHit` on the settled snapshot.  The refund resolved against a
recorded root on the END branch (`EndBranchVerified`), so the premises of
`IsLastOnTimeDerivedBefore` hold on this run too. -/
def Properties.OpPaddingRefundLocatesAbsenceBreak : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    ∃ (cv : CommitValue) (fh : FlowHash) (Y : OpState) (log : List Obligation)
      (clog : List CheckedCall) (e : ExecCall) (r : AuthCall),
      OpSteps h (hl ⟨0, 0, 0⟩) hl cv fh opGenesis Y log clog
        ∧ CheckedCall.execute e ∈ clog ∧ CheckedCall.authorize r ∈ clog
        ∧ r.flow = e.flow ∧ r.leg = e.leg ∧ r.missing = e.leg
        ∧ (∃ R ∈ Y.roots, EndBranchVerified Y.history R r.missing.chain r.flow.deadline r.batch)
        ∧ obligationOf e.flow e.leg ∈ log
        ∧ Refunded Y.chains.mgrs (obligationOf e.flow e.leg)
        ∧ RefundBreak h (hl ⟨0, 0, 0⟩) hl fh Y.history e.flow e.evidence
            (obligationOf e.flow e.leg) (authCalls clog)
        ∧ ¬ InclusionBreak h (hl ⟨0, 0, 0⟩) hl Y.history e.leg.chain (e.evidence e.leg).1
            (e.evidence e.leg).2
        ∧ ¬ FlowIdClash fh e.flow r.flow
        ∧ AbsenceBreak h (hl ⟨0, 0, 0⟩) hl Y.history r.flow.deadline r.missing.chain r.batch
            r.proof
        ∧ Y.history.tree r.missing.chain r.batch = threeLeafTree a b
        ∧ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2 r.proof.sibs r.proof.pathLen
            r.proof.index r.proof.leaf
        ∧ (threeLeafTree a b).leafCount ≤ r.proof.index ∧ hl r.proof.leaf = hl ⟨0, 0, 0⟩

end Contracts.InteropOperational
