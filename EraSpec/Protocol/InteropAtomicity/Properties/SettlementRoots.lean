import EraSpec.Protocol.InteropAtomicity.Specs.SettlementRoots

/-!
# Properties: the timeout and refund headlines from the settlement layer's own roots

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.SettlementRoots`. Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.SettlementRoots`. Namespace `Contracts.SettlementRoots`.
No statement takes a hash premise. `AggregatesBefore` is
`Contracts.InteropOperational.AggregatesBefore`: a batch that settled strictly before the root was
created is inside it.

## (f) The strict form suffices

Every fixed-history timeout and refund headline below holds with `Aggregates` replaced by the
strict `AggregatesBefore`, with the same conclusion and the same located breaks: the verified
gate (`VerifiedImpliesRefundableBefore`, `VerifiedTimeoutAuthorizesBefore`), the timeout
headlines (`TimeoutMeansMissedDeadlineOrBreakBefore`, `TimeoutExcludesFinalityOrBreakBefore`), the
gate with the last-batch path as the contract runs it
(`AcceptedTimeoutMeansMissedDeadlineOrBreakBefore`, `AcceptedImpliesRefundablePinnedBefore`,
`AcceptedImpliesRefundableOnBefore`, `AcceptedTimeoutAuthorizesPinnedBefore`), and the
execution-versus-refund exclusion (`ExecutedExcludesAcceptedRefundOrBreakBefore`). Each is the
`Contracts.Timeout` / `Contracts.Refund` statement of the same name without `Before`. The END
branch's step from the strict form is
`Contracts.InteropOperational.Properties.IsLastOnTimeDerivedBefore`, and `Aggregates` implies
`AggregatesBefore` (`Contracts.InteropOperational.Properties.AggregatesImpliesAggregatesBefore`).

For runs, `ReachLogAt` logs refunds verified against roots. When every admitted root satisfies
the strict form, such a run is a `Contracts.Refund.ReachLog` run with the same log
(`ReachLogAtProjects`), so the run-level headline holds for it with the same `RefundBreak`
(`ExecutedObligationNeverRefundedOrBreakAt`, `OneExecutionFreezesTheFlowOrBreakAt`).

## (i) Imported roots are historical

On an L2 whose storage, from fresh, holds only imports that the Executor's dependency check
accepts at some reachable state of a MessageRoot run, every entry with a nonzero timestamp is keyed
by the settlement layer's chain id and is `(root, timestamp)` of a historical root of that run
(`ImportedRootsAreHistorical`). So whenever the timeout path's root read passes for a deadline `D`,
there is a historical root of the run, created at exactly the timestamp the read compared (so
after `D`), and it satisfies the strict form for every system clocked by the run
(`ImportedTimeoutRootAggregatesBefore`). Which root the END branch's last-batch proof is checked
against, at the hash level, is not tied to that root's ghost count (Specs, "Model boundaries").

## (j) No aggregation premise left

For a `System` clocked by a MessageRoot run, every historical root of the run satisfies the strict
form, under either timestamp rule (`HistoricalRootAggregatesBefore`); under strictly increasing
timestamps, every root as it stands in a reachable state satisfies the non-strict `Aggregates`
(`HistoricalRootAggregatesStrictTs`). The placeholder `upTo = 0` of a chain the root counts no leaf
of admits no END branch (`UncountedChainHasNoEndBranch`). The clock gives `Wf.timeOrdered`, so
`Wf` follows from its tree half (`WfFromMessageRoot`). The timeout headlines therefore hold
against every historical root with no aggregation premise and no `timeOrdered` premise
(`TimeoutMeansMissedDeadlineOrBreakFromMessageRoot`,
`TimeoutExcludesFinalityOrBreakFromMessageRoot`,
`AcceptedTimeoutMeansMissedDeadlineOrBreakFromMessageRoot`), and so do the refund headlines
(`ExecutedExcludesAcceptedRefundOrBreakFromMessageRoot`, and the run-level
`ExecutedObligationNeverRefundedOrBreakFromMessageRoot`). Their premises are the setting (a
reachable MessageRoot state `stF`, a system clocked by it, a historical root of the run to `stF`)
and `WfTrees`; whether a system's trees are the deployed chains' trees at the end of each pushed
batch is outside the statements (Specs, "Model boundaries").

## Witnesses

| Witness | What it shows |
|---|---|
| `SettlementRootsEndBranchWitness` | for every node hash, padding constant and leaf hash: a MessageRoot run under strictly increasing timestamps, a clocked system with `WfTrees`, and a historical root read mid-block that satisfies `AggregatesBefore` but not `Aggregates`; a leg has a verified END-branch timeout against it, at the root's last batch of the leg's chain, which settled on time; no `AbsenceBreak`, and the leg missed its deadline. It meets the premises of every verified-gate statement of (f) and (j), of `HistoricalRootAggregatesBefore` and `WfFromMessageRoot`, and, with a registered chain the root counts no leaf of, of `UncountedChainHasNoEndBranch` |
| `SettlementRootsAcceptedWitness` | the same run and root, with a `RootBacking` and the honest last-batch path under the toy hash `demoHash`: an accepted END-branch timeout with the bounded no-collision premises of `AcceptedImpliesRefundableOnBefore`; no `AbsenceBreak`, `PinnedBreak` or `PathCollision`, and the leg missed its deadline. It meets the premises of the accepted-gate statements |
| `SettlementRootsRefundRunWitness` | for every node hash, padding constant and leaf hash: a MessageRoot run, a clocked system, an executed one-leg flow, and a logged refund of another flow verified against a historical root of the run (BEGIN branch); no `RefundBreak` for the executed obligation, which is not refunded. It meets the premises of the run-level statements, of `ExecutedExcludesAcceptedRefundOrBreak…`, and of `HistoricalRootAggregatesStrictTs` |
| `SettlementRootsImportWitness` | an L2 storage built from fresh by one import the Executor's check accepts, whose entry passes the timeout read for a nonzero deadline; it meets the premises of (i) |
-/

namespace Contracts.SettlementRoots

open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.Refund Contracts.AtomicFlowManager
open Contracts.InteropOperational (AggregatesBefore)

/-! ## (f) The strict form suffices -/

/-- `Contracts.Timeout.Properties.VerifiedImpliesRefundable` with `AggregatesBefore` for
`Aggregates`: a timeout verified against `R` is a refundable leg. -/
def Properties.VerifiedImpliesRefundableBefore : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (R : SlRoot),
    AggregatesBefore S R → ∀ (F : Flow) (leg : FlowLeg),
      LegRefundableVerified h z0 hl cv S R F leg → LegRefundable h z0 hl cv S F leg

/-- `Contracts.Timeout.Properties.TimeoutMeansMissedDeadlineOrBreak` with `AggregatesBefore` for
`Aggregates`: the leg's commit value was absent from its chain's tree at every on-time batch, or
the absence proof `p` carries a located break. -/
def Properties.TimeoutMeansMissedDeadlineOrBreakBefore : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (R : SlRoot), AggregatesBefore S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      LegRefundableVerifiedBy h z0 hl cv S R F leg N p →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p

/-- `Contracts.Timeout.Properties.TimeoutExcludesFinalityOrBreak` with `AggregatesBefore` for
`Aggregates`. -/
def Properties.TimeoutExcludesFinalityOrBreakBefore : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (R : SlRoot), AggregatesBefore S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      LegRefundableVerifiedBy h z0 hl cv S R F leg N p → ∀ (n : ℕ) (p' : ImtProof),
      ¬ LegFinalizedBy h z0 hl cv S F leg n p'
        ∨ InclusionBreak h z0 hl S leg.chain n p'
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p

/-- `Contracts.Timeout.Properties.AcceptedTimeoutMeansMissedDeadlineOrBreak` with
`AggregatesBefore` for `Aggregates`. The corrections on that statement (`LastLeafFaithful`,
`LastBatchInRootOffset`) apply unchanged. -/
def Properties.AcceptedTimeoutMeansMissedDeadlineOrBreakBefore : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), AggregatesBefore S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x))

/-- `Contracts.Timeout.Properties.AcceptedImpliesRefundablePinned` with `AggregatesBefore` for
`Aggregates`. -/
def Properties.AcceptedImpliesRefundablePinnedBefore : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R), AggregatesBefore S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
        LegRefundable h z0 hl cv S F leg ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x))

/-- `Contracts.Timeout.Properties.AcceptedImpliesRefundableOn` with `AggregatesBefore` for
`Aggregates`: under the bounded no-collision premises on the instance's own pairs. -/
def Properties.AcceptedImpliesRefundableOnBefore : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R), AggregatesBefore S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      EntriesNotEmpty ze (B.leaves leg.chain) →
      PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
        ∨ VerifiedPair h sibs (B.height leg.chain) N x q) →
      LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
        LegRefundable h z0 hl cv S F leg

/-- `Contracts.Refund.Properties.VerifiedTimeoutAuthorizes` with `AggregatesBefore` for
`Aggregates`. -/
def Properties.VerifiedTimeoutAuthorizesBefore : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (R : SlRoot),
    AggregatesBefore S R → ∀ (F : Flow) (leg : FlowLeg), leg ∈ F.legs →
      LegRefundableVerified h z0 hl cv S R F leg → RefundAuthorized h z0 hl cv S F

/-- `Contracts.Refund.Properties.AcceptedTimeoutAuthorizesPinned` with `AggregatesBefore` for
`Aggregates`. -/
def Properties.AcceptedTimeoutAuthorizesPinnedBefore : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R), AggregatesBefore S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      leg ∈ F.legs → LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
        RefundAuthorized h z0 hl cv S F ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x))

/-- `Contracts.Refund.Properties.ExecutedExcludesAcceptedRefundOrBreak` with `AggregatesBefore`
for `Aggregates`: a leg of an executed flow has no accepted refund, or the execution's inclusion
proof for that leg, the refund's absence proof, or its last-batch path carries a located break. -/
def Properties.ExecutedExcludesAcceptedRefundOrBreakBefore : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), AggregatesBefore S R →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs, ∀ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      ¬ LegRefundableAcceptedBy h z0 hl cv S B F other N p sibs x
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2
        ∨ AbsenceBreak h z0 hl S F.deadline other.chain N p
        ∨ (EndBranchAccepted B S other.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves other.chain) N
            ∨ PathCollision h ze (B.leaves other.chain) sibs 0 (B.height other.chain) N x))

/-- **A ROOT-VERIFIED RUN IS A LOGGED RUN, WITH THE SAME LOG.** When every root `roots` admits
satisfies `AggregatesBefore`, every `ReachLogAt` run is a `Contracts.Refund.ReachLog` run between
the same managers, with the same log. -/
def Properties.ReachLogAtProjects : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (roots : SlRoot → Prop), (∀ R, roots R → AggregatesBefore S R) →
    ∀ (Ms Ns : Managers) (log : List AuthCall), ReachLogAt h z0 hl cv fh S roots Ms Ns log →
      ReachLog h z0 hl cv fh S Ms Ns log

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED, OR A LOCATED BREAK, WITH ROOT-VERIFIED
REFUNDS.** `Contracts.Refund.Properties.ExecutedObligationNeverRefundedOrBreak` for runs from the
empty managers whose refunds were verified against roots that satisfy `AggregatesBefore`. -/
def Properties.ExecutedObligationNeverRefundedOrBreakAt : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (roots : SlRoot → Prop), (∀ R, roots R → AggregatesBefore S R) →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (log : List AuthCall), ReachLogAt h z0 hl cv fh S roots emptyManagers Ms log →
      ¬ Refunded Ms (obligationOf F leg)
        ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log

/-- The same for every leg of the executed flow. -/
def Properties.OneExecutionFreezesTheFlowOrBreakAt : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (roots : SlRoot → Prop), (∀ R, roots R → AggregatesBefore S R) →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (log : List AuthCall), ReachLogAt h z0 hl cv fh S roots emptyManagers Ms log →
    ∀ other ∈ F.legs,
      ¬ Refunded Ms (obligationOf F other)
        ∨ RefundBreak h z0 hl fh S F ev (obligationOf F other) log

/-! ## (i) Imported roots are historical -/

/-- **EVERY IMPORTED ROOT IS A HISTORICAL ROOT.** If every import of an L2's storage, from fresh,
passed the Executor's dependency check at some reachable state of the MessageRoot run that goes on
to `stF`, then every entry with a nonzero timestamp is keyed by the settlement layer's chain id and
is `(root, timestamp)` of `historicalRoots[n]` as it stood at some reachable state of that run. -/
def Properties.ImportedRootsAreHistorical : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (st : L2InteropRootStorage.State),
    L2InteropRootStorage.Reach (AcceptedInRun P r stF) L2InteropRootStorage.empty st →
    ∀ c n, (st.entries c n).ts ≠ 0 → c = P.self ∧
      ∃ (mst : MessageRoot.Aggregation.State) (e : MessageRoot.Aggregation.HistEntry),
        MessageRoot.Aggregation.Reachable P r mst ∧ MessageRoot.Aggregation.Reach P r mst stF
          ∧ mst.hist n = some e ∧ st.entries c n = ⟨e.root, e.ts⟩

/-- **THE ROOT THE TIMEOUT READ ACCEPTS IS A HISTORICAL ROOT, AND IT AGGREGATES.** On such an L2,
whenever the timeout path's root read passes for `(c, n)` and deadline `D`, there is a historical
root `R` of the run, created at exactly the timestamp the read compared (so after `D`), that
satisfies `AggregatesBefore` for every system clocked by the run. -/
def Properties.ImportedTimeoutRootAggregatesBefore : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (st : L2InteropRootStorage.State),
    L2InteropRootStorage.Reach (AcceptedInRun P r stF) L2InteropRootStorage.empty st →
    ∀ c n D, st.TimeoutRootPasses c n D →
      ∃ R, HistoricalRootOf P r stF R ∧ R.created = (st.entries c n).ts ∧ D < R.created
        ∧ ∀ S, ClockedBy S stF → AggregatesBefore S R

/-! ## (j) No aggregation premise left -/

/-- **EVERY HISTORICAL ROOT SATISFIES THE STRICT FORM**, for a system clocked by the run, under
either timestamp rule. -/
def Properties.HistoricalRootAggregatesBefore : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (R : SlRoot) (S : System),
    HistoricalRootOf P r stF R → ClockedBy S stF → AggregatesBefore S R

/-- **…AND THE NON-STRICT FORM, UNDER STRICTLY INCREASING TIMESTAMPS**, for every root as it
stands in a reachable state, for a system clocked by that state. -/
def Properties.HistoricalRootAggregatesStrictTs : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (st : MessageRoot.Aggregation.State) (b : ℕ)
    (e : MessageRoot.Aggregation.HistEntry) (S : System),
    MessageRoot.Aggregation.Reachable P .strict st → st.hist b = some e → ClockedBy S st →
      Aggregates S (slRootOfEntry e)

/-- **A ROOT THAT COUNTS NO LEAF OF A CHAIN ADMITS NO END BRANCH FOR THAT CHAIN.**
`slRootOfEntry` gives such a chain the placeholder `upTo = 0`. On a system clocked by a later
state of the run, no END branch against that root verifies for that chain, for any deadline and
batch: the placeholder creates no END-branch timeout. -/
def Properties.UncountedChainHasNoEndBranch : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (st stF : MessageRoot.Aggregation.State) (b : ℕ) (e : MessageRoot.Aggregation.HistEntry)
    (c : Chain) (S : System) (D N : ℕ),
    MessageRoot.Aggregation.Reachable P r st → MessageRoot.Aggregation.Reach P r st stF →
      st.hist b = some e → e.count c = 0 → ClockedBy S stF →
        ¬ EndBranchVerified S (slRootOfEntry e) c D N

/-- **THE CLOCK DISCHARGES `Wf.timeOrdered`.** A system clocked by a reachable MessageRoot state is
`Wf` as soon as its trees are (`WfTrees`). -/
def Properties.WfFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (S : System),
    MessageRoot.Aggregation.Reachable P r stF → ClockedBy S stF → WfTrees S → Wf S

/-- **A REFUNDED LEG MISSED ITS DEADLINE, OR A LOCATED BREAK: FROM THE SETTLEMENT LAYER.**
`Contracts.Timeout.Properties.TimeoutMeansMissedDeadlineOrBreak` with `Wf` and `Aggregates`
replaced by: the system is clocked by a reachable MessageRoot state `stF`, its trees satisfy
`WfTrees`, and the root is a historical root of the run to `stF`. -/
def Properties.TimeoutMeansMissedDeadlineOrBreakFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (cv : CommitValue) (S : System),
    MessageRoot.Aggregation.Reachable P r stF → ClockedBy S stF → WfTrees S →
    ∀ (R : SlRoot), HistoricalRootOf P r stF R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      LegRefundableVerifiedBy h z0 hl cv S R F leg N p →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p

/-- `Contracts.Timeout.Properties.TimeoutExcludesFinalityOrBreak`, from the settlement layer, with
the premises of `TimeoutMeansMissedDeadlineOrBreakFromMessageRoot`. -/
def Properties.TimeoutExcludesFinalityOrBreakFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (cv : CommitValue) (S : System),
    MessageRoot.Aggregation.Reachable P r stF → ClockedBy S stF → WfTrees S →
    ∀ (R : SlRoot), HistoricalRootOf P r stF R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      LegRefundableVerifiedBy h z0 hl cv S R F leg N p → ∀ (n : ℕ) (p' : ImtProof),
      ¬ LegFinalizedBy h z0 hl cv S F leg n p'
        ∨ InclusionBreak h z0 hl S leg.chain n p'
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p

/-- `Contracts.Timeout.Properties.AcceptedTimeoutMeansMissedDeadlineOrBreak`, from the settlement
layer: the gate with the last-batch path, against a historical root with any `RootBacking`. The
corrections on that statement (`LastLeafFaithful`, `LastBatchInRootOffset`) apply unchanged. -/
def Properties.AcceptedTimeoutMeansMissedDeadlineOrBreakFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (cv : CommitValue) (S : System),
    MessageRoot.Aggregation.Reachable P r stF → ClockedBy S stF → WfTrees S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), HistoricalRootOf P r stF R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x))

/-- `Contracts.Refund.Properties.ExecutedExcludesAcceptedRefundOrBreak`, from the settlement
layer: no aggregation premise and no `timeOrdered` premise. -/
def Properties.ExecutedExcludesAcceptedRefundOrBreakFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (cv : CommitValue) (fh : FlowHash) (S : System),
    MessageRoot.Aggregation.Reachable P r stF → ClockedBy S stF → WfTrees S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), HistoricalRootOf P r stF R →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs, ∀ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      ¬ LegRefundableAcceptedBy h z0 hl cv S B F other N p sibs x
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2
        ∨ AbsenceBreak h z0 hl S F.deadline other.chain N p
        ∨ (EndBranchAccepted B S other.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves other.chain) N
            ∨ PathCollision h ze (B.leaves other.chain) sibs 0 (B.height other.chain) N x))

/-- **THE RUN-LEVEL HEADLINE, FROM THE SETTLEMENT LAYER.** In every interleaving of the managers'
calls from the empty managers in which each `authorizeRefund` verified its timeout against a
historical root of the MessageRoot run to `stF`, an executed obligation is not refunded, or a call
in the run's log carries a located `RefundBreak`. The system is clocked by `stF` and its trees
satisfy `WfTrees`; there is no `Aggregates` and no `timeOrdered` premise. -/
def Properties.ExecutedObligationNeverRefundedOrBreakFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (cv : CommitValue) (fh : FlowHash) (S : System),
    MessageRoot.Aggregation.Reachable P r stF → ClockedBy S stF → WfTrees S →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (log : List AuthCall),
      ReachLogAt h z0 hl cv fh S (HistoricalRootOf P r stF) emptyManagers Ms log →
      ¬ Refunded Ms (obligationOf F leg)
        ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log

/-! ## Witnesses -/

/-- **THE VERIFIED-GATE PREMISES, ON THE END BRANCH, WHERE `Aggregates` FAILS.** For every node
hash, padding constant and leaf hash: a MessageRoot run under strictly increasing timestamps, a
system clocked by its final state with `WfTrees` (hence `Wf`), and a historical root `R` of the run
read mid-block, with `AggregatesBefore` and not `Aggregates`. A leg of a flow has a verified
END-branch timeout against `R` at batch `N`: `N` is `R`'s last batch of the leg's chain, it settled
on time, and a later batch of that chain settled at `R`'s creation time. The absence proof carries
no `AbsenceBreak`, and the leg missed its deadline. The entry `R` comes from also counts no leaf of
a registered chain other than the deployment's own. -/
def Properties.SettlementRootsEndBranchWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (P : MessageRoot.Aggregation.Params) (stF : MessageRoot.Aggregation.State) (S : System)
      (R : SlRoot) (cv : CommitValue) (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      MessageRoot.Aggregation.Reachable P .strict stF ∧ ClockedBy S stF ∧ WfTrees S ∧ Wf S
        ∧ HistoricalRootOf P .strict stF R ∧ AggregatesBefore S R ∧ ¬ Aggregates S R
        ∧ leg ∈ F.legs ∧ EndBranchVerified S R leg.chain F.deadline N
        ∧ S.time leg.chain (N + 1) = R.created
        ∧ LegRefundableVerifiedBy h z0 hl cv S R F leg N p
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∧ (∀ n, S.time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∧ ∃ (st : MessageRoot.Aggregation.State) (b : ℕ) (e : MessageRoot.Aggregation.HistEntry)
            (c : Chain), MessageRoot.Aggregation.Reachable P .strict st
              ∧ MessageRoot.Aggregation.Reach P .strict st stF ∧ st.hist b = some e
              ∧ R = slRootOfEntry e ∧ c ≠ P.self ∧ st.Registered P c ∧ e.count c = 0

/-- **THE ACCEPTED-GATE PREMISES, ON THE SAME RUN.** For every padding constant and leaf hash,
with the toy node hash `demoHash` (which collides elsewhere): the run, clocked system and root of
`SettlementRootsEndBranchWitness`, a `RootBacking` of the root, and an END-branch timeout accepted
with the honest last-batch path. The bounded no-collision premises of
`AcceptedImpliesRefundableOnBefore` hold on the instance's own pairs; no `AbsenceBreak`,
`PinnedBreak` or `PathCollision` holds; and the leg missed its deadline. -/
def Properties.SettlementRootsAcceptedWitness : Prop :=
  ∀ (z0 : UInt256) (hl : LeafHash),
    ∃ (h : Hash) (P : MessageRoot.Aggregation.Params) (stF : MessageRoot.Aggregation.State)
      (S : System) (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R) (cv : CommitValue)
      (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      MessageRoot.Aggregation.Reachable P .strict stF ∧ ClockedBy S stF ∧ WfTrees S ∧ Wf S
        ∧ HistoricalRootOf P .strict stF R ∧ AggregatesBefore S R ∧ ¬ Aggregates S R
        ∧ leg ∈ F.legs ∧ LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x
        ∧ EndBranchAccepted B S leg.chain F.deadline N sibs x
        ∧ EntriesNotEmpty ze (B.leaves leg.chain)
        ∧ PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
            ∨ VerifiedPair h sibs (B.height leg.chain) N x q)
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∧ ¬ PinnedBreak h ze (B.leaves leg.chain) N
        ∧ ¬ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x
        ∧ (∀ n, S.time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))

/-- **THE RUN-LEVEL PREMISES, WITH A LIVE ROOT-VERIFIED REFUND.** For every node hash, padding
constant and leaf hash: a MessageRoot run under strictly increasing timestamps in which chains 0
and 1 each have a leaf at time 0 and chain 1 a second at time 1; the system with
`Contracts.Atomicity.mixedSystem 1`'s trees, clocked by the run. The one-leg flow
`subsetFlow 0 1` executes on chain 0, while `mixedFlow 1 1 2` is appended and authorized for refund
with its timeout verified (BEGIN branch) against the historical root `slRootOfEntry e` of the run's
current block, which has a `RootBacking`. No `RefundBreak` is located for the executed obligation,
and it is not refunded. -/
def Properties.SettlementRootsRefundRunWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (P : MessageRoot.Aggregation.Params) (stF : MessageRoot.Aggregation.State) (b : ℕ)
      (e : MessageRoot.Aggregation.HistEntry) (cv : CommitValue) (fh : FlowHash) (S : System)
      (F : Flow) (ev : GateEvidence) (leg : FlowLeg) (Ms : Managers) (log : List AuthCall),
      MessageRoot.Aggregation.Reachable P .strict stF ∧ stF.hist b = some e ∧ ClockedBy S stF
        ∧ WfTrees S ∧ Wf S ∧ HistoricalRootOf P .strict stF (slRootOfEntry e)
        ∧ Nonempty (RootBacking h 0 (slRootOfEntry e))
        ∧ (∀ R, HistoricalRootOf P .strict stF R → AggregatesBefore S R)
        ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ReachLogAt h z0 hl cv fh S (HistoricalRootOf P .strict stF) emptyManagers Ms log
        ∧ log ≠ [] ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log
        ∧ ¬ Refunded Ms (obligationOf F leg)

/-- **THE IMPORT PREMISES.** A MessageRoot run under strictly increasing timestamps, and an L2
storage built from fresh by one import that the Executor's check accepts against the run, whose
entry passes the timeout path's root read for a nonzero deadline. -/
def Properties.SettlementRootsImportWitness : Prop :=
  ∃ (P : MessageRoot.Aggregation.Params) (stF : MessageRoot.Aggregation.State)
    (st : L2InteropRootStorage.State) (n D : ℕ), MessageRoot.Aggregation.Reachable P .strict stF
      ∧ L2InteropRootStorage.Reach (AcceptedInRun P .strict stF) L2InteropRootStorage.empty st
      ∧ 0 < D ∧ st.TimeoutRootPasses P.self n D

end Contracts.SettlementRoots
