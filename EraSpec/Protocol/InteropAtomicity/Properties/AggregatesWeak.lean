import EraSpec.Protocol.InteropAtomicity.Specs.AggregatesWeak

/-!
# Properties: the timeout and refund headlines from the settlement layer's own roots

Statements about `EraSpec.Protocol.InteropAtomicity.Specs.AggregatesWeak`. Proofs are in
`EraSpec.Protocol.InteropAtomicity.Proofs.AggregatesWeak`.

## (f) The weak form suffices

`Aggregates` implies `AggregatesWeak` (`AggregatesImpliesWeak`), which is exactly strict
aggregation (`AggregatesWeakIsStrictAggregation`) and strictly weaker
(`AggregatesWeakStrictlyWeaker`). Every timeout and refund headline that took `Aggregates` holds
with `AggregatesWeak` instead, with the same conclusion and the same located breaks: the
derivation of `IsLastOnTime` (`IsLastOnTimeDerivedWeak`), the verified and as-run gates
(`VerifiedImpliesRefundableWeak`, `AcceptedImpliesRefundablePinnedWeak`,
`AcceptedImpliesRefundableOnWeak`), the timeout headlines (`TimeoutMeansMissedDeadlineOrBreakWeak`,
`TimeoutExcludesFinalityOrBreakWeak`, `AcceptedTimeoutMeansMissedDeadlineOrBreakWeak`) and the
refund ones (`VerifiedTimeoutAuthorizesWeak`, `RefundedFlowMissedDeadlineOrBreakWeak`,
`AcceptedTimeoutAuthorizesPinnedWeak`, `ExecutedExcludesAcceptedRefundOrBreakWeak`). No proof
needed the strong direction.

For the run-level capstone, `ReachLogAt` logs refunds verified against roots: every such run is a
`ReachLog` with the same log once its roots aggregate weakly (`ReachLogAtProjects`), so
`ExecutedObligationNeverRefundedOrBreak` holds for it with the same `RefundBreak`
(`ExecutedObligationNeverRefundedOrBreakAt`, `OneExecutionFreezesTheFlowOrBreakAt`).

## (i) Imported roots are historical

An L2 whose imports all passed the Executor's dependency check holds, at every key with a nonzero
timestamp, exactly a historical root of the settlement layer, keyed by the settlement layer's
chain id (`ImportedRootsAreHistorical`). So every root the timeout gate's read accepts is a
historical root created at the timestamp the gate compares, and it aggregates weakly
(`ImportedRootGateIsAggregating`).

## (j) No aggregation premise left

For a `System` clocked by a MessageRoot run under non-decreasing timestamps, every historical root
aggregates weakly (`HistoricalRootAggregatesWeak`; strictly increasing timestamps give the full
`Aggregates` for the roots as they stand, `HistoricalRootAggregatesStrictTs`), and the clock makes
`Wf` out of its tree half (`WfFromMessageRoot`). So the timeout headlines hold against any
historical root with no aggregation premise (`TimeoutMeansMissedDeadlineOrBreakFromMessageRoot`,
`TimeoutExcludesFinalityOrBreakFromMessageRoot`,
`AcceptedTimeoutMeansMissedDeadlineOrBreakFromMessageRoot`), and so do the refund headlines
(`ExecutedExcludesAcceptedRefundOrBreakFromMessageRoot`, and the run-level
`ExecutedObligationNeverRefundedOrBreakFromMessageRoot`).

## Non-vacuity

`TimeoutOrBreakWeakSatisfiable`: a verified timeout against a root that aggregates weakly but not
strongly, with no break and a non-vacuous conclusion.
`ExecutedObligationNeverRefundedOrBreakAtWitness`: a root-verified refund of another flow in the
same run as an execution, with no break.
`FromMessageRootWitness`: a MessageRoot run with equal timestamps across blocks (so `Aggregates`
fails for the historical root used), a clocked system, and a verified timeout against that root
with no break and an on-time batch. `FromMessageRootRefundWitness`: a MessageRoot run, a clocked
system, an executed flow and a refund of another flow verified against a historical root, with no
break. `ImportWitness`: an L2 storage built by an accepted import, whose entry passes the timeout
gate's read.
-/

namespace Contracts.Timeout

open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier IMTAbstract

/-! ## (f) The weak form suffices -/

/-- `Aggregates` implies `AggregatesWeak`. -/
def Properties.AggregatesImpliesWeak : Prop :=
  ∀ (S : System) (R : SlRoot), Aggregates S R → AggregatesWeak S R

/-- **WEAK AGGREGATION IS STRICT AGGREGATION.** A batch that settled strictly before the root was
created is inside it. -/
def Properties.AggregatesWeakIsStrictAggregation : Prop :=
  ∀ (S : System) (R : SlRoot),
    AggregatesWeak S R ↔ ∀ c n, S.time c n < R.created → n ≤ R.upTo c

/-- **STRICTLY WEAKER.** A root created exactly when an outside batch settled. -/
def Properties.AggregatesWeakStrictlyWeaker : Prop :=
  ∃ (S : System) (R : SlRoot), AggregatesWeak S R ∧ ¬ Aggregates S R

/-- `Properties.IsLastOnTimeDerived` from `AggregatesWeak`. -/
def Properties.IsLastOnTimeDerivedWeak : Prop :=
  ∀ (S : System) (R : SlRoot), AggregatesWeak S R → ∀ (c : Chain) (D N : ℕ),
    EndBranchVerified S R c D N → IsLastOnTime S c D N

/-- `Properties.VerifiedImpliesRefundable` from `AggregatesWeak`. -/
def Properties.VerifiedImpliesRefundableWeak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (R : SlRoot),
    AggregatesWeak S R → ∀ (F : Flow) (leg : FlowLeg),
      LegRefundableVerified h z0 hl cv S R F leg → LegRefundable h z0 hl cv S F leg

/-- `Properties.TimeoutMeansMissedDeadlineOrBreak` from `AggregatesWeak`. -/
def Properties.TimeoutMeansMissedDeadlineOrBreakWeak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (R : SlRoot), AggregatesWeak S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      LegRefundableVerifiedBy h z0 hl cv S R F leg N p →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p

/-- `Properties.TimeoutExcludesFinalityOrBreak` from `AggregatesWeak`. -/
def Properties.TimeoutExcludesFinalityOrBreakWeak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (R : SlRoot), AggregatesWeak S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      LegRefundableVerifiedBy h z0 hl cv S R F leg N p → ∀ (n : ℕ) (p' : ImtProof),
      ¬ LegFinalizedBy h z0 hl cv S F leg n p'
        ∨ InclusionBreak h z0 hl S leg.chain n p'
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p

/-- `Properties.AcceptedTimeoutMeansMissedDeadlineOrBreak` from `AggregatesWeak`. -/
def Properties.AcceptedTimeoutMeansMissedDeadlineOrBreakWeak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), AggregatesWeak S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x))

/-- `Properties.AcceptedImpliesRefundablePinned` from `AggregatesWeak`. -/
def Properties.AcceptedImpliesRefundablePinnedWeak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R), AggregatesWeak S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
        LegRefundable h z0 hl cv S F leg ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x))

/-- `Properties.AcceptedImpliesRefundableOn` from `AggregatesWeak`. -/
def Properties.AcceptedImpliesRefundableOnWeak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R), AggregatesWeak S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      EntriesNotEmpty ze (B.leaves leg.chain) →
      PairInjOn h (fun q => TreePair h ze (B.leaves leg.chain) (B.height leg.chain) q
        ∨ VerifiedPair h sibs (B.height leg.chain) N x q) →
      LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
        LegRefundable h z0 hl cv S F leg

/-- **THE WEAK FORM COVERS A ROOT THE STRONG FORM DOES NOT.** For every node hash, leaf hash and
padding constant: in `mixedSystem 1`, the root created at time 1 holding each chain's batch 0 only
aggregates weakly but not strongly (batch 1 settled exactly at time 1). Leg `⟨1, 2⟩` of
`mixedFlow 0 1 2` has a verified BEGIN-branch timeout against it at batch 1 on the honest
low-leaf proof of `setup`; that proof carries no `AbsenceBreak`; and the leg missed its deadline at
the on-time batch 0. -/
def Properties.TimeoutOrBreakWeakSatisfiable : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (S : System) (R : SlRoot) (F : Flow) (leg : FlowLeg) (N : ℕ)
      (p : ImtProof),
      Wf S ∧ AggregatesWeak S R ∧ ¬ Aggregates S R
        ∧ LegRefundableVerifiedBy h z0 hl cv S R F leg N p
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∧ S.time leg.chain 0 ≤ F.deadline
        ∧ (∀ n, S.time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))

/-! ## (i) Imported roots are historical -/

/-- **EVERY IMPORTED ROOT IS A HISTORICAL ROOT.** If every import of an L2's storage passed the
Executor's dependency check against a state of the MessageRoot run reaching `stF`, then every
entry with a nonzero timestamp is keyed by the settlement layer's chain id and is
`(root, timestamp)` of `historicalRoots[n]` at some state of that run. -/
def Properties.ImportedRootsAreHistorical : Prop :=
  ∀ (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State)
    (st : L2InteropRootStorage.State),
    L2InteropRootStorage.Reach (AcceptedInRun P r stF) L2InteropRootStorage.empty st →
    ∀ c n, (st.entries c n).ts ≠ 0 → c = P.self ∧
      ∃ (mst : MessageRoot.State) (e : MessageRoot.HistEntry), MessageRoot.Reachable P r mst
        ∧ MessageRoot.Reach P r mst stF ∧ mst.hist n = some e ∧ st.entries c n = ⟨e.root, e.ts⟩

/-- **THE ROOT THE TIMEOUT GATE READS AGGREGATES.** On such an L2, whenever the timeout path's root
read passes for `(c, n)` and deadline `D`, there is a historical root `R` of the run, created at
exactly the timestamp the gate compared (so after `D`), that aggregates weakly for every system
clocked by the run. -/
def Properties.ImportedRootGateIsAggregating : Prop :=
  ∀ (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State)
    (st : L2InteropRootStorage.State),
    L2InteropRootStorage.Reach (AcceptedInRun P r stF) L2InteropRootStorage.empty st →
    ∀ c n D, st.TimeoutRootPasses c n D →
      ∃ R, HistoricalRootOf P r stF R ∧ R.created = (st.entries c n).ts ∧ D < R.created
        ∧ ∀ S, ClockedBy S stF → AggregatesWeak S R

/-- **NON-VACUITY OF (i).** A MessageRoot run, and an L2 storage built by one import the Executor
accepts against it, whose entry passes the timeout gate's read for deadline `0`. -/
def Properties.ImportWitness : Prop :=
  ∃ (P : MessageRoot.Params) (stF : MessageRoot.State) (st : L2InteropRootStorage.State)
    (n : ℕ), MessageRoot.Reachable P .strict stF
      ∧ L2InteropRootStorage.Reach (AcceptedInRun P .strict stF) L2InteropRootStorage.empty st
      ∧ st.TimeoutRootPasses P.self n 0

/-! ## (j) No aggregation premise left -/

/-- **EVERY HISTORICAL ROOT AGGREGATES WEAKLY**, for a system clocked by the run, under either
timestamp rule. -/
def Properties.HistoricalRootAggregatesWeak : Prop :=
  ∀ (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State) (R : SlRoot)
    (S : System), HistoricalRootOf P r stF R → ClockedBy S stF → AggregatesWeak S R

/-- **…AND STRONGLY, UNDER STRICT TIMESTAMPS**, for the roots as they stand. -/
def Properties.HistoricalRootAggregatesStrictTs : Prop :=
  ∀ (P : MessageRoot.Params) (st : MessageRoot.State) (b : ℕ) (e : MessageRoot.HistEntry)
    (S : System), MessageRoot.Reachable P .strict st → st.hist b = some e → ClockedBy S st →
      Aggregates S (slRootOfEntry e)

/-- **THE CLOCK DISCHARGES `Wf.timeOrdered`.** -/
def Properties.WfFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State) (S : System),
    MessageRoot.Reachable P r stF → ClockedBy S stF → WfTrees S → Wf S

/-- **A REFUNDED LEG MISSED ITS DEADLINE, OR A LOCATED BREAK — FROM THE SETTLEMENT LAYER.**
`TimeoutMeansMissedDeadlineOrBreak` with `Wf` and `Aggregates` replaced by: the system is clocked
by a MessageRoot run, its trees are well formed, and the root is a historical root of the run. -/
def Properties.TimeoutMeansMissedDeadlineOrBreakFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State)
    (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System),
    MessageRoot.Reachable P r stF → ClockedBy S stF → WfTrees S →
    ∀ (R : SlRoot), HistoricalRootOf P r stF R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      LegRefundableVerifiedBy h z0 hl cv S R F leg N p →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p

/-- `TimeoutExcludesFinalityOrBreak`, from the settlement layer. -/
def Properties.TimeoutExcludesFinalityOrBreakFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State)
    (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System),
    MessageRoot.Reachable P r stF → ClockedBy S stF → WfTrees S →
    ∀ (R : SlRoot), HistoricalRootOf P r stF R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      LegRefundableVerifiedBy h z0 hl cv S R F leg N p → ∀ (n : ℕ) (p' : ImtProof),
      ¬ LegFinalizedBy h z0 hl cv S F leg n p'
        ∨ InclusionBreak h z0 hl S leg.chain n p'
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p

/-- `AcceptedTimeoutMeansMissedDeadlineOrBreak`, from the settlement layer. -/
def Properties.AcceptedTimeoutMeansMissedDeadlineOrBreakFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State)
    (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System),
    MessageRoot.Reachable P r stF → ClockedBy S stF → WfTrees S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), HistoricalRootOf P r stF R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x))

/-- **NON-VACUITY OF (j), WHERE `Aggregates` FAILS.** For every node hash, leaf hash and padding
constant: a MessageRoot run under non-decreasing timestamps in which chain 1 pushes batch 0 at
time 3, batch 1 at time 5, and batch 2 in the next block, again at time 5. The root of the middle
block is a historical root that does NOT satisfy `Aggregates` for the clocked system, yet leg
`⟨1, 2⟩` with deadline 4 has a verified BEGIN-branch timeout against it at batch 1, with no
`AbsenceBreak`, an on-time batch 0, and the conclusion of
`TimeoutMeansMissedDeadlineOrBreakFromMessageRoot`. -/
def Properties.FromMessageRootWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (P : MessageRoot.Params) (stF : MessageRoot.State) (S : System) (R : SlRoot)
      (cv : CommitValue) (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      MessageRoot.Reachable P .mono stF ∧ ClockedBy S stF ∧ WfTrees S
        ∧ HistoricalRootOf P .mono stF R ∧ ¬ Aggregates S R
        ∧ LegRefundableVerifiedBy h z0 hl cv S R F leg N p
        ∧ ¬ AbsenceBreak h z0 hl S F.deadline leg.chain N p
        ∧ S.time leg.chain 0 ≤ F.deadline
        ∧ (∀ n, S.time leg.chain n ≤ F.deadline →
            legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))

end Contracts.Timeout

namespace Contracts.Refund

open MerkleSpec MerkleSpec.LastLeaf MerkleSpec.Verifier IMTAbstract
open Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager

/-! ## (f) The refund side -/

/-- `Properties.VerifiedTimeoutAuthorizes` from `AggregatesWeak`. -/
def Properties.VerifiedTimeoutAuthorizesWeak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (R : SlRoot),
    AggregatesWeak S R → ∀ (F : Flow) (leg : FlowLeg), leg ∈ F.legs →
      LegRefundableVerified h z0 hl cv S R F leg → RefundAuthorized h z0 hl cv S F

/-- `Properties.RefundedFlowMissedDeadlineOrBreak` from `AggregatesWeak`. -/
def Properties.RefundedFlowMissedDeadlineOrBreakWeak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System), Wf S →
    ∀ (R : SlRoot), AggregatesWeak S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof),
      LegRefundableVerifiedBy h z0 hl cv S R F leg N p →
      (∀ n, S.time leg.chain n ≤ F.deadline →
          legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n)))
        ∨ AbsenceBreak h z0 hl S F.deadline leg.chain N p

/-- `Properties.AcceptedTimeoutAuthorizesPinned` from `AggregatesWeak`. -/
def Properties.AcceptedTimeoutAuthorizesPinnedWeak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (S : System) (ze : UInt256)
    (R : SlRoot) (B : RootBacking h ze R), AggregatesWeak S R →
    ∀ (F : Flow) (leg : FlowLeg) (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      leg ∈ F.legs → LegRefundableAcceptedBy h z0 hl cv S B F leg N p sibs x →
        RefundAuthorized h z0 hl cv S F ∨ (EndBranchAccepted B S leg.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves leg.chain) N
            ∨ PathCollision h ze (B.leaves leg.chain) sibs 0 (B.height leg.chain) N x))

/-- `Properties.ExecutedExcludesAcceptedRefundOrBreak` from `AggregatesWeak`. -/
def Properties.ExecutedExcludesAcceptedRefundOrBreakWeak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), AggregatesWeak S R →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs, ∀ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      ¬ LegRefundableAcceptedBy h z0 hl cv S B F other N p sibs x
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2
        ∨ AbsenceBreak h z0 hl S F.deadline other.chain N p
        ∨ (EndBranchAccepted B S other.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves other.chain) N
            ∨ PathCollision h ze (B.leaves other.chain) sibs 0 (B.height other.chain) N x))

/-- **A ROOT-VERIFIED RUN IS A LOGGED RUN, WITH THE SAME LOG.** When every admitted root aggregates
weakly, each root-verified `authorize` call passes `ReachLog`'s check. -/
def Properties.ReachLogAtProjects : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System)
    (roots : SlRoot → Prop), (∀ R, roots R → AggregatesWeak S R) →
    ∀ (Ms Ns : Managers) (log : List AuthCall), ReachLogAt h z0 hl cv fh S roots Ms Ns log →
      ReachLog h z0 hl cv fh S Ms Ns log

/-- **AN EXECUTED OBLIGATION IS NEVER REFUNDED, OR A LOCATED BREAK — WITH ROOT-VERIFIED REFUNDS.**
`ExecutedObligationNeverRefundedOrBreak` for runs whose refunds were verified against roots that
aggregate weakly. -/
def Properties.ExecutedObligationNeverRefundedOrBreakAt : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (roots : SlRoot → Prop), (∀ R, roots R → AggregatesWeak S R) →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (log : List AuthCall), ReachLogAt h z0 hl cv fh S roots emptyManagers Ms log →
      ¬ Refunded Ms (obligationOf F leg)
        ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log

/-- The same for every leg of the flow. -/
def Properties.OneExecutionFreezesTheFlowOrBreakAt : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    Wf S → ∀ (roots : SlRoot → Prop), (∀ R, roots R → AggregatesWeak S R) →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (log : List AuthCall), ReachLogAt h z0 hl cv fh S roots emptyManagers Ms log →
    ∀ other ∈ F.legs,
      ¬ Refunded Ms (obligationOf F other)
        ∨ RefundBreak h z0 hl fh S F ev (obligationOf F other) log

/-- **ITS PREMISES ARE SATISFIABLE WITH A LIVE, ROOT-VERIFIED REFUND.** For every node hash, leaf
hash and padding constant: in `mixedSystem 1` the one-leg flow `subsetFlow 0 1` executes on honest
evidence, while a different checked flow `mixedFlow 1 1 2` is appended and authorized for refund
with its timeout verified against `timeOneRoot` (which aggregates weakly). No `RefundBreak` is
located for the executed obligation, and it is not refunded. -/
def Properties.ExecutedObligationNeverRefundedOrBreakAtWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (cv : CommitValue) (fh : FlowHash) (S : System) (roots : SlRoot → Prop) (F : Flow)
      (ev : GateEvidence) (leg : FlowLeg) (Ms : Managers) (log : List AuthCall),
      Wf S ∧ (∀ R, roots R → AggregatesWeak S R) ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ReachLogAt h z0 hl cv fh S roots emptyManagers Ms log ∧ log ≠ []
        ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log
        ∧ ¬ Refunded Ms (obligationOf F leg)

/-! ## (j) The refund side, from the settlement layer -/

/-- `ExecutedExcludesAcceptedRefundOrBreak`, from the settlement layer: no aggregation premise. -/
def Properties.ExecutedExcludesAcceptedRefundOrBreakFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State)
    (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    MessageRoot.Reachable P r stF → ClockedBy S stF → WfTrees S →
    ∀ (ze : UInt256) (R : SlRoot) (B : RootBacking h ze R), HistoricalRootOf P r stF R →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ other ∈ F.legs, ∀ (N : ℕ) (p : ImtProof) (sibs : ℕ → UInt256) (x : UInt256),
      ¬ LegRefundableAcceptedBy h z0 hl cv S B F other N p sibs x
        ∨ InclusionBreak h z0 hl S other.chain (ev other).1 (ev other).2
        ∨ AbsenceBreak h z0 hl S F.deadline other.chain N p
        ∨ (EndBranchAccepted B S other.chain F.deadline N sibs x
          ∧ (PinnedBreak h ze (B.leaves other.chain) N
            ∨ PathCollision h ze (B.leaves other.chain) sibs 0 (B.height other.chain) N x))

/-- **THE CAPSTONE, FROM THE SETTLEMENT LAYER.** In every interleaving of the managers' calls in
which each `authorizeRefund` verified its timeout against a historical root of the MessageRoot
run, an executed obligation is never refunded, or a call in the run's log carries a located
`RefundBreak`. No `Aggregates`, no `timeOrdered`: both come from the MessageRoot. -/
def Properties.ExecutedObligationNeverRefundedOrBreakFromMessageRoot : Prop :=
  ∀ (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State)
    (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash) (S : System),
    MessageRoot.Reachable P r stF → ClockedBy S stF → WfTrees S →
    ∀ (F : Flow) (ev : GateEvidence) (leg : FlowLeg), ExecutedViaBy h z0 hl cv fh S F ev leg →
    ∀ (Ms : Managers) (log : List AuthCall),
      ReachLogAt h z0 hl cv fh S (HistoricalRootOf P r stF) emptyManagers Ms log →
      ¬ Refunded Ms (obligationOf F leg)
        ∨ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log

/-- **ITS PREMISES ARE SATISFIABLE WITH A LIVE REFUND.** For every node hash, leaf hash and padding
constant: a MessageRoot run in which chain 0 settles one batch at time 0 and chain 1 settles one
at time 0 and one at time 1; the system with `mixedSystem 1`'s trees clocked by it; the one-leg
flow `subsetFlow 0 1` executes on chain 0, while `mixedFlow 1 1 2` is appended and authorized for
refund with its timeout verified against the historical root of the second block. No
`RefundBreak` is located for the executed obligation, and it is not refunded. -/
def Properties.FromMessageRootRefundWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash),
    ∃ (P : MessageRoot.Params) (stF : MessageRoot.State) (cv : CommitValue) (fh : FlowHash)
      (S : System) (F : Flow) (ev : GateEvidence) (leg : FlowLeg) (Ms : Managers)
      (log : List AuthCall),
      MessageRoot.Reachable P .strict stF ∧ ClockedBy S stF ∧ WfTrees S
        ∧ ExecutedViaBy h z0 hl cv fh S F ev leg
        ∧ ReachLogAt h z0 hl cv fh S (HistoricalRootOf P .strict stF) emptyManagers Ms log
        ∧ log ≠ [] ∧ ¬ RefundBreak h z0 hl fh S F ev (obligationOf F leg) log
        ∧ ¬ Refunded Ms (obligationOf F leg)

end Contracts.Refund
