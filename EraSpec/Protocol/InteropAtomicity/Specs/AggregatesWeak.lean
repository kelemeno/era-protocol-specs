import EraSpec.Protocol.InteropAtomicity.Specs.Refund
import EraSpec.Contracts.MessageRoot.Specs.Aggregation
import EraSpec.Contracts.L2InteropRootStorage.Specs.Model

/-!
# Model: weak aggregation, and the settlement layer that supplies it

`Contracts.Timeout.Aggregates S R` — "a batch that had settled by the time root `R` was created is
inside `R`" — is the premise behind every timeout and refund headline
(`Protocol/InteropAtomicity/Specs/Timeout.lean`, `PROTO-AGGREGATES`). This file replaces it in two
steps.

**This file is definitions only.** The results are in
`EraSpec.Protocol.InteropAtomicity.Properties.AggregatesWeak` and are proved in
`EraSpec.Protocol.InteropAtomicity.Proofs.AggregatesWeak`.

## 1. The weak form is all the safety argument uses

`AggregatesWeak S R` only asks that a batch past the root's last batch settled **no earlier**
than the root was created; equivalently, a batch that settled **strictly before** the root was
created is inside it. Every use of `Aggregates` in the timeout derivation
(`Proofs/Timeout.lean`, `isLastOnTime_of_verified`) applies it to a batch with
`time ≤ D < created`, so the strict premise is enough. This is also the argument the source states
(`AtomicInteropProof.sol:84-87`: "the last batch `L'` of any root with `T > deadline >= t_B` (that
root already contains `B`)").

## 2. The settlement layer supplies the weak form

The settlement layer is `MessageRootBase` (`Contracts/MessageRoot/Specs/Aggregation.lean`).

* **The clock.** A `System` is *clocked by* a MessageRoot state when its batch `n` of chain `c` is
  the `n`-th leaf pushed into `c`'s chain tree, with that leaf's `l1Timestamp` (`ClockedBy`).
  Batches are pushed positions, not batch numbers: a record-only batch, a chain onboarded at a
  nonzero start, or a migration jump has a batch number with no leaf
  (`Contracts.MessageRoot.Properties.RecordOnlyGap`,
  `OnboardedChainPositionsAreNotBatchNumbers`).
* **The roots.** The root the timeout path resolves against is a historical root
  `historicalRoots[b]`, as it stood at some point of the run — possibly mid-block
  (`HistoricalRootOf`). As a `SlRoot` it was created at the entry's timestamp and holds
  `count c` leaves of chain `c`, so its last leaf index is `count c - 1` (`slRootOfEntry`). For a
  chain with no leaf in the root this `upTo` is the placeholder `0`; `AggregatesWeak` still holds
  for it, since every leaf of such a chain settled at or after the root.
* **The import.** The root reaches the destination chain's `L2InteropRootStorage` by a bootloader
  import, which the settlement layer's Executor checks when the importing batch executes
  (`ExecutorFacet._verifyDependencyInteropRoots`, `Executor.sol:104-146`, quoted below). An import
  the check accepts is `ExecutorAccepts`.

      if (interopRoot.chainId == block.chainid) {                                   // :114
          StoredInteropRoot memory recordedRoot = messageRootContract.historicalRoot(
              uint256(interopRoot.blockOrBatchNumber));                             // :118-120
          correctRootHash = recordedRoot.root; correctTimestamp = recordedRoot.timestamp;
      } else { revert CommitBasedInteropNotSupported(); }                           // :123-125
      if (correctRootHash == bytes32(0)) revert MessageRootIsZero();                // :126-128
      if (interopRoot.sides.length != 1 || interopRoot.sides[0] != correctRootHash)
          revert InvalidMessageRoot(...);                                           // :129-131
      if (interopRoot.timestamp != correctTimestamp)
          revert InvalidInteropRootTimestamp(...);                                  // :132-134

  The check runs during `executeBatchesSharedBridge`, after the batches' own roots are appended
  (`Executor.sol:184-190`), so it reads `historicalRoots` at a point of the settlement layer's run.

## What is premise and what is model boundary

* `TsRule.mono` (non-decreasing block timestamps) is the timestamp premise; it is a property of the
  settlement chain, not of the contracts.
* **Imports must be checked.** An L2's storage is only covered when every import it holds is one
  the Executor accepts (`L2InteropRootStorage.Reach (AcceptedInRun P r stF)`). Imports of an L2
  batch that never executes on the settlement layer are not: a refund authorized against such a
  root lives in a batch that cannot settle either. That settlement step is outside the model.
* **The begin tree.** The `System`'s `beginTree S c (n + 1)` is the end tree of the previous
  *pushed* batch. With a record-only batch or a migration gap between two pushed batches the real
  begin root is a later tree; relating the two (begin ⊇ previous end) is backlog W-INT-2.
* **The trees.** `WfTrees` (the tree half of `Wf`) stays a premise: it is the source chain's
  commitment tree, not the settlement layer.
-/

namespace Contracts.Timeout

open Contracts.InteropCommitmentTree Contracts.Atomicity

/-- **WEAK AGGREGATION.** A batch past the root's last batch settled no earlier than the root was
created. -/
def AggregatesWeak (S : System) (R : SlRoot) : Prop :=
  ∀ c n, R.upTo c < n → R.created ≤ S.time c n

/-- `Wf` without `timeOrdered`: the part the source chain's commitment tree supplies. -/
structure WfTrees (S : System) : Prop where
  /-- `Wf.start`. -/
  start : ∀ c, Reaches setup (S.tree c 0)
  /-- `Wf.batch`. -/
  batch : ∀ c n, Reaches (S.tree c n) (S.tree c (n + 1))
  /-- `Wf.capacity`. -/
  capacity : ∀ c n, (S.tree c n).leafCount ≤ 2 ^ S.height c n

/-- The settlement-layer root a historical MessageRoot entry is: created at the entry's timestamp,
with `count c` leaves of chain `c`, so last leaf index `count c - 1`. -/
def slRootOfEntry (e : MessageRoot.HistEntry) : SlRoot where
  created := e.ts
  upTo := fun c => e.count c - 1

/-- **THE SYSTEM'S CLOCK IS THE SETTLEMENT LAYER'S.** Batch `n` of chain `c` is the `n`-th leaf
pushed into `c`'s chain tree, settled at its `l1Timestamp`. -/
def ClockedBy (S : System) (st : MessageRoot.State) : Prop := S.time = st.leafTime

/-- **A HISTORICAL ROOT OF THE RUN.** `R` is `historicalRoots[b]` as it stood at some state `st` of
the MessageRoot run that goes on to `stF` — mid-block or not, overwritten later or not. -/
def HistoricalRootOf (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State)
    (R : SlRoot) : Prop :=
  ∃ (st : MessageRoot.State) (b : ℕ) (e : MessageRoot.HistEntry),
    MessageRoot.Reachable P r st ∧ MessageRoot.Reach P r st stF ∧ st.hist b = some e
      ∧ R = slRootOfEntry e

/-- **THE EXECUTOR'S DEPENDENCY-ROOT CHECK** (`Executor.sol:110-134`) accepts the imported tuple
`x` against the settlement layer's MessageRoot in state `st`. -/
def ExecutorAccepts (P : MessageRoot.Params) (st : MessageRoot.State)
    (x : L2InteropRootStorage.RootIn) : Prop :=
  x.chainId = P.self ∧ ∃ e, st.hist x.blockOrBatchNumber = some e ∧ e.root ≠ 0
    ∧ x.sides = [e.root] ∧ x.ts = e.ts

/-- The check accepts `x` at some state of the run that goes on to `stF`. -/
def AcceptedInRun (P : MessageRoot.Params) (r : MessageRoot.TsRule) (stF : MessageRoot.State)
    (x : L2InteropRootStorage.RootIn) : Prop :=
  ∃ st, MessageRoot.Reachable P r st ∧ MessageRoot.Reach P r st stF ∧ ExecutorAccepts P st x

end Contracts.Timeout

namespace Contracts.Refund

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager

/-! ## Refunds verified against a root -/

/-- The checks `authorizeRefund` runs, with the timeout verified the way `verifyTimeoutAbsence`
verifies it: the three comparisons against the imported root `R` (`LegRefundableVerifiedBy`), not
the looser `LegRefundableBy` with its unexplained `IsLastOnTime`. -/
def AuthCall.VerifiedAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (R : SlRoot) (a : AuthCall) : Prop :=
  FlowIdChecked fh a.flow ∧ a.leg ∈ a.flow.legs ∧ a.missing ∈ a.flow.legs
    ∧ LegRefundableVerifiedBy h z0 hl cv S R a.flow a.missing a.batch a.proof

/-- **THE RUN WITH ROOT-VERIFIED REFUNDS.** `ReachLog`, except that each `authorize` call verified
its timeout against a root `R` that `roots` admits. -/
inductive ReachLogAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (roots : SlRoot → Prop) :
    Managers → Managers → List AuthCall → Prop
  | refl {Ms} : ReachLogAt h z0 hl cv fh S roots Ms Ms []
  | append {Ms Ns log c f b} : ReachLogAt h z0 hl cv fh S roots Ms Ns log →
      AppendGuard (Ns c) f b →
      ReachLogAt h z0 hl cv fh S roots Ms (setAt Ns c ((Ns c).set f b .Committed)) log
  | authorize {Ms Ns log} (a : AuthCall) (R : SlRoot) :
      ReachLogAt h z0 hl cv fh S roots Ms Ns log → roots R →
      a.VerifiedAt h z0 hl cv fh S R →
      AuthorizeGuard (Ns a.leg.chain) a.flow.flowId a.leg.bundleHash →
      ReachLogAt h z0 hl cv fh S roots Ms
        (setAt Ns a.leg.chain ((Ns a.leg.chain).set a.flow.flowId a.leg.bundleHash .Revertable))
        (a :: log)
  | claim {Ms Ns log c f b} : ReachLogAt h z0 hl cv fh S roots Ms Ns log →
      ClaimGuard (Ns c) f b →
      ReachLogAt h z0 hl cv fh S roots Ms (setAt Ns c ((Ns c).set f b .Reverted)) log

end Contracts.Refund
