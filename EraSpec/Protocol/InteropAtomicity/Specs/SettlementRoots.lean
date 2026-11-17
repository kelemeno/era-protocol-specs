import EraSpec.Protocol.InteropAtomicity.Specs.Refund
import EraSpec.Protocol.InteropAtomicity.Specs.Operational
import EraSpec.Contracts.MessageRoot.Specs.Aggregation
import EraSpec.Contracts.L2InteropRootStorage.Specs.Model

/-!
# Model: the settlement layer's roots, as the roots the timeout gate resolves against

The timeout gate (`AtomicInteropProof.verifyTimeoutAbsence`) resolves against a settlement-layer
root imported into the destination's `L2InteropRootStorage`, and compares that root's timestamp
with the deadline. `Protocol/InteropAtomicity/Specs/Timeout.lean` models that root as an abstract
`Contracts.Timeout.SlRoot` and takes `Contracts.Timeout.Aggregates` as a premise
(`PROTO-AGGREGATES`). This topic ties the abstract root to the settlement layer's own roots, the
historical roots of `MessageRootBase` (`Contracts/MessageRoot`, topic `Aggregation`), and the
import to the Executor's dependency-root check.

**This file is definitions only.** The results are in
`EraSpec.Protocol.InteropAtomicity.Properties.SettlementRoots` and are proved in
`EraSpec.Protocol.InteropAtomicity.Proofs.SettlementRoots`. Namespace
`Contracts.SettlementRoots`. Source paths are relative to `l1-contracts/contracts/` at
`c67894b9`.

## 1. The strict form of aggregation is enough

`Contracts.InteropOperational.AggregatesBefore S R` (`Specs/Operational.lean`) asks only that a
batch that settled **strictly before** `R` was created is inside `R`. The END branch applies the
aggregation fact to batches after the proven one, with the root created after the deadline, so
the strict form is all it needs (`Contracts.InteropOperational.Properties.IsLastOnTimeDerivedBefore`).
This is also the argument the source states (`atomic-interop/libraries/AtomicInteropProof.sol:75-76`:
"any batch aggregated after it has `t' >= T > deadline`"). The non-strict `Aggregates` is
stronger.

## 2. Where the roots come from

* **The clock** (`ClockedBy`). A `System` is clocked by a MessageRoot state when its batch `n` of
  chain `c` is the `n`-th leaf pushed into `c`'s chain tree, with that leaf's `l1Timestamp`
  (`Contracts.MessageRoot.Aggregation.State.leafTime`). The index is the pushed POSITION, not the
  batch number: a record-only batch, a chain registered at a nonzero start, or a migration jump
  gives a batch number with no leaf (`Contracts.MessageRoot.Aggregation.Properties.RecordOnlyGap`,
  `OnboardedChainPositionsAreNotBatchNumbers`), and a batch with no leaf has no inclusion proof
  through the chain tree.
* **The roots** (`HistoricalRootOf`). A root is `historicalRoots[b]` as it stood at some reachable
  state of the MessageRoot run, mid-block or not, overwritten later or not. As an `SlRoot` it was
  created at the entry's timestamp and counts `count c` leaves of chain `c`, so its last position
  is `count c - 1` (`slRootOfEntry`). For a chain with no leaf in the root, `upTo` is the
  placeholder `0`; on a clocked system no END branch against the root verifies for that chain
  (`Properties.UncountedChainHasNoEndBranch`: its position 0 settled at or after the root).
* **The import** (`ExecutorAccepts`, `AcceptedInRun`). The root reaches the destination's
  `L2InteropRootStorage` by a bootloader import, which the settlement layer's Executor checks
  when the importing batch executes (`ExecutorFacet._verifyDependencyInteropRoots`,
  `state-transition/chain-deps/facets/Executor.sol:104-146`):

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

  The check runs in `executeBatchesSharedBridge` after that call's own batch roots are appended
  (`Executor.sol:184-190`), so it reads `historicalRoots` at some state of the settlement layer's
  run. At `draft/v0.35.0` `b17415d20` the check is the same (`Executor.sol:117-158` there).

## Model boundaries

* **Imports must be checked.** An L2's storage is covered only when every import in it is one the
  Executor accepts at some state of the MessageRoot run (`L2InteropRootStorage.Reach
  (AcceptedInRun P r stF)`). An import in an L2 batch that never executes on the settlement layer
  is not covered: the L2 can act on it, but that batch, and so whatever it authorized, does not
  settle. That settlement step is outside the model.
* **More roots than the import check sees.** `HistoricalRootOf` admits a root as it stood at any
  reachable state, including mid-block; an import checked in a later block sees only the block's
  final root. Admitting more roots only strengthens the results, and makes the strict form the
  one that holds (`Contracts.MessageRoot.Aggregation.Properties.MidBlockReadEscapesRoot`).
* **The root's content is the ghost count.** `slRootOfEntry` reads `HistEntry.count`. What the
  END branch's `_verifyLastBatchInRoot` proves against the root VALUE is modelled, as before, by
  `EndBranchVerified.lastInRoot` or by `LastBatchAccepted` over a `RootBacking`, whose leaves are
  not tied to the MessageRoot's leaves here; the corrections in `Specs/Timeout.lean`
  (`LastLeafFaithful`, `LastBatchInRootOffset`) apply unchanged.
* **The trees are a premise** (`WfTrees`, the tree half of `Wf`). For a statement over a clocked
  system to speak about the deployed chains, `S.tree c n` must be chain `c`'s commitment tree at the
  end of its `n`-th PUSHED batch. `Contracts.Atomicity.beginTree S c n` is then the END tree of the
  previous pushed batch. When a record-only batch or a migration jump lies between the two pushed
  batches, the deployed BEGIN root of the `n`-th pushed batch is a later tree: the BEGIN branch's
  relation between consecutive pushed batches is `PROTO-BATCH-SNAPSHOT` together with contiguous
  pushes (`PROTO-CONTIGUOUS-PUSH`), and it is not derived here. The END branch and the clock are
  position-indexed throughout and need neither.
* `TsRule` (non-decreasing or strictly increasing block timestamps) is a premise about the
  settlement chain, not about the contracts.
-/

namespace Contracts.SettlementRoots

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.Refund Contracts.AtomicFlowManager

/-- `Contracts.Atomicity.Wf` without `timeOrdered`: the part the source chains' commitment trees
supply. -/
structure WfTrees (S : System) : Prop where
  /-- `Wf.start`. -/
  start : ∀ c, Reaches setup (S.tree c 0)
  /-- `Wf.batch`. -/
  batch : ∀ c n, Reaches (S.tree c n) (S.tree c (n + 1))
  /-- `Wf.capacity`. -/
  capacity : ∀ c n, (S.tree c n).leafCount ≤ 2 ^ S.height c n

/-- The settlement-layer root a historical MessageRoot entry is: created at the entry's
timestamp, counting `count c` leaves of chain `c`, so last position `count c - 1` (`0` when the
root counts no leaf of `c`). -/
def slRootOfEntry (e : MessageRoot.Aggregation.HistEntry) : SlRoot where
  created := e.ts
  upTo := fun c => e.count c - 1

/-- **THE SYSTEM'S CLOCK IS THE SETTLEMENT LAYER'S.** Batch `n` of chain `c` is the `n`-th leaf
pushed into `c`'s chain tree, settled at its `l1Timestamp`; a position not yet pushed settles
after every timestamp so far (`State.leafTime`). -/
def ClockedBy (S : System) (st : MessageRoot.Aggregation.State) : Prop := S.time = st.leafTime

/-- **A HISTORICAL ROOT OF THE RUN.** `R` is `historicalRoots[b]` as it stood at some reachable
state `st` of the MessageRoot run that goes on to `stF`: mid-block or not, overwritten later or
not. -/
def HistoricalRootOf (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (R : SlRoot) : Prop :=
  ∃ (st : MessageRoot.Aggregation.State) (b : ℕ) (e : MessageRoot.Aggregation.HistEntry),
    MessageRoot.Aggregation.Reachable P r st ∧ MessageRoot.Aggregation.Reach P r st stF
      ∧ st.hist b = some e ∧ R = slRootOfEntry e

/-- **THE EXECUTOR'S DEPENDENCY-ROOT CHECK** (`Executor.sol:110-134`) accepts the imported tuple
`x` against the settlement layer's MessageRoot in state `st`. -/
def ExecutorAccepts (P : MessageRoot.Aggregation.Params) (st : MessageRoot.Aggregation.State)
    (x : L2InteropRootStorage.RootIn) : Prop :=
  x.chainId = P.self ∧ ∃ e, st.hist x.blockOrBatchNumber = some e ∧ e.root ≠ 0
    ∧ x.sides = [e.root] ∧ x.ts = e.ts

/-- The check accepts `x` at some reachable state of the run that goes on to `stF`. -/
def AcceptedInRun (P : MessageRoot.Aggregation.Params) (r : MessageRoot.Aggregation.TsRule)
    (stF : MessageRoot.Aggregation.State) (x : L2InteropRootStorage.RootIn) : Prop :=
  ∃ st, MessageRoot.Aggregation.Reachable P r st ∧ MessageRoot.Aggregation.Reach P r st stF
    ∧ ExecutorAccepts P st x

/-! ## Refunds verified against a root -/

/-- The checks `authorizeRefund` runs for the logged call `a`, with the timeout verified the way
`verifyTimeoutAbsence` verifies it: the three comparisons against the root `R`
(`LegRefundableVerifiedBy`), instead of `Contracts.Refund.AuthCall.Verified`'s
`LegRefundableBy` with its `IsLastOnTime`. -/
def AuthVerifiedAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (S : System) (R : SlRoot) (a : AuthCall) : Prop :=
  FlowIdChecked fh a.flow ∧ a.leg ∈ a.flow.legs ∧ a.missing ∈ a.flow.legs
    ∧ LegRefundableVerifiedBy h z0 hl cv S R a.flow a.missing a.batch a.proof

/-- **THE RUN WITH ROOT-VERIFIED REFUNDS.** `Contracts.Refund.ReachLog`, except that each
`authorize` call verified its timeout against a root `R` that `roots` admits. -/
inductive ReachLogAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (roots : SlRoot → Prop) :
    Managers → Managers → List AuthCall → Prop
  | refl {Ms} : ReachLogAt h z0 hl cv fh S roots Ms Ms []
  | append {Ms Ns log c f b} : ReachLogAt h z0 hl cv fh S roots Ms Ns log →
      AppendGuard (Ns c) f b →
      ReachLogAt h z0 hl cv fh S roots Ms (setAt Ns c ((Ns c).set f b .Committed)) log
  | authorize {Ms Ns log} (a : AuthCall) (R : SlRoot) :
      ReachLogAt h z0 hl cv fh S roots Ms Ns log → roots R →
      AuthVerifiedAt h z0 hl cv fh S R a →
      AuthorizeGuard (Ns a.leg.chain) a.flow.flowId a.leg.bundleHash →
      ReachLogAt h z0 hl cv fh S roots Ms
        (setAt Ns a.leg.chain ((Ns a.leg.chain).set a.flow.flowId a.leg.bundleHash .Revertable))
        (a :: log)
  | claim {Ms Ns log c f b} : ReachLogAt h z0 hl cv fh S roots Ms Ns log →
      ClaimGuard (Ns c) f b →
      ReachLogAt h z0 hl cv fh S roots Ms (setAt Ns c ((Ns c).set f b .Reverted)) log

end Contracts.SettlementRoots
