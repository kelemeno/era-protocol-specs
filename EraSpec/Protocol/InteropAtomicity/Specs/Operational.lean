import EraSpec.Protocol.InteropAtomicity.Specs.OncePerLeg
import EraSpec.Protocol.InteropAtomicity.Specs.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Specs.SourceHeight

/-!
# Model: the operational system, where evidence can only cite settled batches

Every result of `Contracts.Atomicity`, `Contracts.Timeout`, `Contracts.Refund`,
`Contracts.FlowBinding` and `Contracts.AppendPath` (`SysSteps`) checks its evidence against
a FIXED history `S : System`, given up front.  A call may cite any batch of it, including
batches that had not been produced when the call was made, and `S` is not tied to the live
trees the `append` calls build.  This file is the operational model those results are meant
to describe: one global interleaving of every chain's calls and of the settlement layer's
steps, in which the history is produced by the run itself and a call can cite only a batch
that has already settled.  `Contracts.InteropOperational.Properties` proves that every run
of it projects to a fixed history (`OpState.history`) over which its logged calls are a
`SysSteps`, `RunLog` and `ReachLog` run, so the `…OrBreak` headlines transfer.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.Operational`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.Operational`.

Source paths are relative to `l1-contracts/contracts/` in the pinned era-contracts tree
(`c67894b9`).

## The steps, and the source they model

Per chain (`Contracts.AppendPath.ChainState`: the manager's `_state` and the commitment
tree's list state), exactly the steps of `Contracts.AppendPath.SysSteps`:

* `append` — `AtomicFlowManager.append` (`atomic-interop/AtomicFlowManager.sol:87-102`) with
  the tree's whole `insert` flow (`atomic-interop/L2InteropCommitmentTree.sol:53-59`,
  `common/libraries/IndexedMerkleTree.sol:60-106`): `Contracts.AppendPath.AppendSucceeds`.
* `authorize` — `authorizeRefund` (`AtomicFlowManager.sol:134-162`), one leg per step.
* `claim` — `claimRefund` (`AtomicFlowManager.sol:165-180`).
* `initL2` — `L2InteropCommitmentTree.initL2` (`:47-50`); it never fires after genesis.

Per destination, the gate:

* `execute` — `L2InteropHandler.executeAtomicBundle`
  (`interop/interop-handler/L2InteropHandler.sol:49-100`), which calls
  `requireFlowFinalized` (`AtomicFlowManager.sol:105-131`) at `:83`.  It writes no modelled
  state and is logged, as in `Contracts.FlowBinding.RunLog`.

The batch and settlement-layer side, which the fixed history took as given:

* `endBatch c` — the end of chain `c`'s current batch on L2.  The bootloader reads the
  tree's root at every batch boundary and commits both snapshots into the batch's chain
  batch root (leaf 2 = begin, leaf 3 = end: `common/libraries/ChainBatchRootTree.sol:10-16,
  22-25`; `atomic-interop/libraries/AtomicInteropProof.sol:30-37`).  The model records the
  live tree as the batch's END snapshot.  The next batch's BEGIN snapshot is this one
  (`AtomicInteropProof.sol:69`: `begin(N) == end(N-1)`), which is `Contracts.Atomicity.beginTree`.
* `settle c` — the settlement of chain `c`'s oldest ended, unsettled batch:
  `MessageRootBase.addChainBatchRootV32` (`core/message-root/MessageRootBase.sol:217-224`)
  accepts only the next batch number (`:238-239`) and stamps it with
  `l1Timestamp = block.timestamp` (`:251-252`), the `l1BatchTimestamp` the gate compares to
  the deadline (`AtomicInteropProof.sol:41-47`).
* `tick t` — the settlement layer's clock (`block.timestamp` of L1; interop is L1-only in
  this release, `AtomicFlowManager.sol:232-240`) moves to `t ≥ now`.
* `recordRoot` — `_recordHistoricalRoot` (`MessageRootBase.sol:273-277`): the shared root
  at time `now`, holding every chain's settled batches (`:76-78`: each new root
  cumulatively aggregates all prior changes), becomes importable as
  `interopRoots[slChainId][slBlock]` with creation time `now`
  (`AtomicInteropProof.sol:48-52, 171-179`).

## What a call may cite

* An inclusion proof is authenticated against an imported settlement-layer root
  (`AtomicInteropProof._authenticateRoot`, `:256-290`; the verifier "only holds [the root]
  once the source batch has settled", `:36-37`).  So `execute` may cite, for each leg, only
  a SETTLED batch of the leg's declared chain (`OpExecChecks.settled`), and is checked
  against that batch's END snapshot and settlement time.  The contract also needs the batch
  to lie inside a root the destination has imported; asking only that it has settled admits
  more evidence, not less.
* `authorizeRefund` resolves against a root `R` that has been recorded
  (`OpAuthChecks.rootImported`), cites a settled batch, and passes
  `Contracts.Timeout.LegRefundableVerifiedBy` against `R`: on the BEGIN branch the root
  post-dates the deadline and the batch is late; on the END branch the root post-dates the
  deadline, the batch is on time, and it is `R`'s last batch of that chain
  (`AtomicInteropProof.sol:152-206`).  On the BEGIN branch the contract also needs the
  batch to lie inside `R`; the model asks only that it has settled, which again admits
  more.

## Model boundaries

* **Authentication is by its documented meaning.**  `_authenticateRoot` /
  `proveL2LeafInclusionShared` is modelled as: the proven IMT root is the root of the cited
  settled batch's snapshot at the tree's own height.  That the settlement proof really
  authenticates that snapshot is `PROTO-EVIDENCE` and the stored-root obligation O7; the
  root is the pure fold (`Contracts.InteropCommitmentTree.root`) at `fmHeight` of the leaf
  count, which is the source's `FullMerkle._height` (`Contracts.Atomicity.HeightsFromSource`).
* **`_verifyLastBatchInRoot` is modelled by its conclusion** `N = R.upTo c`
  (`EndBranchVerified.lastInRoot`).  The path form reduces to it, or to a pinned collision on
  the submitted path (`Contracts.Timeout.Properties.EndBranchAcceptedImpliesVerifiedPinned`).
* **Every chain id is registered at genesis**, with its genesis batch 0 (the freshly seeded
  tree) settled at time 0.  That is `MessageRoot.seedGenesisRoot` (`MessageRootBase.sol:
  364-387`) with `ChainBatchRootTree.genesisChainBatchRoot` (`ChainBatchRootTree.sol:57-65`),
  and the README's timeout precondition 1 (`atomic-interop/README.md:77-93`).  Chains
  registered later, or onboarded at a nonzero batch, are not modelled.  A chain that never
  registers can only be cited at batch 0, whose tree is `setup`; the contract would reject
  every proof for it, so the model admits more evidence, not less.
* **Every chain imports every recorded root at once**, and a root may be recorded at any
  moment, also between two settlements at one timestamp.  The contract imports roots later,
  per chain, and only a block's final root survives the import double check
  (`MessageRootBase.sol:71-79`).  Both choices admit more evidence, not less.
* **Omitted reject-only checks**: the handler's pause, destination, execution-address and
  `bundleStatus` replay checks (`L2InteropHandler.sol:50-79`), `_checkSettlementLayerIsL1`
  (`AtomicFlowManager.sol:111, 136`), `_checkFlowId`'s sortedness and length checks
  (`:248-254`; `FlowIdChecked` keeps only the hash comparison), and the proof-count and
  source-chain equality checks (`:114, 124-126, 142-145`), which the model enforces by
  construction (evidence is indexed by leg and resolved against the leg's declared chain).
  Omitting a check that can only reject admits more runs, so a result that excludes an
  outcome over this model is the stronger claim.  The enabledness results
  (`Properties.OpFinalizedFlowIsExecutable`, `Properties.OpTimedOutLegIsRefundable`) are the
  exception: they hold for this model, and the omitted checks (a paused handler, an
  already-executed bundle, an unsorted leg list) can still reject the call they exhibit.
* **`authorizeRefund` marks one leg per step, on the leg's declared chain**, as in
  `Contracts.Refund.ReachLog` and `Contracts.AppendPath.SysSteps`.  The contract marks every
  `Committed` leg of the flow in the manager of the chain that runs the call; the two agree
  when a leg's bundle hash fixes its chain (`bundleHash` embeds `block.chainid`,
  `interop/InteropCenter.sol:644`; backlog S4).
* Callers are fixed by the set of steps, as in `Contracts.AppendPath`.  Events, gas and the
  `FullMerkle` node cache are not modelled.
-/

namespace Contracts.InteropOperational

open MerkleSpec IMTAbstract Contracts.InteropCommitmentTree Contracts.Atomicity
open Contracts.Timeout Contracts.AtomicFlowManager Contracts.Refund Contracts.AppendPath
open Contracts.FlowBinding

/-! ## One chain's batches -/

/-- One chain's batch bookkeeping.

* `ended` — how many of the chain's batches have ended on L2, so have their END snapshot:
  batches `0 … ended - 1`.
* `settled` — how many of them have settled on the settlement layer, so have their
  `l1BatchTimestamp`: batches `0 … settled - 1`.  Settlement is in batch order
  (`MessageRootBase.sol:238-239`), so this is a prefix of the ended batches.
* `snap n` — the commitment tree at the end of batch `n` (meaningful for `n < ended`).
* `stamp n` — batch `n`'s `l1BatchTimestamp` (meaningful for `n < settled`). -/
structure BatchLog where
  ended : ℕ
  settled : ℕ
  snap : ℕ → Tree
  stamp : ℕ → ℕ

/-- A chain right after its registration: the genesis batch 0, whose IMT is the freshly
seeded `setup` at both boundaries, has ended and settled at time `0`
(`ChainBatchRootTree.sol:57-65`, `MessageRootBase.sol:364-389`). -/
def BatchLog.genesis : BatchLog where
  ended := 1
  settled := 1
  snap := fun _ => setup
  stamp := fun _ => 0

/-- The current batch ends with tree `T`: `T` becomes the END snapshot of batch `ended`. -/
def BatchLog.endBatch (B : BatchLog) (T : Tree) : BatchLog :=
  { B with ended := B.ended + 1, snap := fun n => if n = B.ended then T else B.snap n }

/-- The oldest unsettled batch settles at settlement-layer time `t`
(`MessageRootBase.sol:251-252`). -/
def BatchLog.settle (B : BatchLog) (t : ℕ) : BatchLog :=
  { B with settled := B.settled + 1, stamp := fun n => if n = B.settled then t else B.stamp n }

/-! ## The whole system -/

/-- The operational state.

* `chains` — every chain's manager and LIVE commitment tree (`Contracts.AppendPath.Chains`).
* `batches` — every chain's batches: their END snapshots and settlement times.
* `now` — the settlement layer's clock.
* `roots` — the settlement-layer roots recorded so far, each with its creation time and
  each chain's last batch inside it (`Contracts.Timeout.SlRoot`), most recent first. -/
structure OpState where
  chains : Chains
  batches : Chain → BatchLog
  now : ℕ
  roots : List SlRoot

/-- Every chain after the genesis upgrade and its registration: the managers are empty, the
trees are `setup`, batch 0 has settled at time `0`, and no root has been recorded. -/
def opGenesis : OpState where
  chains := genesisAll
  batches := fun _ => BatchLog.genesis
  now := 0
  roots := []

/-- Replace one chain's manager and live tree. -/
def OpState.setChain (X : OpState) (c : Chain) (s : ChainState) : OpState :=
  { X with chains := X.chains.update c s }

/-- Replace one chain's batch bookkeeping. -/
def OpState.setBatches (X : OpState) (c : Chain) (B : BatchLog) : OpState :=
  { X with batches := fun x => if x = c then B else X.batches x }

/-- Chain `c`'s current batch ends: its live tree becomes the batch's END snapshot. -/
def OpState.endBatch (X : OpState) (c : Chain) : OpState :=
  X.setBatches c ((X.batches c).endBatch (X.chains c).tree)

/-- Chain `c`'s oldest unsettled batch settles at the current time. -/
def OpState.settle (X : OpState) (c : Chain) : OpState :=
  X.setBatches c ((X.batches c).settle X.now)

/-- The settlement layer's clock moves to `t`. -/
def OpState.tick (X : OpState) (t : ℕ) : OpState :=
  { X with now := t }

/-- The shared root as of now: created now, holding every chain's settled batches. -/
def OpState.currentRoot (X : OpState) : SlRoot where
  created := X.now
  upTo := fun c => (X.batches c).settled - 1

/-- `_recordHistoricalRoot`: the current shared root becomes importable. -/
def OpState.recordRoot (X : OpState) : OpState :=
  { X with roots := X.currentRoot :: X.roots }

/-! ## The history a state determines -/

/-- Chain `c`'s tree at the end of batch `n`, as far as this state determines it: the END
snapshot of an ended batch, and the live tree for every later batch. -/
def OpState.histTree (X : OpState) (c : Chain) (n : ℕ) : Tree :=
  if n < (X.batches c).ended then (X.batches c).snap n else (X.chains c).tree

/-- **THE HISTORY A STATE DETERMINES**, as a fixed history `Contracts.Atomicity.System`.

* `tree c n` — the END snapshot of batch `n` if it has ended, else the live tree;
* `time c n` — the settlement time of batch `n` if it has settled, else `now`;
* `height c n` — `FullMerkle._height` of that tree, `fmHeight` of its leaf count.

On settled batches this is exactly what the contracts can see.  On unsettled batches it is
one consistent continuation: every open batch settles now, unchanged.  No call can cite an
unsettled batch, so the choice affects no logged call
(`Contracts.InteropOperational.Properties.OpRunSettledHistoryIsFinal`). -/
def OpState.history (X : OpState) : System where
  tree := X.histTree
  time := fun c n => if n < (X.batches c).settled then (X.batches c).stamp n else X.now
  height := fun c n => fmHeight (X.histTree c n).leafCount

/-! ## What the two gates check, operationally -/

/-- **`requireFlowFinalized` PASSED, ON SETTLED BATCHES.**  The fixed-history gate
`Contracts.Atomicity.ExecutedViaBy` evaluated on the current history, with every leg's
cited batch settled on the leg's declared chain (the proof is authenticated against an
imported root, `AtomicInteropProof.sol:113-139, 256-290`). -/
structure OpExecChecks (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (X : OpState) (e : ExecCall) : Prop where
  /-- `_checkFlowId`, `ManagerExecutingBundleNotInFlow`, and every leg's
  `verifyInclusion` (`AtomicFlowManager.sol:109-130`). -/
  gate : ExecutedViaBy h z0 hl cv fh X.history e.flow e.evidence e.leg
  /-- Every cited batch has settled. -/
  settled : ∀ ℓ ∈ e.flow.legs, (e.evidence ℓ).1 < (X.batches ℓ.chain).settled

/-- **`authorizeRefund` PASSED, AGAINST A RECORDED ROOT.**  `_checkFlowId`, the marked and
the missing leg are legs of the flow, the cited batch has settled, and the timeout gate
`Contracts.Timeout.LegRefundableVerifiedBy` holds against the recorded root `R` on the
current history (`AtomicFlowManager.sol:134-151`, `AtomicInteropProof.sol:152-206`). -/
structure OpAuthChecks (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (X : OpState) (a : AuthCall) (R : SlRoot) : Prop where
  /-- `interopRoots[slChainId][slBlock]` is imported (`ProofSettlementLayerInteropRootNotImported`,
  `AtomicInteropProof.sol:171-174`). -/
  rootImported : R ∈ X.roots
  /-- `_checkFlowId` (`AtomicFlowManager.sol:135`). -/
  flowChecked : FlowIdChecked fh a.flow
  /-- The leg this step marks is a leg of the flow (`:155-161`). -/
  legMem : a.leg ∈ a.flow.legs
  /-- `_missingLegIndex` indexes a leg of the flow (`:142, 150`). -/
  missingMem : a.missing ∈ a.flow.legs
  /-- The cited batch has settled (it is authenticated against `R`). -/
  settled : a.batch < (X.batches a.missing.chain).settled
  /-- `verifyTimeoutAbsence`, both branches, against `R`. -/
  timeout : LegRefundableVerifiedBy h z0 hl cv X.history R a.flow a.missing a.batch a.proof

/-! ## Runs -/

/-- **EVERY INTERLEAVING OF EVERY CHAIN'S CALLS AND THE SETTLEMENT LAYER'S STEPS.**
`OpSteps h z0 hl cv fh X Y log clog`: from `X` the system reaches `Y`.  `log` lists the
obligations the `append` calls committed, and `clog` the calls that ran `_checkFlowId`
(executions and refund authorizations), each most recent first.  Each per-chain step is the
corresponding step of `Contracts.AppendPath.SysSteps`, and `execute` that of
`Contracts.FlowBinding.RunLog`, except that the evidence is checked against the history
produced so far (`OpExecChecks`, `OpAuthChecks`) rather than a fixed one. -/
inductive OpSteps (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue) (fh : FlowHash)
    (X : OpState) : OpState → List Obligation → List CheckedCall → Prop
  | refl : OpSteps h z0 hl cv fh X X [] []
  /-- `append(f, b, _, hint)` on chain `c`: the manager guard and the tree insert. -/
  | append {Y log clog c f b hint low} : OpSteps h z0 hl cv fh X Y log clog →
      AppendSucceeds cv (Y.chains c) f b hint low →
      OpSteps h z0 hl cv fh X (Y.setChain c ((Y.chains c).appended cv f b low))
        (⟨f, b, c⟩ :: log) clog
  /-- `executeAtomicBundle` / `requireFlowFinalized`, on settled batches. -/
  | execute {Y log clog} (e : ExecCall) : OpSteps h z0 hl cv fh X Y log clog →
      OpExecChecks h z0 hl cv fh Y e →
      OpSteps h z0 hl cv fh X Y log (.execute e :: clog)
  /-- `authorizeRefund` against a recorded root, marking leg `a.leg` on its chain. -/
  | authorize {Y log clog} (a : AuthCall) (R : SlRoot) : OpSteps h z0 hl cv fh X Y log clog →
      OpAuthChecks h z0 hl cv fh Y a R →
      AuthorizeGuard (Y.chains a.leg.chain).mgr a.flow.flowId a.leg.bundleHash →
      OpSteps h z0 hl cv fh X
        (Y.setChain a.leg.chain
          ⟨(Y.chains a.leg.chain).mgr.set a.flow.flowId a.leg.bundleHash .Revertable,
            (Y.chains a.leg.chain).tree⟩)
        log (.authorize a :: clog)
  /-- `claimRefund` on chain `c`. -/
  | claim {Y log clog c f b} : OpSteps h z0 hl cv fh X Y log clog →
      ClaimGuard (Y.chains c).mgr f b →
      OpSteps h z0 hl cv fh X (Y.setChain c ⟨(Y.chains c).mgr.set f b .Reverted, (Y.chains c).tree⟩)
        log clog
  /-- `L2InteropCommitmentTree.initL2` on chain `c`; `setup` lets it through only on an empty
  tree. -/
  | initL2 {Y log clog c} : OpSteps h z0 hl cv fh X Y log clog →
      (Y.chains c).tree.leafCount = 0 →
      OpSteps h z0 hl cv fh X (Y.setChain c ⟨(Y.chains c).mgr, reseed (Y.chains c).tree⟩) log clog
  /-- Chain `c`'s current batch ends on L2. -/
  | endBatch {Y log clog c} : OpSteps h z0 hl cv fh X Y log clog →
      OpSteps h z0 hl cv fh X (Y.endBatch c) log clog
  /-- Chain `c`'s oldest ended, unsettled batch settles now. -/
  | settle {Y log clog c} : OpSteps h z0 hl cv fh X Y log clog →
      (Y.batches c).settled < (Y.batches c).ended →
      OpSteps h z0 hl cv fh X (Y.settle c) log clog
  /-- The settlement layer's clock moves forward (or stays). -/
  | tick {Y log clog t} : OpSteps h z0 hl cv fh X Y log clog → Y.now ≤ t →
      OpSteps h z0 hl cv fh X (Y.tick t) log clog
  /-- The current shared root is recorded and becomes importable. -/
  | recordRoot {Y log clog} : OpSteps h z0 hl cv fh X Y log clog →
      OpSteps h z0 hl cv fh X Y.recordRoot log clog

/-! ## The aggregation fact the timeout gate needs -/

/-- **A BATCH THAT SETTLED STRICTLY BEFORE A ROOT WAS CREATED IS INSIDE IT.**  The form of
`Contracts.Timeout.Aggregates` with `<` for `≤`.  It is what the source's own soundness
argument uses ("any batch aggregated after it has `t' >= T > deadline`",
`AtomicInteropProof.sol:75-76`), and it is what every recorded root of an operational run
satisfies (`Contracts.InteropOperational.Properties.OpRunRootsAggregateBefore`).  The
non-strict `Aggregates` is stronger, and a root recorded between two settlements at one
timestamp does not meet it (`Properties.OpRootMayMissSameTimeBatch`). -/
def AggregatesBefore (S : System) (R : SlRoot) : Prop :=
  ∀ c n, S.time c n < R.created → n ≤ R.upTo c

end Contracts.InteropOperational
