import EraSpec.Examples.BurnMintBridge.ProtocolComposition
import EraSpec.Contracts.AtomicInteropProof.Specs.LastBatchInRoot
import EraSpec.Protocol.InteropAtomicity.Specs.Timeout

/-!
# Spec: the halted-chain (END) timeout branch in the reference bridge's evidence

Sources, in the pinned era-contracts tree (`c67894b9`):

* `contracts/atomic-interop/libraries/AtomicInteropProof.sol` — `verifyTimeoutAbsence`
  (:152-206), `_verifyLastBatchInRoot` (:217-230), `_authenticateRoot` (:256-290), and the
  library header: the two timeout branches (:64-82), SOUNDNESS (:84-87) and
  COMPLETENESS (:89-94);
* `contracts/atomic-interop/README.md:51-59` (timeout and refund, the halted-chain case) and
  `:73-90` (precondition 1: every chain has a batch inside the aggregated root).

`ProtocolComposition` (namespace `Properties.PreparedBridge`) drives the reference bridge
with two predicates over a history of per-chain IMT snapshots: `OnTime` (finalization) and
`Missing` (refund).  `Missing` is the successor-pinned form — a gap witness in snapshot `n`
while snapshot `n + 1` settled after the deadline — which is the BEGIN branch of
`verifyTimeoutAbsence` with `begin(n + 1) = end(n)`.  The END branch, which the header adds
so that a source chain that HALTS can still be refunded (`AtomicInteropProof.sol:77-78`,
`README.md:55-57`), was not composed (`ProtocolComposition.lean:14-16`, `REVIEW.md:135-137`).
This file supplies it at three levels.

1. **Over the adapter's history (§1).**  `MissingEnd` is the END disjunct of
   `AttackVectors.TimeoutSoundness.timeout_implies_never_finalized`, stated over `History`.
   `Properties.MissingEndImpliesMissing` shows it is already an instance of `Missing`: the
   adapter's history is a total function of the batch index, so the batch after `B` that
   `hlast` talks about always exists in the model, and it is late.  Composing the abstract
   END form therefore admits no new refund.  The END branch only has content once the
   evidence is restricted to batches that are actually inside an imported root, which
   `History` does not model.

2. **As the contract runs it (§2).**  Both branches resolve against an imported
   settlement-layer root `R` created strictly after the deadline
   (`ProofInteropRootNotAfterDeadline`, :171-179), and the proven batch is a leaf of that
   root (`_authenticateRoot` verifies the chain-batch-root leaf of `(sourceChainId,
   batchNumber)` against `interopRoots[slChainId][slBlock]`, :256-290).  The BEGIN branch
   needs a batch with `t > deadline` inside `R`; a chain that halts before settling such a
   batch never has one.  The END branch needs `R`'s last batch of the chain to be in time,
   which `_verifyLastBatchInRoot` establishes; here it is the index-level zero-cascade check
   `AttackVectors.LastBatchInRoot.RightEmpty`, the content of that loop under the zero
   cascade's collision resistance (`LastBatchInRoot` header).

3. **With the hash-level last-batch proof (§3).**  The END branch carries the batch-leaf
   path `(sibs, leaf)` and `Contracts.Timeout.LastBatchAccepted` against the chain tree
   behind the root (`Contracts.Timeout.RootBacking`); no hash premise.  A failure is located
   on the submitted path (`PinnedBreak` / `PathCollision`).

The settlement layer's side of the bargain is `RootAggregates` (`PROTO-AGGREGATES`,
`Contracts.Timeout.Aggregates` for this history): a batch that settled by the time a root
was created is inside that root.  It is a property of how the settlement layer builds roots,
not of the interop contracts, and it is a visible premise wherever the END branch is used.

**This file is definitions only.**  Statements: `../Properties/EndBranch.lean`; proofs:
`../Proofs/EndBranch.lean`.

Model boundaries.  Times are the adapter's `UInt256` timestamps; root creation times are
`Contracts.Timeout.SlRoot.created : ℕ` and are compared through `Fin.val`.  The settlement
layer chain id, the begin/end leaf masks (`IMT_BEGIN_ROOT_LEAF_INDEX` /
`IMT_END_ROOT_LEAF_INDEX`) and the IMT proof bytes are not modelled: a non-inclusion proof
is its opened low leaf (`GapWitness`), exactly as in `Missing`.  Finalization keeps the
adapter's unrestricted `OnTime`; restricting it to imported roots only removes executions,
so the safety results below are the stronger claims.
-/

namespace Applications.BurnMintBridge.EndBranch

open IMTAbstract Properties.PreparedBridge

/-- `IndexedMerkleTree.verifyNonInclusion`'s opened low leaf: a leaf of `s` whose window
straddles `v` (`W.key < v` and `W.nextKey = 0 ∨ v < W.nextKey`).  `Missing` and the
reclaim gate use exactly this shape. -/
def GapWitness (s : Finset AbsLeaf) (v : UInt256) : Prop :=
  ∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-! ## 1. The END branch over the adapter's history -/

/-- **THE END BRANCH, ABSTRACTLY.**  `TimeoutSoundness.timeout_implies_never_finalized`'s
END disjunct over the adapter's history: batch `B` settled by the deadline, every later
batch settles no earlier than a time `T` strictly after the deadline (`hlast`, what
`_verifyLastBatchInRoot` plus the post-deadline root buy), and batch `B`'s END tree carries
a gap witness for the leg's commit value. -/
def MissingEnd (H : History) (l : Leg) : Prop :=
  ∃ (B : ℕ) (T : UInt256), H.settledAt l.sourceChain B ≤ l.deadline ∧ l.deadline < T ∧
    (∀ n, B < n → T ≤ H.settledAt l.sourceChain n) ∧
    GapWitness (H.tree l.sourceChain B) l.commitValue

/-- Refund evidence on either branch: the adapter's successor-pinned `Missing` (BEGIN) or
the abstract END form. -/
def MissingEither (H : History) (l : Leg) : Prop :=
  Missing H l ∨ MissingEnd H l

/-- The adapter's evidence (`Properties.PreparedBridge.evidence`) with refunds on either
branch.  Finalization is unchanged: every prerequisite on time. -/
def evidenceEither (H : History) (flow : Transfer → List Leg) : Evidence where
  finalize := fun i => ∀ l ∈ flow i, OnTime H l
  recover := fun i => ∃ l ∈ flow i, MissingEither H l

/-- Chain `c`'s slice of the history as `AttackVectors.TimeoutSoundness` reads it: END sets
are the snapshots' key sets, times are the settlement timestamps as naturals. -/
def batchHistory (H : History) (c : UInt256) : AttackVectors.TimeoutSoundness.BatchHistory where
  endSet := fun n => keys (H.tree c n)
  time := fun n => (H.settledAt c n).val

/-! ## 2. The timeout gate as the contract runs it -/

/-- The imported settlement-layer roots, `L2_INTEROP_ROOT_STORAGE.interopRoots(slChainId,
slBlock)`, indexed by the SL block.  Each is a `Contracts.Timeout.SlRoot`: its creation
timestamp `created` (`rootTimestamp`, nonzero once imported, :171-174) and, per chain, the
last batch `upTo` it aggregates — the root holds that chain's batches `0 … upTo`, so every
chain has a batch inside it (`README.md:77-90`). -/
abbrev Roots := ℕ → Contracts.Timeout.SlRoot

/-- **THE SETTLEMENT LAYER'S SIDE OF THE BARGAIN** (`PROTO-AGGREGATES`;
`Contracts.Timeout.Aggregates` for this history): a batch that had settled by the time `R`
was created is inside `R`.  Not a property of the interop contracts; a premise wherever the
END branch is used. -/
def RootAggregates (H : History) (R : Contracts.Timeout.SlRoot) : Prop :=
  ∀ (c : UInt256) (n : ℕ), (H.settledAt c n).val ≤ R.created → n ≤ R.upTo c

/-- The IMT leaf set at the BEGIN of batch `L` (chain-batch-root leaf 2): the END of batch
`L - 1`, and for the genesis batch `0` the freshly seeded tree (`README.md:80-82`), which is
`History.Valid.genesis`'s snapshot. -/
def beginLeaves (H : History) (c : UInt256) : ℕ → Finset AbsLeaf
  | 0 => {⟨0, 0⟩}
  | n + 1 => H.tree c n

/-- `verifyInclusion` against root `R` (:113-139): a batch inside `R`, settled by the
deadline, whose END tree holds the commit value.  Used only to show that a countermodel's
finalization evidence is realizable inside an imported root; the evidence below keeps the
adapter's unrestricted `OnTime`. -/
def OnTimeIn (H : History) (R : Contracts.Timeout.SlRoot) (l : Leg) : Prop :=
  ∃ n, n ≤ R.upTo l.sourceChain ∧ H.settledAt l.sourceChain n ≤ l.deadline ∧
    l.commitValue ∈ keys (H.tree l.sourceChain n)

/-- **THE BEGIN BRANCH AS RUN, AGAINST ROOT `R`.**  `R` was created after the deadline
(:177-179); batch `L` is inside `R` (:256-290) and settled after the deadline
(`ProofTimeoutBranchMismatch(true, …)`, :185-188); its BEGIN tree has a gap witness for the
commit value (:198-205). -/
def BeginVia (H : History) (R : Contracts.Timeout.SlRoot) (l : Leg) : Prop :=
  l.deadline.val < R.created ∧
    ∃ L, L ≤ R.upTo l.sourceChain ∧ l.deadline < H.settledAt l.sourceChain L ∧
      GapWitness (beginLeaves H l.sourceChain L) l.commitValue

/-- **THE END BRANCH AS RUN, AGAINST ROOT `R`.**  `R` was created after the deadline;
batch `B` is inside `R` and settled by the deadline (`ProofTimeoutBranchMismatch(false, …)`,
:189-192); `_verifyLastBatchInRoot` passed (:195, :217-230), here as its index-level content
`RightEmpty` over the `upTo + 1` batch leaves of the chain's tree, which fits `depth` levels;
and batch `B`'s END tree has a gap witness for the commit value (:198-205). -/
def EndVia (H : History) (R : Contracts.Timeout.SlRoot) (l : Leg) : Prop :=
  l.deadline.val < R.created ∧
    ∃ B depth, H.settledAt l.sourceChain B ≤ l.deadline ∧
      B < R.upTo l.sourceChain + 1 ∧ R.upTo l.sourceChain + 1 ≤ 2 ^ depth ∧
      AttackVectors.LastBatchInRoot.RightEmpty B (R.upTo l.sourceChain + 1) depth ∧
      GapWitness (H.tree l.sourceChain B) l.commitValue

/-- The END branch with `lastInRoot` as a conclusion (`Contracts.Timeout.EndBranchVerified`):
the proven batch IS `R`'s last batch of the chain. -/
def EndLastVia (H : History) (R : Contracts.Timeout.SlRoot) (l : Leg) : Prop :=
  l.deadline.val < R.created ∧
    H.settledAt l.sourceChain (R.upTo l.sourceChain) ≤ l.deadline ∧
    GapWitness (H.tree l.sourceChain (R.upTo l.sourceChain)) l.commitValue

/-- **THE END BRANCH WITHOUT `_verifyLastBatchInRoot`**, for the countermodel: any in-time
batch inside `R` is accepted. -/
def EndUncheckedVia (H : History) (R : Contracts.Timeout.SlRoot) (l : Leg) : Prop :=
  l.deadline.val < R.created ∧
    ∃ B, B ≤ R.upTo l.sourceChain ∧ H.settledAt l.sourceChain B ≤ l.deadline ∧
      GapWitness (H.tree l.sourceChain B) l.commitValue

/-- **`verifyTimeoutAbsence` AGAINST ROOT `R`**: either branch. -/
def TimeoutVia (H : History) (R : Contracts.Timeout.SlRoot) (l : Leg) : Prop :=
  BeginVia H R l ∨ EndVia H R l

/-- The reference bridge driven by the timeout gate as run: execution needs every
prerequisite on time; recovery needs one prerequisite with an accepted timeout against some
imported root. -/
def checkedEvidence (H : History) (roots : Roots) (flow : Transfer → List Leg) : Evidence where
  finalize := fun i => ∀ l ∈ flow i, OnTime H l
  recover := fun i => ∃ l ∈ flow i, ∃ k, TimeoutVia H (roots k) l

/-- The same with the BEGIN branch only: the gate before the END branch was added. -/
def beginOnlyEvidence (H : History) (roots : Roots) (flow : Transfer → List Leg) : Evidence where
  finalize := fun i => ∀ l ∈ flow i, OnTime H l
  recover := fun i => ∃ l ∈ flow i, ∃ k, BeginVia H (roots k) l

/-- The same with the END branch's last-batch check dropped, for the countermodel. -/
def uncheckedEvidence (H : History) (roots : Roots) (flow : Transfer → List Leg) : Evidence where
  finalize := fun i => ∀ l ∈ flow i, OnTime H l
  recover := fun i => ∃ l ∈ flow i, ∃ k,
    BeginVia H (roots k) l ∨ EndUncheckedVia H (roots k) l

/-! ## 3. The END branch with the hash-level last-batch proof -/

/-- The chain trees behind each imported root: root `k`'s per-chain batch-leaf lists and
heights (`Contracts.Timeout.RootBacking`, whose `upToLast` ties the leaf count to
`upTo + 1`).  `h` is the node hash and `ze` the empty-entry constant
`CHAIN_TREE_EMPTY_ENTRY_HASH`.  Part of the world, not chosen by a prover. -/
abbrev Backing (h : MerkleSpec.Hash) (ze : UInt256) (roots : Roots) :=
  (k : ℕ) → Contracts.Timeout.RootBacking h ze (roots k)

/-- **ONE SUBMITTED END-BRANCH TIMEOUT PROOF, WITH EVERY WITNESS NAMED**: the missing leg,
the imported root it resolves against (`slBlock`), the batch, and the batch-leaf path
`MessageHashing.readAggregationHopPath(settlementProof)` as siblings `sibs` plus the batch
leaf `leaf`.  Naming them is what lets a failure be located on this submission. -/
structure EndSubmission where
  leg : Leg
  root : ℕ
  batch : ℕ
  sibs : ℕ → UInt256
  leaf : UInt256

/-- **THE END BRANCH AS RUN, HASH LEVEL.**  As `EndVia`, with `_verifyLastBatchInRoot` as
`Contracts.Timeout.LastBatchAccepted`: the path authenticates the leaf against the chain
tree's root, and every left-turn sibling is that level's zero-cascade hash. -/
def EndAcceptedBy {h : MerkleSpec.Hash} {ze : UInt256} (H : History) (roots : Roots)
    (bk : Backing h ze roots) (e : EndSubmission) : Prop :=
  e.leg.deadline.val < (roots e.root).created ∧
    H.settledAt e.leg.sourceChain e.batch ≤ e.leg.deadline ∧
    Contracts.Timeout.LastBatchAccepted (bk e.root) e.leg.sourceChain e.batch e.sibs e.leaf ∧
    GapWitness (H.tree e.leg.sourceChain e.batch) e.leg.commitValue

/-- **A BREAK LOCATED ON THE SUBMISSION.**  A `PinnedBreak` on the chain tree right after
the submitted batch (a node collision with the zero cascade, or the next entry equal to the
empty-entry constant), or a `PathCollision` at a named level of the submitted path.  Every
compared pair is determined by the instance and the submission. -/
def EndBreak {h : MerkleSpec.Hash} {ze : UInt256} {roots : Roots} (bk : Backing h ze roots)
    (e : EndSubmission) : Prop :=
  MerkleSpec.LastLeaf.PinnedBreak h ze ((bk e.root).leaves e.leg.sourceChain) e.batch
    ∨ MerkleSpec.Verifier.PathCollision h ze ((bk e.root).leaves e.leg.sourceChain) e.sibs 0
        ((bk e.root).height e.leg.sourceChain) e.batch e.leaf

/-- The reference bridge with the END branch at hash level.  `sub i` is the END submission
offered for transfer `i`; the BEGIN branch is as in `checkedEvidence`.  The record is unique,
so a refund on the END branch is authorized by exactly `sub` of the recorded transfer. -/
def pinnedEvidence {h : MerkleSpec.Hash} {ze : UInt256} (H : History) (roots : Roots)
    (bk : Backing h ze roots) (flow : Transfer → List Leg) (sub : Transfer → EndSubmission) :
    Evidence where
  finalize := fun i => ∀ l ∈ flow i, OnTime H l
  recover := fun i => (∃ l ∈ flow i, ∃ k, BeginVia H (roots k) l)
    ∨ ((sub i).leg ∈ flow i ∧ EndAcceptedBy H roots bk (sub i))

/-! ## Concrete instances for the witnesses and countermodels

One leg on chain `0` with commit value `1` and deadline `0`.  Batches `0` and `1` settle at
time `0` (on time) and every later batch at time `2`.  The imported roots are created at time
`1` (after the deadline) and hold batches `0, 1` (`Contracts.Timeout.demoRoot`), so a batch
`≥ 2` is in no imported root: the chain has halted as far as the settlement layer can prove.
`RootAggregates` holds for these roots.  The stale-root countermodel replaces root `0` by
`Contracts.Timeout.staleRoot`; the forged-path countermodel backs the root by a chain tree
whose second batch leaf is the empty-entry constant. -/

/-- The witnesses' leg: chain `0`, commit value `1`, deadline `0`. -/
def demoLeg : Leg := ⟨0, 1, 0⟩

/-- Batches `0, 1` at time `0`; later batches at time `2`. -/
def demoTime (n : ℕ) : UInt256 := if n ≤ 1 then 0 else 2

/-- **A CHAIN THAT NEVER COMMITS THE LEG**: every snapshot is the genesis leaf set. -/
def haltedHistory : History where
  tree := fun _ _ => {⟨0, 0⟩}
  settledAt := fun _ n => demoTime n

/-- The genesis leaf set after the guarded insert of `1` through the genesis leaf. -/
def committedLeaves : Finset AbsLeaf := imtInsert {⟨0, 0⟩} ⟨0, 0⟩ 1

/-- Snapshot `0` is genesis; from snapshot `1` on, `1` is committed. -/
def committedTree : ℕ → Finset AbsLeaf
  | 0 => {⟨0, 0⟩}
  | _ + 1 => committedLeaves

/-- **A CHAIN THAT COMMITS THE LEG IN TIME**, during batch `1` (settled at time `0`). -/
def committedHistory : History where
  tree := fun _ => committedTree
  settledAt := fun _ n => demoTime n

/-- Batch `0` at time `0` (on time), batch `1` at time `1` (late, and inside
`Contracts.Timeout.demoRoot`), later batches at time `2`. -/
def lateTime (n : ℕ) : UInt256 := if n = 0 then 0 else if n = 1 then 1 else 2

/-- **A CHAIN THAT SETTLES A LATE BATCH INSIDE THE ROOT** and never commits the leg: the
BEGIN branch's world. -/
def lateHistory : History where
  tree := fun _ _ => {⟨0, 0⟩}
  settledAt := fun _ n => lateTime n

/-- Root `0` is `Contracts.Timeout.staleRoot` (created at `1`, stops at batch `0`, so it
omits the already-settled batch `1`); every other root is `Contracts.Timeout.demoRoot`. -/
def staleRoots : Roots :=
  fun k => if k = 0 then Contracts.Timeout.staleRoot else Contracts.Timeout.demoRoot

/-- A chain tree whose second batch leaf IS the empty-entry constant `0`: `[5, 0]` at
height `1` under `demoHash`.  A domain-separation failure (`HashBreak.entryIsEmpty`) that lets
batch `0` pass `_verifyLastBatchInRoot` although batch `1` is in the root. -/
def forgedBacking : Contracts.Timeout.RootBacking MerkleSpec.LastLeaf.demoHash 0
    Contracts.Timeout.demoRoot where
  leaves := fun _ => [5, 0]
  height := fun _ => 1
  upToLast := fun _ => rfl
  capacity := fun _ => by norm_num

end Applications.BurnMintBridge.EndBranch
