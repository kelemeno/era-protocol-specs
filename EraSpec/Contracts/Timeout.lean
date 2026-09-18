import EraSpec.Contracts.Atomicity
import EraSpec.Core.LastLeaf

/-!
# Model: the timeout decision, and why it is justified

`Contracts.Atomicity.LegRefundable` takes `IsLastOnTime` — "batch `N` is the
chain's last batch that settled by the deadline" — as a *branch condition*.  That
was an assumption: nothing in that file says where it comes from, and the header
says so.

It comes from the settlement layer, and this file derives it.  What the timeout
path actually verifies is three separate facts about an aggregation root, and
`Properties.Timeout.IsLastOnTimeDerived` turns them into the fact the safety
argument uses.

**This file is definitions only.**  The results are in `EraSpec.Properties.Timeout`
and proved in `EraSpec.Proofs.Timeout`.

## What `verifyTimeoutAbsence` checks

    uint256 rootTimestamp = L2_INTEROP_ROOT_STORAGE.interopRoots(slChainId, slBlock).timestamp;
    if (rootTimestamp == 0) revert ProofSettlementLayerInteropRootNotImported(...);
    if (rootTimestamp <= _deadline) revert ProofInteropRootNotAfterDeadline(...);
    …
    if (_absence.provesAgainstBeginRoot) {
        if (l1BatchTimestamp <= _deadline) revert ProofTimeoutBranchMismatch(true, ...);
    } else {
        if (l1BatchTimestamp > _deadline) revert ProofTimeoutBranchMismatch(false, ...);
        _verifyLastBatchInRoot(MessageHashing.readAggregationHopPath(_absence.settlementProof));
    }

So the two branches are:

* **BEGIN** — the batch settled *after* the deadline, and the commit value is absent
  from the tree as that batch began.  Nothing about aggregation is needed: a late
  batch's begin state is a previous batch's end state, and the tree only grows.
* **END** — the batch settled *by* the deadline, and it is the chain's **last**
  batch inside a settlement-layer root that was itself created after the deadline.

Both branches resolve against an imported settlement-layer root created strictly
after the deadline.  `SlRoot` is that root, and the END branch's `_verifyLastBatchInRoot`
is `lastInRoot` below.

## The one assumption that remains, and where it lives

`Aggregates` is the settlement layer's side of the bargain: a batch that had settled
by the time a root was created is inside that root.  It cannot be derived here —
it is a property of how the settlement layer builds its roots, not of the interop
contracts — so it is a named hypothesis, and
`Properties.Timeout.StaleRootRefundsDeliveredLeg` is the countermodel showing the
safety argument really needs it.  What it replaces is strictly worse: an unexplained
`IsLastOnTime` sitting inside the refund gate with nothing behind it.

## `lastInRoot` is derived too

`EndBranchVerified.lastInRoot` is a conclusion, and `EndBranchAccepted` below
carries the *proof* instead: the batch-leaf path, authenticated against the chain
tree's root, with the zero-sibling check `_verifyLastBatchInRoot` runs.
`EraSpec.Core.LastLeaf` turns that into "this is the last leaf, or here is a hash
collision", so the dependency chain runs all the way from the accepted proof to the
justified timeout.
-/

namespace Contracts.Timeout

open Contracts.InteropCommitmentTree Contracts.Atomicity MerkleSpec MerkleSpec.LastLeaf

/-- An imported settlement-layer aggregation root, as the timeout path resolves
against it.

* `created` — `interopRoots[slChainId][slBlock].timestamp`, nonzero because the
  root must be imported (`ProofSettlementLayerInteropRootNotImported`).
* `upTo` — the last batch of each chain aggregated into this root.  The contract
  never reads this number; it proves a batch *equals* it, which is what
  `_verifyLastBatchInRoot` establishes. -/
structure SlRoot where
  created : ℕ
  upTo : Chain → ℕ

/-- **THE SETTLEMENT LAYER'S SIDE OF THE BARGAIN.**  A batch that had settled by the
time a root was created is inside that root.

This is not a property of the interop contracts and is not derived here.  It is
what makes "last batch in this root" mean "last batch that settled in time", which
is the step the refund gate needs.  `Properties.Timeout.StaleRootRefundsDeliveredLeg`
shows that without it a delivered leg can be refunded. -/
def Aggregates (S : System) (R : SlRoot) : Prop :=
  ∀ c n, S.time c n ≤ R.created → n ≤ R.upTo c

/-- The END branch, exactly as verified: the root post-dates the deadline, the batch
settled by the deadline, and the batch is the chain's last one in that root. -/
structure EndBranchVerified (S : System) (R : SlRoot) (c : Chain) (D N : ℕ) : Prop where
  /-- `ProofInteropRootNotAfterDeadline`. -/
  rootAfterDeadline : D < R.created
  /-- `ProofTimeoutBranchMismatch(false, …)`. -/
  onTime : S.time c N ≤ D
  /-- `_verifyLastBatchInRoot`, as a conclusion. -/
  lastInRoot : N = R.upTo c

/-- The BEGIN branch, exactly as verified: the root post-dates the deadline and the
batch settled after it. -/
structure BeginBranchVerified (S : System) (R : SlRoot) (c : Chain) (D N : ℕ) : Prop where
  /-- `ProofInteropRootNotAfterDeadline`. -/
  rootAfterDeadline : D < R.created
  /-- `ProofTimeoutBranchMismatch(true, …)`. -/
  late : D < S.time c N

/-- **THE TIMEOUT GATE, WITH THE ROOT IN HAND.**  What `verifyTimeoutAbsence`
accepts, with no `IsLastOnTime` anywhere: the branch conditions are the three
comparisons the contract makes, and the aggregation fact is supplied separately by
`Aggregates`. -/
def LegRefundableVerified (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) (R : SlRoot) (F : Flow) (leg : FlowLeg) : Prop :=
  ∃ (N : ℕ) (p : ImtProof),
    (BeginBranchVerified S R leg.chain F.deadline N ∧
        AbsenceAccepted h z0 hl (beginTree S leg.chain N) (beginHeight S leg.chain N)
          (legValue cv F leg) p)
      ∨ (EndBranchVerified S R leg.chain F.deadline N ∧
          AbsenceAccepted h z0 hl (S.tree leg.chain N) (S.height leg.chain N)
            (legValue cv F leg) p)

/-! ## Where `lastInRoot` comes from

`EndBranchVerified.lastInRoot` above is a conclusion, not a check.  The check is
`_verifyLastBatchInRoot`, and these definitions are what it actually runs against:
the per-chain batch trees the aggregation root is built from, and the shape test on
the batch leaf's path. -/

/-- The per-chain batch trees an aggregation root is built from.  Leaf `i` of chain
`c`'s tree is that chain's batch `i`, so "the last leaf" and "the last batch in the
root" are the same index.

`ze` is the chain tree's empty-entry constant `CHAIN_TREE_EMPTY_ENTRY_HASH`, which is
a different constant from the IMT's `IMT_EMPTY_LEAF_HASH` — the two trees are built
by different libraries and pad with their own values. -/
structure RootBacking (h : Hash) (ze : UInt256) (R : SlRoot) where
  /-- Chain `c`'s batch leaves inside this root, in batch order. -/
  leaves : Chain → List UInt256
  /-- The chain tree's height. -/
  height : Chain → ℕ
  /-- `R.upTo c` is the last leaf index, so the root holds batches `0 … upTo c`. -/
  upToLast : ∀ c, (leaves c).length = R.upTo c + 1
  /-- The tree fits its height. -/
  capacity : ∀ c, (leaves c).length ≤ 2 ^ height c

/-- `_verifyLastBatchInRoot` accepted for chain `c`'s batch `N`.

`authenticated` is the path recomputing the chain tree's root — the same proof words
`_authenticateRoot` already verified, which is what stops the prover from choosing
its own siblings.  `zeroRightSiblings` is the check itself: wherever the path goes
left, the right sibling must be that level's empty-subtree hash. -/
structure LastBatchAccepted {h : Hash} {ze : UInt256} {R : SlRoot} (B : RootBacking h ze R)
    (c : Chain) (N : ℕ) (sibs : ℕ → UInt256) (x : UInt256) : Prop where
  inRange : N < (B.leaves c).length
  authenticated : walkPure h sibs 0 (B.height c) N x = rootOf h ze (B.leaves c) (B.height c)
  zeroRightSiblings : ∀ l < B.height c, (N / 2 ^ l) % 2 = 0 → sibs l = zeros h ze l

/-- The END branch with `lastInRoot` replaced by the proof that establishes it —
this is the branch as the contract runs it. -/
structure EndBranchAccepted {h : Hash} {ze : UInt256} {R : SlRoot} (B : RootBacking h ze R)
    (S : System) (c : Chain) (D N : ℕ) (sibs : ℕ → UInt256) (x : UInt256) : Prop where
  /-- `ProofInteropRootNotAfterDeadline`. -/
  rootAfterDeadline : D < R.created
  /-- `ProofTimeoutBranchMismatch(false, …)`. -/
  onTime : S.time c N ≤ D
  /-- `_verifyLastBatchInRoot`. -/
  lastBatch : LastBatchAccepted B c N sibs x

/-- **THE TIMEOUT GATE AS THE CONTRACT RUNS IT.**  Same as `LegRefundableVerified`
except that the END branch carries the last-batch *proof* rather than its
conclusion. -/
def LegRefundableAccepted (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) {ze : UInt256} {R : SlRoot} (B : RootBacking h ze R) (F : Flow)
    (leg : FlowLeg) : Prop :=
  ∃ (N : ℕ) (p : ImtProof),
    (BeginBranchVerified S R leg.chain F.deadline N ∧
        AbsenceAccepted h z0 hl (beginTree S leg.chain N) (beginHeight S leg.chain N)
          (legValue cv F leg) p)
      ∨ (∃ (sibs : ℕ → UInt256) (x : UInt256),
          EndBranchAccepted B S leg.chain F.deadline N sibs x ∧
            AbsenceAccepted h z0 hl (S.tree leg.chain N) (S.height leg.chain N)
              (legValue cv F leg) p)

/-! ## A stale root, for the countermodel

One chain, two batches, both settled at time `0`, so both are on time for deadline
`0`.  The commit value is absent at batch 0 and present from batch 1 on. -/

/-- The chain commits `a` during its second batch; every batch settles at time `0`. -/
def staleSystem (a : UInt256) : System where
  tree := fun _ n => if n = 0 then setup else insert setup a 0
  time := fun _ _ => 0
  height := fun _ n => if n = 0 then 0 else 1

/-- A root created after the deadline that nevertheless stops at batch 0 — it omits
a batch that had already settled, which is exactly what `Aggregates` forbids. -/
def staleRoot : SlRoot where
  created := 1
  upTo := fun _ => 0

end Contracts.Timeout
