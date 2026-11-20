import EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRoot

/-!
# Stale-snapshot reclaim, against the absence verifier as deployed

`AttackVectors.StaleSnapshot` models a reclaim witness at snapshot `j` as a leaf
`W ∈ S j` whose window straddles `v`, and reads its theorems as statements about
"an accepted reclaim".  The deployed reclaim gate does not receive a leaf of the
snapshot.  It receives a preimage `ℓ`, an index and a sibling path, and accepts when
`IndexedMerkleTree.verifyNonInclusion` returns `true` (era-contracts `b17415d20`, paths under
`l1-contracts/contracts/`):

* `common/libraries/IndexedMerkleTree.sol:46-55`: `setup` pads `FullMerkle` with
  `IMT_EMPTY_LEAF_HASH` (`:51`; `common/Config.sol:141`) and pushes the sentinel leaf
  `{0,0,0}` at index 0 (`:52-53`);
* `IndexedMerkleTree.sol:154-172`: `verifyNonInclusion` checks `_value != 0`,
  `_lowLeaf.value < _value`, `_lowLeaf.nextValue == 0 || _value < _lowLeaf.nextValue`,
  and `Merkle.calculateRootMemory(_lowLeafProof, _lowLeafIndex, hashLeaf(_lowLeaf)) == _root`;
  nothing checks that `_lowLeafIndex` is an occupied slot;
* `atomic-interop/libraries/AtomicInteropProof.sol:116-123`: this call is the only absence
  check of the timeout gate, on both branches.

So the accepted low leaf need not be a leaf of the snapshot: it is a preimage whose hash the
submitted path opens, and `StaleSnapshot`'s theorems (about genuine leaves `W ∈ S j`) do not
speak about it.  The results below take the padding constant as a parameter `z0` (at
`b17415d20`, `IMT_EMPTY_LEAF_HASH`) and locate any accepted proof that is not a genuine witness
as a `TreeRootBreak` on the submitted proof.  At the extraction pin `c67894b9` the padding was
`hashLeaf({0,0,0})`, so `{0,0,0}` presented at an empty slot was accepted as a low leaf for
every nonzero value; that H2 record is `../History/Specs/StaleSnapshotFaithful.lean`.

This file restates the stale-snapshot gate over the concrete contract state:

* a contract run `R : ℕ → Tree` from `setup` (`Contracts.InteropCommitmentTree.Run`),
  whose snapshot `j` is `R j`;
* the root `FullMerkle` publishes for it at height `ht j`
  (`Contracts.InteropCommitmentTree.root`);
* the reclaim proof as `verifyNonInclusion` consumes it
  (`Contracts.InteropCommitmentTree.NonInclusionAccepted`), with the index and path
  length the prover's;
* delivery as genuine membership, `v ∈ keys (toAbs (R i))` at an on-time snapshot
  (`t i ≤ D`), and the reclaim pin `D < t (j+1)` exactly as `StaleSnapshot` has it.

That pin is `StaleSnapshot`'s abstract model of the deadline gate: the deployed gate
makes no such comparison.  `AttackVectors.StaleSnapshotBranches` maps the two deployed
timeout branches onto the pin, under its own bridging premises.  The two topics are
separate results: no theorem composes `StaleSnapshotBranches` with this one.  A composed
statement is in the Atomicity model: `Contracts.Timeout.TimeoutMeansMissedDeadlineOrBreak`,
the counterpart of `Properties.StaleWitnessNotRedeemableOrBreak`.  It takes, over `Wf`
systems, a timeout verified on either deployed branch with `verifyNonInclusion` acceptance
(`Contracts.Atomicity.AbsenceAccepted`): the BEGIN branch reads
`Contracts.Atomicity.beginTree`, in which `begin(n+1) = end(n)` is built in, and the END
branch (which takes `_verifyLastBatchInRoot` by its conclusion) is bridged by
`Contracts.Timeout.Aggregates`.  It concludes that the leg's commit value is absent from its
source chain's tree at every on-time batch, or the absence proof carries a located break.
`Contracts.Timeout.TimeoutExcludesFinalityOrBreak`, on the same premises, concludes that no
inclusion proof finalizes the leg at an on-time batch unless that proof or the absence
proof carries a located break.  The padding instance at the pin,
`Contracts.Timeout.PaddingTimeoutLocatesAbsenceBreak`, is the deployed-branch counterpart of
`History.Properties.PaddingReclaimRedeemsDeliveredLeg`.
`Contracts.Timeout.AcceptedTimeoutMeansMissedDeadlineOrBreak` runs the END branch with the
last-batch proof instead (`Contracts.Timeout.LastBatchAccepted`, over
`Contracts.Timeout.RootBacking`; see the Correction notes on both).

The located break is `Contracts.InteropCommitmentTree.TreeRootBreak` on the submitted
reclaim proof; its `paddingHit` case is the padding forgery.

**This file is definitions only.**  Results: `../Properties/StaleSnapshotFaithful.lean`.
-/

namespace AttackVectors.StaleSnapshotFaithful

open IMTAbstract Contracts.InteropCommitmentTree

/-- The contract run `setup; insert 2 (low 0)`, idle afterwards: value `2` is committed
at snapshot 1, and value `1` is never committed. -/
def oneInsertRun : ℕ → Tree :=
  fun n => if n = 0 then setup else insert setup 2 0

/-- The `FullMerkle` heights along `oneInsertRun`: one leaf at height 0, two at height 1. -/
def oneInsertRunHeight : ℕ → ℕ :=
  fun n => if n = 0 then 0 else 1

/-- Settlement timestamps along `oneInsertRun`: snapshots 0 and 1 settle at time 0, every
later one at time 1.  Monotone. -/
def oneInsertRunTime : ℕ → UInt256 :=
  fun n => if n ≤ 1 then 0 else 1

end AttackVectors.StaleSnapshotFaithful
