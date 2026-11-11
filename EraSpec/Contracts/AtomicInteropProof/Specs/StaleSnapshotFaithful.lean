import EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRoot

/-!
# Stale-snapshot reclaim, against the absence verifier as deployed

`AttackVectors.StaleSnapshot` models a reclaim witness at snapshot `j` as a leaf
`W ∈ S j` whose window straddles `v`, and reads its theorems as statements about
"an accepted reclaim".  The deployed reclaim gate does not receive a leaf of the
snapshot.  It receives a preimage `ℓ`, an index and a sibling path, and accepts when
`IndexedMerkleTree.verifyNonInclusion` returns `true`:

* `IndexedMerkleTree.sol:47-49` (pinned `c67894b9`): `setup` pads `FullMerkle` with
  `zeroLeafHash = hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0}))`, so every
  empty slot of the tree hashes exactly like the sentinel leaf `{0,0,0}`;
* `IndexedMerkleTree.sol:153-171`: `verifyNonInclusion` checks `_value != 0`,
  `_lowLeaf.value < _value`, `_lowLeaf.nextValue == 0 || _value < _lowLeaf.nextValue`,
  and `Merkle.calculateRootMemory(_lowLeafProof, _lowLeafIndex, hashLeaf(_lowLeaf)) == _root`;
  nothing checks that `_lowLeafIndex` is an occupied slot;
* `AtomicInteropProof.sol:198-205`: this call is the only absence check of the
  timeout gate, on both branches.

So `{0,0,0}` presented at an empty slot is accepted as a low leaf for every nonzero
value, including a delivered one.  That accepted "witness" is not a leaf of the
snapshot, so it is not a `W ∈ S j` witness, and `StaleSnapshot`'s theorems do not
speak about it.  The upgrade tree (`e561b9cc2`) pads with a dedicated
`IMT_EMPTY_LEAF_HASH` instead; the verifier code is unchanged.

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

The located break is `Contracts.InteropCommitmentTree.TreeRootBreak` on the submitted
reclaim proof; its `paddingHit` case is the padding forgery.

**This file is definitions only.**  Results: `../Properties/StaleSnapshotFaithful.lean`.
-/

namespace AttackVectors.StaleSnapshotFaithful

open IMTAbstract Contracts.InteropCommitmentTree

/-- The contract run `setup; insert a (low 0); insert b (low 1)`, idle afterwards.
Snapshot 2 is `threeLeafTree a b`: three leaves, slot 3 empty. -/
def paddedRun (a b : UInt256) : ℕ → Tree :=
  fun n => if n = 0 then setup else if n = 1 then insert setup a 0 else threeLeafTree a b

/-- The `FullMerkle` heights along `paddedRun`: one leaf at height 0, two at height 1,
three at height 2. -/
def paddedRunHeight : ℕ → ℕ :=
  fun n => if n = 0 then 0 else if n = 1 then 1 else 2

/-- Settlement timestamps along `paddedRun`: snapshots 0, 1 and 2 settle at time 0,
every later one at time 1.  Monotone. -/
def paddedRunTime : ℕ → UInt256 :=
  fun n => if n ≤ 2 then 0 else 1

end AttackVectors.StaleSnapshotFaithful
