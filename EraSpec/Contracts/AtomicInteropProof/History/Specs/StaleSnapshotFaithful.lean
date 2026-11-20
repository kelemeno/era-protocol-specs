import EraSpec.Contracts.AtomicInteropProof.Specs.StaleSnapshotFaithful

/-!
# Spec (History): the padding countermodel run at the extraction pin

**History.** This is the record of the H2 padding finding at era-contracts `c67894b9`, not a claim
about `draft/v0.35.0` `b17415d20`. At the pin `IndexedMerkleTree.setup` padded `FullMerkle` with
`hashLeaf(IMTLeaf({0, 0, 0}))`, so every empty slot hashed like the sentinel leaf, and
`verifyNonInclusion` accepted `{0,0,0}` at an empty slot as a low leaf for every nonzero value. At
`b17415d20` `setup` pads with `IMT_EMPTY_LEAF_HASH` (`common/libraries/IndexedMerkleTree.sol:51`,
`common/Config.sol:141`); the verifier (`:154-172`) is unchanged. The current results, with the
padding a parameter, are in `../../Specs/StaleSnapshotFaithful.lean`.

The run below is used only by `History.Properties.PaddingReclaimRedeemsDeliveredLeg`.
-/

namespace AttackVectors.StaleSnapshotFaithful.History

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

end AttackVectors.StaleSnapshotFaithful.History
