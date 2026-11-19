import EraSpec.Contracts.IndexedMerkleTree.Specs.Model

/-!
# Contract spec: the forged padding witness, pinned to the padding leaf

## Why this file exists

`IMTAbstract.Properties.forged_padding_witness_breaks_exclusivity` (`Model`) is meant to show
that the membership premise `W ∈ s` of `present_not_reclaimable` cannot be dropped, and that the
leaf the padding hash stands for, `⟨0, 0⟩`, is the witness an attacker would present.  Its
statement is

    ∃ s v W, SoundState s ∧ v ∈ keys s ∧ W ∉ s ∧ W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

Its parameter `a` does not occur in it and `W` is unconstrained, so it is also met by one fixed
tree built at `1` with the non-padding leaf `⟨0, 2⟩`.  It records that `W ∈ s` cannot be dropped
on SOME sound tree; it says nothing about the padding leaf, about `a`, or about how often the
forged witness is available.

`../Properties/ModelStrong.lean` states the padding-leaf version: in EVERY `GapSound` tree, for
EVERY delivered nonzero value `v`, the leaf `⟨0, 0⟩` is not a member and carries a window
straddling `v`, while no member does.  So the forged witness is available against every delivered
leg of every sound tree, and in particular on every state of a guarded history from genesis once
a leg has been delivered.

## The padding leaf at `b17415d20` and at the interop pin

**Commit.** era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5` (`b17415d20`).  The statements are order theory and hold at every
revision: they show that the membership premise of the exclusivity theorems cannot be dropped.
Whether a deployed absence proof can present the non-member `⟨0, 0⟩` depends on the padding
constant.  At `b17415d20` `setup` pads with `IMT_EMPTY_LEAF_HASH`
(`IndexedMerkleTree.sol:51`, `Config.sol:141`), so presenting it at an empty slot needs a keccak
collision (`Contracts.InteropCommitmentTree.Properties.PaddingHitAtHeadIffEmptyLeafCollision`).

At the interop pin `c67894b9` (History, line numbers of that pin)

`l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol`:

    bytes32 zeroLeafHash = hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0}));  // :47
    self.tree.setup(zeroLeafHash);                                                      // :48
    self.tree.pushNewLeaf(zeroLeafHash);                                                // :49
    self.leaves[0] = IMTLeaf({value: 0, nextIndex: 0, nextValue: 0});                   // :50

The padding constant of the underlying `FullMerkle` tree is the hash of the genesis sentinel
`{0, 0, 0}`.  The first `insert` retargets the sentinel (:96-100), so from then on no real leaf is
`{0, 0, 0}`, but every empty slot still hashes as one.  `verifyNonInclusion` (:153-171) checks
`_lowLeaf.value < _value` (:163-165) and `_lowLeaf.nextValue == 0 || _value < _lowLeaf.nextValue`
(:166-168), then only that `_lowLeaf` hashes to an entry under the root (:170).  For
`_lowLeaf = {0, 0, 0}` the two window checks pass for every nonzero `_value`.  The abstract leaf
`⟨key, nextKey⟩` is `(value, nextValue)`; `nextIndex` is erased.

## Model boundary

Order theory over `Finset AbsLeaf`, as in `Model`.  Whether the padding leaf's hash is accepted
under a published root is the Merkle-level question, answered for the deployed tree by
`Contracts.InteropCommitmentTree.History.Properties.PaddingCollisionRefundsDeliveredLeg`
(`../../L2InteropCommitmentTree/Properties/TreeRoot.lean`).
-/

namespace IMTAbstract.ModelStrong

open Clear

/-- The guarded history that inserts one value `a` into the genesis singleton `{⟨0, 0⟩}` at the
`0 → 1` step and then stays put.  For `a ≠ 0` it is a `GuardedEvolution` from genesis
(`Properties.genesisInsertHistory_guarded`), used to meet the premises of the history-level
statements here and in `ResetAndZeroStrong`. -/
def genesisInsertHistory (a : UInt256) : ℕ → Finset AbsLeaf :=
  fun n => if n = 0 then {⟨0, 0⟩} else imtInsert {⟨0, 0⟩} ⟨0, 0⟩ a

end IMTAbstract.ModelStrong
