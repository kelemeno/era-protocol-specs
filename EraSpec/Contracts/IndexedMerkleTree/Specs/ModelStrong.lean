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

## What the source does (era-contracts `c67894b9`)

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
`Contracts.InteropCommitmentTree.Properties.PaddingCollisionRefundsDeliveredLeg`
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
