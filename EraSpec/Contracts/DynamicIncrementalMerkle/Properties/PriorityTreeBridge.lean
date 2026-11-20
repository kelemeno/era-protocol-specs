import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.PriorityTreeBridge

/-!
# Properties: the priority tree's `push` is the library's `push`

Statements about `../Specs/PriorityTreeBridge.lean`. Proofs:
`../Proofs/PriorityTreeBridge.lean`. These are model-bridge statements between two Lean
transcriptions of the same code, so none is a headline.
-/

namespace Contracts.DynamicIncrementalMerkle.PriorityTreeBridge

open MerkleSpec

/-- **THE TWO `push` TRANSCRIPTIONS AGREE IN THE `uint256` RANGE.** For every node hash, every
priority-tree storage with fewer than 256 levels (`_zeros.length - 1 < 256`) whose counter can be
incremented (`_nextLeafIndex + 1 < 2^256`), and every leaf: the `PriorityTree` transcription's
`push` reverts exactly when this folder's does (empty `_zeros`), and otherwise both write the same
storage and return the same root. -/
def Properties.PriorityTreePushIsDimPush : Prop :=
  ∀ (h : Hash) (t : Contracts.PriorityTree.Library.PushTree) (leaf : UInt256),
    t.zeros.length - 1 < 256 → t.nextLeafIndex + 1 < Contracts.PriorityTree.Library.wordLimit →
      (Contracts.PriorityTree.Library.PushTree.push h t leaf).map (fun r => (toDim r.1, r.2))
        = (push h (toDim t) leaf).map (fun r => (r.1, r.2.2))

/-- **THE TWO `setup` TRANSCRIPTIONS AGREE.** On every storage and zero value they write the same
storage and return the same value, `bytes32(0)`. -/
def Properties.PriorityTreeSetupIsDimSetup : Prop :=
  ∀ (t : Contracts.PriorityTree.Library.PushTree) (zero : UInt256),
    toDim (Contracts.PriorityTree.Library.PushTree.setup t zero).1 = (setup (toDim t) zero).1
      ∧ (Contracts.PriorityTree.Library.PushTree.setup t zero).2 = (setup (toDim t) zero).2

/-- **THE TWO `root` TRANSCRIPTIONS AGREE WHERE THE SOURCE DOES NOT REVERT.** On storage with
nonempty `_sides`, the `PriorityTree` reading of `root()` is the value this folder's `root` returns. -/
def Properties.PriorityTreeRootIsDimRoot : Prop :=
  ∀ t : Contracts.PriorityTree.Library.PushTree, t.sides ≠ [] →
    root (toDim t) = some (Contracts.PriorityTree.Library.PushTree.root t)

/-- **THE PREMISES ARE MET ON THE PRIORITY TREE AFTER `setup` AND ONE PUSH, AND THE PUSH SUCCEEDS.**
For every node hash, zero value and leaf: on `setup(zero)` over empty storage, both premises of
`PriorityTreePushIsDimPush` hold and the `PriorityTree` `push` does not revert. -/
def Properties.PriorityTreePushIsDimPushWitness : Prop :=
  ∀ (h : Hash) (zero leaf : UInt256),
    let t := (Contracts.PriorityTree.Library.PushTree.setup ⟨0, [], []⟩ zero).1
    t.zeros.length - 1 < 256 ∧ t.nextLeafIndex + 1 < Contracts.PriorityTree.Library.wordLimit
      ∧ (Contracts.PriorityTree.Library.PushTree.push h t leaf).isSome

end Contracts.DynamicIncrementalMerkle.PriorityTreeBridge
