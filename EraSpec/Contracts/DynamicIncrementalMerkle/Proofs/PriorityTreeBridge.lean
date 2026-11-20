import EraSpec.Contracts.DynamicIncrementalMerkle.Properties.PriorityTreeBridge

/-!
# Proofs: the priority tree's `push` is the library's `push`

Proofs of `../Properties/PriorityTreeBridge.lean`. The one real step is `foldl_walkStep`: the
`PriorityTree` loop, a `foldl` of `walkStep` over `List.range' i k`, computes what `pushLoop`
computes with `k` iterations left from level `i`.
-/

namespace Contracts.DynamicIncrementalMerkle.PriorityTreeBridge

open MerkleSpec
open Contracts.PriorityTree.Library (wordLimit)
open Contracts.PriorityTree.Library.PushTree (walkStep walk pushZeros pushSides Grows shl1)

/-- The `foldl` loop is the recursive loop, on the hash and on `_sides`. -/
theorem foldl_walkStep (h : Hash) (zs : List UInt256) :
    ∀ (k i : ℕ) (w : Contracts.PriorityTree.Library.PushTree.Walk),
      ((List.range' i k).foldl (walkStep h zs) w).hash
          = (pushLoop h true zs k i w.index w.hash w.updatedSides w.sides).1
        ∧ ((List.range' i k).foldl (walkStep h zs) w).sides
          = (pushLoop h true zs k i w.index w.hash w.updatedSides w.sides).2
  | 0, i, w => by simp [pushLoop]
  | k + 1, i, w => by
    rw [List.range'_succ, List.foldl_cons]
    obtain ⟨h1, h2⟩ := foldl_walkStep h zs k (i + 1) (walkStep h zs w i)
    rw [h1, h2]
    by_cases hp : w.index % 2 = 0
    · constructor <;> simp [walkStep, pushLoop, hp]
    · constructor <;> simp [walkStep, pushLoop, hp]

/-- The priority tree's `walk` is `pushLoop` from level 0 over the grown arrays. -/
theorem walk_eq (h : Hash) (t : Contracts.PriorityTree.Library.PushTree) (leaf : UInt256) :
    (walk h t leaf).hash = (pushLoop h true (pushZeros h t) ((pushZeros h t).length - 1) 0
        t.nextLeafIndex leaf false (pushSides t)).1
      ∧ (walk h t leaf).sides = (pushLoop h true (pushZeros h t) ((pushZeros h t).length - 1) 0
        t.nextLeafIndex leaf false (pushSides t)).2 := by
  have := foldl_walkStep h (pushZeros h t) ((pushZeros h t).length - 1) 0
    ⟨t.nextLeafIndex, leaf, false, pushSides t⟩
  rw [← List.range_eq_range'] at this
  exact this

/-- The growth step: below 256 levels, the `PriorityTree` reading of the growth branch is
`Model`'s. -/
theorem grown_eq (h : Hash) (t : Contracts.PriorityTree.Library.PushTree)
    (hlev : t.zeros.length - 1 < 256) :
    (if t.nextLeafIndex = 2 ^ (t.zeros.length - 1) then grow h (toDim t) else toDim t)
      = ⟨t.nextLeafIndex, pushSides t, pushZeros h t⟩ := by
  have hshl : shl1 (t.zeros.length - 1) = 2 ^ (t.zeros.length - 1) := by
    simp [shl1, hlev]
  by_cases hg : t.nextLeafIndex = 2 ^ (t.zeros.length - 1)
  · have hG : Grows t := by unfold Grows; rw [hshl]; exact hg
    simp [hg, grow, toDim, pushZeros, pushSides, hG]
  · have hG : ¬ Grows t := by unfold Grows; rw [hshl]; exact hg
    simp [hg, toDim, pushZeros, pushSides, hG]

theorem priority_tree_push_is_dim_push : Properties.PriorityTreePushIsDimPush := by
  intro h t leaf hlev hcnt
  by_cases hz : t.zeros.length = 0
  · simp [Contracts.PriorityTree.Library.PushTree.push, push, pushWith, toDim, hz]
  · have hw : ¬ wordLimit ≤ t.nextLeafIndex + 1 := by omega
    have hz' : ¬ (toDim t).zeros.length = 0 := hz
    obtain ⟨hW1, hW2⟩ := walk_eq h t leaf
    have hS := grown_eq h t hlev
    unfold Contracts.PriorityTree.Library.PushTree.push push pushWith
    rw [if_neg hz, if_neg hw, if_neg hz']
    simp only [Option.map_some]
    rw [show (toDim t).next = t.nextLeafIndex from rfl,
      show (toDim t).zeros = t.zeros from rfl, hS, hW1, hW2]
    rfl

theorem priority_tree_setup_is_dim_setup : Properties.PriorityTreeSetupIsDimSetup :=
  fun _ _ => ⟨rfl, rfl⟩

theorem priority_tree_root_is_dim_root : Properties.PriorityTreeRootIsDimRoot := by
  intro t ht
  have hl : t.sides.length ≠ 0 := by simpa using ht
  simp [root, toDim, Contracts.PriorityTree.Library.PushTree.root, hl]

theorem priority_tree_push_is_dim_push_witness : Properties.PriorityTreePushIsDimPushWitness := by
  intro h zero leaf
  refine ⟨by simp [Contracts.PriorityTree.Library.PushTree.setup], ?_, ?_⟩
  · simp [Contracts.PriorityTree.Library.PushTree.setup, wordLimit]
  · simp [Contracts.PriorityTree.Library.PushTree.push, Contracts.PriorityTree.Library.PushTree.setup,
      wordLimit]

/-! ## Certificates -/

theorem PriorityTreePushIsDimPush : Properties.PriorityTreePushIsDimPush :=
  priority_tree_push_is_dim_push

theorem PriorityTreeSetupIsDimSetup : Properties.PriorityTreeSetupIsDimSetup :=
  priority_tree_setup_is_dim_setup

theorem PriorityTreeRootIsDimRoot : Properties.PriorityTreeRootIsDimRoot :=
  priority_tree_root_is_dim_root

theorem PriorityTreePushIsDimPushWitness : Properties.PriorityTreePushIsDimPushWitness :=
  priority_tree_push_is_dim_push_witness

end Contracts.DynamicIncrementalMerkle.PriorityTreeBridge
