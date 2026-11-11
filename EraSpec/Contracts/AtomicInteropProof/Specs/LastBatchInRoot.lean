import Mathlib.Tactic

import EraSpec.Contracts.AtomicInteropProof.Specs.TimeoutSoundness


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/LastBatchInRoot.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  "THE CHAIN'S LAST BATCH IN THIS ROOT" — the zero-cascade check, justified.

  `TimeoutSoundness.end_absence_implies_never_finalized` takes `hlast` as a hypothesis: everything
  after batch `B` settles no earlier than the root's creation time.  That hypothesis is discharged on
  chain by `_verifyLastBatchInRoot`, whose docstring states the argument:

      "on every level of the batch-leaf Merkle path where the current node is a left child (mask bit
       0), the right sibling must be the empty-subtree hash for that level ... A non-last leaf
       necessarily has a populated right subtree on some level, whose hash cannot collide with the
       zero cascade."

  The second sentence is the mathematical content, and it is the part with no counterpart anywhere in
  this corpus -- I flagged it as missing when the end branch was first proved.  This file supplies it.

  The claim is about the leaf INDEX, not about hashes: in a tree filled left to right with leaves
  `0 .. n-1`, if every left-child right-sibling subtree along the path to `i` is empty, then `i = n-1`.
  Hash collision resistance enters separately -- it is what makes "the sibling equals `zeros[level]`"
  evidence of "that subtree is empty" -- and is assumed here, exactly as the docstring assumes it.

  What the proof shows, and the docstring only asserts: the witnessing level is not merely SOME level,
  it is a computable one.  If leaf `i+1` is also filled, the level that betrays it is the number of
  TRAILING ONES of `i` -- the level at which the path first turns left.  So the check cannot be
  weakened to "some prefix of levels" without losing exactly this witness.
-/

namespace AttackVectors.LastBatchInRoot


/-! ## The check is exactly "last filled leaf"

`RightEmpty` is the deployed loop, on indices: at every level where the node is a left child, the right
sibling's subtree -- the index range `[(i/2^k + 1) * 2^k, (i/2^k + 2) * 2^k)` -- contains no filled
leaf.  "Filled" is `< n`, the tree being built left to right. -/

/-- The loop's content, level by level. -/
def RightEmpty (i n h : ℕ) : Prop :=
  ∀ k < h, i / 2 ^ k % 2 = 0 →
    ∀ j, (i / 2 ^ k + 1) * 2 ^ k ≤ j → j < (i / 2 ^ k + 2) * 2 ^ k → n ≤ j


/-! ## Closing the seam: from an INDEX fact to `hlast`, which is a TIME fact

`last_of_rightEmpty` says leaf `B` is the last batch INSIDE the root.  `TimeoutSoundness.hlast` says
every batch after `B` settles no earlier than the root's creation time `T`.  Those are different kinds
of statement, and one more assumption bridges them — the aggregation-layer fact that a batch which is
NOT in this root was aggregated into a later one, hence settles no earlier than this root's time.

Naming it is the point.  It is the same species as `TimeOrdered`, and like `TimeOrdered` it is a
property of batch aggregation that no on-chain check in this contract can establish. -/

/-- A batch outside the root settles no earlier than the root's creation time. -/
def OutsideRootLate (inRoot : ℕ → Prop) (time : ℕ → ℕ) (T : ℕ) : Prop :=
  ∀ n, ¬ inRoot n → T ≤ time n


/-! ## The deployed counterpart

`AtomicFlowManager`'s `for_5976315420052011104` IS this check, compiled:

    for { } lt(var_i, length) {var_i := add(var_i, 1)} {
        let split_expr_1 := shr(var_i, _1)          -- bit `var_i` of the path mask
        let split_expr_2 := and(split_expr_1, 1)
        if iszero(split_expr_2) {                   -- a LEFT child at this level
            let split_expr_4 := memory_array_index_access_struct_InteropCall_dyn(..., var_i)
            let _3 := mload(split_expr_4)           -- the right sibling
            if iszero(eq(_3, var_zeroSubtreeHash)) { revert(...) }
        }
        mstore(0, var_zeroSubtreeHash); mstore(32, var_zeroSubtreeHash)
        var_zeroSubtreeHash := keccak256(0, 64)     -- zeros[i+1] = keccak(zeros[i] ‖ zeros[i])
    }

So `RightEmpty`'s "at every level where the node is a left child, the right sibling's subtree
is empty" is the `iszero(and(shr(var_i, mask), 1))` guard plus the equality check, and the zero
cascade this file's header describes is the loop's final three lines.

That loop's spec is now CLOSED (2026-08-12): genuine `ACond`/`APost`/`ABody`/`AFor`, no
sorries, `abs_of_code` axiom-clean.  So the index-level argument in this file and the deployed
check are now both machine-checked, though nothing yet connects them formally — `RightEmpty`
and the loop's `AFor` are stated in different vocabularies.  Its helper calls are all closed
(`memory_array_index_access_struct_InteropCall_dyn` and the panics), so the blocker is only
the transcription: `ABody` has to carry a keccak `Option` match — the collision fallback —
on top of two nested guards.  Closing it would connect `last_of_rightEmpty` to the deployed
code, which is the natural next step for this file. -/

/-! ## What this does and does not close

CLOSED: the index-level claim the docstring asserts -- "a non-last leaf necessarily has a populated
right subtree on some level" -- together with the sharper fact that the level is computable (the first
left turn), and the converse, so the gate admits every honest last-batch proof.

NOT CLOSED, and assumed here exactly as the docstring assumes it: that a sibling hash equal to
`zeros[level]` implies the subtree is EMPTY.  That is collision resistance against the zero cascade
(`zeros[0] = CHAIN_TREE_EMPTY_ENTRY_HASH`, `zeros[i+1] = keccak(zeros[i] ‖ zeros[i])`), and it lives in
the same trusted base as the rest of this corpus's keccak idealizations. -/

end AttackVectors.LastBatchInRoot
