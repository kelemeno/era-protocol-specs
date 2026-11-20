import Mathlib.Tactic


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/CapacityInvariant.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  THE CAPACITY INVARIANT — the growth RULE is correct.

  `TreeShape.capacity_overflow_forges_root` proves `hcap : leafCount ≤ 2 ^ height` indispensable: drop
  it and a forged root exists.  Part D records that nothing in the corpus supplies it — the deployed
  system maintains it structurally, in `FullMerkle.sol`'s push:

      if (index == 1 << self._height) {
          uint256 newHeight = self._height.uncheckedInc();
          self._height = newHeight;
          …
      }

  This file closes the ABSTRACT half of that gap: it models the rule and proves the invariant is
  preserved, from a genesis tree, for any number of pushes.  So `hcap` is not merely plausible — the
  growth rule is provably the right one.

  Source: era-contracts `draft/v0.35.0` `b17415d20`, `common/libraries/FullMerkle.sol`:
  `index = _leafNumber++` (:43) and the growth branch `index == 1 << _height` (:45-52).  The
  statement-by-statement transcription of `pushNewLeaf` (topic `CachedNodes`) moves
  `(_leafNumber, _height)` by `push` below (`Properties.PushNewLeafComputesRoot`).  What is not
  proved is that compiled code executes that transcription.  The `uint256` wrap of
  `1 << _height` (from `_height = 256`, more than `2^255` leaves) does not change the growth
  test's outcome (`CachedNodes`'s model boundary).  Axiom-free.
-/

namespace AttackVectors.CapacityInvariant


/-- A Merkle tree's shape: how many leaves it holds and how tall it is. -/
structure TreeDims where
  count : ℕ
  height : ℕ
deriving DecidableEq


/-- The capacity invariant every `hcap` hypothesis in this corpus asserts. -/
def Cap (d : TreeDims) : Prop := d.count ≤ 2 ^ d.height


/-- `FullMerkle.push`'s rule: append a leaf, growing the height exactly when the new leaf's index has
reached the current capacity. -/
def push (d : TreeDims) : TreeDims :=
  if d.count = 2 ^ d.height then ⟨d.count + 1, d.height + 1⟩ else ⟨d.count + 1, d.height⟩


end AttackVectors.CapacityInvariant
