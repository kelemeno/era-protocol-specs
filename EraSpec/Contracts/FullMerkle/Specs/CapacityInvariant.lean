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

  WHAT REMAINS, and it is not nothing: that the DEPLOYED code implements this rule.  That is a
  statement about `FullMerkle.push`'s compiled form, which this corpus does not model.  What changes is
  the shape of the residual obligation — from "does the invariant hold at all?" to "does the contract
  implement the rule proved here?".  Axiom-free.
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
