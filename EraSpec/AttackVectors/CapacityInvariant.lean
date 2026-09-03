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

/-- The genesis tree satisfies the invariant. -/
theorem cap_genesis : Cap ⟨0, 0⟩ := by
  unfold Cap; norm_num

/-- **THE GROWTH RULE PRESERVES CAPACITY.**  The two branches are tight in different ways: when the
height grows, the new count is `2^h + 1`, which fits `2^(h+1)` with room to spare; when it does not, the
count was STRICTLY below capacity, so incrementing stays within it.

The `if` is therefore doing real work — replacing its condition with anything that fires later would
break the second branch. -/
theorem cap_push {d : TreeDims} (h : Cap d) : Cap (push d) := by
  unfold Cap push at *
  by_cases hfull : d.count = 2 ^ d.height
  · rw [if_pos hfull]
    show d.count + 1 ≤ 2 ^ (d.height + 1)
    rw [hfull, pow_succ]
    have : 1 ≤ 2 ^ d.height := Nat.one_le_two_pow
    omega
  · rw [if_neg hfull]
    show d.count + 1 ≤ 2 ^ d.height
    omega

/-- The height never shrinks. -/
theorem height_mono (d : TreeDims) : d.height ≤ (push d).height := by
  unfold push
  by_cases hfull : d.count = 2 ^ d.height <;> simp [hfull]

/-- Each push adds exactly one leaf. -/
theorem count_succ (d : TreeDims) : (push d).count = d.count + 1 := by
  unfold push
  by_cases hfull : d.count = 2 ^ d.height <;> simp [hfull]

/-- **CAPACITY IS NEVER EXCEEDED.**  From the genesis tree, after any number of pushes, the leaf count
is within capacity — so `hcap` holds at every point of a tree's life, given the contract follows the
rule above. -/
theorem capacity_never_exceeded (n : ℕ) : Cap (push^[n] ⟨0, 0⟩) := by
  induction n with
  | zero => exact cap_genesis
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact cap_push ih

/-- The count after `n` pushes is exactly `n` — so "capacity is never exceeded" is a statement about
every tree size, not only reachable ones. -/
theorem count_after (n : ℕ) : (push^[n] ⟨0, 0⟩).count = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', count_succ, ih]

/-- **THE INVARIANT AT EVERY SIZE.**  Combining the two: a tree grown to `n` leaves by this rule has
height at least `log₂ n`, i.e. `n ≤ 2 ^ height`.  This is the exact form `hcap` is used in. -/
theorem cap_at_size (n : ℕ) : n ≤ 2 ^ (push^[n] ⟨0, 0⟩).height := by
  have h := capacity_never_exceeded n
  unfold Cap at h
  rwa [count_after] at h

end AttackVectors.CapacityInvariant
