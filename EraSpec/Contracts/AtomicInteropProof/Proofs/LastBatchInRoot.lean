import EraSpec.Contracts.AtomicInteropProof.Properties.LastBatchInRoot
import Mathlib.Tactic
import EraSpec.Contracts.AtomicInteropProof.Proofs.TimeoutSoundness


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


/-! ## The arithmetic of the first left turn -/

/-- Splitting a modulus: `a % (2 * d)` is determined by `a / 2` mod `d` together with `a`'s parity. -/
theorem mod_two_mul (a d : ℕ) (hd : 0 < d) :
    Properties.mod_two_mul (a := a) (d := d) (hd := hd) := by
  unfold Properties.mod_two_mul
  rw [Nat.mod_mul]
  omega


/-- **THE FIRST LEFT TURN EXISTS.**  Every index has a level at which its path turns left, namely its
count of trailing ones: below that level the path went right, at it the node is a left child. -/
theorem exists_first_left (i : ℕ) :
    Properties.exists_first_left (i := i) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.even_or_odd' i with ⟨m, rfl | rfl⟩
    · exact ⟨0, by simp [Nat.mod_one], by simp⟩
    · obtain ⟨k, hk1, hk2⟩ := ih m (by omega)
      have hhalf : (2 * m + 1) / 2 = m := by omega
      have := Nat.one_le_two_pow (n := k)
      refine ⟨k + 1, ?_, ?_⟩
      · rw [pow_succ', Nat.mod_mul, hhalf, hk1]
        omega
      · rwa [pow_succ', ← Nat.div_div_eq_div_mul, hhalf]


/-- At the first left turn, the right sibling subtree starts exactly at `i + 1`. -/
theorem right_sibling_starts_at_succ {i k : ℕ}
    (h1 : i % 2 ^ k = 2 ^ k - 1) :
    Properties.right_sibling_starts_at_succ (i := i) (k := k) (h1 := h1) := by
  have := Nat.div_add_mod' i (2 ^ k)
  have := Nat.one_le_two_pow (n := k)
  unfold Properties.right_sibling_starts_at_succ
  rw [add_mul, one_mul]
  omega


/-- **SOUNDNESS OF THE ZERO-CASCADE CHECK.**  If the check passes for leaf `i` in a tree holding
leaves `0 .. n-1`, then `i` IS the last one.  This is what `_verifyLastBatchInRoot` buys, and hence
what discharges `TimeoutSoundness`'s `hlast`: no batch of this chain sits after `B` inside the root. -/
theorem last_of_rightEmpty {i n h : ℕ} (hi : i < n) (hn : n ≤ 2 ^ h)
    (hemp : RightEmpty i n h) :
    Properties.last_of_rightEmpty (i := i) (n := n) (h := h) (hi := hi) (hn := hn) (hemp := hemp) := by
  by_contra hne
  have hgt : i + 1 < n := by omega
  obtain ⟨k, hk1, hk2⟩ := exists_first_left i
  have hstart : (i / 2 ^ k + 1) * 2 ^ k = i + 1 := right_sibling_starts_at_succ hk1
  have hd : 0 < 2 ^ k := by positivity
  have hsplit : (i / 2 ^ k + 2) * 2 ^ k = (i / 2 ^ k + 1) * 2 ^ k + 2 ^ k := by ring
  -- the witnessing level lies inside the path: otherwise `i + 1` would already fill the tree
  have hklt : k < h := by
    have : 2 ^ k ≤ i + 1 := (Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans hstart.le
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by omega)
  -- leaf `i + 1` is filled and sits in the right sibling's range, contradicting the check
  have := hemp k hklt hk2 (i + 1) hstart.le (by omega)
  omega


/-- **AND THE CHECK IS NECESSARY, NOT JUST SUFFICIENT.**  The last filled leaf does satisfy it, so an
honest prover can always produce the witness -- the gate does not lock out legitimate end-branch
timeouts. -/
theorem rightEmpty_of_last {i h : ℕ} :
    Properties.rightEmpty_of_last (i := i) (h := h) := by
  intro k _ _ j hj _
  have := Nat.div_add_mod' i (2 ^ k)
  have := Nat.mod_lt i (by positivity : 0 < 2 ^ k)
  rw [add_mul, one_mul] at hj
  omega


/-- **THE BRIDGE.**  Last-in-root (an index fact, from the zero-cascade check) plus aggregation
ordering (a time fact, assumed) gives exactly `TimeoutSoundness`'s `hlast`. -/
theorem hlast_of_last_in_root {inRoot : ℕ → Prop} {time : ℕ → ℕ} {T B : ℕ}
    (hlastIdx : ∀ m, inRoot m → m ≤ B)
    (hout : OutsideRootLate inRoot time T) :
    Properties.hlast_of_last_in_root (inRoot := inRoot) (time := time) (T := T) (B := B) (hlastIdx := hlastIdx) (hout := hout) :=
  fun n hn => hout n (fun hin => absurd (hlastIdx n hin) (by omega))


/-- The zero-cascade check supplies `hlastIdx` when the root holds batches `0 .. n-1`. -/
theorem lastIdx_of_rightEmpty {i n h : ℕ} (hi : i < n) (hn : n ≤ 2 ^ h)
    (hemp : RightEmpty i n h) :
    Properties.lastIdx_of_rightEmpty (i := i) (n := n) (h := h) (hi := hi) (hn := hn) (hemp := hemp) := by
  have := last_of_rightEmpty hi hn hemp
  omega


/-- **THE WHOLE END-BRANCH CHAIN, COMPOSED.**  On-chain zero-cascade check ⇒ `B` is the last batch in
the root ⇒ (with aggregation ordering) `hlast` ⇒ the value is absent from every in-time batch, i.e. the
leg can never finalize.  Every hypothesis is either an on-chain check or a named assumption; nothing is
left implicit. -/
theorem end_branch_from_onchain_check {H : AttackVectors.TimeoutSoundness.BatchHistory} {time : ℕ → ℕ}
    (hao : AttackVectors.TimeoutSoundness.AppendOnly H)
    {B nBatches hDepth D T : ℕ} {v : UInt256}
    (htime : time = H.time)
    (hroot : D < T)
    (hin : B < nBatches) (hcap : nBatches ≤ 2 ^ hDepth)
    (hemp : RightEmpty B nBatches hDepth)
    (hout : OutsideRootLate (· < nBatches) time T)
    (habsent : v ∉ H.endSet B) :
    Properties.end_branch_from_onchain_check (H := H) (time := time) (hao := hao) (B := B) (nBatches := nBatches) (hDepth := hDepth) (D := D) (T := T) (v := v) (htime := htime) (hroot := hroot) (hin := hin) (hcap := hcap) (hemp := hemp) (hout := hout) (habsent := habsent) := by
  subst htime
  exact AttackVectors.TimeoutSoundness.end_absence_implies_never_finalized' hao hroot
    (hlast_of_last_in_root (lastIdx_of_rightEmpty hin hcap hemp) hout) habsent


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
