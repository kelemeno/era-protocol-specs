import Mathlib.Tactic
import EraSpec.AttackVectors.TimeoutSoundness

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
theorem mod_two_mul (a d : ℕ) (hd : 0 < d) : a % (2 * d) = 2 * (a / 2 % d) + a % 2 := by
  have hpar : a % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hmd : a / 2 % d < d := Nat.mod_lt _ hd
  have hlt : 2 * (a / 2 % d) + a % 2 < 2 * d := by omega
  have hsmall : a % 2 % (2 * d) = a % 2 := Nat.mod_eq_of_lt (by omega)
  have key : 2 * (a / 2) % (2 * d) = 2 * (a / 2 % d) := Nat.mul_mod_mul_left 2 (a / 2) d
  calc a % (2 * d)
      = (2 * (a / 2) + a % 2) % (2 * d) := by rw [Nat.div_add_mod]
    _ = (2 * (a / 2) % (2 * d) + a % 2 % (2 * d)) % (2 * d) := by rw [Nat.add_mod]
    _ = (2 * (a / 2 % d) + a % 2) % (2 * d) := by rw [key, hsmall]
    _ = 2 * (a / 2 % d) + a % 2 := Nat.mod_eq_of_lt hlt

/-- **THE FIRST LEFT TURN EXISTS.**  Every index has a level at which its path turns left, namely its
count of trailing ones: below that level the path went right, at it the node is a left child. -/
theorem exists_first_left (i : ℕ) : ∃ k, i % 2 ^ k = 2 ^ k - 1 ∧ i / 2 ^ k % 2 = 0 := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    rcases Nat.even_or_odd i with he | ho
    · exact ⟨0, by simp [Nat.mod_one], by simpa [Nat.even_iff] using he⟩
    · obtain ⟨m, hm⟩ := ho
      have hmlt : m < i := by omega
      obtain ⟨k, hk1, hk2⟩ := ih m hmlt
      refine ⟨k + 1, ?_, ?_⟩
      · have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        have hd : 0 < 2 ^ k := Nat.pos_pow_of_pos _ (by norm_num)
        rw [hpow, mod_two_mul i _ hd]
        have hhalf : i / 2 = m := by omega
        have hpar : i % 2 = 1 := by omega
        rw [hhalf, hk1, hpar]
        have : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
      · have hpow : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
        have hhalf : i / 2 = m := by omega
        rw [hpow, ← Nat.div_div_eq_div_mul, hhalf]
        exact hk2

/-- At the first left turn, the right sibling subtree starts exactly at `i + 1`. -/
theorem right_sibling_starts_at_succ {i k : ℕ}
    (h1 : i % 2 ^ k = 2 ^ k - 1) : (i / 2 ^ k + 1) * 2 ^ k = i + 1 := by
  have hd : 0 < 2 ^ k := by positivity
  have h2 : i % 2 ^ k + 1 = 2 ^ k := by omega
  calc (i / 2 ^ k + 1) * 2 ^ k
      = 2 ^ k * (i / 2 ^ k) + 2 ^ k := by ring
    _ = 2 ^ k * (i / 2 ^ k) + (i % 2 ^ k + 1) := by rw [h2]
    _ = (2 ^ k * (i / 2 ^ k) + i % 2 ^ k) + 1 := by ring
    _ = i + 1 := by rw [Nat.div_add_mod]

/-! ## The check is exactly "last filled leaf"

`RightEmpty` is the deployed loop, on indices: at every level where the node is a left child, the right
sibling's subtree -- the index range `[(i/2^k + 1) * 2^k, (i/2^k + 2) * 2^k)` -- contains no filled
leaf.  "Filled" is `< n`, the tree being built left to right. -/

/-- The loop's content, level by level. -/
def RightEmpty (i n h : ℕ) : Prop :=
  ∀ k < h, i / 2 ^ k % 2 = 0 →
    ∀ j, (i / 2 ^ k + 1) * 2 ^ k ≤ j → j < (i / 2 ^ k + 2) * 2 ^ k → n ≤ j

/-- **SOUNDNESS OF THE ZERO-CASCADE CHECK.**  If the check passes for leaf `i` in a tree holding
leaves `0 .. n-1`, then `i` IS the last one.  This is what `_verifyLastBatchInRoot` buys, and hence
what discharges `TimeoutSoundness`'s `hlast`: no batch of this chain sits after `B` inside the root. -/
theorem last_of_rightEmpty {i n h : ℕ} (hi : i < n) (hn : n ≤ 2 ^ h)
    (hemp : RightEmpty i n h) : n = i + 1 := by
  by_contra hne
  have hgt : i + 1 < n := by omega
  obtain ⟨k, hk1, hk2⟩ := exists_first_left i
  have hstart : (i / 2 ^ k + 1) * 2 ^ k = i + 1 := right_sibling_starts_at_succ hk1
  have hd : 0 < 2 ^ k := by positivity
  -- the witnessing level lies inside the path: otherwise `i + 1` would already fill the tree
  have hklt : k < h := by
    by_contra hkh
    have hle : (2 : ℕ) ^ h ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hk_le : (2 : ℕ) ^ k ≤ i + 1 := by
      calc (2 : ℕ) ^ k = 1 * 2 ^ k := (one_mul _).symm
        _ ≤ (i / 2 ^ k + 1) * 2 ^ k := Nat.mul_le_mul_right _ (Nat.le_add_left 1 _)
        _ = i + 1 := hstart
    omega
  -- leaf `i + 1` is filled and sits in the right sibling's range, contradicting the check
  have hub : i + 1 < (i / 2 ^ k + 2) * 2 ^ k := by
    have hsplit : (i / 2 ^ k + 2) * 2 ^ k = (i / 2 ^ k + 1) * 2 ^ k + 2 ^ k := by ring
    rw [hsplit, hstart]
    omega
  have := hemp k hklt hk2 (i + 1) (le_of_eq hstart) hub
  omega

/-- **AND THE CHECK IS NECESSARY, NOT JUST SUFFICIENT.**  The last filled leaf does satisfy it, so an
honest prover can always produce the witness -- the gate does not lock out legitimate end-branch
timeouts. -/
theorem rightEmpty_of_last {i h : ℕ} : RightEmpty i (i + 1) h := by
  intro k _ _ j hj _
  have hd : 0 < 2 ^ k := by positivity
  have h1 : i % 2 ^ k < 2 ^ k := Nat.mod_lt _ hd
  have hlt : i < (i / 2 ^ k + 1) * 2 ^ k := by
    calc i = 2 ^ k * (i / 2 ^ k) + i % 2 ^ k := (Nat.div_add_mod i (2 ^ k)).symm
      _ < 2 ^ k * (i / 2 ^ k) + 2 ^ k := Nat.add_lt_add_left h1 _
      _ = (i / 2 ^ k + 1) * 2 ^ k := by ring
  exact lt_of_lt_of_le hlt hj

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

/-- **THE BRIDGE.**  Last-in-root (an index fact, from the zero-cascade check) plus aggregation
ordering (a time fact, assumed) gives exactly `TimeoutSoundness`'s `hlast`. -/
theorem hlast_of_last_in_root {inRoot : ℕ → Prop} {time : ℕ → ℕ} {T B : ℕ}
    (hlastIdx : ∀ m, inRoot m → m ≤ B)
    (hout : OutsideRootLate inRoot time T) :
    ∀ n, B < n → T ≤ time n :=
  fun n hn => hout n (fun hin => absurd (hlastIdx n hin) (by omega))

/-- The zero-cascade check supplies `hlastIdx` when the root holds batches `0 .. n-1`. -/
theorem lastIdx_of_rightEmpty {i n h : ℕ} (hi : i < n) (hn : n ≤ 2 ^ h)
    (hemp : RightEmpty i n h) : ∀ m, m < n → m ≤ i := by
  intro m hm
  have := last_of_rightEmpty hi hn hemp
  omega

/-- **THE WHOLE END-BRANCH CHAIN, COMPOSED.**  On-chain zero-cascade check ⇒ `B` is the last batch in
the root ⇒ (with aggregation ordering) `hlast` ⇒ the value is absent from every in-time batch, i.e. the
leg can never finalize.  Every hypothesis is either an on-chain check or a named assumption; nothing is
left implicit. -/
theorem end_branch_from_onchain_check
    {H : AttackVectors.TimeoutSoundness.BatchHistory} {time : ℕ → ℕ}
    (hao : AttackVectors.TimeoutSoundness.AppendOnly H)
    {B nBatches hDepth D T : ℕ} {v : UInt256}
    (htime : time = H.time)
    (hroot : D < T)
    (hin : B < nBatches) (hcap : nBatches ≤ 2 ^ hDepth)
    (hemp : RightEmpty B nBatches hDepth)
    (hout : OutsideRootLate (· < nBatches) time T)
    (habsent : v ∉ H.endSet B) :
    ∀ B' : ℕ, H.time B' ≤ D → v ∉ H.endSet B' := by
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
