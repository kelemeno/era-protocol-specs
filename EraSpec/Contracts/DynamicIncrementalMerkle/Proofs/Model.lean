import EraSpec.Contracts.DynamicIncrementalMerkle.Properties.Model
import EraSpec.Contracts.FullMerkle.Proofs.Model
import EraSpec.Contracts.Merkle.Proofs.Verifier

/-!
# Proofs: the storage `DynamicIncrementalMerkle` computes the fold at its minimal height

Proofs of `EraSpec.Contracts.DynamicIncrementalMerkle.Properties.Model`.

The one real induction is `pushLoop_spec`, over the iterations of `push`'s loop for the leaf at
index `n = |L|`.  At level `i` the loop's current hash is the append path node
`appendPath h z L x i` (the level-`i` node above the new leaf, `MerkleSpec`'s M-B), and the
`updatedSides` flag is false exactly when the low `i` bits of `n` are all set.  Below `i`, `_sides`
already satisfies the invariant for `L ++ [x]`; from `i` up it still satisfies the one for `L`.
The two facts that make the induction go through are arithmetic:

* at a right child the saved side is the completed left node (the old invariant), which is the
  sibling `appendPath` combines with;
* `(n + 1) / 2^i` is `n / 2^i + 1` when the low `i` bits of `n` are all set, and `n / 2^i`
  otherwise (`succ_div_pow`).  So the new invariant constrains level `i` either at the first left
  turn, which is the one write the fork makes, or at a right child, where the old value is still
  the right one.

The loop lemma does not depend on the write policy (`guarded`), which is `OzEquivalent`.
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec MerkleSpec.Verifier

/-! ## List toolkit -/

private lemma getD_append_left' {A B : List UInt256} {m : ℕ} (hm : m < A.length) (d : UInt256) :
    (A ++ B).getD m d = A.getD m d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

private lemma getD_append_right' {A B : List UInt256} {m : ℕ} (hm : A.length ≤ m)
    (d : UInt256) : (A ++ B).getD m d = B.getD (m - A.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_append_right hm]

private lemma getD_take' {A : List UInt256} {m q : ℕ} (hm : m < q) (d : UInt256) :
    (A.take q).getD m d = A.getD m d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hm]

private lemma getD_set_ne' {A : List UInt256} {i j : ℕ} (hij : i ≠ j) (v d : UInt256) :
    (A.set i v).getD j d = A.getD j d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set, ite_eq_right hij]

private lemma getD_set_self' {A : List UInt256} {i : ℕ} (hi : i < A.length) (v d : UInt256) :
    (A.set i v).getD i d = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, ite_eq_left rfl, ite_eq_left hi, Option.getD_some]

private lemma getD_map_range {f : ℕ → UInt256} {n m : ℕ} (hm : m < n) (d : UInt256) :
    ((List.range n).map f).getD m d = f m := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm]
  rfl

private lemma range_succ_map (f : ℕ → UInt256) (n : ℕ) :
    (List.range (n + 1)).map f = (List.range n).map f ++ [f n] := by
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-! ## Arithmetic on the leaf index -/

private lemma div_two_pow_succ' (a l : ℕ) : a / 2 ^ l / 2 = a / 2 ^ (l + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- The low `i + 1` bits of `n` are all set iff the low `i` are and bit `i` is. -/
private lemma allOnes_succ (n i : ℕ) :
    n % 2 ^ (i + 1) = 2 ^ (i + 1) - 1 ↔ n % 2 ^ i = 2 ^ i - 1 ∧ n / 2 ^ i % 2 = 1 := by
  rw [Nat.mod_pow_succ, pow_succ]
  have hr : n % 2 ^ i < 2 ^ i := Nat.mod_lt _ (Nat.two_pow_pos i)
  have hp := Nat.two_pow_pos i
  rcases (by omega : n / 2 ^ i % 2 = 0 ∨ n / 2 ^ i % 2 = 1) with hb | hb
  · rw [hb]; omega
  · rw [hb]; omega

/-- **Appending one leaf moves the level-`i` index by one exactly when the low `i` bits of the
old count are all set.** -/
private lemma succ_div_pow (n i : ℕ) :
    (n + 1) / 2 ^ i = n / 2 ^ i + if n % 2 ^ i = 2 ^ i - 1 then 1 else 0 := by
  have hp := Nat.two_pow_pos i
  have hr := Nat.mod_lt n hp
  have hdec : n + 1 = (n % 2 ^ i + 1) + 2 ^ i * (n / 2 ^ i) := by
    have := Nat.mod_add_div n (2 ^ i); omega
  rw [hdec, Nat.add_mul_div_left _ _ hp]
  by_cases hm : n % 2 ^ i = 2 ^ i - 1
  · rw [ite_eq_left hm, show n % 2 ^ i + 1 = 2 ^ i from by omega, Nat.div_self hp]
    have := Nat.mod_add_div n (2 ^ i)
    omega
  · rw [ite_eq_right hm, Nat.div_eq_of_lt (by omega)]
    have := Nat.mod_add_div n (2 ^ i)
    omega

private lemma succ_div_pow_of_allOnes {n i : ℕ} (h : n % 2 ^ i = 2 ^ i - 1) :
    (n + 1) / 2 ^ i = n / 2 ^ i + 1 := by
  rw [succ_div_pow, ite_eq_left h]

private lemma succ_div_pow_of_not_allOnes {n i : ℕ} (h : ¬ n % 2 ^ i = 2 ^ i - 1) :
    (n + 1) / 2 ^ i = n / 2 ^ i := by
  rw [succ_div_pow, ite_eq_right h, Nat.add_zero]

/-! ## The tree over `L ++ [x]`, read through `levels_append` -/

/-- The new leaf's level-`i` path node is entry `n / 2^i` of the new level. -/
private lemma levels_append_at_path (h : Hash) (z : UInt256) (L : List UInt256) (x : UInt256)
    (i : ℕ) :
    (levels h z (L ++ [x]) i).getD (L.length / 2 ^ i) (zeros h z i) = appendPath h z L x i := by
  rw [levels_append h z L x i]
  have hlen : ((levels h z L i).take (L.length / 2 ^ i)).length = L.length / 2 ^ i := by
    rw [List.length_take]
    exact Nat.min_eq_left (div_le_levels_length h z L i)
  rw [getD_append_right' hlen.le, hlen, Nat.sub_self]
  rfl

/-- Entries left of the new leaf's path are unchanged. -/
private lemma levels_append_left (h : Hash) (z : UInt256) (L : List UInt256) (x : UInt256)
    (i m : ℕ) (hm : m < L.length / 2 ^ i) (d : UInt256) :
    (levels h z (L ++ [x]) i).getD m d = (levels h z L i).getD m d := by
  rw [levels_append h z L x i]
  have hlen : ((levels h z L i).take (L.length / 2 ^ i)).length = L.length / 2 ^ i := by
    rw [List.length_take]
    exact Nat.min_eq_left (div_le_levels_length h z L i)
  rw [getD_append_left' (by omega), getD_take' hm]

/-- When the new leaf still fits the height, its top path node is the new root. -/
private lemma appendPath_top (h : Hash) (z : UInt256) (L : List UInt256) (x : UInt256) (H : ℕ)
    (hcap : L.length + 1 ≤ 2 ^ H) :
    appendPath h z L x H = rootOf h z (L ++ [x]) H := by
  rw [rootOf, levels_append h z L x H, Nat.div_eq_of_lt (by omega), List.take_zero,
    List.nil_append]
  rfl

/-- The root at a height is the single top entry: the fold at `H` is entry 0 of level `H`. -/
private lemma rootOf_eq_getD_zero (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) :
    rootOf h z L H = (levels h z L H).getD 0 (zeros h z H) := by
  rw [rootOf, getD_zero_headD]

/-- One level above a tree that fits its height, the fold pairs the old root with the level
zero. -/
private lemma rootOf_succ (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ)
    (hcap : L.length ≤ 2 ^ H) :
    rootOf h z L (H + 1) = h (rootOf h z L H) (zeros h z H) := by
  by_cases hne : L = []
  · subst hne
    simp [rootOf, levels_nil]
  · have hn : L.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hne
    rw [rootOf, levels_succ, levels_height_singleton h z L H hn hcap]
    rfl

/-! ## The loop of `push` -/

/-- The invariant the new storage must meet at level `l`, for the tree over `L ++ [x]` (whose
count is `n + 1`). -/
private def NewF (h : Hash) (z : UInt256) (L : List UInt256) (x : UInt256) (sd : List UInt256)
    (l : ℕ) : Prop :=
  (L.length + 1) / 2 ^ l % 2 = 1 → sd.getD l 0 = frontierNode h z (L ++ [x]) l

/-- The invariant the old storage meets at level `l`, for the tree over `L`. -/
private def OldF (h : Hash) (z : UInt256) (L : List UInt256) (sd : List UInt256) (l : ℕ) :
    Prop :=
  L.length / 2 ^ l % 2 = 1 → sd.getD l 0 = frontierNode h z L l

private lemma frontierNode_append (h : Hash) (z : UInt256) (L : List UInt256) (x : UInt256)
    (l : ℕ) :
    frontierNode h z (L ++ [x]) l
      = (levels h z (L ++ [x]) l).getD ((L.length + 1) / 2 ^ l - 1) (zeros h z l) := by
  rw [frontierNode, List.length_append, List.length_singleton]

/-- **`push`'s loop.**  For the leaf at index `n = |L|`, with `_zeros` correct below the height
`H'` and room for the new leaf: started at level `i` with the path node `appendPath h z L x i`,
the flag false iff the low `i` bits of `n` are all set, the new invariant below `i` and the old one
from `i` up, the loop ends with the top path node, `_sides` of the same length, and the new
invariant at every level below `H'`.  For both write policies. -/
private theorem pushLoop_spec (h : Hash) (z : UInt256) (L : List UInt256) (x : UInt256)
    (H' : ℕ) (guarded : Bool) (zs : List UInt256) (hzs : ∀ l, l < H' → zs.getD l 0 = zeros h z l) :
    ∀ (k i : ℕ) (cur : UInt256) (upd : Bool) (sd : List UInt256),
      i + k = H' → H' ≤ sd.length → cur = appendPath h z L x i →
      (upd = false ↔ L.length % 2 ^ i = 2 ^ i - 1) →
      (∀ l, l < i → NewF h z L x sd l) →
      (∀ l, i ≤ l → l < H' → OldF h z L sd l) →
      (pushLoop h guarded zs k i (L.length / 2 ^ i) cur upd sd).1 = appendPath h z L x H'
        ∧ (pushLoop h guarded zs k i (L.length / 2 ^ i) cur upd sd).2.length = sd.length
        ∧ ∀ l, l < H' → NewF h z L x (pushLoop h guarded zs k i (L.length / 2 ^ i) cur upd sd).2 l := by
  intro k
  induction k with
  | zero =>
    intro i cur upd sd hik _ hcur _ hnew _
    rw [Nat.add_zero] at hik
    subst hik
    exact ⟨hcur, rfl, hnew⟩
  | succ k ih =>
    intro i cur upd sd hik hsd hcur hupd hnew hold
    have hi : i < H' := by omega
    have hzi := hzs i hi
    by_cases hpar : L.length / 2 ^ i % 2 = 0
    · -- a left child: hash with the level zero, and save the node unless one was saved
      have hstep : pushLoop h guarded zs (k + 1) i (L.length / 2 ^ i) cur upd sd
          = pushLoop h guarded zs k (i + 1) (L.length / 2 ^ (i + 1)) (h cur (zs.getD i 0)) true
              (if guarded && upd then sd else sd.set i cur) := by
        rw [pushLoop, ite_eq_left hpar, div_two_pow_succ']
      rw [hstep]
      set sd' := (if guarded && upd then sd else sd.set i cur) with hsd'
      have hlen' : sd'.length = sd.length := by
        rw [hsd']; split_ifs <;> simp
      have hoff : ∀ l, l ≠ i → sd'.getD l 0 = sd.getD l 0 := by
        intro l hl
        rw [hsd']; split_ifs
        · rfl
        · exact getD_set_ne' (Ne.symm hl) cur 0
      have hcur' : h cur (zs.getD i 0) = appendPath h z L x (i + 1) := by
        rw [appendPath_succ, ite_eq_right (by omega), hcur, hzi]
      have hupd' : (true = false ↔ L.length % 2 ^ (i + 1) = 2 ^ (i + 1) - 1) := by
        rw [allOnes_succ]
        constructor
        · intro hc; cases hc
        · rintro ⟨_, hb⟩; omega
      have hnew' : ∀ l, l < i + 1 → NewF h z L x sd' l := by
        intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
        · intro hb
          rw [hoff l (by omega)]
          exact hnew l hl hb
        · subst hl
          intro hb
          by_cases hu : upd = false
          · -- the first left turn: the one write
            have hall := hupd.mp hu
            have hsucc := succ_div_pow_of_allOnes hall
            have hw : sd'.getD l 0 = cur := by
              rw [hsd', hu]
              simp only [Bool.and_false, Bool.false_eq_true, ite_false]
              exact getD_set_self' (by omega) cur 0
            rw [hw, frontierNode_append, hsucc, Nat.add_sub_cancel, levels_append_at_path, hcur]
          · -- a later left turn: the new index is even, so nothing is required
            have hnall : ¬ L.length % 2 ^ l = 2 ^ l - 1 := fun h' => hu (hupd.mpr h')
            rw [succ_div_pow_of_not_allOnes hnall] at hb
            omega
      have hold' : ∀ l, i + 1 ≤ l → l < H' → OldF h z L sd' l := by
        intro l hl1 hl2 hb
        rw [hoff l (by omega)]
        exact hold l (by omega) hl2 hb
      exact ih (i + 1) _ true sd' (by omega) (by omega) hcur' hupd' hnew' hold'
        |>.imp_right (fun h' => ⟨h'.1.trans hlen', h'.2⟩)
    · -- a right child: hash the saved side with the current node
      have hodd : L.length / 2 ^ i % 2 = 1 := by omega
      have hstep : pushLoop h guarded zs (k + 1) i (L.length / 2 ^ i) cur upd sd
          = pushLoop h guarded zs k (i + 1) (L.length / 2 ^ (i + 1)) (h (sd.getD i 0) cur) upd
              sd := by
        rw [pushLoop, ite_eq_right hpar, div_two_pow_succ']
      rw [hstep]
      have hside : sd.getD i 0 = frontierNode h z L i := hold i le_rfl hi hodd
      have hcur' : h (sd.getD i 0) cur = appendPath h z L x (i + 1) := by
        rw [appendPath_succ, ite_eq_left hodd, hside, hcur, frontierNode]
      have hupd' : (upd = false ↔ L.length % 2 ^ (i + 1) = 2 ^ (i + 1) - 1) := by
        rw [allOnes_succ, hupd]
        constructor
        · intro h'; exact ⟨h', hodd⟩
        · intro h'; exact h'.1
      have hnew' : ∀ l, l < i + 1 → NewF h z L x sd l := by
        intro l hl
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
        · exact hnew l hl
        · subst hl
          intro hb
          by_cases hall : L.length % 2 ^ l = 2 ^ l - 1
          · rw [succ_div_pow_of_allOnes hall] at hb
            omega
          · have hsucc := succ_div_pow_of_not_allOnes hall
            have hpos : 0 < L.length / 2 ^ l := by
              rcases Nat.eq_zero_or_pos (L.length / 2 ^ l) with h0 | h0
              · rw [h0] at hodd; simp at hodd
              · exact h0
            rw [hside, frontierNode_append, hsucc, frontierNode,
              levels_append_left h z L x l (L.length / 2 ^ l - 1) (Nat.sub_lt hpos Nat.one_pos)]
      have hold' : ∀ l, i + 1 ≤ l → l < H' → OldF h z L sd l :=
        fun l hl1 hl2 => hold l (by omega) hl2
      exact ih (i + 1) _ upd sd (by omega) hsd hcur' hupd' hnew' hold'

/-! ## `push` -/

/-- `pushWith` on storage with nonempty `_zeros`, with the `let`s spelled out. -/
private lemma pushWith_eq (h : Hash) (guarded : Bool) (S : PushTree) (x : UInt256)
    (hz0 : S.zeros.length ≠ 0) :
    pushWith h guarded S x
      = some ({ next := S.next + 1,
                sides := (pushLoop h guarded
                  (if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).zeros
                  ((if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).zeros.length - 1)
                  0 S.next x false
                  (if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).sides).2.set
                  ((if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).zeros.length - 1)
                  (pushLoop h guarded
                  (if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).zeros
                  ((if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).zeros.length - 1)
                  0 S.next x false
                  (if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).sides).1,
                zeros := (if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).zeros },
              S.next,
              (pushLoop h guarded
                  (if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).zeros
                  ((if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).zeros.length - 1)
                  0 S.next x false
                  (if S.next = 2 ^ (S.zeros.length - 1) then grow h S else S).sides).1) := by
  unfold pushWith
  rw [ite_eq_right hz0]

/-- **The loop and the final write, from the storage the loop starts on.**  If the storage
`S₁` after the growth branch has the zero cascade up to `H'`, `H' + 1` sides, the old invariant
below `H'`, and room for the new leaf, then the loop returns the new root and the final storage
represents `L ++ [x]` at `H'`. -/
private lemma finish (h : Hash) (z : UInt256) (L : List UInt256) (x : UInt256) (H' : ℕ)
    (guarded : Bool) (S₁ : PushTree)
    (hz : S₁.zeros = (List.range (H' + 1)).map (zeros h z)) (hs : S₁.sides.length = H' + 1)
    (hold : ∀ l, l < H' → OldF h z L S₁.sides l) (hcap : L.length + 1 ≤ 2 ^ H') :
    (pushLoop h guarded S₁.zeros H' 0 L.length x false S₁.sides).1 = rootOf h z (L ++ [x]) H'
      ∧ Represents h z (L ++ [x]) H'
          ⟨L.length + 1,
            (pushLoop h guarded S₁.zeros H' 0 L.length x false S₁.sides).2.set H'
              (pushLoop h guarded S₁.zeros H' 0 L.length x false S₁.sides).1,
            S₁.zeros⟩ := by
  have hzs : ∀ l, l < H' → S₁.zeros.getD l 0 = zeros h z l := by
    intro l hl
    rw [hz, getD_map_range (by omega)]
  have hloop := pushLoop_spec h z L x H' guarded S₁.zeros hzs H' 0 x false S₁.sides
    (by omega) (by omega) (by rw [appendPath_zero])
    (by simp [Nat.mod_one]) (fun l hl => absurd hl (Nat.not_lt_zero l)) (fun l _ hl => hold l hl)
  rw [pow_zero, Nat.div_one] at hloop
  obtain ⟨hcur, hlen, hnew⟩ := hloop
  set r := pushLoop h guarded S₁.zeros H' 0 L.length x false S₁.sides
  have hroot : r.1 = rootOf h z (L ++ [x]) H' := by
    rw [hcur, appendPath_top h z L x H' hcap]
  refine ⟨hroot, ?_⟩
  have hne : L ++ [x] ≠ [] := by simp
  refine { next_eq := by simp, capacity := by simpa using hcap, zeros_eq := hz,
           sides_length := by rw [List.length_set, hlen, hs], sides_eq := ?_, top_eq := ?_ }
  · intro l hl hb
    rw [getD_set_ne' (by omega)]
    exact hnew l hl (by simpa using hb)
  · rw [getD_set_self' (by rw [hlen, hs]; omega), hroot, dimRoot, ite_eq_right hne]

/-- Bit `l < H` of `2^H` is clear. -/
private lemma pow_div_pow_mod_two {H l : ℕ} (hl : l < H) : 2 ^ H / 2 ^ l % 2 = 0 := by
  rw [Nat.pow_div (by omega) (by norm_num)]
  obtain ⟨m, hm⟩ : ∃ m, H - l = m + 1 := ⟨H - l - 1, by omega⟩
  rw [hm, pow_succ, Nat.mul_mod_left]

/-- **`push` under either write policy.**  From storage meeting the sides invariant for `L` at
`H` whose root slot holds the fold when `L` is nonempty, `push` returns index `|L|` and the new
fold, and the new storage represents `L ++ [x]` at the new height. -/
private theorem pushWith_spec (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ)
    (S : PushTree) (x : UInt256) (guarded : Bool) (hF : Frontier h z L H S)
    (htop : L ≠ [] → S.sides.getD H 0 = rootOf h z L H) :
    ∃ S' : PushTree,
      pushWith h guarded S x
          = some (S', L.length, rootOf h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H))
        ∧ Represents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) S' := by
  have hzlen : S.zeros.length = H + 1 := by
    rw [hF.zeros_eq, List.length_map, List.length_range]
  rw [pushWith_eq h guarded S x (by omega), hF.next_eq, hzlen, Nat.add_sub_cancel]
  by_cases hg : L.length = 2 ^ H
  · -- the growth branch
    rw [ite_eq_left hg, ite_eq_left hg]
    have hLne : L ≠ [] := by
      intro he; rw [he] at hg; have := Nat.two_pow_pos H; simp at hg; omega
    set S₁ := grow h S with hS₁
    have hz₁ : S₁.zeros = (List.range (H + 1 + 1)).map (zeros h z) := by
      rw [hS₁, grow, hzlen, Nat.add_sub_cancel, hF.zeros_eq, getD_map_range (by omega),
        range_succ_map (zeros h z) (H + 1), zeros_succ]
    have hs₁ : S₁.sides.length = H + 1 + 1 := by
      rw [hS₁, grow]; simp [hF.sides_length]
    have hold : ∀ l, l < H + 1 → OldF h z L S₁.sides l := by
      intro l hl hb
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
      · rw [hg, pow_div_pow_mod_two hl] at hb; omega
      · subst hl
        rw [hS₁, grow]
        simp only
        rw [getD_append_left' (by rw [hF.sides_length]; omega), htop hLne, frontierNode, hg,
          Nat.div_self (Nat.two_pow_pos l), Nat.sub_self, rootOf_eq_getD_zero]
    have hcap : L.length + 1 ≤ 2 ^ (H + 1) := by rw [hg, pow_succ]; have := Nat.two_pow_pos H; omega
    obtain ⟨hroot, hR⟩ := finish h z L x (H + 1) guarded S₁ hz₁ hs₁ hold hcap
    have hk : S₁.zeros.length - 1 = H + 1 := by
      rw [hz₁, List.length_map, List.length_range, Nat.add_sub_cancel]
    rw [hk, hroot]
    rw [hroot] at hR
    exact ⟨_, rfl, hR⟩
  · -- no growth
    rw [ite_eq_right hg, ite_eq_right hg]
    have hold : ∀ l, l < H → OldF h z L S.sides l := fun l hl hb => hF.sides_eq l hl hb
    have hcap : L.length + 1 ≤ 2 ^ H := by have := hF.capacity; omega
    obtain ⟨hroot, hR⟩ := finish h z L x H guarded S hF.zeros_eq hF.sides_length hold hcap
    rw [hzlen, Nat.add_sub_cancel, hroot]
    rw [hroot] at hR
    exact ⟨_, rfl, hR⟩

theorem push_computes_root (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree)
    (x : UInt256) (hR : Represents h z L H S) :
    ∃ S' : PushTree,
      push h S x
          = some (S', L.length, rootOf h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H))
        ∧ Represents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) S' :=
  pushWith_spec h z L H S x true hR.toFrontier
    (fun hne => by rw [hR.top_eq, dimRoot, ite_eq_right hne])

theorem push_after_extend_computes_root (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ)
    (S : PushTree) (x : UInt256) (hR : ExtendedRepresents h z L H S) :
    ∃ S' : PushTree,
      push h S x
          = some (S', L.length, rootOf h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H))
        ∧ Represents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) S' :=
  pushWith_spec h z L H S x true hR.toFrontier (fun _ => hR.top_eq)

theorem push_before_setup_reverts (h : Hash) (S : PushTree) (x : UInt256) (hS : S.zeros = []) :
    push h S x = none := by
  unfold push pushWith
  rw [ite_eq_left (by rw [hS]; rfl)]

/-! ## `setup`, `root`, `height` -/

theorem setup_represents_empty (h : Hash) (z : UInt256) :
    Represents h z [] 0 (setup PushTree.empty z).1 ∧ (setup PushTree.empty z).2 = 0 :=
  ⟨{ next_eq := rfl, capacity := by simp, zeros_eq := by simp [setup, PushTree.empty],
     sides_length := rfl, sides_eq := fun i hi => absurd hi (Nat.not_lt_zero i),
     top_eq := by simp [setup, PushTree.empty, dimRoot] }, rfl⟩

theorem root_is_fold (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree)
    (hR : Represents h z L H S) : root S = some (dimRoot h z L H) ∧ height S = some H := by
  have hl := hR.sides_length
  unfold root height
  rw [ite_eq_right (by omega), ite_eq_right (by omega), hl, Nat.add_sub_cancel, hR.top_eq]
  exact ⟨rfl, rfl⟩

private lemma extended_root (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree)
    (hR : ExtendedRepresents h z L H S) : root S = some (rootOf h z L H) := by
  have hl := hR.sides_length
  unfold root
  rw [ite_eq_right (by omega), hl, Nat.add_sub_cancel, hR.top_eq]

theorem dim_empty_root_is_zero (h : Hash) (z : UInt256) :
    root (setup PushTree.empty z).1 = some 0 ∧ height (setup PushTree.empty z).1 = some 0
      ∧ ∀ (H : ℕ) (S : PushTree), Represents h z [] H S → root S = some 0 := by
  have hR := (setup_represents_empty h z).1
  obtain ⟨hr, hh⟩ := root_is_fold h z [] 0 _ hR
  refine ⟨by rw [hr]; rfl, hh, fun H S hS => ?_⟩
  rw [(root_is_fold h z [] H S hS).1]
  rfl

theorem empty_root_is_not_the_fold (h : Hash) (z : UInt256) (hz : z ≠ 0) :
    rootOf h z [] 0 = z ∧ root (setup PushTree.empty z).1 ≠ some (rootOf h z [] 0) := by
  have hfold : rootOf h z [] 0 = z := rfl
  refine ⟨hfold, ?_⟩
  rw [(dim_empty_root_is_zero h z).1, hfold]
  intro h'
  exact hz (Option.some.inj h').symm

theorem chain_tree_empty_root_is_not_the_fold (h : Hash) :
    root (setup PushTree.empty chainTreeEmptyEntryHash).1 = some 0
      ∧ root (setup PushTree.empty chainTreeEmptyEntryHash).1
          ≠ some (rootOf h chainTreeEmptyEntryHash [] 0) :=
  ⟨(dim_empty_root_is_zero h chainTreeEmptyEntryHash).1,
    (empty_root_is_not_the_fold h chainTreeEmptyEntryHash (by decide)).2⟩

/-! ## The minimal height -/

theorem dimHeight_succ (n : ℕ) :
    dimHeight (n + 1) = if n = 2 ^ dimHeight n then dimHeight n + 1 else dimHeight n := by
  unfold dimHeight
  have h2 : 1 < 2 := by norm_num
  have hle := Nat.le_pow_clog h2 n
  split_ifs with hn
  · apply le_antisymm
    · rw [Nat.clog_le_iff_le_pow h2, pow_succ]
      have := Nat.two_pow_pos (Nat.clog 2 n)
      omega
    · by_contra hlt
      have hle' : Nat.clog 2 (n + 1) ≤ Nat.clog 2 n := by omega
      rw [Nat.clog_le_iff_le_pow h2] at hle'
      omega
  · apply le_antisymm
    · rw [Nat.clog_le_iff_le_pow h2]
      omega
    · rw [Nat.clog_le_iff_le_pow h2]
      have := Nat.le_pow_clog h2 (n + 1)
      omega

theorem dimHeight_minimal (n H : ℕ) (hn : n ≤ 2 ^ H) : dimHeight n ≤ H :=
  (Nat.clog_le_iff_le_pow (by norm_num)).mpr hn

/-! ## Runs -/

private lemma push_inj {h : Hash} {S S' S'' : PushTree} {x : UInt256} {i i' : ℕ}
    {r r' : UInt256} (h₁ : push h S x = some (S', i, r)) (h₂ : push h S x = some (S'', i', r')) :
    S' = S'' ∧ i = i' ∧ r = r' := by
  rw [h₁] at h₂
  obtain ⟨hS, hir⟩ := Prod.mk.inj (Option.some.inj h₂)
  obtain ⟨hi, hr⟩ := Prod.mk.inj hir
  exact ⟨hS, hi, hr⟩

theorem run_represents (h : Hash) (z : UInt256) (L : List UInt256) (S : PushTree)
    (hS : Run h z L S) : Represents h z L (dimHeight L.length) S := by
  induction hS with
  | setup => exact (setup_represents_empty h z).1
  | @push L S S' x i r _ hpush ih =>
    obtain ⟨S'', hp, hR⟩ := push_computes_root h z L _ S x ih
    obtain ⟨hS', _, _⟩ := push_inj hpush hp
    subst hS'
    rw [List.length_append, List.length_singleton, dimHeight_succ]
    exact hR

theorem reachable_height_minimal (h : Hash) (z : UInt256) (L : List UInt256) (S : PushTree)
    (hS : Run h z L S) :
    Represents h z L (dimHeight L.length) S ∧ height S = some (dimHeight L.length)
      ∧ ∀ H', L.length ≤ 2 ^ H' → dimHeight L.length ≤ H' := by
  have hR := run_represents h z L S hS
  exact ⟨hR, (root_is_fold h z L _ S hR).2, fun H' hH' => dimHeight_minimal _ H' hH'⟩

theorem sides_invariant (h : Hash) (z : UInt256) (L : List UInt256) (S : PushTree)
    (hS : Run h z L S) :
    ∀ i, i < dimHeight L.length → L.length / 2 ^ i % 2 = 1 →
      S.sides.getD i 0 = frontierNode h z L i :=
  (run_represents h z L S hS).sides_eq

theorem run_root_is_fold (h : Hash) (z : UInt256) (L : List UInt256) (S : PushTree)
    (hS : Run h z L S) : root S = some (dimRoot h z L (dimHeight L.length)) :=
  (root_is_fold h z L _ S (run_represents h z L S hS)).1

theorem push_returns_stored_root (h : Hash) (z : UInt256) (L : List UInt256) (S S' : PushTree)
    (x : UInt256) (i : ℕ) (r : UInt256) (hS : Run h z L S) (hp : push h S x = some (S', i, r)) :
    i = L.length ∧ root S' = some r ∧ r = rootOf h z (L ++ [x]) (dimHeight (L.length + 1)) := by
  obtain ⟨S'', hp', hR⟩ := push_computes_root h z L _ S x (run_represents h z L S hS)
  obtain ⟨hS', hi, hr⟩ := push_inj hp hp'
  subst hS'
  rw [← dimHeight_succ] at hR hr
  refine ⟨hi, ?_, hr⟩
  rw [(root_is_fold h z _ _ S' hR).1, hr, dimRoot, ite_eq_right (by simp)]

private lemma pushAll_from_run (h : Hash) (z : UInt256) :
    ∀ (xs L₀ : List UInt256) (S₀ : PushTree), Run h z L₀ S₀ →
      ∃ S : PushTree, pushAll h S₀ xs = some S ∧ Run h z (L₀ ++ xs) S := by
  intro xs
  induction xs with
  | nil => intro L₀ S₀ hS; exact ⟨S₀, rfl, by simpa using hS⟩
  | cons x xs ih =>
    intro L₀ S₀ hS
    obtain ⟨S₁, hp, _⟩ := push_computes_root h z L₀ _ S₀ x (run_represents h z L₀ S₀ hS)
    obtain ⟨S, hall, hrun⟩ := ih (L₀ ++ [x]) S₁ (Run.push hS hp)
    refine ⟨S, ?_, by simpa using hrun⟩
    show pushAllWith h true S₀ (x :: xs) = some S
    rw [pushAllWith]
    unfold push at hp
    rw [hp]
    exact hall

theorem push_all_succeeds (h : Hash) (z : UInt256) (L : List UInt256) :
    ∃ S : PushTree, pushAll h (setup PushTree.empty z).1 L = some S ∧ Run h z L S := by
  simpa using pushAll_from_run h z L [] _ Run.setup

/-! ## `extendUntilEnd` -/

/-- At a level `H` the leaves fit, bit `H` of the count is set only when the tree is full. -/
private lemma full_of_odd {n H : ℕ} (hcap : n ≤ 2 ^ H) (hb : n / 2 ^ H % 2 = 1) : n = 2 ^ H := by
  have hp := Nat.two_pow_pos H
  have hle : n / 2 ^ H ≤ 1 := by
    rw [Nat.div_le_iff_le_mul_add_pred hp]; omega
  have hge : 1 ≤ n / 2 ^ H := by
    rcases Nat.eq_zero_or_pos (n / 2 ^ H) with h0 | h0
    · rw [h0] at hb; simp at hb
    · exact h0
  rw [Nat.le_div_iff_mul_le hp] at hge
  omega

/-- **`extendUntilEnd`'s loop.**  From storage in the extended form at height `H` (sides
invariant, root slot `rootOf h z L H`), `k` iterations started at `currentSide = rootOf h z L H`
and `currentZero = zeros h z H` reach the extended form at height `H + k`. -/
private theorem extendLoop_spec (h : Hash) (z : UInt256) (L : List UInt256) :
    ∀ (k H : ℕ) (S : PushTree), Frontier h z L H S → S.sides.getD H 0 = rootOf h z L H →
      ExtendedRepresents h z L (H + k) (extendLoop h k (rootOf h z L H) (zeros h z H) S) := by
  intro k
  induction k with
  | zero => intro H S hF htop; exact ⟨hF, htop⟩
  | succ k ih =>
    intro H S hF htop
    have hside : h (rootOf h z L H) (zeros h z H) = rootOf h z L (H + 1) :=
      (rootOf_succ h z L H hF.capacity).symm
    have hzero : h (zeros h z H) (zeros h z H) = zeros h z (H + 1) := rfl
    rw [extendLoop, hside, hzero]
    have hslen := hF.sides_length
    have hF' : Frontier h z L (H + 1)
        { S with zeros := S.zeros ++ [zeros h z (H + 1)],
                 sides := S.sides ++ [rootOf h z L (H + 1)] } := by
      refine { next_eq := hF.next_eq, capacity := ?_, zeros_eq := ?_, sides_length := ?_,
               sides_eq := ?_ }
      · have := hF.capacity; rw [pow_succ]; omega
      · simp only; rw [hF.zeros_eq, range_succ_map (zeros h z) (H + 1)]
      · simp [hslen]
      · intro l hl hb
        simp only
        rw [getD_append_left' (by omega)]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
        · exact hF.sides_eq l hl hb
        · subst hl
          have hfull := full_of_odd hF.capacity hb
          rw [htop, frontierNode, hfull, Nat.div_self (Nat.two_pow_pos l), Nat.sub_self,
            rootOf_eq_getD_zero]
    have htop' : (S.sides ++ [rootOf h z L (H + 1)]).getD (H + 1) 0 = rootOf h z L (H + 1) := by
      rw [getD_append_right' (by omega), hslen, Nat.sub_self]
      rfl
    have := ih (H + 1) _ hF' htop'
    rwa [show H + 1 + k = H + (k + 1) by omega] at this

/-- **`extendUntilEnd`.**  From storage meeting the sides invariant at `H` whose root slot holds
the fold when nonempty, and, when empty, is at height 0 or already holds the zero cascade. -/
private theorem extendUntilEnd_spec (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ)
    (S : PushTree) (d : ℕ) (hF : Frontier h z L H S)
    (htop : L ≠ [] → S.sides.getD H 0 = rootOf h z L H)
    (hempty : L = [] → H = 0 ∨ S.sides.getD H 0 = rootOf h z L H) :
    ∃ S' : PushTree, extendUntilEnd h S d = some S'
      ∧ ExtendedRepresents h z L (max H (d - 1)) S'
      ∧ root S' = some (rootOf h z L (max H (d - 1))) := by
  have hzlen : S.zeros.length = H + 1 := by
    rw [hF.zeros_eq, List.length_map, List.length_range]
  have hslen := hF.sides_length
  have hz : S.zeros.getD (S.zeros.length - 1) 0 = zeros h z H := by
    rw [hzlen, Nat.add_sub_cancel, hF.zeros_eq, getD_map_range (by omega)]
  set sides₁ := (if S.next = 0 then S.sides.set 0 (zeros h z H) else S.sides) with hsides₁
  have hlen₁ : sides₁.length = H + 1 := by
    rw [hsides₁]; split_ifs <;> simp [hslen]
  have htop₁ : sides₁.getD H 0 = rootOf h z L H := by
    rw [hsides₁]
    split_ifs with hn
    · have hL : L = [] := List.length_eq_zero_iff.mp (hF.next_eq ▸ hn)
      rcases hempty hL with hH | hH
      · subst hH; rw [hL, getD_set_self' (by omega)]; rfl
      · by_cases hH0 : H = 0
        · subst hH0; rw [hL, getD_set_self' (by omega)]; rfl
        · rw [getD_set_ne' (Ne.symm hH0)]; exact hH
    · have hL : L ≠ [] := by
        intro hL; apply hn; rw [hF.next_eq, hL]; rfl
      exact htop hL
  have hF₁ : Frontier h z L H { S with sides := sides₁ } := by
    refine { next_eq := hF.next_eq, capacity := hF.capacity, zeros_eq := hF.zeros_eq,
             sides_length := hlen₁, sides_eq := ?_ }
    intro i hi hb
    simp only
    rw [hsides₁]
    split_ifs with hn
    · rw [hF.next_eq] at hn; rw [hn] at hb; simp at hb
    · exact hF.sides_eq i hi hb
  have hloop := extendLoop_spec h z L (d - sides₁.length) H { S with sides := sides₁ } hF₁ htop₁
  rw [hlen₁, show H + (d - (H + 1)) = max H (d - 1) by omega] at hloop
  refine ⟨_, ?_, hloop, extended_root h z L _ _ hloop⟩
  unfold extendUntilEnd
  rw [ite_eq_right (by omega), ite_eq_right (by omega), hz]
  simp only [← hsides₁]
  rw [hlen₁, Nat.add_sub_cancel, htop₁]

theorem extendUntilEnd_root (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree)
    (d : ℕ) (hR : Represents h z L H S) (hH : L = [] → H = 0) :
    ∃ S' : PushTree, extendUntilEnd h S d = some S'
      ∧ ExtendedRepresents h z L (max H (d - 1)) S'
      ∧ root S' = some (rootOf h z L (max H (d - 1))) :=
  extendUntilEnd_spec h z L H S d hR.toFrontier
    (fun hne => by rw [hR.top_eq, dimRoot, ite_eq_right hne]) (fun hL => Or.inl (hH hL))

theorem extendUntilEnd_again (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree)
    (d : ℕ) (hR : ExtendedRepresents h z L H S) :
    ∃ S' : PushTree, extendUntilEnd h S d = some S'
      ∧ ExtendedRepresents h z L (max H (d - 1)) S'
      ∧ root S' = some (rootOf h z L (max H (d - 1))) :=
  extendUntilEnd_spec h z L H S d hR.toFrontier (fun _ => hR.top_eq) (fun _ => Or.inr hR.top_eq)

theorem reset_is_setup (S : PushTree) (z : UInt256) : reset S z = setup PushTree.empty z := rfl

/-! ## The two write policies -/

theorem oz_equivalent (h : Hash) (z : UInt256) (L : List UInt256) (H : ℕ) (S : PushTree)
    (x : UInt256) (hR : Represents h z L H S) :
    ∃ (S₁ S₂ : PushTree) (r : UInt256),
      push h S x = some (S₁, L.length, r) ∧ ozPush h S x = some (S₂, L.length, r)
        ∧ Represents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) S₁
        ∧ Represents h z (L ++ [x]) (if L.length = 2 ^ H then H + 1 else H) S₂ := by
  have htop : L ≠ [] → S.sides.getD H 0 = rootOf h z L H :=
    fun hne => by rw [hR.top_eq, dimRoot, ite_eq_right hne]
  obtain ⟨S₁, h₁, hR₁⟩ := pushWith_spec h z L H S x true hR.toFrontier htop
  obtain ⟨S₂, h₂, hR₂⟩ := pushWith_spec h z L H S x false hR.toFrontier htop
  exact ⟨S₁, S₂, _, h₁, h₂, hR₁, hR₂⟩

/-- The five-push storages under the two policies, for every hash. -/
private lemma five_pushes (h : Hash) (z a b c d e : UInt256) :
    (pushAll h (setup PushTree.empty z).1 [a, b, c, d, e]).map PushTree.sides
        = some [e, h a b, h (h a b) (h c d), h (h (h a b) (h c d)) (h (h e z) (h z z))]
      ∧ (pushAllWith h false (setup PushTree.empty z).1 [a, b, c, d, e]).map PushTree.sides
        = some [e, h e z, h (h a b) (h c d), h (h (h a b) (h c d)) (h (h e z) (h z z))] := by
  constructor <;>
    simp [pushAll, pushAllWith, pushWith, grow, pushLoop, setup, PushTree.empty]

theorem oz_sides_differ : ∃ (h : Hash) (z a b c d e : UInt256) (S₁ S₂ : PushTree),
    pushAll h (setup PushTree.empty z).1 [a, b, c, d, e] = some S₁
      ∧ pushAllWith h false (setup PushTree.empty z).1 [a, b, c, d, e] = some S₂
      ∧ S₁.sides ≠ S₂.sides ∧ root S₁ = root S₂ := by
  -- the left projection as the node hash: `h a b = a`, so `h a b ≠ h e z` once `a ≠ e`
  let hp : Hash := fun p _ => p
  obtain ⟨h₁, h₂⟩ := five_pushes hp 0 0 0 0 0 1
  obtain ⟨S₁, hS₁, _⟩ := push_all_succeeds hp 0 [0, 0, 0, 0, 1]
  have hS₂ : ∃ S₂, pushAllWith hp false (setup PushTree.empty 0).1 [0, 0, 0, 0, 1] = some S₂ := by
    cases hq : pushAllWith hp false (setup PushTree.empty 0).1 [0, 0, 0, 0, 1] with
    | none => rw [hq] at h₂; cases h₂
    | some S₂ => exact ⟨S₂, rfl⟩
  obtain ⟨S₂, hS₂⟩ := hS₂
  rw [hS₁] at h₁
  rw [hS₂] at h₂
  have e₁ := Option.some.inj h₁
  have e₂ := Option.some.inj h₂
  refine ⟨hp, 0, 0, 0, 0, 0, 1, S₁, S₂, hS₁, hS₂, ?_, ?_⟩
  · rw [e₁, e₂]
    simp [hp]
  · unfold root
    rw [e₁, e₂]
    rfl

/-! ## The misplaced guard -/

private lemma misplaced_two_pushes (h : Hash) (z a b : UInt256) :
    ((misplacedPush h (setup PushTree.empty z).1 a).bind fun r => misplacedPush h r.1 b).map
        (·.2.2) = some (h b b) := by
  simp [misplacedPush, misplacedLoop, grow, setup, PushTree.empty]

theorem misplaced_guard_breaks_root :
    (∀ (h : Hash) (z a b : UInt256),
      ((misplacedPush h (setup PushTree.empty z).1 a).bind fun r => misplacedPush h r.1 b).map
          (·.2.2) = some (h b b))
      ∧ ∃ (h : Hash) (z a b : UInt256), h b b ≠ rootOf h z [a, b] 1 := by
  refine ⟨misplaced_two_pushes, fun p _ => p, 0, 0, 1, ?_⟩
  simp [rootOf, levels, levelUp]

/-! ## Witnesses -/

theorem one_push_witness (h : Hash) (z a : UInt256) :
    pushAll h (setup PushTree.empty z).1 [a] = some ⟨1, [a], [z]⟩
      ∧ Run h z [a] ⟨1, [a], [z]⟩ ∧ root ⟨1, [a], [z]⟩ = some a := by
  have hp : pushAll h (setup PushTree.empty z).1 [a] = some ⟨1, [a], [z]⟩ := by
    simp [pushAll, pushAllWith, pushWith, pushLoop, setup, PushTree.empty]
  obtain ⟨S, hS, hrun⟩ := push_all_succeeds h z [a]
  rw [hp] at hS
  cases hS
  exact ⟨hp, hrun, rfl⟩

theorem two_push_witness (h : Hash) (z a b : UInt256) :
    pushAll h (setup PushTree.empty z).1 [a, b] = some ⟨2, [a, h a b], [z, h z z]⟩
      ∧ Run h z [a, b] ⟨2, [a, h a b], [z, h z z]⟩
      ∧ root ⟨2, [a, h a b], [z, h z z]⟩ = some (h a b) := by
  have hp : pushAll h (setup PushTree.empty z).1 [a, b] = some ⟨2, [a, h a b], [z, h z z]⟩ := by
    simp [pushAll, pushAllWith, pushWith, grow, pushLoop, setup, PushTree.empty]
  obtain ⟨S, hS, hrun⟩ := push_all_succeeds h z [a, b]
  rw [hp] at hS
  cases hS
  exact ⟨hp, hrun, rfl⟩

theorem three_push_witness (h : Hash) (z a b c : UInt256) :
    pushAll h (setup PushTree.empty z).1 [a, b, c]
        = some ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ Run h z [a, b, c] ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩
      ∧ root ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩
          = some (h (h a b) (h c z)) := by
  have hp : pushAll h (setup PushTree.empty z).1 [a, b, c]
      = some ⟨3, [c, h a b, h (h a b) (h c z)], [z, h z z, h (h z z) (h z z)]⟩ := by
    simp [pushAll, pushAllWith, pushWith, grow, pushLoop, setup, PushTree.empty]
  obtain ⟨S, hS, hrun⟩ := push_all_succeeds h z [a, b, c]
  rw [hp] at hS
  cases hS
  exact ⟨hp, hrun, rfl⟩

end Contracts.DynamicIncrementalMerkle

/-! ## Certificates -/

namespace Contracts.DynamicIncrementalMerkle

theorem SetupRepresentsEmpty : Properties.SetupRepresentsEmpty := setup_represents_empty
theorem DimEmptyRootIsZero : Properties.DimEmptyRootIsZero := dim_empty_root_is_zero
theorem EmptyRootIsNotTheFold : Properties.EmptyRootIsNotTheFold := empty_root_is_not_the_fold
theorem ChainTreeEmptyRootIsNotTheFold : Properties.ChainTreeEmptyRootIsNotTheFold :=
  chain_tree_empty_root_is_not_the_fold
theorem PushComputesRoot : Properties.PushComputesRoot := push_computes_root
theorem PushAfterExtendComputesRoot : Properties.PushAfterExtendComputesRoot :=
  push_after_extend_computes_root
theorem PushBeforeSetupReverts : Properties.PushBeforeSetupReverts := push_before_setup_reverts
theorem SidesInvariant : Properties.SidesInvariant := sides_invariant
theorem OzEquivalent : Properties.OzEquivalent := oz_equivalent
theorem OzSidesDiffer : Properties.OzSidesDiffer := oz_sides_differ
theorem MisplacedGuardBreaksRoot : Properties.MisplacedGuardBreaksRoot :=
  misplaced_guard_breaks_root
theorem ReachableHeightMinimal : Properties.ReachableHeightMinimal := reachable_height_minimal
theorem DimHeightSucc : Properties.DimHeightSucc := dimHeight_succ
theorem RootIsFold : Properties.RootIsFold := root_is_fold
theorem RunRootIsFold : Properties.RunRootIsFold := run_root_is_fold
theorem PushReturnsStoredRoot : Properties.PushReturnsStoredRoot := push_returns_stored_root
theorem PushAllSucceeds : Properties.PushAllSucceeds := push_all_succeeds
theorem ExtendUntilEndRoot : Properties.ExtendUntilEndRoot := extendUntilEnd_root
theorem ExtendUntilEndAgain : Properties.ExtendUntilEndAgain := extendUntilEnd_again
theorem ResetIsSetup : Properties.ResetIsSetup := reset_is_setup
theorem OnePushWitness : Properties.OnePushWitness := one_push_witness
theorem TwoPushWitness : Properties.TwoPushWitness := two_push_witness
theorem ThreePushWitness : Properties.ThreePushWitness := three_push_witness

end Contracts.DynamicIncrementalMerkle
