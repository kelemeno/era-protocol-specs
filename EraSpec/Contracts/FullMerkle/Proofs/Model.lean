import EraSpec.Contracts.FullMerkle.Properties.Model
import EraSpec.Core.Word


/- EXTRACTED from contracts-formal-verification (`specs/specs/MerkleSpec.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  PURE MERKLE SPEC — the EVM-free Merkle layer of the root-fidelity track
  (ROOT_FIDELITY_BLUEPRINT.md §1.1).

  `FullMerkle`-shaped trees: level `l+1` pairs up level `l` left-to-right,
  and a lone left child at the frontier is combined with the level-`l` zero
  (`_zeros[l]` in the contract) as its right sibling.  Everything is
  parameterized over an abstract two-child hash `h` and base zero `z0`;
  `h` is instantiated per-theorem from the keccak cache downstream (R6) —
  the model has no global pure keccak.

  Main results (tags match the blueprint):
  * M-C — frontier arithmetic: `levels_length` (+ ceiling form), `levels_nil`,
    `levels_length_pos`, `levels_length_le`, `div_le_levels_length`,
    `div_pow_eq_zero`.
  * M-A — `walkPure_update` / `walkPure_update_orig`: the one-path sibling
    walk recomputes the WHOLE tree root of `leaves.set idx x`.  The engine
    `walkPure_levels` is the intermediate-accumulator form (each partial
    walk value = the parent-level entry on the updated path); the off-path
    helper is `levels_set_off_path`.
  * M-B — `rootOf_append`: appending a leaf at the frontier equals the walk
    from index `leaves.length` whose sibling stream reads the OLD tree via
    `getD` with default `zeros l` — out-of-frontier right siblings collapse
    to the `_zeros` read automatically, matching `stepEdge` and the
    `pushNewLeaf` walk (blueprint §0.2, last bullet).  List surgery in
    `levels_append`; walk bridge in `walkPure_appendPath`.

  Sibling indices and path indices are kept in `ℕ` (`idx / 2^l`, `sibIdx`);
  bridging to `Fin`/UInt256 `shiftRight` is deliberately left to the
  concrete layer (blueprint §4.7).

  * M-D — `rootOf_inj_of_h_inj`: pointwise injectivity of `rootOf` from
    pair-injectivity of `h` (the tree-shaped generalization of
    `foldRoot_binding`).  Engine `levelUp_inj` (equal-width levels) lifts
    through `levels_inj`; `levels_height_singleton` collapses a non-full
    tree's top level to its root.  Node-hash injectivity is discharged
    downstream from keccak injectivity (R6).

  Pure list/arithmetic reasoning — no EVM semantics, no extra axioms.
-/

namespace MerkleSpec


open Clear


/-! ## List `getD` toolkit

Small self-contained helpers over `List.getD`, proved from first principles
to stay independent of lemma-name drift. -/

private theorem getD_nil' (n : ℕ) (d : UInt256) : ([] : List UInt256).getD n d = d := rfl


private theorem getD_cons_zero' (a : UInt256) (t : List UInt256) (d : UInt256) :
    (a :: t).getD 0 d = a := rfl


private theorem getD_cons_succ' (a : UInt256) (t : List UInt256) (n : ℕ) (d : UInt256) :
    (a :: t).getD (n + 1) d = t.getD n d := rfl


/-- In-range `getD` does not depend on the default. -/
private theorem getD_congr : ∀ (L : List UInt256) (n : ℕ) (d₁ d₂ : UInt256),
    n < L.length → L.getD n d₁ = L.getD n d₂
  | [], _, _, _, hn => absurd hn (by simp)
  | _ :: _, 0, _, _, _ => rfl
  | _ :: t, n + 1, d₁, d₂, hn =>
    getD_congr t n d₁ d₂ (by simp only [List.length_cons] at hn; omega)


/-- Out-of-range `getD` is the default. -/
private theorem getD_default : ∀ (L : List UInt256) (n : ℕ) (d : UInt256),
    L.length ≤ n → L.getD n d = d
  | [], _, _, _ => rfl
  | _ :: _, 0, _, hn => absurd hn (by simp)
  | _ :: t, n + 1, d, hn =>
    getD_default t n d (by simp only [List.length_cons] at hn; omega)


/-- In-range `getD` is `get`. -/
private theorem getD_eq_get : ∀ (L : List UInt256) (n : ℕ) (d : UInt256)
    (hn : n < L.length), L.getD n d = L.get ⟨n, hn⟩
  | [], _, _, hn => absurd hn (by simp)
  | _ :: _, 0, _, _ => rfl
  | _ :: t, n + 1, d, hn =>
    getD_eq_get t n d (by simp only [List.length_cons] at hn; omega)


/-- `getD` off the written index is unchanged by `set`. -/
private theorem getD_set_ne (x : UInt256) : ∀ (L : List UInt256) (i j : ℕ) (d : UInt256),
    i ≠ j → (L.set i x).getD j d = L.getD j d
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, hij => absurd rfl hij
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: t, i + 1, j + 1, d, hij =>
    getD_set_ne x t i j d (fun hcon => hij (by rw [hcon]))


/-- `getD` at the written index reads the written value. -/
private theorem getD_set_self (x : UInt256) : ∀ (L : List UInt256) (i : ℕ) (d : UInt256),
    i < L.length → (L.set i x).getD i d = x
  | [], _, _, hi => absurd hi (by simp)
  | _ :: _, 0, _, _ => rfl
  | _ :: t, i + 1, d, hi =>
    getD_set_self x t i d (by simp only [List.length_cons] at hi; omega)


/-- `getD 0` is `headD`. -/
private theorem getD_zero_headD : ∀ (L : List UInt256) (d : UInt256), L.getD 0 d = L.headD d
  | [], _ => rfl
  | _ :: _, _ => rfl


@[simp] theorem zeros_zero (h : Hash) (z0 : UInt256) :
    Properties.zeros_zero (h := h) (z0 := z0) := by
  unfold Properties.zeros_zero
  rfl


@[simp] theorem zeros_succ (h : Hash) (z0 : UInt256) (l : ℕ) :
    Properties.zeros_succ (h := h) (z0 := z0) (l := l) := by
  unfold Properties.zeros_succ
  rfl


@[simp] theorem levelUp_nil (h : Hash) (z : UInt256) :
    Properties.levelUp_nil (h := h) (z := z) := by
  unfold Properties.levelUp_nil
  rfl


@[simp] theorem levelUp_single (h : Hash) (z a : UInt256) :
    Properties.levelUp_single (h := h) (z := z) (a := a) := by
  unfold Properties.levelUp_single
  rfl


@[simp] theorem levelUp_cons₂ (h : Hash) (z a b : UInt256) (rest : List UInt256) :
    Properties.levelUp_cons₂ (h := h) (z := z) (a := a) (b := b) (rest := rest) := by
  unfold Properties.levelUp_cons₂
  rfl


@[simp] theorem levelUp_pair (h : Hash) (z a b : UInt256) :
    Properties.levelUp_pair (h := h) (z := z) (a := a) (b := b) := by
  unfold Properties.levelUp_pair
  rfl


@[simp] theorem levels_zero (h : Hash) (z0 : UInt256) (leaves : List UInt256) :
    Properties.levels_zero (h := h) (z0 := z0) (leaves := leaves) := by
  unfold Properties.levels_zero
  rfl


@[simp] theorem levels_succ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (l : ℕ) :
    Properties.levels_succ (h := h) (z0 := z0) (leaves := leaves) (l := l) := by
  unfold Properties.levels_succ
  rfl


theorem rootOf_def (h : Hash) (z0 : UInt256) (leaves : List UInt256) (height : ℕ) :
    Properties.rootOf_def (h := h) (z0 := z0) (leaves := leaves) (height := height) := by
  unfold Properties.rootOf_def
  rfl


theorem sibIdx_ne (j : ℕ) :
    Properties.sibIdx_ne (j := j) := by
  unfold Properties.sibIdx_ne sibIdx
  split <;> omega


@[simp] theorem walkPure_zero (h : Hash) (sibs : ℕ → UInt256) (lvl idx : ℕ) (x : UInt256) :
    Properties.walkPure_zero (h := h) (sibs := sibs) (lvl := lvl) (idx := idx) (x := x) := by
  unfold Properties.walkPure_zero
  rfl


@[simp] theorem walkPure_succ (h : Hash) (sibs : ℕ → UInt256) (lvl k idx : ℕ) (x : UInt256) :
    Properties.walkPure_succ (h := h) (sibs := sibs) (lvl := lvl) (k := k) (idx := idx) (x := x) := by
  unfold Properties.walkPure_succ
  rfl


@[simp] theorem appendPath_zero (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (x : UInt256) :
    Properties.appendPath_zero (h := h) (z0 := z0) (leaves := leaves) (x := x) := by
  unfold Properties.appendPath_zero
  rfl


theorem appendPath_succ (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (x : UInt256) (l : ℕ) :
    Properties.appendPath_succ (h := h) (z0 := z0) (leaves := leaves) (x := x) (l := l) := by
  unfold Properties.appendPath_succ
  rfl


/-! ## `levelUp` structure -/

/-- One level halves the width, rounding up. -/
theorem levelUp_length (h : Hash) (z : UInt256) :
    Properties.levelUp_length (h := h) (z := z)
  | [] => by simp only [levelUp_nil, List.length_nil]
  | [_] => by simp only [levelUp_single, List.length_cons, List.length_nil]
  | a :: b :: rest => by
    simp only [levelUp_cons₂, List.length_cons, levelUp_length h z rest]
    omega


/-- The parent entry `j` combines the child entries `2j` and `2j+1`; the
`getD` default `z` on the right child is exactly the frontier-edge zero. -/
theorem levelUp_getD (h : Hash) (z d : UInt256) :
    Properties.levelUp_getD (h := h) (z := z) (d := d)
  | [], _, hj => absurd hj (by simp)
  | [_], 0, _ => rfl
  | [_], _ + 1, hj => by simp at hj
  | a :: b :: rest, 0, _ => rfl
  | a :: b :: rest, j + 1, hj => by
    rw [levelUp_cons₂, show 2 * (j + 1) = 2 * j + 1 + 1 by omega]
    exact levelUp_getD h z d rest j (by simp only [List.length_cons] at hj; omega)


/-- `levelUp` distributes over an append at an even cut. -/
theorem levelUp_append_even (h : Hash) (z : UInt256) :
    Properties.levelUp_append_even (h := h) (z := z)
  | [], B, _ => by simp
  | [_], _, hA => by simp at hA
  | a :: b :: rest, B, hA => by
    have hrest : rest.length % 2 = 0 := by
      simp only [List.length_cons] at hA; omega
    rw [List.cons_append, List.cons_append, levelUp_cons₂, levelUp_cons₂,
        levelUp_append_even h z rest B hrest, List.cons_append]


/-- `levelUp` commutes with an even-length prefix. -/
theorem levelUp_take_even (h : Hash) (z : UInt256) :
    Properties.levelUp_take_even (h := h) (z := z)
  | 0, L, _ => by simp
  | q + 1, [], hq => by simp at hq
  | q + 1, [_], hq => by simp at hq; omega
  | q + 1, a :: b :: rest, hq => by
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 by omega, List.take_succ_cons, List.take_succ_cons,
      levelUp_cons₂, levelUp_cons₂,
      levelUp_take_even h z q rest (by simp only [List.length_cons] at hq; omega),
      List.take_succ_cons]


/-! ## M-C — frontier arithmetic -/

/-- The empty tree has empty levels. -/
theorem levels_nil (h : Hash) (z0 : UInt256) :
    Properties.levels_nil (h := h) (z0 := z0)
  | 0 => rfl
  | l + 1 => by rw [levels_succ, levels_nil h z0 l, levelUp_nil]


/-- **M-C.**  Level `l` of a nonempty tree has width `⌈n / 2^l⌉`, in the
`Nat.div` phrasing that recurses cleanly: `(n - 1) / 2^l + 1`. -/
theorem levels_length (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (hne : leaves.length ≠ 0) :
    Properties.levels_length (h := h) (z0 := z0) (leaves := leaves) (hne := hne)
  | 0 => by rw [levels_zero, pow_zero, Nat.div_one]; omega
  | l + 1 => by
    rw [levels_succ, levelUp_length, levels_length h z0 leaves hne l, pow_succ,
        ← Nat.div_div_eq_div_mul]
    omega


/-- M-C, ceiling form: the width is `(n + 2^l - 1) / 2^l`. -/
theorem levels_length_ceil (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (hne : leaves.length ≠ 0) (l : ℕ) :
    Properties.levels_length_ceil (h := h) (z0 := z0) (leaves := leaves) (hne := hne) (l := l) := by
  unfold Properties.levels_length_ceil
  have h2 := Nat.two_pow_pos l
  rw [levels_length h z0 leaves hne l,
      show leaves.length + 2 ^ l - 1 = (leaves.length - 1) + 2 ^ l by omega,
      Nat.add_div_right _ h2]


/-- M-C: every level of a nonempty tree is nonempty. -/
theorem levels_length_pos (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (hne : leaves.length ≠ 0) (l : ℕ) :
    Properties.levels_length_pos (h := h) (z0 := z0) (leaves := leaves) (hne := hne) (l := l) := by
  unfold Properties.levels_length_pos
  rw [levels_length h z0 leaves hne l]
  exact Nat.succ_pos _


/-- M-C, upper bound: the level width never exceeds the floor path index
plus one — the entry `⌊n/2^l⌋ + 1` (and beyond) is always outside, so an
even frontier path always reads the `zeros` default. -/
theorem levels_length_le (h : Hash) (z0 : UInt256) (leaves : List UInt256) (l : ℕ) :
    Properties.levels_length_le (h := h) (z0 := z0) (leaves := leaves) (l := l) := by
  unfold Properties.levels_length_le
  by_cases hne : leaves.length = 0
  · rw [List.length_eq_zero_iff.mp hne, levels_nil]; simp
  · rw [levels_length h z0 leaves hne l]
    have := Nat.div_le_div_right (c := 2 ^ l) (Nat.sub_le leaves.length 1)
    omega


/-- M-C, lower bound: the floor path index is inside (or at) the level. -/
theorem div_le_levels_length (h : Hash) (z0 : UInt256) (leaves : List UInt256) (l : ℕ) :
    Properties.div_le_levels_length (h := h) (z0 := z0) (leaves := leaves) (l := l) := by
  unfold Properties.div_le_levels_length
  by_cases hne : leaves.length = 0
  · rw [hne, List.length_eq_zero_iff.mp hne, levels_nil]; simp
  · have h2 := Nat.two_pow_pos l
    rw [levels_length h z0 leaves hne l, ← Nat.add_div_right _ h2]
    exact Nat.div_le_div_right (by omega)


/-- `set` preserves every level width. -/
theorem levels_set_length (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (idx : ℕ) (x : UInt256) :
    Properties.levels_set_length (h := h) (z0 := z0) (leaves := leaves) (idx := idx) (x := x)
  | 0 => by rw [levels_zero, levels_zero, List.length_set]
  | l + 1 => by
    rw [levels_succ, levels_succ, levelUp_length, levelUp_length,
        levels_set_length h z0 leaves idx x l]


/-- M-C: an in-tree index collapses to 0 at the top (`Nat.div_eq_of_lt`,
re-exported for downstream convenience). -/
theorem div_pow_eq_zero {idx k : ℕ} (hidx : idx < 2 ^ k) :
    Properties.div_pow_eq_zero (idx := idx) (k := k) (hidx := hidx) := by
  unfold Properties.div_pow_eq_zero
  exact Nat.div_eq_of_lt hidx


/-! ## M-A — the update walk recomputes the whole tree -/

/-- **M-A helper.**  Off the updated path, the levels of `leaves.set idx x`
agree with the levels of `leaves`: entry `j ≠ idx / 2^l` of level `l` is
unchanged.  (Sibling reads live here, since `sibIdx j ≠ j`.) -/
theorem levels_set_off_path (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (idx : ℕ) (x : UInt256) :
    Properties.levels_set_off_path (h := h) (z0 := z0) (leaves := leaves) (idx := idx) (x := x)
  | 0, j, d, hj => by
    have hidx : idx ≠ j := by
      intro he; apply hj; rw [pow_zero, Nat.div_one, he]
    exact getD_set_ne x leaves idx j d hidx
  | l + 1, j, d, hj => by
    have hdd : idx / 2 ^ (l + 1) = idx / 2 ^ l / 2 := by
      rw [show (2 : ℕ) ^ (l + 1) = 2 ^ l * 2 from by ring, Nat.div_div_eq_div_mul]
    have h2j : 2 * j ≠ idx / 2 ^ l := by
      intro he; apply hj; rw [hdd, ← he]; omega
    have h2j1 : 2 * j + 1 ≠ idx / 2 ^ l := by
      intro he; apply hj; rw [hdd, ← he]; omega
    by_cases hlt : 2 * j < (levels h z0 leaves l).length
    · have hlt' : 2 * j < (levels h z0 (leaves.set idx x) l).length := by
        rw [levels_set_length h z0 leaves idx x l]; exact hlt
      rw [levels_succ, levels_succ,
          levelUp_getD h (zeros h z0 l) d _ j hlt',
          levelUp_getD h (zeros h z0 l) d _ j hlt,
          levels_set_off_path h z0 leaves idx x l (2 * j) d h2j,
          levels_set_off_path h z0 leaves idx x l (2 * j + 1) (zeros h z0 l) h2j1]
    · push Not at hlt
      rw [levels_succ, levels_succ,
          getD_default _ _ _ (by
            rw [levelUp_length, levels_set_length h z0 leaves idx x l]; omega),
          getD_default _ _ _ (by rw [levelUp_length]; omega)]


/-- **M-A engine (intermediate-accumulator form).**  If the walk starts at
absolute level `lvl` on the level-`lvl` entry `j` of the tree over `L`, and
the sibling stream matches the tree (`getD` with default `zeros l` — the
frontier edge reads the zero automatically), then after `k` steps the
accumulator is the level-`lvl+k` entry `j / 2^k`.  Every intermediate
accumulator of the walk is therefore the corresponding on-path node. -/
theorem walkPure_levels (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (L : List UInt256) :
    Properties.walkPure_levels (h := h) (z0 := z0) (sibs := sibs) (L := L) := by
  unfold Properties.walkPure_levels
  intro k
  induction k with
  | zero => intro lvl j _ _; simp
  | succ k ih =>
    intro lvl j hj hsibs
    have hs : sibs lvl = (levels h z0 L lvl).getD (sibIdx j) (zeros h z0 lvl) := by
      simpa using hsibs lvl le_rfl (by omega)
    have hup := levelUp_getD h (zeros h z0 lvl) (zeros h z0 (lvl + 1)) (levels h z0 L lvl)
      (j / 2) (by omega)
    rw [← levels_succ] at hup
    have hacc : (if j % 2 = 1
          then h (sibs lvl) ((levels h z0 L lvl).getD j (zeros h z0 lvl))
          else h ((levels h z0 L lvl).getD j (zeros h z0 lvl)) (sibs lvl))
        = (levels h z0 L (lvl + 1)).getD (j / 2) (zeros h z0 (lvl + 1)) := by
      by_cases hpar : j % 2 = 1
      · rw [show 2 * (j / 2) = j - 1 by omega, show j - 1 + 1 = j by omega] at hup
        rw [ite_eq_left hpar, hs, hup, show sibIdx j = j - 1 by simp [sibIdx, hpar]]
        exact congrArg (fun w => h w _) (getD_congr _ _ _ _ (by omega))
      · rw [show 2 * (j / 2) = j by omega] at hup
        rw [ite_eq_right hpar, hs, hup, show sibIdx j = j + 1 by simp [sibIdx, hpar]]
        exact congrArg (fun w => h w _) (getD_congr _ _ _ _ hj)
    have hj' : j / 2 < (levels h z0 L (lvl + 1)).length := by
      rw [levels_succ, levelUp_length]; omega
    have hsibs' : ∀ l, lvl + 1 ≤ l → l < (lvl + 1) + k →
        sibs l = (levels h z0 L l).getD (sibIdx (j / 2 / 2 ^ (l - (lvl + 1))))
          (zeros h z0 l) := by
      intro l hl1 hl2
      rw [Nat.div_div_eq_div_mul, ← pow_succ', show l - (lvl + 1) + 1 = l - lvl by omega]
      exact hsibs l (by omega) (by omega)
    rw [walkPure_succ, hacc, ih (lvl + 1) (j / 2) hj' hsibs',
      show lvl + 1 + k = lvl + (k + 1) by omega, Nat.div_div_eq_div_mul, ← pow_succ']


/-- **M-A `walkPure_update`.**  Under the in-tree bounds, if the sibling
stream reads the UPDATED tree's levels at the sibling index (with default
`zeros l` beyond the frontier), the walk from `idx` with accumulator `x`
computes the root of `leaves.set idx x`. -/
theorem walkPure_update (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (idx : ℕ) (x : UInt256) (height : ℕ)
    (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 (leaves.set idx x) l).getD (sibIdx (idx / 2 ^ l))
        (zeros h z0 l)) :
    Properties.walkPure_update (h := h) (z0 := z0) (sibs := sibs) (leaves := leaves) (idx := idx) (x := x) (height := height) (hidx := hidx) (hcap := hcap) (hsibs := hsibs) := by
  unfold Properties.walkPure_update
  have hmain := walkPure_levels h z0 sibs (leaves.set idx x) height 0 idx
    (by rw [levels_zero, List.length_set]; exact hidx)
    (fun l _ hl => by rw [Nat.sub_zero]; exact hsibs l (by omega))
  rw [levels_zero, getD_set_self x leaves idx (zeros h z0 0) hidx, zero_add,
      Nat.div_eq_of_lt (lt_of_lt_of_le hidx hcap), getD_zero_headD] at hmain
  rwa [rootOf_def]


/-- **M-A, old-tree sibling form** (what the contract walk actually reads:
siblings are FETCHED from pre-update storage).  Follows from
`walkPure_update` via `levels_set_off_path` since `sibIdx j ≠ j`. -/
theorem walkPure_update_orig (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (idx : ℕ) (x : UInt256) (height : ℕ)
    (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (idx / 2 ^ l)) (zeros h z0 l)) :
    Properties.walkPure_update_orig (h := h) (z0 := z0) (sibs := sibs) (leaves := leaves) (idx := idx) (x := x) (height := height) (hidx := hidx) (hcap := hcap) (hsibs := hsibs) := by
  unfold Properties.walkPure_update_orig
  refine walkPure_update h z0 sibs leaves idx x height hidx hcap fun l hl => ?_
  rw [hsibs l hl, levels_set_off_path h z0 leaves idx x l _ _ (sibIdx_ne _)]


/-! ## M-B — appending at the frontier is a walk from `leaves.length` -/

/-- **M-B list surgery.**  Appending one leaf turns every level `l` into the
old level truncated at the path index `n / 2^l` plus the new path node:
the appended path is always the LAST entry of its level, old entries left
of it are untouched, and old entries at/right of it (the odd-path left
sibling absorbed into the new node) disappear into the path node. -/
theorem levels_append (h : Hash) (z0 : UInt256) (leaves : List UInt256) (x : UInt256) :
    Properties.levels_append (h := h) (z0 := z0) (leaves := leaves) (x := x)
  | 0 => by
    rw [levels_zero, levels_zero, appendPath_zero, pow_zero, Nat.div_one,
        List.take_length]
  | l + 1 => by
    have hple : leaves.length / 2 ^ l ≤ (levels h z0 leaves l).length :=
      div_le_levels_length h z0 leaves l
    rw [levels_succ, levels_append h z0 leaves x l, levels_succ, appendPath_succ]
    by_cases hpar : leaves.length / 2 ^ l % 2 = 1
    · -- odd path index: the lone old tail entry pairs with the new path node
      rw [ite_eq_left hpar]
      have hp2 : 2 * (leaves.length / 2 ^ (l + 1)) + 1 = leaves.length / 2 ^ l := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega
      have h2Q : 2 * (leaves.length / 2 ^ (l + 1)) < (levels h z0 leaves l).length := by
        omega
      rw [← hp2, Nat.add_sub_cancel, List.take_add_one, List.getElem?_eq_getElem h2Q]
      simp only [Option.toList_some]
      rw [List.append_assoc, List.singleton_append]
      have hAeven :
          ((levels h z0 leaves l).take (2 * (leaves.length / 2 ^ (l + 1)))).length % 2
            = 0 := by
        rw [List.length_take, min_eq_left (le_of_lt h2Q)]
        omega
      rw [levelUp_append_even h (zeros h z0 l) _ _ hAeven, levelUp_pair,
          levelUp_take_even h (zeros h z0 l) _ _ (le_of_lt h2Q),
          getD_eq_get _ _ _ h2Q, List.get_eq_getElem]
    · -- even path index: the new path node is a lone tail, paired with zeros l
      rw [ite_eq_right hpar]
      have hp2 : 2 * (leaves.length / 2 ^ (l + 1)) = leaves.length / 2 ^ l := by
        rw [pow_succ, ← Nat.div_div_eq_div_mul]; omega
      have hAeven :
          ((levels h z0 leaves l).take (leaves.length / 2 ^ l)).length % 2 = 0 := by
        rw [List.length_take, min_eq_left hple]
        omega
      rw [levelUp_append_even h (zeros h z0 l) _ _ hAeven, levelUp_single, ← hp2,
          levelUp_take_even h (zeros h z0 l) _ _ (by omega)]


/-- **M-B walk bridge.**  With the sibling stream reading the OLD tree at
`sibIdx (n / 2^l)` (default `zeros l` — every even level at the frontier
reads the zero, since the right sibling is outside the old level), the walk
from level `lvl` reproduces the append-path nodes. -/
theorem walkPure_appendPath (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (x : UInt256) :
    Properties.walkPure_appendPath (h := h) (z0 := z0) (sibs := sibs) (leaves := leaves) (x := x) := by
  unfold Properties.walkPure_appendPath
  intro k
  induction k with
  | zero => intro lvl _; rw [walkPure_zero, add_zero]
  | succ k ih =>
    intro lvl hsibs
    have hacc : (if leaves.length / 2 ^ lvl % 2 = 1
          then h (sibs lvl) (appendPath h z0 leaves x lvl)
          else h (appendPath h z0 leaves x lvl) (sibs lvl))
        = appendPath h z0 leaves x (lvl + 1) := by
      rw [appendPath_succ, hsibs lvl le_rfl (by omega), sibIdx]
      split_ifs
      · rfl
      · rw [getD_default _ _ _ (levels_length_le h z0 leaves lvl)]
    rw [walkPure_succ, hacc, Nat.div_div_eq_div_mul, ← pow_succ,
        ih (lvl + 1) (fun l h1 h2 => hsibs l (by omega) (by omega)),
        show lvl + 1 + k = lvl + (k + 1) by omega]


/-- **M-B `rootOf_append`.**  For a non-full tree, the root after appending
`x` is the update walk from the frontier index `leaves.length` whose sibling
stream reads the OLD tree: at odd path indices the real left neighbor, at
even path indices the `getD` default `zeros l` (the right sibling is beyond
the old frontier) — exactly `stepEdge`'s `_zeros[l]` read at every even
level of the contract's walk #2, where `idx = maxN = count`. -/
theorem rootOf_append (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (x : UInt256) (height : ℕ)
    (hcap : leaves.length < 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (leaves.length / 2 ^ l))
        (zeros h z0 l)) :
    Properties.rootOf_append (h := h) (z0 := z0) (sibs := sibs) (leaves := leaves) (x := x) (height := height) (hcap := hcap) (hsibs := hsibs) := by
  unfold Properties.rootOf_append
  have hwalk := walkPure_appendPath h z0 sibs leaves x height 0
    (fun l _ hl => hsibs l (by omega))
  rw [pow_zero, Nat.div_one, appendPath_zero, zero_add] at hwalk
  rw [hwalk, rootOf_def, levels_append h z0 leaves x height,
      Nat.div_eq_of_lt hcap, List.take_zero, List.nil_append]
  rfl


/-! ## M-D — root injectivity from node-hash injectivity

The tree-shaped generalization of `foldRoot_binding`: when the two-child
hash `h` is injective on the pairs it is fed, the recomputed root pins the
whole leaf multiset — same width and same root ⟹ same leaves.  Node-hash
injectivity `hinj` is discharged downstream from keccak injectivity (R6),
exactly as the abstract `h` is instantiated from the keccak cache. -/

/-- `levelUp` is injective on equal-width levels when `h` is pair-injective:
a lone left tail combines with the fixed zero `z`, so its parent still
determines it. -/
theorem levelUp_inj (h : Hash) (z : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) :
    Properties.levelUp_inj (h := h) (z := z) (hinj := hinj)
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ | _ :: _, [], hlen, _
  | [_], _ :: _ :: _, hlen, _ | _ :: _ :: _, [_], hlen, _ => by simp at hlen
  | [a], [c], _, he => by
      rw [levelUp_single, levelUp_single, List.cons.injEq] at he
      rw [(hinj a z c z he.1).1]
  | a :: b :: rest, c :: d :: rest', hlen, he => by
      rw [levelUp_cons₂, levelUp_cons₂, List.cons.injEq] at he
      obtain ⟨rfl, rfl⟩ := hinj a b c d he.1
      rw [levelUp_inj h z hinj rest rest' (by simpa using hlen) he.2]


/-- Level width depends only on the leaf-list width. -/
theorem levels_length_eq (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (hlen : L₁.length = L₂.length) :
    Properties.levels_length_eq (h := h) (z0 := z0) (L₁ := L₁) (L₂ := L₂) (hlen := hlen)
  | 0 => by rw [levels_zero, levels_zero]; exact hlen
  | l + 1 => by
      rw [levels_succ, levels_succ, levelUp_length, levelUp_length,
          levels_length_eq h z0 L₁ L₂ hlen l]


/-- Equal-width leaf lists whose level-`l` lists coincide are equal. -/
theorem levels_inj (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (hlen : L₁.length = L₂.length) :
    Properties.levels_inj (h := h) (z0 := z0) (hinj := hinj) (L₁ := L₁) (L₂ := L₂) (hlen := hlen)
  | 0 => by rw [levels_zero, levels_zero]; exact id
  | l + 1 => fun he => by
      rw [levels_succ, levels_succ] at he
      exact levels_inj h z0 hinj L₁ L₂ hlen l
        (levelUp_inj h (zeros h z0 l) hinj _ _
          (levels_length_eq h z0 L₁ L₂ hlen l) he)


/-- **M-D.**  For a non-full tree (`0 < width ≤ 2^height`), the level-`height`
list is a singleton, so it equals its root. -/
theorem levels_height_singleton (h : Hash) (z0 : UInt256) (L : List UInt256)
    (height : ℕ) (hne : L.length ≠ 0) (hcap : L.length ≤ 2 ^ height) :
    Properties.levels_height_singleton (h := h) (z0 := z0) (L := L) (height := height) (hne := hne) (hcap := hcap) := by
  unfold Properties.levels_height_singleton
  have hlen1 : (levels h z0 L height).length = 1 := by
    rw [levels_length h z0 L hne height, Nat.div_eq_of_lt (by omega)]
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen1
  rw [rootOf_def, ha]
  rfl


/-- **M-D — `rootOf_inj_of_h_inj`.**  When the node hash is pair-injective,
the recomputed root of a non-full tree pins the whole leaf list: same width,
same root ⟹ same leaves.  The tree-shaped `foldRoot_binding`. -/
theorem rootOf_inj_of_h_inj (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hne : L₁.length ≠ 0)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    Properties.rootOf_inj_of_h_inj (h := h) (z0 := z0) (hinj := hinj) (L₁ := L₁) (L₂ := L₂) (height := height) (hlen := hlen) (hne := hne) (hcap := hcap) (hroot := hroot) := by
  unfold Properties.rootOf_inj_of_h_inj
  apply levels_inj h z0 hinj L₁ L₂ hlen height
  rw [levels_height_singleton h z0 L₁ height hne hcap,
      levels_height_singleton h z0 L₂ height (hlen ▸ hne) (hlen ▸ hcap),
      hroot]


/-- **M-D binding corollary.**  Appending different leaves to the *same*
frontier of a non-full tree yields different roots: the recomputed root
pins the just-appended leaf.  The tree-level statement behind
`refund is bound to the committed bundle hash`. -/
theorem rootOf_append_inj (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (leaves : List UInt256) (x y : UInt256) (height : ℕ)
    (hcap : (leaves ++ [x]).length ≤ 2 ^ height)
    (hroot : rootOf h z0 (leaves ++ [x]) height
      = rootOf h z0 (leaves ++ [y]) height) :
    Properties.rootOf_append_inj (h := h) (z0 := z0) (hinj := hinj) (leaves := leaves) (x := x) (y := y) (height := height) (hcap := hcap) (hroot := hroot) := by
  unfold Properties.rootOf_append_inj
  simpa using rootOf_inj_of_h_inj h z0 hinj (leaves ++ [x]) (leaves ++ [y])
    height (by simp) (by simp) hcap hroot


/-- **M-D binding corollary (interior leaves).**  Overwriting one leaf with
a different value changes the recomputed root of a non-full tree: the root
pins *every* leaf, not only the appended one.  Companion to
`rootOf_append_inj`. -/
theorem rootOf_set_inj (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (leaves : List UInt256) (idx : ℕ) (x y : UInt256) (height : ℕ)
    (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hroot : rootOf h z0 (leaves.set idx x) height
      = rootOf h z0 (leaves.set idx y) height) :
    Properties.rootOf_set_inj (h := h) (z0 := z0) (hinj := hinj) (leaves := leaves) (idx := idx) (x := x) (y := y) (height := height) (hidx := hidx) (hcap := hcap) (hroot := hroot) := by
  unfold Properties.rootOf_set_inj
  have heq := rootOf_inj_of_h_inj h z0 hinj (leaves.set idx x) (leaves.set idx y)
    height (by rw [List.length_set, List.length_set])
    (by rw [List.length_set]; omega) (by rw [List.length_set]; exact hcap) hroot
  have hx : (leaves.set idx x).getD idx x = (leaves.set idx y).getD idx x := by
    rw [heq]
  rwa [getD_set_self x leaves idx x hidx, getD_set_self y leaves idx x hidx] at hx


/-- **M-D walk-level binding.**  The update walk is injective in its leaf
accumulator when `h` is pair-injective: each level combines the accumulator
with a sibling via `h`, so injectivity propagates from the root back down to
the leaf, regardless of the sibling stream or path parities.  The `walkPure`
shadow of `rootOf_set_inj`, and the walk-level form of "the recomputed root
pins the written leaf" (R8). -/
theorem walkPure_inj (h : Hash) (sibs : ℕ → UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d) :
    Properties.walkPure_inj (h := h) (sibs := sibs) (hinj := hinj)
  | 0, _, _, _, _ => by rw [walkPure_zero, walkPure_zero]; exact id
  | k + 1, lvl, idx, x, y => by
      simp only [walkPure_succ]
      intro hh
      have hcomb := walkPure_inj h sibs hinj k (lvl + 1) (idx / 2) _ _ hh
      split_ifs at hcomb
      exacts [(hinj _ _ _ _ hcomb).2, (hinj _ _ _ _ hcomb).1]


/-- **WALK SIBLING FRAME.**  `walkPure` reads the sibling stream only at the
levels `[lvl, lvl+k)` it actually climbs, so two streams agreeing there give
equal walks — the frame that lets a caller supply siblings level-by-level and
lets the atlas re-anchor the sibling reads between levels (R2). -/
theorem walkPure_congr_sibs (h : Hash) (s₁ s₂ : ℕ → UInt256) :
    Properties.walkPure_congr_sibs (h := h) (s₁ := s₁) (s₂ := s₂)
  | 0, _, _, _, _ => by rw [walkPure_zero, walkPure_zero]
  | k + 1, lvl, idx, x, hsib => by
      rw [walkPure_succ, walkPure_succ, hsib lvl (le_refl _) (by omega)]
      exact walkPure_congr_sibs h s₁ s₂ k (lvl + 1) (idx / 2) _
        (fun l h1 h2 => hsib l (by omega) (by omega))


/-- **M-D WITHOUT THE NONEMPTINESS HYPOTHESIS.**  `rootOf_inj_of_h_inj` requires
`L₁.length ≠ 0`, but that hypothesis is SPURIOUS: two equal-length lists that are
empty are equal outright, so the degenerate case needs no Merkle reasoning at all.

Worth removing because `hne` is the one hypothesis of M-D that
`AttackVectors.TreeShape` does NOT exhibit a counterexample for — it proved `hlen`
and `hcap` load-bearing but left `hne` unexamined, and this shows why: it was never
needed. -/
theorem rootOf_inj_of_h_inj' (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length)
    (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    Properties.rootOf_inj_of_h_inj' (h := h) (z0 := z0) (hinj := hinj) (L₁ := L₁) (L₂ := L₂) (height := height) (hlen := hlen) (hcap := hcap) (hroot := hroot) := by
  unfold Properties.rootOf_inj_of_h_inj'
  by_cases hne : L₁.length = 0
  · rw [List.length_eq_zero_iff.mp hne, List.length_eq_zero_iff.mp (show L₂.length = 0 by omega)]
  · exact rootOf_inj_of_h_inj h z0 hinj L₁ L₂ height hlen hne hcap hroot


end MerkleSpec
