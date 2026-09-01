import EraSpec.Word

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

/-- Abstract two-child node hash (instantiated from the keccak cache downstream). -/
abbrev Hash := UInt256 → UInt256 → UInt256

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

/-! ## Definitions -/

/-- The zero cascade: `zeros l` is the all-empty subtree hash at level `l`
(`_zeros[l]` in `FullMerkle`). -/
def zeros (h : Hash) (z0 : UInt256) : ℕ → UInt256
  | 0 => z0
  | l + 1 => h (zeros h z0 l) (zeros h z0 l)

@[simp] theorem zeros_zero (h : Hash) (z0 : UInt256) : zeros h z0 0 = z0 := rfl

@[simp] theorem zeros_succ (h : Hash) (z0 : UInt256) (l : ℕ) :
    zeros h z0 (l + 1) = h (zeros h z0 l) (zeros h z0 l) := rfl

/-- One level up: combine pairwise; a lone left tail combines with the
level zero `z` as its right sibling (the `FullMerkle` frontier edge). -/
def levelUp (h : Hash) (z : UInt256) : List UInt256 → List UInt256
  | [] => []
  | [a] => [h a z]
  | a :: b :: rest => h a b :: levelUp h z rest

@[simp] theorem levelUp_nil (h : Hash) (z : UInt256) : levelUp h z [] = [] := rfl

@[simp] theorem levelUp_single (h : Hash) (z a : UInt256) : levelUp h z [a] = [h a z] := rfl

@[simp] theorem levelUp_cons₂ (h : Hash) (z a b : UInt256) (rest : List UInt256) :
    levelUp h z (a :: b :: rest) = h a b :: levelUp h z rest := rfl

@[simp] theorem levelUp_pair (h : Hash) (z a b : UInt256) :
    levelUp h z [a, b] = [h a b] := rfl

/-- The level lists of the tree over `leaves`: `levels 0 = leaves`,
`levels (l+1) = levelUp` with the level-`l` zero. -/
def levels (h : Hash) (z0 : UInt256) (leaves : List UInt256) : ℕ → List UInt256
  | 0 => leaves
  | l + 1 => levelUp h (zeros h z0 l) (levels h z0 leaves l)

@[simp] theorem levels_zero (h : Hash) (z0 : UInt256) (leaves : List UInt256) :
    levels h z0 leaves 0 = leaves := rfl

@[simp] theorem levels_succ (h : Hash) (z0 : UInt256) (leaves : List UInt256) (l : ℕ) :
    levels h z0 leaves (l + 1) = levelUp h (zeros h z0 l) (levels h z0 leaves l) := rfl

/-- The root at a given height: head of the level-`height` list, or the
all-empty hash when there are no leaves. -/
def rootOf (h : Hash) (z0 : UInt256) (leaves : List UInt256) (height : ℕ) : UInt256 :=
  (levels h z0 leaves height).headD (zeros h z0 height)

theorem rootOf_def (h : Hash) (z0 : UInt256) (leaves : List UInt256) (height : ℕ) :
    rootOf h z0 leaves height = (levels h z0 leaves height).headD (zeros h z0 height) := rfl

/-- The sibling index of `j` inside one level: `j-1` for odd `j`, `j+1` for
even `j` (ℕ form of `j XOR 1`). -/
def sibIdx (j : ℕ) : ℕ := if j % 2 = 1 then j - 1 else j + 1

theorem sibIdx_ne (j : ℕ) : sibIdx j ≠ j := by
  unfold sibIdx; split <;> omega

/-- The pure update walk (`updateWalk`'s shadow): starting at absolute level
`lvl`, walk `k` levels up from index `idx` with accumulator `x`, orienting
each combine by the parity of the current index and reading the sibling from
the stream `sibs` at the absolute level. -/
def walkPure (h : Hash) (sibs : ℕ → UInt256) : ℕ → ℕ → ℕ → UInt256 → UInt256
  | _, 0, _, x => x
  | lvl, k + 1, idx, x =>
      walkPure h sibs (lvl + 1) k (idx / 2)
        (if idx % 2 = 1 then h (sibs lvl) x else h x (sibs lvl))

@[simp] theorem walkPure_zero (h : Hash) (sibs : ℕ → UInt256) (lvl idx : ℕ) (x : UInt256) :
    walkPure h sibs lvl 0 idx x = x := rfl

@[simp] theorem walkPure_succ (h : Hash) (sibs : ℕ → UInt256) (lvl k idx : ℕ) (x : UInt256) :
    walkPure h sibs lvl (k + 1) idx x
      = walkPure h sibs (lvl + 1) k (idx / 2)
          (if idx % 2 = 1 then h (sibs lvl) x else h x (sibs lvl)) := rfl

/-- The path values created by appending `x` at the frontier: `appendPath l`
is the level-`l` node on the new leaf's path (used by M-B).  At each level
the left sibling is the old tree's last entry when the path index is odd,
and the level zero when it is even (the path is at the frontier). -/
def appendPath (h : Hash) (z0 : UInt256) (leaves : List UInt256) (x : UInt256) : ℕ → UInt256
  | 0 => x
  | l + 1 =>
      if leaves.length / 2 ^ l % 2 = 1 then
        h ((levels h z0 leaves l).getD (leaves.length / 2 ^ l - 1) (zeros h z0 l))
          (appendPath h z0 leaves x l)
      else
        h (appendPath h z0 leaves x l) (zeros h z0 l)

@[simp] theorem appendPath_zero (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (x : UInt256) : appendPath h z0 leaves x 0 = x := rfl

theorem appendPath_succ (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (x : UInt256) (l : ℕ) :
    appendPath h z0 leaves x (l + 1)
      = if leaves.length / 2 ^ l % 2 = 1 then
          h ((levels h z0 leaves l).getD (leaves.length / 2 ^ l - 1) (zeros h z0 l))
            (appendPath h z0 leaves x l)
        else
          h (appendPath h z0 leaves x l) (zeros h z0 l) := rfl

/-! ## `levelUp` structure -/

/-- One level halves the width, rounding up. -/
theorem levelUp_length (h : Hash) (z : UInt256) :
    ∀ L : List UInt256, (levelUp h z L).length = (L.length + 1) / 2
  | [] => by
    simp only [levelUp_nil, List.length_nil]
  | [_] => by
    simp only [levelUp_single, List.length_cons, List.length_nil]
  | a :: b :: rest => by
    rw [levelUp_cons₂]
    simp only [List.length_cons]
    rw [levelUp_length h z rest]
    omega

/-- The parent entry `j` combines the child entries `2j` and `2j+1`; the
`getD` default `z` on the right child is exactly the frontier-edge zero. -/
theorem levelUp_getD (h : Hash) (z d : UInt256) :
    ∀ (L : List UInt256) (j : ℕ), 2 * j < L.length →
      (levelUp h z L).getD j d = h (L.getD (2 * j) d) (L.getD (2 * j + 1) z)
  | [], _, hj => absurd hj (by simp)
  | [a], j, hj => by
    have hj0 : j = 0 := by
      simp only [List.length_cons, List.length_nil] at hj; omega
    subst hj0
    rfl
  | a :: b :: rest, 0, _ => rfl
  | a :: b :: rest, j + 1, hj => by
    have hrest : 2 * j < rest.length := by
      simp only [List.length_cons] at hj; omega
    rw [levelUp_cons₂, show 2 * (j + 1) = 2 * j + 1 + 1 from by ring]
    rw [getD_cons_succ', getD_cons_succ', getD_cons_succ',
        getD_cons_succ', getD_cons_succ']
    exact levelUp_getD h z d rest j hrest

/-- `levelUp` distributes over an append at an even cut. -/
theorem levelUp_append_even (h : Hash) (z : UInt256) :
    ∀ A B : List UInt256, A.length % 2 = 0 →
      levelUp h z (A ++ B) = levelUp h z A ++ levelUp h z B
  | [], B, _ => by simp
  | [_], _, hA => by simp at hA
  | a :: b :: rest, B, hA => by
    have hrest : rest.length % 2 = 0 := by
      simp only [List.length_cons] at hA; omega
    rw [List.cons_append, List.cons_append, levelUp_cons₂, levelUp_cons₂,
        levelUp_append_even h z rest B hrest, List.cons_append]

/-- `levelUp` commutes with an even-length prefix. -/
theorem levelUp_take_even (h : Hash) (z : UInt256) :
    ∀ (q : ℕ) (L : List UInt256), 2 * q ≤ L.length →
      levelUp h z (L.take (2 * q)) = (levelUp h z L).take q
  | 0, L, _ => by simp
  | q + 1, [], hq => by simp at hq
  | q + 1, [_], hq => by
    simp only [List.length_cons, List.length_nil] at hq; omega
  | q + 1, a :: b :: rest, hq => by
    have hrest : 2 * q ≤ rest.length := by
      simp only [List.length_cons] at hq; omega
    rw [show 2 * (q + 1) = 2 * q + 1 + 1 from by ring]
    show levelUp h z (a :: b :: rest.take (2 * q))
        = (levelUp h z (a :: b :: rest)).take (q + 1)
    rw [levelUp_cons₂, levelUp_cons₂, levelUp_take_even h z q rest hrest]
    rfl

/-! ## M-C — frontier arithmetic -/

/-- The empty tree has empty levels. -/
theorem levels_nil (h : Hash) (z0 : UInt256) : ∀ l, levels h z0 [] l = []
  | 0 => rfl
  | l + 1 => by rw [levels_succ, levels_nil h z0 l, levelUp_nil]

/-- **M-C.**  Level `l` of a nonempty tree has width `⌈n / 2^l⌉`, in the
`Nat.div` phrasing that recurses cleanly: `(n - 1) / 2^l + 1`. -/
theorem levels_length (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (hne : leaves.length ≠ 0) :
    ∀ l, (levels h z0 leaves l).length = (leaves.length - 1) / 2 ^ l + 1
  | 0 => by
    rw [levels_zero, pow_zero, Nat.div_one]
    omega
  | l + 1 => by
    rw [levels_succ, levelUp_length, levels_length h z0 leaves hne l,
        show (2 : ℕ) ^ (l + 1) = 2 ^ l * 2 from by ring,
        ← Nat.div_div_eq_div_mul]
    omega

/-- M-C, ceiling form: the width is `(n + 2^l - 1) / 2^l`. -/
theorem levels_length_ceil (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (hne : leaves.length ≠ 0) (l : ℕ) :
    (levels h z0 leaves l).length = (leaves.length + 2 ^ l - 1) / 2 ^ l := by
  have h2 : 0 < (2 : ℕ) ^ l := pow_pos (by norm_num) l
  rw [levels_length h z0 leaves hne l,
      show leaves.length + 2 ^ l - 1 = (leaves.length - 1) + 2 ^ l from by omega,
      Nat.add_div_right _ h2]

/-- M-C: every level of a nonempty tree is nonempty. -/
theorem levels_length_pos (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (hne : leaves.length ≠ 0) (l : ℕ) :
    0 < (levels h z0 leaves l).length := by
  rw [levels_length h z0 leaves hne l]
  exact Nat.succ_pos _

/-- M-C, upper bound: the level width never exceeds the floor path index
plus one — the entry `⌊n/2^l⌋ + 1` (and beyond) is always outside, so an
even frontier path always reads the `zeros` default. -/
theorem levels_length_le (h : Hash) (z0 : UInt256) (leaves : List UInt256) (l : ℕ) :
    (levels h z0 leaves l).length ≤ leaves.length / 2 ^ l + 1 := by
  by_cases hne : leaves.length = 0
  · rw [List.length_eq_zero.mp hne, levels_nil]
    simp
  · rw [levels_length h z0 leaves hne l]
    exact Nat.add_le_add_right
      (Nat.div_le_div_right (c := 2 ^ l) (Nat.sub_le leaves.length 1)) 1

/-- M-C, lower bound: the floor path index is inside (or at) the level. -/
theorem div_le_levels_length (h : Hash) (z0 : UInt256) (leaves : List UInt256) (l : ℕ) :
    leaves.length / 2 ^ l ≤ (levels h z0 leaves l).length := by
  by_cases hne : leaves.length = 0
  · rw [hne, List.length_eq_zero.mp hne, levels_nil]
    simp
  · have h2 : 0 < (2 : ℕ) ^ l := pow_pos (by norm_num) l
    rw [levels_length h z0 leaves hne l]
    calc leaves.length / 2 ^ l
        ≤ ((leaves.length - 1) + 2 ^ l) / 2 ^ l :=
          Nat.div_le_div_right (by omega)
      _ = (leaves.length - 1) / 2 ^ l + 1 := Nat.add_div_right _ h2

/-- `set` preserves every level width. -/
theorem levels_set_length (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (idx : ℕ) (x : UInt256) :
    ∀ l, (levels h z0 (leaves.set idx x) l).length = (levels h z0 leaves l).length
  | 0 => by rw [levels_zero, levels_zero, List.length_set]
  | l + 1 => by
    rw [levels_succ, levels_succ, levelUp_length, levelUp_length,
        levels_set_length h z0 leaves idx x l]

/-- M-C: an in-tree index collapses to 0 at the top (`Nat.div_eq_of_lt`,
re-exported for downstream convenience). -/
theorem div_pow_eq_zero {idx k : ℕ} (hidx : idx < 2 ^ k) : idx / 2 ^ k = 0 :=
  Nat.div_eq_of_lt hidx

/-! ## M-A — the update walk recomputes the whole tree -/

/-- **M-A helper.**  Off the updated path, the levels of `leaves.set idx x`
agree with the levels of `leaves`: entry `j ≠ idx / 2^l` of level `l` is
unchanged.  (Sibling reads live here, since `sibIdx j ≠ j`.) -/
theorem levels_set_off_path (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (idx : ℕ) (x : UInt256) :
    ∀ (l j : ℕ) (d : UInt256), j ≠ idx / 2 ^ l →
      (levels h z0 (leaves.set idx x) l).getD j d = (levels h z0 leaves l).getD j d
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
    · push_neg at hlt
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
    ∀ k lvl j : ℕ,
      j < (levels h z0 L lvl).length →
      (∀ l, lvl ≤ l → l < lvl + k →
        sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ (l - lvl))) (zeros h z0 l)) →
      walkPure h sibs lvl k j ((levels h z0 L lvl).getD j (zeros h z0 lvl))
        = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k)) := by
  intro k
  induction k with
  | zero =>
    intro lvl j _ _
    simp
  | succ k ih =>
    intro lvl j hj hsibs
    have hs : sibs lvl = (levels h z0 L lvl).getD (sibIdx j) (zeros h z0 lvl) := by
      have := hsibs lvl (le_refl _) (by omega)
      simpa using this
    rw [walkPure_succ]
    have hup : (levels h z0 L (lvl + 1)).getD (j / 2) (zeros h z0 (lvl + 1))
        = h ((levels h z0 L lvl).getD (2 * (j / 2)) (zeros h z0 (lvl + 1)))
            ((levels h z0 L lvl).getD (2 * (j / 2) + 1) (zeros h z0 lvl)) := by
      rw [levels_succ]
      exact levelUp_getD h (zeros h z0 lvl) (zeros h z0 (lvl + 1)) _ (j / 2) (by omega)
    have hacc : (if j % 2 = 1
          then h (sibs lvl) ((levels h z0 L lvl).getD j (zeros h z0 lvl))
          else h ((levels h z0 L lvl).getD j (zeros h z0 lvl)) (sibs lvl))
        = (levels h z0 L (lvl + 1)).getD (j / 2) (zeros h z0 (lvl + 1)) := by
      by_cases hpar : j % 2 = 1
      · rw [show 2 * (j / 2) = j - 1 from by omega] at hup
        rw [show j - 1 + 1 = j from by omega] at hup
        rw [if_pos hpar, hs, hup,
            show sibIdx j = j - 1 from by simp [sibIdx, hpar]]
        exact congrArg (fun w => h w _) (getD_congr _ _ _ _ (by omega))
      · rw [show 2 * (j / 2) = j from by omega] at hup
        rw [if_neg hpar, hs, hup,
            show sibIdx j = j + 1 from by simp [sibIdx, hpar]]
        exact congrArg (fun w => h w _) (getD_congr _ _ _ _ hj)
    rw [hacc]
    have hj' : j / 2 < (levels h z0 L (lvl + 1)).length := by
      rw [levels_succ, levelUp_length]
      omega
    have hsibs' : ∀ l, lvl + 1 ≤ l → l < (lvl + 1) + k →
        sibs l = (levels h z0 L l).getD (sibIdx (j / 2 / 2 ^ (l - (lvl + 1))))
          (zeros h z0 l) := by
      intro l hl1 hl2
      have hidx : j / 2 / 2 ^ (l - (lvl + 1)) = j / 2 ^ (l - lvl) := by
        rw [Nat.div_div_eq_div_mul,
            show 2 * 2 ^ (l - (lvl + 1)) = 2 ^ (l - lvl) from by
              rw [show l - lvl = (l - (lvl + 1)) + 1 from by omega]; ring]
      rw [hidx]
      exact hsibs l (by omega) (by omega)
    rw [ih (lvl + 1) (j / 2) hj' hsibs',
        show lvl + 1 + k = lvl + (k + 1) from by omega,
        show j / 2 / 2 ^ k = j / 2 ^ (k + 1) from by
          rw [Nat.div_div_eq_div_mul, show 2 * 2 ^ k = (2 : ℕ) ^ (k + 1) from by ring]]

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
    walkPure h sibs 0 height idx x = rootOf h z0 (leaves.set idx x) height := by
  have hlen : idx < (levels h z0 (leaves.set idx x) 0).length := by
    rw [levels_zero, List.length_set]; exact hidx
  have hside : ∀ l, 0 ≤ l → l < 0 + height →
      sibs l = (levels h z0 (leaves.set idx x) l).getD (sibIdx (idx / 2 ^ (l - 0)))
        (zeros h z0 l) := by
    intro l _ hl
    rw [Nat.sub_zero]
    exact hsibs l (by omega)
  have hmain := walkPure_levels h z0 sibs (leaves.set idx x) height 0 idx hlen hside
  rw [levels_zero, getD_set_self x leaves idx (zeros h z0 0) hidx, zero_add,
      Nat.div_eq_of_lt (lt_of_lt_of_le hidx hcap), getD_zero_headD] at hmain
  rw [rootOf_def]
  exact hmain

/-- **M-A, old-tree sibling form** (what the contract walk actually reads:
siblings are FETCHED from pre-update storage).  Follows from
`walkPure_update` via `levels_set_off_path` since `sibIdx j ≠ j`. -/
theorem walkPure_update_orig (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (idx : ℕ) (x : UInt256) (height : ℕ)
    (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (idx / 2 ^ l)) (zeros h z0 l)) :
    walkPure h sibs 0 height idx x = rootOf h z0 (leaves.set idx x) height := by
  refine walkPure_update h z0 sibs leaves idx x height hidx hcap ?_
  intro l hl
  rw [hsibs l hl,
      levels_set_off_path h z0 leaves idx x l _ _ (sibIdx_ne _)]

/-! ## M-B — appending at the frontier is a walk from `leaves.length` -/

/-- **M-B list surgery.**  Appending one leaf turns every level `l` into the
old level truncated at the path index `n / 2^l` plus the new path node:
the appended path is always the LAST entry of its level, old entries left
of it are untouched, and old entries at/right of it (the odd-path left
sibling absorbed into the new node) disappear into the path node. -/
theorem levels_append (h : Hash) (z0 : UInt256) (leaves : List UInt256) (x : UInt256) :
    ∀ l, levels h z0 (leaves ++ [x]) l
      = (levels h z0 leaves l).take (leaves.length / 2 ^ l)
        ++ [appendPath h z0 leaves x l]
  | 0 => by
    rw [levels_zero, levels_zero, appendPath_zero, pow_zero, Nat.div_one,
        List.take_length]
  | l + 1 => by
    have hple : leaves.length / 2 ^ l ≤ (levels h z0 leaves l).length :=
      div_le_levels_length h z0 leaves l
    rw [levels_succ, levels_append h z0 leaves x l, levels_succ, appendPath_succ]
    by_cases hpar : leaves.length / 2 ^ l % 2 = 1
    · -- odd path index: the lone old tail entry pairs with the new path node
      rw [if_pos hpar]
      have hp2 : 2 * (leaves.length / 2 ^ (l + 1)) + 1 = leaves.length / 2 ^ l := by
        rw [show (2 : ℕ) ^ (l + 1) = 2 ^ l * 2 from by ring, ← Nat.div_div_eq_div_mul]
        omega
      have h2Q : 2 * (leaves.length / 2 ^ (l + 1)) < (levels h z0 leaves l).length := by
        omega
      rw [← hp2, Nat.add_sub_cancel, List.take_succ, List.get?_eq_get h2Q]
      simp only [Option.toList_some]
      rw [List.append_assoc, List.singleton_append]
      have hAeven :
          ((levels h z0 leaves l).take (2 * (leaves.length / 2 ^ (l + 1)))).length % 2
            = 0 := by
        rw [List.length_take, min_eq_left (le_of_lt h2Q)]
        omega
      rw [levelUp_append_even h (zeros h z0 l) _ _ hAeven, levelUp_pair,
          levelUp_take_even h (zeros h z0 l) _ _ (le_of_lt h2Q),
          getD_eq_get _ _ _ h2Q]
    · -- even path index: the new path node is a lone tail, paired with zeros l
      rw [if_neg hpar]
      have hp2 : 2 * (leaves.length / 2 ^ (l + 1)) = leaves.length / 2 ^ l := by
        rw [show (2 : ℕ) ^ (l + 1) = 2 ^ l * 2 from by ring, ← Nat.div_div_eq_div_mul]
        omega
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
    ∀ k lvl : ℕ,
      (∀ l, lvl ≤ l → l < lvl + k →
        sibs l = (levels h z0 leaves l).getD (sibIdx (leaves.length / 2 ^ l))
          (zeros h z0 l)) →
      walkPure h sibs lvl k (leaves.length / 2 ^ lvl) (appendPath h z0 leaves x lvl)
        = appendPath h z0 leaves x (lvl + k) := by
  intro k
  induction k with
  | zero =>
    intro lvl _
    rw [walkPure_zero, add_zero]
  | succ k ih =>
    intro lvl hsibs
    have hs := hsibs lvl (le_refl _) (by omega)
    rw [walkPure_succ]
    have hacc : (if leaves.length / 2 ^ lvl % 2 = 1
          then h (sibs lvl) (appendPath h z0 leaves x lvl)
          else h (appendPath h z0 leaves x lvl) (sibs lvl))
        = appendPath h z0 leaves x (lvl + 1) := by
      rw [appendPath_succ, hs]
      by_cases hpar : leaves.length / 2 ^ lvl % 2 = 1
      · rw [if_pos hpar, if_pos hpar,
            show sibIdx (leaves.length / 2 ^ lvl) = leaves.length / 2 ^ lvl - 1 from by
              simp [sibIdx, hpar]]
      · rw [if_neg hpar, if_neg hpar,
            show sibIdx (leaves.length / 2 ^ lvl) = leaves.length / 2 ^ lvl + 1 from by
              simp [sibIdx, hpar],
            getD_default _ _ _ (levels_length_le h z0 leaves lvl)]
    rw [hacc,
        show leaves.length / 2 ^ lvl / 2 = leaves.length / 2 ^ (lvl + 1) from by
          rw [Nat.div_div_eq_div_mul, show (2 : ℕ) ^ lvl * 2 = 2 ^ (lvl + 1) from by ring],
        ih (lvl + 1) (fun l h1 h2 => hsibs l (by omega) (by omega)),
        show lvl + 1 + k = lvl + (k + 1) from by omega]

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
    rootOf h z0 (leaves ++ [x]) height = walkPure h sibs 0 height leaves.length x := by
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
    ∀ L₁ L₂ : List UInt256, L₁.length = L₂.length →
      levelUp h z L₁ = levelUp h z L₂ → L₁ = L₂
  | [], [], _, _ => rfl
  | [], _ :: _ :: _, hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; try omega
  | [], [_], hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; try omega
  | [_], [], hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; try omega
  | _ :: _ :: _, [], hlen, _ => by
      simp only [List.length_nil, List.length_cons] at hlen; try omega
  | [a], [c], _, he => by
      rw [levelUp_single, levelUp_single, List.cons.injEq] at he
      rw [(hinj a z c z he.1).1]
  | [_], _ :: _ :: _, hlen, _ => by
      simp only [List.length_cons, List.length_nil] at hlen; try omega
  | _ :: _ :: _, [_], hlen, _ => by
      simp only [List.length_cons, List.length_nil] at hlen; try omega
  | a :: b :: rest, c :: d :: rest', hlen, he => by
      rw [levelUp_cons₂, levelUp_cons₂, List.cons.injEq] at he
      obtain ⟨hh, ht⟩ := he
      obtain ⟨rfl, rfl⟩ := hinj a b c d hh
      have hrl : rest.length = rest'.length := by
        simp only [List.length_cons] at hlen; omega
      rw [levelUp_inj h z hinj rest rest' hrl ht]

/-- Level width depends only on the leaf-list width. -/
theorem levels_length_eq (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (hlen : L₁.length = L₂.length) :
    ∀ l, (levels h z0 L₁ l).length = (levels h z0 L₂ l).length
  | 0 => by rw [levels_zero, levels_zero]; exact hlen
  | l + 1 => by
      rw [levels_succ, levels_succ, levelUp_length, levelUp_length,
          levels_length_eq h z0 L₁ L₂ hlen l]

/-- Equal-width leaf lists whose level-`l` lists coincide are equal. -/
theorem levels_inj (h : Hash) (z0 : UInt256)
    (hinj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d)
    (L₁ L₂ : List UInt256) (hlen : L₁.length = L₂.length) :
    ∀ l, levels h z0 L₁ l = levels h z0 L₂ l → L₁ = L₂
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
    levels h z0 L height = [rootOf h z0 L height] := by
  have hlen1 : (levels h z0 L height).length = 1 := by
    rw [levels_length h z0 L hne height, Nat.div_eq_of_lt (by omega)]
  obtain ⟨a, ha⟩ := List.length_eq_one.mp hlen1
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
    L₁ = L₂ := by
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
    x = y := by
  have heq := rootOf_inj_of_h_inj h z0 hinj (leaves ++ [x]) (leaves ++ [y])
    height (by simp) (by simp) hcap hroot
  simpa using heq

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
    x = y := by
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
    ∀ (k lvl idx : ℕ) (x y : UInt256),
      walkPure h sibs lvl k idx x = walkPure h sibs lvl k idx y → x = y
  | 0, _, _, _, _ => by rw [walkPure_zero, walkPure_zero]; exact id
  | k + 1, lvl, idx, x, y => by
      simp only [walkPure_succ]
      intro hh
      have hcomb := walkPure_inj h sibs hinj k (lvl + 1) (idx / 2) _ _ hh
      by_cases hpar : idx % 2 = 1
      · rw [if_pos hpar, if_pos hpar] at hcomb
        exact (hinj _ _ _ _ hcomb).2
      · rw [if_neg hpar, if_neg hpar] at hcomb
        exact (hinj _ _ _ _ hcomb).1

/-- **WALK SIBLING FRAME.**  `walkPure` reads the sibling stream only at the
levels `[lvl, lvl+k)` it actually climbs, so two streams agreeing there give
equal walks — the frame that lets a caller supply siblings level-by-level and
lets the atlas re-anchor the sibling reads between levels (R2). -/
theorem walkPure_congr_sibs (h : Hash) (s₁ s₂ : ℕ → UInt256) :
    ∀ (k lvl idx : ℕ) (x : UInt256),
      (∀ l, lvl ≤ l → l < lvl + k → s₁ l = s₂ l) →
      walkPure h s₁ lvl k idx x = walkPure h s₂ lvl k idx x
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
    L₁ = L₂ := by
  by_cases hne : L₁.length = 0
  · have h1 : L₁ = [] := List.length_eq_zero.mp hne
    have h2 : L₂ = [] := List.length_eq_zero.mp (by rw [← hlen]; exact hne)
    rw [h1, h2]
  · exact rootOf_inj_of_h_inj h z0 hinj L₁ L₂ height hlen hne hcap hroot

end MerkleSpec
