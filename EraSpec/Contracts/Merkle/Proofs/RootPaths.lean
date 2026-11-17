import EraSpec.Contracts.Merkle.Properties.RootPaths
import EraSpec.Contracts.Merkle.Proofs.PathCollision
import EraSpec.Contracts.Merkle.Proofs.RootForgeryPinned

/-!
# Proofs: `Merkle.calculateRootPaths` (see `../Specs/RootPaths.lean`)

Four engines:

* **Index arithmetic** (`nextLen_val`, `lhs_idx`, `rhs_idx`, `nextLen_window`): every read of
  an iteration is below `levelLen` and at or above the iteration's own index, and a window of
  absolute positions `[a, e]` shrinks to `[a / 2, e / 2]`.
* **In place = level by level** (`foldl_inner`, `levelLoop_win`): the in-place inner loop,
  having written entries `0 … k - 1`, still holds the level's old values at `k …`, which are
  the only ones iteration `k` reads.
* **Windows of the tree** (`stepWin_tree`, `win_tree`): with the tree's paths and entries, the
  level-`ℓ` values are the tree's level-`ℓ` entries at `[s / 2^ℓ, (s + n - 1) / 2^ℓ]`.
* **One walk per item** (`stepWin_pair`, `walk_win`): the pair an item's walk hashes at a level
  is the pair the level computes for the item's parent, so the walk's accumulators are the
  level values above the item.

Soundness then reuses the single-leaf extractors `accept_pins_entry_or_collision` and
`accept_pins_entry_any_length_or_break` (`PathCollision.lean`) once per item.
-/

namespace MerkleSpec.RootPaths

open Clear MerkleSpec MerkleSpec.Verifier MerkleSpec.Pinned

/-! ## Index arithmetic -/

theorem lor_bits (p q : ℕ) (hp : p < 2) (hq : q < 2) :
    p ||| q = if p = 1 ∨ q = 1 then 1 else 0 := by
  interval_cases p <;> interval_cases q <;> decide

/-- `nextLevelLen` without the bitwise or. -/
theorem nextLen_val (p L : ℕ) (hp : p < 2) :
    nextLen p L = L / 2 + (if p = 1 ∨ L % 2 = 1 then 1 else 0) := by
  unfold nextLen
  rw [lor_bits p (L % 2) hp (Nat.mod_lt _ (by norm_num))]

theorem nextLen_pos (p L : ℕ) (hp : p < 2) (hL : 1 ≤ L) : 1 ≤ nextLen p L := by
  rw [nextLen_val p L hp]; split_ifs <;> omega

theorem nextLen_le (p L : ℕ) (hp : p < 2) (hL : 1 ≤ L) : nextLen p L ≤ L := by
  rw [nextLen_val p L hp]; split_ifs <;> omega

/-- The `lhs` read of iteration `k`, when taken, is in `[k, L)`. -/
theorem lhs_idx (p L k : ℕ) (hp : p < 2) (hL : 1 ≤ L) (hk : k < nextLen p L)
    (hc : ¬ (k = 0 ∧ p = 1)) : p ≤ 2 * k ∧ 2 * k - p < L ∧ k ≤ 2 * k - p := by
  rw [nextLen_val p L hp] at hk
  split_ifs at hk <;> omega

/-- The `rhs` read of iteration `k`, when taken, is in `[k, L)`. -/
theorem rhs_idx (p L k : ℕ) (hp : p < 2) (hL : 1 ≤ L) (hk : k < nextLen p L)
    (hc : ¬ (k = nextLen p L - 1 ∧ (L - p) % 2 = 1)) : 2 * k + 1 - p < L ∧ k ≤ 2 * k + 1 - p := by
  rw [nextLen_val p L hp] at hk hc
  split_ifs at hk hc <;> omega

/-- A window of absolute positions `[a, e]` has `e / 2 - a / 2 + 1` parents. -/
theorem nextLen_window (a e : ℕ) (hae : a ≤ e) :
    nextLen (a % 2) (e - a + 1) = e / 2 - a / 2 + 1 := by
  rw [nextLen_val _ _ (Nat.mod_lt _ (by norm_num))]
  split_ifs <;> omega

theorem div_pow_succ' (x ℓ : ℕ) : x / 2 ^ ℓ / 2 = x / 2 ^ (ℓ + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ]

/-! ## `getD` toolkit -/

theorem getD_map_range (f : ℕ → UInt256) (n j : ℕ) (hj : j < n) :
    ((List.range n).map f).getD j 0 = f j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  rfl

theorem getD_set_ne' (x : UInt256) (L : List UInt256) (i j : ℕ) (hij : i ≠ j) :
    (L.set i x).getD j 0 = L.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne hij]

theorem getD_set_self' (x : UInt256) (L : List UInt256) (i : ℕ) (hi : i < L.length) :
    (L.set i x).getD i 0 = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hi]
  rfl

/-! ## In place = level by level -/

/-- **The in-place inner loop.** After iterations `0 … k - 1` of level `level` on `arr`, the
array has its old length, holds at `j < k` the value iteration `j` computes from the OLD
array, and holds the old values at `j ≥ k`. -/
theorem foldl_inner (h : Hash) (sp ep : List UInt256) (level p L : ℕ) (arr : List UInt256)
    (hp : p < 2) (hL : 1 ≤ L) (hLn : L ≤ arr.length) :
    ∀ k, k ≤ nextLen p L →
      ((List.range k).foldl (innerStep h sp ep level p L (nextLen p L)) arr).length = arr.length
      ∧ (∀ j, j < k →
          ((List.range k).foldl (innerStep h sp ep level p L (nextLen p L)) arr).getD j 0
            = h (lhsAt sp arr level p j) (rhsAt ep arr level p L (nextLen p L) j))
      ∧ (∀ j, k ≤ j →
          ((List.range k).foldl (innerStep h sp ep level p L (nextLen p L)) arr).getD j 0
            = arr.getD j 0) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨rfl, fun j hj => absurd hj (by omega), fun j _ => rfl⟩
  | succ k ih =>
    intro hk
    obtain ⟨hlen, hlow, hhigh⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    set res := (List.range k).foldl (innerStep h sp ep level p L (nextLen p L)) arr with hres
    have hnlL := nextLen_le p L hp hL
    -- the reads of iteration `k` see the old values
    have hlhs : lhsAt sp res level p k = lhsAt sp arr level p k := by
      unfold lhsAt
      by_cases hc : k = 0 ∧ p = 1
      · rw [ite_eq_left hc, ite_eq_left hc]
      · rw [ite_eq_right hc, ite_eq_right hc]
        obtain ⟨_, _, hge⟩ := lhs_idx p L k hp hL (by omega) hc
        exact hhigh _ hge
    have hrhs : rhsAt ep res level p L (nextLen p L) k
        = rhsAt ep arr level p L (nextLen p L) k := by
      unfold rhsAt
      by_cases hc : k = nextLen p L - 1 ∧ (L - p) % 2 = 1
      · rw [ite_eq_left hc, ite_eq_left hc]
      · rw [ite_eq_right hc, ite_eq_right hc]
        obtain ⟨_, hge⟩ := rhs_idx p L k hp hL (by omega) hc
        exact hhigh _ hge
    have hkres : k < res.length := by rw [hlen]; omega
    refine ⟨?_, ?_, ?_⟩
    · unfold innerStep; rw [List.length_set, hlen]
    · intro j hj
      unfold innerStep
      rw [hlhs, hrhs]
      by_cases hjk : j = k
      · subst hjk; exact getD_set_self' _ _ _ hkres
      · rw [getD_set_ne' _ _ _ _ (Ne.symm hjk)]; exact hlow j (by omega)
    · intro j hj
      unfold innerStep
      rw [getD_set_ne' _ _ _ _ (by omega)]
      exact hhigh j (by omega)

theorem stepWin_length (h : Hash) (sp ep : List UInt256) (level a : ℕ) (v : List UInt256) :
    (stepWin h sp ep level a v).length = nextLen (a % 2) v.length := by
  unfold stepWin; rw [List.length_map, List.length_range]

theorem win_length (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) :
    ∀ ℓ, (win h sp ep s items ℓ).length = lenAt s items.length ℓ
  | 0 => rfl
  | ℓ + 1 => by
    rw [win, stepWin_length, win_length h sp ep s items ℓ]
    rfl

theorem lenAt_bounds (s n : ℕ) (hn : 1 ≤ n) : ∀ ℓ, 1 ≤ lenAt s n ℓ ∧ lenAt s n ℓ ≤ n
  | 0 => ⟨hn, le_rfl⟩
  | ℓ + 1 => by
    obtain ⟨h1, h2⟩ := lenAt_bounds s n hn ℓ
    exact ⟨nextLen_pos _ _ (Nat.mod_lt _ (by norm_num)) h1,
      le_trans (nextLen_le _ _ (Nat.mod_lt _ (by norm_num)) h1) h2⟩

/-- Reading `lhs`/`rhs` from an array that agrees with the level's values below `levelLen`
gives what reading them from the values gives. -/
theorem lhsAt_congr (sp arr v : List UInt256) (level p k : ℕ) (hp : p < 2) (hL : 1 ≤ v.length)
    (hk : k < nextLen p v.length)
    (hagree : ∀ j, j < v.length → arr.getD j 0 = v.getD j 0) :
    lhsAt sp arr level p k = lhsAt sp v level p k := by
  unfold lhsAt
  by_cases hc : k = 0 ∧ p = 1
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact hagree _ (lhs_idx p v.length k hp hL hk hc).2.1

theorem rhsAt_congr (ep arr v : List UInt256) (level p k : ℕ) (hp : p < 2) (hL : 1 ≤ v.length)
    (hk : k < nextLen p v.length)
    (hagree : ∀ j, j < v.length → arr.getD j 0 = v.getD j 0) :
    rhsAt ep arr level p v.length (nextLen p v.length) k
      = rhsAt ep v level p v.length (nextLen p v.length) k := by
  unfold rhsAt
  by_cases hc : k = nextLen p v.length - 1 ∧ (v.length - p) % 2 = 1
  · rw [ite_eq_left hc, ite_eq_left hc]
  · rw [ite_eq_right hc, ite_eq_right hc]
    exact hagree _ (rhs_idx p v.length k hp hL hk hc).1

/-- **The in-place level loop computes the level-by-level values.** Started at level `ℓ` on an
array of the items' length that agrees with `win … ℓ` below its length, `k` more levels leave
an array of the same length that agrees with `win … (ℓ + k)` below its length. -/
theorem levelLoop_win (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256)
    (hn : 1 ≤ items.length) :
    ∀ k ℓ (arr : List UInt256), arr.length = items.length →
      (∀ j, j < (win h sp ep s items ℓ).length →
        arr.getD j 0 = (win h sp ep s items ℓ).getD j 0) →
      (levelLoop h sp ep k ℓ (s / 2 ^ ℓ) (win h sp ep s items ℓ).length arr).length
          = items.length
      ∧ ∀ j, j < (win h sp ep s items (ℓ + k)).length →
          (levelLoop h sp ep k ℓ (s / 2 ^ ℓ) (win h sp ep s items ℓ).length arr).getD j 0
            = (win h sp ep s items (ℓ + k)).getD j 0 := by
  intro k
  induction k with
  | zero =>
    intro ℓ arr hlen hagree
    exact ⟨hlen, hagree⟩
  | succ k ih =>
    intro ℓ arr hlen hagree
    have hp : (s / 2 ^ ℓ) % 2 < 2 := Nat.mod_lt _ (by norm_num)
    set v := win h sp ep s items ℓ with hv
    have hvb := lenAt_bounds s items.length hn ℓ
    rw [← win_length h sp ep s items ℓ, ← hv] at hvb
    have hvL : v.length ≤ arr.length := by rw [hlen]; exact hvb.2
    obtain ⟨hlen', hlow', _⟩ :=
      foldl_inner h sp ep ℓ ((s / 2 ^ ℓ) % 2) v.length arr hp hvb.1 hvL _ le_rfl
    have hwin1 : win h sp ep s items (ℓ + 1) = stepWin h sp ep ℓ (s / 2 ^ ℓ) v := rfl
    have hnl : nextLen ((s / 2 ^ ℓ) % 2) v.length = (win h sp ep s items (ℓ + 1)).length := by
      rw [hwin1, stepWin_length]
    have hstep : levelLoop h sp ep (k + 1) ℓ (s / 2 ^ ℓ) v.length arr
        = levelLoop h sp ep k (ℓ + 1) (s / 2 ^ (ℓ + 1)) (win h sp ep s items (ℓ + 1)).length
            ((List.range (nextLen ((s / 2 ^ ℓ) % 2) v.length)).foldl
              (innerStep h sp ep ℓ ((s / 2 ^ ℓ) % 2) v.length
                (nextLen ((s / 2 ^ ℓ) % 2) v.length)) arr) := by
      rw [← hnl, ← div_pow_succ']
      rfl
    rw [hstep, show ℓ + (k + 1) = (ℓ + 1) + k from by omega]
    refine ih (ℓ + 1) _ (by rw [hlen', hlen]) ?_
    intro j hj
    have hj' : j < nextLen ((s / 2 ^ ℓ) % 2) v.length := by rw [hnl]; exact hj
    rw [hlow' j hj', hwin1]
    unfold stepWin
    rw [getD_map_range _ _ _ hj',
      lhsAt_congr sp arr v ℓ _ j hp hvb.1 hj' (fun i hi => hagree i hi),
      rhsAt_congr ep arr v ℓ _ j hp hvb.1 hj' (fun i hi => hagree i hi)]

/-- The loop run from level 0 on the items agrees with `win` at the top. -/
theorem levelLoop_top (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256)
    (hn : 1 ≤ items.length) :
    (levelLoop h sp ep sp.length 0 s items.length items).length = items.length
    ∧ ∀ j, j < (win h sp ep s items sp.length).length →
        (levelLoop h sp ep sp.length 0 s items.length items).getD j 0
          = (win h sp ep s items sp.length).getD j 0 := by
  have := levelLoop_win h sp ep s items hn sp.length 0 items rfl (fun j _ => rfl)
  have h0 : win h sp ep s items 0 = items := rfl
  rw [h0] at this
  simpa only [pow_zero, Nat.div_one, Nat.zero_add] using this

/-! ## The checks -/

theorem two_pow_lt_wordLimit (P : ℕ) (hP : P < 256) : 2 ^ P < wordLimit := by
  unfold wordLimit; exact Nat.pow_lt_pow_right (by norm_num) hP

/-- **The checks pass exactly on the acceptance set.** -/
theorem guard_eq_none_iff (sp ep : List UInt256) (s : ℕ) (items : List UInt256) :
    guard sp ep s items = none ↔
      (sp.length = ep.length ∧ sp.length < 256 ∧ 0 < items.length
        ∧ s + items.length ≤ 2 ^ sp.length) := by
  constructor
  · intro hg
    unfold guard at hg
    split_ifs at hg with h1 h2 h3 h4 h5 h6
    exact ⟨not_not.mp h1, by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hw := two_pow_lt_wordLimit sp.length h2
    have hP0 : sp.length = 0 → 2 ^ sp.length = 1 := fun h0 => by rw [h0]; rfl
    have c1 : ¬ sp.length ≠ ep.length := by omega
    have c2 : ¬ 256 ≤ sp.length := by omega
    have c3 : ¬ (sp.length = 0 ∧ (s ≠ 0 ∨ items.length ≠ 1)) := by
      rintro ⟨h0, hc⟩; have := hP0 h0; omega
    have c4 : ¬ items.length = 0 := by omega
    have c5 : ¬ wordLimit ≤ s + items.length := by omega
    have c6 : ¬ 2 ^ sp.length < s + items.length := by omega
    unfold guard
    rw [ite_eq_right c1, ite_eq_right c2, ite_eq_right c3, ite_eq_right c4, ite_eq_right c5,
      ite_eq_right c6]

theorem guardNoEmptyCheck_eq_none_iff (sp ep : List UInt256) (s : ℕ) (items : List UInt256) :
    guardNoEmptyCheck sp ep s items = none ↔
      (sp.length = ep.length ∧ sp.length < 256 ∧ 0 < items.length
        ∧ s + items.length ≤ 2 ^ sp.length) := by
  constructor
  · intro hg
    unfold guardNoEmptyCheck at hg
    split_ifs at hg with h1 h2 h4 h5 h6
    exact ⟨not_not.mp h1, by omega, by omega, by omega⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hw := two_pow_lt_wordLimit sp.length h2
    have c1 : ¬ sp.length ≠ ep.length := by omega
    have c2 : ¬ 256 ≤ sp.length := by omega
    have c4 : ¬ items.length = 0 := by omega
    have c5 : ¬ wordLimit ≤ s + items.length := by omega
    have c6 : ¬ 2 ^ sp.length < s + items.length := by omega
    unfold guardNoEmptyCheck
    rw [ite_eq_right c1, ite_eq_right c2, ite_eq_right c4, ite_eq_right c5, ite_eq_right c6]

theorem rootPaths_eq (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256) :
    rootPaths h sp ep s items
      = if guard sp ep s items = none then some (runLoop h sp ep s items).1 else none := by
  unfold rootPaths rootPathsMem
  split_ifs <;> rfl

theorem rootPathsMem_of_guard {h : Hash} {sp ep : List UInt256} {s : ℕ} {items : List UInt256}
    (hg : guard sp ep s items = none) :
    rootPathsMem h sp ep s items = some (runLoop h sp ep s items) := by
  unfold rootPathsMem; rw [ite_eq_left hg]

theorem guard_of_rootPathsMem {h : Hash} {sp ep : List UInt256} {s : ℕ} {items : List UInt256}
    {x : UInt256 × List UInt256} (hr : rootPathsMem h sp ep s items = some x) :
    guard sp ep s items = none ∧ x = runLoop h sp ep s items := by
  unfold rootPathsMem at hr
  split_ifs at hr with hg
  exact ⟨hg, (Option.some.inj hr).symm⟩

theorem guard_of_rootPaths {h : Hash} {sp ep : List UInt256} {s : ℕ} {items : List UInt256}
    {r : UInt256} (hr : rootPaths h sp ep s items = some r) :
    guard sp ep s items = none ∧ r = (runLoop h sp ep s items).1 := by
  rw [rootPaths_eq] at hr
  split_ifs at hr with hg
  exact ⟨hg, (Option.some.inj hr).symm⟩

/-- On an accepted call the returned root is the top level-by-level value. -/
theorem runLoop_fst_eq_win {h : Hash} {sp ep : List UInt256} {s : ℕ} {items : List UInt256}
    (hg : guard sp ep s items = none) :
    (runLoop h sp ep s items).1 = (win h sp ep s items sp.length).getD 0 0 := by
  obtain ⟨_, _, hn, _⟩ := (guard_eq_none_iff sp ep s items).mp hg
  have hpos := (lenAt_bounds s items.length hn sp.length).1
  rw [← win_length h sp ep s items sp.length] at hpos
  exact (levelLoop_top h sp ep s items hn).2 0 (by omega)

/-! ## Windows of absolute positions -/

/-- The level-`ℓ` values cover the absolute positions `[s / 2^ℓ, (s + n - 1) / 2^ℓ]`. -/
theorem win_length_abs (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256)
    (hn : 1 ≤ items.length) :
    ∀ ℓ, (win h sp ep s items ℓ).length
      = (s + items.length - 1) / 2 ^ ℓ - s / 2 ^ ℓ + 1
  | 0 => by
    show items.length = _
    rw [pow_zero, Nat.div_one, Nat.div_one]; omega
  | ℓ + 1 => by
    rw [win, stepWin_length, win_length_abs h sp ep s items hn ℓ,
      nextLen_window _ _ (Nat.div_le_div_right (by omega)), div_pow_succ', div_pow_succ']

/-- **One level of an honest window.** If the values `v` at positions `[a, e]` are the tree's
level-`ℓ` entries there, and the paths hold the tree's neighbours where the loop reads them (`a`'s
left neighbour when `a` is odd, `e`'s right neighbour when `e` is even), then the next level's
values are the tree's level-`ℓ + 1` entries at `[a / 2, …]`. -/
theorem stepWin_tree (h : Hash) (z0 : UInt256) (L : List UInt256) (sp ep : List UInt256)
    (ℓ a e : ℕ) (v : List UInt256) (hae : a ≤ e) (hv : v.length = e - a + 1)
    (hval : ∀ r, r < v.length → v.getD r 0 = (levels h z0 L ℓ).getD (a + r) (zeros h z0 ℓ))
    (hsp : a % 2 = 1 → sp.getD ℓ 0 = (levels h z0 L ℓ).getD (a - 1) (zeros h z0 ℓ))
    (hep : e % 2 = 0 → ep.getD ℓ 0 = (levels h z0 L ℓ).getD (e + 1) (zeros h z0 ℓ)) :
    ∀ r, r < (stepWin h sp ep ℓ a v).length →
      (stepWin h sp ep ℓ a v).getD r 0
        = (levels h z0 L (ℓ + 1)).getD (a / 2 + r) (zeros h z0 (ℓ + 1)) := by
  intro r hr
  rw [stepWin_length] at hr
  have hp : a % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have hL1 : 1 ≤ v.length := by omega
  have hnl : nextLen (a % 2) v.length = e / 2 - a / 2 + 1 := by
    rw [hv]; exact nextLen_window a e hae
  unfold stepWin
  rw [getD_map_range _ _ _ hr, levels_succ_getD]
  congr 1
  · unfold lhsAt
    by_cases hc : r = 0 ∧ a % 2 = 1
    · rw [ite_eq_left hc, hsp hc.2]
      congr 1; omega
    · rw [ite_eq_right hc]
      obtain ⟨_, hlt, _⟩ := lhs_idx (a % 2) v.length r hp hL1 hr hc
      rw [hval _ hlt]
      congr 1; omega
  · unfold rhsAt
    by_cases hc : r = nextLen (a % 2) v.length - 1 ∧ (v.length - a % 2) % 2 = 1
    · rw [ite_eq_left hc]
      rw [hnl, hv] at hc
      have he : e % 2 = 0 := by omega
      rw [hep he]
      congr 1; omega
    · rw [ite_eq_right hc]
      obtain ⟨hlt, _⟩ := rhs_idx (a % 2) v.length r hp hL1 hr hc
      rw [hval _ hlt]
      congr 1; omega

theorem honestPath_length (h : Hash) (z0 : UInt256) (L : List UInt256) (j H : ℕ) :
    (honestPath h z0 L j H).length = H := by
  unfold honestPath; rw [List.length_map, List.length_range]

theorem treeSegment_length (z0 : UInt256) (L : List UInt256) (s n : ℕ) :
    (treeSegment z0 L s n).length = n := by
  unfold treeSegment; rw [List.length_map, List.length_range]

theorem honestPath_getD (h : Hash) (z0 : UInt256) (L : List UInt256) (j H ℓ : ℕ) (hℓ : ℓ < H) :
    (honestPath h z0 L j H).getD ℓ 0
      = (levels h z0 L ℓ).getD (sibIdx (j / 2 ^ ℓ)) (zeros h z0 ℓ) := by
  unfold honestPath; rw [getD_map_range _ _ _ hℓ]; rfl

theorem sibIdx_odd {j : ℕ} (hj : j % 2 = 1) : sibIdx j = j - 1 := by simp [sibIdx, hj]

theorem sibIdx_even {j : ℕ} (hj : j % 2 = 0) : sibIdx j = j + 1 := by simp [sibIdx, hj]

/-- **Honest windows.** With the tree's paths and the tree's entries as items, the level-`ℓ`
values (`ℓ ≤ H`) are the tree's level-`ℓ` entries from position `s / 2^ℓ` on. -/
theorem win_tree (h : Hash) (z0 : UInt256) (L : List UInt256) (H s n : ℕ) (hn : 1 ≤ n) :
    ∀ ℓ, ℓ ≤ H → ∀ r,
      r < (win h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s
        (treeSegment z0 L s n) ℓ).length →
      (win h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s
        (treeSegment z0 L s n) ℓ).getD r 0
        = (levels h z0 L ℓ).getD (s / 2 ^ ℓ + r) (zeros h z0 ℓ)
  | 0, _, r, hr => by
    show (treeSegment z0 L s n).getD r 0 = _
    have hr' : r < (treeSegment z0 L s n).length := hr
    rw [treeSegment_length] at hr'
    unfold treeSegment
    rw [getD_map_range _ _ _ hr', pow_zero, Nat.div_one, levels_zero, zeros_zero]
  | ℓ + 1, hℓ, r, hr => by
    have hn' : 1 ≤ (treeSegment z0 L s n).length := by rw [treeSegment_length]; exact hn
    have hlen := win_length_abs h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s
      (treeSegment z0 L s n) hn' ℓ
    rw [treeSegment_length] at hlen
    have hstep := stepWin_tree h z0 L (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H)
      ℓ (s / 2 ^ ℓ) ((s + n - 1) / 2 ^ ℓ) _ (Nat.div_le_div_right (by omega)) hlen
      (win_tree h z0 L H s n hn ℓ (by omega))
      (fun hodd => by rw [honestPath_getD _ _ _ _ _ _ (by omega), sibIdx_odd hodd])
      (fun heven => by rw [honestPath_getD _ _ _ _ _ _ (by omega), sibIdx_even heven]) r hr
    rw [win, hstep, div_pow_succ']

/-! ## Completeness -/

theorem rootPaths_complete (h : Hash) (z0 : UInt256) (L : List UInt256) (H s n : ℕ)
    (hn : 1 ≤ n) (hsn : s + n ≤ 2 ^ H) (hH : H < 256) :
    rootPaths h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s (treeSegment z0 L s n)
      = some (rootOf h z0 L H) := by
  have hg : guard (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s
      (treeSegment z0 L s n) = none := by
    rw [guard_eq_none_iff, honestPath_length, honestPath_length, treeSegment_length]
    exact ⟨rfl, hH, hn, hsn⟩
  rw [rootPaths_eq, ite_eq_left hg, runLoop_fst_eq_win hg, honestPath_length]
  have hn' : 1 ≤ (treeSegment z0 L s n).length := by rw [treeSegment_length]; exact hn
  have hlen := win_length_abs h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s
    (treeSegment z0 L s n) hn' H
  rw [treeSegment_length, Nat.div_eq_of_lt (by omega : s + n - 1 < 2 ^ H),
    Nat.div_eq_of_lt (by omega : s < 2 ^ H)] at hlen
  rw [win_tree h z0 L H s n hn H le_rfl 0 (by omega), Nat.div_eq_of_lt (by omega : s < 2 ^ H),
    rootOf_def, Nat.zero_add, getD_zero_headD]

/-! ## One walk per item -/

/-- **The pair at an item's ancestor is the pair the level computes for its parent.** For a
position `jj` inside the window `[a, e]`, the ordered pair (`jj`'s value and its `sibAt`
neighbour) is the `(lhs, rhs)` of the level's iteration for `jj`'s parent, and the loop runs
that iteration. -/
theorem stepWin_pair (sp ep v : List UInt256) (ℓ a e jj : ℕ) (hae : a ≤ jj) (hje : jj ≤ e)
    (hv : v.length = e - a + 1) :
    jj / 2 - a / 2 < nextLen (a % 2) v.length
    ∧ (if jj % 2 = 1 then (sibAt sp ep v ℓ a jj, v.getD (jj - a) 0)
        else (v.getD (jj - a) 0, sibAt sp ep v ℓ a jj))
      = (lhsAt sp v ℓ (a % 2) (jj / 2 - a / 2),
         rhsAt ep v ℓ (a % 2) v.length (nextLen (a % 2) v.length) (jj / 2 - a / 2)) := by
  have hnl : nextLen (a % 2) v.length = e / 2 - a / 2 + 1 := by
    rw [hv]; exact nextLen_window a e (le_trans hae hje)
  refine ⟨by rw [hnl]; omega, ?_⟩
  unfold sibAt lhsAt rhsAt
  rw [hnl, hv]
  by_cases hj : jj % 2 = 1
  · rw [ite_eq_left hj, ite_eq_left hj]
    have hr : ¬ (jj / 2 - a / 2 = e / 2 - a / 2 + 1 - 1 ∧ (e - a + 1 - a % 2) % 2 = 1) := by
      omega
    rw [ite_eq_right hr, show 2 * (jj / 2 - a / 2) + 1 - a % 2 = jj - a by omega]
    by_cases hja : jj = a
    · have hc : jj / 2 - a / 2 = 0 ∧ a % 2 = 1 := by omega
      rw [ite_eq_left hja, ite_eq_left hc]
    · have hc : ¬ (jj / 2 - a / 2 = 0 ∧ a % 2 = 1) := by omega
      rw [ite_eq_right hja, ite_eq_right hc, show 2 * (jj / 2 - a / 2) - a % 2 = jj - 1 - a by omega]
  · rw [ite_eq_right hj, ite_eq_right hj]
    have hc : ¬ (jj / 2 - a / 2 = 0 ∧ a % 2 = 1) := by omega
    rw [ite_eq_right hc, show 2 * (jj / 2 - a / 2) - a % 2 = jj - a by omega]
    by_cases hje' : jj + 1 = a + (e - a + 1)
    · have hr : jj / 2 - a / 2 = e / 2 - a / 2 + 1 - 1 ∧ (e - a + 1 - a % 2) % 2 = 1 := by
        omega
      rw [ite_eq_left hje', ite_eq_left hr]
    · have hr : ¬ (jj / 2 - a / 2 = e / 2 - a / 2 + 1 - 1 ∧ (e - a + 1 - a % 2) % 2 = 1) := by
        omega
      rw [ite_eq_right hje', ite_eq_right hr, show 2 * (jj / 2 - a / 2) + 1 - a % 2 = jj + 1 - a by omega]

/-- **An item's walk climbs through the level values above it.** For the item at absolute
index `j` of the range, walking `k` levels from level `ℓ` (where its ancestor `j / 2^ℓ` holds
the level-`ℓ` value) with the stream `rangeSib … j` lands on the level-`ℓ + k` value above it. -/
theorem walk_win (h : Hash) (sp ep : List UInt256) (s : ℕ) (items : List UInt256)
    (hn : 1 ≤ items.length) (j : ℕ) (hj1 : s ≤ j) (hj2 : j < s + items.length) :
    ∀ k ℓ, walkPure h (rangeSib h sp ep s items j) ℓ k (j / 2 ^ ℓ)
        ((win h sp ep s items ℓ).getD (j / 2 ^ ℓ - s / 2 ^ ℓ) 0)
      = (win h sp ep s items (ℓ + k)).getD (j / 2 ^ (ℓ + k) - s / 2 ^ (ℓ + k)) 0 := by
  intro k
  induction k with
  | zero => intro ℓ; rfl
  | succ k ih =>
    intro ℓ
    rw [walkPure_succ]
    have hae : s / 2 ^ ℓ ≤ j / 2 ^ ℓ := Nat.div_le_div_right hj1
    have hje : j / 2 ^ ℓ ≤ (s + items.length - 1) / 2 ^ ℓ := Nat.div_le_div_right (by omega)
    obtain ⟨hlt, hpair⟩ := stepWin_pair sp ep (win h sp ep s items ℓ) ℓ (s / 2 ^ ℓ)
      ((s + items.length - 1) / 2 ^ ℓ) (j / 2 ^ ℓ) hae hje (win_length_abs h sp ep s items hn ℓ)
    have hacc : (if j / 2 ^ ℓ % 2 = 1
          then h (rangeSib h sp ep s items j ℓ)
            ((win h sp ep s items ℓ).getD (j / 2 ^ ℓ - s / 2 ^ ℓ) 0)
          else h ((win h sp ep s items ℓ).getD (j / 2 ^ ℓ - s / 2 ^ ℓ) 0)
            (rangeSib h sp ep s items j ℓ))
        = (win h sp ep s items (ℓ + 1)).getD (j / 2 ^ (ℓ + 1) - s / 2 ^ (ℓ + 1)) 0 := by
      have hw : win h sp ep s items (ℓ + 1)
          = stepWin h sp ep ℓ (s / 2 ^ ℓ) (win h sp ep s items ℓ) := rfl
      rw [hw, ← div_pow_succ', ← div_pow_succ']
      unfold stepWin
      rw [getD_map_range _ _ _ hlt]
      have hsib : rangeSib h sp ep s items j ℓ
          = sibAt sp ep (win h sp ep s items ℓ) ℓ (s / 2 ^ ℓ) (j / 2 ^ ℓ) := rfl
      rw [hsib]
      by_cases hodd : j / 2 ^ ℓ % 2 = 1
      · rw [ite_eq_left hodd] at hpair ⊢
        rw [Prod.mk.injEq] at hpair
        rw [hpair.1, hpair.2]
      · rw [ite_eq_right hodd] at hpair ⊢
        rw [Prod.mk.injEq] at hpair
        rw [hpair.1, hpair.2]
    rw [hacc, div_pow_succ', ih (ℓ + 1), show ℓ + 1 + k = ℓ + (k + 1) by omega]

/-- **Each item's walk gives the returned root.** -/
theorem item_walk {h : Hash} {sp ep : List UInt256} {s : ℕ} {items : List UInt256} {r : UInt256}
    (hr : rootPaths h sp ep s items = some r) (i : ℕ) (hi : i < items.length) :
    s + i < 2 ^ sp.length
    ∧ walkPure h (rangeSib h sp ep s items (s + i)) 0 sp.length (s + i) (items.getD i 0) = r := by
  obtain ⟨hg, hrv⟩ := guard_of_rootPaths hr
  obtain ⟨_, _, hn, hsn⟩ := (guard_eq_none_iff sp ep s items).mp hg
  refine ⟨by omega, ?_⟩
  have hw := walk_win h sp ep s items hn (s + i) (by omega) (by omega) sp.length 0
  simp only [pow_zero, Nat.div_one, Nat.zero_add] at hw
  rw [show s + i - s = i by omega,
    Nat.div_eq_of_lt (by omega : s + i < 2 ^ sp.length),
    Nat.div_eq_of_lt (by omega : s < 2 ^ sp.length)] at hw
  rw [hrv, runLoop_fst_eq_win hg, ← hw]
  rfl

/-- `walkPair` at step `i` is the step taken from the walk's accumulator after `i` steps. -/
theorem walkPair_eq_walkStep (h : Hash) (sibs : ℕ → UInt256) :
    ∀ (i lvl j : ℕ) (x : UInt256),
      walkPair h sibs lvl j x i = walkStep sibs (lvl + i) (j / 2 ^ i) (walkPure h sibs lvl i j x) := by
  intro i
  induction i with
  | zero => intro lvl j x; simp [walkPair]
  | succ i ih =>
    intro lvl j x
    rw [walkPair_succ, ih, walkPure_succ, walkStep_hash h sibs lvl j x, div_div_pow_succ_two,
      show lvl + 1 + i = lvl + (i + 1) by omega]
  where
    div_div_pow_succ_two {j i : ℕ} : j / 2 / 2 ^ i = j / 2 ^ (i + 1) := by
      rw [Nat.div_div_eq_div_mul, show 2 * 2 ^ i = (2 : ℕ) ^ (i + 1) by ring]

/-! ## Soundness -/

theorem rootPaths_sound (h : Hash) (z0 : UInt256) (L : List UInt256) (sp ep : List UInt256)
    (s : ℕ) (items : List UInt256)
    (hr : rootPaths h sp ep s items = some (rootOf h z0 L sp.length)) :
    items = treeSegment z0 L s items.length
    ∨ ∃ i, i < items.length ∧
        PathCollision h z0 L (rangeSib h sp ep s items (s + i)) 0 sp.length (s + i)
          (items.getD i 0) := by
  by_cases hall : ∀ i, i < items.length → L.getD (s + i) z0 = items.getD i 0
  · left
    refine ext_getD' 0 _ _ (by rw [treeSegment_length]) ?_
    intro i hi
    unfold treeSegment
    rw [getD_map_range _ _ _ hi]
    exact (hall i hi).symm
  · right
    push Not at hall
    obtain ⟨i, hi, hne⟩ := hall
    obtain ⟨hlt, hw⟩ := item_walk hr i hi
    rcases accept_pins_entry_or_collision h z0 L _ sp.length (s + i) _ hlt hw with he | hc
    · exact absurd he hne
    · exact ⟨i, hi, hc⟩

theorem rootPaths_siblings_pinned (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sp ep : List UInt256) (s : ℕ) (items : List UInt256)
    (hr : rootPaths h sp ep s items = some (rootOf h z0 L sp.length)) (i : ℕ)
    (hi : i < items.length) :
    (∀ ℓ, ℓ < sp.length → rangeSib h sp ep s items (s + i) ℓ
        = (levels h z0 L ℓ).getD (sibIdx ((s + i) / 2 ^ ℓ)) (zeros h z0 ℓ))
    ∨ PathCollision h z0 L (rangeSib h sp ep s items (s + i)) 0 sp.length (s + i)
        (items.getD i 0) := by
  obtain ⟨hlt, hw⟩ := item_walk hr i hi
  have hroot : (levels h z0 L (0 + sp.length)).getD ((s + i) / 2 ^ sp.length)
      (zeros h z0 (0 + sp.length)) = rootOf h z0 L sp.length := by
    rw [Nat.zero_add, Nat.div_eq_of_lt hlt, rootOf_def, getD_zero_headD]
  rcases walk_pins_or_collision h z0 L _ sp.length 0 (s + i) _ (by rw [hroot]; exact hw) with
    ⟨_, hsibs⟩ | hc
  · left
    intro ℓ hℓ
    have := hsibs ℓ (Nat.zero_le _) (by omega)
    rwa [Nat.sub_zero] at this
  · exact Or.inr hc

theorem rootPaths_any_length (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ)
    (sp ep : List UInt256) (s : ℕ) (items : List UInt256)
    (hr : rootPaths h sp ep s items = some (rootOf h z0 L H)) :
    (sp.length = H ∧ items = treeSegment z0 L s items.length)
    ∨ (sp.length = H ∧ ∃ i, i < items.length ∧
        PathCollision h z0 L (rangeSib h sp ep s items (s + i)) 0 sp.length (s + i)
          (items.getD i 0))
    ∨ (sp.length ≠ H ∧ ∀ i, i < items.length →
        HeightBreak h z0 L (rangeSib h sp ep s items (s + i)) sp.length H (s + i)
          (items.getD i 0)) := by
  by_cases hPH : sp.length = H
  · subst hPH
    rcases rootPaths_sound h z0 L sp ep s items hr with h1 | h2
    · exact Or.inl ⟨rfl, h1⟩
    · exact Or.inr (Or.inl ⟨rfl, h2⟩)
  · refine Or.inr (Or.inr ⟨hPH, fun i hi => ?_⟩)
    obtain ⟨hlt, hw⟩ := item_walk hr i hi
    rcases accept_forces_height_or_break h z0 L _ sp.length H (s + i) _ hlt hw with he | hb
    · exact absurd he hPH
    · exact hb

/-! ## Honest proofs locate no break -/

/-- In an honest window, the value `sibAt` reads next to a position is the tree's sibling of
that position. -/
theorem sibAt_tree (h : Hash) (z0 : UInt256) (L : List UInt256) (sp ep v : List UInt256)
    (ℓ a e jj : ℕ) (hae : a ≤ jj) (hje : jj ≤ e) (hv : v.length = e - a + 1)
    (hval : ∀ r, r < v.length → v.getD r 0 = (levels h z0 L ℓ).getD (a + r) (zeros h z0 ℓ))
    (hsp : a % 2 = 1 → sp.getD ℓ 0 = (levels h z0 L ℓ).getD (a - 1) (zeros h z0 ℓ))
    (hep : e % 2 = 0 → ep.getD ℓ 0 = (levels h z0 L ℓ).getD (e + 1) (zeros h z0 ℓ)) :
    sibAt sp ep v ℓ a jj = (levels h z0 L ℓ).getD (sibIdx jj) (zeros h z0 ℓ) := by
  unfold sibAt
  by_cases hodd : jj % 2 = 1
  · rw [ite_eq_left hodd, sibIdx_odd hodd]
    by_cases hja : jj = a
    · rw [ite_eq_left hja, hsp (by rw [← hja]; exact hodd), hja]
    · rw [ite_eq_right hja, hval _ (by omega)]
      congr 1; omega
  · have heven : jj % 2 = 0 := by omega
    rw [ite_eq_right hodd, sibIdx_even heven]
    by_cases hje' : jj + 1 = a + v.length
    · have hje2 : jj = e := by omega
      rw [ite_eq_left hje', hep (by rw [← hje2]; exact heven), hje2]
    · rw [ite_eq_right hje', hval _ (by omega)]
      congr 1; omega

/-- On an honest proof every item's stream is the tree's own sibling path, below the height. -/
theorem rangeSib_honest (h : Hash) (z0 : UInt256) (L : List UInt256) (H s n : ℕ) (hn : 1 ≤ n)
    (j : ℕ) (hj1 : s ≤ j) (hj2 : j < s + n) (ℓ : ℕ) (hℓ : ℓ < H) :
    rangeSib h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s (treeSegment z0 L s n) j ℓ
      = (levels h z0 L ℓ).getD (sibIdx (j / 2 ^ ℓ)) (zeros h z0 ℓ) := by
  have hn' : 1 ≤ (treeSegment z0 L s n).length := by rw [treeSegment_length]; exact hn
  have hlen := win_length_abs h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s
    (treeSegment z0 L s n) hn' ℓ
  rw [treeSegment_length] at hlen
  exact sibAt_tree h z0 L _ _ _ ℓ (s / 2 ^ ℓ) ((s + n - 1) / 2 ^ ℓ) (j / 2 ^ ℓ)
    (Nat.div_le_div_right hj1) (Nat.div_le_div_right (by omega)) hlen
    (win_tree h z0 L H s n hn ℓ (by omega))
    (fun hodd => by rw [honestPath_getD _ _ _ _ _ _ hℓ, sibIdx_odd hodd])
    (fun heven => by rw [honestPath_getD _ _ _ _ _ _ hℓ, sibIdx_even heven])

theorem rootPaths_honest_no_break (h : Hash) (z0 : UInt256) (L : List UInt256) (H s n : ℕ)
    (hn : 1 ≤ n) (_hsn : s + n ≤ 2 ^ H) (_hH : H < 256) (i : ℕ) (hi : i < n) :
    ¬ PathCollision h z0 L
        (rangeSib h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s
          (treeSegment z0 L s n) (s + i)) 0 H (s + i) ((treeSegment z0 L s n).getD i 0)
    ∧ ¬ HeightBreak h z0 L
        (rangeSib h (honestPath h z0 L s H) (honestPath h z0 L (s + n - 1) H) s
          (treeSegment z0 L s n) (s + i)) H H (s + i) ((treeSegment z0 L s n).getD i 0) := by
  refine ⟨?_, heightBreak_not_tautology.1 _ _ _ _ _ _ _⟩
  rintro ⟨i', hi', hne, _⟩
  apply hne
  refine walkPair_honest h z0 L _ i' 0 (s + i) _ ?_ ?_
  · intro l _ hl
    rw [Nat.sub_zero]
    exact rangeSib_honest h z0 L H s n hn (s + i) (by omega) (by omega) l (by omega)
  · unfold treeSegment
    rw [getD_map_range _ _ _ hi, levels_zero, zeros_zero]

/-! ## The walk hashes the loop's pairs -/

theorem walk_pairs_are_loop_pairs {h : Hash} {sp ep : List UInt256} {s : ℕ}
    {items : List UInt256} {r : UInt256} (hr : rootPaths h sp ep s items = some r)
    (i ℓ : ℕ) (hi : i < items.length) (_hℓ : ℓ < sp.length) :
    (s + i) / 2 ^ (ℓ + 1) - s / 2 ^ (ℓ + 1)
        < nextLen ((s / 2 ^ ℓ) % 2) (win h sp ep s items ℓ).length
    ∧ walkPair h (rangeSib h sp ep s items (s + i)) 0 (s + i) (items.getD i 0) ℓ
      = (lhsAt sp (win h sp ep s items ℓ) ℓ ((s / 2 ^ ℓ) % 2)
            ((s + i) / 2 ^ (ℓ + 1) - s / 2 ^ (ℓ + 1)),
         rhsAt ep (win h sp ep s items ℓ) ℓ ((s / 2 ^ ℓ) % 2)
            (win h sp ep s items ℓ).length
            (nextLen ((s / 2 ^ ℓ) % 2) (win h sp ep s items ℓ).length)
            ((s + i) / 2 ^ (ℓ + 1) - s / 2 ^ (ℓ + 1))) := by
  obtain ⟨hg, _⟩ := guard_of_rootPaths hr
  obtain ⟨_, _, hn, _⟩ := (guard_eq_none_iff sp ep s items).mp hg
  have hae : s / 2 ^ ℓ ≤ (s + i) / 2 ^ ℓ := Nat.div_le_div_right (by omega)
  have hje : (s + i) / 2 ^ ℓ ≤ (s + items.length - 1) / 2 ^ ℓ := Nat.div_le_div_right (by omega)
  obtain ⟨hlt, hpair⟩ := stepWin_pair sp ep (win h sp ep s items ℓ) ℓ (s / 2 ^ ℓ)
    ((s + items.length - 1) / 2 ^ ℓ) ((s + i) / 2 ^ ℓ) hae hje
    (win_length_abs h sp ep s items hn ℓ)
  rw [← div_pow_succ', ← div_pow_succ']
  refine ⟨hlt, ?_⟩
  have hw := walk_win h sp ep s items hn (s + i) (by omega) (by omega) ℓ 0
  have h0 : win h sp ep s items 0 = items := rfl
  simp only [pow_zero, Nat.div_one, Nat.zero_add, h0] at hw
  rw [show s + i - s = i by omega] at hw
  rw [walkPair_eq_walkStep, Nat.zero_add, hw, ← hpair]
  unfold walkStep
  rfl

/-! ## What the call leaves in memory -/

theorem levelLoop_frame (h : Hash) (sp ep : List UInt256) :
    ∀ k ℓ a L (arr : List UInt256), 1 ≤ L → L ≤ arr.length →
      (levelLoop h sp ep k ℓ a L arr).length = arr.length
      ∧ (∀ j, L ≤ j → (levelLoop h sp ep k ℓ a L arr).getD j 0 = arr.getD j 0)
      ∧ (0 < k → ∀ j, nextLen (a % 2) L ≤ j →
          (levelLoop h sp ep k ℓ a L arr).getD j 0 = arr.getD j 0) := by
  intro k
  induction k with
  | zero =>
    intro ℓ a L arr _ _
    exact ⟨rfl, fun _ _ => rfl, fun hk => absurd hk (lt_irrefl 0)⟩
  | succ k ih =>
    intro ℓ a L arr hL hLn
    have hp : a % 2 < 2 := Nat.mod_lt _ (by norm_num)
    have hnl1 := nextLen_pos (a % 2) L hp hL
    have hnlL := nextLen_le (a % 2) L hp hL
    obtain ⟨hlen', _, hhigh'⟩ := foldl_inner h sp ep ℓ (a % 2) L arr hp hL hLn _ le_rfl
    obtain ⟨hlen'', hhigh'', _⟩ := ih (ℓ + 1) (a / 2) (nextLen (a % 2) L) _ hnl1
      (by rw [hlen']; omega)
    have hstep : levelLoop h sp ep (k + 1) ℓ a L arr
        = levelLoop h sp ep k (ℓ + 1) (a / 2) (nextLen (a % 2) L)
            ((List.range (nextLen (a % 2) L)).foldl
              (innerStep h sp ep ℓ (a % 2) L (nextLen (a % 2) L)) arr) := rfl
    rw [hstep]
    refine ⟨by rw [hlen'', hlen'], fun j hj => ?_, fun _ j hj => ?_⟩
    · rw [hhigh'' j (by omega), hhigh' j (by omega)]
    · rw [hhigh'' j hj, hhigh' j hj]

theorem rootPaths_frame {h : Hash} {sp ep : List UInt256} {s : ℕ} {items : List UInt256}
    {r : UInt256} {mem : List UInt256} (hr : rootPathsMem h sp ep s items = some (r, mem)) :
    mem.length = items.length ∧ mem.getD 0 0 = r
    ∧ (sp = [] → mem = items)
    ∧ (sp ≠ [] → ∀ j, nextLen (s % 2) items.length ≤ j → mem.getD j 0 = items.getD j 0) := by
  obtain ⟨hg, hx⟩ := guard_of_rootPathsMem hr
  obtain ⟨_, _, hn, _⟩ := (guard_eq_none_iff sp ep s items).mp hg
  unfold runLoop at hx
  rw [Prod.mk.injEq] at hx
  obtain ⟨hrv, hmem⟩ := hx
  obtain ⟨hlen, _, hfirst⟩ := levelLoop_frame h sp ep sp.length 0 s items.length items hn le_rfl
  refine ⟨by rw [hmem, hlen], by rw [hrv, hmem], fun hsp => ?_, fun hsp j hj => ?_⟩
  · rw [hmem, hsp]; rfl
  · rw [hmem]
    exact hfirst (List.length_pos_iff.mpr hsp) j hj

/-! ## Certificates -/

theorem RootPathsAcceptIff : Properties.RootPathsAcceptIff := by
  intro h sp ep s items
  rw [← guard_eq_none_iff, rootPaths_eq]
  constructor
  · intro hne
    by_contra hg
    rw [ite_eq_right hg] at hne
    exact hne rfl
  · intro hg
    rw [ite_eq_left hg]
    exact Option.some_ne_none _

theorem RootPathsEmptyPathIsTheItem : Properties.RootPathsEmptyPathIsTheItem := by
  refine ⟨fun h sp ep s items r hr hsp => ?_, fun h x => ?_⟩
  · obtain ⟨hg, hrv⟩ := guard_of_rootPaths hr
    obtain ⟨hlen, _, hn, hsn⟩ := (guard_eq_none_iff sp ep s items).mp hg
    subst hsp
    simp only [List.length_nil, pow_zero] at hlen hsn
    refine ⟨List.length_eq_zero_iff.mp hlen.symm, by omega, by omega, ?_⟩
    rw [hrv]
    rfl
  · have hg : guard [] [] 0 [x] = none :=
      (guard_eq_none_iff _ _ _ _).mpr ⟨rfl, by norm_num, by simp, by simp⟩
    rw [rootPaths_eq, ite_eq_left hg]
    rfl

theorem RootPathsEmptyCheckOnlyChangesReason :
    Properties.RootPathsEmptyCheckOnlyChangesReason := by
  refine ⟨fun h sp ep s items => ?_, by decide, by decide, by decide, by decide⟩
  have hiff : guardNoEmptyCheck sp ep s items = none ↔ guard sp ep s items = none := by
    rw [guardNoEmptyCheck_eq_none_iff, guard_eq_none_iff]
  unfold rootPathsNoEmptyCheck
  rw [rootPaths_eq]
  by_cases hg : guard sp ep s items = none
  · rw [ite_eq_left (hiff.mpr hg), ite_eq_left hg]
  · rw [ite_eq_right (fun h' => hg (hiff.mp h')), ite_eq_right hg]

theorem RootPathsReadsInBounds : Properties.RootPathsReadsInBounds := by
  intro s n ℓ hn
  obtain ⟨h1, h2⟩ := lenAt_bounds s n hn ℓ
  have hp : (s / 2 ^ ℓ) % 2 < 2 := Nat.mod_lt _ (by norm_num)
  refine ⟨h1, h2, nextLen_pos _ _ hp h1, fun i hi => ⟨lt_of_lt_of_le hi (nextLen_le _ _ hp h1),
    fun hc => ?_, fun hc => (rhs_idx _ _ i hp h1 hi hc).1⟩⟩
  obtain ⟨a1, a2, _⟩ := lhs_idx _ _ i hp h1 hi hc
  exact ⟨a1, a2⟩

theorem RootPathsInPlaceIsLevelByLevel : Properties.RootPathsInPlaceIsLevelByLevel := by
  intro h sp ep s items hg
  obtain ⟨_, _, hn, hsn⟩ := (guard_eq_none_iff sp ep s items).mp hg
  refine ⟨fun ℓ => ?_, win_length h sp ep s items, ?_,
    by rw [rootPaths_eq, ite_eq_left hg, runLoop_fst_eq_win hg]⟩
  · have := levelLoop_win h sp ep s items hn ℓ 0 items rfl (fun j _ => rfl)
    have h0 : win h sp ep s items 0 = items := rfl
    rw [h0] at this
    simpa only [pow_zero, Nat.div_one, Nat.zero_add] using this
  · rw [win_length_abs h sp ep s items hn,
      Nat.div_eq_of_lt (by omega : s + items.length - 1 < 2 ^ sp.length),
      Nat.div_eq_of_lt (by omega : s < 2 ^ sp.length)]

theorem RootPathsFrame : Properties.RootPathsFrame :=
  fun _ _ _ _ _ _ _ hr => rootPaths_frame hr

theorem RootPathsComplete : Properties.RootPathsComplete := rootPaths_complete

theorem RootPathsIsItemWalks : Properties.RootPathsIsItemWalks :=
  fun _ _ _ _ _ _ hr i hi => item_walk hr i hi

theorem RootPathsWalkPairsAreLoopPairs : Properties.RootPathsWalkPairsAreLoopPairs :=
  fun _ _ _ _ _ _ hr i ℓ hi hℓ => walk_pairs_are_loop_pairs hr i ℓ hi hℓ

theorem RootPathsSoundOrCollision : Properties.RootPathsSoundOrCollision := rootPaths_sound

theorem RootPathsSiblingsPinnedOrCollision : Properties.RootPathsSiblingsPinnedOrCollision :=
  rootPaths_siblings_pinned

theorem RootPathsAnyLengthOrBreak : Properties.RootPathsAnyLengthOrBreak := rootPaths_any_length

theorem RootPathsHonestNoBreak : Properties.RootPathsHonestNoBreak := rootPaths_honest_no_break

/-! ## Witnesses -/

theorem RootPathsHonestWitness : Properties.RootPathsHonestWitness := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by decide, ?_, ?_,
    honestPath_length _ _ _ _ _, by decide, by decide, fun i hi =>
      (rootPaths_honest_no_break rangeToyHash 7 [10, 20] 2 1 2 (by norm_num) (by norm_num)
        (by norm_num) i hi).1⟩
  · rw [guard_eq_none_iff, honestPath_length, honestPath_length, treeSegment_length]
    norm_num
  · rw [honestPath_length]
    exact rootPaths_complete rangeToyHash 7 [10, 20] 2 1 2 (by norm_num) (by norm_num)
      (by norm_num)

theorem RootPathsCollisionFires : Properties.RootPathsCollisionFires := by
  unfold Properties.RootPathsCollisionFires PathCollision
  decide

theorem RootPathsWrongLengthFires : Properties.RootPathsWrongLengthFires :=
  ⟨⟨by decide, by decide, HeightBreak.shortInteriorLeaf (by decide) (by decide), by decide,
      by decide⟩,
    ⟨by decide, by decide, HeightBreak.longEntryIsNode (by decide) (by decide), by decide⟩⟩

theorem RootPathsClobbersItems : Properties.RootPathsClobbersItems := by
  unfold Properties.RootPathsClobbersItems
  decide

end MerkleSpec.RootPaths
