import EraSpec.Contracts.FullMerkle.Properties.CachedNodes
import EraSpec.Contracts.FullMerkle.Proofs.Model
import EraSpec.Contracts.FullMerkle.Proofs.CapacityInvariant
import EraSpec.Contracts.Merkle.Proofs.Verifier

/-!
# Proofs: the cached-node algorithm computes the fold

Proofs of `EraSpec.Contracts.FullMerkle.Properties.CachedNodes`.

The two loops are proved by induction on the iterations left, against a description of
`_nodes` level by level:

* `updateLoop_spec` — `updateLeaf`'s loop.  At level `i` the rows `≤ i` already hold the
  new levels, and each row above agrees with its new level except at the one position on
  the updated path.  The sibling the loop reads is therefore the new level's sibling
  (`sibRead_eq`), the parent it writes is the new level's entry (`levelUp_getD`), and
  after the write the next row is exact.
* `padLoop_spec` — `pushNewLeaf`'s padding loop.  It lengthens exactly the rows whose
  last index moves when one leaf is appended, and stops at the first that does not
  (all higher ones do not move either: `div_eq_of_div_eq`).  Afterwards every row has
  the length of the appended tree's level and agrees with the old level left of the
  appended path, which is what `levels_append` says the new level is.

Everything else is assembled from `MerkleSpec`'s M-A/M-B/M-C lemmas.
-/

namespace Contracts.FullMerkle

open MerkleSpec MerkleSpec.Verifier AttackVectors.CapacityInvariant

/-! ## Arithmetic -/

private lemma div_two_pow_succ (a l : ℕ) : a / 2 ^ l / 2 = a / 2 ^ (l + 1) := by
  rw [Nat.div_div_eq_div_mul, pow_succ]

/-- Once the old and the new last index of a level coincide, they coincide above it. -/
private lemma div_eq_of_div_eq {a b i l : ℕ} (hil : i ≤ l) (h : a / 2 ^ i = b / 2 ^ i) :
    a / 2 ^ l = b / 2 ^ l := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hil
  rw [pow_add, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h]

/-- Appending one leaf moves a level's last index by at most one. -/
private lemma succ_div_le (n d : ℕ) : (n + 1) / d ≤ n / d + 1 := by
  rw [Nat.succ_div]
  split_ifs <;> omega

/-! ## Storage-array access -/

private lemma nodeAt_of_row {N : List (List UInt256)} {row : List UInt256} {i : ℕ}
    (hrow : N[i]? = some row) (j : ℕ) : nodeAt N i j = row[j]? := by
  simp [nodeAt, hrow]

private lemma setNode_of_row {N : List (List UInt256)} {row : List UInt256} {i j : ℕ}
    (hrow : N[i]? = some row) (hj : j < row.length) (a : UInt256) :
    setNode N i j a = some (N.set i (row.set j a)) := by
  simp [setNode, hrow, hj]

private lemma pushNode_of_row {N : List (List UInt256)} {row : List UInt256} {i : ℕ}
    (hrow : N[i]? = some row) (a : UInt256) :
    pushNode N i a = some (N.set i (row ++ [a])) := by
  simp [pushNode, hrow]

/-- `getD` in range is the entry `getElem?` returns. -/
private lemma getElem?_eq_some_getD {L : List UInt256} {j : ℕ} (hj : j < L.length)
    (d : UInt256) : L[j]? = some (L.getD j d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]

private lemma getD_of_getElem? {L : List UInt256} {j : ℕ} {a : UInt256} (h : L[j]? = some a)
    (d : UInt256) : L.getD j d = a := by
  rw [List.getD_eq_getElem?_getD, h, Option.getD_some]

private lemma lt_length_of_getElem? {L : List UInt256} {j : ℕ} {a : UInt256}
    (h : L[j]? = some a) : j < L.length :=
  (List.getElem?_eq_some_iff.mp h).1

/-- A row with the right length that agrees with `T` off position `p`, once `p` is
written with `T`'s entry, is `T`. -/
private lemma set_eq_of_agree {row T : List UInt256} {p : ℕ} {v : UInt256}
    (hlen : row.length = T.length) (hoff : ∀ j, j ≠ p → row[j]? = T[j]?)
    (hv : T[p]? = some v) : row.set p v = T := by
  apply List.ext_getElem?
  intro q
  by_cases hq : q = p
  · subst hq
    rw [List.getElem?_set_self (by have := lt_length_of_getElem? hv; omega), hv]
  · rw [List.getElem?_set_ne (Ne.symm hq), hoff q hq]

/-- `getD`-agreement of two lists of the same length, as `getElem?`-agreement. -/
private lemma getElem?_eq_of_getD {A B : List UInt256} {j : ℕ} (hlen : A.length = B.length)
    (hD : ∀ d, A.getD j d = B.getD j d) : A[j]? = B[j]? := by
  rcases Nat.lt_or_ge j A.length with hj | hj
  · rw [getElem?_eq_some_getD hj 0, getElem?_eq_some_getD (by omega) 0, hD 0]
  · rw [List.getElem?_eq_none hj, List.getElem?_eq_none (by omega)]

/-! ## The sibling read -/

/-- **The sibling read is the level's sibling.**  If row `l` of `_nodes` is a list `row`
whose last index is `mx`, `_zeros[l]` is the level zero `z`, and `j ≤ mx`, then
`sibRead` returns `row.getD (sibIdx j) z`: the neighbour inside the row, or `z` when `j`
is the last, even, index. -/
private lemma sibRead_eq {zs : List UInt256} {N : List (List UInt256)} {row : List UInt256}
    {l j mx : ℕ} {z : UInt256} (hrow : N[l]? = some row) (hlen : row.length = mx + 1)
    (hzs : zs[l]? = some z) (hj : j ≤ mx) :
    sibRead zs N l j mx = some (row.getD (sibIdx j) z) := by
  unfold sibRead
  by_cases hpar : j % 2 = 0
  · have hs : sibIdx j = j + 1 := by simp [sibIdx]; omega
    rw [ite_eq_left hpar, hs]
    by_cases hlast : mx = j
    · rw [ite_eq_left hlast, hzs, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by omega), Option.getD_none]
    · rw [ite_eq_right hlast, nodeAt_of_row hrow, getElem?_eq_some_getD (by omega)]
  · have hs : sibIdx j = j - 1 := by simp [sibIdx]; omega
    rw [ite_eq_right hpar, hs, nodeAt_of_row hrow, getElem?_eq_some_getD (by omega)]

/-! ## One level up

The parent the loop computes from the accumulator and the sibling is the next level's
entry.  This is `levelUp_getD` read at the parent index `j / 2`. -/

private lemma parent_eq (h : Hash) (z0 : UInt256) (L : List UInt256) (i j : ℕ) (cur : UInt256)
    (hcur : (levels h z0 L i)[j]? = some cur) :
    (levels h z0 L (i + 1))[j / 2]?
      = some (if j % 2 = 0 then h cur ((levels h z0 L i).getD (sibIdx j) (zeros h z0 i))
              else h ((levels h z0 L i).getD (sibIdx j) (zeros h z0 i)) cur) := by
  have hj := lt_length_of_getElem? hcur
  have h2 : 2 * (j / 2) < (levels h z0 L i).length := by omega
  have hlen1 : j / 2 < (levels h z0 L (i + 1)).length := by
    rw [levels_succ, levelUp_length]; omega
  rw [getElem?_eq_some_getD hlen1 0, levels_succ,
    levelUp_getD h (zeros h z0 i) 0 _ (j / 2) h2]
  congr 1
  by_cases hpar : j % 2 = 0
  · have hs : sibIdx j = j + 1 := by simp [sibIdx]; omega
    rw [ite_eq_left hpar, hs, show 2 * (j / 2) = j from by omega, getD_of_getElem? hcur]
  · have hs : sibIdx j = j - 1 := by simp [sibIdx]; omega
    rw [ite_eq_right hpar, hs, show 2 * (j / 2) = j - 1 from by omega,
      show j - 1 + 1 = j from by omega, getD_of_getElem? hcur,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : j - 1 < (levels h z0 L i).length),
      Option.getD_some, Option.getD_some]

/-! ## `updateLeaf`'s loop -/

/-- **The update loop recomputes the levels of `L`.**  Fix the target leaves `L`
(nonempty), the updated index `idx` and the height `H` (`L` fits it), with `_zeros`
correct below `H`.  At iteration `i` (with `k = H - i` left), suppose rows `0..i` of
`_nodes` are the levels of `L`, each row above `i` agrees with its level of `L` except
at the path position `idx / 2^l`, and the accumulator is the level-`i` path entry.  Then
the loop ends with `_nodes` the levels of `L` and returns `rootOf h z0 L H`. -/
private theorem updateLoop_spec (h : Hash) (z0 : UInt256) (L : List UInt256) (H idx : ℕ)
    (zs : List UInt256) (hne : L ≠ []) (hidx : idx < L.length) (hcap : L.length ≤ 2 ^ H)
    (hzs : ∀ l, l < H → zs[l]? = some (zeros h z0 l)) :
    ∀ (k i : ℕ) (N : List (List UInt256)) (cur : UInt256),
      i + k = H → N.length = H + 1 →
      (∀ l, l ≤ i → N[l]? = some (levels h z0 L l)) →
      (∀ l, i < l → l ≤ H → ∃ row, N[l]? = some row ∧ row.length = (levels h z0 L l).length
        ∧ ∀ j, j ≠ idx / 2 ^ l → row[j]? = (levels h z0 L l)[j]?) →
      (levels h z0 L i)[idx / 2 ^ i]? = some cur →
      updateLoop h zs k i (idx / 2 ^ i) ((L.length - 1) / 2 ^ i) cur N
        = some ((List.range (H + 1)).map (levels h z0 L), rootOf h z0 L H) := by
  have hn : L.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hne
  intro k
  induction k with
  | zero =>
    intro i N cur hik hN hdone _ hcur
    rw [Nat.add_zero] at hik
    subst hik
    have hNeq : N = (List.range (i + 1)).map (levels h z0 L) := by
      apply List.ext_getElem?
      intro l
      by_cases hl : l ≤ i
      · rw [hdone l hl, List.getElem?_map, List.getElem?_range (by omega)]
        rfl
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
    have hroot : cur = rootOf h z0 L i := by
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hidx hcap)] at hcur
      rw [rootOf, List.headD_eq_getD, getD_of_getElem? hcur]
    simp only [updateLoop, hNeq, hroot]
  | succ k ih =>
    intro i N cur hik hN hdone habove hcur
    have hi : i < H := by omega
    have hrowlen : (levels h z0 L i).length = (L.length - 1) / 2 ^ i + 1 :=
      levels_length h z0 L hn i
    have hjmx : idx / 2 ^ i ≤ (L.length - 1) / 2 ^ i := Nat.div_le_div_right (by omega)
    have hsib := sibRead_eq (hdone i le_rfl) hrowlen (hzs i hi) hjmx
    have hpar := parent_eq h z0 L i (idx / 2 ^ i) cur hcur
    rw [div_two_pow_succ] at hpar
    obtain ⟨row, hrow, hrowlen', hrowoff⟩ := habove (i + 1) (by omega) (by omega)
    have hj2 : idx / 2 ^ i / 2 < row.length := by
      rw [div_two_pow_succ, hrowlen']; exact lt_length_of_getElem? hpar
    have hset := setNode_of_row hrow hj2
      (if idx / 2 ^ i % 2 = 0
        then h cur ((levels h z0 L i).getD (sibIdx (idx / 2 ^ i)) (zeros h z0 i))
        else h ((levels h z0 L i).getD (sibIdx (idx / 2 ^ i)) (zeros h z0 i)) cur)
    rw [div_two_pow_succ] at hset
    rw [set_eq_of_agree hrowlen' hrowoff hpar] at hset
    have hNi1 : i + 1 < N.length := by omega
    simp only [updateLoop, hsib, Option.bind_eq_bind, Option.bind_some]
    rw [div_two_pow_succ, div_two_pow_succ, hset, Option.bind_some]
    refine ih (i + 1) _ _ (by omega) (by rw [List.length_set]; exact hN) ?_ ?_ hpar
    · intro l hl
      by_cases hli : l = i + 1
      · subst hli
        exact List.getElem?_set_self hNi1
      · rw [List.getElem?_set_ne (Ne.symm hli)]
        exact hdone l (by omega)
    · intro l hl1 hl2
      rw [List.getElem?_set_ne (by omega)]
      exact habove l (by omega) hl2

/-- The loop from level 0, as `updateLeaf` calls it. -/
private theorem updateLoop_from_zero (h : Hash) (z0 : UInt256) (L : List UInt256) (H idx : ℕ)
    (zs : List UInt256) (N : List (List UInt256)) (hne : L ≠ []) (hidx : idx < L.length)
    (hcap : L.length ≤ 2 ^ H) (hzs : ∀ l, l < H → zs[l]? = some (zeros h z0 l))
    (hN : N.length = H + 1) (h0 : N[0]? = some L)
    (habove : ∀ l, 0 < l → l ≤ H → ∃ row, N[l]? = some row
      ∧ row.length = (levels h z0 L l).length
      ∧ ∀ j, j ≠ idx / 2 ^ l → row[j]? = (levels h z0 L l)[j]?) :
    updateLoop h zs H 0 idx (L.length - 1) (L.getD idx 0) N
      = some ((List.range (H + 1)).map (levels h z0 L), rootOf h z0 L H) := by
  have := updateLoop_spec h z0 L H idx zs hne hidx hcap hzs H 0 N (L.getD idx 0) (by omega) hN
    (fun l hl => by rw [show l = 0 by omega, levels_zero]; exact h0) habove
    (by rw [pow_zero, Nat.div_one, levels_zero]; exact getElem?_eq_some_getD hidx 0)
  simpa only [pow_zero, Nat.div_one] using this

/-! ## Facts about `Represents` -/

private lemma cachedLevel_of_ne {h : Hash} {z0 : UInt256} {L : List UInt256} (hne : L ≠ [])
    (l : ℕ) : cachedLevel h z0 L l = levels h z0 L l := by
  simp [cachedLevel, hne]

private lemma cachedLevel_nil (h : Hash) (z0 : UInt256) (l : ℕ) :
    cachedLevel h z0 [] l = [zeros h z0 l] := by
  simp [cachedLevel]

private lemma Represents.nodes_getElem? {h : Hash} {z0 : UInt256} {L : List UInt256}
    {S : FullTree} (hR : Represents h z0 L S) {l : ℕ} (hl : l ≤ S.height) :
    S.nodes[l]? = some (cachedLevel h z0 L l) := by
  rw [hR.nodes_eq, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

private lemma Represents.zeros_getElem? {h : Hash} {z0 : UInt256} {L : List UInt256}
    {S : FullTree} (hR : Represents h z0 L S) {l : ℕ} (hl : l ≤ S.height) :
    S.zeros[l]? = some (zeros h z0 l) := by
  rw [hR.zeros_eq, List.getElem?_map, List.getElem?_range (by omega)]
  rfl

private lemma Represents.nodes_length {h : Hash} {z0 : UInt256} {L : List UInt256}
    {S : FullTree} (hR : Represents h z0 L S) : S.nodes.length = S.height + 1 := by
  rw [hR.nodes_eq, List.length_map, List.length_range]

private lemma Represents.zeros_length {h : Hash} {z0 : UInt256} {L : List UInt256}
    {S : FullTree} (hR : Represents h z0 L S) : S.zeros.length = S.height + 1 := by
  rw [hR.zeros_eq, List.length_map, List.length_range]

/-- For a nonempty tree the rows are the abstract levels. -/
private lemma Represents.nodes_eq_levels {h : Hash} {z0 : UInt256} {L : List UInt256}
    {S : FullTree} (hR : Represents h z0 L S) (hne : L ≠ []) :
    S.nodes = (List.range (S.height + 1)).map (levels h z0 L) := by
  rw [hR.nodes_eq]
  exact List.map_congr_left (fun l _ => cachedLevel_of_ne hne l)

/-! ## `updateLeaf` -/

theorem updateLeaf_computes_root (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (S : FullTree) (idx : ℕ) (x : UInt256) (hR : Represents h z0 leaves S)
    (hidx : idx < leaves.length) :
    ∃ S' : FullTree, updateLeaf h S idx x = some (S', rootOf h z0 (leaves.set idx x) S.height)
      ∧ Represents h z0 (leaves.set idx x) S'
      ∧ S'.height = S.height ∧ S'.leafNumber = S.leafNumber := by
  have hne : leaves ≠ [] := by rintro rfl; simp at hidx
  have hlen' : (leaves.set idx x).length = leaves.length := List.length_set
  have hne' : leaves.set idx x ≠ [] := by
    intro he; rw [he, List.length_nil] at hlen'; omega
  have hrow0 : S.nodes[0]? = some leaves := by
    rw [hR.nodes_getElem? (Nat.zero_le _), cachedLevel_of_ne hne, levels_zero]
  have hset0 := setNode_of_row hrow0 hidx x
  have hloop := updateLoop_from_zero h z0 (leaves.set idx x) S.height idx S.zeros
    (S.nodes.set 0 (leaves.set idx x)) hne' (by omega) (by rw [hlen']; exact hR.capacity)
    (fun l hl => hR.zeros_getElem? (by omega))
    (by rw [List.length_set, hR.nodes_length])
    (List.getElem?_set_self (by rw [hR.nodes_length]; omega))
    (by
      intro l hl _
      refine ⟨levels h z0 leaves l, ?_, (levels_set_length h z0 leaves idx x l).symm, ?_⟩
      · rw [List.getElem?_set_ne (by omega), hR.nodes_getElem? (by omega), cachedLevel_of_ne hne]
      · intro j hj
        exact (getElem?_eq_of_getD (levels_set_length h z0 leaves idx x l)
          (fun d => levels_set_off_path h z0 leaves idx x l j d hj)).symm)
  rw [getD_of_getElem? (List.getElem?_set_self hidx), hlen'] at hloop
  refine ⟨{ S with nodes := (List.range (S.height + 1)).map (levels h z0 (leaves.set idx x)) },
    ?_, ?_, rfl, rfl⟩
  · unfold updateLeaf
    rw [ite_eq_right (by rw [hR.leafNumber_eq]; omega),
      ite_eq_right (by rw [hR.leafNumber_eq]; omega), hset0, hR.leafNumber_eq]
    simp only [Option.bind_eq_bind, Option.bind_some, hloop, Option.pure_def]
  · refine ⟨by rw [hR.leafNumber_eq, hlen'], by rw [hlen']; exact hR.capacity, hR.zeros_eq, ?_⟩
    exact List.map_congr_left (fun l _ => (cachedLevel_of_ne hne' l).symm)

theorem updateLeaf_out_of_range_reverts (h : Hash) (S : FullTree) (idx : ℕ) (x : UInt256)
    (hidx : S.leafNumber ≤ idx) : updateLeaf h S idx x = none := by
  unfold updateLeaf
  by_cases h0 : S.leafNumber = 0
  · rw [ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_left (by omega)]

/-! ## `pushNewLeaf`'s padding loop

Write `n` for the old leaf count.  Appending a leaf makes level `l` of the tree
`n / 2^l + 1` long (`levels_append`); before, it was `(n - 1) / 2^l + 1` long. -/

/-- Row `l` has the old length and the old entries left of the appended path. -/
private def Unpadded (h : Hash) (z0 : UInt256) (L : List UInt256) (N : List (List UInt256))
    (l : ℕ) : Prop :=
  ∃ row, N[l]? = some row ∧ row.length = (L.length - 1) / 2 ^ l + 1
    ∧ ∀ j, j < L.length / 2 ^ l → row[j]? = (levels h z0 L l)[j]?

/-- Row `l` has the appended tree's length and the old entries left of the appended path:
what `updateLeaf(n, x)` needs to find before it writes the path. -/
private def Ready (h : Hash) (z0 : UInt256) (L : List UInt256) (N : List (List UInt256))
    (l : ℕ) : Prop :=
  ∃ row, N[l]? = some row ∧ row.length = L.length / 2 ^ l + 1
    ∧ ∀ j, j < L.length / 2 ^ l → row[j]? = (levels h z0 L l)[j]?

/-- A row whose last index does not move is ready as it is. -/
private lemma ready_of_unpadded {h : Hash} {z0 : UInt256} {L : List UInt256}
    {N : List (List UInt256)} {l : ℕ} (hu : Unpadded h z0 L N l)
    (heq : (L.length - 1) / 2 ^ l = L.length / 2 ^ l) : Ready h z0 L N l := by
  obtain ⟨row, hrow, hlen, hagree⟩ := hu
  exact ⟨row, hrow, by rw [hlen, heq], hagree⟩

/-- **The padding loop readies every row.**  With `_zeros` correct below `H'` and the
appended leaf's index `n < 2^H'`: at iteration `i`, if the rows below `i` are ready and
the rows from `i` to `H'` are unpadded, the loop succeeds and leaves every row ready. -/
private theorem padLoop_spec (h : Hash) (z0 : UInt256) (L : List UInt256) (H' : ℕ)
    (zs : List UInt256) (hcap : L.length < 2 ^ H')
    (hzs : ∀ l, l < H' → zs[l]? = some (zeros h z0 l)) :
    ∀ (k i : ℕ) (N : List (List UInt256)), i + k = H' → N.length = H' + 1 →
      (∀ l, l < i → Ready h z0 L N l) → (∀ l, i ≤ l → l ≤ H' → Unpadded h z0 L N l) →
      ∃ N', padLoop zs k i ((L.length - 1) / 2 ^ i) (L.length / 2 ^ i) N = some N'
        ∧ N'.length = H' + 1 ∧ ∀ l, l ≤ H' → Ready h z0 L N' l := by
  have htop : (L.length - 1) / 2 ^ H' = L.length / 2 ^ H' := by
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt hcap]
  intro k
  induction k with
  | zero =>
    intro i N hik hN hready hunp
    rw [Nat.add_zero] at hik
    subst hik
    refine ⟨N, rfl, hN, fun l hl => ?_⟩
    rcases Nat.lt_or_ge l i with hli | hli
    · exact hready l hli
    · exact ready_of_unpadded (hunp l hli hl) (by rw [show l = i by omega]; exact htop)
  | succ k ih =>
    intro i N hik hN hready hunp
    have hi : i < H' := by omega
    by_cases heq : (L.length - 1) / 2 ^ i = L.length / 2 ^ i
    · -- `break`: every row from `i` up keeps its last index
      refine ⟨N, by simp only [padLoop, heq, ite_true], hN, fun l hl => ?_⟩
      rcases Nat.lt_or_ge l i with hli | hli
      · exact hready l hli
      · exact ready_of_unpadded (hunp l hli hl) (div_eq_of_div_eq hli heq)
    · -- `_nodes[i].push(_zeros[i])`: row `i` grows by its level zero
      obtain ⟨row, hrow, hlen, hagree⟩ := hunp i le_rfl (by omega)
      have hgrow : L.length / 2 ^ i = (L.length - 1) / 2 ^ i + 1 := by
        have h1 : (L.length - 1) / 2 ^ i ≤ L.length / 2 ^ i := Nat.div_le_div_right (by omega)
        have h2 : L.length / 2 ^ i ≤ (L.length - 1) / 2 ^ i + 1 := by
          rcases Nat.eq_zero_or_pos L.length with h0 | hpos
          · rw [h0]; simp
          · have := succ_div_le (L.length - 1) (2 ^ i)
            rwa [show L.length - 1 + 1 = L.length by omega] at this
        omega
      have hpush := pushNode_of_row hrow (zeros h z0 i)
      have hNi : i < N.length := by omega
      obtain ⟨N', hloop, hN', hready'⟩ := ih (i + 1) (N.set i (row ++ [zeros h z0 i]))
        (by omega) (by rw [List.length_set]; exact hN)
        (by
          intro l hl
          by_cases hli : l = i
          · subst hli
            refine ⟨row ++ [zeros h z0 l], List.getElem?_set_self hNi, ?_, ?_⟩
            · rw [List.length_append, hlen, hgrow, List.length_singleton]
            · intro j hj
              rw [List.getElem?_append_left (by omega)]
              exact hagree j hj
          · rw [Ready, List.getElem?_set_ne (Ne.symm hli)]
            exact hready l (by omega))
        (by
          intro l hl1 hl2
          rw [Unpadded, List.getElem?_set_ne (by omega)]
          exact hunp l (by omega) hl2)
      refine ⟨N', ?_, hN', hready'⟩
      simp only [padLoop, heq, ite_false, hzs i hi, hpush, Option.bind_eq_bind, Option.bind_some]
      rw [div_two_pow_succ, div_two_pow_succ]
      exact hloop

/-- **The padding block readies every row.**  If every row up to `_height` is unpadded
and the appended index is below capacity, `pad` succeeds, changes only `_nodes`, and
leaves every row ready.  On an empty tree there is nothing to pad: every row already
has length `1 = 0 / 2^l + 1`. -/
private theorem pad_spec (h : Hash) (z0 : UInt256) (L : List UInt256) (S₂ : FullTree)
    (hcap : L.length < 2 ^ S₂.height)
    (hzs : ∀ l, l < S₂.height → S₂.zeros[l]? = some (zeros h z0 l))
    (hN : S₂.nodes.length = S₂.height + 1)
    (hunp : ∀ l, l ≤ S₂.height → Unpadded h z0 L S₂.nodes l) :
    ∃ S₃, pad S₂ L.length = some S₃ ∧ S₃.height = S₂.height ∧ S₃.leafNumber = S₂.leafNumber
      ∧ S₃.zeros = S₂.zeros ∧ S₃.nodes.length = S₂.height + 1
      ∧ ∀ l, l ≤ S₂.height → Ready h z0 L S₃.nodes l := by
  by_cases h0 : L.length = 0
  · refine ⟨S₂, by simp [pad, h0], rfl, rfl, rfl, hN, fun l hl => ?_⟩
    exact ready_of_unpadded (hunp l hl) (by rw [h0])
  · obtain ⟨N', hloop, hN', hready⟩ := padLoop_spec h z0 L S₂.height S₂.zeros hcap hzs
      S₂.height 0 S₂.nodes (by omega) hN (fun l hl => absurd hl (Nat.not_lt_zero _))
      (fun l _ hl => hunp l hl)
    refine ⟨{ S₂ with nodes := N' }, ?_, rfl, rfl, rfl, hN', hready⟩
    simp only [pow_zero, Nat.div_one] at hloop
    simp [pad, h0, hloop]

/-! ## `updateLeaf(n, x)` on ready rows -/

/-- A ready row, against the appended tree's level: the right length, and agreement off
the appended path. -/
private lemma ready_row_agrees (h : Hash) (z0 : UInt256) (L : List UInt256) (x : UInt256)
    {row : List UInt256} (l : ℕ) (hlen : row.length = L.length / 2 ^ l + 1)
    (hagree : ∀ j, j < L.length / 2 ^ l → row[j]? = (levels h z0 L l)[j]?) :
    row.length = (levels h z0 (L ++ [x]) l).length
      ∧ ∀ j, j ≠ L.length / 2 ^ l → row[j]? = (levels h z0 (L ++ [x]) l)[j]? := by
  have hple := div_le_levels_length h z0 L l
  have hlenA : (levels h z0 (L ++ [x]) l).length = L.length / 2 ^ l + 1 := by
    rw [levels_append h z0 L x l, List.length_append, List.length_take, List.length_singleton,
      min_eq_left hple]
  refine ⟨by rw [hlen, hlenA], fun j hj => ?_⟩
  rcases Nat.lt_or_ge j (L.length / 2 ^ l) with hlt | hge
  · rw [hagree j hlt, levels_append h z0 L x l,
      List.getElem?_append_left (by rw [List.length_take, min_eq_left hple]; exact hlt),
      List.getElem?_take, ite_eq_left hlt]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **`updateLeaf(n, x)` on ready rows writes the appended tree.**  This is the last call
of `pushNewLeaf`, with `_leafNumber` already incremented. -/
private theorem updateLeaf_of_ready (h : Hash) (z0 : UInt256) (L : List UInt256) (x : UInt256)
    (S₃ : FullTree) (hnum : S₃.leafNumber = L.length + 1) (hcap : L.length < 2 ^ S₃.height)
    (hzs : ∀ l, l < S₃.height → S₃.zeros[l]? = some (zeros h z0 l))
    (hN : S₃.nodes.length = S₃.height + 1)
    (hready : ∀ l, l ≤ S₃.height → Ready h z0 L S₃.nodes l) :
    updateLeaf h S₃ L.length x
      = some ({ S₃ with nodes := (List.range (S₃.height + 1)).map (levels h z0 (L ++ [x])) },
          rootOf h z0 (L ++ [x]) S₃.height) := by
  obtain ⟨row0, hrow0, hlen0, hagree0⟩ := hready 0 (Nat.zero_le _)
  rw [pow_zero, Nat.div_one] at hlen0 hagree0
  have hset0 := setNode_of_row hrow0 (show L.length < row0.length by omega) x
  have hrow0_eq : row0.set L.length x = L ++ [x] := by
    refine set_eq_of_agree (by rw [hlen0, List.length_append, List.length_singleton])
      (fun j hj => ?_) List.getElem?_concat_length
    rcases Nat.lt_or_ge j L.length with hlt | hge
    · rw [hagree0 j hlt, levels_zero, List.getElem?_append_left hlt]
    · rw [List.getElem?_eq_none (by omega),
        List.getElem?_eq_none (by rw [List.length_append, List.length_singleton]; omega)]
  rw [hrow0_eq] at hset0
  have hloop := updateLoop_from_zero h z0 (L ++ [x]) S₃.height L.length S₃.zeros
    (S₃.nodes.set 0 (L ++ [x])) (by simp) (by simp)
    (by rw [List.length_append, List.length_singleton]; omega) hzs
    (by rw [List.length_set, hN]) (List.getElem?_set_self (by omega))
    (by
      intro l hl1 hl2
      obtain ⟨row, hrow, hlen, hagree⟩ := hready l hl2
      exact ⟨row, by rw [List.getElem?_set_ne (by omega)]; exact hrow,
        ready_row_agrees h z0 L x l hlen hagree⟩)
  rw [List.length_append, List.length_singleton, Nat.add_sub_cancel,
    getD_of_getElem? List.getElem?_concat_length] at hloop
  unfold updateLeaf
  rw [ite_eq_right (by omega), ite_eq_right (by omega), hset0, hnum, Nat.add_sub_cancel]
  simp only [Option.bind_eq_bind, Option.bind_some, hloop, Option.pure_def]

/-! ## `pushNewLeaf` -/

/-- `pushNewLeaf` with its `do` block written out as binds. -/
private lemma pushNewLeaf_eq (h : Hash) (S : FullTree) (x : UInt256) :
    pushNewLeaf h S x
      = (if S.leafNumber = 2 ^ S.height then grow h { S with leafNumber := S.leafNumber + 1 }
          else some { S with leafNumber := S.leafNumber + 1 }).bind
        (fun S₂ => (pad S₂ S.leafNumber).bind fun S₃ => updateLeaf h S₃ S.leafNumber x) := by
  unfold pushNewLeaf
  by_cases hc : S.leafNumber = 2 ^ S.height
  · simp only [hc, ite_true]; rfl
  · simp only [hc, ite_false]; rfl

/-- The state after `index = _leafNumber++` and the growth branch (FullMerkle.sol:43-52):
the height grows exactly when the tree is full, `_zeros` gains the next zero, and every
row up to the new height is unpadded (the new top row `[zeros (H+1)]` has the old length
`1` and nothing left of the appended path to agree on). -/
private theorem grow_spec (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree)
    (hR : Represents h z0 leaves S) :
    ∃ S₂ : FullTree,
      (if S.leafNumber = 2 ^ S.height then grow h { S with leafNumber := S.leafNumber + 1 }
        else some { S with leafNumber := S.leafNumber + 1 }) = some S₂
      ∧ S₂.height = (if leaves.length = 2 ^ S.height then S.height + 1 else S.height)
      ∧ S₂.leafNumber = leaves.length + 1
      ∧ S₂.zeros = (List.range (S₂.height + 1)).map (zeros h z0)
      ∧ S₂.nodes.length = S₂.height + 1
      ∧ (∀ l, l ≤ S₂.height → Unpadded h z0 leaves S₂.nodes l)
      ∧ leaves.length < 2 ^ S₂.height := by
  have hnum := hR.leafNumber_eq
  have hcap := hR.capacity
  by_cases hfull : leaves.length = 2 ^ S.height
  · -- the growth branch: `_height += 1`, push `h(topZero, topZero)` twice
    have hne : leaves ≠ [] := by
      intro he; rw [he, List.length_nil] at hfull; exact absurd hfull (by positivity)
    have hn : leaves.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hne
    have htop : S.zeros[S.height + 1 - 1]? = some (zeros h z0 S.height) := by
      rw [Nat.add_sub_cancel]; exact hR.zeros_getElem? le_rfl
    refine ⟨⟨S.height + 1, S.leafNumber + 1,
        S.nodes ++ [[h (zeros h z0 S.height) (zeros h z0 S.height)]],
        S.zeros ++ [h (zeros h z0 S.height) (zeros h z0 S.height)]⟩,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_left (by rw [hnum]; exact hfull)]
      simp only [grow, htop, Option.map_some]
    · rw [ite_eq_left hfull]
    · simp only [hnum]
    · simp only
      rw [List.range_succ, List.map_append, ← hR.zeros_eq, List.map_singleton, zeros_succ]
    · simp only [List.length_append, hR.nodes_length, List.length_singleton]
    · intro l hl
      simp only at hl
      rcases Nat.lt_or_ge l (S.height + 1) with hlt | hge
      · refine ⟨levels h z0 leaves l, ?_, levels_length h z0 leaves hn l, fun _ _ => rfl⟩
        rw [List.getElem?_append_left (by rw [hR.nodes_length]; exact hlt),
          hR.nodes_getElem? (by omega), cachedLevel_of_ne hne]
      · have hl' : l = S.height + 1 := by omega
        subst hl'
        refine ⟨[h (zeros h z0 S.height) (zeros h z0 S.height)], ?_, ?_, ?_⟩
        · rw [List.getElem?_append_right (by rw [hR.nodes_length]),
            hR.nodes_length, Nat.sub_self]
          rfl
        · rw [List.length_singleton, Nat.div_eq_of_lt (by rw [pow_succ]; omega)]
        · intro j hj
          rw [Nat.div_eq_of_lt (by rw [pow_succ]; omega)] at hj
          omega
    · simp only
      rw [pow_succ]; omega
  · -- no growth: only `_leafNumber` moves
    refine ⟨{ S with leafNumber := S.leafNumber + 1 }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [ite_eq_right (by rw [hnum]; exact hfull)]
    · rw [ite_eq_right hfull]
    · simp only [hnum]
    · exact hR.zeros_eq
    · exact hR.nodes_length
    · intro l hl
      by_cases he : leaves = []
      · subst he
        refine ⟨[zeros h z0 l], ?_, by simp, fun j hj => by simp at hj⟩
        rw [hR.nodes_getElem? hl, cachedLevel_nil]
      · refine ⟨levels h z0 leaves l, ?_,
          levels_length h z0 leaves (by simpa [List.length_eq_zero_iff] using he) l,
          fun _ _ => rfl⟩
        rw [hR.nodes_getElem? hl, cachedLevel_of_ne he]
    · exact lt_of_le_of_ne hcap hfull

theorem pushNewLeaf_computes_root (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (S : FullTree) (x : UInt256) (hR : Represents h z0 leaves S) :
    ∃ S' : FullTree, pushNewLeaf h S x = some (S', rootOf h z0 (leaves ++ [x]) S'.height)
      ∧ Represents h z0 (leaves ++ [x]) S'
      ∧ (⟨S'.leafNumber, S'.height⟩ : TreeDims) = push ⟨S.leafNumber, S.height⟩ := by
  obtain ⟨S₂, hS₂, hH₂, hnum₂, hzs₂, hN₂, hunp₂, hcap₂⟩ := grow_spec h z0 leaves S hR
  have hzs₂' : ∀ l, l < S₂.height → S₂.zeros[l]? = some (zeros h z0 l) := by
    intro l hl
    rw [hzs₂, List.getElem?_map, List.getElem?_range (by omega)]
    rfl
  obtain ⟨S₃, hpad, hH₃, hnum₃, hzs₃, hN₃, hready₃⟩ :=
    pad_spec h z0 leaves S₂ hcap₂ hzs₂' hN₂ hunp₂
  have hupd := updateLeaf_of_ready h z0 leaves x S₃ (by rw [hnum₃, hnum₂])
    (by rw [hH₃]; exact hcap₂) (by rw [hzs₃, hH₃]; exact hzs₂') (by rw [hN₃, hH₃])
    (by rw [hH₃]; exact hready₃)
  refine ⟨{ S₃ with nodes := (List.range (S₃.height + 1)).map (levels h z0 (leaves ++ [x])) },
    ?_, ?_, ?_⟩
  · rw [pushNewLeaf_eq, hS₂, Option.bind_some, hR.leafNumber_eq, hpad, Option.bind_some, hupd]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [hnum₃, hnum₂, List.length_append, List.length_singleton]
    · simp only [List.length_append, List.length_singleton, hH₃]; omega
    · simp only [hzs₃, hzs₂, hH₃]
    · exact List.map_congr_left (fun l _ => (cachedLevel_of_ne (by simp) l).symm)
  · simp only [hnum₃, hnum₂, hH₃, hH₂, push, hR.leafNumber_eq]
    split_ifs <;> rfl

/-! ## `setup` -/

theorem setup_represents_empty (h : Hash) (z0 : UInt256) :
    Represents h z0 [] (setup FullTree.empty z0).1
      ∧ (setup FullTree.empty z0).2 = rootOf h z0 [] 0 := by
  refine ⟨⟨rfl, ?_, ?_, ?_⟩, ?_⟩ <;> simp [setup, FullTree.empty, cachedLevel_nil, rootOf]

/-! ## `root` -/

theorem root_is_fold (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree)
    (hR : Represents h z0 leaves S) : root S = some (rootOf h z0 leaves S.height) := by
  unfold root
  rw [nodeAt_of_row (hR.nodes_getElem? le_rfl)]
  by_cases he : leaves = []
  · subst he
    rw [cachedLevel_nil]
    simp [rootOf, levels_nil]
  · rw [cachedLevel_of_ne he,
      levels_height_singleton h z0 leaves S.height (by simpa [List.length_eq_zero_iff] using he)
        hR.capacity]
    rfl

/-! ## `merklePath` -/

/-- **The path loop reads the honest siblings.**  On rows that are exactly the levels of
`L`, with `_zeros` correct below `H`, the loop from level `lvl` returns `honestSibs h z0
L i` at the levels `lvl, …, H - 1`. -/
private theorem pathLoop_spec (h : Hash) (z0 : UInt256) (L : List UInt256) (H i : ℕ)
    (zs : List UInt256) (N : List (List UInt256)) (hne : L ≠ []) (hi : i < L.length)
    (hzs : ∀ l, l < H → zs[l]? = some (zeros h z0 l))
    (hN : ∀ l, l ≤ H → N[l]? = some (levels h z0 L l)) :
    ∀ k lvl : ℕ, lvl + k = H →
      pathLoop zs N k lvl (i / 2 ^ lvl) ((L.length - 1) / 2 ^ lvl)
        = some ((List.range' lvl k).map (honestSibs h z0 L i)) := by
  have hn : L.length ≠ 0 := by simpa [List.length_eq_zero_iff] using hne
  intro k
  induction k with
  | zero => intro lvl _; rfl
  | succ k ih =>
    intro lvl hlk
    have hsib := sibRead_eq (hN lvl (by omega)) (levels_length h z0 L hn lvl)
      (hzs lvl (by omega)) (Nat.div_le_div_right (c := 2 ^ lvl) (by omega : i ≤ L.length - 1))
    have hrest := ih (lvl + 1) (by omega)
    rw [← div_two_pow_succ, ← div_two_pow_succ] at hrest
    simp only [pathLoop, hsib, hrest, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
      List.range'_succ, List.map_cons]
    rfl

theorem merklePath_is_honest (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree)
    (i : ℕ) (hR : Represents h z0 leaves S) (hi : i < leaves.length) :
    merklePath S i = some ((List.range S.height).map (honestSibs h z0 leaves i)) := by
  have hne : leaves ≠ [] := by rintro rfl; simp at hi
  have hloop := pathLoop_spec h z0 leaves S.height i S.zeros S.nodes hne hi
    (fun l hl => hR.zeros_getElem? (by omega))
    (fun l hl => by rw [hR.nodes_getElem? hl, cachedLevel_of_ne hne]) S.height 0 (by omega)
  simp only [pow_zero, Nat.div_one] at hloop
  unfold merklePath
  rw [ite_eq_right (by rw [hR.leafNumber_eq]; omega),
    ite_eq_right (by rw [hR.leafNumber_eq]; omega), hR.leafNumber_eq, hloop,
    List.range_eq_range']

theorem merklePath_out_of_range_reverts (S : FullTree) (i : ℕ) (hi : S.leafNumber ≤ i) :
    merklePath S i = none := by
  unfold merklePath
  by_cases h0 : S.leafNumber = 0
  · rw [ite_eq_left h0]
  · rw [ite_eq_right h0, ite_eq_left (by omega)]

/-- The verifier's stream over the returned path is the honest stream at every level the
walk reads. -/
theorem pathSibs_honest (h : Hash) (z0 : UInt256) (L : List UInt256) (H i l : ℕ)
    (hl : l < H) :
    pathSibs ((List.range H).map (honestSibs h z0 L i)) l = honestSibs h z0 L i l := by
  unfold pathSibs
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]
  rfl

theorem contract_path_verifies (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree)
    (i : ℕ) (hR : Represents h z0 leaves S) (hi : i < leaves.length) :
    ∃ (p : List UInt256) (R : UInt256), merklePath S i = some p ∧ root S = some R
      ∧ p.length = S.height ∧ i < 2 ^ p.length
      ∧ walkPure h (pathSibs p) 0 p.length i (leaves.getD i z0) = R := by
  have hlen : ((List.range S.height).map (honestSibs h z0 leaves i)).length = S.height := by
    rw [List.length_map, List.length_range]
  have hi2 : i < 2 ^ S.height := lt_of_lt_of_le hi hR.capacity
  refine ⟨_, _, merklePath_is_honest h z0 leaves S i hR hi, root_is_fold h z0 leaves S hR,
    hlen, by rw [hlen]; exact hi2, ?_⟩
  rw [hlen, walkPure_congr_sibs h _ (honestSibs h z0 leaves i) S.height 0 i _
    (fun l _ hl => pathSibs_honest h z0 leaves S.height i l (by omega))]
  exact honest_walk_root h z0 leaves S.height i hi2

/-! ## The storage determines the leaves -/

theorem represents_leaves (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree)
    (hR : Represents h z0 leaves S) : leavesOf S = leaves := by
  unfold leavesOf
  rw [List.headD_eq_getD, List.getD_eq_getElem?_getD, hR.nodes_getElem? (Nat.zero_le _),
    Option.getD_some, hR.leafNumber_eq]
  by_cases he : leaves = []
  · subst he; simp
  · rw [cachedLevel_of_ne he, levels_zero, List.take_length]

theorem cache_entries (h : Hash) (z0 : UInt256) (leaves : List UInt256) (S : FullTree)
    (hR : Represents h z0 leaves S) (hne : leaves ≠ []) :
    (∀ i, i ≤ S.height → S.zeros[i]? = some (zeros h z0 i))
      ∧ (∀ i j, i ≤ S.height → nodeAt S.nodes i j = (levels h z0 leaves i)[j]?) :=
  ⟨fun _ hi => hR.zeros_getElem? hi, fun i j hi => by
    rw [nodeAt_of_row (hR.nodes_getElem? hi), cachedLevel_of_ne hne]⟩

/-! ## Along runs -/

/-- After `n` pushes from `⟨0, 0⟩` the count is `n`. -/
private lemma iterate_push_eq (n H : ℕ) (hH : H = (push^[n] (⟨0, 0⟩ : TreeDims)).height) :
    push^[n] (⟨0, 0⟩ : TreeDims) = ⟨n, H⟩ := by
  have hc : (push^[n] (⟨0, 0⟩ : TreeDims)).count = n := count_after n
  rw [hH]
  generalize push^[n] (⟨0, 0⟩ : TreeDims) = d at hc ⊢
  cases d
  simp only at hc
  subst hc
  rfl

theorem reachable_represents (h : Hash) (z0 : UInt256) (S : FullTree)
    (hS : Reachable h z0 S) :
    Represents h z0 (leavesOf S) S ∧ S.height = (push^[S.leafNumber] ⟨0, 0⟩).height := by
  induction hS with
  | init =>
    have hR := (setup_represents_empty h z0).1
    rw [represents_leaves h z0 [] _ hR]
    exact ⟨hR, rfl⟩
  | @step S S' _ hstep ih =>
    obtain ⟨hR, hH⟩ := ih
    cases hstep with
    | @push x r hpush =>
      obtain ⟨S'', hpush', hR'', hdims⟩ := pushNewLeaf_computes_root h z0 _ S x hR
      rw [hpush] at hpush'
      have hS' : S' = S'' := (Prod.mk.inj (Option.some.inj hpush')).1
      subst hS'
      rw [represents_leaves h z0 _ _ hR'']
      refine ⟨hR'', ?_⟩
      have hnum : S'.leafNumber = S.leafNumber + 1 :=
        (congrArg TreeDims.count hdims).trans (count_succ _)
      rw [hnum, Function.iterate_succ_apply', iterate_push_eq S.leafNumber S.height hH, ← hdims]
    | @update i x r hupd =>
      by_cases hi : i < (leavesOf S).length
      · obtain ⟨S'', hupd', hR'', hH'', hnum''⟩ := updateLeaf_computes_root h z0 _ S i x hR hi
        rw [hupd] at hupd'
        have hS' : S' = S'' := (Prod.mk.inj (Option.some.inj hupd')).1
        subst hS'
        rw [represents_leaves h z0 _ _ hR'']
        exact ⟨hR'', by rw [hH'', hnum'']; exact hH⟩
      · rw [updateLeaf_out_of_range_reverts h S i x (by rw [hR.leafNumber_eq]; omega)] at hupd
        cases hupd

theorem reachable_root_is_fold (h : Hash) (z0 : UInt256) (S : FullTree)
    (hS : Reachable h z0 S) : root S = some (rootOf h z0 (leavesOf S) S.height) :=
  root_is_fold h z0 _ S (reachable_represents h z0 S hS).1

theorem calls_return_the_stored_root (h : Hash) (z0 : UInt256) (S S' : FullTree) (r : UInt256)
    (hS : Reachable h z0 S)
    (hcall : (∃ x, pushNewLeaf h S x = some (S', r)) ∨ (∃ i x, updateLeaf h S i x = some (S', r))) :
    root S' = some r := by
  have hR := (reachable_represents h z0 S hS).1
  rcases hcall with ⟨x, hpush⟩ | ⟨i, x, hupd⟩
  · obtain ⟨S'', hpush', hR'', _⟩ := pushNewLeaf_computes_root h z0 _ S x hR
    rw [hpush] at hpush'
    obtain ⟨hS', hr⟩ := Prod.mk.inj (Option.some.inj hpush')
    rw [hS', hr]
    exact root_is_fold h z0 _ _ hR''
  · by_cases hi : i < (leavesOf S).length
    · obtain ⟨S'', hupd', hR'', hH'', _⟩ := updateLeaf_computes_root h z0 _ S i x hR hi
      rw [hupd] at hupd'
      obtain ⟨hS', hr⟩ := Prod.mk.inj (Option.some.inj hupd')
      rw [hS', hr, root_is_fold h z0 _ _ hR'', hH'']
    · rw [updateLeaf_out_of_range_reverts h S i x (by rw [hR.leafNumber_eq]; omega)] at hupd
      cases hupd

/-! ## Anti-vacuity -/

theorem three_pushes_witness (h : Hash) (z0 a b c : UInt256) : ∃ S : FullTree,
    threePushes h z0 a b c = some S ∧ Reachable h z0 S ∧ Represents h z0 [a, b, c] S
      ∧ S.height = 2 ∧ S.leafNumber = 3
      ∧ ∃ (S' : FullTree) (r : UInt256), updateLeaf h S 0 c = some (S', r) := by
  have hR₀ := (setup_represents_empty h z0).1
  obtain ⟨S₁, hp₁, hR₁, hd₁⟩ := pushNewLeaf_computes_root h z0 [] _ a hR₀
  obtain ⟨S₂, hp₂, hR₂, hd₂⟩ := pushNewLeaf_computes_root h z0 _ S₁ b hR₁
  obtain ⟨S₃, hp₃, hR₃, hd₃⟩ := pushNewLeaf_computes_root h z0 _ S₂ c hR₂
  simp only [List.nil_append, List.cons_append] at hR₁ hR₂ hR₃
  have hd₁' : (⟨S₁.leafNumber, S₁.height⟩ : TreeDims) = ⟨1, 0⟩ := by
    rw [hd₁]; rfl
  have hd₂' : (⟨S₂.leafNumber, S₂.height⟩ : TreeDims) = ⟨2, 1⟩ := by
    rw [hd₂, show (⟨S₁.leafNumber, S₁.height⟩ : TreeDims) = ⟨1, 0⟩ from hd₁']; rfl
  have hd₃' : (⟨S₃.leafNumber, S₃.height⟩ : TreeDims) = ⟨3, 2⟩ := by
    rw [hd₃, show (⟨S₂.leafNumber, S₂.height⟩ : TreeDims) = ⟨2, 1⟩ from hd₂']; rfl
  obtain ⟨S', hu, _⟩ := updateLeaf_computes_root h z0 [a, b, c] S₃ 0 c hR₃ (by simp)
  refine ⟨S₃, ?_, ?_, hR₃, congrArg TreeDims.height hd₃', congrArg TreeDims.count hd₃',
    S', _, hu⟩
  · simp only [threePushes, hp₁, hp₂, hp₃, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def]
  · exact Reachable.step (Reachable.step (Reachable.step Reachable.init (Step.push hp₁))
      (Step.push hp₂)) (Step.push hp₃)

end Contracts.FullMerkle

/-! ## Certificates -/

namespace Contracts.FullMerkle

theorem SetupRepresentsEmpty : Properties.SetupRepresentsEmpty := setup_represents_empty
theorem PushNewLeafComputesRoot : Properties.PushNewLeafComputesRoot := pushNewLeaf_computes_root
theorem UpdateLeafComputesRoot : Properties.UpdateLeafComputesRoot := updateLeaf_computes_root
theorem UpdateLeafOutOfRangeReverts : Properties.UpdateLeafOutOfRangeReverts :=
  updateLeaf_out_of_range_reverts
theorem RootIsFold : Properties.RootIsFold := root_is_fold
theorem MerklePathIsHonest : Properties.MerklePathIsHonest := merklePath_is_honest
theorem MerklePathOutOfRangeReverts : Properties.MerklePathOutOfRangeReverts :=
  merklePath_out_of_range_reverts
theorem ContractPathVerifies : Properties.ContractPathVerifies := contract_path_verifies
theorem RepresentsLeaves : Properties.RepresentsLeaves := represents_leaves
theorem CacheEntries : Properties.CacheEntries := cache_entries
theorem ReachableRepresents : Properties.ReachableRepresents := reachable_represents
theorem ReachableRootIsFold : Properties.ReachableRootIsFold := reachable_root_is_fold
theorem CallsReturnTheStoredRoot : Properties.CallsReturnTheStoredRoot :=
  calls_return_the_stored_root
theorem ThreePushesWitness : Properties.ThreePushesWitness := three_pushes_witness

end Contracts.FullMerkle
