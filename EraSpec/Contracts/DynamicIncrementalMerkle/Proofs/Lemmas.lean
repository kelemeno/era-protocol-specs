import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.Model
import EraSpec.Contracts.FullMerkle.Proofs.Model

/-!
# Lemmas shared by the storage and memory push trees

Pure list and arithmetic facts about `lowZero`, `frontierNode`, the append path of
`MerkleSpec` and the branch-rebuild loop `pushLoop`. No property statements here; the named
results are in `Model.lean` (storage tree) and in `../../DynamicIncrementalMerkleMemory/`.
-/

namespace Contracts.DynamicIncrementalMerkle

open Clear MerkleSpec

/-! ## `getD` on lists -/

theorem getD_default : ∀ (L : List UInt256) (n : ℕ) (d : UInt256),
    L.length ≤ n → L.getD n d = d
  | [], _, _, _ => rfl
  | _ :: _, 0, _, hn => absurd hn (by simp)
  | _ :: t, n + 1, d, hn =>
    getD_default t n d (by simp only [List.length_cons] at hn; omega)

theorem getD_set_ne (x : UInt256) : ∀ (L : List UInt256) (i j : ℕ) (d : UInt256),
    i ≠ j → (L.set i x).getD j d = L.getD j d
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, hij => absurd rfl hij
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: t, i + 1, j + 1, d, hij =>
    getD_set_ne x t i j d (fun hcon => hij (by rw [hcon]))

theorem getD_set_self (x : UInt256) : ∀ (L : List UInt256) (i : ℕ) (d : UInt256),
    i < L.length → (L.set i x).getD i d = x
  | [], _, _, hi => absurd hi (by simp)
  | _ :: _, 0, _, _ => rfl
  | _ :: t, i + 1, d, hi =>
    getD_set_self x t i d (by simp only [List.length_cons] at hi; omega)

theorem getD_zero_headD : ∀ (L : List UInt256) (d : UInt256), L.getD 0 d = L.headD d
  | [], _ => rfl
  | _ :: _, _ => rfl

theorem getD_append_left : ∀ (A B : List UInt256) (i : ℕ) (d : UInt256),
    i < A.length → (A ++ B).getD i d = A.getD i d
  | [], _, _, _, hi => absurd hi (by simp)
  | _ :: _, _, 0, _, _ => rfl
  | _ :: t, B, i + 1, d, hi =>
    getD_append_left t B i d (by simp only [List.length_cons] at hi; omega)

theorem getD_append_length : ∀ (A : List UInt256) (b d : UInt256),
    (A ++ [b]).getD A.length d = b
  | [], _, _ => rfl
  | _ :: t, b, d => getD_append_length t b d

theorem getD_take : ∀ (L : List UInt256) (k i : ℕ) (d : UInt256),
    i < k → (L.take k).getD i d = L.getD i d
  | [], _, _, _, _ => by simp
  | _ :: _, 0, _, _, hi => absurd hi (by omega)
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: t, k + 1, i + 1, d, hi => getD_take t k i d (by omega)

/-! ## `lowZero`: the trailing ones of the leaf index -/

theorem lowZero_even {n : ℕ} (hn : n % 2 = 0) : lowZero n = 0 := by
  rw [lowZero]; simp [hn]

theorem lowZero_odd {n : ℕ} (hn : n % 2 = 1) : lowZero n = lowZero (n / 2) + 1 := by
  rw [lowZero]; simp [hn]

theorem div_pow_succ (n i : ℕ) : n / 2 ^ (i + 1) = n / 2 / 2 ^ i := by
  rw [pow_succ', Nat.div_div_eq_div_mul]

theorem div_pow_div_two (n i : ℕ) : n / 2 ^ i / 2 = n / 2 ^ (i + 1) := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

/-- Every bit below `lowZero n` is one. -/
theorem lowZero_lt_bit : ∀ (i n : ℕ), i < lowZero n → n / 2 ^ i % 2 = 1
  | 0, n, hi => by
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · rw [lowZero_even h0] at hi; omega
      · simpa using h1
  | i + 1, n, hi => by
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · rw [lowZero_even h0] at hi; omega
      · rw [lowZero_odd h1] at hi
        rw [div_pow_succ]
        exact lowZero_lt_bit i (n / 2) (by omega)

/-- Bit `lowZero n` is zero. -/
theorem lowZero_bit (n : ℕ) : n / 2 ^ lowZero n % 2 = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
    · rw [lowZero_even h0]; simpa using h0
    · rw [lowZero_odd h1, div_pow_succ]
      exact ih (n / 2) (by omega)

/-- Incrementing carries exactly through the levels up to `lowZero n`. -/
theorem succ_div_pow : ∀ (i n : ℕ),
    (n + 1) / 2 ^ i = n / 2 ^ i + (if i ≤ lowZero n then 1 else 0)
  | 0, n => by simp
  | i + 1, n => by
      rw [div_pow_succ, div_pow_succ n]
      rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
      · rw [lowZero_even h0]
        have e : (n + 1) / 2 = n / 2 := by omega
        simp [e]
      · rw [lowZero_odd h1]
        have e : (n + 1) / 2 = n / 2 + 1 := by omega
        rw [e, succ_div_pow i (n / 2)]
        simp

/-! ## The fold: roots, appended levels, the frontier node -/

theorem rootOf_nil (h : Hash) (z0 : UInt256) (H : ℕ) : rootOf h z0 [] H = zeros h z0 H := by
  unfold rootOf
  rw [MerkleSpec.levels_nil h z0 H]
  rfl

theorem rootOf_eq_getD (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ) :
    rootOf h z0 L H = (levels h z0 L H).getD 0 (zeros h z0 H) := by
  unfold rootOf
  exact (getD_zero_headD _ _).symm

/-- One more level over a tree that fits: hash the root with that level's zero. -/
theorem rootOf_succ (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ)
    (hcap : L.length ≤ 2 ^ H) :
    rootOf h z0 L (H + 1) = h (rootOf h z0 L H) (zeros h z0 H) := by
  by_cases hne : L.length = 0
  · have hnil : L = [] := List.eq_nil_of_length_eq_zero hne
    subst hnil
    rw [rootOf_nil, rootOf_nil]
    rfl
  · have hs : levels h z0 L H = [rootOf h z0 L H] :=
      MerkleSpec.levels_height_singleton h z0 L H hne hcap
    show (levelUp h (zeros h z0 H) (levels h z0 L H)).headD (zeros h z0 (H + 1)) = _
    rw [hs]
    rfl

theorem levels_append_getD_lt (h : Hash) (z0 : UInt256) (L : List UInt256) (x : UInt256)
    (i k : ℕ) (d : UInt256) (hk : k < L.length / 2 ^ i) :
    (levels h z0 (L ++ [x]) i).getD k d = (levels h z0 L i).getD k d := by
  have e : levels h z0 (L ++ [x]) i
      = (levels h z0 L i).take (L.length / 2 ^ i) ++ [appendPath h z0 L x i] :=
    MerkleSpec.levels_append h z0 L x i
  have hlen : L.length / 2 ^ i ≤ (levels h z0 L i).length :=
    MerkleSpec.div_le_levels_length h z0 L i
  rw [e, getD_append_left _ _ _ _ (by rw [List.length_take]; omega), getD_take _ _ _ _ hk]

theorem levels_append_getD_eq (h : Hash) (z0 : UInt256) (L : List UInt256) (x : UInt256)
    (i : ℕ) (d : UInt256) :
    (levels h z0 (L ++ [x]) i).getD (L.length / 2 ^ i) d = appendPath h z0 L x i := by
  have e : levels h z0 (L ++ [x]) i
      = (levels h z0 L i).take (L.length / 2 ^ i) ++ [appendPath h z0 L x i] :=
    MerkleSpec.levels_append h z0 L x i
  have hlen : L.length / 2 ^ i ≤ (levels h z0 L i).length :=
    MerkleSpec.div_le_levels_length h z0 L i
  have hl : ((levels h z0 L i).take (L.length / 2 ^ i)).length = L.length / 2 ^ i := by
    rw [List.length_take]; omega
  rw [e]
  have := getD_append_length ((levels h z0 L i).take (L.length / 2 ^ i))
    (appendPath h z0 L x i) d
  rwa [hl] at this

/-- The root after an append into a tree with room is the top of the append path. -/
theorem rootOf_append_eq (h : Hash) (z0 : UInt256) (L : List UInt256) (x : UInt256) (H : ℕ)
    (hcap : L.length < 2 ^ H) : rootOf h z0 (L ++ [x]) H = appendPath h z0 L x H := by
  rw [rootOf_eq_getD]
  have := levels_append_getD_eq h z0 L x H (zeros h z0 H)
  rwa [Nat.div_eq_of_lt hcap] at this

/-- At a full tree the frontier node of the top level is the root. -/
theorem frontierNode_top (h : Hash) (z0 : UInt256) (L : List UInt256) (H : ℕ)
    (hn : L.length = 2 ^ H) : frontierNode h z0 L H = rootOf h z0 L H := by
  have e : 2 * ((L.length / 2 ^ H - 1) / 2) = 0 := by
    rw [hn, Nat.div_self (Nat.two_pow_pos H)]
  unfold frontierNode
  rw [e, rootOf_eq_getD]

/-- With an odd number of complete nodes, the frontier node is the left neighbour of the
next leaf's path. -/
theorem frontierNode_odd (h : Hash) (z0 : UInt256) (L : List UInt256) (i : ℕ)
    (hodd : L.length / 2 ^ i % 2 = 1) :
    frontierNode h z0 L i
      = (levels h z0 L i).getD (L.length / 2 ^ i - 1) (zeros h z0 i) := by
  have e : 2 * ((L.length / 2 ^ i - 1) / 2) = L.length / 2 ^ i - 1 := by omega
  unfold frontierNode
  rw [e]

/-- `2^i ≤ n` as soon as bit `i` of `n` is set. -/
theorem pow_le_of_bit {n i : ℕ} (hodd : n / 2 ^ i % 2 = 1) : 2 ^ i ≤ n := by
  by_contra hlt
  rw [Nat.div_eq_of_lt (by omega)] at hodd
  omega

/-- **The frontier after a push.** If `sd` holds the frontier nodes of `L` below level `H`,
then writing the append-path node at level `lowZero L.length` (when that level is below `H`)
gives the frontier nodes of `L ++ [x]` below level `H`. -/
theorem frontier_push (h : Hash) (z0 : UInt256) (L : List UInt256) (x : UInt256)
    (sd : List UInt256) (H : ℕ) (hlen : H ≤ sd.length)
    (hf : ∀ i, i < H → 2 ^ i ≤ L.length → sd.getD i 0 = frontierNode h z0 L i) :
    ∀ i, i < H → 2 ^ i ≤ L.length + 1 →
      (if lowZero L.length < H then
          sd.set (lowZero L.length) (appendPath h z0 L x (lowZero L.length)) else sd).getD i 0
        = frontierNode h z0 (L ++ [x]) i := by
  intro i hi hpow
  have hsucc := succ_div_pow i L.length
  have hlenA : (L ++ [x]).length = L.length + 1 := by simp
  by_cases hij : i = lowZero L.length
  · -- the written level
    rw [if_pos (by omega), ← hij, getD_set_self _ _ _ _ (by omega)]
    have hbit : L.length / 2 ^ i % 2 = 0 := by rw [hij]; exact lowZero_bit L.length
    rw [if_pos (by omega)] at hsucc
    have e : 2 * (((L ++ [x]).length / 2 ^ i - 1) / 2) = L.length / 2 ^ i := by
      rw [hlenA, hsucc]; omega
    unfold frontierNode
    rw [e]
    exact (levels_append_getD_eq h z0 L x i _).symm
  · -- every other level keeps its entry
    have hkeep : (if lowZero L.length < H then
          sd.set (lowZero L.length) (appendPath h z0 L x (lowZero L.length)) else sd).getD i 0
        = sd.getD i 0 := by
      split
      · exact getD_set_ne _ _ _ _ _ (fun hcon => hij hcon.symm)
      · rfl
    rw [hkeep]
    have hpos : 0 < 2 ^ i := Nat.two_pow_pos i
    -- the level already held a complete node before the push
    have hold : 2 ^ i ≤ L.length := by
      by_contra hlt
      have h0 : L.length / 2 ^ i = 0 := Nat.div_eq_of_lt (by omega)
      have h1 : (L.length + 1) / 2 ^ i = 1 := by
        have : L.length + 1 = 2 ^ i := by omega
        rw [this, Nat.div_self hpos]
      rw [h0, h1] at hsucc
      have hle : i ≤ lowZero L.length := by
        by_contra hnle
        rw [if_neg hnle] at hsucc
        omega
      have hbit := lowZero_lt_bit i L.length (by omega)
      rw [h0] at hbit
      omega
    rw [hf i hi hold]
    have hq : 1 ≤ L.length / 2 ^ i := (Nat.le_div_iff_mul_le hpos).mpr (by omega)
    have e : 2 * (((L ++ [x]).length / 2 ^ i - 1) / 2) = 2 * ((L.length / 2 ^ i - 1) / 2) := by
      rw [hlenA, hsucc]
      by_cases hle : i ≤ lowZero L.length
      · have hbit := lowZero_lt_bit i L.length (by omega)
        rw [if_pos hle]
        omega
      · rw [if_neg hle]
        rfl
    unfold frontierNode
    rw [e]
    exact levels_append_getD_lt h z0 L x i _ _ (by omega)

/-! ## The branch-rebuild loop -/

theorem pushLoop_left_first (h : Hash) (zs : List UInt256) (i k idx : ℕ) (acc : UInt256)
    (sd : List UInt256) (hb : idx % 2 = 0) :
    pushLoop h zs i (k + 1) idx acc false sd
      = pushLoop h zs (i + 1) k (idx / 2) (h acc (zs.getD i 0)) true (sd.set i acc) := by
  simp [pushLoop, hb]

theorem pushLoop_left_done (h : Hash) (zs : List UInt256) (i k idx : ℕ) (acc : UInt256)
    (sd : List UInt256) (hb : idx % 2 = 0) :
    pushLoop h zs i (k + 1) idx acc true sd
      = pushLoop h zs (i + 1) k (idx / 2) (h acc (zs.getD i 0)) true sd := by
  simp [pushLoop, hb]

theorem pushLoop_right (h : Hash) (zs : List UInt256) (i k idx : ℕ) (acc : UInt256)
    (upd : Bool) (sd : List UInt256) (hb : idx % 2 = 1) :
    pushLoop h zs i (k + 1) idx acc upd sd
      = pushLoop h zs (i + 1) k (idx / 2) (h (sd.getD i 0) acc) upd sd := by
  simp [pushLoop, hb]

/-- **The loop computes the append path and writes one side.** With `zs` the zero cascade
and `sd` holding, at every level whose path index is odd, the left neighbour of the new
leaf's path: from level `i` the loop ends with the level-`H` append-path node, having
written the append-path node at level `lowZero L.length` (if below `H`) and nothing else. -/
theorem pushLoop_spec (h : Hash) (z0 : UInt256) (L : List UInt256) (x : UInt256)
    (zs sd : List UInt256) (H : ℕ)
    (hz : ∀ l, l < H → zs.getD l 0 = zeros h z0 l)
    (hf : ∀ l, l < H → L.length / 2 ^ l % 2 = 1 →
        sd.getD l 0 = (levels h z0 L l).getD (L.length / 2 ^ l - 1) (zeros h z0 l)) :
    ∀ (k i : ℕ), i + k = H →
      pushLoop h zs i k (L.length / 2 ^ i) (appendPath h z0 L x i)
          (decide (lowZero L.length < i))
          (if lowZero L.length < i then
            sd.set (lowZero L.length) (appendPath h z0 L x (lowZero L.length)) else sd)
        = (if lowZero L.length < H then
            sd.set (lowZero L.length) (appendPath h z0 L x (lowZero L.length)) else sd,
           appendPath h z0 L x H) := by
  intro k
  induction k with
  | zero =>
    intro i hi
    have : i = H := by omega
    subst this
    simp [pushLoop]
  | succ k ih =>
    intro i hi
    have hiH : i < H := by omega
    refine Eq.trans ?_ (ih (i + 1) (by omega))
    have hdiv := div_pow_div_two L.length i
    have hap : appendPath h z0 L x (i + 1)
        = if L.length / 2 ^ i % 2 = 1 then
            h ((levels h z0 L i).getD (L.length / 2 ^ i - 1) (zeros h z0 i))
              (appendPath h z0 L x i)
          else h (appendPath h z0 L x i) (zeros h z0 i) := rfl
    rcases Nat.lt_trichotomy (lowZero L.length) i with hlt | heq | hgt
    · -- the side was written at an earlier level
      have hlt' : lowZero L.length < i + 1 := by omega
      rw [if_pos hlt, if_pos hlt', decide_eq_true hlt, decide_eq_true hlt']
      rcases Nat.mod_two_eq_zero_or_one (L.length / 2 ^ i) with hb | hb
      · rw [pushLoop_left_done h zs i k _ _ _ hb, hdiv, hap, if_neg (by omega), hz i hiH]
      · rw [pushLoop_right h zs i k _ _ _ _ hb, hdiv, hap, if_pos hb,
          getD_set_ne _ _ _ _ _ (by omega), hf i hiH hb]
    · -- this is the level that writes
      subst heq
      have hb : L.length / 2 ^ lowZero L.length % 2 = 0 := lowZero_bit L.length
      rw [if_neg (lt_irrefl _), if_pos (Nat.lt_succ_self _), decide_eq_false (lt_irrefl _),
        decide_eq_true (Nat.lt_succ_self _), pushLoop_left_first h zs _ k _ _ _ hb, hdiv, hap,
        if_neg (by omega), hz _ hiH]
    · -- still climbing through right children
      have hb : L.length / 2 ^ i % 2 = 1 := lowZero_lt_bit i L.length hgt
      have hnlt : ¬ lowZero L.length < i := by omega
      have hnlt' : ¬ lowZero L.length < i + 1 := by omega
      rw [if_neg hnlt, if_neg hnlt', decide_eq_false hnlt, decide_eq_false hnlt',
        pushLoop_right h zs i k _ _ _ _ hb, hdiv, hap, if_pos hb, hf i hiH hb]

/-- `pushLoop_spec` from level 0, as `push` calls it. -/
theorem pushLoop_spec0 (h : Hash) (z0 : UInt256) (L : List UInt256) (x : UInt256)
    (zs sd : List UInt256) (H : ℕ)
    (hz : ∀ l, l < H → zs.getD l 0 = zeros h z0 l)
    (hf : ∀ l, l < H → L.length / 2 ^ l % 2 = 1 →
        sd.getD l 0 = (levels h z0 L l).getD (L.length / 2 ^ l - 1) (zeros h z0 l)) :
    pushLoop h zs 0 H L.length x false sd
      = (if lowZero L.length < H then
            sd.set (lowZero L.length) (appendPath h z0 L x (lowZero L.length)) else sd,
         appendPath h z0 L x H) := by
  have hs := pushLoop_spec h z0 L x zs sd H hz hf H 0 (by omega)
  have e0 : L.length / 2 ^ 0 = L.length := by simp
  have e1 : appendPath h z0 L x 0 = x := rfl
  rw [e0, e1, decide_eq_false (Nat.not_lt_zero _), if_neg (Nat.not_lt_zero _)] at hs
  exact hs

end Contracts.DynamicIncrementalMerkle
