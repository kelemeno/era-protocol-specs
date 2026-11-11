import EraSpec.Contracts.Merkle.Properties.RootForgeryPinned
import EraSpec.Contracts.Merkle.Proofs.PathCollision

/-!
# Proofs: located collisions between two trees, two walks, or two levels

Proofs of `EraSpec.Contracts.Merkle.Properties.RootForgeryPinned`.  Three engines do all the
work, each the hash-premise-free form of an induction that used `hinj` once per level:

* `path_nodes_or_collision` — walk two trees' nodes on index `i`'s path from level `k` down
  to level 0: where the level-`l+1` nodes agree and the level-`l` nodes differ, the pairs
  under the level-`l+1` node differ (one component IS the level-`l` node) and hash equal.
* `walk_vs_walk_or_collision` — peel one step off two walks: equal accumulators above and
  different pairs at this step is a collision at this step; equal pairs give equal leaves and
  siblings here.
* `levelUp_inj_or_collision` — two equal-width levels with the same parent level: a parent
  whose child pairs differ is a collision under that parent.

For the padding-hit witnesses, `same_tree_of_getD_eq`: two lists that agree at every entry
read with the padding default (a list and the same list with `z0` appended) have the same
root at every height and no collision on any path, for every hash.
-/

namespace MerkleSpec.Pinned

open Clear MerkleSpec MerkleSpec.Verifier

/-! ## `getD` toolkit (the `MerkleSpec` and `TreeRoot` copies are private) -/

/-- In-range `getD` does not depend on the default. -/
theorem getD_congr_lt : ∀ (L : List UInt256) (n : ℕ) (d₁ d₂ : UInt256),
    n < L.length → L.getD n d₁ = L.getD n d₂
  | [], _, _, _, hn => absurd hn (by simp)
  | _ :: _, 0, _, _, _ => rfl
  | _ :: t, n + 1, d₁, d₂, hn =>
    getD_congr_lt t n d₁ d₂ (by simp only [List.length_cons] at hn; omega)

/-- `getD` at the written index reads the written value. -/
theorem getD_set_eq (x : UInt256) : ∀ (L : List UInt256) (i : ℕ) (d : UInt256),
    i < L.length → (L.set i x).getD i d = x
  | [], _, _, hi => absurd hi (by simp)
  | _ :: _, 0, _, _ => rfl
  | _ :: t, i + 1, d, hi =>
    getD_set_eq x t i d (by simp only [List.length_cons] at hi; omega)

/-- `getD` at the old length reads the appended leaf. -/
theorem getD_append_singleton : ∀ (A : List UInt256) (y d : UInt256),
    (A ++ [y]).getD A.length d = y
  | [], _, _ => rfl
  | _ :: t, y, d => getD_append_singleton t y d

/-- Two lists agreeing in length and at every in-range `getD` are equal. -/
theorem ext_getD' (d : UInt256) : ∀ (L₁ L₂ : List UInt256),
    L₁.length = L₂.length → (∀ n, n < L₁.length → L₁.getD n d = L₂.getD n d) → L₁ = L₂
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => absurd hlen (by simp)
  | _ :: _, [], hlen, _ => absurd hlen (by simp)
  | a :: t, b :: u, hlen, hget => by
    have hab : a = b := hget 0 (by simp)
    have htu : t = u := ext_getD' d t u (by simpa using hlen)
      (fun n hn => hget (n + 1) (by simp only [List.length_cons]; omega))
    rw [hab, htu]

/-- The first position of a member reads that member. -/
theorem getD_idxOf {L : List UInt256} {x : UInt256} (hx : x ∈ L) (d : UInt256) :
    L.getD (L.idxOf x) d = x := by
  have hlt := List.idxOf_lt_length_of_mem hx
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some,
    List.getElem_idxOf]

/-! ## Engine 1: tree versus tree -/

/-- The entry under `treePair`'s parent that sits at `j` is a component of the pair, so equal
pairs mean equal entries at `j`. -/
theorem getD_eq_of_treePair_eq (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (l j : ℕ)
    (he : treePair h z0 L₁ l j = treePair h z0 L₂ l j) :
    (levels h z0 L₁ l).getD j (zeros h z0 l) = (levels h z0 L₂ l).getD j (zeros h z0 l) := by
  unfold treePair at he
  simp only [Prod.mk.injEq] at he
  by_cases hpar : j % 2 = 0
  · rw [show 2 * (j / 2) = j by omega] at he; exact he.1
  · rw [show 2 * (j / 2) + 1 = j by omega] at he; exact he.2

/-- On index `i`'s path, the pair under the level-`l+1` node hashes to that node. -/
theorem hash_treePair_path (h : Hash) (z0 : UInt256) (L : List UInt256) (i l : ℕ) :
    h (treePair h z0 L l (i / 2 ^ l)).1 (treePair h z0 L l (i / 2 ^ l)).2
      = (levels h z0 L (l + 1)).getD (i / 2 ^ (l + 1)) (zeros h z0 (l + 1)) := by
  rw [hash_treePair h z0 L l (i / 2 ^ l), Nat.div_div_eq_div_mul, ← pow_succ]

/-- **Engine 1.**  If two trees' level-`k` nodes on index `i`'s path agree, their level-0
entries at `i` agree, or the trees collide on `i`'s path below level `k`. -/
theorem path_nodes_or_collision (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (i : ℕ) :
    ∀ k, (levels h z0 L₁ k).getD (i / 2 ^ k) (zeros h z0 k)
        = (levels h z0 L₂ k).getD (i / 2 ^ k) (zeros h z0 k) →
      L₁.getD i z0 = L₂.getD i z0 ∨ TreeCollision h z0 L₁ L₂ k i
  | 0, he => by left; simpa using he
  | k + 1, he => by
    by_cases hk : (levels h z0 L₁ k).getD (i / 2 ^ k) (zeros h z0 k)
        = (levels h z0 L₂ k).getD (i / 2 ^ k) (zeros h z0 k)
    · rcases path_nodes_or_collision h z0 L₁ L₂ i k hk with h0 | ⟨l, hl, hne, heq⟩
      · exact Or.inl h0
      · exact Or.inr ⟨l, by omega, hne, heq⟩
    · right
      refine ⟨k, by omega, fun hp => hk (getD_eq_of_treePair_eq h z0 L₁ L₂ k _ hp), ?_⟩
      rw [hash_treePair_path h z0 L₁ i k, hash_treePair_path h z0 L₂ i k]
      exact he

/-- The root form of engine 1: at `height`, index `i < 2^height` sits under the root. -/
theorem root_pins_entry_or_collision (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (height i : ℕ) (hi : i < 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    L₁.getD i z0 = L₂.getD i z0 ∨ TreeCollision h z0 L₁ L₂ height i := by
  apply path_nodes_or_collision
  rw [Nat.div_eq_of_lt hi, getD_zero_headD, getD_zero_headD, ← rootOf_def, ← rootOf_def]
  exact hroot

/-! ## Engine 2: walk versus walk -/

/-- **Engine 2.**  Two walks from the same level and index with equal results used the same
leaf and the same climbed siblings, or they collide at a named step. -/
theorem walk_vs_walk_or_collision (h : Hash) (s₁ s₂ : ℕ → UInt256) :
    ∀ (k lvl j : ℕ) (x y : UInt256),
      walkPure h s₁ lvl k j x = walkPure h s₂ lvl k j y →
      (x = y ∧ ∀ l, lvl ≤ l → l < lvl + k → s₁ l = s₂ l) ∨ WalkCollision h s₁ s₂ lvl k j x y := by
  intro k
  induction k with
  | zero =>
    intro lvl j x y hw
    exact Or.inl ⟨hw, fun l _ h2 => absurd h2 (by omega)⟩
  | succ k ih =>
    intro lvl j x y hw
    have hw' : walkPure h s₁ (lvl + 1) k (j / 2) (h (walkStep s₁ lvl j x).1 (walkStep s₁ lvl j x).2)
        = walkPure h s₂ (lvl + 1) k (j / 2) (h (walkStep s₂ lvl j y).1 (walkStep s₂ lvl j y).2) := by
      rw [walkStep_hash h s₁ lvl j x, walkStep_hash h s₂ lvl j y]
      exact hw
    rcases ih (lvl + 1) (j / 2) _ _ hw' with ⟨hacc, hsib⟩ | ⟨i, hi, hne, heq⟩
    · by_cases hpe : walkStep s₁ lvl j x = walkStep s₂ lvl j y
      · left
        have hboth : x = y ∧ s₁ lvl = s₂ lvl := by
          unfold walkStep at hpe
          by_cases hpar : j % 2 = 1
          · rw [ite_eq_left hpar, ite_eq_left hpar, Prod.mk.injEq] at hpe
            exact ⟨hpe.2, hpe.1⟩
          · rw [ite_eq_right hpar, ite_eq_right hpar, Prod.mk.injEq] at hpe
            exact ⟨hpe.1, hpe.2⟩
        refine ⟨hboth.1, fun l h1 h2 => ?_⟩
        rcases Nat.eq_or_lt_of_le h1 with he | h1'
        · rw [← he]; exact hboth.2
        · exact hsib l (by omega) (by omega)
      · right
        exact ⟨0, by omega, hpe, hacc⟩
    · right
      refine ⟨i + 1, by omega, ?_, ?_⟩
      · rw [walkPair_succ, walkPair_succ]; exact hne
      · rw [walkPair_succ, walkPair_succ]; exact heq

/-! ## Engine 3: level versus level -/

/-- **Engine 3.**  Two equal-width levels with the same parent level are equal, or collide
under some parent. -/
theorem levelUp_inj_or_collision (h : Hash) (z : UInt256) (L₁ L₂ : List UInt256)
    (hlen : L₁.length = L₂.length) (he : levelUp h z L₁ = levelUp h z L₂) :
    L₁ = L₂ ∨ LevelCollision h z L₁ L₂ := by
  by_cases hall : ∀ m < (L₁.length + 1) / 2, parentPair z L₁ m = parentPair z L₂ m
  · left
    refine ext_getD' z L₁ L₂ hlen (fun j hj => ?_)
    have hp := hall (j / 2) (by omega)
    unfold parentPair at hp
    simp only [Prod.mk.injEq] at hp
    by_cases hpar : j % 2 = 0
    · rw [show 2 * (j / 2) = j by omega] at hp; exact hp.1
    · rw [show 2 * (j / 2) + 1 = j by omega] at hp; exact hp.2
  · right
    push Not at hall
    obtain ⟨m, hm, hne⟩ := hall
    refine ⟨m, hm, hne, ?_⟩
    have hg := congrArg (fun L => L.getD m (h z z)) he
    simp only [levelUp_getD_all] at hg
    exact hg

/-- Engine 3 lifted through the levels. -/
theorem levels_inj_or_collision (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (hlen : L₁.length = L₂.length) :
    ∀ l, levels h z0 L₁ l = levels h z0 L₂ l →
      L₁ = L₂ ∨ ∃ l' < l, LevelCollision h (zeros h z0 l') (levels h z0 L₁ l') (levels h z0 L₂ l')
  | 0, he => Or.inl (by simpa using he)
  | l + 1, he => by
    rw [levels_succ, levels_succ] at he
    rcases levelUp_inj_or_collision h (zeros h z0 l) _ _ (levels_length_eq h z0 L₁ L₂ hlen l) he
      with hl | hc
    · rcases levels_inj_or_collision h z0 L₁ L₂ hlen l hl with h0 | ⟨l', hl', hc'⟩
      · exact Or.inl h0
      · exact Or.inr ⟨l', by omega, hc'⟩
    · exact Or.inr ⟨l, by omega, hc⟩

/-! ## FullMerkle `Model`, `CachedHashInjectivity`, `TreeShape` -/

theorem root_of_inj_or_collision (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256) (height : ℕ)
    (hlen : L₁.length = L₂.length) (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    L₁ = L₂ ∨ ∃ i < L₁.length, L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i := by
  by_cases hall : ∀ i < L₁.length, L₁.getD i z0 = L₂.getD i z0
  · exact Or.inl (ext_getD' z0 L₁ L₂ hlen hall)
  · right
    push Not at hall
    obtain ⟨i, hi, hne⟩ := hall
    rcases root_pins_entry_or_collision h z0 L₁ L₂ height i (by omega) hroot with he | hc
    · exact absurd he hne
    · exact ⟨i, hi, hne, hc⟩

theorem root_of_append_inj_or_collision (h : Hash) (z0 : UInt256) (leaves : List UInt256)
    (x y : UInt256) (height : ℕ) (hcap : (leaves ++ [x]).length ≤ 2 ^ height)
    (hroot : rootOf h z0 (leaves ++ [x]) height = rootOf h z0 (leaves ++ [y]) height) :
    x = y ∨ TreeCollision h z0 (leaves ++ [x]) (leaves ++ [y]) height leaves.length := by
  have hi : leaves.length < 2 ^ height := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hcap; omega
  rcases root_pins_entry_or_collision h z0 _ _ height leaves.length hi hroot with he | hc
  · left; rwa [getD_append_singleton, getD_append_singleton] at he
  · exact Or.inr hc

theorem root_of_set_inj_or_collision (h : Hash) (z0 : UInt256) (leaves : List UInt256) (idx : ℕ)
    (x y : UInt256) (height : ℕ) (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hroot : rootOf h z0 (leaves.set idx x) height = rootOf h z0 (leaves.set idx y) height) :
    x = y ∨ TreeCollision h z0 (leaves.set idx x) (leaves.set idx y) height idx := by
  rcases root_pins_entry_or_collision h z0 _ _ height idx (by omega) hroot with he | hc
  · left; rwa [getD_set_eq x leaves idx z0 hidx, getD_set_eq y leaves idx z0 hidx] at he
  · exact Or.inr hc

theorem walk_pure_inj_or_collision (h : Hash) (sibs : ℕ → UInt256) (k lvl idx : ℕ)
    (x y : UInt256) (hw : walkPure h sibs lvl k idx x = walkPure h sibs lvl k idx y) :
    x = y ∨ WalkCollision h sibs sibs lvl k idx x y := by
  rcases walk_vs_walk_or_collision h sibs sibs k lvl idx x y hw with ⟨he, _⟩ | hc
  · exact Or.inl he
  · exact Or.inr hc

theorem root_commits_list_or_break (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (height : ℕ) (hcap₁ : L₁.length ≤ 2 ^ height) (hcap₂ : L₂.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    L₁ = L₂ ∨ PaddingHit z0 L₁ L₂
      ∨ ∃ i < max L₁.length L₂.length,
          L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i := by
  by_cases hall : ∀ i < max L₁.length L₂.length, L₁.getD i z0 = L₂.getD i z0
  · rcases lt_trichotomy L₁.length L₂.length with hlt | heq | hgt
    · refine Or.inr (Or.inl (Or.inl ⟨hlt, ?_⟩))
      rw [← hall L₁.length (by omega)]
      exact getD_default L₁ L₁.length z0 le_rfl
    · exact Or.inl (ext_getD' z0 L₁ L₂ heq (fun n hn => hall n (by omega)))
    · refine Or.inr (Or.inl (Or.inr ⟨hgt, ?_⟩))
      rw [hall L₂.length (by omega)]
      exact getD_default L₂ L₂.length z0 le_rfl
  · right; right
    push Not at hall
    obtain ⟨i, hi, hne⟩ := hall
    rcases root_pins_entry_or_collision h z0 L₁ L₂ height i (by omega) hroot with he | hc
    · exact absurd he hne
    · exact ⟨i, hi, hne, hc⟩

theorem padding_hit_needs_padding_leaf (z0 : UInt256) (L₁ L₂ : List UInt256)
    (hp : PaddingHit z0 L₁ L₂) : z0 ∈ L₁ ∨ z0 ∈ L₂ := by
  rcases hp with ⟨hlt, he⟩ | ⟨hlt, he⟩
  · right
    have hm := getD_mem L₂ L₁.length z0 hlt
    rwa [he] at hm
  · left
    have hm := getD_mem L₁ L₂.length z0 hlt
    rwa [he] at hm

theorem root_commits_list_under_pad_separation (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (height : ℕ) (hz₁ : z0 ∉ L₁) (hz₂ : z0 ∉ L₂) (hcap₁ : L₁.length ≤ 2 ^ height)
    (hcap₂ : L₂.length ≤ 2 ^ height) (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) :
    L₁ = L₂ ∨ ∃ i < max L₁.length L₂.length,
      L₁.getD i z0 ≠ L₂.getD i z0 ∧ TreeCollision h z0 L₁ L₂ height i := by
  rcases root_commits_list_or_break h z0 L₁ L₂ height hcap₁ hcap₂ hroot with he | hp | hc
  · exact Or.inl he
  · rcases padding_hit_needs_padding_leaf z0 L₁ L₂ hp with hm | hm
    · exact absurd hm hz₁
    · exact absurd hm hz₂
  · exact Or.inr hc

/-! ## Merkle `ProofSound` -/

theorem no_forged_walk_or_collision (h : Hash) (z0 : UInt256) (L : List UInt256) (k lvl j : ℕ)
    (x : UInt256) (hne : (levels h z0 L lvl).getD j (zeros h z0 lvl) ≠ x) (sibs : ℕ → UInt256)
    (hw : walkPure h sibs lvl k j x
      = (levels h z0 L (lvl + k)).getD (j / 2 ^ k) (zeros h z0 (lvl + k))) :
    PathCollision h z0 L sibs lvl k j x := by
  rcases walk_pins_or_collision h z0 L sibs k lvl j x hw with ⟨he, _⟩ | hc
  · exact absurd he hne
  · exact hc

theorem walk_accept_pins_leaf_free_sibs_or_collision (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (height j : ℕ) (x : UInt256) (hj : j < 2 ^ height)
    (hacc : walkPure h sibs 0 height j x = rootOf h z0 L height) :
    (L.getD j z0 = x
      ∧ ∀ l, l < height → sibs l = (levels h z0 L l).getD (sibIdx (j / 2 ^ l)) (zeros h z0 l))
    ∨ PathCollision h z0 L sibs 0 height j x := by
  have hroot : (levels h z0 L (0 + height)).getD (j / 2 ^ height) (zeros h z0 (0 + height))
      = rootOf h z0 L height := by
    rw [Nat.zero_add, Nat.div_eq_of_lt hj, rootOf_def, getD_zero_headD]
  rcases walk_pins_or_collision h z0 L sibs height 0 j x (by rw [hroot]; exact hacc)
    with ⟨he, hs⟩ | hc
  · refine Or.inl ⟨by simpa using he, fun l hl => ?_⟩
    have hsl := hs l (Nat.zero_le l) (by omega)
    simpa using hsl
  · exact Or.inr hc

/-! ## Merkle `RootBinding` -/

theorem mem_of_root_of_eq_or_collision (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (height : ℕ) (x : UInt256) (hlen : L₁.length = L₂.length) (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) (hx : x ∈ L₁) :
    x ∈ L₂ ∨ TreeCollision h z0 L₁ L₂ height (L₁.idxOf x) := by
  have hi := List.idxOf_lt_length_of_mem hx
  rcases root_pins_entry_or_collision h z0 L₁ L₂ height (L₁.idxOf x) (by omega) hroot with he | hc
  · left
    rw [getD_idxOf hx] at he
    rw [he]
    exact getD_mem L₂ _ z0 (by omega)
  · exact Or.inr hc

theorem getD_of_root_of_eq_or_collision (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (height : ℕ) (hlen : L₁.length = L₂.length) (hcap : L₁.length ≤ 2 ^ height)
    (hroot : rootOf h z0 L₁ height = rootOf h z0 L₂ height) (i : ℕ) (d : UInt256) :
    L₁.getD i d = L₂.getD i d ∨ TreeCollision h z0 L₁ L₂ height i := by
  by_cases hi : i < L₁.length
  · rcases root_pins_entry_or_collision h z0 L₁ L₂ height i (by omega) hroot with he | hc
    · left
      rw [getD_congr_lt L₁ i d z0 hi, getD_congr_lt L₂ i d z0 (by omega)]
      exact he
    · exact Or.inr hc
  · left
    rw [getD_default L₁ i d (by omega), getD_default L₂ i d (by omega)]

theorem root_of_ne_of_not_mem_or_collision (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (height : ℕ) (x : UInt256) (hlen : L₁.length = L₂.length) (hcap : L₁.length ≤ 2 ^ height)
    (hx : x ∈ L₁) (hnx : x ∉ L₂) :
    rootOf h z0 L₁ height ≠ rootOf h z0 L₂ height
      ∨ TreeCollision h z0 L₁ L₂ height (L₁.idxOf x) := by
  by_cases hr : rootOf h z0 L₁ height = rootOf h z0 L₂ height
  · rcases mem_of_root_of_eq_or_collision h z0 L₁ L₂ height x hlen hcap hr hx with hm | hc
    · exact absurd hm hnx
    · exact Or.inr hc
  · exact Or.inl hr

/-! ## Merkle `RootForgery` -/

theorem root_ne_of_leaf_ne_or_collision (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (height i : ℕ) (d : UInt256) (hlen : L₁.length = L₂.length) (hcap : L₁.length ≤ 2 ^ height)
    (hdiff : L₁.getD i d ≠ L₂.getD i d) :
    rootOf h z0 L₁ height ≠ rootOf h z0 L₂ height ∨ TreeCollision h z0 L₁ L₂ height i := by
  by_cases hr : rootOf h z0 L₁ height = rootOf h z0 L₂ height
  · rcases getD_of_root_of_eq_or_collision h z0 L₁ L₂ height hlen hcap hr i d with he | hc
    · exact absurd he hdiff
    · exact Or.inr hc
  · exact Or.inl hr

theorem path_forgery_changes_walk_or_collision (h : Hash) (sibs : ℕ → UInt256) (k lvl idx : ℕ)
    (x y : UInt256) (hxy : x ≠ y) :
    walkPure h sibs lvl k idx x ≠ walkPure h sibs lvl k idx y
      ∨ WalkCollision h sibs sibs lvl k idx x y := by
  by_cases hw : walkPure h sibs lvl k idx x = walkPure h sibs lvl k idx y
  · rcases walk_pure_inj_or_collision h sibs k lvl idx x y hw with he | hc
    · exact absurd he hxy
    · exact Or.inr hc
  · exact Or.inl hw

theorem walk_accept_pins_leaf_or_collision (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (idx : ℕ) (x : UInt256) (height : ℕ) (root : UInt256)
    (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (idx / 2 ^ l)) (zeros h z0 l))
    (haccept : walkPure h sibs 0 height idx x = root) :
    rootOf h z0 (leaves.set idx x) height = root
      ∧ ∀ y : UInt256, walkPure h sibs 0 height idx y = root →
          y = x ∨ WalkCollision h sibs sibs 0 height idx y x := by
  refine ⟨?_, fun y hy => ?_⟩
  · rw [← walkPure_update_orig h z0 sibs leaves idx x height hidx hcap hsibs]
    exact haccept
  · exact walk_pure_inj_or_collision h sibs height 0 idx y x (by rw [hy, haccept])

theorem leaf_only_substitution_changes_root_or_collision (h : Hash) (z0 : UInt256)
    (sibs : ℕ → UInt256) (leaves : List UInt256) (idx : ℕ) (x y : UInt256) (height : ℕ)
    (hidx : idx < leaves.length) (hcap : leaves.length ≤ 2 ^ height) (hxy : x ≠ y) :
    (walkPure h sibs 0 height idx x ≠ walkPure h sibs 0 height idx y
        ∨ WalkCollision h sibs sibs 0 height idx x y)
    ∧ (rootOf h z0 (leaves.set idx x) height ≠ rootOf h z0 (leaves.set idx y) height
        ∨ TreeCollision h z0 (leaves.set idx x) (leaves.set idx y) height idx) := by
  refine ⟨path_forgery_changes_walk_or_collision h sibs height 0 idx x y hxy, ?_⟩
  by_cases hr : rootOf h z0 (leaves.set idx x) height = rootOf h z0 (leaves.set idx y) height
  · rcases root_of_set_inj_or_collision h z0 leaves idx x y height hidx hcap hr with he | hc
    · exact absurd he hxy
    · exact Or.inr hc
  · exact Or.inl hr

theorem single_sibling_substitution_or_collision (h : Hash) (s₁ s₂ : ℕ → UInt256)
    (k lvl m idx : ℕ) (x : UInt256) (hm1 : lvl ≤ m) (hm2 : m < lvl + k)
    (_hagree : ∀ l, l ≠ m → s₁ l = s₂ l)
    (heq : walkPure h s₁ lvl k idx x = walkPure h s₂ lvl k idx x) :
    s₁ m = s₂ m ∨ WalkCollision h s₁ s₂ lvl k idx x x := by
  rcases walk_vs_walk_or_collision h s₁ s₂ k lvl idx x x heq with ⟨_, hs⟩ | hc
  · exact Or.inl (hs m hm1 hm2)
  · exact Or.inr hc

theorem no_append_forgery_walk_or_collision (h : Hash) (z0 : UInt256) (sibs : ℕ → UInt256)
    (leaves : List UInt256) (x y : UInt256) (height : ℕ) (hcap : leaves.length < 2 ^ height)
    (hsibs : ∀ l, l < height →
      sibs l = (levels h z0 leaves l).getD (sibIdx (leaves.length / 2 ^ l)) (zeros h z0 l))
    (hforge : walkPure h sibs 0 height leaves.length y = rootOf h z0 (leaves ++ [x]) height) :
    y = x ∨ WalkCollision h sibs sibs 0 height leaves.length y x := by
  rw [rootOf_append h z0 sibs leaves x height hcap hsibs] at hforge
  exact walk_pure_inj_or_collision h sibs height 0 leaves.length y x hforge

/-! ## Merkle `Verifier` -/

theorem accept_pins_entry_cases_or_collision (h : Hash) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256) (hj : j < 2 ^ k)
    (haccept : walkPure h sibs 0 k j x = rootOf h z0 L k) :
    (j < L.length ∧ L.getD j z0 = x) ∨ (L.length ≤ j ∧ x = z0)
      ∨ PathCollision h z0 L sibs 0 k j x := by
  rcases accept_pins_entry_or_collision h z0 L sibs k j x hj haccept with he | hc
  · by_cases hjL : j < L.length
    · exact Or.inl ⟨hjL, he⟩
    · refine Or.inr (Or.inl ⟨by omega, ?_⟩)
      rw [← he]
      exact getD_default L j z0 (by omega)
  · exact Or.inr (Or.inr hc)

/-! ## Certificates -/

theorem RootPinsEntryOrCollision : Properties.RootPinsEntryOrCollision :=
  root_pins_entry_or_collision
theorem WalkVsWalkOrCollision : Properties.WalkVsWalkOrCollision :=
  fun h s₁ s₂ k lvl j x y hw => walk_vs_walk_or_collision h s₁ s₂ k lvl j x y hw
theorem WalkVsWalkNeedsSameIndex : Properties.WalkVsWalkNeedsSameIndex := fun _ _ _ => rfl
theorem LevelUpInjOrCollision : Properties.LevelUpInjOrCollision := levelUp_inj_or_collision
theorem LevelsInjOrCollision : Properties.LevelsInjOrCollision :=
  fun h z0 L₁ L₂ l hlen he => levels_inj_or_collision h z0 L₁ L₂ hlen l he
theorem RootOfInjOrCollision : Properties.RootOfInjOrCollision := root_of_inj_or_collision
theorem RootOfAppendInjOrCollision : Properties.RootOfAppendInjOrCollision :=
  root_of_append_inj_or_collision
theorem RootOfSetInjOrCollision : Properties.RootOfSetInjOrCollision :=
  root_of_set_inj_or_collision
theorem WalkPureInjOrCollision : Properties.WalkPureInjOrCollision := walk_pure_inj_or_collision
theorem RootCommitsListOrBreak : Properties.RootCommitsListOrBreak := root_commits_list_or_break
theorem RootCommitsListUnderPadSeparation : Properties.RootCommitsListUnderPadSeparation :=
  root_commits_list_under_pad_separation
theorem NoForgedWalkOrCollision : Properties.NoForgedWalkOrCollision :=
  no_forged_walk_or_collision
theorem WalkAcceptPinsLeafFreeSibsOrCollision :
    Properties.WalkAcceptPinsLeafFreeSibsOrCollision :=
  walk_accept_pins_leaf_free_sibs_or_collision
theorem MemOfRootOfEqOrCollision : Properties.MemOfRootOfEqOrCollision :=
  mem_of_root_of_eq_or_collision
theorem GetDOfRootOfEqOrCollision : Properties.GetDOfRootOfEqOrCollision :=
  getD_of_root_of_eq_or_collision
theorem RootOfNeOfNotMemOrCollision : Properties.RootOfNeOfNotMemOrCollision :=
  root_of_ne_of_not_mem_or_collision
theorem RootNeOfLeafNeOrCollision : Properties.RootNeOfLeafNeOrCollision :=
  root_ne_of_leaf_ne_or_collision
theorem PathForgeryChangesWalkOrCollision : Properties.PathForgeryChangesWalkOrCollision :=
  path_forgery_changes_walk_or_collision
theorem WalkAcceptPinsLeafOrCollision : Properties.WalkAcceptPinsLeafOrCollision :=
  walk_accept_pins_leaf_or_collision
theorem LeafOnlySubstitutionChangesRootOrCollision :
    Properties.LeafOnlySubstitutionChangesRootOrCollision :=
  leaf_only_substitution_changes_root_or_collision
theorem SingleSiblingSubstitutionOrCollision : Properties.SingleSiblingSubstitutionOrCollision :=
  single_sibling_substitution_or_collision
theorem NoAppendForgeryWalkOrCollision : Properties.NoAppendForgeryWalkOrCollision :=
  no_append_forgery_walk_or_collision
theorem AcceptPinsEntryCasesOrCollision : Properties.AcceptPinsEntryCasesOrCollision :=
  accept_pins_entry_cases_or_collision

/-! ## Pinning, firing and padding witnesses -/

theorem EqualInstancesNeverCollide : Properties.EqualInstancesNeverCollide := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro h z0 L height i ⟨l, _, hne, _⟩; exact hne rfl
  · rintro h s lvl k j x ⟨i, _, hne, _⟩; exact hne rfl
  · rintro h z L ⟨m, _, hne, _⟩; exact hne rfl
  · rintro z0 L (⟨hlt, _⟩ | ⟨hlt, _⟩) <;> omega

theorem PaddingHitNeedsPaddingLeaf : Properties.PaddingHitNeedsPaddingLeaf :=
  padding_hit_needs_padding_leaf

theorem RootPinsEntryPinnedToPath : Properties.RootPinsEntryPinnedToPath := by
  unfold Properties.RootPinsEntryPinnedToPath TreeCollision
  decide

theorem PinnedFormsFire : Properties.PinnedFormsFire := by
  unfold Properties.PinnedFormsFire TreeCollision WalkCollision LevelCollision PathCollision
  -- Every conjunct is a closed computation except case 3's "agree off level 0", which
  -- quantifies over all levels.
  refine ⟨by decide, by decide, ⟨fun l hl => ite_eq_right hl, by decide, by decide, by decide⟩,
    by decide, by decide, by decide, by decide, by decide⟩

/-! ## Lists that agree at every padded entry are the same tree -/

/-- Appending the padding constant changes no `getD` with that default. -/
theorem getD_append_pad (z0 : UInt256) : ∀ (L : List UInt256) (j : ℕ),
    (L ++ [z0]).getD j z0 = L.getD j z0
  | [], 0 => rfl
  | [], _ + 1 => by simp
  | _ :: _, 0 => rfl
  | _ :: t, j + 1 => getD_append_pad z0 t j

/-- Two lists that agree at every `getD` with default `z0` agree at every level, every entry
read with the zero cascade as the default. -/
theorem levels_getD_congr (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (hL : ∀ j, L₁.getD j z0 = L₂.getD j z0) :
    ∀ l j, (levels h z0 L₁ l).getD j (zeros h z0 l) = (levels h z0 L₂ l).getD j (zeros h z0 l)
  | 0, j => by simpa using hL j
  | l + 1, j => by
    rw [levels_succ_getD, levels_succ_getD, levels_getD_congr h z0 L₁ L₂ hL l (2 * j),
      levels_getD_congr h z0 L₁ L₂ hL l (2 * j + 1)]

/-- **Lists agreeing at every padded entry are the same tree**, for every hash: the same root
at every height, and no collision located on any index's path. -/
theorem same_tree_of_getD_eq (h : Hash) (z0 : UInt256) (L₁ L₂ : List UInt256)
    (hL : ∀ j, L₁.getD j z0 = L₂.getD j z0) (height : ℕ) :
    rootOf h z0 L₁ height = rootOf h z0 L₂ height ∧ ∀ i, ¬ TreeCollision h z0 L₁ L₂ height i := by
  refine ⟨?_, ?_⟩
  · rw [rootOf_def, rootOf_def, ← getD_zero_headD, ← getD_zero_headD]
    exact levels_getD_congr h z0 L₁ L₂ hL height 0
  · rintro i ⟨l, _, hne, _⟩
    apply hne
    simp only [treePair, levels_getD_congr h z0 L₁ L₂ hL l]

/-- The one-leaf list and the same list padded with `z0` agree at every `getD` with default
`z0`. -/
theorem getD_singleton_padded (a z0 : UInt256) :
    ∀ n, ([a] : List UInt256).getD n z0 = ([a, z0] : List UInt256).getD n z0 :=
  fun n => (getD_append_pad z0 [a] n).symm

theorem padding_hit_fires (h : Hash) (z0 a : UInt256) :
    ([a] : List UInt256).length ≤ 2 ^ 1 ∧ ([a, z0] : List UInt256).length ≤ 2 ^ 1
      ∧ rootOf h z0 [a] 1 = rootOf h z0 [a, z0] 1 ∧ ([a] : List UInt256) ≠ [a, z0]
      ∧ PaddingHit z0 [a] [a, z0] ∧ ∀ i, ¬ TreeCollision h z0 [a] [a, z0] 1 i := by
  have hsame := same_tree_of_getD_eq h z0 [a] [a, z0] (getD_singleton_padded a z0) 1
  exact ⟨by simp, by simp, hsame.1, by simp, Or.inl ⟨by simp, rfl⟩, hsame.2⟩

theorem PaddingHitFires : Properties.PaddingHitFires := padding_hit_fires

theorem RootCommitsListCollisionFires : Properties.RootCommitsListCollisionFires := by
  unfold Properties.RootCommitsListCollisionFires PaddingHit TreeCollision
  decide

/-! ## Non-vacuity witnesses -/

theorem RootPinsEntryOrCollisionSatisfiable : Properties.RootPinsEntryOrCollisionSatisfiable :=
  ⟨constHash, 0, [1, 0, 5, 5], [0, 1, 5, 5], 2, 2, by decide, by decide, by decide,
    by unfold TreeCollision; decide⟩

theorem WalkVsWalkOrCollisionSatisfiable : Properties.WalkVsWalkOrCollisionSatisfiable := by
  refine ⟨constHash, fun _ => 0, fun l => if l = 0 then 0 else 1, 1, 0, 0, 0, 0, by decide,
    fun he => ?_, by unfold WalkCollision; decide⟩
  have h1 := congrFun he 1
  revert h1
  decide

theorem LevelUpInjOrCollisionSatisfiable : Properties.LevelUpInjOrCollisionSatisfiable :=
  ⟨constHash, 0, [1], [1], by decide, rfl, rfl, by unfold LevelCollision; decide⟩

theorem LevelsInjOrCollisionSatisfiable : Properties.LevelsInjOrCollisionSatisfiable :=
  ⟨constHash, 0, [1], [1], 1, by decide, by decide, rfl, rfl,
    by unfold LevelCollision; decide⟩

theorem RootOfInjOrCollisionSatisfiable : Properties.RootOfInjOrCollisionSatisfiable :=
  ⟨constHash, 0, [1], [1], 1, by decide, rfl, by decide, rfl, by unfold TreeCollision; decide⟩

theorem RootOfAppendInjOrCollisionSatisfiable :
    Properties.RootOfAppendInjOrCollisionSatisfiable :=
  ⟨constHash, 0, [1], 2, 2, 1, by decide, rfl, by unfold TreeCollision; decide⟩

theorem RootOfSetInjOrCollisionSatisfiable : Properties.RootOfSetInjOrCollisionSatisfiable :=
  ⟨constHash, 0, [7], 0, 1, 1, 1, by decide, by decide, rfl, by unfold TreeCollision; decide⟩

theorem WalkPureInjOrCollisionSatisfiable : Properties.WalkPureInjOrCollisionSatisfiable :=
  ⟨constHash, fun _ => 0, 1, 0, 0, 1, 1, by decide, rfl, by unfold WalkCollision; decide⟩

theorem RootCommitsListOrBreakSatisfiable : Properties.RootCommitsListOrBreakSatisfiable :=
  ⟨constHash, 0, [1], [1], 1, by decide, by decide, by decide, rfl,
    by unfold PaddingHit; decide, by unfold TreeCollision; decide⟩

theorem RootCommitsListUnderPadSeparationSatisfiable :
    Properties.RootCommitsListUnderPadSeparationSatisfiable :=
  ⟨constHash, 0, [1], [1], 1, by decide, by decide, by decide, by decide, by decide, rfl,
    by unfold TreeCollision; decide⟩

theorem NoForgedWalkOrCollisionSatisfiable : Properties.NoForgedWalkOrCollisionSatisfiable :=
  ⟨constHash, 0, [0], 1, 0, 0, 1, fun _ => 0, by decide, by decide⟩

theorem WalkAcceptPinsLeafFreeSibsOrCollisionSatisfiable :
    Properties.WalkAcceptPinsLeafFreeSibsOrCollisionSatisfiable :=
  ⟨constHash, 0, [1, 2], fun _ => 1, 1, 1, 2, by decide, by decide, by decide, by decide,
    by unfold PathCollision; decide⟩

theorem MemOfRootOfEqOrCollisionSatisfiable : Properties.MemOfRootOfEqOrCollisionSatisfiable :=
  ⟨constHash, 0, [1, 0, 5, 5], [0, 1, 5, 5], 2, 5, rfl, by decide, by decide, by decide,
    by decide, by unfold TreeCollision; decide⟩

theorem GetDOfRootOfEqOrCollisionSatisfiable :
    Properties.GetDOfRootOfEqOrCollisionSatisfiable :=
  ⟨constHash, 0, [1, 0, 5, 5], [0, 1, 5, 5], 2, 2, by decide, by decide, by decide, by decide,
    by decide, by unfold TreeCollision; decide⟩

theorem RootOfNeOfNotMemOrCollisionSatisfiable :
    Properties.RootOfNeOfNotMemOrCollisionSatisfiable :=
  ⟨sumHash, 0, [1], [0], 1, 1, by decide, by decide, by decide, by decide, by decide,
    by unfold TreeCollision; decide⟩

theorem RootNeOfLeafNeOrCollisionSatisfiable :
    Properties.RootNeOfLeafNeOrCollisionSatisfiable :=
  ⟨sumHash, 0, [1], [0], 1, 0, 0, by decide, by decide, by decide, by decide,
    by unfold TreeCollision; decide⟩

theorem PathForgeryChangesWalkOrCollisionSatisfiable :
    Properties.PathForgeryChangesWalkOrCollisionSatisfiable :=
  ⟨sumHash, fun _ => 0, 1, 0, 0, 1, 0, by decide, by decide, by unfold WalkCollision; decide⟩

theorem WalkAcceptPinsLeafOrCollisionSatisfiable :
    Properties.WalkAcceptPinsLeafOrCollisionSatisfiable :=
  ⟨constHash, 0, fun _ => 2, [1, 2], 0, 1, 1, walkPure constHash (fun _ => 2) 0 1 0 1,
    by decide, by decide, by decide, by decide, rfl, by unfold WalkCollision; decide⟩

theorem LeafOnlySubstitutionChangesRootOrCollisionSatisfiable :
    Properties.LeafOnlySubstitutionChangesRootOrCollisionSatisfiable :=
  ⟨sumHash, 0, fun _ => 0, [7], 0, 1, 0, 1, by decide, by decide, by decide, by decide,
    by unfold WalkCollision; decide, by unfold TreeCollision; decide⟩

theorem SingleSiblingSubstitutionOrCollisionSatisfiable :
    Properties.SingleSiblingSubstitutionOrCollisionSatisfiable :=
  ⟨constHash, fun _ => 0, fun _ => 0, 1, 0, 0, 0, 0, le_rfl, by decide, fun _ _ => rfl, rfl,
    by unfold WalkCollision; decide⟩

theorem NoAppendForgeryWalkOrCollisionSatisfiable :
    Properties.NoAppendForgeryWalkOrCollisionSatisfiable :=
  ⟨sumHash, 0, fun _ => 1, [1], 2, 2, 1, by decide, by decide, by decide, by decide, by decide,
    by unfold WalkCollision; decide⟩

theorem AcceptPinsEntryCasesOrCollisionSatisfiable :
    Properties.AcceptPinsEntryCasesOrCollisionSatisfiable :=
  ⟨sumHash, 0, [1], fun _ => 1, 1, 1, 0, by decide, by decide, by decide, by decide,
    by unfold PathCollision; decide⟩

end MerkleSpec.Pinned
