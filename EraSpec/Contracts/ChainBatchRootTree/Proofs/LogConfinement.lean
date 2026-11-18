import EraSpec.Contracts.ChainBatchRootTree.Properties.LogConfinement
import EraSpec.Contracts.ChainBatchRootTree.Proofs.Layout

/-!
# Proofs: log proofs against a ZKsync OS chain batch root (see `../Specs/LogConfinement.lean`)

The generic extractor is one induction on the walk length (`land_spec`): while `land` descends,
the walk's value after the remaining steps is the current subtree's value, because the pair it
hashed at the step above IS the node's pair. Where `land` stops, the walk's keccak input at that
step hashes to the landing node's value: either the two keccak inputs are the same string, or they
are a collision, or the node is a constant and the input hashes to it.

For the chain batch root, the only `cut` is leaf 0, reached exactly when the top three pairs
match with zero mask bits (`cbr_land_cut`), which is `PassesLeafZero`. A preimage match elsewhere
is impossible: at a node with steps left, `land` stopped because the pairs differ
(`land_mismatch`); at a node with no steps left the 88-byte log is not a 64-byte node preimage; at a
leaf the leaf's 96- or 34-byte input is neither a 64-byte node preimage nor an 88-byte log.
-/

namespace Contracts.ChainBatchRootTree

open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision word toBytesBE word_length length_toBytesBE)

/-! ## Lengths -/

theorem logPre_length (log : L2Log) : (logPre log).length = 88 := by
  simp [logPre, length_toBytesBE]

theorem imtLeafPre_length (ℓ : Contracts.InteropCommitmentTree.Leaf) :
    (imtLeafPre ℓ).length = 96 := by
  simp [imtLeafPre, length_toBytesBE]

theorem imtPaddingPre_length : imtPaddingPre.length = 34 := rfl

theorem walkPre_succ_length (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (xPre : List UInt8)
    (i : ℕ) : (walkPre keccak sibs j xPre (i + 1)).length = 64 :=
  pairPre_length _

/-- The walk's value after `i` steps is keccak of its keccak input there. -/
theorem walkPre_hash (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (xPre : List UInt8) :
    ∀ i, walkPure (node keccak) sibs 0 i j (keccak xPre) = keccak (walkPre keccak sibs j xPre i)
  | 0 => rfl
  | i + 1 => walkPure_succ_eq_walkPair (node keccak) sibs i 0 j _

/-! ## `land` -/

theorem land_zero (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) (T : PreTree) :
    T.land keccak sibs j x 0 = (T, 0) := by
  cases T <;> rfl

theorem land_node_succ (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256)
    (l r : PreTree) (k : ℕ) :
    (PreTree.node l r).land keccak sibs j x (k + 1)
      = if walkPair (node keccak) sibs 0 j x k = (l.val keccak, r.val keccak) then
          (if j / 2 ^ k % 2 = 1 then r.land keccak sibs j x k else l.land keccak sibs j x k)
        else (.node l r, k + 1) := rfl

theorem land_leaf (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) (p : List UInt8)
    (k : ℕ) : (PreTree.leaf p).land keccak sibs j x k = (.leaf p, k) := by
  cases k <;> rfl

theorem land_const (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) (v : UInt256)
    (k : ℕ) : (PreTree.const v).land keccak sibs j x k = (.const v, k) := by
  cases k <;> rfl

theorem land_cut (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) (v : UInt256)
    (k : ℕ) : (PreTree.cut v).land keccak sibs j x k = (.cut v, k) := by
  cases k <;> rfl

/-- The pair a walk hashes at step `k`, by the index bit there. -/
theorem walkPair_top (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) (k : ℕ) :
    walkPair (node keccak) sibs 0 j x k
      = if j / 2 ^ k % 2 = 1 then (sibs k, walkPure (node keccak) sibs 0 k j x)
        else (walkPure (node keccak) sibs 0 k j x, sibs k) := by
  rw [walkPair_eq_walkStep, Nat.zero_add]
  rfl

/-- **THE EXTRACTOR'S INVARIANT.** While `land` descends, the walk's value after the remaining steps
is the current subtree's value; so at the landing it is the landing node's value. -/
theorem land_spec (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) :
    ∀ (k : ℕ) (T : PreTree),
      walkPure (node keccak) sibs 0 k j x = T.val keccak →
        walkPure (node keccak) sibs 0 (T.land keccak sibs j x k).2 j x
          = (T.land keccak sibs j x k).1.val keccak := by
  intro k
  induction k with
  | zero =>
    intro T h
    rw [land_zero]
    exact h
  | succ k ih =>
    intro T h
    cases T with
    | node l r =>
      rw [land_node_succ]
      by_cases hp : walkPair (node keccak) sibs 0 j x k = (l.val keccak, r.val keccak)
      · rw [ite_eq_left hp]
        rw [walkPair_top] at hp
        by_cases hb : j / 2 ^ k % 2 = 1
        · rw [ite_eq_left hb]
          rw [ite_eq_left hb, Prod.mk.injEq] at hp
          exact ih r hp.2
        · rw [ite_eq_right hb]
          rw [ite_eq_right hb, Prod.mk.injEq] at hp
          exact ih l hp.1
      · rw [ite_eq_right hp]
        exact h
    | leaf p => rw [land_leaf]; exact h
    | const v => rw [land_const]; exact h
    | cut v => rw [land_cut]; exact h

/-- `land` stops at a node with steps left only where the walk's pair differs from the node's. -/
theorem land_mismatch (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) :
    ∀ (k : ℕ) (T l r : PreTree) (m : ℕ),
      T.land keccak sibs j x k = (.node l r, m + 1) →
        walkPair (node keccak) sibs 0 j x m ≠ (l.val keccak, r.val keccak) := by
  intro k
  induction k with
  | zero =>
    intro T l r m h
    rw [land_zero, Prod.mk.injEq] at h
    omega
  | succ k ih =>
    intro T l r m h
    cases T with
    | node l' r' =>
      rw [land_node_succ] at h
      by_cases hp : walkPair (node keccak) sibs 0 j x k = (l'.val keccak, r'.val keccak)
      · rw [ite_eq_left hp] at h
        by_cases hb : j / 2 ^ k % 2 = 1
        · rw [ite_eq_left hb] at h
          exact ih r' l r m h
        · rw [ite_eq_right hb] at h
          exact ih l' l r m h
      · rw [ite_eq_right hp, Prod.mk.injEq, PreTree.node.injEq] at h
        obtain ⟨⟨rfl, rfl⟩, hm⟩ := h
        rw [show m = k from by omega]
        exact hp
    | leaf p => rw [land_leaf, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
    | const v => rw [land_const, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
    | cut v => rw [land_cut, Prod.mk.injEq] at h; exact absurd h.1 (by simp)

/-- `land` returns a subtree. -/
theorem land_sub (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) :
    ∀ (k : ℕ) (T : PreTree), PreTree.Sub (T.land keccak sibs j x k).1 T := by
  intro k
  induction k with
  | zero => intro T; rw [land_zero]; exact .refl T
  | succ k ih =>
    intro T
    cases T with
    | node l r =>
      rw [land_node_succ]
      split_ifs
      · exact .right (ih r)
      · exact .left (ih l)
      · exact .refl _
    | leaf p => rw [land_leaf]; exact .refl _
    | const v => rw [land_const]; exact .refl _
    | cut v => rw [land_cut]; exact .refl _

/-! ## Subtree-closed predicates -/

theorem PreTree.Sub.cutFree {S T : PreTree} (h : S.Sub T) (hT : T.CutFree) : S.CutFree := by
  induction h with
  | refl => exact hT
  | left _ ih => exact ih hT.1
  | right _ ih => exact ih hT.2

theorem PreTree.Sub.leafLengthsAvoid {S T : PreTree} (h : S.Sub T) (hT : T.LeafLengthsAvoid) :
    S.LeafLengthsAvoid := by
  induction h with
  | refl => exact hT
  | left _ ih => exact ih hT.1
  | right _ ih => exact ih hT.2

theorem PreTree.Sub.hasLeaf {S T : PreTree} (h : S.Sub T) {q : List UInt8} (hS : S.HasLeaf q) :
    T.HasLeaf q := by
  induction h with
  | refl => exact hS
  | left _ ih => exact Or.inl ih
  | right _ ih => exact Or.inr ih

theorem PreTree.Sub.hasConst {S T : PreTree} (h : S.Sub T) {v : UInt256} (hS : S.HasConst v) :
    T.HasConst v := by
  induction h with
  | refl => exact hS
  | left _ ih => exact Or.inl ih
  | right _ ih => exact Or.inr ih

theorem land_not_cut_of_cutFree (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256)
    {T : PreTree} (hT : T.CutFree) (k : ℕ) (v : UInt256) (m : ℕ) :
    T.land keccak sibs j x k ≠ (.cut v, m) := by
  intro h
  have hs := (land_sub keccak sibs j x k T).cutFree hT
  rw [h] at hs
  exact hs

/-! ## (d1) The generic extractor -/

theorem accepted_walk_cut_match_or_break (keccak : Keccak) (T : PreTree) (sibs : ℕ → UInt256)
    (k j : ℕ) (xPre : List UInt8)
    (h : walkPure (node keccak) sibs 0 k j (keccak xPre) = T.val keccak) :
    LandingAtCut keccak T sibs k j xPre ∨ LandingPreimageMatch keccak T sibs k j xPre
      ∨ LandingBreak keccak T sibs k j xPre := by
  have hspec := land_spec keccak sibs j (keccak xPre) k T h
  have hin : keccak (landingInput keccak T sibs k j xPre)
      = (landing keccak T sibs k j xPre).1.val keccak := by
    rw [landingInput, ← walkPre_hash keccak sibs j xPre]
    exact hspec
  unfold LandingAtCut LandingPreimageMatch
  cases hS : (landing keccak T sibs k j xPre).1 with
  | node l r =>
    -- a node: its keccak input is the node preimage of its children's values
    rw [hS] at hin
    by_cases hm : landingInput keccak T sibs k j xPre = nodePre (l.val keccak) (r.val keccak)
    · exact Or.inr (Or.inl (by simp [PreTree.pre?, hm]))
    · exact Or.inr (Or.inr (LandingBreak.collision (nodePre (l.val keccak) (r.val keccak))
        (by rw [hS]; rfl) ⟨hm, hin⟩))
  | leaf p =>
    rw [hS] at hin
    by_cases hm : landingInput keccak T sibs k j xPre = p
    · exact Or.inr (Or.inl (by simp [PreTree.pre?, hm]))
    · exact Or.inr (Or.inr (LandingBreak.collision p (by rw [hS]; rfl) ⟨hm, hin⟩))
  | const v =>
    rw [hS] at hin
    exact Or.inr (Or.inr (LandingBreak.constHit v hS hin))
  | cut v =>
    refine Or.inl ⟨v, rfl, ?_⟩
    have hS' : (T.land keccak sibs j (keccak xPre) k).1 = .cut v := hS
    show walkPure (node keccak) sibs 0 (T.land keccak sibs j (keccak xPre) k).2 j (keccak xPre) = v
    rw [hspec, hS']
    rfl

/-- In a tree whose leaves avoid 64- and 88-byte inputs, a log proof's landing is never a
preimage match: at a node with steps left `land` stopped on differing pairs, at a node with no
steps left the 88-byte log is not a 64-byte node preimage, and at a leaf the lengths differ. -/
theorem no_preimage_match (keccak : Keccak) (T : PreTree) (hT : T.LeafLengthsAvoid) (log : L2Log)
    (sibs : ℕ → UInt256) (k j : ℕ) : ¬ LandingPreimageMatch keccak T sibs k j (logPre log) := by
  intro hmatch
  unfold LandingPreimageMatch landingInput landing at hmatch
  have hsub := land_sub keccak sibs j (keccak (logPre log)) k T
  have hmis := land_mismatch keccak sibs j (keccak (logPre log)) k T
  generalize T.land keccak sibs j (keccak (logPre log)) k = L at hmatch hsub hmis
  obtain ⟨S, r⟩ := L
  have havoid := hsub.leafLengthsAvoid hT
  cases S with
  | node l r' =>
    simp only [PreTree.pre?, Option.some.injEq] at hmatch
    cases r with
    | zero =>
      have := congrArg List.length hmatch
      simp only [walkPre, logPre_length, nodePre_length] at this
      omega
    | succ m =>
      exact hmis l r' m rfl (pairPre_inj (p := walkPair (node keccak) sibs 0 j _ m)
        (q := (l.val keccak, r'.val keccak)) hmatch.symm)
  | leaf p =>
    simp only [PreTree.pre?, Option.some.injEq] at hmatch
    obtain ⟨h64, h88⟩ := havoid
    cases r with
    | zero =>
      simp only [walkPre] at hmatch
      rw [hmatch, logPre_length] at h88
      exact h88 rfl
    | succ m =>
      rw [hmatch, walkPre_succ_length] at h64
      exact h64 rfl
  | const v => simp [PreTree.pre?] at hmatch
  | cut v => simp [PreTree.pre?] at hmatch

/-! ## (d2) The chain batch root -/

theorem cbrPreTree_val (keccak : Keccak) (a : UInt256) (T1 T2 T3 R : PreTree)
    (hR : R.val keccak = RESERVED_SUBTREE_NODE) :
    (cbrPreTree a T1 T2 T3 R).val keccak
      = compute keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak) := by
  simp only [cbrPreTree, PreTree.val, compute, liveSubtreeNode, hR]

theorem cbrPreTree_leafLengthsAvoid {a : UInt256} {T1 T2 T3 R : PreTree}
    (h1 : T1.LeafLengthsAvoid) (h2 : T2.LeafLengthsAvoid) (h3 : T3.LeafLengthsAvoid)
    (hR : R.LeafLengthsAvoid) : (cbrPreTree a T1 T2 T3 R).LeafLengthsAvoid :=
  ⟨⟨⟨trivial, h1⟩, ⟨h2, h3⟩⟩, hR⟩

/-- **THE ONLY CUT IS LEAF 0.** If `land` in the chain batch root's tree stops at a cut, the walk is
`k₃ + 3` long with `k₃` steps below the cut, the cut is leaf 0, the top three mask bits are zero, and
the walk hashed the tree's own pairs at the top three steps. -/
theorem cbr_land_cut (keccak : Keccak) (a : UInt256) (T1 T2 T3 R : PreTree) (sibs : ℕ → UInt256)
    (j : ℕ) (x : UInt256) (h1 : T1.CutFree) (h2 : T2.CutFree) (h3 : T3.CutFree) (hR : R.CutFree)
    (k : ℕ) (v : UInt256) (m : ℕ)
    (h : (cbrPreTree a T1 T2 T3 R).land keccak sibs j x k = (.cut v, m)) :
    ∃ k₃, k = k₃ + 3 ∧ m = k₃ ∧ v = a
      ∧ j / 2 ^ (k₃ + 2) % 2 = 0 ∧ j / 2 ^ (k₃ + 1) % 2 = 0 ∧ j / 2 ^ k₃ % 2 = 0
      ∧ walkPair (node keccak) sibs 0 j x (k₃ + 2)
          = ((PreTree.node (.node (.cut a) T1) (.node T2 T3)).val keccak, R.val keccak)
      ∧ walkPair (node keccak) sibs 0 j x (k₃ + 1)
          = ((PreTree.node (.cut a) T1).val keccak, (PreTree.node T2 T3).val keccak)
      ∧ walkPair (node keccak) sibs 0 j x k₃ = (a, T1.val keccak) := by
  have h23 : (PreTree.node T2 T3).CutFree := ⟨h2, h3⟩
  unfold cbrPreTree at h
  rcases k with _ | k₁
  · rw [land_zero, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
  rw [land_node_succ] at h
  by_cases hp₁ : walkPair (node keccak) sibs 0 j x k₁
      = ((PreTree.node (.node (.cut a) T1) (.node T2 T3)).val keccak, R.val keccak)
  swap
  · rw [ite_eq_right hp₁, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
  rw [ite_eq_left hp₁] at h
  by_cases hb₁ : j / 2 ^ k₁ % 2 = 1
  · rw [ite_eq_left hb₁] at h; exact absurd h (land_not_cut_of_cutFree keccak sibs j x hR k₁ v m)
  rw [ite_eq_right hb₁] at h
  rcases k₁ with _ | k₂
  · rw [land_zero, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
  rw [land_node_succ] at h
  by_cases hp₂ : walkPair (node keccak) sibs 0 j x k₂
      = ((PreTree.node (.cut a) T1).val keccak, (PreTree.node T2 T3).val keccak)
  swap
  · rw [ite_eq_right hp₂, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
  rw [ite_eq_left hp₂] at h
  by_cases hb₂ : j / 2 ^ k₂ % 2 = 1
  · rw [ite_eq_left hb₂] at h; exact absurd h (land_not_cut_of_cutFree keccak sibs j x h23 k₂ v m)
  rw [ite_eq_right hb₂] at h
  rcases k₂ with _ | k₃
  · rw [land_zero, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
  rw [land_node_succ] at h
  by_cases hp₃ : walkPair (node keccak) sibs 0 j x k₃ = ((PreTree.cut a).val keccak, T1.val keccak)
  swap
  · rw [ite_eq_right hp₃, Prod.mk.injEq] at h; exact absurd h.1 (by simp)
  rw [ite_eq_left hp₃] at h
  by_cases hb₃ : j / 2 ^ k₃ % 2 = 1
  · rw [ite_eq_left hb₃] at h; exact absurd h (land_not_cut_of_cutFree keccak sibs j x h1 k₃ v m)
  rw [ite_eq_right hb₃, land_cut, Prod.mk.injEq, PreTree.cut.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have b2 : j / 2 ^ (k₃ + 2) % 2 = 0 := by
    have := hb₁; rw [show k₃ + 1 + 1 = k₃ + 2 from rfl] at this; omega
  have b1 : j / 2 ^ (k₃ + 1) % 2 = 0 := by omega
  have b0 : j / 2 ^ k₃ % 2 = 0 := by omega
  exact ⟨k₃, rfl, rfl, rfl, b2, b1, b0, hp₁, hp₂, hp₃⟩

/-- Three zero bits on top of a `k₃ + 3`-bit index leave an index below `2^k₃`. -/
theorem lt_of_top_bits_zero {j k₃ : ℕ} (hj : j < 2 ^ (k₃ + 3)) (b2 : j / 2 ^ (k₃ + 2) % 2 = 0)
    (b1 : j / 2 ^ (k₃ + 1) % 2 = 0) (b0 : j / 2 ^ k₃ % 2 = 0) : j < 2 ^ k₃ := by
  have e1 : j / 2 ^ (k₃ + 1) = j / 2 ^ k₃ / 2 := by
    rw [Nat.div_div_eq_div_mul, pow_succ]
  have e2 : j / 2 ^ (k₃ + 2) = j / 2 ^ k₃ / 4 := by
    rw [Nat.div_div_eq_div_mul, show (2 : ℕ) ^ (k₃ + 2) = 2 ^ k₃ * 4 from by ring]
  have hq : j / 2 ^ k₃ < 8 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]
    calc j < 2 ^ (k₃ + 3) := hj
      _ = 8 * 2 ^ k₃ := by ring
  rw [e1] at b1
  rw [e2] at b2
  have hq0 : j / 2 ^ k₃ = 0 := by
    generalize j / 2 ^ k₃ = q at hq b0 b1 b2 ⊢
    omega
  by_contra hcon
  have := Nat.div_pos (not_lt.mp hcon) (by positivity : 0 < 2 ^ k₃)
  omega

/-- With mask bit `i` zero, the walk's value after `i + 1` steps is `node v (sibs i)`. -/
theorem walkPure_succ_left (keccak : Keccak) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256) (i : ℕ)
    (hb : j / 2 ^ i % 2 = 0) :
    walkPure (node keccak) sibs 0 (i + 1) j x
      = node keccak (walkPure (node keccak) sibs 0 i j x) (sibs i) := by
  rw [walkPure_succ_eq_walkPair, walkPair_top, ite_eq_right (by omega)]

theorem passes_leaf_zero_of_cut (keccak : Keccak) (a : UInt256) (T1 T2 T3 R : PreTree)
    (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256) (hR : R.val keccak = RESERVED_SUBTREE_NODE)
    (hj : j < 2 ^ k) (k₃ : ℕ) (hk : k = k₃ + 3)
    (b2 : j / 2 ^ (k₃ + 2) % 2 = 0) (b1 : j / 2 ^ (k₃ + 1) % 2 = 0) (b0 : j / 2 ^ k₃ % 2 = 0)
    (hp₁ : walkPair (node keccak) sibs 0 j x (k₃ + 2)
          = ((PreTree.node (.node (.cut a) T1) (.node T2 T3)).val keccak, R.val keccak))
    (hp₂ : walkPair (node keccak) sibs 0 j x (k₃ + 1)
          = ((PreTree.node (.cut a) T1).val keccak, (PreTree.node T2 T3).val keccak))
    (hp₃ : walkPair (node keccak) sibs 0 j x k₃ = (a, T1.val keccak)) :
    PassesLeafZero keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak) sibs k j x := by
  subst hk
  rw [walkPair_top, ite_eq_right (by omega), Prod.mk.injEq] at hp₁
  rw [walkPair_top, ite_eq_right (by omega), Prod.mk.injEq] at hp₂
  rw [walkPair_top, ite_eq_right (by omega), Prod.mk.injEq] at hp₃
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using lt_of_top_bits_zero hj b2 b1 b0
  · simpa using hp₃.1
  · simpa using hp₃.2
  · simpa [PreTree.val] using hp₂.2
  · simpa [hR] using hp₁.2

theorem log_proof_passes_leaf_zero_or_break (keccak : Keccak) (a : UInt256) (T1 T2 T3 R : PreTree)
    (log : L2Log) (sibs : ℕ → UInt256) (k j : ℕ) (c1 : T1.CutFree) (c2 : T2.CutFree)
    (c3 : T3.CutFree) (cR : R.CutFree) (l1 : T1.LeafLengthsAvoid) (l2 : T2.LeafLengthsAvoid)
    (l3 : T3.LeafLengthsAvoid) (lR : R.LeafLengthsAvoid) (hR : R.val keccak = RESERVED_SUBTREE_NODE)
    (hj : j < 2 ^ k)
    (hw : walkPure (node keccak) sibs 0 k j (keccak (logPre log))
        = compute keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak)) :
    PassesLeafZero keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak) sibs k j
        (keccak (logPre log))
      ∨ LandingBreak keccak (cbrPreTree a T1 T2 T3 R) sibs k j (logPre log) := by
  rw [← cbrPreTree_val keccak a T1 T2 T3 R hR] at hw
  rcases accepted_walk_cut_match_or_break keccak _ sibs k j (logPre log) hw with
    ⟨v, hcut, _⟩ | hmatch | hbreak
  · -- the cut: leaf 0
    left
    have hland : (cbrPreTree a T1 T2 T3 R).land keccak sibs j (keccak (logPre log)) k
        = (.cut v, (landing keccak (cbrPreTree a T1 T2 T3 R) sibs k j (logPre log)).2) := by
      rw [← hcut]; rfl
    obtain ⟨k₃, hk, _, _, b2, b1, b0, hp₁, hp₂, hp₃⟩ :=
      cbr_land_cut keccak a T1 T2 T3 R sibs j _ c1 c2 c3 cR k v _ hland
    exact passes_leaf_zero_of_cut keccak a T1 T2 T3 R sibs k j _ hR hj k₃ hk b2 b1 b0 hp₁ hp₂ hp₃
  · -- a preimage match is impossible
    exact absurd hmatch (no_preimage_match keccak _ (cbrPreTree_leafLengthsAvoid l1 l2 l3 lR) log
      sibs k j)
  · exact Or.inr hbreak

/-- `PassesLeafZero` puts the landing on the leaf-0 cut. -/
theorem land_of_passes_leaf_zero (keccak : Keccak) (a : UInt256) (T1 T2 T3 R : PreTree)
    (sibs : ℕ → UInt256) (k j : ℕ) (x : UInt256) (hR : R.val keccak = RESERVED_SUBTREE_NODE)
    (hp : PassesLeafZero keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak) sibs k j x) :
    (cbrPreTree a T1 T2 T3 R).land keccak sibs j x k = (.cut a, k - 3) := by
  obtain ⟨hk, hj, hv, hs0, hs1, hs2⟩ := hp
  obtain ⟨k₃, rfl⟩ : ∃ k₃, k = k₃ + 3 := ⟨k - 3, by omega⟩
  simp only [show k₃ + 3 - 3 = k₃ from by omega, show k₃ + 3 - 2 = k₃ + 1 from by omega,
    show k₃ + 3 - 1 = k₃ + 2 from by omega] at hj hv hs0 hs1 hs2 ⊢
  have hq : ∀ i, j / 2 ^ (k₃ + i) = 0 := fun i =>
    Nat.div_eq_of_lt (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have b0 : j / 2 ^ k₃ % 2 = 0 := by simpa using congrArg (· % 2) (hq 0)
  have b1 : j / 2 ^ (k₃ + 1) % 2 = 0 := by rw [hq 1]
  have b2 : j / 2 ^ (k₃ + 2) % 2 = 0 := by rw [hq 2]
  have v1 : walkPure (node keccak) sibs 0 (k₃ + 1) j x = node keccak a (T1.val keccak) := by
    rw [walkPure_succ_left keccak sibs j x k₃ b0, hv, hs0]
  have v2 : walkPure (node keccak) sibs 0 (k₃ + 2) j x
      = node keccak (node keccak a (T1.val keccak)) (node keccak (T2.val keccak) (T3.val keccak)) := by
    rw [walkPure_succ_left keccak sibs j x (k₃ + 1) b1, v1, hs1]
  have hp₃ : walkPair (node keccak) sibs 0 j x k₃ = ((PreTree.cut a).val keccak, T1.val keccak) := by
    rw [walkPair_top, ite_eq_right (by omega), hv, hs0]; rfl
  have hp₂ : walkPair (node keccak) sibs 0 j x (k₃ + 1)
      = ((PreTree.node (.cut a) T1).val keccak, (PreTree.node T2 T3).val keccak) := by
    rw [walkPair_top, ite_eq_right (by omega), v1, hs1]; rfl
  have hp₁ : walkPair (node keccak) sibs 0 j x (k₃ + 2)
      = ((PreTree.node (.node (.cut a) T1) (.node T2 T3)).val keccak, R.val keccak) := by
    rw [walkPair_top, ite_eq_right (by omega), v2, hs2, hR]; rfl
  unfold cbrPreTree
  rw [show k₃ + 3 = (k₃ + 2) + 1 from rfl, land_node_succ, ite_eq_left hp₁, ite_eq_right (by omega),
    show k₃ + 2 = (k₃ + 1) + 1 from rfl, land_node_succ, ite_eq_left hp₂, ite_eq_right (by omega),
    land_node_succ, ite_eq_left hp₃, ite_eq_right (by omega), land_cut]

theorem passes_leaf_zero_excludes_break (keccak : Keccak) (a : UInt256) (T1 T2 T3 R : PreTree)
    (log : L2Log) (sibs : ℕ → UInt256) (k j : ℕ) (hR : R.val keccak = RESERVED_SUBTREE_NODE)
    (hp : PassesLeafZero keccak a (T1.val keccak) (T2.val keccak) (T3.val keccak) sibs k j
        (keccak (logPre log))) :
    ¬ LandingBreak keccak (cbrPreTree a T1 T2 T3 R) sibs k j (logPre log) := by
  have hland := land_of_passes_leaf_zero keccak a T1 T2 T3 R sibs k j _ hR hp
  intro hb
  cases hb with
  | collision Y hY _ =>
    simp only [landing, hland, PreTree.pre?] at hY
    exact absurd hY (by simp)
  | constHit v hv _ =>
    simp only [landing, hland] at hv
    exact absurd hv (by simp)

/-! ## (d3) The IMT subtrees and the reserved half -/

/-- Every node of a complete tree over `f` is a node, or some `f m`. -/
theorem completePreTree_pred (P : PreTree → Prop) (f : ℕ → PreTree)
    (hf : ∀ m, P (f m)) (hnode : ∀ l r, P l → P r → P (.node l r)) :
    ∀ h o, P (completePreTree f h o)
  | 0, o => hf o
  | h + 1, o => hnode _ _ (completePreTree_pred P f hf hnode h o)
      (completePreTree_pred P f hf hnode h (o + 2 ^ h))

/-- The IMT's level-0 entries, as `PreTree` leaves. -/
def imtEntry (T : Contracts.InteropCommitmentTree.Tree) (m : ℕ) : PreTree :=
  if m < T.leafCount then .leaf (imtLeafPre (T.leaf m)) else .leaf imtPaddingPre

theorem imtEntry_val (keccak : Keccak) (T : Contracts.InteropCommitmentTree.Tree) (m : ℕ) :
    (imtEntry T m).val keccak
      = (Contracts.InteropCommitmentTree.leafHashes (imtHashLeaf keccak) T).getD m
          (keccak imtPaddingPre) := by
  unfold imtEntry Contracts.InteropCommitmentTree.leafHashes
  rw [List.getD_eq_getElem?_getD]
  by_cases hm : m < T.leafCount
  · rw [ite_eq_left hm]
    simp [PreTree.val, imtHashLeaf, hm]
  · rw [ite_eq_right hm]
    have : (List.map (fun i => imtHashLeaf keccak (T.leaf i)) (List.range T.leafCount))[m]? = none := by
      simp; omega
    rw [this]
    rfl

theorem completePreTree_val (keccak : Keccak) (z0 : UInt256) (L : List UInt256)
    (f : ℕ → PreTree) (hf : ∀ m, (f m).val keccak = L.getD m z0) :
    ∀ h o, (completePreTree f h (o * 2 ^ h)).val keccak
      = (levels (node keccak) z0 L h).getD o (zeros (node keccak) z0 h)
  | 0, o => by simpa [completePreTree] using hf o
  | h + 1, o => by
      have e1 : o * 2 ^ (h + 1) = (2 * o) * 2 ^ h := by ring
      have e2 : o * 2 ^ (h + 1) + 2 ^ h = (2 * o + 1) * 2 ^ h := by ring
      rw [levels_succ_getD]
      show node keccak ((completePreTree f h (o * 2 ^ (h + 1))).val keccak)
          ((completePreTree f h (o * 2 ^ (h + 1) + 2 ^ h)).val keccak) = _
      rw [e2, e1, completePreTree_val keccak z0 L f hf h (2 * o),
        completePreTree_val keccak z0 L f hf h (2 * o + 1)]

theorem imt_pre_tree_root (keccak : Keccak) (T : Contracts.InteropCommitmentTree.Tree) (H : ℕ) :
    (imtPreTree T H).val keccak = imtRoot keccak T H := by
  have := completePreTree_val keccak (keccak imtPaddingPre)
    (Contracts.InteropCommitmentTree.leafHashes (imtHashLeaf keccak) T) (imtEntry T)
    (imtEntry_val keccak T) H 0
  rw [Nat.zero_mul] at this
  rw [imtRoot, Contracts.InteropCommitmentTree.root, rootOf_def, ← getD_zero_headD, ← this]
  rfl

theorem zeroPreTree_val (keccak : Keccak) : ∀ h, (zeroPreTree h).val keccak = zeros (node keccak) 0 h
  | 0 => rfl
  | h + 1 => by
      show node keccak ((zeroPreTree h).val keccak) ((zeroPreTree h).val keccak) = _
      rw [zeroPreTree_val keccak h, zeros_succ]

theorem zero_pre_tree_reserved (keccak : Keccak) (hres : ReservedSubtreeDocumented keccak) :
    (zeroPreTree 2).val keccak = RESERVED_SUBTREE_NODE := by
  rw [zeroPreTree_val, hres]
  simp

/-! ### Shapes -/

theorem imtPreTree_cutFree (T : Contracts.InteropCommitmentTree.Tree) (H : ℕ) :
    (imtPreTree T H).CutFree :=
  completePreTree_pred PreTree.CutFree (imtEntry T)
    (fun m => by unfold imtEntry; split_ifs <;> trivial)
    (fun _ _ hl hr => ⟨hl, hr⟩) H 0

theorem imtPreTree_leafLengthsAvoid (T : Contracts.InteropCommitmentTree.Tree) (H : ℕ) :
    (imtPreTree T H).LeafLengthsAvoid :=
  completePreTree_pred PreTree.LeafLengthsAvoid (imtEntry T)
    (fun m => by
      unfold imtEntry
      split_ifs
      · show (imtLeafPre _).length ≠ 64 ∧ (imtLeafPre _).length ≠ 88
        rw [imtLeafPre_length]; omega
      · show imtPaddingPre.length ≠ 64 ∧ imtPaddingPre.length ≠ 88
        rw [imtPaddingPre_length]; omega)
    (fun _ _ hl hr => ⟨hl, hr⟩) H 0

theorem imtPreTree_hasLeaf (T : Contracts.InteropCommitmentTree.Tree) (H : ℕ) (q : List UInt8)
    (h : (imtPreTree T H).HasLeaf q) : q.length = 96 ∨ q.length = 34 := by
  have key := completePreTree_pred (fun S => S.HasLeaf q → q.length = 96 ∨ q.length = 34)
    (imtEntry T)
    (fun m hm => by
      unfold imtEntry at hm
      split_ifs at hm
      · left; rw [← hm]; exact imtLeafPre_length _
      · right; rw [← hm]; exact imtPaddingPre_length)
    (fun _ _ hl hr hlr => hlr.elim hl hr) H 0
  exact key h

theorem imtPreTree_not_hasConst (T : Contracts.InteropCommitmentTree.Tree) (H : ℕ) (v : UInt256) :
    ¬ (imtPreTree T H).HasConst v := by
  have key := completePreTree_pred (fun S => ¬ S.HasConst v) (imtEntry T)
    (fun m => by unfold imtEntry; split_ifs <;> exact fun h => h)
    (fun _ _ hl hr hlr => hlr.elim hl hr) H 0
  exact key

theorem zeroPreTree_cutFree : ∀ h, (zeroPreTree h).CutFree
  | 0 => trivial
  | h + 1 => ⟨zeroPreTree_cutFree h, zeroPreTree_cutFree h⟩

theorem zeroPreTree_leafLengthsAvoid : ∀ h, (zeroPreTree h).LeafLengthsAvoid
  | 0 => trivial
  | h + 1 => ⟨zeroPreTree_leafLengthsAvoid h, zeroPreTree_leafLengthsAvoid h⟩

theorem zeroPreTree_not_hasLeaf (q : List UInt8) : ∀ h, ¬ (zeroPreTree h).HasLeaf q
  | 0 => fun h => h
  | h + 1 => fun hh => hh.elim (zeroPreTree_not_hasLeaf q h) (zeroPreTree_not_hasLeaf q h)

theorem zeroPreTree_hasConst (v : UInt256) : ∀ h, (zeroPreTree h).HasConst v → v = 0
  | 0 => fun h => h.symm
  | h + 1 => fun hh => hh.elim (zeroPreTree_hasConst v h) (zeroPreTree_hasConst v h)

/-- **CLASSIFYING A `LandingBreak`.** In a collision the landing node's keccak input is a 64-byte
node preimage or a leaf input of the tree; in a constant hit the constant is one of the tree's. -/
theorem landingBreak_classify (keccak : Keccak) (T : PreTree) (sibs : ℕ → UInt256) (k j : ℕ)
    (xPre : List UInt8) (hb : LandingBreak keccak T sibs k j xPre) :
    (∃ Y, HashCollision keccak (landingInput keccak T sibs k j xPre) Y
        ∧ (Y.length = 64 ∨ T.HasLeaf Y))
      ∨ (∃ v, keccak (landingInput keccak T sibs k j xPre) = v ∧ T.HasConst v) := by
  have hsub := land_sub keccak sibs j (keccak xPre) k T
  cases hb with
  | collision Y hY hc =>
    left
    refine ⟨Y, hc, ?_⟩
    unfold landing at hY
    revert hY hsub
    generalize T.land keccak sibs j (keccak xPre) k = L
    obtain ⟨S, r⟩ := L
    intro hsub hY
    cases S with
    | node l r' =>
      simp only [PreTree.pre?, Option.some.injEq] at hY
      left; rw [← hY]; exact nodePre_length _ _
    | leaf p =>
      simp only [PreTree.pre?, Option.some.injEq] at hY
      right; rw [← hY]; exact hsub.hasLeaf rfl
    | const v => simp [PreTree.pre?] at hY
    | cut v => simp [PreTree.pre?] at hY
  | constHit v hS hv =>
    right
    refine ⟨v, hv, ?_⟩
    unfold landing at hS
    rw [hS] at hsub
    exact hsub.hasConst rfl

/-! ### The instantiated confinement -/

theorem imt_batch_root_log_proof (keccak : Keccak) (a : UInt256) (T1 : PreTree)
    (Tb Te : Contracts.InteropCommitmentTree.Tree) (Hb He : ℕ) (log : L2Log) (sibs : ℕ → UInt256)
    (k j : ℕ) (hres : ReservedSubtreeDocumented keccak) (c1 : T1.CutFree)
    (l1 : T1.LeafLengthsAvoid) (hj : j < 2 ^ k)
    (hw : walkPure (node keccak) sibs 0 k j (keccak (logPre log))
        = compute keccak a (T1.val keccak) (imtRoot keccak Tb Hb) (imtRoot keccak Te He)) :
    PassesLeafZero keccak a (T1.val keccak) (imtRoot keccak Tb Hb) (imtRoot keccak Te He) sibs k j
        (keccak (logPre log))
      ∨ (∃ Y, HashCollision keccak
            (landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)) Y
          ∧ ((landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).length
              = 88
            ∨ (landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).length
              = 64)
          ∧ (Y.length = 64 ∨ Y.length = 96 ∨ Y.length = 34 ∨ T1.HasLeaf Y))
      ∨ (∃ v, keccak
            (landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)) = v
          ∧ ((landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).length
              = 88
            ∨ (landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).length
              = 64)
          ∧ (v = 0 ∨ T1.HasConst v)) := by
  rw [← imt_pre_tree_root keccak Tb Hb, ← imt_pre_tree_root keccak Te He] at hw ⊢
  have hlen : (landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).length
        = 88
      ∨ (landingInput keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).length
        = 64 := by
    unfold landingInput
    rcases (landing keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log)).2 with _ | m
    · left; exact logPre_length log
    · right; exact walkPre_succ_length keccak sibs j _ m
  rcases log_proof_passes_leaf_zero_or_break keccak a T1 (imtPreTree Tb Hb) (imtPreTree Te He)
      (zeroPreTree 2) log sibs k j c1 (imtPreTree_cutFree Tb Hb) (imtPreTree_cutFree Te He)
      (zeroPreTree_cutFree 2) l1 (imtPreTree_leafLengthsAvoid Tb Hb)
      (imtPreTree_leafLengthsAvoid Te He) (zeroPreTree_leafLengthsAvoid 2)
      (zero_pre_tree_reserved keccak hres) hj hw with hp | hb
  · exact Or.inl hp
  · right
    have hb' : LandingBreak keccak (imtBatchPreTree a T1 Tb Hb Te He) sibs k j (logPre log) := hb
    rcases landingBreak_classify keccak _ sibs k j _ hb' with ⟨Y, hc, hY⟩ | ⟨v, hv, hc⟩
    · left
      refine ⟨Y, hc, hlen, ?_⟩
      rcases hY with hY | hl
      · exact Or.inl hY
      · simp only [imtBatchPreTree, cbrPreTree, PreTree.HasLeaf] at hl
        rcases hl with ((hl | hl) | (hl | hl)) | hl
        · exact absurd hl id
        · exact Or.inr (Or.inr (Or.inr hl))
        · exact (imtPreTree_hasLeaf Tb Hb Y hl).elim (fun h => Or.inr (Or.inl h))
            (fun h => Or.inr (Or.inr (Or.inl h)))
        · exact (imtPreTree_hasLeaf Te He Y hl).elim (fun h => Or.inr (Or.inl h))
            (fun h => Or.inr (Or.inr (Or.inl h)))
        · exact absurd hl (zeroPreTree_not_hasLeaf Y 2)
    · right
      refine ⟨v, hv, hlen, ?_⟩
      simp only [imtBatchPreTree, cbrPreTree, PreTree.HasConst] at hc
      rcases hc with ((hc | hc) | (hc | hc)) | hc
      · exact absurd hc id
      · exact Or.inr hc
      · exact absurd hc (imtPreTree_not_hasConst Tb Hb v)
      · exact absurd hc (imtPreTree_not_hasConst Te He v)
      · exact Or.inl (zeroPreTree_hasConst v 2 hc)

/-! ## Witnesses -/

/-- The witness keccak: 64 zero bytes ↦ `1`, `nodePre 1 1` ↦ `RESERVED_SUBTREE_NODE`, every 88- or
96-byte string ↦ `7`, everything else ↦ `0`. -/
def confinementKeccak : Keccak := fun s =>
  if s = nodePre 0 0 then 1 else if s = nodePre 1 1 then RESERVED_SUBTREE_NODE
  else if s.length = 88 ∨ s.length = 96 then 7 else 0

theorem confinementKeccak_long {s : List UInt8} (h : s.length = 88 ∨ s.length = 96) :
    confinementKeccak s = 7 := by
  have h0 : s ≠ nodePre 0 0 := fun e => by
    rw [e, nodePre_length] at h; omega
  have h1 : s ≠ nodePre 1 1 := fun e => by
    rw [e, nodePre_length] at h; omega
  simp [confinementKeccak, h0, h1, h]

theorem confinementKeccak_documented : ReservedSubtreeDocumented confinementKeccak := by
  have h01 : nodePre 1 1 ≠ nodePre 0 0 := fun h => absurd (nodePre_inj h).1 (by decide)
  have e1 : node confinementKeccak 0 0 = 1 := by
    show confinementKeccak (nodePre 0 0) = 1
    simp [confinementKeccak]
  have e2 : node confinementKeccak 1 1 = RESERVED_SUBTREE_NODE := by
    show confinementKeccak (nodePre 1 1) = RESERVED_SUBTREE_NODE
    simp [confinementKeccak, h01]
  unfold ReservedSubtreeDocumented
  rw [e1, e2]

/-- A log for the witnesses: shard 0, a service log, transaction 1, sender 1, key 1, value 1. -/
def witnessLog : L2Log := ⟨0, true, 1, 1, 1, 1⟩

/-- The freshly set-up IMT at height 0 is its sentinel leaf. -/
theorem imtPreTree_setup_val (K : Keccak) :
    (imtPreTree Contracts.InteropCommitmentTree.setup 0).val K = K (imtLeafPre ⟨0, 0, 0⟩) := rfl

/-! The witnesses are proved for every keccak `K` with three properties (documented reserved
value, the witness log and the `{0,0,0}` leaf both hashed to `7`), then instantiated with
`confinementKeccak`. -/

theorem honest_witness_of (K : Keccak) (hdoc : ReservedSubtreeDocumented K)
    (hlog : K (logPre witnessLog) = 7) (himt : K (imtLeafPre ⟨0, 0, 0⟩) = 7) :
    let c := imtRoot K Contracts.InteropCommitmentTree.setup 0
    let sibs : ℕ → UInt256 := fun l =>
      if l = 0 then 0 else if l = 1 then node K c c else RESERVED_SUBTREE_NODE
    walkPure (node K) sibs 0 3 0 (K (logPre witnessLog))
        = compute K 7 ((PreTree.const 0).val K) c c
      ∧ PassesLeafZero K 7 ((PreTree.const 0).val K) c c sibs 3 0 (K (logPre witnessLog))
      ∧ ¬ LandingBreak K (imtBatchPreTree 7 (.const 0) Contracts.InteropCommitmentTree.setup 0
          Contracts.InteropCommitmentTree.setup 0) sibs 3 0 (logPre witnessLog) := by
  intro c sibs
  have hc : c = 7 := by
    show imtRoot K Contracts.InteropCommitmentTree.setup 0 = 7
    rw [← imt_pre_tree_root, imtPreTree_setup_val, himt]
  have hpass : PassesLeafZero K 7 ((PreTree.const 0).val K) c c sibs 3 0 (K (logPre witnessLog)) :=
    ⟨le_rfl, by decide, by rw [hlog]; rfl, rfl, rfl, rfl⟩
  refine ⟨?_, hpass, ?_⟩
  · rw [hlog]
    rfl
  · have hpass' : PassesLeafZero K 7 ((PreTree.const 0).val K)
        ((imtPreTree Contracts.InteropCommitmentTree.setup 0).val K)
        ((imtPreTree Contracts.InteropCommitmentTree.setup 0).val K) sibs 3 0
        (K (logPre witnessLog)) := by
      rw [imt_pre_tree_root]
      exact hpass
    exact passes_leaf_zero_excludes_break K 7 (.const 0)
      (imtPreTree Contracts.InteropCommitmentTree.setup 0)
      (imtPreTree Contracts.InteropCommitmentTree.setup 0) (zeroPreTree 2) witnessLog sibs 3 0
      (zero_pre_tree_reserved K hdoc) hpass'

theorem collision_witness_of (K : Keccak) (hdoc : ReservedSubtreeDocumented K)
    (hlog : K (logPre witnessLog) = 7) (himt : K (imtLeafPre ⟨0, 0, 0⟩) = 7) :
    let sibs : ℕ → UInt256 := fun l =>
      if l = 0 then 7 else if l = 1 then node K 5 0 else RESERVED_SUBTREE_NODE
    walkPure (node K) sibs 0 TREE_DEPTH IMT_BEGIN_ROOT_LEAF_INDEX (K (logPre witnessLog))
        = compute K 5 ((PreTree.const 0).val K)
            (imtRoot K Contracts.InteropCommitmentTree.setup 0)
            (imtRoot K Contracts.InteropCommitmentTree.setup 0)
      ∧ landing K (imtBatchPreTree 5 (.const 0) Contracts.InteropCommitmentTree.setup 0
          Contracts.InteropCommitmentTree.setup 0) sibs TREE_DEPTH IMT_BEGIN_ROOT_LEAF_INDEX
          (logPre witnessLog) = (.leaf (imtLeafPre ⟨0, 0, 0⟩), 0) := by
  intro sibs
  have hT2 : (imtPreTree Contracts.InteropCommitmentTree.setup 0).val K = 7 := by
    rw [imtPreTree_setup_val, himt]
  have hc : imtRoot K Contracts.InteropCommitmentTree.setup 0 = 7 := by
    rw [← imt_pre_tree_root]; exact hT2
  have hR : (zeroPreTree 2).val K = RESERVED_SUBTREE_NODE := zero_pre_tree_reserved K hdoc
  -- the three pairs the walk hashes
  have hp0 : walkPair (node K) sibs 0 IMT_BEGIN_ROOT_LEAF_INDEX (K (logPre witnessLog)) 0
      = ((imtPreTree Contracts.InteropCommitmentTree.setup 0).val K,
         (imtPreTree Contracts.InteropCommitmentTree.setup 0).val K) := by
    rw [hT2, hlog]; rfl
  have hp1 : walkPair (node K) sibs 0 IMT_BEGIN_ROOT_LEAF_INDEX (K (logPre witnessLog)) 1
      = ((PreTree.node (.cut 5) (.const 0)).val K,
         (PreTree.node (imtPreTree Contracts.InteropCommitmentTree.setup 0)
           (imtPreTree Contracts.InteropCommitmentTree.setup 0)).val K) := by
    show _ = (node K 5 0, node K ((imtPreTree Contracts.InteropCommitmentTree.setup 0).val K)
      ((imtPreTree Contracts.InteropCommitmentTree.setup 0).val K))
    rw [hT2, hlog]; rfl
  have hp2 : walkPair (node K) sibs 0 IMT_BEGIN_ROOT_LEAF_INDEX (K (logPre witnessLog)) 2
      = ((PreTree.node (.node (.cut 5) (.const 0))
           (.node (imtPreTree Contracts.InteropCommitmentTree.setup 0)
             (imtPreTree Contracts.InteropCommitmentTree.setup 0))).val K,
         (zeroPreTree 2).val K) := by
    show _ = (node K (node K 5 0) (node K ((imtPreTree Contracts.InteropCommitmentTree.setup 0).val K)
      ((imtPreTree Contracts.InteropCommitmentTree.setup 0).val K)), (zeroPreTree 2).val K)
    rw [hT2, hlog, hR]; rfl
  refine ⟨?_, ?_⟩
  · rw [hc, hlog]
    rfl
  · unfold landing imtBatchPreTree cbrPreTree
    rw [show TREE_DEPTH = 2 + 1 from rfl, land_node_succ, ite_eq_left hp2,
      ite_eq_right (by decide), land_node_succ, ite_eq_left hp1, ite_eq_left (by decide),
      land_node_succ, ite_eq_left hp0, ite_eq_right (by decide), land_zero]
    rfl

theorem witness_log_hash : confinementKeccak (logPre witnessLog) = 7 :=
  confinementKeccak_long (Or.inl (logPre_length _))

theorem witness_imt_hash : confinementKeccak (imtLeafPre ⟨0, 0, 0⟩) = 7 :=
  confinementKeccak_long (Or.inr (imtLeafPre_length _))

theorem honest_log_proof_passes_leaf_zero : Properties.HonestLogProofPassesLeafZero := by
  obtain ⟨hw, hp, hnb⟩ := honest_witness_of confinementKeccak confinementKeccak_documented
    witness_log_hash witness_imt_hash
  exact ⟨confinementKeccak, 7, .const 0, Contracts.InteropCommitmentTree.setup,
    Contracts.InteropCommitmentTree.setup, 0, 0, witnessLog, _, 3, 0, confinementKeccak_documented,
    trivial, trivial, by decide, hw, hp, hnb⟩

theorem imt_landing_collision_fires : Properties.ImtLandingCollisionFires := by
  obtain ⟨hw, hland⟩ := collision_witness_of confinementKeccak confinementKeccak_documented
    witness_log_hash witness_imt_hash
  refine ⟨confinementKeccak, 5, .const 0, witnessLog, _, confinementKeccak_documented, trivial,
    trivial, by decide, hw, ?_, ?_, congrArg Prod.fst hland, ?_⟩
  · rintro ⟨_, hj, _⟩
    exact absurd hj (by decide)
  · simp only [landingInput, hland]
    rfl
  · refine ⟨fun h => ?_, ?_⟩
    · have := congrArg List.length h
      rw [logPre_length, imtLeafPre_length] at this
      omega
    · rw [witness_log_hash, witness_imt_hash]

/-! ## Certificates -/

theorem AcceptedWalkCutMatchOrBreak : Properties.AcceptedWalkCutMatchOrBreak :=
  accepted_walk_cut_match_or_break

theorem LogProofPassesLeafZeroOrBreak : Properties.LogProofPassesLeafZeroOrBreak :=
  log_proof_passes_leaf_zero_or_break

theorem PassesLeafZeroExcludesBreak : Properties.PassesLeafZeroExcludesBreak :=
  passes_leaf_zero_excludes_break

theorem ImtPreTreeRoot : Properties.ImtPreTreeRoot := imt_pre_tree_root

theorem ZeroPreTreeReserved : Properties.ZeroPreTreeReserved := zero_pre_tree_reserved

theorem ImtBatchRootLogProofConfinedOrKeccakEvent :
    Properties.ImtBatchRootLogProofConfinedOrKeccakEvent :=
  imt_batch_root_log_proof

theorem HonestLogProofPassesLeafZero : Properties.HonestLogProofPassesLeafZero :=
  honest_log_proof_passes_leaf_zero

theorem ImtLandingCollisionFires : Properties.ImtLandingCollisionFires :=
  imt_landing_collision_fires

theorem LogProofPassesLeafZeroWitness : Properties.LogProofPassesLeafZeroWitness := by
  obtain ⟨hw, hp, _⟩ := honest_witness_of confinementKeccak confinementKeccak_documented
    witness_log_hash witness_imt_hash
  refine ⟨confinementKeccak, 7, .const 0, imtPreTree Contracts.InteropCommitmentTree.setup 0,
    imtPreTree Contracts.InteropCommitmentTree.setup 0, zeroPreTree 2, witnessLog,
    fun l => if l = 0 then 0
      else if l = 1 then node confinementKeccak
          (imtRoot confinementKeccak Contracts.InteropCommitmentTree.setup 0)
          (imtRoot confinementKeccak Contracts.InteropCommitmentTree.setup 0)
      else RESERVED_SUBTREE_NODE, 3, 0,
    trivial, imtPreTree_cutFree _ _, imtPreTree_cutFree _ _, zeroPreTree_cutFree 2,
    trivial, imtPreTree_leafLengthsAvoid _ _, imtPreTree_leafLengthsAvoid _ _,
    zeroPreTree_leafLengthsAvoid 2, zero_pre_tree_reserved _ confinementKeccak_documented,
    by decide, ?_, ?_⟩
  · rw [imt_pre_tree_root]; exact hw
  · rw [imt_pre_tree_root]; exact hp

end Contracts.ChainBatchRootTree
