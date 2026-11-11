import EraSpec.Contracts.L2InteropCommitmentTree.Properties.TreeRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Model
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Reaches
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearch
import EraSpec.Contracts.Merkle.Proofs.Verifier
import EraSpec.Contracts.Merkle.Proofs.PathCollision

/-!
# Proofs: the root and the two proof gates

Proofs of `EraSpec.Contracts.L2InteropCommitmentTree.Properties.TreeRoot`.  The Merkle content is
`EraSpec.Contracts.Merkle.Proofs.Verifier` (an accepted walk pins the level-0 entry at any
index and forces the path length); what this file adds is the translation
between that list-level statement and the `Tree`, and the concrete padding
countermodel.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier

/-! ## The leaf-hash list -/

@[simp] lemma leafHashes_length {hl : LeafHash} {T : Tree} :
    (leafHashes hl T).length = T.leafCount := by
  simp [leafHashes]

lemma leafHashes_getD {hl : LeafHash} {T : Tree} {i : ℕ} (hi : i < T.leafCount) (d : UInt256) :
    (leafHashes hl T).getD i d = hl (T.leaf i) := by
  simp [leafHashes, List.getD_eq_get?, List.get?_map, List.get?_range hi]

lemma mem_leafHashes {hl : LeafHash} {T : Tree} {y : UInt256} :
    y ∈ leafHashes hl T ↔ ∃ i < T.leafCount, hl (T.leaf i) = y := by
  simp [leafHashes, List.mem_map, List.mem_range]

/-! ## Fold correspondence -/

private theorem getD_set_ne (x : UInt256) : ∀ (L : List UInt256) (i j : ℕ) (d : UInt256),
    i ≠ j → (L.set i x).getD j d = L.getD j d
  | [], _, _, _, _ => rfl
  | _ :: _, 0, 0, _, hij => absurd rfl hij
  | _ :: _, 0, _ + 1, _, _ => rfl
  | _ :: _, _ + 1, 0, _, _ => rfl
  | _ :: t, i + 1, j + 1, d, hij =>
    getD_set_ne x t i j d (fun hcon => hij (by rw [hcon]))

private theorem getD_set_self (x : UInt256) : ∀ (L : List UInt256) (i : ℕ) (d : UInt256),
    i < L.length → (L.set i x).getD i d = x
  | [], _, _, hi => absurd hi (by simp)
  | _ :: _, 0, _, _ => rfl
  | _ :: t, i + 1, d, hi =>
    getD_set_self x t i d (by simp only [List.length_cons] at hi; omega)

private theorem getD_append_lt : ∀ (A B : List UInt256) (n : ℕ) (d : UInt256),
    n < A.length → (A ++ B).getD n d = A.getD n d
  | [], _, _, _, hn => absurd hn (by simp)
  | _ :: _, _, 0, _, _ => rfl
  | _ :: t, B, n + 1, d, hn =>
    getD_append_lt t B n d (by simp only [List.length_cons] at hn; omega)

private theorem getD_append_len : ∀ (A : List UInt256) (y d : UInt256) (n : ℕ),
    n = A.length → (A ++ [y]).getD n d = y
  | [], _, _, 0, _ => rfl
  | [], _, _, _ + 1, hn => absurd hn (by simp)
  | _ :: _, _, _, 0, hn => absurd hn (by simp)
  | _ :: t, y, d, n + 1, hn =>
    getD_append_len t y d n (by simp only [List.length_cons] at hn; omega)

/-- Two lists agreeing in length and at every in-range `getD` are equal. -/
private theorem ext_getD (d : UInt256) : ∀ (L₁ L₂ : List UInt256),
    L₁.length = L₂.length → (∀ n, n < L₁.length → L₁.getD n d = L₂.getD n d) → L₁ = L₂
  | [], [], _, _ => rfl
  | [], _ :: _, hlen, _ => absurd hlen (by simp)
  | _ :: _, [], hlen, _ => absurd hlen (by simp)
  | a :: t, b :: u, hlen, hget => by
    have hab : a = b := hget 0 (by simp)
    have htu : t = u := ext_getD d t u (by simpa using hlen)
      (fun n hn => hget (n + 1) (by simp only [List.length_cons]; omega))
    rw [hab, htu]

/-- **`insert` IS `updateLeaf` THEN `pushNewLeaf` ON THE LEAF-HASH LIST.** -/
theorem leafHashes_insert {hl : LeafHash} {T : Tree} {v : UInt256} {low : ℕ}
    (hlow : low < T.leafCount) :
    leafHashes hl (insert T v low)
      = (leafHashes hl T).set low (hl { T.leaf low with nextIndex := T.leafCount, nextValue := v })
          ++ [hl ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩] := by
  apply ext_getD 0
  · simp
  · intro n hn
    rw [leafHashes_length, insert_leafCount] at hn
    rw [leafHashes_getD (by rw [insert_leafCount]; exact hn)]
    by_cases hnew : n = T.leafCount
    · rw [hnew, insert_leaf_new hlow, getD_append_len _ _ _ _ (by simp)]
    · have hn' : n < T.leafCount := by omega
      rw [getD_append_lt _ _ _ _ (by rw [List.length_set, leafHashes_length]; exact hn')]
      by_cases hl : n = low
      · rw [hl, insert_leaf_low, getD_set_self _ _ _ _ (by rw [leafHashes_length]; exact hlow)]
      · rw [insert_leaf_other hl hnew, getD_set_ne _ _ _ _ _ (fun e => hl e.symm),
            leafHashes_getD hn']

/-- The intermediate root `updateLeaf` returns — M-A over the leaf-hash list. -/
theorem root_after_updateLeaf {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree} {low : ℕ}
    {x : UInt256} {height : ℕ} (hlow : low < T.leafCount) (hcap : T.leafCount ≤ 2 ^ height) :
    rootOf h z0 ((leafHashes hl T).set low x) height
      = walkPure h (honestSibs h z0 (leafHashes hl T) low) 0 height low x :=
  (walkPure_update_orig h z0 (honestSibs h z0 (leafHashes hl T) low) (leafHashes hl T) low x
    height (by rw [leafHashes_length]; exact hlow) (by rw [leafHashes_length]; exact hcap)
    (fun l _ => rfl)).symm

/-- M-B with the honest sibling stream. -/
theorem rootOf_append_honest (h : Hash) (z0 : UInt256) (L : List UInt256) (x : UInt256)
    (height : ℕ) (hcap : L.length < 2 ^ height) :
    rootOf h z0 (L ++ [x]) height = walkPure h (honestSibs h z0 L L.length) 0 height L.length x :=
  rootOf_append h z0 _ L x height hcap (fun _ _ => rfl)

/-- **THE ROOT AFTER `insert` IS THE `pushNewLeaf` WALK.** -/
theorem root_after_insert {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree} {v : UInt256}
    {low height : ℕ} (hlow : low < T.leafCount) (hcap : T.leafCount < 2 ^ height) :
    root h z0 hl (insert T v low) height
      = walkPure h
          (honestSibs h z0
            ((leafHashes hl T).set low (hl { T.leaf low with nextIndex := T.leafCount, nextValue := v }))
            T.leafCount)
          0 height T.leafCount (hl ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩) := by
  unfold root
  rw [leafHashes_insert hlow,
      rootOf_append_honest h z0 _ _ height (by rw [List.length_set, leafHashes_length]; exact hcap),
      List.length_set, leafHashes_length]

/-! ## Soundness -/

theorem accepted_path_pins_leaf {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {T : Tree} {height : ℕ}
    {sibs : ℕ → UInt256} {k idx : ℕ} {ℓ : Leaf}
    (hp : PathAccepts h (root h z0 hl T height) sibs k idx (hl ℓ)) :
    k = height ∧ idx < T.leafCount ∧ T.leaf idx = ℓ := by
  have hL : ∀ y ∈ leafHashes hl T, ∀ a b : UInt256, y ≠ h a b := by
    intro y hy a b
    obtain ⟨i, _, rfl⟩ := mem_leafHashes.mp hy
    exact hA.leafNotNode _ a b
  obtain ⟨hk, hget⟩ := accept_pins_entry_any_length h z0 hA.nodeInj (leafHashes hl T) hL
    hA.padNotNode sibs k height idx (hl ℓ) (hA.leafNotNode ℓ) hp.inBounds hp.recompute
  refine ⟨hk, ?_⟩
  by_cases hidx : idx < T.leafCount
  · refine ⟨hidx, ?_⟩
    rw [leafHashes_getD hidx] at hget
    exact hA.leafInj hget
  · exfalso
    rw [getD_default _ _ _ (by rw [leafHashes_length]; omega)] at hget
    exact hA.padNotLeaf ℓ hget.symm

theorem inclusion_sound {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {T : Tree} {height : ℕ} {v : UInt256} {ℓ : Leaf}
    {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hI : InclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k) :
    v ∈ keys (toAbs T) := by
  obtain ⟨_, hidx, hleaf⟩ := accepted_path_pins_leaf hA hI.path
  exact Finset.mem_image.mpr
    ⟨⟨v, ℓ.nextValue⟩,
     mem_toAbs.mpr ⟨idx, hidx, by rw [hleaf]; exact hI.valueMatch, by rw [hleaf]⟩, rfl⟩

theorem non_inclusion_sound {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {T : Tree} {height : ℕ} {v : UInt256} {ℓ : Leaf}
    {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k) :
    ∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey) := by
  obtain ⟨_, hidx, hleaf⟩ := accepted_path_pins_leaf hA hN.path
  exact ⟨⟨ℓ.value, ℓ.nextValue⟩,
    mem_toAbs.mpr ⟨idx, hidx, by rw [hleaf], by rw [hleaf]⟩, hN.lowBelow, hN.window⟩

theorem verified_absence_excludes_delivered {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {T : Tree} (hV : Valid T) {height : ℕ} {v : UInt256}
    {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k) :
    v ∉ keys (toAbs T) :=
  fun hmem => present_not_reclaimable hV.absSound.1 hmem (non_inclusion_sound hA hN)

theorem proofs_exclusive {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {T : Tree} (hV : Valid T) {height : ℕ} {v : UInt256}
    {ℓ₁ ℓ₂ : Leaf} {i₁ i₂ : ℕ} {s₁ s₂ : ℕ → UInt256} {k₁ k₂ : ℕ} :
    ¬ (InclusionAccepted h hl (root h z0 hl T height) v ℓ₁ i₁ s₁ k₁
        ∧ NonInclusionAccepted h hl (root h z0 hl T height) v ℓ₂ i₂ s₂ k₂) :=
  fun ⟨hI, hN⟩ => verified_absence_excludes_delivered hA hV hN (inclusion_sound hA hI)

theorem run_roots_exclusive {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {R : ℕ → Tree} (hR : Run R) (h0 : R 0 = setup)
    {n height : ℕ} {v : UInt256} {ℓ₁ ℓ₂ : Leaf} {i₁ i₂ : ℕ} {s₁ s₂ : ℕ → UInt256} {k₁ k₂ : ℕ} :
    ¬ (InclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₁ i₁ s₁ k₁
        ∧ NonInclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₂ i₂ s₂ k₂) :=
  proofs_exclusive hA (run_valid hR (by rw [h0]; exact setup_valid) n)

open Contracts.Protocol in
theorem verified_absence_is_witness {h : Hash} {z0 : UInt256} {hl : LeafHash}
    (hA : HashAssumptions h z0 hl) {T : Chain → Tree} {c : Chain} {height : ℕ}
    {v : UInt256} {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted h hl (root h z0 hl (T c) height) v ℓ idx sibs k) :
    AbsenceWitnessAt (ofChains T) c v :=
  non_inclusion_sound hA hN

/-! ## Completeness -/

theorem inclusion_complete {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree} {height : ℕ}
    (hcap : T.leafCount ≤ 2 ^ height) {i : ℕ} (hi : i < T.leafCount) :
    InclusionAccepted h hl (root h z0 hl T height) (T.leaf i).value (T.leaf i) i
      (honestSibs h z0 (leafHashes hl T) i) height where
  valueMatch := rfl
  path := ⟨lt_of_lt_of_le hi hcap, by
    have := honest_walk_root h z0 (leafHashes hl T) height i (lt_of_lt_of_le hi hcap)
    rw [leafHashes_getD hi] at this
    exact this⟩

theorem non_inclusion_complete {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    (hV : Valid T) {height : ℕ} (hcap : T.leafCount ≤ 2 ^ height)
    {v : UInt256} (hv : v ≠ 0) (habs : v ∉ keys (toAbs T)) :
    ∃ (ℓ : Leaf) (idx : ℕ),
      NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx
        (honestSibs h z0 (leafHashes hl T) idx) height := by
  obtain ⟨_, _, hnc, hwp⟩ := hV.absSound
  have hbelow : ∃ X ∈ toAbs T, X.key < v :=
    ⟨⟨(T.leaf 0).value, (T.leaf 0).nextValue⟩,
     mem_toAbs.mpr ⟨0, hV.occupied, rfl, rfl⟩,
     by show (T.leaf 0).value < v; rw [hV.sentinel]; exact Fin.pos_of_ne_zero hv⟩
  obtain ⟨W, hW, hlow, hwin⟩ := gap_witness_exists hnc hwp hbelow habs
  obtain ⟨i, hi, hval, hnext⟩ := mem_toAbs.mp hW
  refine ⟨T.leaf i, i, hv, by rw [hval]; exact hlow, by rw [hnext]; exact hwin,
    ⟨lt_of_lt_of_le hi hcap, ?_⟩⟩
  have := honest_walk_root h z0 (leafHashes hl T) height i (lt_of_lt_of_le hi hcap)
  rw [leafHashes_getD hi] at this
  exact this

/-! ## The padding countermodel -/

theorem padding_collision_forges_absence (h : Hash) (hl : LeafHash) (T : Tree) (height : ℕ)
    (hpad : T.leafCount < 2 ^ height) (v : UInt256) (hv : 0 < v) :
    NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ⟨0, 0, 0⟩ T.leafCount
      (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl T) T.leafCount) height where
  nonzero := (ne_of_lt hv).symm
  lowBelow := hv
  window := Or.inl rfl
  path := ⟨hpad,
    padded_slot_verifies h (hl ⟨0, 0, 0⟩) (leafHashes hl T) height T.leafCount
      (le_of_eq leafHashes_length) hpad⟩

theorem threeLeafTree_guards {a b : UInt256} (ha : 0 < a) (hab : a < b) :
    InsertGuard setup a 0 ∧ InsertGuard (insert setup a 0) b 1 := by
  refine ⟨setup_insertGuard ha,
          ⟨?_, (ne_of_lt (lt_trans ha hab)).symm, ?_, ?_, ?_, ?_⟩⟩
  · show (1 : ℕ) + 1 ≠ 0; omega
  · rw [insert_vti_other (ne_of_gt hab)]; rfl
  · show (1 : ℕ) < 1 + 1; omega
  · simp [insert, setup]; exact hab
  · left; simp [insert, setup]

theorem padding_collision_refunds_delivered_leg (h : Hash) (hl : LeafHash) {a b : UInt256}
    (ha : 0 < a) (hab : a < b) :
    Valid (threeLeafTree a b)
      ∧ a ∈ keys (toAbs (threeLeafTree a b))
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  have hV1 := insert_preserves_valid setup_valid hg1
  refine ⟨insert_preserves_valid hV1 hg2, ?_, ?_⟩
  · show a ∈ keys (toAbs (insert (insert setup a 0) b 1))
    rw [(insert_sound_step hV1 hg2).2, (insert_sound_step setup_valid hg1).2]
    simp
  · have hcount : (threeLeafTree a b).leafCount = 3 := rfl
    have := padding_collision_forges_absence h hl (threeLeafTree a b) 2
      (by rw [hcount]; norm_num) a ha
    rw [hcount] at this
    exact this

/-! ## Soundness without hash premises: the property, or a located break -/

theorem accepted_path_pins_leaf_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    {height : ℕ} {sibs : ℕ → UInt256} {k idx : ℕ} {ℓ : Leaf}
    (hp : PathAccepts h (root h z0 hl T height) sibs k idx (hl ℓ)) :
    (k = height ∧ idx < T.leafCount ∧ T.leaf idx = ℓ)
      ∨ TreeRootBreak h z0 hl T height sibs k idx ℓ := by
  rcases accept_pins_entry_any_length_or_break h z0 (leafHashes hl T) sibs k height idx (hl ℓ)
      hp.inBounds hp.recompute with ⟨hk, hget⟩ | ⟨hk, hc⟩ | hb
  · by_cases hidx : idx < T.leafCount
    · rw [leafHashes_getD hidx] at hget
      by_cases hle : T.leaf idx = ℓ
      · exact Or.inl ⟨hk, hidx, hle⟩
      · exact Or.inr (TreeRootBreak.leafCollision hidx hle hget)
    · rw [getD_default _ _ _ (by rw [leafHashes_length]; omega)] at hget
      exact Or.inr (TreeRootBreak.paddingHit (by omega) hget.symm)
  · exact Or.inr (TreeRootBreak.pathCollision hk hc)
  · exact Or.inr (TreeRootBreak.wrongLength hb)

theorem inclusion_sound_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    {height : ℕ} {v : UInt256} {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hI : InclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k) :
    v ∈ keys (toAbs T) ∨ TreeRootBreak h z0 hl T height sibs k idx ℓ := by
  rcases accepted_path_pins_leaf_or_break hI.path with ⟨_, hidx, hleaf⟩ | hb
  · exact Or.inl (Finset.mem_image.mpr
      ⟨⟨v, ℓ.nextValue⟩,
       mem_toAbs.mpr ⟨idx, hidx, by rw [hleaf]; exact hI.valueMatch, by rw [hleaf]⟩, rfl⟩)
  · exact Or.inr hb

theorem non_inclusion_sound_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    {height : ℕ} {v : UInt256} {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k) :
    (∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
      ∨ TreeRootBreak h z0 hl T height sibs k idx ℓ := by
  rcases accepted_path_pins_leaf_or_break hN.path with ⟨_, hidx, hleaf⟩ | hb
  · exact Or.inl ⟨⟨ℓ.value, ℓ.nextValue⟩,
      mem_toAbs.mpr ⟨idx, hidx, by rw [hleaf], by rw [hleaf]⟩, hN.lowBelow, hN.window⟩
  · exact Or.inr hb

theorem verified_absence_excludes_delivered_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {T : Tree} (hV : Valid T) {height : ℕ} {v : UInt256} {ℓ : Leaf} {idx : ℕ}
    {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k) :
    v ∉ keys (toAbs T) ∨ TreeRootBreak h z0 hl T height sibs k idx ℓ := by
  rcases non_inclusion_sound_or_break hN with hW | hb
  · exact Or.inl (fun hmem => present_not_reclaimable hV.absSound.1 hmem hW)
  · exact Or.inr hb

theorem proofs_exclusive_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    (hV : Valid T) {height : ℕ} {v : UInt256} {ℓ₁ ℓ₂ : Leaf} {i₁ i₂ : ℕ}
    {s₁ s₂ : ℕ → UInt256} {k₁ k₂ : ℕ}
    (hI : InclusionAccepted h hl (root h z0 hl T height) v ℓ₁ i₁ s₁ k₁)
    (hN : NonInclusionAccepted h hl (root h z0 hl T height) v ℓ₂ i₂ s₂ k₂) :
    TreeRootBreak h z0 hl T height s₁ k₁ i₁ ℓ₁ ∨ TreeRootBreak h z0 hl T height s₂ k₂ i₂ ℓ₂ := by
  rcases inclusion_sound_or_break hI with hmem | hb₁
  · rcases verified_absence_excludes_delivered_or_break hV hN with hnot | hb₂
    · exact absurd hmem hnot
    · exact Or.inr hb₂
  · exact Or.inl hb₁

theorem run_roots_exclusive_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash} {R : ℕ → Tree}
    (hR : Run R) (h0 : R 0 = setup) {n height : ℕ} {v : UInt256} {ℓ₁ ℓ₂ : Leaf} {i₁ i₂ : ℕ}
    {s₁ s₂ : ℕ → UInt256} {k₁ k₂ : ℕ}
    (hI : InclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₁ i₁ s₁ k₁)
    (hN : NonInclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₂ i₂ s₂ k₂) :
    TreeRootBreak h z0 hl (R n) height s₁ k₁ i₁ ℓ₁
      ∨ TreeRootBreak h z0 hl (R n) height s₂ k₂ i₂ ℓ₂ :=
  proofs_exclusive_or_break (run_valid hR (by rw [h0]; exact setup_valid) n) hI hN

open Contracts.Protocol in
theorem verified_absence_is_witness_or_break {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {T : Chain → Tree} {c : Chain} {height : ℕ} {v : UInt256} {ℓ : Leaf} {idx : ℕ}
    {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted h hl (root h z0 hl (T c) height) v ℓ idx sibs k) :
    AbsenceWitnessAt (ofChains T) c v ∨ TreeRootBreak h z0 hl (T c) height sibs k idx ℓ :=
  non_inclusion_sound_or_break hN

/-! ### Anti-vacuity -/

theorem honest_proof_no_break (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree)
    (height i : ℕ) (hi : i < T.leafCount) :
    ¬ TreeRootBreak h z0 hl T height (honestSibs h z0 (leafHashes hl T) i) height i (T.leaf i) := by
  intro hb
  cases hb with
  | wrongLength hh => exact heightBreak_not_tautology.1 _ _ _ _ _ _ _ hh
  | pathCollision _ hc =>
      apply honest_walk_no_collision h z0 (leafHashes hl T) height i
      rw [leafHashes_getD hi]
      exact hc
  | leafCollision _ hne _ => exact hne rfl
  | paddingHit hle _ => omega

theorem threeLeafTree_leaf_one_value (a b : UInt256) : ((threeLeafTree a b).leaf 1).value = a := by
  simp [threeLeafTree, insert, setup]

theorem proofs_exclusive_or_break_satisfiable (h : Hash) (hl : LeafHash) (a b : UInt256)
    (ha : 0 < a) (hab : a < b) :
    Valid (threeLeafTree a b)
      ∧ InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2) a
          ((threeLeafTree a b).leaf 1) 1
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 1) 2
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 := by
  obtain ⟨hV, _, hN⟩ := padding_collision_refunds_delivered_leg h hl ha hab
  refine ⟨hV, ?_, hN⟩
  have hcount : (threeLeafTree a b).leafCount = 3 := rfl
  have hI := inclusion_complete (h := h) (z0 := hl ⟨0, 0, 0⟩) (hl := hl) (T := threeLeafTree a b)
    (height := 2) (by rw [hcount]; norm_num) (i := 1) (by rw [hcount]; norm_num)
  rw [threeLeafTree_leaf_one_value] at hI
  exact hI

theorem padding_countermodel_locates_padding_hit (h : Hash) (hl : LeafHash) (a b : UInt256) :
    ¬ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2
        (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 1) 2 1
        ((threeLeafTree a b).leaf 1)
      ∧ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2
        (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩ := by
  have hcount : (threeLeafTree a b).leafCount = 3 := rfl
  exact ⟨honest_proof_no_break h _ hl _ 2 1 (by rw [hcount]; norm_num),
    TreeRootBreak.paddingHit (by rw [hcount]) rfl⟩

theorem run_roots_exclusive_or_break_satisfiable (h : Hash) (hl : LeafHash) (a b : UInt256)
    (ha : 0 < a) (hab : a < b) :
    ∃ R : ℕ → Tree, Run R ∧ R 0 = setup ∧ R 2 = threeLeafTree a b
      ∧ InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (R 2) 2) a ((R 2).leaf 1) 1
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (R 2)) 1) 2
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (R 2) 2) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (R 2)) 3) 2 := by
  obtain ⟨hg1, hg2⟩ := threeLeafTree_guards ha hab
  refine ⟨fun n => if n = 0 then setup else if n = 1 then insert setup a 0 else threeLeafTree a b,
    ?_, rfl, rfl, (proofs_exclusive_or_break_satisfiable h hl a b ha hab).2⟩
  intro n
  match n with
  | 0 => exact Or.inr ⟨a, 0, hg1, rfl⟩
  | 1 => exact Or.inr ⟨b, 1, hg2, rfl⟩
  | n + 2 => exact Or.inl (by simp)

end Contracts.InteropCommitmentTree

/-! ## Certificates -/

namespace Contracts.InteropCommitmentTree

open Contracts.InteropCommitmentTree

theorem LeafHashesInsert : Contracts.InteropCommitmentTree.Properties.LeafHashesInsert := @leafHashes_insert
theorem RootAfterUpdateLeaf : Contracts.InteropCommitmentTree.Properties.RootAfterUpdateLeaf := @root_after_updateLeaf
theorem RootAfterInsert : Contracts.InteropCommitmentTree.Properties.RootAfterInsert := @root_after_insert
theorem AcceptedPathPinsLeaf : Contracts.InteropCommitmentTree.Properties.AcceptedPathPinsLeaf := @accepted_path_pins_leaf
theorem InclusionSound : Contracts.InteropCommitmentTree.Properties.InclusionSound := @inclusion_sound
theorem NonInclusionSound : Contracts.InteropCommitmentTree.Properties.NonInclusionSound := @non_inclusion_sound
theorem VerifiedAbsenceExcludesDelivered : Contracts.InteropCommitmentTree.Properties.VerifiedAbsenceExcludesDelivered :=
  @verified_absence_excludes_delivered
theorem ProofsExclusive : Contracts.InteropCommitmentTree.Properties.ProofsExclusive := @proofs_exclusive
theorem RunRootsExclusive : Contracts.InteropCommitmentTree.Properties.RunRootsExclusive := @run_roots_exclusive
theorem VerifiedAbsenceIsWitness : Contracts.InteropCommitmentTree.Properties.VerifiedAbsenceIsWitness :=
  @verified_absence_is_witness
theorem InclusionComplete : Contracts.InteropCommitmentTree.Properties.InclusionComplete := @inclusion_complete
theorem NonInclusionComplete : Contracts.InteropCommitmentTree.Properties.NonInclusionComplete := @non_inclusion_complete
theorem PaddingCollisionForgesAbsence : Contracts.InteropCommitmentTree.Properties.PaddingCollisionForgesAbsence :=
  @padding_collision_forges_absence
theorem PaddingCollisionRefundsDeliveredLeg :
    Contracts.InteropCommitmentTree.Properties.PaddingCollisionRefundsDeliveredLeg :=
  @padding_collision_refunds_delivered_leg


/-- Pigeonhole: no `h : UInt256 → UInt256 → UInt256` is injective on pairs. -/
theorem not_nodeInj (h : MerkleSpec.Hash) : ¬ ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d := by
  intro hinj
  have hf : Function.Injective (fun p : UInt256 × UInt256 => h p.1 p.2) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ he
    obtain ⟨rfl, rfl⟩ := hinj a b c d he
    rfl
  have hc := Fintype.card_le_of_injective _ hf
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  have hpos : 1 < UInt256.size := by decide
  nlinarith

theorem HashAssumptionsUnsatisfiable : Properties.HashAssumptionsUnsatisfiable :=
  fun h _ _ hA => not_nodeInj h hA.nodeInj

theorem AcceptedPathPinsLeafOrBreak : Properties.AcceptedPathPinsLeafOrBreak :=
  @accepted_path_pins_leaf_or_break
theorem InclusionSoundOrBreak : Properties.InclusionSoundOrBreak := @inclusion_sound_or_break
theorem NonInclusionSoundOrBreak : Properties.NonInclusionSoundOrBreak :=
  @non_inclusion_sound_or_break
theorem VerifiedAbsenceExcludesDeliveredOrBreak :
    Properties.VerifiedAbsenceExcludesDeliveredOrBreak :=
  @verified_absence_excludes_delivered_or_break
theorem ProofsExclusiveOrBreak : Properties.ProofsExclusiveOrBreak := @proofs_exclusive_or_break
theorem RunRootsExclusiveOrBreak : Properties.RunRootsExclusiveOrBreak :=
  @run_roots_exclusive_or_break
theorem VerifiedAbsenceIsWitnessOrBreak : Properties.VerifiedAbsenceIsWitnessOrBreak :=
  @verified_absence_is_witness_or_break
theorem HonestProofNoBreak : Properties.HonestProofNoBreak := honest_proof_no_break
theorem ProofsExclusiveOrBreakSatisfiable : Properties.ProofsExclusiveOrBreakSatisfiable :=
  proofs_exclusive_or_break_satisfiable
theorem PaddingCountermodelLocatesPaddingHit : Properties.PaddingCountermodelLocatesPaddingHit :=
  padding_countermodel_locates_padding_hit
theorem RunRootsExclusiveOrBreakSatisfiable : Properties.RunRootsExclusiveOrBreakSatisfiable :=
  run_roots_exclusive_or_break_satisfiable

end Contracts.InteropCommitmentTree

/-! ## Every case of the break fires, and is attributed alone -/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier

theorem treeRootBreak_iff_some_case {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    {height : ℕ} {sibs : ℕ → UInt256} {k idx : ℕ} {ℓ : Leaf} :
    TreeRootBreak h z0 hl T height sibs k idx ℓ
      ↔ ∃ c, TreeRootBreakAt h z0 hl T height sibs k idx ℓ c := by
  constructor
  · intro hb
    cases hb with
    | wrongLength hh => exact ⟨.wrongLength, hh⟩
    | pathCollision hk hc => exact ⟨.pathCollision, hk, hc⟩
    | leafCollision hi hne he => exact ⟨.leafCollision, hi, hne, he⟩
    | paddingHit hle he => exact ⟨.paddingHit, hle, he⟩
  · rintro ⟨c, hc⟩
    cases c with
    | wrongLength => exact TreeRootBreak.wrongLength hc
    | pathCollision => exact TreeRootBreak.pathCollision hc.1 hc.2
    | leafCollision => exact TreeRootBreak.leafCollision hc.1 hc.2.1 hc.2.2
    | paddingHit => exact TreeRootBreak.paddingHit hc.1 hc.2

/-- To show case `c` fires alone: it fires, and every other case does not. -/
theorem treeRootBreakExactly_of {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    {height : ℕ} {sibs : ℕ → UInt256} {k idx : ℕ} {ℓ : Leaf} {c : TreeRootBreakCase}
    (hc : TreeRootBreakAt h z0 hl T height sibs k idx ℓ c)
    (hno : ∀ c', c' ≠ c → ¬ TreeRootBreakAt h z0 hl T height sibs k idx ℓ c') :
    TreeRootBreakExactly h z0 hl T height sibs k idx ℓ c := by
  intro c'
  constructor
  · intro hc'
    by_contra hne
    exact hno c' hne hc'
  · rintro rfl
    exact hc

/-- At the right length no `wrongLength` break holds. -/
theorem not_wrongLength_at_height {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    {height : ℕ} {sibs : ℕ → UInt256} {idx : ℕ} {ℓ : Leaf} :
    ¬ TreeRootBreakAt h z0 hl T height sibs height idx ℓ .wrongLength :=
  heightBreak_not_tautology.1 _ _ _ _ _ _ _

lemma setup_leafHashes (hl : LeafHash) : leafHashes hl setup = [hl ⟨0, 0, 0⟩] := rfl

lemma setup_root (h : Hash) (z0 : UInt256) (hl : LeafHash) :
    root h z0 hl setup 1 = h (hl ⟨0, 0, 0⟩) z0 := rfl

lemma setup_leaf_eq_value {i : ℕ} {ℓ : Leaf} (he : setup.leaf i = ℓ) : ℓ.value = 0 := by
  rw [← he]; rfl

lemma not_mem_keys_setup {v : UInt256} (hv : v ≠ 0) : v ∉ keys (toAbs setup) := by
  rw [toAbs_setup]
  intro hmem
  obtain ⟨X, hX, hXv⟩ := Finset.mem_image.mp hmem
  rw [Finset.mem_singleton] at hX
  subst hX
  exact hv (hXv : (0 : UInt256) = v).symm

lemma setup_capacity : setup.leafCount ≤ 2 ^ 1 := by norm_num [setup]

theorem path_collision_forges_inclusion (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf)
    (s : UInt256) (hv : ℓ.value ≠ 0) (hne : hl ℓ ≠ hl ⟨0, 0, 0⟩)
    (hc : h (hl ℓ) s = h (hl ⟨0, 0, 0⟩) z0) :
    Valid setup ∧ setup.leafCount ≤ 2 ^ 1
      ∧ InclusionAccepted h hl (root h z0 hl setup 1) ℓ.value ℓ 0 (fun _ => s) 1
      ∧ ℓ.value ∉ keys (toAbs setup)
      ∧ TreeRootBreakExactly h z0 hl setup 1 (fun _ => s) 1 0 ℓ .pathCollision := by
  refine ⟨setup_valid, setup_capacity, ⟨rfl, by norm_num, ?_⟩, not_mem_keys_setup hv, ?_⟩
  · show h (hl ℓ) s = root h z0 hl setup 1
    rw [setup_root]; exact hc
  · refine treeRootBreakExactly_of ⟨rfl, 0, by norm_num, ?_, ?_⟩ ?_
    · show (hl ℓ, s) ≠ (hl ⟨0, 0, 0⟩, z0)
      intro hp; exact hne (congrArg Prod.fst hp)
    · exact hc
    · intro c' hc'
      cases c' with
      | wrongLength => exact not_wrongLength_at_height
      | pathCollision => exact absurd rfl hc'
      | leafCollision =>
          rintro ⟨_, _, he⟩
          exact hne he.symm
      | paddingHit =>
          rintro ⟨hle, _⟩
          exact absurd hle (by norm_num [setup])

theorem leaf_collision_forges_inclusion (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf)
    (hv : ℓ.value ≠ 0) (he : hl ℓ = hl ⟨0, 0, 0⟩) :
    Valid setup ∧ setup.leafCount ≤ 2 ^ 1
      ∧ InclusionAccepted h hl (root h z0 hl setup 1) ℓ.value ℓ 0
          (honestSibs h z0 (leafHashes hl setup) 0) 1
      ∧ ℓ.value ∉ keys (toAbs setup)
      ∧ TreeRootBreakExactly h z0 hl setup 1 (honestSibs h z0 (leafHashes hl setup) 0) 1 0 ℓ
          .leafCollision := by
  have hget : (leafHashes hl setup).getD 0 z0 = hl ℓ := by rw [setup_leafHashes, he]; rfl
  refine ⟨setup_valid, setup_capacity, ⟨rfl, by norm_num, ?_⟩, not_mem_keys_setup hv, ?_⟩
  · have := honest_walk_root h z0 (leafHashes hl setup) 1 0 (by norm_num)
    rw [hget] at this
    exact this
  · refine treeRootBreakExactly_of ⟨by norm_num [setup], fun hl0 => hv (setup_leaf_eq_value hl0),
      he.symm⟩ ?_
    intro c' hc'
    cases c' with
    | wrongLength => exact not_wrongLength_at_height
    | pathCollision =>
        rintro ⟨_, hpc⟩
        apply honest_walk_no_collision h z0 (leafHashes hl setup) 1 0
        rw [hget]; exact hpc
    | leafCollision => exact absurd rfl hc'
    | paddingHit =>
        rintro ⟨hle, _⟩
        exact absurd hle (by norm_num [setup])

theorem wrong_length_forges_inclusion (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf)
    (sibs : ℕ → UInt256) (hv : ℓ.value ≠ 0) (hne : hl ℓ ≠ hl ⟨0, 0, 0⟩)
    (hr : hl ℓ = root h z0 hl setup 1) :
    Valid setup ∧ setup.leafCount ≤ 2 ^ 1
      ∧ InclusionAccepted h hl (root h z0 hl setup 1) ℓ.value ℓ 0 sibs 0
      ∧ ℓ.value ∉ keys (toAbs setup)
      ∧ TreeRootBreakExactly h z0 hl setup 1 sibs 0 0 ℓ .wrongLength := by
  refine ⟨setup_valid, setup_capacity, ⟨rfl, by norm_num, hr⟩, not_mem_keys_setup hv, ?_⟩
  refine treeRootBreakExactly_of ?_ ?_
  · show HeightBreak h z0 (leafHashes hl setup) sibs 0 1 0 (hl ℓ)
    have := (zero_length_path_accepts_root h z0 (leafHashes hl setup) sibs 1 (by norm_num)).2
    rw [hr]; exact this
  · intro c' hc'
    cases c' with
    | wrongLength => exact absurd rfl hc'
    | pathCollision =>
        rintro ⟨hk, _⟩
        exact absurd hk (by norm_num)
    | leafCollision =>
        rintro ⟨_, _, he⟩
        exact hne he.symm
    | paddingHit =>
        rintro ⟨hle, _⟩
        exact absurd hle (by norm_num [setup])

theorem padding_hit_forges_inclusion (h : Hash) (z0 : UInt256) (hl : LeafHash) (ℓ : Leaf)
    (hv : ℓ.value ≠ 0) (hz : hl ℓ = z0) :
    Valid setup ∧ setup.leafCount ≤ 2 ^ 1
      ∧ InclusionAccepted h hl (root h z0 hl setup 1) ℓ.value ℓ 1
          (honestSibs h z0 (leafHashes hl setup) 1) 1
      ∧ ℓ.value ∉ keys (toAbs setup)
      ∧ TreeRootBreakExactly h z0 hl setup 1 (honestSibs h z0 (leafHashes hl setup) 1) 1 1 ℓ
          .paddingHit := by
  have hget : (leafHashes hl setup).getD 1 z0 = hl ℓ := by
    rw [getD_default _ _ _ (by rw [leafHashes_length]; rfl), hz]
  refine ⟨setup_valid, setup_capacity, ⟨rfl, by norm_num, ?_⟩, not_mem_keys_setup hv, ?_⟩
  · have := honest_walk_root h z0 (leafHashes hl setup) 1 1 (by norm_num)
    rw [hget] at this
    exact this
  · refine treeRootBreakExactly_of ⟨le_refl _, hz⟩ ?_
    intro c' hc'
    cases c' with
    | wrongLength => exact not_wrongLength_at_height
    | pathCollision =>
        rintro ⟨_, hpc⟩
        apply honest_walk_no_collision h z0 (leafHashes hl setup) 1 1
        rw [hget]; exact hpc
    | leafCollision =>
        rintro ⟨hlt, _⟩
        exact absurd hlt (by norm_num [setup])
    | paddingHit => exact absurd rfl hc'

theorem padding_countermodel_exactly_padding_hit (h : Hash) (hl : LeafHash) (a b : UInt256) :
    TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2
      (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩
      .paddingHit := by
  have hcount : (threeLeafTree a b).leafCount = 3 := rfl
  have hget : (leafHashes hl (threeLeafTree a b)).getD 3 (hl ⟨0, 0, 0⟩) = hl ⟨0, 0, 0⟩ :=
    getD_default _ _ _ (by rw [leafHashes_length, hcount])
  refine treeRootBreakExactly_of ⟨by rw [hcount], rfl⟩ ?_
  intro c' hc'
  cases c' with
  | wrongLength => exact not_wrongLength_at_height
  | pathCollision =>
      rintro ⟨_, hpc⟩
      apply honest_walk_no_collision h _ (leafHashes hl (threeLeafTree a b)) 2 3
      rw [hget]; exact hpc
  | leafCollision =>
      rintro ⟨hlt, _⟩
      rw [hcount] at hlt
      exact absurd hlt (lt_irrefl 3)
  | paddingHit => exact absurd rfl hc'

theorem forged_inclusion_premises_satisfiable :
    ((⟨1, 0, 0⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨1, 0, 0⟩ ≠ toyLeafHash ⟨0, 0, 0⟩
        ∧ toyNodeHash (toyLeafHash ⟨1, 0, 0⟩) 0 = toyNodeHash (toyLeafHash ⟨0, 0, 0⟩) 1)
      ∧ ((⟨1, 0, 1⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨1, 0, 1⟩ = toyLeafHash ⟨0, 0, 0⟩)
      ∧ ((⟨1, 0, 0⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨1, 0, 0⟩ ≠ toyLeafHash ⟨0, 0, 0⟩
        ∧ toyLeafHash ⟨1, 0, 0⟩ = root toyNodeHash 1 toyLeafHash setup 1)
      ∧ ((⟨1, 0, 0⟩ : Leaf).value ≠ 0 ∧ toyLeafHash ⟨1, 0, 0⟩ = 1) := by
  rw [setup_root]
  simp only [toyLeafHash, toyNodeHash]
  decide

theorem tree_root_break_every_case_fires (c : TreeRootBreakCase) :
    ∃ (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf),
      Valid setup ∧ setup.leafCount ≤ 2 ^ 1
        ∧ InclusionAccepted toyNodeHash toyLeafHash (root toyNodeHash 1 toyLeafHash setup 1)
            ℓ.value ℓ idx sibs k
        ∧ ℓ.value ∉ keys (toAbs setup)
        ∧ ¬ (k = 1 ∧ idx < setup.leafCount ∧ setup.leaf idx = ℓ)
        ∧ TreeRootBreakExactly toyNodeHash 1 toyLeafHash setup 1 sibs k idx ℓ c := by
  obtain ⟨⟨hv1, hne1, hc1⟩, ⟨hv2, he2⟩, ⟨hv3, hne3, hr3⟩, ⟨hv4, hz4⟩⟩ :=
    forged_inclusion_premises_satisfiable
  have wrong : ∀ {i : ℕ} {ℓ : Leaf} {k : ℕ}, ℓ.value ≠ 0 →
      ¬ (k = 1 ∧ i < setup.leafCount ∧ setup.leaf i = ℓ) :=
    fun hv ⟨_, _, he⟩ => hv (setup_leaf_eq_value he)
  cases c with
  | wrongLength =>
      obtain ⟨hV, hcap, hI, hk, hx⟩ :=
        wrong_length_forges_inclusion toyNodeHash 1 toyLeafHash ⟨1, 0, 0⟩ (fun _ => 0) hv3 hne3 hr3
      exact ⟨_, _, _, _, hV, hcap, hI, hk, wrong hv3, hx⟩
  | pathCollision =>
      obtain ⟨hV, hcap, hI, hk, hx⟩ :=
        path_collision_forges_inclusion toyNodeHash 1 toyLeafHash ⟨1, 0, 0⟩ 0 hv1 hne1 hc1
      exact ⟨_, _, _, _, hV, hcap, hI, hk, wrong hv1, hx⟩
  | leafCollision =>
      obtain ⟨hV, hcap, hI, hk, hx⟩ :=
        leaf_collision_forges_inclusion toyNodeHash 1 toyLeafHash ⟨1, 0, 1⟩ hv2 he2
      exact ⟨_, _, _, _, hV, hcap, hI, hk, wrong hv2, hx⟩
  | paddingHit =>
      obtain ⟨hV, hcap, hI, hk, hx⟩ :=
        padding_hit_forges_inclusion toyNodeHash 1 toyLeafHash ⟨1, 0, 0⟩ hv4 hz4
      exact ⟨_, _, _, _, hV, hcap, hI, hk, wrong hv4, hx⟩

theorem TreeRootBreakIffSomeCase : Properties.TreeRootBreakIffSomeCase :=
  @treeRootBreak_iff_some_case
theorem PathCollisionForgesInclusion : Properties.PathCollisionForgesInclusion :=
  path_collision_forges_inclusion
theorem LeafCollisionForgesInclusion : Properties.LeafCollisionForgesInclusion :=
  leaf_collision_forges_inclusion
theorem WrongLengthForgesInclusion : Properties.WrongLengthForgesInclusion :=
  wrong_length_forges_inclusion
theorem PaddingHitForgesInclusion : Properties.PaddingHitForgesInclusion :=
  padding_hit_forges_inclusion
theorem PaddingCountermodelExactlyPaddingHit : Properties.PaddingCountermodelExactlyPaddingHit :=
  padding_countermodel_exactly_padding_hit
theorem ForgedInclusionPremisesSatisfiable : Properties.ForgedInclusionPremisesSatisfiable :=
  forged_inclusion_premises_satisfiable
theorem TreeRootBreakEveryCaseFires : Properties.TreeRootBreakEveryCaseFires :=
  tree_root_break_every_case_fires

end Contracts.InteropCommitmentTree
