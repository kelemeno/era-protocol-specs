import EraSpec.Properties.TreeRoot
import EraSpec.Proofs.InteropCommitmentTree

/-!
# Proofs: the root and the two proof gates

Proofs of `EraSpec.Properties.TreeRoot`.  The Merkle content is
`EraSpec.Core.MerkleVerifier` (an accepted walk pins the level-0 entry at any
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
  refine ⟨⟨?_, (ne_of_lt ha).symm, rfl, ?_, ha, Or.inl rfl⟩,
          ⟨?_, (ne_of_lt (lt_trans ha hab)).symm, ?_, ?_, ?_, ?_⟩⟩
  · show (1 : ℕ) ≠ 0; omega
  · show (0 : ℕ) < 1; omega
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

end Contracts.InteropCommitmentTree

/-! ## Certificates -/

namespace Proofs.TreeRoot

open Contracts.InteropCommitmentTree

theorem LeafHashesInsert : Properties.TreeRoot.LeafHashesInsert := @leafHashes_insert
theorem RootAfterUpdateLeaf : Properties.TreeRoot.RootAfterUpdateLeaf := @root_after_updateLeaf
theorem RootAfterInsert : Properties.TreeRoot.RootAfterInsert := @root_after_insert
theorem AcceptedPathPinsLeaf : Properties.TreeRoot.AcceptedPathPinsLeaf := @accepted_path_pins_leaf
theorem InclusionSound : Properties.TreeRoot.InclusionSound := @inclusion_sound
theorem NonInclusionSound : Properties.TreeRoot.NonInclusionSound := @non_inclusion_sound
theorem VerifiedAbsenceExcludesDelivered : Properties.TreeRoot.VerifiedAbsenceExcludesDelivered :=
  @verified_absence_excludes_delivered
theorem ProofsExclusive : Properties.TreeRoot.ProofsExclusive := @proofs_exclusive
theorem RunRootsExclusive : Properties.TreeRoot.RunRootsExclusive := @run_roots_exclusive
theorem VerifiedAbsenceIsWitness : Properties.TreeRoot.VerifiedAbsenceIsWitness :=
  @verified_absence_is_witness
theorem InclusionComplete : Properties.TreeRoot.InclusionComplete := @inclusion_complete
theorem NonInclusionComplete : Properties.TreeRoot.NonInclusionComplete := @non_inclusion_complete
theorem PaddingCollisionForgesAbsence : Properties.TreeRoot.PaddingCollisionForgesAbsence :=
  @padding_collision_forges_absence
theorem PaddingCollisionRefundsDeliveredLeg :
    Properties.TreeRoot.PaddingCollisionRefundsDeliveredLeg :=
  @padding_collision_refunds_delivered_leg

end Proofs.TreeRoot
