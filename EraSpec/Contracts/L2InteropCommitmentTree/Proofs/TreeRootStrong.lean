import EraSpec.Contracts.L2InteropCommitmentTree.Properties.TreeRootStrong
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight

/-!
# Proofs: the seven soundness results under the pinned hash premise

Proofs of `EraSpec.Contracts.L2InteropCommitmentTree.Properties.TreeRootStrong`.

The engine is `treeRootStrong_no_break`. Each case of `TreeRootBreak` on an accepted path
names either two pairs with one node hash, one from the walk log and one from the tree
log, or a value that one field of `TreeRootStrongLogSafe` keeps apart from another. The
work is locating those pairs in the logs: a re-anchored walk (short path) or a split
walk (long path) hashes the same pairs as the submitted walk, at shifted step numbers
(`treeRootStrong_walkPair_congr`, `treeRootStrong_walkPair_add`), and every tree pair the
break names sits under a parent inside the tree's range (`treeRootStrong_parent_lt`). The
seven results then follow from the `…OrBreak` theorems of `Proofs/TreeRoot.lean`.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier

/-! ## Walk pairs under a shifted stream and a split walk -/

/-- The pairs a walk hashes depend only on the siblings it reads: two streams that agree
on the levels the walk visits give the same pair at every step. -/
theorem treeRootStrong_walkPair_congr (h : Hash) (s₁ s₂ : ℕ → UInt256) :
    ∀ (i lvl₁ lvl₂ j : ℕ) (x : UInt256), (∀ t ≤ i, s₁ (lvl₁ + t) = s₂ (lvl₂ + t)) →
      walkPair h s₁ lvl₁ j x i = walkPair h s₂ lvl₂ j x i := by
  intro i
  induction i with
  | zero =>
    intro lvl₁ lvl₂ j x hs
    have h0 := hs 0 le_rfl
    simp only [Nat.add_zero] at h0
    simp only [walkPair, walkStep, h0]
  | succ i ih =>
    intro lvl₁ lvl₂ j x hs
    have h0 := hs 0 (Nat.zero_le _)
    simp only [Nat.add_zero] at h0
    have hstep : walkStep s₁ lvl₁ j x = walkStep s₂ lvl₂ j x := by
      simp only [walkStep, h0]
    rw [walkPair_succ, walkPair_succ, hstep]
    apply ih
    intro t ht
    have := hs (t + 1) (by omega)
    rw [show lvl₁ + (t + 1) = lvl₁ + 1 + t by omega,
      show lvl₂ + (t + 1) = lvl₂ + 1 + t by omega] at this
    exact this

/-- A walk's pair at step `d + i` is the pair at step `i` of the walk restarted after its
first `d` steps. -/
theorem treeRootStrong_walkPair_add (h : Hash) (sibs : ℕ → UInt256) :
    ∀ (d lvl j : ℕ) (x : UInt256) (i : ℕ),
      walkPair h sibs lvl j x (d + i)
        = walkPair h sibs (lvl + d) (j / 2 ^ d) (walkPure h sibs lvl d j x) i := by
  intro d
  induction d with
  | zero => intro lvl j x i; simp
  | succ d ih =>
    intro lvl j x i
    rw [show d + 1 + i = (d + i) + 1 by omega, walkPair_succ, ih, walkPure_succ,
      ← walkStep_hash, show lvl + 1 + d = lvl + (d + 1) by omega, Nat.div_div_eq_div_mul,
      ← pow_succ']

/-! ## The logs -/

lemma treeRootStrong_mem_walkLog {h : Hash} {sibs : ℕ → UInt256} {k idx : ℕ} {x : UInt256}
    {i : ℕ} (hi : i < k) :
    walkPair h sibs 0 idx x i ∈ treeRootStrongWalkLog h sibs k idx x :=
  Finset.mem_image_of_mem _ (Finset.mem_range.mpr hi)

lemma treeRootStrong_mem_walkLog_iff {h : Hash} {sibs : ℕ → UInt256} {k idx : ℕ} {x : UInt256}
    {p : UInt256 × UInt256} :
    p ∈ treeRootStrongWalkLog h sibs k idx x ↔ ∃ i < k, walkPair h sibs 0 idx x i = p := by
  simp [treeRootStrongWalkLog]

/-- `treePair` reads only the parent index. -/
lemma treeRootStrong_treePair_parent (h : Hash) (z0 : UInt256) (L : List UInt256) (l j : ℕ) :
    treePair h z0 L l (2 * (j / 2)) = treePair h z0 L l j := by
  simp only [treePair]
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

lemma treeRootStrong_mem_treeLog {h : Hash} {z0 : UInt256} {L : List UInt256} {height l j : ℕ}
    (hl : l < height) (hj : j / 2 < 2 ^ (height - l - 1)) :
    treePair h z0 L l j ∈ treeRootStrongTreeLog h z0 L height := by
  unfold treeRootStrongTreeLog
  rw [Finset.mem_biUnion]
  exact ⟨l, Finset.mem_range.mpr hl,
    Finset.mem_image.mpr ⟨j / 2, Finset.mem_range.mpr hj, treeRootStrong_treePair_parent h z0 L l j⟩⟩

lemma treeRootStrong_mem_treeLog_iff {h : Hash} {z0 : UInt256} {L : List UInt256} {height : ℕ}
    {p : UInt256 × UInt256} :
    p ∈ treeRootStrongTreeLog h z0 L height
      ↔ ∃ l < height, ∃ m < 2 ^ (height - l - 1), treePair h z0 L l (2 * m) = p := by
  simp [treeRootStrongTreeLog]

/-- The parent of the level-`i` ancestor of an index below `2 ^ n` is below
`2 ^ (n - i - 1)`. -/
lemma treeRootStrong_parent_lt {j n i : ℕ} (hj : j < 2 ^ n) (hi : i < n) :
    j / 2 ^ i / 2 < 2 ^ (n - i - 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity), ← pow_succ, ← pow_add,
    show n - i - 1 + (i + 1) = n by omega]
  exact hj

/-- A level-0 entry is the padding constant or a member of the list. -/
lemma treeRootStrong_getD_mem_cons (L : List UInt256) (n : ℕ) (d : UInt256) :
    L.getD n d ∈ d :: L := by
  by_cases hn : n < L.length
  · exact List.mem_cons_of_mem _ (getD_mem L n d hn)
  · rw [getD_default L n d (by omega)]
    exact List.mem_cons_self

/-! ## The engine -/

/-- **A SAFE LOG LOCATES NO BREAK.** -/
theorem treeRootStrong_no_break {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    {height : ℕ} {sibs : ℕ → UInt256} {k idx : ℕ} {ℓ : Leaf}
    (hp : PathAccepts h (root h z0 hl T height) sibs k idx (hl ℓ))
    (hs : TreeRootStrongLogSafe h z0 hl T height sibs k idx ℓ) :
    ¬ TreeRootBreak h z0 hl T height sibs k idx ℓ := by
  have hj : idx < 2 ^ k := hp.inBounds
  -- A walk pair and a tree pair that differ cannot share a node hash.
  have hsep : ∀ p ∈ treeRootStrongWalkLog h sibs k idx (hl ℓ),
      ∀ q ∈ treeRootStrongTreeLog h z0 (leafHashes hl T) height,
        p ≠ q → h p.1 p.2 = h q.1 q.2 → False :=
    fun p hp' q hq hne he =>
      hne (hs.nodeInjOn p (Finset.mem_union_left _ hp') q (Finset.mem_union_right _ hq) he)
  intro hb
  cases hb with
  | wrongLength hh =>
    cases hh with
    | shortInteriorLeaf hlt he =>
      refine hs.shortSeparated hlt _ (treeRootStrong_mem_treeLog (by omega) ?_) he
      rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2),
        show height - (height - k - 1) - 1 = k by omega]
      exact hj
    | shortCollision hlt hc =>
      obtain ⟨i, hi, hne, heq⟩ := hc
      have hw : walkPair h (fun l => sibs (l - (height - k))) (height - k) idx (hl ℓ) i
          = walkPair h sibs 0 idx (hl ℓ) i :=
        treeRootStrong_walkPair_congr h _ _ i (height - k) 0 idx (hl ℓ) (fun t _ => by simp)
      rw [hw] at hne heq
      refine hsep _ (treeRootStrong_mem_walkLog hi) _ (treeRootStrong_mem_treeLog (by omega) ?_)
        hne heq
      rw [show height - (height - k + i) - 1 = k - i - 1 by omega]
      exact treeRootStrong_parent_lt hj hi
    | longEntryIsNode hlt he =>
      exact hs.longSeparated hlt _ (treeRootStrong_mem_walkLog (by omega)) _
        (treeRootStrong_getD_mem_cons _ _ _) he
    | longCollision hlt hc =>
      obtain ⟨i, hi, hne, heq⟩ := hc
      have hw : walkPair h (fun l => sibs (l + (k - height))) 0 (idx / 2 ^ (k - height))
          (walkPure h sibs 0 (k - height) idx (hl ℓ)) i
            = walkPair h sibs 0 idx (hl ℓ) ((k - height) + i) := by
        rw [treeRootStrong_walkPair_add h sibs (k - height) 0 idx (hl ℓ) i, Nat.zero_add]
        exact treeRootStrong_walkPair_congr h _ _ i 0 (k - height) _ _
          (fun t _ => by simp only [Nat.zero_add]; rw [Nat.add_comm])
      rw [hw] at hne heq
      refine hsep _ (treeRootStrong_mem_walkLog (by omega)) _
        (treeRootStrong_mem_treeLog (by omega) ?_) hne heq
      have hj' : idx / 2 ^ (k - height) < 2 ^ height := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add,
          show height + (k - height) = k by omega]
        exact hj
      rw [Nat.zero_add]
      exact treeRootStrong_parent_lt hj' hi
  | pathCollision hk hc =>
    obtain ⟨i, hi, hne, heq⟩ := hc
    refine hsep _ (treeRootStrong_mem_walkLog hi) _ (treeRootStrong_mem_treeLog (by omega) ?_)
      hne heq
    rw [Nat.zero_add]
    exact treeRootStrong_parent_lt (by rw [← hk]; exact hj) (by omega)
  | leafCollision hi hne he => exact hne (hs.openedLeafInj hi he)
  | paddingHit hle he => exact hs.padNotPresented hle he

/-! ## The log is bounded -/

lemma treeRootStrong_sum_pow_two (n : ℕ) : ∑ l ∈ Finset.range n, 2 ^ l + 1 = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, pow_succ]; omega

theorem treeRootStrong_treeLog_card (h : Hash) (z0 : UInt256) (L : List UInt256) (height : ℕ) :
    (treeRootStrongTreeLog h z0 L height).card + 1 ≤ 2 ^ height := by
  have hle : (treeRootStrongTreeLog h z0 L height).card
      ≤ ∑ l ∈ Finset.range height, 2 ^ (height - 1 - l) := by
    unfold treeRootStrongTreeLog
    refine le_trans Finset.card_biUnion_le (Finset.sum_le_sum fun l _ => ?_)
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_range, show height - l - 1 = height - 1 - l by omega]
  rw [Finset.sum_range_reflect (fun l => 2 ^ l) height] at hle
  have := treeRootStrong_sum_pow_two height
  omega

theorem treeRootStrong_log_bounded (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree)
    (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) :
    (treeRootStrongWalkLog h sibs k idx (hl ℓ)
      ∪ treeRootStrongTreeLog h z0 (leafHashes hl T) height).card ≤ k + 2 ^ height := by
  have hw : (treeRootStrongWalkLog h sibs k idx (hl ℓ)).card ≤ k := by
    unfold treeRootStrongWalkLog
    exact le_trans Finset.card_image_le (by rw [Finset.card_range])
  have ht := treeRootStrong_treeLog_card h z0 (leafHashes hl T) height
  have hu := Finset.card_union_le (treeRootStrongWalkLog h sibs k idx (hl ℓ))
    (treeRootStrongTreeLog h z0 (leafHashes hl T) height)
  omega

/-! ## The seven results -/

theorem treeRootStrong_accepted_path_pins_leaf {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {T : Tree} {height : ℕ} {sibs : ℕ → UInt256} {k idx : ℕ} {ℓ : Leaf}
    (hp : PathAccepts h (root h z0 hl T height) sibs k idx (hl ℓ))
    (hs : TreeRootStrongLogSafe h z0 hl T height sibs k idx ℓ) :
    k = height ∧ idx < T.leafCount ∧ T.leaf idx = ℓ :=
  (accepted_path_pins_leaf_or_break hp).resolve_right (treeRootStrong_no_break hp hs)

theorem treeRootStrong_inclusion_sound {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    {height : ℕ} {v : UInt256} {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hI : InclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k)
    (hs : TreeRootStrongLogSafe h z0 hl T height sibs k idx ℓ) :
    v ∈ keys (toAbs T) :=
  (inclusion_sound_or_break hI).resolve_right (treeRootStrong_no_break hI.path hs)

theorem treeRootStrong_non_inclusion_sound {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    {height : ℕ} {v : UInt256} {ℓ : Leaf} {idx : ℕ} {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k)
    (hs : TreeRootStrongLogSafe h z0 hl T height sibs k idx ℓ) :
    ∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey) :=
  (non_inclusion_sound_or_break hN).resolve_right (treeRootStrong_no_break hN.path hs)

theorem treeRootStrong_verified_absence_excludes_delivered {h : Hash} {z0 : UInt256}
    {hl : LeafHash} {T : Tree} (hV : Valid T) {height : ℕ} {v : UInt256} {ℓ : Leaf} {idx : ℕ}
    {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k)
    (hs : TreeRootStrongLogSafe h z0 hl T height sibs k idx ℓ) :
    v ∉ keys (toAbs T) :=
  (verified_absence_excludes_delivered_or_break hV hN).resolve_right
    (treeRootStrong_no_break hN.path hs)

theorem treeRootStrong_proofs_exclusive {h : Hash} {z0 : UInt256} {hl : LeafHash} {T : Tree}
    (hV : Valid T) {height : ℕ} {v : UInt256} {ℓ₁ ℓ₂ : Leaf} {i₁ i₂ : ℕ}
    {s₁ s₂ : ℕ → UInt256} {k₁ k₂ : ℕ}
    (hs₁ : TreeRootStrongLogSafe h z0 hl T height s₁ k₁ i₁ ℓ₁)
    (hs₂ : TreeRootStrongLogSafe h z0 hl T height s₂ k₂ i₂ ℓ₂) :
    ¬ (InclusionAccepted h hl (root h z0 hl T height) v ℓ₁ i₁ s₁ k₁
        ∧ NonInclusionAccepted h hl (root h z0 hl T height) v ℓ₂ i₂ s₂ k₂) := by
  rintro ⟨hI, hN⟩
  rcases proofs_exclusive_or_break hV hI hN with hb | hb
  · exact treeRootStrong_no_break hI.path hs₁ hb
  · exact treeRootStrong_no_break hN.path hs₂ hb

theorem treeRootStrong_run_roots_exclusive {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {R : ℕ → Tree} (hR : Run R) (h0 : R 0 = setup) {n height : ℕ} {v : UInt256}
    {ℓ₁ ℓ₂ : Leaf} {i₁ i₂ : ℕ} {s₁ s₂ : ℕ → UInt256} {k₁ k₂ : ℕ}
    (hs₁ : TreeRootStrongLogSafe h z0 hl (R n) height s₁ k₁ i₁ ℓ₁)
    (hs₂ : TreeRootStrongLogSafe h z0 hl (R n) height s₂ k₂ i₂ ℓ₂) :
    ¬ (InclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₁ i₁ s₁ k₁
        ∧ NonInclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₂ i₂ s₂ k₂) :=
  treeRootStrong_proofs_exclusive (run_valid hR (by rw [h0]; exact setup_valid) n) hs₁ hs₂

open Contracts.Protocol in
theorem treeRootStrong_verified_absence_is_witness {h : Hash} {z0 : UInt256} {hl : LeafHash}
    {T : Chain → Tree} {c : Chain} {height : ℕ} {v : UInt256} {ℓ : Leaf} {idx : ℕ}
    {sibs : ℕ → UInt256} {k : ℕ}
    (hN : NonInclusionAccepted h hl (root h z0 hl (T c) height) v ℓ idx sibs k)
    (hs : TreeRootStrongLogSafe h z0 hl (T c) height sibs k idx ℓ) :
    AbsenceWitnessAt (ofChains T) c v :=
  (verified_absence_is_witness_or_break hN).resolve_right (treeRootStrong_no_break hN.path hs)

/-! ## Honest proofs -/

/-- The honest sibling stream of any slot within capacity, presenting that slot's level-0
entry, hashes only pairs of the tree's own log. -/
theorem treeRootStrong_honest_walkLog_subset (h : Hash) (z0 : UInt256) (L : List UInt256)
    (height j : ℕ) (hj : j < 2 ^ height) :
    treeRootStrongWalkLog h (honestSibs h z0 L j) height j (L.getD j z0)
      ⊆ treeRootStrongTreeLog h z0 L height := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := treeRootStrong_mem_walkLog_iff.mp hp
  have hw : walkPair h (honestSibs h z0 L j) 0 j (L.getD j z0) i
      = treePair h z0 L (0 + i) (j / 2 ^ i) :=
    walkPair_honest h z0 L _ i 0 j _ (fun l _ _ => by simp [honestSibs]) (by simp)
  rw [hw]
  exact treeRootStrong_mem_treeLog (by omega) (by rw [Nat.zero_add]; exact treeRootStrong_parent_lt hj hi)

theorem treeRootStrong_honest_logSafe_iff (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree)
    (height i : ℕ) (hi : i < T.leafCount) (hcap : T.leafCount ≤ 2 ^ height) :
    TreeRootStrongLogSafe h z0 hl T height (honestSibs h z0 (leafHashes hl T) i) height i
        (T.leaf i)
      ↔ TreeRootStrongPairInjOn h (treeRootStrongTreeLog h z0 (leafHashes hl T) height) := by
  have hsub := treeRootStrong_honest_walkLog_subset h z0 (leafHashes hl T) height i
    (lt_of_lt_of_le hi hcap)
  rw [leafHashes_getD hi] at hsub
  have hunion := Finset.union_eq_right.mpr hsub
  constructor
  · intro hs
    have := hs.nodeInjOn
    rw [hunion] at this
    exact this
  · intro hinj
    refine ⟨?_, fun hlt => absurd hlt (lt_irrefl _), fun hlt => absurd hlt (lt_irrefl _),
      fun _ _ => rfl, fun hle => absurd hle (by omega)⟩
    rw [hunion]
    exact hinj

/-! ## At the published root, along runs -/

theorem treeRootStrong_run_roots_at_own_height (h : Hash) (z0 : UInt256) (hl : LeafHash)
    (R : ℕ → HState) (hR : HRun R) (h0 : R 0 = hSetup) (n : ℕ) :
    (TreeRootStrongPairInjOn h
        (treeRootStrongTreeLog h z0 (leafHashes hl (R n).tree) (R n).height) →
      ∀ v : UInt256, v ∈ keys (toAbs (R n).tree) →
        ∃ i < (R n).tree.leafCount, ((R n).tree.leaf i).value = v
          ∧ InclusionAccepted h hl ((R n).root h z0 hl) v ((R n).tree.leaf i) i
              (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height
          ∧ TreeRootStrongLogSafe h z0 hl (R n).tree (R n).height
              (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height i ((R n).tree.leaf i))
    ∧ (TreeRootStrongPairInjOn h
        (treeRootStrongTreeLog h z0 (leafHashes hl (R n).tree) (R n).height) →
      ∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs (R n).tree) →
        ∃ i < (R n).tree.leafCount,
          NonInclusionAccepted h hl ((R n).root h z0 hl) v ((R n).tree.leaf i) i
              (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height
          ∧ TreeRootStrongLogSafe h z0 hl (R n).tree (R n).height
              (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height i ((R n).tree.leaf i))
    ∧ (∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      TreeRootStrongLogSafe h z0 hl (R n).tree (R n).height s₁ k₁ i₁ ℓ₁ →
      TreeRootStrongLogSafe h z0 hl (R n).tree (R n).height s₂ k₂ i₂ ℓ₂ →
      ¬ (InclusionAccepted h hl ((R n).root h z0 hl) v ℓ₁ i₁ s₁ k₁
          ∧ NonInclusionAccepted h hl ((R n).root h z0 hl) v ℓ₂ i₂ s₂ k₂)) := by
  have hReach := hRun_reaches hR h0 n
  have hV : Valid (R n).tree := reaches_valid (hReaches_projects hReach) setup_valid
  have hcap := hReaches_capacity hReach
  obtain ⟨h1, h2, _⟩ := proofs_exclusive_or_break_at_own_height h z0 hl (R n) hReach
  refine ⟨fun hinj v hv => ?_, fun hinj v hv0 habs => ?_,
    fun v ℓ₁ ℓ₂ i₁ i₂ s₁ s₂ k₁ k₂ hs₁ hs₂ => treeRootStrong_proofs_exclusive hV hs₁ hs₂⟩
  · obtain ⟨i, hi, hval, hI, _⟩ := h1 v hv
    exact ⟨i, hi, hval, hI, (treeRootStrong_honest_logSafe_iff h z0 hl _ _ i hi hcap).mpr hinj⟩
  · obtain ⟨i, hi, hN, _⟩ := h2 v hv0 habs
    exact ⟨i, hi, hN, (treeRootStrong_honest_logSafe_iff h z0 hl _ _ i hi hcap).mpr hinj⟩

/-! ## The concrete witness -/

lemma treeRootStrong_witness_leafHashes :
    leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2) = [115, 1225, 2005] := by
  decide

lemma treeRootStrong_witness_pad : treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩ = 5 := by
  decide

/-- The witness tree's log at height 2, for any padding constant `z`: the two level-0 pairs
and the level-1 pair. -/
lemma treeRootStrong_witness_treeLog_mem_any (z : UInt256) {p : UInt256 × UInt256} :
    p ∈ treeRootStrongTreeLog treeRootStrongWitnessNodeHash z [115, 1225, 2005] 2
      ↔ p = (115, 1225) ∨ p = (2005, z)
        ∨ p = (treeRootStrongWitnessNodeHash 115 1225, treeRootStrongWitnessNodeHash 2005 z) := by
  rw [treeRootStrong_mem_treeLog_iff]
  constructor
  · rintro ⟨l, hl, m, hm, rfl⟩
    interval_cases l
    · norm_num at hm
      interval_cases m
      · left; rfl
      · right; left; rfl
    · norm_num at hm
      subst hm
      right; right; rfl
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, 0, by norm_num, rfl⟩
    · exact ⟨0, by norm_num, 1, by norm_num, rfl⟩
    · exact ⟨1, by norm_num, 0, by norm_num, rfl⟩

lemma treeRootStrong_witness_treeLog_mem {p : UInt256 × UInt256} :
    p ∈ treeRootStrongTreeLog treeRootStrongWitnessNodeHash 5 [115, 1225, 2005] 2
      ↔ p = (115, 1225) ∨ p = (2005, 5) ∨ p = (8921, 6051) := by
  rw [treeRootStrong_witness_treeLog_mem_any]
  have e₁ : treeRootStrongWitnessNodeHash 115 1225 = 8921 := by decide
  have e₂ : treeRootStrongWitnessNodeHash 2005 5 = 6051 := by decide
  rw [e₁, e₂]

lemma treeRootStrong_witness_pairInjOn :
    TreeRootStrongPairInjOn treeRootStrongWitnessNodeHash
      (treeRootStrongTreeLog treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
        (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 2) := by
  rw [treeRootStrong_witness_pad, treeRootStrong_witness_leafHashes]
  intro p hp q hq he
  rw [treeRootStrong_witness_treeLog_mem] at hp hq
  rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert he; decide)

theorem treeRootStrong_witness :
    Valid (threeLeafTree 1 2)
      ∧ (∃ R : ℕ → Tree, Run R ∧ R 0 = setup ∧ R 2 = threeLeafTree 1 2)
      ∧ TreeRootStrongPairInjOn treeRootStrongWitnessNodeHash
          (treeRootStrongTreeLog treeRootStrongWitnessNodeHash
            (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
            (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 2)
      ∧ InclusionAccepted treeRootStrongWitnessNodeHash treeRootStrongWitnessLeafHash
          (root treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
            treeRootStrongWitnessLeafHash (threeLeafTree 1 2) 2)
          1 ((threeLeafTree 1 2).leaf 1) 1
          (honestSibs treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
            (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 1) 2
      ∧ TreeRootStrongLogSafe treeRootStrongWitnessNodeHash
          (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
          treeRootStrongWitnessLeafHash (threeLeafTree 1 2) 2
          (honestSibs treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
            (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 1) 2 1
          ((threeLeafTree 1 2).leaf 1)
      ∧ NonInclusionAccepted treeRootStrongWitnessNodeHash treeRootStrongWitnessLeafHash
          (root treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
            treeRootStrongWitnessLeafHash (threeLeafTree 1 2) 2)
          3 ((threeLeafTree 1 2).leaf 2) 2
          (honestSibs treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
            (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 2) 2
      ∧ TreeRootStrongLogSafe treeRootStrongWitnessNodeHash
          (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
          treeRootStrongWitnessLeafHash (threeLeafTree 1 2) 2
          (honestSibs treeRootStrongWitnessNodeHash (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
            (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 2) 2 2
          ((threeLeafTree 1 2).leaf 2) := by
  have h01 : (0 : UInt256) < 1 := by decide
  have h12 : (1 : UInt256) < 2 := by decide
  have hcount : (threeLeafTree 1 2).leafCount = 3 := rfl
  have hcap : (threeLeafTree 1 2).leafCount ≤ 2 ^ 2 := by rw [hcount]; norm_num
  have hinj := treeRootStrong_witness_pairInjOn
  obtain ⟨hV, _, _⟩ := padding_collision_refunds_delivered_leg treeRootStrongWitnessNodeHash
    treeRootStrongWitnessLeafHash h01 h12
  obtain ⟨R, hR, hR0, hR2, _⟩ := run_roots_exclusive_or_break_satisfiable
    treeRootStrongWitnessNodeHash treeRootStrongWitnessLeafHash 1 2 h01 h12
  have hI := inclusion_complete (h := treeRootStrongWitnessNodeHash)
    (z0 := treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩) (hl := treeRootStrongWitnessLeafHash)
    (T := threeLeafTree 1 2) (height := 2) hcap (i := 1) (by rw [hcount]; norm_num)
  have hI2 := inclusion_complete (h := treeRootStrongWitnessNodeHash)
    (z0 := treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩) (hl := treeRootStrongWitnessLeafHash)
    (T := threeLeafTree 1 2) (height := 2) hcap (i := 2) (by rw [hcount]; norm_num)
  rw [threeLeafTree_leaf_one_value] at hI
  refine ⟨hV, ⟨R, hR, hR0, hR2⟩, hinj, hI,
    (treeRootStrong_honest_logSafe_iff _ _ _ _ 2 1 (by rw [hcount]; norm_num) hcap).mpr hinj,
    ⟨by decide, by decide, Or.inl (by decide), hI2.path⟩,
    (treeRootStrong_honest_logSafe_iff _ _ _ _ 2 2 (by rw [hcount]; norm_num) hcap).mpr hinj⟩

/-- The forged walk at the dedicated padding `7` hashes `(2005, 5)` and then `(8921, 6051)`. -/
lemma treeRootStrong_dedicated_walkLog_mem {p : UInt256 × UInt256} :
    p ∈ treeRootStrongWalkLog treeRootStrongWitnessNodeHash
        (honestSibs treeRootStrongWitnessNodeHash 7 [115, 1225, 2005] 3) 2 3 5
      ↔ p = (2005, 5) ∨ p = (8921, 6051) := by
  rw [treeRootStrong_mem_walkLog_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i
    · left; decide
    · right; decide
  · rintro (rfl | rfl)
    · exact ⟨0, by norm_num, by decide⟩
    · exact ⟨1, by norm_num, by decide⟩

theorem treeRootStrong_dedicated_padding_witness :
    1 ∈ keys (toAbs (threeLeafTree 1 2))
      ∧ TreeRootStrongLogSafe treeRootStrongWitnessNodeHash 7 treeRootStrongWitnessLeafHash
          (threeLeafTree 1 2) 2
          (honestSibs treeRootStrongWitnessNodeHash 7
            (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 3) 2 3 ⟨0, 0, 0⟩
      ∧ ¬ NonInclusionAccepted treeRootStrongWitnessNodeHash treeRootStrongWitnessLeafHash
          (root treeRootStrongWitnessNodeHash 7 treeRootStrongWitnessLeafHash (threeLeafTree 1 2) 2)
          1 ⟨0, 0, 0⟩ 3
          (honestSibs treeRootStrongWitnessNodeHash 7
            (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 3) 2 := by
  obtain ⟨hV, hmem, _⟩ := padding_collision_refunds_delivered_leg treeRootStrongWitnessNodeHash
    treeRootStrongWitnessLeafHash (a := 1) (b := 2) (by decide) (by decide)
  have hcount : (threeLeafTree 1 2).leafCount = 3 := rfl
  have hs : TreeRootStrongLogSafe treeRootStrongWitnessNodeHash 7 treeRootStrongWitnessLeafHash
      (threeLeafTree 1 2) 2
      (honestSibs treeRootStrongWitnessNodeHash 7
        (leafHashes treeRootStrongWitnessLeafHash (threeLeafTree 1 2)) 3) 2 3 ⟨0, 0, 0⟩ := by
    refine ⟨?_, fun hlt => absurd hlt (lt_irrefl _), fun hlt => absurd hlt (lt_irrefl _),
      fun hlt => absurd hlt (by rw [hcount]; exact lt_irrefl _), fun _ => ?_⟩
    · rw [treeRootStrong_witness_leafHashes, treeRootStrong_witness_pad]
      intro p hp q hq he
      rw [Finset.mem_union, treeRootStrong_dedicated_walkLog_mem,
        treeRootStrong_witness_treeLog_mem_any] at hp hq
      rcases hp with (rfl | rfl) | (rfl | rfl | rfl) <;>
        rcases hq with (rfl | rfl) | (rfl | rfl | rfl) <;>
        first | rfl | (exfalso; revert he; decide)
    · rw [treeRootStrong_witness_pad]; decide
  exact ⟨hmem, hs, fun hN => treeRootStrong_verified_absence_excludes_delivered hV hN hs hmem⟩

theorem treeRootStrong_run_roots_at_own_height_witness :
    HRun (hThreeRun 1 2) ∧ hThreeRun 1 2 0 = hSetup
      ∧ (hThreeRun 1 2 2).tree = threeLeafTree 1 2 ∧ (hThreeRun 1 2 2).height = 2
      ∧ TreeRootStrongPairInjOn treeRootStrongWitnessNodeHash
          (treeRootStrongTreeLog treeRootStrongWitnessNodeHash
            (treeRootStrongWitnessLeafHash ⟨0, 0, 0⟩)
            (leafHashes treeRootStrongWitnessLeafHash (hThreeRun 1 2 2).tree)
            (hThreeRun 1 2 2).height) := by
  obtain ⟨hR, h0, _, _, _, _, hh2, ht2, _⟩ := hThreeRun_witness 1 2 (by decide) (by decide)
  refine ⟨hR, h0, ht2, hh2, ?_⟩
  rw [ht2, hh2]
  exact treeRootStrong_witness_pairInjOn

/-! ## The premise cannot be dropped -/

theorem treeRootStrong_pin_forgery_fails_logSafe (h : Hash) (hl : LeafHash) (a b : UInt256)
    (ha : 0 < a) (hab : a < b) :
    Valid (threeLeafTree a b)
      ∧ a ∈ keys (toAbs (threeLeafTree a b))
      ∧ InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2) a
          ((threeLeafTree a b).leaf 1) 1
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 1) 2
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2
      ∧ ¬ (∃ W ∈ toAbs (threeLeafTree a b), W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey))
      ∧ ¬ TreeRootStrongLogSafe h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3 ⟨0, 0, 0⟩ := by
  obtain ⟨hV, hmem, hN⟩ := padding_collision_refunds_delivered_leg h hl ha hab
  obtain ⟨_, hI, _⟩ := proofs_exclusive_or_break_satisfiable h hl a b ha hab
  exact ⟨hV, hmem, hI, hN, present_not_reclaimable hV.absSound.1 hmem,
    fun hs => hs.padNotPresented (le_of_eq rfl) rfl⟩

open Contracts.Protocol in
theorem treeRootStrong_without_premise_fails :
    (∀ (h : Hash) (hl : LeafHash),
      (¬ ∀ (T : Tree) (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf),
          PathAccepts h (root h (hl ⟨0, 0, 0⟩) hl T height) sibs k idx (hl ℓ) →
            k = height ∧ idx < T.leafCount ∧ T.leaf idx = ℓ)
      ∧ (¬ ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256)
            (k : ℕ),
          NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ℓ idx sibs k →
            ∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
      ∧ (¬ ∀ (T : Tree), Valid T →
          ∀ (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
            NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ℓ idx sibs k →
              v ∉ keys (toAbs T))
      ∧ (¬ ∀ (T : Tree), Valid T →
          ∀ (height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256)
            (k₁ k₂ : ℕ),
            ¬ (InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ℓ₁ i₁ s₁ k₁
                ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ℓ₂ i₂ s₂ k₂))
      ∧ (¬ ∀ (R : ℕ → Tree), Run R → R 0 = setup →
          ∀ (n height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256)
            (k₁ k₂ : ℕ),
            ¬ (InclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (R n) height) v ℓ₁ i₁ s₁ k₁
                ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (R n) height) v ℓ₂ i₂ s₂ k₂))
      ∧ (¬ ∀ (T : Chain → Tree) (c : Chain) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ)
            (sibs : ℕ → UInt256) (k : ℕ),
          NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (T c) height) v ℓ idx sibs k →
            AbsenceWitnessAt (ofChains T) c v))
    ∧ ¬ ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256)
        (k : ℕ),
        InclusionAccepted toyNodeHash toyLeafHash (root toyNodeHash 1 toyLeafHash T height) v ℓ
          idx sibs k → v ∈ keys (toAbs T) := by
  refine ⟨fun h hl => ?_, ?_⟩
  · obtain ⟨hV, hmem, hI, hN, hnoW, _⟩ :=
      treeRootStrong_pin_forgery_fails_logSafe h hl 1 2 (by decide) (by decide)
    obtain ⟨R, hR, hR0, _, hIR, hNR⟩ :=
      run_roots_exclusive_or_break_satisfiable h hl 1 2 (by decide) (by decide)
    refine ⟨fun hall => ?_, fun hall => hnoW (hall _ _ _ _ _ _ _ hN),
      fun hall => hall _ hV _ _ _ _ _ _ hN hmem,
      fun hall => hall _ hV _ _ _ _ _ _ _ _ _ _ ⟨hI, hN⟩,
      fun hall => hall R hR hR0 2 _ _ _ _ _ _ _ _ _ _ ⟨hIR, hNR⟩,
      fun hall => hnoW (hall (fun _ => threeLeafTree 1 2) 0 _ _ _ _ _ _ hN)⟩
    obtain ⟨_, hidx, _⟩ := hall _ _ _ _ _ _ hN.path
    exact lt_irrefl 3 hidx
  · intro hall
    obtain ⟨sibs, k, idx, ℓ, _, _, hI, hnot, _⟩ := tree_root_break_every_case_fires .pathCollision
    exact hnot (hall _ _ _ _ _ _ _ hI)

theorem treeRootStrong_pin_forgery_fails_only_padding (h : Hash) (hl : LeafHash) (a b : UInt256) :
    treeRootStrongWalkLog h (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3)
        2 3 (hl ⟨0, 0, 0⟩)
      ⊆ treeRootStrongTreeLog h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 2
    ∧ (TreeRootStrongPairInjOn h
          (treeRootStrongTreeLog h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 2) →
        TreeRootStrongPairInjOn h
            (treeRootStrongWalkLog h
                (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3
                (hl ⟨0, 0, 0⟩)
              ∪ treeRootStrongTreeLog h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 2)
          ∧ (2 < 2 → ∀ p ∈ treeRootStrongTreeLog h (hl ⟨0, 0, 0⟩)
                (leafHashes hl (threeLeafTree a b)) 2, hl ⟨0, 0, 0⟩ ≠ h p.1 p.2)
          ∧ (2 < 2 → ∀ p ∈ treeRootStrongWalkLog h
                (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2 3
                (hl ⟨0, 0, 0⟩),
              ∀ y ∈ hl ⟨0, 0, 0⟩ :: leafHashes hl (threeLeafTree a b), y ≠ h p.1 p.2)
          ∧ (3 < (threeLeafTree a b).leafCount →
              hl ((threeLeafTree a b).leaf 3) = hl ⟨0, 0, 0⟩ →
                (threeLeafTree a b).leaf 3 = ⟨0, 0, 0⟩))
    ∧ ¬ ((threeLeafTree a b).leafCount ≤ 3 → hl ⟨0, 0, 0⟩ ≠ hl ⟨0, 0, 0⟩) := by
  have hcount : (threeLeafTree a b).leafCount = 3 := rfl
  have hget : (leafHashes hl (threeLeafTree a b)).getD 3 (hl ⟨0, 0, 0⟩) = hl ⟨0, 0, 0⟩ :=
    getD_default _ _ _ (by rw [leafHashes_length, hcount])
  have hsub := treeRootStrong_honest_walkLog_subset h (hl ⟨0, 0, 0⟩)
    (leafHashes hl (threeLeafTree a b)) 2 3 (by norm_num)
  rw [hget] at hsub
  refine ⟨hsub, fun hinj => ⟨?_, fun hlt => absurd hlt (lt_irrefl _),
    fun hlt => absurd hlt (lt_irrefl _), fun hlt => absurd hlt (by rw [hcount]; exact lt_irrefl _)⟩,
    fun hpad => hpad (le_of_eq hcount) rfl⟩
  rw [Finset.union_eq_right.mpr hsub]
  exact hinj

end Contracts.InteropCommitmentTree

/-! ## Certificates -/

namespace Contracts.InteropCommitmentTree

theorem TreeRootStrongLogSafeExcludesBreak : Properties.TreeRootStrongLogSafeExcludesBreak :=
  fun _ _ _ _ _ _ _ _ _ hp hs => treeRootStrong_no_break hp hs
theorem TreeRootStrongLogBounded : Properties.TreeRootStrongLogBounded :=
  treeRootStrong_log_bounded
theorem TreeRootStrongAcceptedPathPinsLeaf : Properties.TreeRootStrongAcceptedPathPinsLeaf :=
  fun _ _ _ _ _ _ _ _ _ hp hs => treeRootStrong_accepted_path_pins_leaf hp hs
theorem TreeRootStrongInclusionSound : Properties.TreeRootStrongInclusionSound :=
  fun _ _ _ _ _ _ _ _ _ _ hI hs => treeRootStrong_inclusion_sound hI hs
theorem TreeRootStrongNonInclusionSound : Properties.TreeRootStrongNonInclusionSound :=
  fun _ _ _ _ _ _ _ _ _ _ hN hs => treeRootStrong_non_inclusion_sound hN hs
theorem TreeRootStrongVerifiedAbsenceExcludesDelivered :
    Properties.TreeRootStrongVerifiedAbsenceExcludesDelivered :=
  fun _ _ _ _ hV _ _ _ _ _ _ hN hs => treeRootStrong_verified_absence_excludes_delivered hV hN hs
theorem TreeRootStrongProofsExclusive : Properties.TreeRootStrongProofsExclusive :=
  fun _ _ _ _ hV _ _ _ _ _ _ _ _ _ _ hs₁ hs₂ => treeRootStrong_proofs_exclusive hV hs₁ hs₂
theorem TreeRootStrongRunRootsExclusive : Properties.TreeRootStrongRunRootsExclusive :=
  fun _ _ _ _ hR h0 _ _ _ _ _ _ _ _ _ _ _ hs₁ hs₂ =>
    treeRootStrong_run_roots_exclusive hR h0 hs₁ hs₂
theorem TreeRootStrongVerifiedAbsenceIsWitness : Properties.TreeRootStrongVerifiedAbsenceIsWitness :=
  fun _ _ _ _ _ _ _ _ _ _ _ hN hs => treeRootStrong_verified_absence_is_witness hN hs
theorem TreeRootStrongRunRootsAtOwnHeight : Properties.TreeRootStrongRunRootsAtOwnHeight :=
  treeRootStrong_run_roots_at_own_height
theorem TreeRootStrongHonestLogSafeIff : Properties.TreeRootStrongHonestLogSafeIff :=
  treeRootStrong_honest_logSafe_iff
theorem TreeRootStrongWitness : Properties.TreeRootStrongWitness := treeRootStrong_witness
theorem TreeRootStrongDedicatedPaddingWitness : Properties.TreeRootStrongDedicatedPaddingWitness :=
  treeRootStrong_dedicated_padding_witness
theorem TreeRootStrongRunRootsAtOwnHeightWitness :
    Properties.TreeRootStrongRunRootsAtOwnHeightWitness :=
  treeRootStrong_run_roots_at_own_height_witness
theorem TreeRootStrongPinForgeryFailsLogSafe : Properties.TreeRootStrongPinForgeryFailsLogSafe :=
  treeRootStrong_pin_forgery_fails_logSafe
theorem TreeRootStrongWithoutPremiseFails : Properties.TreeRootStrongWithoutPremiseFails :=
  treeRootStrong_without_premise_fails
theorem TreeRootStrongPinForgeryFailsOnlyPadding :
    Properties.TreeRootStrongPinForgeryFailsOnlyPadding :=
  treeRootStrong_pin_forgery_fails_only_padding

end Contracts.InteropCommitmentTree
