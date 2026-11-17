import EraSpec.Contracts.IndexedMerkleTree.Properties.UnboundedSearchAtV35
import EraSpec.Contracts.IndexedMerkleTree.Proofs.Model

/-!
# Proofs: the unbounded low-leaf walk at draft/v0.35.0

Proofs of `../Properties/UnboundedSearchAtV35.lean`.  Pure order theory over `Finset AbsLeaf`.

* The walk is handled by induction on its derivation.  Termination uses the measure "leaves of the
  set with a key above the current one", which each hop shrinks by at least the hop target.
* The walk's length is the gap: the hop target is the smallest key above the current one
  (`GapSound`), so the gap from the current key is the gap from the target plus the target.
* The insert and history results reduce to `guarded_insert_sound_step`,
  `guarded_insert_toggles_reclaimable` and the `GuardedEvolution` capstones of `Proofs/Model.lean`.
* The pin's counted loop is related to the walk by induction with the attempt counter generalised.
* The concrete witnesses are computed by `decide` on the small chain sets, and their walks are
  obtained from the general results (termination, length, uniqueness of the exit leaf) rather than
  built hop by hop.
-/

namespace IMTAbstract

open Clear

/-! ## Helpers -/

/-- Membership in `imtInsert`. -/
private theorem mem_imtInsert_unboundedV35 {s : Finset AbsLeaf} {W₀ X : AbsLeaf} {v : UInt256} :
    X ∈ imtInsert s W₀ v ↔ X = ⟨W₀.key, v⟩ ∨ X = ⟨v, W₀.nextKey⟩ ∨ (X ∈ s ∧ X ≠ W₀) := by
  unfold imtInsert
  simp only [Finset.mem_insert, Finset.mem_erase]
  tauto

/-- A key of a leaf of the set is a key of the set. -/
private theorem key_mem_keys_unboundedV35 {s : Finset AbsLeaf} {X : AbsLeaf} (hX : X ∈ s) :
    X.key ∈ keys s :=
  Finset.mem_image.mpr ⟨X, hX, rfl⟩

/-- The loop test is false: the leaf is in the weak loop-exit window. -/
private theorem exit_of_not_test_unboundedV35 {W : AbsLeaf} {v : UInt256}
    (hc : ¬ (W.nextKey ≠ 0 ∧ W.nextKey < v)) : W.nextKey = 0 ∨ v ≤ W.nextKey := by
  by_cases h0 : W.nextKey = 0
  · exact Or.inl h0
  · exact Or.inr (not_lt.mp fun hlt => hc ⟨h0, hlt⟩)

/-- A leaf in the weak loop-exit window fails the loop test. -/
private theorem not_test_of_exit_unboundedV35 {W : AbsLeaf} {v : UInt256}
    (hx : W.nextKey = 0 ∨ v ≤ W.nextKey) (hnz : W.nextKey ≠ 0) (hlt : W.nextKey < v) : False := by
  rcases hx with h | h
  · exact hnz h
  · exact absurd hlt (not_lt.mpr h)

/-- A hop target sits strictly above the leaf it leaves (`WindowPos`). -/
private theorem hop_key_gt_unboundedV35 {s : Finset AbsLeaf} {W L : AbsLeaf} (hwp : WindowPos s)
    (hW : W ∈ s) (hnz : W.nextKey ≠ 0) (hkey : L.key = W.nextKey) : W.key < L.key := by
  rcases hwp W hW with h | h
  · exact absurd h hnz
  · rw [hkey]; exact h

/-! ## The walk -/

theorem WalkSoundV35 : Properties.WalkSoundV35 := by
  intro s v n W₀ W hw
  induction hw with
  | exit hx => exact fun hW hlt => ⟨hW, hlt, hx⟩
  | hop _ hlt hL hkey _ ih => exact fun _ _ => ih hL (by rw [hkey]; exact hlt)

/-- The measure of the termination argument: the leaves of `s` with a key above `k`. -/
private theorem walkV35_exists_le {s : Finset AbsLeaf} {v : UInt256} (hnc : NextClosed s)
    (hwp : WindowPos s) :
    ∀ (m : ℕ) (W₀ : AbsLeaf), W₀ ∈ s → (s.filter (fun X => W₀.key < X.key)).card ≤ m →
      ∃ (n : ℕ) (W : AbsLeaf), WalkV35 s v n W₀ W
        ∧ n ≤ (s.filter (fun X => W₀.key < X.key)).card := by
  intro m
  induction m with
  | zero =>
    intro W₀ hW₀ hm
    by_cases hc : W₀.nextKey ≠ 0 ∧ W₀.nextKey < v
    · exfalso
      obtain ⟨L, hL, hLkey⟩ := hnc W₀ hW₀ hc.1
      have hmem : L ∈ s.filter (fun X => W₀.key < X.key) :=
        Finset.mem_filter.mpr ⟨hL, hop_key_gt_unboundedV35 hwp hW₀ hc.1 hLkey⟩
      have := Finset.card_pos.mpr ⟨L, hmem⟩
      omega
    · exact ⟨0, W₀, WalkV35.exit (exit_of_not_test_unboundedV35 hc), Nat.zero_le _⟩
  | succ m ih =>
    intro W₀ hW₀ hm
    by_cases hc : W₀.nextKey ≠ 0 ∧ W₀.nextKey < v
    · obtain ⟨L, hL, hLkey⟩ := hnc W₀ hW₀ hc.1
      have hpos := hop_key_gt_unboundedV35 hwp hW₀ hc.1 hLkey
      have hsub : s.filter (fun X => L.key < X.key) ⊂ s.filter (fun X => W₀.key < X.key) := by
        rw [Finset.ssubset_iff_of_subset]
        · exact ⟨L, Finset.mem_filter.mpr ⟨hL, hpos⟩,
            fun h => lt_irrefl _ (Finset.mem_filter.mp h).2⟩
        · intro X hX
          obtain ⟨hXs, hXk⟩ := Finset.mem_filter.mp hX
          exact Finset.mem_filter.mpr ⟨hXs, lt_trans hpos hXk⟩
      have hlt := Finset.card_lt_card hsub
      obtain ⟨n, W, hw, hn⟩ := ih L hL (by omega)
      exact ⟨n + 1, W, WalkV35.hop hc.1 hc.2 hL hLkey hw, by omega⟩
    · exact ⟨0, W₀, WalkV35.exit (exit_of_not_test_unboundedV35 hc), Nat.zero_le _⟩

theorem WalkTerminatesV35 : Properties.WalkTerminatesV35 := by
  intro s v W₀ hnc hwp hW₀
  obtain ⟨n, W, hw, hn⟩ := walkV35_exists_le (v := v) hnc hwp _ W₀ hW₀ le_rfl
  refine ⟨n, W, hw, lt_of_le_of_lt hn (Finset.card_lt_card ?_)⟩
  rw [Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)]
  exact ⟨W₀, hW₀, fun h => lt_irrefl _ (Finset.mem_filter.mp h).2⟩

theorem WalkDeterministicV35 : Properties.WalkDeterministicV35 := by
  intro s v n n' W₀ W W' hinj h1 h2
  induction h1 generalizing n' W' with
  | exit hx =>
    cases h2 with
    | exit _ => exact ⟨rfl, rfl⟩
    | hop hnz hlt _ _ _ => exact (not_test_of_exit_unboundedV35 hx hnz hlt).elim
  | hop hnz hlt hL hkey _ ih =>
    cases h2 with
    | exit hx => exact (not_test_of_exit_unboundedV35 hx hnz hlt).elim
    | hop _ _ hL' hkey' hw' =>
      obtain rfl := hinj _ hL _ hL' (hkey.trans hkey'.symm)
      obtain ⟨rfl, rfl⟩ := ih _ _ hw'
      exact ⟨rfl, rfl⟩

theorem WalkLengthIsGapV35 : Properties.WalkLengthIsGapV35 := by
  intro s v n W₀ W hgs hwp hW₀ hw
  induction hw with
  | @exit X hx =>
    symm
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro x hx'
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hx'
    rintro ⟨h1, h2⟩
    obtain ⟨hnz, hle⟩ := hgs X hW₀ L hL h1
    rcases hx with h | h
    · exact hnz h
    · exact absurd (lt_of_le_of_lt (le_trans h hle) h2) (lt_irrefl _)
  | @hop m X L Y hnz hlt hL hkey _ ih =>
    rw [ih hL]
    have hpos := hop_key_gt_unboundedV35 hwp hW₀ hnz hkey
    have heq : gapKeysV35 s X.key v = insert L.key (gapKeysV35 s L.key v) := by
      ext x
      simp only [gapKeysV35, Finset.mem_insert, Finset.mem_filter]
      constructor
      · rintro ⟨hxk, h1, h2⟩
        obtain ⟨Z, hZ, rfl⟩ := Finset.mem_image.mp hxk
        obtain ⟨_, hle⟩ := hgs X hW₀ Z hZ h1
        rw [← hkey] at hle
        rcases lt_or_eq_of_le hle with h | h
        · exact Or.inr ⟨hxk, h, h2⟩
        · exact Or.inl h.symm
      · rintro (rfl | ⟨hxk, h1, h2⟩)
        · exact ⟨key_mem_keys_unboundedV35 hL, hpos, by rw [hkey]; exact hlt⟩
        · exact ⟨hxk, lt_trans hpos h1, h2⟩
    rw [heq, Finset.card_insert_of_notMem]
    simp [gapKeysV35]

theorem StraddlingLeafUniqueV35 : Properties.StraddlingLeafUniqueV35 := by
  intro s v W₁ W₂ hgs hinj hW₁ hW₂ h1 hw1 h2 hw2
  rcases lt_trichotomy W₁.key W₂.key with hlt | heq | hgt
  · exfalso
    obtain ⟨hnz, hle⟩ := hgs W₁ hW₁ W₂ hW₂ hlt
    rcases hw1 with h | h
    · exact hnz h
    · exact absurd (lt_trans h (lt_of_le_of_lt hle h2)) (lt_irrefl _)
  · exact hinj W₁ hW₁ W₂ hW₂ heq
  · exfalso
    obtain ⟨hnz, hle⟩ := hgs W₂ hW₂ W₁ hW₁ hgt
    rcases hw2 with h | h
    · exact hnz h
    · exact absurd (lt_trans h (lt_of_le_of_lt hle h1)) (lt_irrefl _)

theorem WalkFindsLowLeafV35 : Properties.WalkFindsLowLeafV35 := by
  intro s v n W₀ W hs habs hW₀ hlt hw
  obtain ⟨hW, hWlt, hwin⟩ := WalkSoundV35 s v n W₀ W hw hW₀ hlt
  have hstrict : W.nextKey = 0 ∨ v < W.nextKey := window_strict_of_not_mem hs.2.2.1 hW habs hwin
  exact ⟨hW, hWlt, hstrict, fun W' hW' h1 h2 =>
    StraddlingLeafUniqueV35 s v W' W hs.1 hs.2.1 hW' hW h1 h2 hWlt hstrict⟩

theorem WalkHintIndependentV35 : Properties.WalkHintIndependentV35 := by
  intro s v n₁ n₂ W₁ W₂ R₁ R₂ hs habs hW₁ h1 hW₂ h2 hw1 hw2
  obtain ⟨hR₁, hR₁lt, hR₁w, _⟩ := WalkFindsLowLeafV35 s v n₁ W₁ R₁ hs habs hW₁ h1 hw1
  obtain ⟨_, _, _, huniq⟩ := WalkFindsLowLeafV35 s v n₂ W₂ R₂ hs habs hW₂ h2 hw2
  exact huniq R₁ hR₁ hR₁lt hR₁w

/-! ## The insert -/

theorem InsertV35IsGuardedStep : Properties.InsertV35IsGuardedStep := by
  intro s s' v W₀ hins
  cases hins with
  | @mk n W _ habs hW₀ hlt hw =>
    obtain ⟨hW, hWlt, hwin⟩ := WalkSoundV35 s v n W₀ W hw hW₀ hlt
    exact ⟨W, hW, hWlt, hwin, habs, rfl⟩

theorem InsertV35SoundStep : Properties.InsertV35SoundStep := by
  intro s s' v W₀ hs hins
  obtain ⟨W, hW, hlt, hwin, habs, rfl⟩ := InsertV35IsGuardedStep s s' v W₀ hins
  exact guarded_insert_sound_step hs hW hlt hwin habs

theorem InsertV35TogglesReclaimable : Properties.InsertV35TogglesReclaimable := by
  intro s s' v W₀ hs hins
  obtain ⟨W, hW, hlt, hwin, habs, rfl⟩ := InsertV35IsGuardedStep s s' v W₀ hins
  exact guarded_insert_toggles_reclaimable hs hW hlt hwin habs

theorem InsertV35HintIndependent : Properties.InsertV35HintIndependent := by
  intro s s₁ s₂ v W₁ W₂ hs h1 h2
  cases h1 with
  | @mk n₁ R₁ _ habs hW₁ hlt₁ hw₁ =>
    cases h2 with
    | @mk n₂ R₂ _ _ hW₂ hlt₂ hw₂ =>
      rw [WalkHintIndependentV35 s v n₁ n₂ W₁ W₂ R₁ R₂ hs habs hW₁ hlt₁ hW₂ hlt₂ hw₁ hw₂]

theorem HonestInsertNeverSearchRevertsV35 : Properties.HonestInsertNeverSearchRevertsV35 := by
  intro s v W₀ hs hv0 habs hW₀ hlt
  obtain ⟨n, W, hw, _⟩ := WalkTerminatesV35 s v W₀ hs.2.2.1 hs.2.2.2 hW₀
  exact ⟨n, W, hw, WalkLengthIsGapV35 s v n W₀ W hs.1 hs.2.2.2 hW₀ hw,
    InsertV35.mk hv0 habs hW₀ hlt hw⟩

/-! ## The headlines over v35 histories -/

theorem RunV35IsGuardedEvolution : Properties.RunV35IsGuardedEvolution := by
  intro S hrun n
  rcases hrun n with h | ⟨v, W₀, hins⟩
  · exact Or.inl h
  · obtain ⟨W, hW, hlt, hwin, habs, heq⟩ := InsertV35IsGuardedStep _ _ v W₀ hins
    exact Or.inr ⟨W, v, hW, hlt, hwin, habs, heq⟩

theorem RunV35IsEvolution : Properties.RunV35IsEvolution := fun S hrun h0 =>
  guardedEvolution_isEvolution (RunV35IsGuardedEvolution S hrun) h0

theorem RunV35Sound : Properties.RunV35Sound := fun S hrun h0 =>
  guardedEvolution_sound (RunV35IsGuardedEvolution S hrun) h0

theorem ReclaimableIffAbsentV35 : Properties.ReclaimableIffAbsentV35 := fun S hrun hgen j _ hv0 =>
  guardedEvolution_reclaimable_iff_absent (RunV35IsGuardedEvolution S hrun) hgen (j := j) hv0

theorem DeliveredAvailableForeverV35 : Properties.DeliveredAvailableForeverV35 :=
  fun S _ _ _ hrun hgen hmono _ hti hdel =>
    guardedEvolution_delivered_available_forever (RunV35IsGuardedEvolution S hrun) hgen hmono
      hti hdel

theorem DeliveryExactlyOnceV35 : Properties.DeliveryExactlyOnceV35 :=
  fun S hrun hgen _ hv0 _ hmem =>
    guardedEvolution_delivery_exactly_once (RunV35IsGuardedEvolution S hrun) hgen hv0 hmem

/-! ## Liveness along v35 histories -/

theorem SentinelHintAlwaysWorksV35 : Properties.SentinelHintAlwaysWorksV35 := by
  intro S hrun hgen j v hv0 habs
  have h0 : SoundState (S 0) := by rw [hgen]; exact genesis_soundState
  have hevo := RunV35IsEvolution S hrun h0
  have hzero0 : (0 : UInt256) ∈ keys (S 0) := by rw [hgen]; exact genesis_zero_mem
  have hzero : (0 : UInt256) ∈ keys (S j) := evolution_keys_mono hevo (Nat.zero_le j) hzero0
  obtain ⟨W₀, hW₀, hk⟩ := Finset.mem_image.mp hzero
  have hlt : W₀.key < v := by rw [hk]; exact Fin.pos_of_ne_zero hv0
  obtain ⟨_, _, _, _, hins⟩ :=
    HonestInsertNeverSearchRevertsV35 (S j) v W₀ (RunV35Sound S hrun h0 j) hv0 habs hW₀ hlt
  exact ⟨W₀, hW₀, hk, _, hins⟩

theorem OnceValidHintStaysValidV35 : Properties.OnceValidHintStaysValidV35 := by
  intro S hrun h0 i j W₀ v hij hW₀ hlt hv0 habs
  have hevo := RunV35IsEvolution S hrun h0
  have hk : W₀.key ∈ keys (S j) := evolution_keys_mono hevo hij (key_mem_keys_unboundedV35 hW₀)
  obtain ⟨W₀', hW₀', hk'⟩ := Finset.mem_image.mp hk
  obtain ⟨_, _, _, _, hins⟩ :=
    HonestInsertNeverSearchRevertsV35 (S j) v W₀' (RunV35Sound S hrun h0 j) hv0 habs hW₀'
      (by rw [hk']; exact hlt)
  exact ⟨W₀', hW₀', hk', _, hins⟩

/-! ## Data availability -/

/-- In a sound set, a member's `nextKey` is pinned by its key and the key set: if another sound
set has the same keys, its leaf with the same key has the same `nextKey`. -/
private theorem nextKey_eq_of_keys_unboundedV35 {s s' : Finset AbsLeaf} (hs : SoundState s)
    (hs' : SoundState s') (hk : keys s = keys s') {W W' : AbsLeaf} (hW : W ∈ s) (hW' : W' ∈ s')
    (hkey : W.key = W'.key) : W.nextKey = W'.nextKey := by
  -- a nonzero `nextKey` is a key of its own set, above its leaf's key
  have hup : ∀ {t : Finset AbsLeaf} {X : AbsLeaf}, SoundState t → X ∈ t → X.nextKey ≠ 0 →
      X.nextKey ∈ keys t ∧ X.key < X.nextKey := by
    intro t X ht hX hnz
    obtain ⟨L, hL, hLkey⟩ := ht.2.2.1 X hX hnz
    exact ⟨by rw [← hLkey]; exact key_mem_keys_unboundedV35 hL,
      by rw [← hLkey]; exact hop_key_gt_unboundedV35 ht.2.2.2 hX hnz hLkey⟩
  -- `GapSound` against a key of the set
  have hgap : ∀ {t : Finset AbsLeaf} {X : AbsLeaf} {x : UInt256}, SoundState t → X ∈ t →
      x ∈ keys t → X.key < x → X.nextKey ≠ 0 ∧ X.nextKey ≤ x := by
    intro t X x ht hX hx hlt
    obtain ⟨L, hL, rfl⟩ := Finset.mem_image.mp hx
    exact ht.1 X hX L hL hlt
  by_cases h0 : W.nextKey = 0
  · by_cases h0' : W'.nextKey = 0
    · rw [h0, h0']
    · exfalso
      obtain ⟨hmem, hgt⟩ := hup hs' hW' h0'
      rw [← hk] at hmem
      exact (hgap hs hW hmem (by rw [hkey]; exact hgt)).1 h0
  · obtain ⟨hmem, hgt⟩ := hup hs hW h0
    rw [hk] at hmem
    obtain ⟨h0', hle'⟩ := hgap hs' hW' hmem (by rw [← hkey]; exact hgt)
    obtain ⟨hmem', hgt'⟩ := hup hs' hW' h0'
    rw [← hk] at hmem'
    obtain ⟨_, hle⟩ := hgap hs hW hmem' (by rw [hkey]; exact hgt')
    exact le_antisymm hle hle'

/-- One inclusion of `SoundLeafSetDeterminedByKeysV35`. -/
private theorem subset_of_keys_unboundedV35 {s s' : Finset AbsLeaf} (hs : SoundState s)
    (hs' : SoundState s') (hk : keys s = keys s') : s ⊆ s' := by
  intro W hW
  have hkW : W.key ∈ keys s' := by rw [← hk]; exact key_mem_keys_unboundedV35 hW
  obtain ⟨W', hW', hkey⟩ := Finset.mem_image.mp hkW
  have hnext := nextKey_eq_of_keys_unboundedV35 hs hs' hk hW hW' hkey.symm
  have hWeq : W = W' := by
    cases W
    cases W'
    simp only at hkey hnext
    rw [hkey, hnext]
  rw [hWeq]
  exact hW'

theorem SoundLeafSetDeterminedByKeysV35 : Properties.SoundLeafSetDeterminedByKeysV35 :=
  fun _ _ hs hs' hk =>
    Finset.Subset.antisymm (subset_of_keys_unboundedV35 hs hs' hk)
      (subset_of_keys_unboundedV35 hs' hs hk.symm)

/-- A history of `StepV35` steps is a v35 history. -/
private theorem runV35_of_steps_unboundedV35 {S : ℕ → Finset AbsLeaf} {vals : ℕ → Option UInt256}
    (hS : ∀ n, StepV35 (vals n) (S n) (S (n + 1))) : RunV35 S := by
  intro m
  have hm := hS m
  cases hv : vals m with
  | none =>
    rw [hv] at hm
    exact Or.inl hm
  | some v =>
    rw [hv] at hm
    obtain ⟨W₀, hins⟩ := hm
    exact Or.inr ⟨v, W₀, hins⟩

theorem ValuesDetermineTreeV35 : Properties.ValuesDetermineTreeV35 := by
  intro S S' vals hS hS' h0 hsound n
  have hrun := runV35_of_steps_unboundedV35 hS
  induction n with
  | zero => exact h0
  | succ m ih =>
    have hm := hS m
    have hm' := hS' m
    cases hv : vals m with
    | none =>
      rw [hv] at hm hm'
      change S (m + 1) = S m at hm
      change S' (m + 1) = S' m at hm'
      rw [hm, hm', ih]
    | some v =>
      rw [hv] at hm hm'
      obtain ⟨W₁, h1⟩ := hm
      obtain ⟨W₂, h2⟩ := hm'
      rw [← ih] at h2
      exact InsertV35HintIndependent (S m) (S (m + 1)) (S' (m + 1)) v W₁ W₂
        (RunV35Sound S hrun hsound m) h1 h2

/-! ## The pin's bound, for contrast -/

/-- The pin's counted loop, entered at attempt `a`, follows a v35 walk: it exits where the walk
exits if the walk fits in the remaining attempts, and reverts otherwise. -/
private theorem boundedWalkV35_of_walk {s : Finset AbsLeaf} {v : UInt256} {bound : ℕ} :
    ∀ {n : ℕ} {W₀ W : AbsLeaf}, WalkV35 s v n W₀ W → ∀ a : ℕ,
      (a + n ≤ bound → BoundedWalkV35 s v bound a W₀ (some W))
        ∧ (a ≤ bound → bound < a + n → BoundedWalkV35 s v bound a W₀ none) := by
  intro n W₀ W hw
  induction hw with
  | exit hx =>
    intro a
    exact ⟨fun _ => BoundedWalkV35.exit hx, fun h1 h2 => absurd h1 (by omega)⟩
  | hop hnz hlt hL hkey _ ih =>
    intro a
    refine ⟨fun h => ?_, fun h1 h2 => ?_⟩
    · exact BoundedWalkV35.hop hnz hlt (by omega) hL hkey ((ih (a + 1)).1 (by omega))
    · by_cases ha : a = bound
      · exact BoundedWalkV35.revert hnz hlt ha
      · exact BoundedWalkV35.hop hnz hlt ha hL hkey ((ih (a + 1)).2 (by omega) (by omega))

theorem BoundedWalkIsTruncatedWalkV35 : Properties.BoundedWalkIsTruncatedWalkV35 := by
  intro s v bound n W₀ W hw
  have h := boundedWalkV35_of_walk (bound := bound) hw 0
  exact ⟨fun hn => h.1 (by omega), fun hn => h.2 (Nat.zero_le _) (by omega)⟩

/-- With unique keys the pin's counted loop has one outcome. -/
private theorem boundedWalkV35_deterministic {s : Finset AbsLeaf} {v : UInt256} {bound : ℕ}
    (hinj : KeyInj s) :
    ∀ {a : ℕ} {W : AbsLeaf} {r r' : Option AbsLeaf}, BoundedWalkV35 s v bound a W r →
      BoundedWalkV35 s v bound a W r' → r = r' := by
  intro a W r r' h1 h2
  induction h1 generalizing r' with
  | exit hx =>
    cases h2 with
    | exit _ => rfl
    | revert hnz hlt _ => exact (not_test_of_exit_unboundedV35 hx hnz hlt).elim
    | hop hnz hlt _ _ _ _ => exact (not_test_of_exit_unboundedV35 hx hnz hlt).elim
  | revert hnz hlt ha =>
    cases h2 with
    | exit hx => exact (not_test_of_exit_unboundedV35 hx hnz hlt).elim
    | revert _ _ _ => rfl
    | hop _ _ ha' _ _ _ => exact absurd ha ha'
  | hop hnz hlt ha hL hkey _ ih =>
    cases h2 with
    | exit hx => exact (not_test_of_exit_unboundedV35 hx hnz hlt).elim
    | revert _ _ ha' => exact absurd ha' ha
    | hop _ _ _ hL' hkey' hw' =>
      obtain rfl := hinj _ hL _ hL' (hkey.trans hkey'.symm)
      exact ih hw'

/-- A successful run of the pin's counted loop is a v35 walk that fits in the attempts left. -/
private theorem walk_of_boundedWalkV35_some {s : Finset AbsLeaf} {v : UInt256} {bound : ℕ} :
    ∀ {a : ℕ} {W₀ : AbsLeaf} {r : Option AbsLeaf}, BoundedWalkV35 s v bound a W₀ r →
      ∀ W : AbsLeaf, r = some W → a ≤ bound → ∃ n, WalkV35 s v n W₀ W ∧ a + n ≤ bound := by
  intro a W₀ r h
  induction h with
  | exit hx =>
    intro W hr ha
    cases hr
    exact ⟨0, WalkV35.exit hx, by omega⟩
  | revert _ _ _ =>
    intro W hr
    cases hr
  | hop hnz hlt ha hL hkey _ ih =>
    intro W hr hab
    obtain ⟨n, hw, hn⟩ := ih W hr (by omega)
    exact ⟨n + 1, WalkV35.hop hnz hlt hL hkey hw, by omega⟩

theorem BoundedWalkRevertsIffGapExceedsV35 : Properties.BoundedWalkRevertsIffGapExceedsV35 := by
  intro s v bound W₀ hs hW₀
  obtain ⟨n, W, hw, _⟩ := WalkTerminatesV35 s v W₀ hs.2.2.1 hs.2.2.2 hW₀
  have hgap := WalkLengthIsGapV35 s v n W₀ W hs.1 hs.2.2.2 hW₀ hw
  have htr := BoundedWalkIsTruncatedWalkV35 s v bound n W₀ W hw
  refine ⟨⟨fun hnone => ?_, fun hlt => htr.2 (by omega)⟩, fun W' => ⟨fun hsome => ?_, ?_⟩⟩
  · by_contra hle
    have hsome := htr.1 (by omega)
    cases boundedWalkV35_deterministic hs.2.1 hnone hsome
  · obtain ⟨n', hw', hn'⟩ := walk_of_boundedWalkV35_some hsome W' rfl (Nat.zero_le _)
    have := WalkLengthIsGapV35 s v n' W₀ W' hs.1 hs.2.2.2 hW₀ hw'
    exact ⟨by omega, n', hw'⟩
  · rintro ⟨hle, n', hw'⟩
    have := WalkLengthIsGapV35 s v n' W₀ W' hs.1 hs.2.2.2 hW₀ hw'
    exact (BoundedWalkIsTruncatedWalkV35 s v bound n' W₀ W' hw').1 (by omega)

/-! ## Witnesses

The walks are not built hop by hop: on a sound set, the walk from a hint ends at the straddling
leaf (`WalkFindsLowLeafV35`) after the gap's number of hops (`WalkLengthIsGapV35`), and both are
computed by `decide` on the small sets. -/

/-- On a sound set, the walk from a hint below an absent `v` reaches any straddling leaf, in the
gap's number of hops. -/
private theorem walkV35_to_straddler {s : Finset AbsLeaf} {v : UInt256} {W₀ R : AbsLeaf}
    (hs : SoundState s) (habs : v ∉ keys s) (hW₀ : W₀ ∈ s) (hlt : W₀.key < v)
    (hR : R ∈ s) (hRlt : R.key < v) (hRw : R.nextKey = 0 ∨ v < R.nextKey) :
    WalkV35 s v (gapKeysV35 s W₀.key v).card W₀ R := by
  obtain ⟨n, W, hw, _⟩ := WalkTerminatesV35 s v W₀ hs.2.2.1 hs.2.2.2 hW₀
  have hn := WalkLengthIsGapV35 s v n W₀ W hs.1 hs.2.2.2 hW₀ hw
  obtain ⟨_, _, _, huniq⟩ := WalkFindsLowLeafV35 s v n W₀ W hs habs hW₀ hlt hw
  rw [← hn, huniq R hR hRlt hRw]
  exact hw

/-- On a sound set, the insert of an absent nonzero `v` through a hint below it retargets any
straddling leaf. -/
private theorem insertV35_through_straddler {s : Finset AbsLeaf} {v : UInt256} {W₀ R : AbsLeaf}
    (hs : SoundState s) (hv0 : v ≠ 0) (habs : v ∉ keys s) (hW₀ : W₀ ∈ s) (hlt : W₀.key < v)
    (hR : R ∈ s) (hRlt : R.key < v) (hRw : R.nextKey = 0 ∨ v < R.nextKey) :
    InsertV35 s v W₀ (imtInsert s R v) :=
  InsertV35.mk hv0 habs hW₀ hlt (walkV35_to_straddler hs habs hW₀ hlt hR hRlt hRw)

/-- The facts each step of `chainRunV35` needs, by computation. -/
private theorem chainSetV35_step_facts (k : ℕ) (hk : k < 7) :
    SoundState (chainSetV35 k) ∧ ((k + 1 : ℕ) : UInt256) ∉ keys (chainSetV35 k)
      ∧ (⟨(k : UInt256), 0⟩ : AbsLeaf) ∈ chainSetV35 k ∧ (k : UInt256) < ((k + 1 : ℕ) : UInt256)
      ∧ ((k + 1 : ℕ) : UInt256) ≠ 0 ∧ ∃ W₀ ∈ chainSetV35 k, W₀.key = 0 := by
  interval_cases k <;> (unfold SoundState GapSound KeyInj NextClosed WindowPos; decide)

/-- Step `k < 7` of the chain: the insert of `k + 1` through the key-0 leaf. -/
private theorem chainSetV35_insert (k : ℕ) (hk : k < 7) :
    ∃ W₀ ∈ chainSetV35 k, W₀.key = 0
      ∧ InsertV35 (chainSetV35 k) ((k + 1 : ℕ) : UInt256) W₀ (chainSetV35 (k + 1)) := by
  obtain ⟨hs, habs, hR, hRlt, hv0, W₀, hW₀, hW₀k⟩ := chainSetV35_step_facts k hk
  refine ⟨W₀, hW₀, hW₀k, ?_⟩
  exact insertV35_through_straddler hs hv0 habs hW₀
    (by rw [hW₀k]; exact Fin.pos_of_ne_zero hv0) hR hRlt (Or.inl rfl)

private theorem chainRunV35_of_le {n : ℕ} (h : n ≤ 7) : chainRunV35 n = chainSetV35 n := by
  unfold chainRunV35
  rw [Nat.min_eq_left h]

private theorem chainRunV35_of_ge {n : ℕ} (h : 7 ≤ n) : chainRunV35 n = chainSetV35 7 := by
  unfold chainRunV35
  rw [Nat.min_eq_right h]

/-- The six-hop walk of `PinBoundRevertsWhereV35InsertsV35`. -/
private theorem chainSetV35_six_walk : WalkV35 (chainSetV35 6) 7 6 ⟨0, 1⟩ ⟨6, 0⟩ := by
  have hs := (chainSetV35_step_facts 6 (by omega)).1
  have h := walkV35_to_straddler (s := chainSetV35 6) (v := 7) (W₀ := ⟨0, 1⟩) (R := ⟨6, 0⟩) hs
    (by decide) (by decide) (by decide) (by decide) (by decide) (Or.inl rfl)
  have hcard : (gapKeysV35 (chainSetV35 6) (⟨0, 1⟩ : AbsLeaf).key 7).card = 6 := by decide
  rw [hcard] at h
  exact h

theorem PinBoundRevertsWhereV35InsertsV35 : Properties.PinBoundRevertsWhereV35InsertsV35 := by
  have hs := (chainSetV35_step_facts 6 (by omega)).1
  have hmem : (⟨0, 1⟩ : AbsLeaf) ∈ chainSetV35 6 := by decide
  have habs : (7 : UInt256) ∉ keys (chainSetV35 6) := by decide
  have hcard : (gapKeysV35 (chainSetV35 6) (⟨0, 1⟩ : AbsLeaf).key 7).card = 6 := by decide
  have hw := chainSetV35_six_walk
  refine ⟨hs, hmem, habs, hcard, hw, InsertV35.mk (by decide) habs hmem (by decide) hw,
    (BoundedWalkIsTruncatedWalkV35 _ _ _ _ _ _ hw).2 (by decide), ?_⟩
  intro W h
  obtain ⟨hle, _⟩ :=
    ((BoundedWalkRevertsIffGapExceedsV35 _ 7 pinSearchAttemptsV35 _ hs hmem).2 W).1 h
  rw [hcard] at hle
  exact absurd hle (by decide)

theorem WalkPremisesSatisfiableV35 : Properties.WalkPremisesSatisfiableV35 := by
  have hs : SoundState (chainSetV35 2) := (chainSetV35_step_facts 2 (by omega)).1
  have habs : (3 : UInt256) ∉ keys (chainSetV35 2) := by decide
  have h01 : (⟨0, 1⟩ : AbsLeaf) ∈ chainSetV35 2 := by decide
  have h12 : (⟨1, 2⟩ : AbsLeaf) ∈ chainSetV35 2 := by decide
  have h20 : (⟨2, 0⟩ : AbsLeaf) ∈ chainSetV35 2 := by decide
  have hcard0 : (gapKeysV35 (chainSetV35 2) (⟨0, 1⟩ : AbsLeaf).key 3).card = 2 := by decide
  have hcard1 : (gapKeysV35 (chainSetV35 2) (⟨1, 2⟩ : AbsLeaf).key 3).card = 1 := by decide
  have hw0 := walkV35_to_straddler hs habs h01 (by decide) h20 (by decide) (Or.inl rfl)
  have hw1 := walkV35_to_straddler hs habs h12 (by decide) h20 (by decide) (Or.inl rfl)
  rw [hcard0] at hw0
  rw [hcard1] at hw1
  exact ⟨hs, by decide, habs, h01, by decide, h12, by decide, h20, by decide, rfl, hcard0, hw0, hw1,
    InsertV35.mk (by decide) habs h01 (by decide) hw0,
    InsertV35.mk (by decide) habs h12 (by decide) hw1⟩

theorem InsertOrderForgottenV35 : Properties.InsertOrderForgottenV35 := by
  have hs2 : SoundState (chainSetV35 2) := (chainSetV35_step_facts 2 (by omega)).1
  have hsw : SoundState swappedSetV35 := by
    unfold SoundState GapSound KeyInj NextClosed WindowPos
    decide
  refine ⟨hs2, hsw, by decide, ?_, ?_, by decide⟩
  · exact InsertV35.mk (n := 0) (W := ⟨0, 0⟩) (by decide) (by decide) (by decide) (by decide)
      (WalkV35.exit (Or.inl rfl))
  · exact InsertV35.mk (n := 0) (W := ⟨0, 2⟩) (by decide) (by decide) (by decide) (by decide)
      (WalkV35.exit (Or.inr (by decide)))

theorem RunV35Satisfiable : Properties.RunV35Satisfiable := by
  have hins : ∀ n, n < 7 → ∃ W₀ ∈ chainRunV35 n, W₀.key = 0
      ∧ InsertV35 (chainRunV35 n) ((n + 1 : ℕ) : UInt256) W₀ (chainRunV35 (n + 1)) := by
    intro n hn
    rw [chainRunV35_of_le (by omega), chainRunV35_of_le (by omega)]
    exact chainSetV35_insert n hn
  have hidle : ∀ n, 7 ≤ n → chainRunV35 (n + 1) = chainRunV35 n := by
    intro n hn
    rw [chainRunV35_of_ge (by omega), chainRunV35_of_ge hn]
  have hrun : RunV35 chainRunV35 := by
    intro n
    by_cases hn : n < 7
    · obtain ⟨W₀, _, _, h⟩ := hins n hn
      exact Or.inr ⟨_, W₀, h⟩
    · exact Or.inl (hidle n (by omega))
  have hsteps : ∀ n, StepV35 (chainValsV35 n) (chainRunV35 n) (chainRunV35 (n + 1)) := by
    intro n
    by_cases hn : n < 7
    · have hv : chainValsV35 n = some ((n + 1 : ℕ) : UInt256) := by simp [chainValsV35, hn]
      rw [hv]
      obtain ⟨W₀, _, _, h⟩ := hins n hn
      exact ⟨W₀, h⟩
    · have hv : chainValsV35 n = none := by simp [chainValsV35, hn]
      rw [hv]
      exact hidle n (by omega)
  have hpin := PinBoundRevertsWhereV35InsertsV35
  refine ⟨hrun, by decide, hins, hidle, hsteps, ?_, ?_, by decide⟩
  · rw [chainRunV35_of_le (by omega)]
    exact hpin.2.2.2.2.1
  · rw [chainRunV35_of_le (by omega)]
    exact hpin.2.2.2.2.2.2.1

/-- The witness clock is monotone. -/
private theorem chainClockV35_monotone : Monotone chainClockV35 := by
  intro a b hab
  unfold chainClockV35
  have ha : min a 8 < UInt256.size := lt_of_le_of_lt (min_le_right a 8) (by decide)
  have hb : min b 8 < UInt256.size := lt_of_le_of_lt (min_le_right b 8) (by decide)
  rw [Fin.le_iff_val_le_val]
  show (min a 8) % UInt256.size ≤ (min b 8) % UInt256.size
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  omega

theorem RunV35PremisesMetV35 : Properties.RunV35PremisesMetV35 := by
  have hs6 : SoundState (chainSetV35 6) := (chainSetV35_step_facts 6 (by omega)).1
  refine ⟨chainClockV35_monotone, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, ?_⟩
  rw [chainRunV35_of_le (n := 6) (by omega), chainRunV35_of_le (n := 7) le_rfl]
  exact insertV35_through_straddler hs6 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (Or.inl rfl)

end IMTAbstract
