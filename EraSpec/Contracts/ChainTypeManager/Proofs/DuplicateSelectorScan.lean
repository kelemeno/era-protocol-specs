import EraSpec.Contracts.ChainTypeManager.Properties.DuplicateSelectorScan
import EraSpec.Contracts.ChainTypeManager.Proofs.LiveRouting

/-!
# Proofs: the duplicate-selector scan is exact

Linear probing without deletions. `ScanInv` says, after the selectors `P`, that every
nonempty slot holds the entry of a selector of `P`, that no entry is held twice, and that each
selector's entry sits on its probe path with every slot before it on that path occupied.

* A repeated selector's probe walks its own path, meets only occupied slots before its earlier
  entry, and reverts there at the latest (`probe_dup`).
* A new selector's probe meets no equal entry, so it stops at the first empty slot on its path
  (`probe_ins`); one exists because the table has `2·n + 1` slots and fewer than `n + 1`
  entries (`exists_empty_DuplicateSelectorScan`, by pigeonhole), and every slot is on every path (`onPath_of_lt`).
  Writing it there keeps `ScanInv` (`scanInv_insert`).
-/

namespace Contracts.ChainTypeManager

/-! ## One probe -/

lemma mod_succ_mod (a N : ℕ) : (a % N + 1) % N = (a + 1) % N := by
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- A probe that meets the same entry before any empty slot reverts. -/
lemma probe_dup {N : ℕ} {T : ℕ → ℕ} {e : ℕ} (he : e ≠ 0) :
    ∀ (n j : ℕ), (∃ i < n, T ((e + j + i) % N) = e ∧ ∀ i' < i, T ((e + j + i') % N) ≠ 0) →
      scanProbe N T e n ((e + j) % N) = none := by
  intro n
  induction n with
  | zero => rintro j ⟨i, hi, _⟩; omega
  | succ n ih =>
    rintro j ⟨i, hi, hTi, hpre⟩
    simp only [scanProbe]
    obtain _ | i'' := i
    · simp only [add_zero] at hTi
      simp [hTi, he]
    rw [ite_eq_right (by simpa using hpre 0 (by omega))]
    split_ifs with heq
    · rfl
    · rw [mod_succ_mod, show e + j + 1 = e + (j + 1) by omega]
      refine ih (j + 1) ⟨i'', by omega, ?_, fun i' hi' => ?_⟩
      · rw [show e + (j + 1) + i'' = e + j + (i'' + 1) by omega]; exact hTi
      · rw [show e + (j + 1) + i' = e + j + (i' + 1) by omega]; exact hpre _ (by omega)

/-- A probe for an entry the table does not hold ends at the first empty slot on its path,
and writes the entry there. -/
lemma probe_ins {N : ℕ} {T : ℕ → ℕ} {e : ℕ} (hnot : ∀ k, T k ≠ e) :
    ∀ (n j : ℕ), (∃ i < n, T ((e + j + i) % N) = 0) →
      ∃ i < n, T ((e + j + i) % N) = 0 ∧ (∀ i' < i, T ((e + j + i') % N) ≠ 0) ∧
        scanProbe N T e n ((e + j) % N) = some (upd T ((e + j + i) % N) e) := by
  intro n
  induction n with
  | zero => rintro j ⟨i, hi, _⟩; omega
  | succ n ih =>
    rintro j ⟨i, hi, hTi⟩
    simp only [scanProbe]
    by_cases h0 : T ((e + j) % N) = 0
    · exact ⟨0, by omega, by simpa using h0, fun i' hi' => by omega, by simp [h0]⟩
    · rw [ite_eq_right h0, ite_eq_right (hnot _)]
      obtain _ | i'' := i
      · exact absurd (by simpa using hTi) h0
      rw [mod_succ_mod, show e + j + 1 = e + (j + 1) by omega]
      obtain ⟨i₁, hi₁, hT₁, hpre₁, hres⟩ := ih (j + 1) ⟨i'', by omega, by
        rw [show e + (j + 1) + i'' = e + j + (i'' + 1) by omega]; exact hTi⟩
      refine ⟨i₁ + 1, by omega, ?_, fun i' hi' => ?_, ?_⟩
      · rw [show e + j + (i₁ + 1) = e + (j + 1) + i₁ by omega]; exact hT₁
      · obtain _ | i''' := i'
        · simpa using h0
        · rw [show e + j + (i''' + 1) = e + (j + 1) + i''' by omega]
          exact hpre₁ _ (by omega)
      · rw [hres, show e + (j + 1) + i₁ = e + j + (i₁ + 1) by omega]

/-! ## The table invariant -/

lemma scanEntry_pos (x : Selector) : scanEntry x ≠ 0 := by simp [scanEntry]

lemma scanEntry_inj {x y : Selector} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32)
    (h : scanEntry x = scanEntry y) : x = y := by
  unfold scanEntry at h
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h
  exact Nat.add_right_cancel h

/-- After the selectors `P`: every nonempty slot is a slot of the table and holds the entry of
some selector of `P`; every selector of `P` sits on its probe path with the path before it
full; and no entry is held twice. -/
structure ScanInv (N : ℕ) (T : ℕ → ℕ) (P : List Selector) : Prop where
  fromP : ∀ k, T k ≠ 0 → k < N ∧ ∃ x ∈ P, T k = scanEntry x
  onPath : ∀ x ∈ P, ∃ i < N, T ((scanEntry x + i) % N) = scanEntry x ∧
    ∀ i' < i, T ((scanEntry x + i') % N) ≠ 0
  uniq : ∀ k k', T k ≠ 0 → T k = T k' → k = k'

lemma scanInv_nil (N : ℕ) : ScanInv N (fun _ => 0) [] :=
  ⟨fun _ h => absurd rfl h, fun _ h => by simp at h, fun _ _ h => absurd rfl h⟩

lemma scanInv_not_held {N : ℕ} {T : ℕ → ℕ} {P : List Selector} {x : Selector}
    (hI : ScanInv N T P) (hb : ∀ y ∈ P, y < 2 ^ 32) (hx : x < 2 ^ 32) (hxP : x ∉ P) :
    ∀ k, T k ≠ scanEntry x := by
  intro k h
  obtain ⟨_, y, hy, hTy⟩ := hI.fromP k (by rw [h]; exact scanEntry_pos x)
  have hxy : x = y := scanEntry_inj hx (hb y hy) (h.symm.trans hTy)
  exact hxP (hxy ▸ hy)

/-- A table holding fewer entries than it has slots has an empty slot. -/
lemma exists_empty_DuplicateSelectorScan {N : ℕ} {T : ℕ → ℕ} {P : List Selector} (hI : ScanInv N T P)
    (hb : ∀ x ∈ P, x < 2 ^ 32) (hlen : P.length < N) : ∃ k < N, T k = 0 := by
  by_contra hall
  simp only [not_exists, not_and] at hall
  have hmaps : ∀ k ∈ Finset.range N, T k - 1 ∈ P.toFinset := by
    intro k hk
    obtain ⟨_, x, hx, hTk⟩ := hI.fromP k (hall k (Finset.mem_range.mp hk))
    rw [List.mem_toFinset, hTk, scanEntry, Nat.mod_eq_of_lt (hb x hx)]
    simpa using hx
  have hinj : Set.InjOn (fun k => T k - 1) (Finset.range N : Set ℕ) := by
    intro k hk k' hk' h
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    have h1 := hall k hk
    have h2 := hall k' hk'
    exact hI.uniq k k' h1 (by simp only at h; omega)
  have h1 := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_range] at h1
  have h2 := List.toFinset_card_le P
  omega

/-- Every slot is on every entry's probe path. -/
lemma onPath_of_lt {N e k : ℕ} (hk : k < N) : ∃ i < N, (e + i) % N = k := by
  have hN : 0 < N := by omega
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < N ∧ e = N * q + r :=
    ⟨e / N, e % N, Nat.mod_lt _ hN, (Nat.div_add_mod e N).symm⟩
  by_cases hkr : r ≤ k
  · refine ⟨k - r, by omega, ?_⟩
    rw [show N * q + r + (k - r) = k + N * q by omega, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt hk]
  · refine ⟨k + N - r, by omega, ?_⟩
    rw [show N * q + r + (k + N - r) = k + N * (q + 1) by rw [Nat.mul_succ]; omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

lemma scanInv_insert {N : ℕ} {T : ℕ → ℕ} {P : List Selector} {x : Selector} {i : ℕ}
    (hI : ScanInv N T P) (hb : ∀ y ∈ P, y < 2 ^ 32) (hx : x < 2 ^ 32) (hxP : x ∉ P)
    (hN : 0 < N) (hi : i < N) (hT0 : T ((scanEntry x + i) % N) = 0)
    (hpre : ∀ i' < i, T ((scanEntry x + i') % N) ≠ 0) :
    ScanInv N (upd T ((scanEntry x + i) % N) (scanEntry x)) (P ++ [x]) := by
  have hkN : (scanEntry x + i) % N < N := Nat.mod_lt _ hN
  have hnot := scanInv_not_held hI hb hx hxP
  constructor
  · intro k' hk'
    by_cases hkk : k' = (scanEntry x + i) % N
    · rw [hkk]; exact ⟨hkN, x, by simp, by simp⟩
    · rw [upd_ne _ _ hkk] at hk' ⊢
      obtain ⟨h1, y, hy, h2⟩ := hI.fromP k' hk'
      exact ⟨h1, y, List.mem_append_left _ hy, h2⟩
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨j, hj, hTj, hprej⟩ := hI.onPath y hy
      have hslot : (scanEntry y + j) % N ≠ (scanEntry x + i) % N := by
        intro he; rw [he, hT0] at hTj; exact scanEntry_pos y hTj.symm
      refine ⟨j, hj, by rw [upd_ne _ _ hslot]; exact hTj, fun i' hi' => ?_⟩
      by_cases hs : (scanEntry y + i') % N = (scanEntry x + i) % N
      · rw [hs, upd_same]; exact scanEntry_pos x
      · rw [upd_ne _ _ hs]; exact hprej i' hi'
    · simp only [List.mem_singleton] at hy
      subst hy
      refine ⟨i, hi, by rw [upd_same], fun i' hi' => ?_⟩
      by_cases hs : (scanEntry y + i') % N = (scanEntry y + i) % N
      · rw [hs, upd_same]; exact scanEntry_pos _
      · rw [upd_ne _ _ hs]; exact hpre i' hi'
  · intro k₁ k₂ h1 h12
    by_cases hk1 : k₁ = (scanEntry x + i) % N <;> by_cases hk2 : k₂ = (scanEntry x + i) % N
    · rw [hk1, hk2]
    · rw [hk1, upd_same, upd_ne _ _ hk2] at h12; exact absurd h12.symm (hnot k₂)
    · rw [hk2, upd_same, upd_ne _ _ hk1] at h12; exact absurd h12 (hnot k₁)
    · rw [upd_ne _ _ hk1] at h1 h12; rw [upd_ne _ _ hk2] at h12; exact hI.uniq k₁ k₂ h1 h12

/-! ## The scan -/

lemma scanLoop_iff {N : ℕ} (hN : 0 < N) :
    ∀ (rest P : List Selector) (T : ℕ → ℕ), ScanInv N T P → P.Nodup →
      (P ++ rest).length < N → (∀ x ∈ P ++ rest, x < 2 ^ 32) →
      ((scanLoop N T rest).isSome ↔ (P ++ rest).Nodup) := by
  intro rest
  induction rest with
  | nil => intro P T _ hnd _ _; simp [scanLoop, hnd]
  | cons x rest ih =>
    intro P T hI hnd hlen hb
    have hbP : ∀ y ∈ P, y < 2 ^ 32 := fun y hy => hb y (List.mem_append_left _ hy)
    have hx : x < 2 ^ 32 := hb x (by simp)
    simp only [scanLoop]
    by_cases hxP : x ∈ P
    · -- a repeated selector: its probe meets its own earlier entry
      obtain ⟨i, hi, hTi, hpre⟩ := hI.onPath x hxP
      have hnone : scanProbe N T (scanEntry x) N (scanEntry x % N) = none := by
        have := probe_dup (N := N) (T := T) (scanEntry_pos x) N 0
          ⟨i, hi, by simpa using hTi, fun i' hi' => by simpa using hpre i' hi'⟩
        simpa using this
      rw [hnone]
      simp only [Option.bind_none, Option.isSome_none, Bool.false_eq_true, false_iff]
      intro hnd'
      rw [List.nodup_append] at hnd'
      exact hnd'.2.2 x hxP x List.mem_cons_self rfl
    · -- a new selector: its probe ends at an empty slot, which exists
      obtain ⟨k, hk, hTk⟩ := exists_empty_DuplicateSelectorScan hI hbP (by simp at hlen; omega)
      obtain ⟨i0, hi0, hik⟩ := onPath_of_lt (e := scanEntry x) hk
      obtain ⟨i, hi, hT0, hpre, hres⟩ := probe_ins (N := N) (T := T) (e := scanEntry x)
        (scanInv_not_held hI hbP hx hxP) N 0 ⟨i0, hi0, by simpa [hik] using hTk⟩
      simp only [add_zero] at hT0 hpre hres
      rw [hres, Option.bind_some]
      have hI' := scanInv_insert hI hbP hx hxP hN hi hT0 hpre
      have hnd' : (P ++ [x]).Nodup := by simpa using hnd.concat hxP
      have := ih (P ++ [x]) _ hI' hnd' (by simpa using hlen) (by simpa using hb)
      rw [this, List.append_assoc, List.singleton_append]

theorem noDuplicateScan_iff (routing : List (List Selector))
    (hb : ∀ x ∈ routing.flatten, x < 2 ^ 32) :
    NoDuplicateScanPasses routing ↔ routing.flatten.Nodup := by
  unfold NoDuplicateScanPasses
  have := scanLoop_iff (N := 2 * routing.flatten.length + 1) (by omega) routing.flatten []
    (fun _ => 0) (scanInv_nil _) List.nodup_nil (by simp; omega) (by simpa using hb)
  simpa using this

theorem validateRows_iff (sel : Address → List Selector) (rows : List FacetRow)
    (hb : ∀ fb ∈ rows, ∀ x ∈ sel fb.1, x < 2 ^ 32) :
    ValidateRowsPasses sel rows ↔ RowsWf sel rows := by
  have hflat : (rows.map fun fb => sel fb.1).flatten = rows.flatMap fun fb => sel fb.1 := by
    simp [List.flatMap]
  unfold ValidateRowsPasses
  rw [noDuplicateScan_iff _ (by
    rw [hflat]; intro x hx
    obtain ⟨fb, hfb, hx⟩ := List.mem_flatMap.mp hx
    exact hb fb hfb x hx), hflat]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h2⟩⟩


/-! ## The properties -/

theorem DuplicateScanIffNodup : Properties.DuplicateScanIffNodup :=
  fun routing hb => noDuplicateScan_iff routing hb

theorem ValidateRowsIffRowsWf : Properties.ValidateRowsIffRowsWf :=
  fun sel rows hb => validateRows_iff sel rows hb

theorem CountCheckExactAfterValidate : Properties.CountCheckExactAfterValidate :=
  fun _ _ _ hI hb hv => countCheck_iff hI ((validateRows_iff _ _ hb).mp hv)

attribute [local instance 2000] List.decidableBAll

theorem DuplicateScanWitness : Properties.DuplicateScanWitness := by
  refine ⟨by decide, ?_, ?_, ?_, by decide, ⟨by decide, ?_⟩,
    ⟨_, rfl, diamondCut_ok (newChainInstallations wDWorld 100) _ _ fresh_ok rfl, by decide⟩⟩
  all_goals unfold NoDuplicateScanPasses; decide

end Contracts.ChainTypeManager
