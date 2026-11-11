import EraSpec.Contracts.ChainTypeManager.Properties.DuplicateSelectorCheck
import EraSpec.Contracts.ChainTypeManager.Proofs.VersionRegistry

/-!
# Proofs: `_requireNoDuplicateSelectors` is exactly `ReleaseWf`

The standard linear-probing invariant (`ProbeInv`) carries the proof. The table holds exactly
the entries of the selectors inserted so far, each in one slot. Each entry sits a number of
steps from its home slot `entry % n`, with every slot on the way occupied. A probe for a stored
entry therefore walks to it and reverts (`probe_hit`). A probe for a new entry stops at the
first empty slot (`probe_empty`), and there is one, because the table has more slots than
entries (`exists_empty`). Storing the new entry there keeps the invariant
(`insertSelector_spec`). The two outer loops are one loop over the flattened lists
(`insertRouting_eq`).
-/

namespace Contracts.ChainTypeManager

/-! ## The probe -/

/-- A probe walks to a slot holding its entry, through occupied slots holding other values, and
reverts there. Offsets are counted from the home slot `h`; the probe starts `k` steps in. -/
lemma probe_hit {T : ProbeTable} {n e h : ℕ} (he : e ≠ 0) :
    ∀ (d k fuel : ℕ), d < fuel →
      (∀ d' < d, T ((h + (k + d')) % n) ≠ 0 ∧ T ((h + (k + d')) % n) ≠ e) →
      T ((h + (k + d)) % n) = e → probeSlot T n e ((h + k) % n) fuel = none := by
  intro d
  induction d with
  | zero =>
    intro k fuel hf _ hT
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [Nat.add_zero] at hT
    simp [probeSlot, hT, he]
  | succ d ih =>
    intro k fuel hf hpre hT
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨h0, h0e⟩ := hpre 0 (by omega)
    simp only [Nat.add_zero] at h0 h0e
    simp only [probeSlot, h0, h0e, ite_false]
    rw [Nat.mod_add_mod, Nat.add_assoc]
    apply ih (k + 1) f (by omega)
    · intro d' hd'
      have := hpre (d' + 1) (by omega)
      rwa [show k + (d' + 1) = k + 1 + d' by omega] at this
    · rwa [show k + (d + 1) = k + 1 + d by omega] at hT

/-- A probe walks through occupied slots holding other values and stops at the first empty
slot. -/
lemma probe_empty {T : ProbeTable} {n e h : ℕ} :
    ∀ (d k fuel : ℕ), d < fuel →
      (∀ d' < d, T ((h + (k + d')) % n) ≠ 0 ∧ T ((h + (k + d')) % n) ≠ e) →
      T ((h + (k + d)) % n) = 0 →
      probeSlot T n e ((h + k) % n) fuel = some ((h + (k + d)) % n) := by
  intro d
  induction d with
  | zero =>
    intro k fuel hf _ hT
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    simp only [Nat.add_zero] at hT ⊢
    simp [probeSlot, hT]
  | succ d ih =>
    intro k fuel hf hpre hT
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    obtain ⟨h0, h0e⟩ := hpre 0 (by omega)
    simp only [Nat.add_zero] at h0 h0e
    simp only [probeSlot, h0, h0e, ite_false]
    rw [Nat.mod_add_mod, Nat.add_assoc, show k + (d + 1) = k + 1 + d by omega]
    apply ih (k + 1) f (by omega)
    · intro d' hd'
      have := hpre (d' + 1) (by omega)
      rwa [show k + (d' + 1) = k + 1 + d' by omega] at this
    · rwa [show k + (d + 1) = k + 1 + d by omega] at hT

/-- Within one cycle, distinct offsets from the same home slot are distinct slots. -/
lemma offset_inj {h a b n : ℕ} (ha : a < n) (hb : b < n) (hab : (h + a) % n = (h + b) % n) :
    a = b := by
  have hm : a ≡ b [MOD n] := Nat.ModEq.add_left_cancel' h hab
  unfold Nat.ModEq at hm
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at hm

/-! ## The linear-probing invariant -/

/-- After inserting the selectors `S` into a table of `n` slots, the table holds exactly the
entries `x + 1` for `x ∈ S`, each in one slot below `n`. Each is a number of steps below `n`
from its home slot `(x + 1) % n`, and every slot on the way is occupied. -/
structure ProbeInv (n : ℕ) (T : ProbeTable) (S : List Selector) : Prop where
  support : ∀ j, T j ≠ 0 → j < n
  mem : ∀ j, T j ≠ 0 → ∃ x ∈ S, T j = x + 1
  stored : ∀ x ∈ S, ∃ j, T j = x + 1
  uniq : ∀ j k, T j ≠ 0 → T j = T k → j = k
  cluster : ∀ j, T j ≠ 0 →
    ∃ d < n, j = (T j % n + d) % n ∧ ∀ d' < d, T ((T j % n + d') % n) ≠ 0
  nodup : S.Nodup

lemma probeInv_empty (n : ℕ) : ProbeInv n (fun _ => 0) [] where
  support := fun _ h => absurd rfl h
  mem := fun _ h => absurd rfl h
  stored := fun _ h => absurd h List.not_mem_nil
  uniq := fun _ _ h => absurd rfl h
  cluster := fun _ h => absurd rfl h
  nodup := List.nodup_nil

/-- A table holding fewer entries than it has slots has an empty slot. -/
lemma exists_empty {n : ℕ} {T : ProbeTable} {S : List Selector} (hI : ProbeInv n T S)
    (hlt : S.length < n) : ∃ j < n, T j = 0 := by
  by_contra hnone
  have hall : ∀ j < n, T j ≠ 0 := fun j hj h0 => hnone ⟨j, hj, h0⟩
  have hmaps : Set.MapsTo (fun j => T j - 1) ↑(Finset.range n) ↑S.toFinset := by
    intro j hj
    obtain ⟨x, hx, hTx⟩ := hI.mem j (hall j (Finset.mem_range.mp hj))
    rw [Finset.mem_coe, List.mem_toFinset]
    show T j - 1 ∈ S
    rw [hTx, Nat.add_sub_cancel]
    exact hx
  have hinj : Set.InjOn (fun j => T j - 1) ↑(Finset.range n) := by
    intro j hj k hk hjk
    have hj0 := hall j (Finset.mem_range.mp hj)
    have hk0 := hall k (Finset.mem_range.mp hk)
    apply hI.uniq j k hj0
    simp only at hjk
    omega
  have hcard := Finset.card_le_card_of_injOn (fun j => T j - 1) hmaps hinj
  rw [Finset.card_range] at hcard
  have := List.toFinset_card_le S
  omega

/-- From any home slot, some offset below `n` reaches the first empty slot. -/
lemma exists_first_empty {n : ℕ} {T : ProbeTable} {h : ℕ} (hh : h < n)
    (hex : ∃ j < n, T j = 0) :
    ∃ d < n, T ((h + d) % n) = 0 ∧ ∀ d' < d, T ((h + d') % n) ≠ 0 := by
  obtain ⟨j, hj, hT⟩ := hex
  have hP : ∃ d, d < n ∧ T ((h + d) % n) = 0 := by
    by_cases hhj : h ≤ j
    · exact ⟨j - h, by omega, by rw [show h + (j - h) = j by omega, Nat.mod_eq_of_lt hj]; exact hT⟩
    · refine ⟨j + n - h, by omega, ?_⟩
      rw [show h + (j + n - h) = j + n by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
      exact hT
  refine ⟨Nat.find hP, (Nat.find_spec hP).1, (Nat.find_spec hP).2, fun d' hd' hT' => ?_⟩
  exact Nat.find_min hP hd' ⟨by have := (Nat.find_spec hP).1; omega, hT'⟩

/-! ## One insertion -/

lemma insertSelector_spec {n : ℕ} {T : ProbeTable} {S : List Selector} {x : Selector}
    (hI : ProbeInv n T S) (hn : 0 < n) (hlt : S.length < n) :
    (x ∈ S → insertSelector n T x = none) ∧
    (x ∉ S → ∃ T', insertSelector n T x = some T' ∧ ProbeInv n T' (S ++ [x])) := by
  have hh : (x + 1) % n < n := Nat.mod_lt _ hn
  have hstart : (x + 1) % n = ((x + 1) % n + 0) % n := by simp
  constructor
  · -- a stored selector: the probe walks to its slot and reverts
    intro hx
    obtain ⟨j, hj⟩ := hI.stored x hx
    have hj0 : T j ≠ 0 := by rw [hj]; omega
    obtain ⟨d, hd, hjd, hpre⟩ := hI.cluster j hj0
    rw [hj] at hjd hpre
    have hnone : probeSlot T n (x + 1) (((x + 1) % n + 0) % n) n = none := by
      refine probe_hit (by omega) d 0 n hd (fun d' hd' => ⟨?_, fun hT' => ?_⟩) ?_
      · rw [Nat.zero_add]; exact hpre d' hd'
      · rw [Nat.zero_add] at hT'
        have := hI.uniq _ _ (by rw [hT']; omega) (hT'.trans hj.symm)
        rw [hjd] at this
        have := offset_inj (by omega) hd this
        omega
      · rw [Nat.zero_add, ← hjd]; exact hj
    unfold insertSelector
    rw [← hstart] at hnone
    rw [hnone]
    rfl
  · -- a new selector: the probe stops at the first empty slot, where the entry is stored
    intro hx
    obtain ⟨d, hd, hT0, hpre⟩ := exists_first_empty hh (exists_empty hI hlt)
    set j' := ((x + 1) % n + d) % n with hj'
    have hsome : probeSlot T n (x + 1) (((x + 1) % n + 0) % n) n = some j' := by
      have := probe_empty (T := T) (n := n) (e := x + 1) (h := (x + 1) % n) d 0 n hd
        (fun d' hd' => ⟨by rw [Nat.zero_add]; exact hpre d' hd', fun hT' => ?_⟩)
        (by rw [Nat.zero_add]; exact hT0)
      · rwa [Nat.zero_add] at this
      · rw [Nat.zero_add] at hT'
        obtain ⟨y, hy, hTy⟩ := hI.mem _ (by rw [hT']; exact Nat.add_one_ne_zero x)
        rw [hT'] at hTy
        exact hx (by rw [Nat.add_right_cancel hTy]; exact hy)
    refine ⟨upd T j' (x + 1), ?_, ?_⟩
    · unfold insertSelector
      rw [← hstart] at hsome
      rw [hsome]
      rfl
    · -- the invariant for the extended table
      have hj'n : j' < n := Nat.mod_lt _ hn
      have hgrow : ∀ k, T k ≠ 0 → upd T j' (x + 1) k ≠ 0 := by
        intro k hk
        by_cases hkj : k = j' <;> simp [upd, hkj, hk]
      refine ⟨fun k hk => ?_, fun k hk => ?_, fun y hy => ?_, fun k l hk hkl => ?_, fun k hk => ?_,
        ?_⟩
      · -- support
        by_cases hkj : k = j'
        · rw [hkj]; exact hj'n
        · rw [upd_ne _ _ hkj] at hk; exact hI.support k hk
      · -- mem
        by_cases hkj : k = j'
        · exact ⟨x, by simp, by rw [hkj, upd_same]⟩
        · rw [upd_ne _ _ hkj] at hk ⊢
          obtain ⟨y, hy, hTy⟩ := hI.mem k hk
          exact ⟨y, List.mem_append_left _ hy, hTy⟩
      · -- stored
        rcases List.mem_append.mp hy with hy | hy
        · obtain ⟨k, hk⟩ := hI.stored y hy
          have hkj : k ≠ j' := by
            rintro rfl
            rw [hT0] at hk
            omega
          exact ⟨k, by rw [upd_ne _ _ hkj]; exact hk⟩
        · rw [List.mem_singleton] at hy
          exact ⟨j', by rw [hy, upd_same]⟩
      · -- uniq
        have hval : ∀ m, m ≠ j' → upd T j' (x + 1) m ≠ x + 1 := by
          intro m hm hTm
          rw [upd_ne _ _ hm] at hTm
          obtain ⟨y, hy, hTy⟩ := hI.mem m (by rw [hTm]; exact Nat.add_one_ne_zero x)
          rw [hTm] at hTy
          exact hx (by rw [Nat.add_right_cancel hTy]; exact hy)
        by_cases hkj : k = j'
        · by_cases hlj : l = j'
          · rw [hkj, hlj]
          · rw [hkj, upd_same] at hkl
            exact absurd hkl.symm (hval l hlj)
        · by_cases hlj : l = j'
          · rw [hlj, upd_same] at hkl
            exact absurd hkl (hval k hkj)
          · rw [upd_ne _ _ hkj] at hk hkl
            rw [upd_ne _ _ hlj] at hkl
            exact hI.uniq k l hk hkl
      · -- cluster
        by_cases hkj : k = j'
        · subst hkj
          rw [upd_same]
          exact ⟨d, hd, rfl, fun d' hd' => hgrow _ (hpre d' hd')⟩
        · have hk' := hk
          rw [upd_ne _ _ hkj] at hk' ⊢
          obtain ⟨d0, hd0, hk0, hpre0⟩ := hI.cluster k hk'
          exact ⟨d0, hd0, hk0, fun d' hd' => hgrow _ (hpre0 d' hd')⟩
      · -- nodup
        simpa using hI.nodup.concat hx

/-! ## The loops -/

lemma insertSelectors_ok {n : ℕ} (hn : 0 < n) :
    ∀ (xs : List Selector) (T : ProbeTable) (S : List Selector), ProbeInv n T S →
      S.length + xs.length < n → (S ++ xs).Nodup →
      ∃ T', insertSelectors n T xs = some T' ∧ ProbeInv n T' (S ++ xs) := by
  intro xs
  induction xs with
  | nil => intro T S hI _ _; exact ⟨T, rfl, by simpa using hI⟩
  | cons x xs ih =>
    intro T S hI hlen hnd
    have hx : x ∉ S := fun hm => (List.nodup_append.mp hnd).2.2 x hm x List.mem_cons_self rfl
    obtain ⟨T', hT', hI'⟩ := (insertSelector_spec (x := x) hI hn (by simp at hlen; omega)).2 hx
    obtain ⟨T'', hT'', hI''⟩ := ih T' (S ++ [x]) hI' (by simp at hlen ⊢; omega)
      (by simpa using hnd)
    refine ⟨T'', ?_, by simpa using hI''⟩
    simp only [insertSelectors, hT', Option.bind_some, hT'']

lemma insertSelectors_none {n : ℕ} (hn : 0 < n) :
    ∀ (xs : List Selector) (T : ProbeTable) (S : List Selector), ProbeInv n T S →
      S.length + xs.length < n → ¬ (S ++ xs).Nodup → insertSelectors n T xs = none := by
  intro xs
  induction xs with
  | nil => intro T S hI _ hnd; exact absurd (by simpa using hI.nodup) hnd
  | cons x xs ih =>
    intro T S hI hlen hnd
    by_cases hx : x ∈ S
    · simp only [insertSelectors, (insertSelector_spec hI hn (by simp at hlen; omega)).1 hx,
        Option.bind_none]
    · obtain ⟨T', hT', hI'⟩ := (insertSelector_spec (x := x) hI hn (by simp at hlen; omega)).2 hx
      simp only [insertSelectors, hT', Option.bind_some]
      exact ih T' (S ++ [x]) hI' (by simp at hlen ⊢; omega) (by simpa using hnd)

lemma insertSelectors_append (n : ℕ) :
    ∀ (xs ys : List Selector) (T : ProbeTable),
      insertSelectors n T (xs ++ ys) =
        (insertSelectors n T xs).bind (fun T' => insertSelectors n T' ys) := by
  intro xs
  induction xs with
  | nil => intro ys T; rfl
  | cons x xs ih =>
    intro ys T
    simp only [List.cons_append, insertSelectors, Option.bind_assoc, ih]

/-- The two nested loops are one loop over the flattened lists. -/
lemma insertRouting_eq (n : ℕ) :
    ∀ (routing : List (List Selector)) (T : ProbeTable),
      insertRouting n T routing = insertSelectors n T routing.flatten := by
  intro routing
  induction routing with
  | nil => intro T; rfl
  | cons sels rest ih =>
    intro T
    simp only [insertRouting, List.flatten_cons, insertSelectors_append, ih]

/-! ## The results -/

theorem DuplicateCheckExactForAnyLargerTable :
    Properties.DuplicateCheckExactForAnyLargerTable := by
  intro routing n hn
  have hlen : routing.flatten.length < n := by
    rw [List.length_flatten]; exact hn
  have hn0 : 0 < n := by omega
  rw [insertRouting_eq]
  constructor
  · intro hs
    by_contra hnd
    have := insertSelectors_none hn0 routing.flatten _ [] (probeInv_empty n) (by simpa using hlen)
      (by simpa using hnd)
    simp [this] at hs
  · intro hnd
    obtain ⟨T', hT', -⟩ := insertSelectors_ok hn0 routing.flatten _ [] (probeInv_empty n)
      (by simpa using hlen) (by simpa using hnd)
    rw [hT']
    rfl

theorem DuplicateCheckIsExact : Properties.DuplicateCheckIsExact := by
  intro routing
  exact DuplicateCheckExactForAnyLargerTable routing _ (by omega)

theorem ReleaseWfIsTheDuplicateCheck : Properties.ReleaseWfIsTheDuplicateCheck := by
  intro W r routing h
  unfold ReleaseWf
  rw [h, DuplicateCheckIsExact]

theorem DuplicateCheckWitness : Properties.DuplicateCheckWitness := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end Contracts.ChainTypeManager
