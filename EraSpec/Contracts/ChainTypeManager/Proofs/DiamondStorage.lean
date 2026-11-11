import EraSpec.Contracts.ChainTypeManager.Properties.DiamondStorage
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainRouting

/-!
# Proofs: `Diamond.diamondCut` keeps a diamond's storage consistent

`DiamondOk` is stated position by position: each list entry points back at its index, and
each routed selector or listed facet sits at its recorded index. That form makes the
swap-and-pop removals tractable: `ok_removeKeep` covers both branches of
`_removeOneFunction` for a facet that keeps a selector (when the removed selector is last, the
"moved" one is itself), and `ok_removeDrop` the branch that also runs `_removeFacet`. Adding
goes through `ok_addNew` / `ok_addOld`; `_saveFacetIfNew` briefly lists a facet with no
selectors, so it is handled together with the first `_addOneFunction` (`addOne_save_ok`).

The routing lemmas need no invariant at all: routing reads only `selectorToFacet`, and every
writer changes at most the one selector it names (positions aside).
-/

namespace Contracts.ChainTypeManager

/-! ## Reading the invariant -/

lemma DiamondOk.mem_sels {ds : DiamondStorage} (hI : DiamondOk ds) {f : Address} {x : Selector} :
    x ∈ (ds.facetToSelectors f).selectors ↔ (ds.selectorToFacet x).facetAddress = f ∧ f ≠ 0 := by
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
    have hb := (hI.selsBack f i x hi).1
    refine ⟨hb, fun h0 => ?_⟩
    subst h0
    rw [hI.zeroNoSels] at hx
    simp at hx
  · rintro ⟨hb, hf⟩
    have := hI.selsThere x (by rw [hb]; exact hf)
    rw [hb] at this
    exact List.mem_iff_getElem?.mpr ⟨_, this⟩

lemma DiamondOk.mem_facets {ds : DiamondStorage} (hI : DiamondOk ds) {f : Address} :
    f ∈ ds.facets ↔ (ds.facetToSelectors f).selectors ≠ [] := by
  constructor
  · intro hf
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hf
    exact (hI.facetsBack i f hi).2
  · intro h
    exact List.mem_iff_getElem?.mpr ⟨_, hI.facetsThere f h⟩

/-- A list whose entries determine their own index has no duplicates. -/
lemma nodup_of_index {α : Type} {l : List α} (pos : α → ℕ)
    (h : ∀ i a, l[i]? = some a → pos a = i) : l.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro i j hij
  have hi := h i _ (List.getElem?_eq_getElem i.2)
  have hj := h j _ (List.getElem?_eq_getElem j.2)
  simp only at hij
  rw [hij] at hi
  exact Fin.ext (hi.symm.trans hj)

lemma DiamondOk.facets_nodup {ds : DiamondStorage} (hI : DiamondOk ds) : ds.facets.Nodup :=
  nodup_of_index (fun f => (ds.facetToSelectors f).facetPosition)
    (fun i f h => (hI.facetsBack i f h).1)

lemma DiamondOk.sels_nodup {ds : DiamondStorage} (hI : DiamondOk ds) (f : Address) :
    (ds.facetToSelectors f).selectors.Nodup :=
  nodup_of_index (fun x => (ds.selectorToFacet x).selectorPosition)
    (fun i x h => (hI.selsBack f i x h).2)

/-! ## Adding one selector -/

lemma ok_addNew {ds : DiamondStorage} {f : Address} {x : Selector} (b : Bool)
    (hI : DiamondOk ds) (hf : f ≠ 0) (hx : (ds.selectorToFacet x).facetAddress = 0)
    (hS : (ds.facetToSelectors f).selectors = []) :
    DiamondOk ⟨upd ds.selectorToFacet x ⟨f, 0, b⟩,
      upd ds.facetToSelectors f ⟨[x], ds.facets.length⟩, ds.facets ++ [f]⟩ := by
  have hfnot : f ∉ ds.facets := by rw [hI.mem_facets, hS]; simp
  constructor
  · intro g i y hy
    by_cases hg : g = f
    · subst hg
      simp only [upd_same, List.getElem?_singleton] at hy
      split_ifs at hy with hi
      cases hy; subst hi; simp
    · simp only [upd_ne _ _ hg] at hy
      obtain ⟨h1, h2⟩ := hI.selsBack g i y hy
      have hg0 : g ≠ 0 := by
        rintro rfl; rw [hI.zeroNoSels] at hy; simp at hy
      have hyx : y ≠ x := by rintro rfl; exact hg0 (h1.symm.trans hx)
      simp only [upd_ne _ _ hyx]
      exact ⟨h1, h2⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; simp
    · simp only [upd_ne _ _ hyx] at hy ⊢
      have hthere := hI.selsThere y hy
      have hgf : (ds.selectorToFacet y).facetAddress ≠ f := by
        intro he; rw [he, hS] at hthere; simp at hthere
      rw [upd_ne _ _ hgf]
      exact hthere
  · intro i g hg
    rw [List.getElem?_append] at hg
    split_ifs at hg with hi
    · obtain ⟨h1, h2⟩ := hI.facetsBack i g hg
      have hgf : g ≠ f := by rintro rfl; exact hfnot (List.mem_of_getElem? hg)
      simp only [upd_ne _ _ hgf]
      exact ⟨h1, h2⟩
    · simp only [List.getElem?_singleton] at hg
      split_ifs at hg with hi'
      cases hg; simp; omega
  · intro g hg
    by_cases hgf : g = f
    · subst hgf; simp
    · simp only [upd_ne _ _ hgf] at hg ⊢
      have := hI.facetsThere g hg
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp this).1]
      exact this
  · simp only [upd_ne _ _ (Ne.symm hf)]
    exact hI.zeroNoSels

lemma ok_addOld {ds : DiamondStorage} {f : Address} {x : Selector} (b : Bool)
    (hI : DiamondOk ds) (hf : f ≠ 0) (hx : (ds.selectorToFacet x).facetAddress = 0)
    (hS : (ds.facetToSelectors f).selectors ≠ []) :
    DiamondOk ⟨upd ds.selectorToFacet x ⟨f, (ds.facetToSelectors f).selectors.length, b⟩,
      upd ds.facetToSelectors f
        ⟨(ds.facetToSelectors f).selectors ++ [x], (ds.facetToSelectors f).facetPosition⟩,
      ds.facets⟩ := by
  constructor
  · intro g i y hy
    by_cases hg : g = f
    · subst hg
      simp only [upd_same] at hy
      rw [List.getElem?_append] at hy
      split_ifs at hy with hi
      · obtain ⟨h1, h2⟩ := hI.selsBack g i y hy
        have hyx : y ≠ x := by rintro rfl; exact hf (h1.symm.trans hx)
        simp only [upd_ne _ _ hyx]
        exact ⟨h1, h2⟩
      · simp only [List.getElem?_singleton] at hy
        split_ifs at hy with hi'
        cases hy; simp; omega
    · simp only [upd_ne _ _ hg] at hy
      obtain ⟨h1, h2⟩ := hI.selsBack g i y hy
      have hg0 : g ≠ 0 := by
        rintro rfl; rw [hI.zeroNoSels] at hy; simp at hy
      have hyx : y ≠ x := by rintro rfl; exact hg0 (h1.symm.trans hx)
      simp only [upd_ne _ _ hyx]
      exact ⟨h1, h2⟩
  · intro y hy
    by_cases hyx : y = x
    · subst hyx; simp
    · simp only [upd_ne _ _ hyx] at hy ⊢
      have hthere := hI.selsThere y hy
      by_cases hgf : (ds.selectorToFacet y).facetAddress = f
      · rw [hgf] at hthere ⊢
        simp only [upd_same]
        rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hthere).1]
        exact hthere
      · rw [upd_ne _ _ hgf]
        exact hthere
  · intro i g hg
    obtain ⟨h1, h2⟩ := hI.facetsBack i g hg
    by_cases hgf : g = f
    · subst hgf; simp [h1]
    · simp only [upd_ne _ _ hgf]
      exact ⟨h1, h2⟩
  · intro g _
    by_cases hgf : g = f
    · subst hgf; simpa using hI.facetsThere g hS
    · simp only [upd_ne _ _ hgf] at *
      exact hI.facetsThere g (by assumption)
  · simp only [upd_ne _ _ (Ne.symm hf)]
    exact hI.zeroNoSels

/-- Saving the facet and adding one free selector keeps the invariant, and leaves the facet
with a selector. -/
lemma addOne_save_ok {ds d : DiamondStorage} {f : Address} {x : Selector} {b : Bool}
    (hI : DiamondOk ds) (hf : f ≠ 0) (hx : (ds.selectorToFacet x).facetAddress = 0)
    (h : addOneFunction (saveFacetIfNew ds f) f x b = some d) :
    DiamondOk d ∧ (d.facetToSelectors f).selectors ≠ [] := by
  by_cases hS : (ds.facetToSelectors f).selectors = []
  · have hsave : saveFacetIfNew ds f = { ds with
        facetToSelectors := upd ds.facetToSelectors f
          { ds.facetToSelectors f with facetPosition := ds.facets.length },
        facets := ds.facets ++ [f] } := by
      simp [saveFacetIfNew, hS]
    rw [hsave] at h
    simp only [addOneFunction, upd_same, hS, List.length_nil, ne_eq, not_true_eq_false,
      false_and, ite_false, Option.some.injEq] at h
    subst h
    have := ok_addNew b hI hf hx hS
    refine ⟨?_, by simp⟩
    convert this using 2
    funext g
    by_cases hg : g = f
    · subst hg; simp
    · simp [upd_ne _ _ hg]
  · have hsave : saveFacetIfNew ds f = ds := by
      simp [saveFacetIfNew, hS]
    rw [hsave] at h
    simp only [addOneFunction] at h
    split_ifs at h with hfrz
    cases h
    exact ⟨ok_addOld b hI hf hx hS, by simp⟩

/-! ## Removing one selector -/

/-- Swap-and-pop of selector `x` out of facet `f`'s list when the facet keeps at least one
selector. Covers both branches of `_removeOneFunction`: with `p = n - 1` the moved selector is
`x` itself, whose slot is deleted anyway. -/
lemma ok_removeKeep {ds : DiamondStorage} {f : Address} {x y : Selector} (S' : List Selector)
    (hI : DiamondOk ds) (hf : f ≠ 0) (hxf : (ds.selectorToFacet x).facetAddress = f)
    (hn : 2 ≤ (ds.facetToSelectors f).selectors.length)
    (hSy : (ds.facetToSelectors f).selectors[(ds.facetToSelectors f).selectors.length - 1]? =
      some y)
    (hS' : ∀ i, S'[i]? = if i < (ds.facetToSelectors f).selectors.length - 1 then
      (if i = (ds.selectorToFacet x).selectorPosition then some y
      else (ds.facetToSelectors f).selectors[i]?) else none) :
    DiamondOk ⟨upd (upd ds.selectorToFacet y
        { ds.selectorToFacet y with selectorPosition := (ds.selectorToFacet x).selectorPosition })
        x SelectorToFacet.zero,
      upd ds.facetToSelectors f ⟨S', (ds.facetToSelectors f).facetPosition⟩,
      ds.facets⟩ := by
  -- names for the pieces
  set S := (ds.facetToSelectors f).selectors with hSdef
  set n := S.length with hndef
  set p := (ds.selectorToFacet x).selectorPosition with hpdef
  have hSp : S[p]? = some x := by
    have := hI.selsThere x (by rw [hxf]; exact hf)
    rw [hxf] at this; exact this
  have hpn : p < n := (List.getElem?_eq_some_iff.mp hSp).1
  obtain ⟨hyf, hyp⟩ := hI.selsBack f (n - 1) y hSy
  have hS'ne : S' ≠ [] := by
    intro h
    have h0 := hS' 0
    rw [h, List.getElem?_nil, ite_eq_left (by omega)] at h0
    split_ifs at h0 with h0p
    rw [List.getElem?_eq_getElem (by omega)] at h0; simp at h0
  constructor
  · intro g i z hz
    by_cases hg : g = f
    · subst hg
      simp only [upd_same, hS'] at hz
      split_ifs at hz with hi hip
      · -- the moved selector
        have hyz : y = z := Option.some.inj hz
        subst hyz
        have hyx : y ≠ x := by
          intro he; rw [he] at hyp; omega
        simp only [upd_ne _ _ hyx, upd_same]
        exact ⟨hyf, hip.symm⟩
      · obtain ⟨h1, h2⟩ := hI.selsBack g i z hz
        have hzx : z ≠ x := by intro he; rw [he] at h2; exact hip h2.symm
        have hzy : z ≠ y := by intro he; rw [he] at h2; omega
        simp only [upd_ne _ _ hzx, upd_ne _ _ hzy]
        exact ⟨h1, h2⟩
    · simp only [upd_ne _ _ hg] at hz
      obtain ⟨h1, h2⟩ := hI.selsBack g i z hz
      have hzx : z ≠ x := by intro he; rw [he, hxf] at h1; exact hg h1.symm
      have hzy : z ≠ y := by intro he; rw [he, hyf] at h1; exact hg h1.symm
      simp only [upd_ne _ _ hzx, upd_ne _ _ hzy]
      exact ⟨h1, h2⟩
  · intro z hz
    by_cases hzx : z = x
    · subst hzx; simp [SelectorToFacet.zero] at hz
    · simp only [upd_ne _ _ hzx] at hz ⊢
      by_cases hzy : z = y
      · subst hzy
        simp only [upd_same, hyf] at hz ⊢
        simp only [hS']
        have hpl : p ≠ n - 1 := by
          intro he; rw [he] at hSp; rw [hSp] at hSy; exact hzx (Option.some.inj hSy).symm
        simp [show p < n - 1 by omega]
      · simp only [upd_ne _ _ hzy] at hz ⊢
        have hthere := hI.selsThere z hz
        by_cases hgf : (ds.selectorToFacet z).facetAddress = f
        · rw [hgf] at hthere ⊢
          simp only [upd_same, hS']
          set q := (ds.selectorToFacet z).selectorPosition
          have hqn : q < n := (List.getElem?_eq_some_iff.mp hthere).1
          have hqp : q ≠ p := by
            intro he; rw [he] at hthere; rw [hthere] at hSp; exact hzx (Option.some.inj hSp)
          have hql : q ≠ n - 1 := by
            intro he; rw [he] at hthere; rw [hthere] at hSy; exact hzy (Option.some.inj hSy)
          rw [ite_eq_left (by omega), ite_eq_right hqp]
          exact hthere
        · rw [upd_ne _ _ hgf]
          exact hthere
  · intro i g hg
    obtain ⟨h1, h2⟩ := hI.facetsBack i g hg
    by_cases hgf : g = f
    · subst hgf; simp only [upd_same]; exact ⟨h1, hS'ne⟩
    · simp only [upd_ne _ _ hgf]
      exact ⟨h1, h2⟩
  · intro g hg
    by_cases hgf : g = f
    · subst hgf
      simp only [upd_same]
      exact hI.facetsThere g (by
        intro h; rw [hSdef, h] at hndef; simp at hndef; omega)
    · simp only [upd_ne _ _ hgf] at hg ⊢
      exact hI.facetsThere g hg
  · simp only [upd_ne _ _ (Ne.symm hf)]
    exact hI.zeroNoSels

/-- Removing a facet's only selector and then the facet itself (swap-and-pop on `facets`),
stated through what the result reads: the facet's list is empty, the moved facet `g` records
the vacated position, and the facet list is the swapped-and-popped one. -/
lemma ok_removeDrop {ds : DiamondStorage} {f g : Address} {x : Selector}
    (T : Address → FacetToSelectors) (F' : List Address)
    (hI : DiamondOk ds) (hf : f ≠ 0) (hxf : (ds.selectorToFacet x).facetAddress = f)
    (hS : (ds.facetToSelectors f).selectors = [x])
    (hFg : ds.facets[ds.facets.length - 1]? = some g)
    (hTs : ∀ h, (T h).selectors = if h = f then [] else (ds.facetToSelectors h).selectors)
    (hTp : ∀ h, (T h).facetPosition =
      if h = g then (ds.facetToSelectors f).facetPosition
      else (ds.facetToSelectors h).facetPosition)
    (hF' : ∀ i, F'[i]? = if i < ds.facets.length - 1 then
      (if i = (ds.facetToSelectors f).facetPosition then some g else ds.facets[i]?)
      else none) :
    DiamondOk ⟨upd ds.selectorToFacet x SelectorToFacet.zero, T, F'⟩ := by
  set P := (ds.facetToSelectors f).facetPosition with hPdef
  set m := ds.facets.length with hmdef
  have hFP : ds.facets[P]? = some f := hI.facetsThere f (by rw [hS]; simp)
  have hPm : P < m := (List.getElem?_eq_some_iff.mp hFP).1
  obtain ⟨hgp, hgs⟩ := hI.facetsBack (m - 1) g hFg
  constructor
  · intro h i z hz
    simp only [hTs] at hz
    split_ifs at hz with hhf
    · simp at hz
    · obtain ⟨h1, h2⟩ := hI.selsBack h i z hz
      have hzx : z ≠ x := by intro he; rw [he, hxf] at h1; exact hhf h1.symm
      simp only [upd_ne _ _ hzx]
      exact ⟨h1, h2⟩
  · intro z hz
    by_cases hzx : z = x
    · subst hzx; simp [SelectorToFacet.zero] at hz
    · simp only [upd_ne _ _ hzx] at hz ⊢
      have hthere := hI.selsThere z hz
      have hhf : (ds.selectorToFacet z).facetAddress ≠ f := by
        intro he; rw [he, hS] at hthere
        simp only [List.getElem?_singleton] at hthere
        split_ifs at hthere
        exact hzx (Option.some.inj hthere).symm
      rw [hTs, ite_eq_right hhf]
      exact hthere
  · intro i h hh
    rw [hF'] at hh
    split_ifs at hh with him hiP
    · -- the moved facet, now at `P`
      have hgh : g = h := Option.some.inj hh
      subst hgh
      have hgf : g ≠ f := by
        intro he; rw [he] at hgp; omega
      rw [hTp, hTs, ite_eq_left rfl, ite_eq_right hgf]
      exact ⟨hiP.symm, hgs⟩
    · obtain ⟨h1, h2⟩ := hI.facetsBack i h hh
      have hhf : h ≠ f := by intro he; rw [he] at h1; exact hiP h1.symm
      have hhg : h ≠ g := by intro he; rw [he] at h1; omega
      rw [hTp, hTs, ite_eq_right hhg, ite_eq_right hhf]
      exact ⟨h1, h2⟩
  · intro h hh
    rw [hTs] at hh
    split_ifs at hh with hhf
    · exact absurd rfl hh
    by_cases hhg : h = g
    · subst hhg
      rw [hTp, ite_eq_left rfl, hF']
      have hPl : P ≠ m - 1 := by
        intro he; rw [he] at hFP; rw [hFP] at hFg; exact hhf (Option.some.inj hFg).symm
      rw [ite_eq_left (by omega), ite_eq_left rfl]
    · rw [hTp, ite_eq_right hhg, hF']
      have hthere := hI.facetsThere h hh
      set Q := (ds.facetToSelectors h).facetPosition
      have hQm : Q < m := (List.getElem?_eq_some_iff.mp hthere).1
      have hQP : Q ≠ P := by
        intro he; rw [he] at hthere; rw [hthere] at hFP; exact hhf (Option.some.inj hFP)
      have hQl : Q ≠ m - 1 := by
        intro he; rw [he] at hthere; rw [hthere] at hFg; exact hhg (Option.some.inj hFg)
      rw [ite_eq_left (by omega), ite_eq_right hQP]
      exact hthere
  · rw [hTs, ite_eq_right (Ne.symm hf)]
    exact hI.zeroNoSels

lemma upd_upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b c : β) :
    upd (upd f a b) a c = upd f a c := by
  funext z; by_cases hz : z = a <;> simp [upd, hz]

/-- **`_removeOneFunction` keeps the invariant**, for a routed selector and its own facet. -/
lemma removeOne_ok {ds d : DiamondStorage} {f : Address} {x : Selector}
    (hI : DiamondOk ds) (hf : f ≠ 0) (hxf : (ds.selectorToFacet x).facetAddress = f)
    (h : removeOneFunction ds f x = some d) : DiamondOk d := by
  have hSp : (ds.facetToSelectors f).selectors[(ds.selectorToFacet x).selectorPosition]? =
      some x := by
    have := hI.selsThere x (by rw [hxf]; exact hf)
    rw [hxf] at this; exact this
  have hpn := (List.getElem?_eq_some_iff.mp hSp).1
  unfold removeOneFunction at h
  simp only [show (ds.facetToSelectors f).selectors.length ≠ 0 by omega, ite_false] at h
  generalize hy : (ds.facetToSelectors f).selectors.getD
    ((ds.facetToSelectors f).selectors.length - 1) 0 = y at h
  have hSy : (ds.facetToSelectors f).selectors[(ds.facetToSelectors f).selectors.length - 1]? =
      some y := by
    rw [← hy, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  by_cases hpl : (ds.selectorToFacet x).selectorPosition =
      (ds.facetToSelectors f).selectors.length - 1
  · -- `x` is the last selector: no move
    have hyx : y = x := by
      rw [← hpl, hSp] at hSy; exact (Option.some.inj hSy).symm
    simp only [hpl, ite_true, Option.bind_some] at h
    by_cases hn1 : (ds.facetToSelectors f).selectors.length - 1 = 0
    · -- and the only one: the facet goes too
      simp only [hn1, ite_true] at h
      have hS : (ds.facetToSelectors f).selectors = [x] := by
        rw [hn1] at hpl
        match hL : (ds.facetToSelectors f).selectors, hSp with
        | [z], h1 => rw [hpl] at h1; simp at h1; rw [h1]
        | [], h1 => simp at h1
        | _ :: _ :: _, _ => rw [hL] at hn1; simp at hn1
      unfold removeFacet at h
      simp only [upd_same] at h
      have hFP : ds.facets[(ds.facetToSelectors f).facetPosition]? = some f :=
        hI.facetsThere f (by rw [hS]; simp)
      have hPm := (List.getElem?_eq_some_iff.mp hFP).1
      simp only [show ds.facets.length ≠ 0 by omega, ite_false] at h
      generalize hg : ds.facets.getD (ds.facets.length - 1) 0 = g at h
      have hFg : ds.facets[ds.facets.length - 1]? = some g := by
        rw [← hg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      by_cases hPl : (ds.facetToSelectors f).facetPosition = ds.facets.length - 1
      · simp only [hPl, ite_true, Option.map_some, Option.some.injEq] at h
        subst h
        have hgf : g = f := by
          rw [← hPl, hFP] at hFg; exact (Option.some.inj hFg).symm
        subst hgf
        refine ok_removeDrop _ _ hI hf hxf hS hFg ?_ ?_ ?_
        · intro k; by_cases hk : k = g <;> simp [upd, hk, hS]
        · intro k; by_cases hk : k = g <;> simp [upd, hk, hPl]
        · intro i; rw [List.getElem?_dropLast]
          split_ifs with h1 h2 <;> first | rfl | omega
      · simp only [hPl, ite_false, hPm, ite_true, Option.map_some, Option.some.injEq] at h
        subst h
        refine ok_removeDrop _ _ hI hf hxf hS hFg ?_ ?_ ?_
        · intro k
          by_cases hkg : k = g <;> by_cases hkf : k = f <;> simp_all [upd]
        · intro k
          by_cases hkg : k = g <;> by_cases hkf : k = f <;> simp_all [upd]
        · intro i; rw [List.getElem?_dropLast, List.length_set, List.getElem?_set]
          split_ifs with h1 h2 h3 <;> first | rfl | omega
    · -- other selectors remain
      simp only [hn1, ite_false, Option.some.injEq] at h
      subst h
      have := ok_removeKeep (ds := ds) (f := f) (x := x) (y := y)
        ((ds.facetToSelectors f).selectors.dropLast) hI hf hxf (by omega) hSy (by
          intro i; rw [List.getElem?_dropLast]
          split_ifs with h1 h2 <;> first | rfl | omega)
      rw [hyx, upd_upd_same] at this
      exact this
  · -- move the last selector into `x`'s slot
    simp only [hpl, ite_false, hpn, ite_true, Option.bind_some, upd_same] at h
    have hn1 : (ds.facetToSelectors f).selectors.length - 1 ≠ 0 := by omega
    simp only [hn1, ite_false, Option.some.injEq] at h
    subst h
    have := ok_removeKeep (ds := ds) (f := f) (x := x) (y := y)
      (((ds.facetToSelectors f).selectors.set (ds.selectorToFacet x).selectorPosition y).dropLast)
      hI hf hxf (by omega) hSy (by
        intro i; rw [List.getElem?_dropLast, List.length_set, List.getElem?_set]
        split_ifs with h1 h2 h3 <;> first | rfl | omega)
    convert this using 2
    rw [upd_upd_same]

/-! ## The loops and the actions -/

lemma saveFacetIfNew_s2f (ds : DiamondStorage) (f : Address) :
    (saveFacetIfNew ds f).selectorToFacet = ds.selectorToFacet := by
  unfold saveFacetIfNew; split_ifs <;> rfl

lemma saveFacetIfNew_of_ne {ds : DiamondStorage} {f : Address}
    (h : (ds.facetToSelectors f).selectors ≠ []) : saveFacetIfNew ds f = ds := by
  unfold saveFacetIfNew
  rw [ite_eq_right (by intro h0; exact h (List.eq_nil_of_length_eq_zero h0))]

lemma addLoop_ok {f : Address} {b : Bool} (hf : f ≠ 0) :
    ∀ (xs : List Selector) (d d' : DiamondStorage), DiamondOk d →
      (d.facetToSelectors f).selectors ≠ [] → addLoop d f xs b = some d' →
      DiamondOk d' ∧ (d'.facetToSelectors f).selectors ≠ [] := by
  intro xs
  induction xs with
  | nil => intro d d' hI hne h; simp [addLoop] at h; subst h; exact ⟨hI, hne⟩
  | cons x xs ih =>
    intro d d' hI hne h
    simp only [addLoop] at h
    split_ifs at h with hx
    cases h1 : addOneFunction d f x b with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      rw [← saveFacetIfNew_of_ne hne] at h1
      obtain ⟨hI1, hne1⟩ := addOne_save_ok hI hf (not_not.mp hx) h1
      exact ih d1 d' hI1 hne1 h

lemma addFunctions_ok {ds d : DiamondStorage} {f : Address} {xs : List Selector} {b : Bool}
    (hI : DiamondOk ds) (hxs : xs ≠ []) (h : addFunctions ds f xs b = some d) : DiamondOk d := by
  unfold addFunctions at h
  split_ifs at h with hf
  obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil hxs
  simp only [addLoop, saveFacetIfNew_s2f] at h
  split_ifs at h with hx
  cases h1 : addOneFunction (saveFacetIfNew ds f) f x b with
  | none => rw [h1] at h; simp at h
  | some d1 =>
    rw [h1, Option.bind_some] at h
    obtain ⟨hI1, hne1⟩ := addOne_save_ok hI hf (not_not.mp hx) h1
    exact (addLoop_ok hf xs d1 d hI1 hne1 h).1

lemma removeLoop_ok : ∀ (xs : List Selector) (d d' : DiamondStorage), DiamondOk d →
    removeLoop d xs = some d' → DiamondOk d' := by
  intro xs
  induction xs with
  | nil => intro d d' hI h; simp [removeLoop] at h; subst h; exact hI
  | cons x xs ih =>
    intro d d' hI h
    simp only [removeLoop] at h
    split_ifs at h with hx
    cases h1 : removeOneFunction d (d.selectorToFacet x).facetAddress x with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      exact ih d1 d' (removeOne_ok hI hx rfl h1) h

lemma removeFunctions_ok {ds d : DiamondStorage} {f : Address} {xs : List Selector}
    (hI : DiamondOk ds) (h : removeFunctions ds f xs = some d) : DiamondOk d := by
  unfold removeFunctions at h
  split_ifs at h with hf
  exact removeLoop_ok xs ds d hI h

lemma removeFacet_s2f {ds d : DiamondStorage} {f : Address} (h : removeFacet ds f = some d) :
    d.selectorToFacet = ds.selectorToFacet := by
  unfold removeFacet at h
  dsimp only at h
  split_ifs at h <;> simp at h <;> (subst h; rfl)

lemma upd_pos_facet (s : Selector → SelectorToFacet) (y z : Selector) (p : ℕ) :
    (upd s y { s y with selectorPosition := p } z).facetAddress = (s z).facetAddress ∧
    (upd s y { s y with selectorPosition := p } z).isFreezable = (s z).isFreezable := by
  by_cases h : z = y
  · subst h; simp
  · simp [upd_ne _ _ h]

/-- What `_removeOneFunction` does to routing: it clears the removed selector's slot and
moves at most one other selector's position. -/
lemma removeOne_s2f {ds d : DiamondStorage} {f : Address} {x : Selector}
    (h : removeOneFunction ds f x = some d) (z : Selector) :
    (d.selectorToFacet z).facetAddress =
        (if z = x then 0 else (ds.selectorToFacet z).facetAddress) ∧
      (d.selectorToFacet z).isFreezable =
        (if z = x then false else (ds.selectorToFacet z).isFreezable) := by
  unfold removeOneFunction at h
  dsimp only at h
  split_ifs at h
  all_goals try simp only [Option.bind_some, Option.bind_none, reduceCtorEq,
    Option.some.injEq] at h
  all_goals first | rw [removeFacet_s2f h] | subst h
  all_goals by_cases hz : z = x
  all_goals first
    | (subst hz; simp [SelectorToFacet.zero])
    | (simp only [upd_ne _ _ hz]; simp [upd_pos_facet, hz])

lemma removeOne_s2f_self {ds d : DiamondStorage} {f : Address} {x : Selector}
    (h : removeOneFunction ds f x = some d) : (d.selectorToFacet x).facetAddress = 0 := by
  simpa using (removeOne_s2f h x).1

lemma replaceLoop_ok {f : Address} {b : Bool} (hf : f ≠ 0) :
    ∀ (xs : List Selector) (d d' : DiamondStorage), DiamondOk d →
      replaceLoop d f xs b = some d' → DiamondOk d' := by
  intro xs
  induction xs with
  | nil => intro d d' hI h; simp [replaceLoop] at h; subst h; exact hI
  | cons x xs ih =>
    intro d d' hI h
    simp only [replaceLoop] at h
    split_ifs at h with hx
    cases h1 : removeOneFunction d (d.selectorToFacet x).facetAddress x with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      have hI1 := removeOne_ok hI hx rfl h1
      have hx1 : (d1.selectorToFacet x).facetAddress = 0 := removeOne_s2f_self h1
      cases h2 : addOneFunction (saveFacetIfNew d1 f) f x b with
      | none => rw [h2] at h; simp at h
      | some d2 =>
        rw [h2, Option.bind_some] at h
        exact ih d2 d' (addOne_save_ok hI1 hf hx1 h2).1 h

lemma replaceFunctions_ok {ds d : DiamondStorage} {f : Address} {xs : List Selector} {b : Bool}
    (hI : DiamondOk ds) (h : replaceFunctions ds f xs b = some d) : DiamondOk d := by
  unfold replaceFunctions at h
  split_ifs at h with hf
  exact replaceLoop_ok hf xs ds d hI h

lemma facetCut_ok {ds d : DiamondStorage} {c : FacetCut} (hI : DiamondOk ds)
    (h : facetCut ds c = some d) : DiamondOk d := by
  unfold facetCut at h
  split_ifs at h with hne
  cases hc : c.action with
  | add => rw [hc] at h; exact addFunctions_ok hI hne h
  | replace => rw [hc] at h; exact replaceFunctions_ok hI h
  | remove => rw [hc] at h; exact removeFunctions_ok hI h

lemma diamondCut_ok : ∀ (cs : List FacetCut) (ds d : DiamondStorage), DiamondOk ds →
    diamondCut ds cs = some d → DiamondOk d := by
  intro cs
  induction cs with
  | nil => intro ds d hI h; simp [diamondCut] at h; subst h; exact hI
  | cons c cs ih =>
    intro ds d hI h
    simp only [diamondCut] at h
    cases h1 : facetCut ds c with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      exact ih d1 d (facetCut_ok hI h1) h

lemma fresh_ok : DiamondOk DiamondStorage.fresh := by
  constructor
  · intro f i x h; simp [DiamondStorage.fresh] at h
  · intro x h; simp [DiamondStorage.fresh, SelectorToFacet.zero] at h
  · intro i f h; simp [DiamondStorage.fresh] at h
  · intro f h; simp [DiamondStorage.fresh] at h
  · rfl

/-! ## What a cut does to routing -/

lemma addOne_routing {ds d : DiamondStorage} {f : Address} {x : Selector} {b : Bool}
    (hf : f ≠ 0) (h : addOneFunction ds f x b = some d) :
    d.routing = upd ds.routing x (some (f, b)) := by
  unfold addOneFunction at h
  dsimp only at h
  split_ifs at h with hfrz
  cases h
  funext z
  by_cases hz : z = x
  · subst hz; simp [DiamondStorage.routing, hf]
  · simp [DiamondStorage.routing, upd_ne _ _ hz]

lemma saveFacetIfNew_routing (ds : DiamondStorage) (f : Address) :
    (saveFacetIfNew ds f).routing = ds.routing := by
  unfold DiamondStorage.routing; rw [saveFacetIfNew_s2f]

lemma removeOne_routing {ds d : DiamondStorage} {f : Address} {x : Selector}
    (h : removeOneFunction ds f x = some d) : d.routing = upd ds.routing x none := by
  funext z
  obtain ⟨h1, h2⟩ := removeOne_s2f h z
  by_cases hz : z = x
  · subst hz; simp [DiamondStorage.routing, h1]
  · simp only [hz, ite_false] at h1 h2
    simp [DiamondStorage.routing, upd_ne _ _ hz, h1, h2]

lemma routing_eq_none {ds : DiamondStorage} {x : Selector} :
    ds.routing x = none ↔ (ds.selectorToFacet x).facetAddress = 0 := by
  unfold DiamondStorage.routing; split_ifs with h <;> simp [h]

lemma addLoop_routing {f : Address} {b : Bool} (hf : f ≠ 0) :
    ∀ (xs : List Selector) (d d' : DiamondStorage), addLoop d f xs b = some d' →
      addAll d.routing (xs.map fun x => (x, (f, b))) = some d'.routing := by
  intro xs
  induction xs with
  | nil => intro d d' h; simp [addLoop] at h; subst h; rfl
  | cons x xs ih =>
    intro d d' h
    simp only [addLoop] at h
    split_ifs at h with hx
    cases h1 : addOneFunction d f x b with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      have hfree : d.routing x = none := routing_eq_none.mpr (not_not.mp hx)
      simp only [List.map_cons, addAll, addSel, hfree, ite_true, Option.bind_some]
      rw [← addOne_routing hf h1]
      exact ih d1 d' h

lemma addFunctions_routing {ds d : DiamondStorage} {f : Address} {xs : List Selector} {b : Bool}
    (h : addFunctions ds f xs b = some d) :
    addAll ds.routing (xs.map fun x => (x, (f, b))) = some d.routing := by
  unfold addFunctions at h
  split_ifs at h with hf
  rw [← saveFacetIfNew_routing ds f]
  exact addLoop_routing hf xs _ d h

lemma removeLoop_routing : ∀ (xs : List Selector) (d d' : DiamondStorage),
    removeLoop d xs = some d' → removeAll d.routing xs = some d'.routing := by
  intro xs
  induction xs with
  | nil => intro d d' h; simp [removeLoop] at h; subst h; rfl
  | cons x xs ih =>
    intro d d' h
    simp only [removeLoop] at h
    split_ifs at h with hx
    cases h1 : removeOneFunction d (d.selectorToFacet x).facetAddress x with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      have hrouted : d.routing x ≠ none := fun h0 => hx (routing_eq_none.mp h0)
      simp only [removeAll, removeSel, hrouted, ite_false, Option.bind_some]
      rw [← removeOne_routing h1]
      exact ih d1 d' h

lemma removeFunctions_routing {ds d : DiamondStorage} {f : Address} {xs : List Selector}
    (h : removeFunctions ds f xs = some d) : removeAll ds.routing xs = some d.routing := by
  unfold removeFunctions at h
  split_ifs at h with hf
  exact removeLoop_routing xs ds d h

lemma replaceLoop_routing {f : Address} {b : Bool} (hf : f ≠ 0) :
    ∀ (xs : List Selector) (d d' : DiamondStorage), replaceLoop d f xs b = some d' →
      (∀ y ∈ xs, d.routing y ≠ none) ∧
        ∀ y, d'.routing y = if y ∈ xs then some (f, b) else d.routing y := by
  intro xs
  induction xs with
  | nil => intro d d' h; simp [replaceLoop] at h; subst h; simp
  | cons x xs ih =>
    intro d d' h
    simp only [replaceLoop] at h
    split_ifs at h with hx
    cases h1 : removeOneFunction d (d.selectorToFacet x).facetAddress x with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      cases h2 : addOneFunction (saveFacetIfNew d1 f) f x b with
      | none => rw [h2] at h; simp at h
      | some d2 =>
        rw [h2, Option.bind_some] at h
        have hd2 : d2.routing = upd d.routing x (some (f, b)) := by
          rw [addOne_routing hf h2, saveFacetIfNew_routing, removeOne_routing h1, upd_upd_same]
        obtain ⟨ih1, ih2⟩ := ih d2 d' h
        have hrouted : d.routing x ≠ none := fun h0 => hx (routing_eq_none.mp h0)
        refine ⟨?_, ?_⟩
        · intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact hrouted
          · have := ih1 y hy
            rw [hd2] at this
            by_cases hyx : y = x
            · subst hyx; exact hrouted
            · rwa [upd_ne _ _ hyx] at this
        · intro y
          rw [ih2 y, hd2]
          by_cases hyx : y = x
          · subst hyx; simp
          · by_cases hy : y ∈ xs <;> simp [hy, hyx, upd_ne _ _ hyx]

lemma replaceFunctions_routing {ds d : DiamondStorage} {f : Address} {xs : List Selector}
    {b : Bool} (h : replaceFunctions ds f xs b = some d) :
    f ≠ 0 ∧ (∀ y ∈ xs, ds.routing y ≠ none) ∧
      ∀ y, d.routing y = if y ∈ xs then some (f, b) else ds.routing y := by
  unfold replaceFunctions at h
  split_ifs at h with hf
  exact ⟨hf, replaceLoop_routing hf xs ds d h⟩

/-! ## The properties -/

theorem FreshStorageOk : Properties.FreshStorageOk := fresh_ok

lemma DiamondOk.mem_routing {ds : DiamondStorage} (hI : DiamondOk ds) {f : Address}
    {x : Selector} : x ∈ (ds.facetToSelectors f).selectors ↔ ∃ b, ds.routing x = some (f, b) := by
  rw [hI.mem_sels]
  unfold DiamondStorage.routing
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(ds.selectorToFacet x).isFreezable, by rw [h1]; simp [h2]⟩
  · rintro ⟨b, hb⟩
    split_ifs at hb with h0
    cases hb
    exact ⟨rfl, h0⟩

theorem DiamondOkMeans : Properties.DiamondOkMeans := by
  intro ds hI
  refine ⟨hI.facets_nodup, fun f => hI.mem_facets, hI.sels_nodup, ?_, fun f x => hI.mem_routing⟩
  rw [hI.mem_facets, hI.zeroNoSels]
  simp

theorem AddFunctionsPreservesOk : Properties.AddFunctionsPreservesOk :=
  fun _ _ _ _ _ hI hxs h => addFunctions_ok hI hxs h

theorem RemoveFunctionsPreservesOk : Properties.RemoveFunctionsPreservesOk :=
  fun _ _ _ _ hI h => removeFunctions_ok hI h

theorem ReplaceFunctionsPreservesOk : Properties.ReplaceFunctionsPreservesOk :=
  fun _ _ _ _ _ hI h => replaceFunctions_ok hI h

theorem DiamondCutPreservesOk : Properties.DiamondCutPreservesOk :=
  fun ds d cuts hI h => diamondCut_ok cuts ds d hI h

theorem AddFunctionsRoutes : Properties.AddFunctionsRoutes :=
  fun _ _ _ _ _ h => addFunctions_routing h

theorem RemoveFunctionsRoutes : Properties.RemoveFunctionsRoutes :=
  fun _ _ _ _ h => removeFunctions_routing h

theorem ReplaceFunctionsRoutes : Properties.ReplaceFunctionsRoutes :=
  fun _ _ _ _ _ h => replaceFunctions_routing h

theorem EmptyAddBreaksOk : Properties.EmptyAddBreaksOk := by
  refine ⟨_, rfl, ?_, by decide, rfl, rfl⟩
  intro hI
  exact (hI.facetsBack 0 11 rfl).2 rfl

theorem DiamondCutWitness : Properties.DiamondCutWitness := by
  have h₁ := diamondCut_ok wTwoFacetCuts _ _ fresh_ok rfl
  exact ⟨_, _, rfl, rfl, h₁, diamondCut_ok wRemoveReplaceCuts _ _ h₁ rfl, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

end Contracts.ChainTypeManager
