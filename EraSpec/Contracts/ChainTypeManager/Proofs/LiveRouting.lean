import EraSpec.Contracts.ChainTypeManager.Properties.LiveRouting
import EraSpec.Contracts.ChainTypeManager.Proofs.DiamondStorage

/-!
# Proofs: the counting check is exact, and the headline holds with it

**The equivalence** (`countCheck_iff`). From the count check: every row's facet has a
selector, so it is listed; the rows' facets are distinct (`rowsWf_facets_nodup`) and as many
as the listed facets, so they are all of them (a duplicate-free sublist of equal length is a
permutation); each row's self-described selectors are in its facet's list and as many, so
they are all of it. A routed selector therefore belongs to some row. Conversely, exact
routing makes each facet's list and the facet list have the same members as the release's,
and duplicate-free lists with the same members have the same length.

**The system** (`countedStep_view`). Each concrete cut refines the `ChainRouting` operation
on routing (`installCuts_routing`, `removeCuts_routing`, and `transitionCuts_routing`, which
handles the byte-different-but-equal-routing case of the shortcut); the count check gives the
semantic guard through `countCheck_iff`, using `CtmInv` to identify the transition's
departing release with an installed, validated one. The headline is then `ChainRouting`'s,
read through the refinement, plus the count check from the converse direction.
-/

namespace Contracts.ChainTypeManager

/-! ## Flattened rows -/

lemma flattenRows_keys (sel : Address → List Selector) (rows : List FacetRow) :
    (flattenRows sel rows).map Prod.fst = rows.flatMap fun fb => sel fb.1 := by
  simp [flattenRows, List.map_flatMap, Function.comp_def]

lemma mem_flattenRows {sel : Address → List Selector} {rows : List FacetRow} {x : Selector}
    {r : Route} : (x, r) ∈ flattenRows sel rows ↔ r ∈ rows ∧ x ∈ sel r.1 := by
  simp [flattenRows, List.mem_flatMap]

lemma rowsRouting_of_mem {L : ReleaseRows} {x : Selector} {r : Route}
    (hnd : (L.map Prod.fst).Nodup) (h : (x, r) ∈ L) : rowsRouting L x = some r := by
  induction L with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨y, q⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp h with h' | h'
    · cases h'; simp [rowsRouting]
    · have hxy : x ≠ y := by
        rintro rfl; exact hnd.1 (List.mem_map.mpr ⟨(x, r), h', rfl⟩)
      simp [rowsRouting, hxy, ih hnd.2 h']

lemma mem_of_rowsRouting {L : ReleaseRows} {x : Selector} {r : Route}
    (h : rowsRouting L x = some r) : (x, r) ∈ L := by
  induction L with
  | nil => simp [rowsRouting] at h
  | cons hd tl ih =>
    obtain ⟨y, q⟩ := hd
    simp only [rowsRouting] at h
    split_ifs at h with hxy
    · cases h; subst hxy; simp
    · exact List.mem_cons_of_mem _ (ih h)

lemma routing_eq_some {ds : DiamondStorage} {x : Selector} {f : Address} {b : Bool} :
    ds.routing x = some (f, b) ↔
      (ds.selectorToFacet x).facetAddress = f ∧ f ≠ 0 ∧ (ds.selectorToFacet x).isFreezable = b := by
  unfold DiamondStorage.routing
  split_ifs with h0
  · simp only [false_iff]
    rintro ⟨h1, h2, _⟩; exact h2 (h1 ▸ h0)
  · simp only [Option.some.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h1 ▸ h0, h2⟩
    · rintro ⟨h1, _, h2⟩; exact ⟨h1, h2⟩

/-! ## Valid rows -/

lemma rowsWf_facets_nodup {sel : Address → List Selector} :
    ∀ {rows : List FacetRow}, RowsWf sel rows → (rows.map Prod.fst).Nodup
  | [], _ => by simp
  | fb :: rs, ⟨hne, hnd⟩ => by
    rw [List.flatMap_cons, List.nodup_append] at hnd
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, rowsWf_facets_nodup ⟨fun fb' h' => hne fb' (List.mem_cons_of_mem _ h'), hnd.2.1⟩⟩
    intro hmem
    obtain ⟨fb', hfb', heq⟩ := List.mem_map.mp hmem
    obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil _ (hne fb List.mem_cons_self)
    exact hnd.2.2 x hx x (List.mem_flatMap.mpr ⟨fb', hfb', heq ▸ hx⟩) rfl

lemma rowsWf_sel_nodup {sel : Address → List Selector} {rows : List FacetRow}
    (h : RowsWf sel rows) {fb : FacetRow} (hfb : fb ∈ rows) : (sel fb.1).Nodup :=
  (List.nodup_flatMap.mp h.nodup).1 fb hfb

/-! ## The equivalence -/

theorem countCheck_iff {sel : Address → List Selector} {ds : DiamondStorage}
    {rows : List FacetRow} (hI : DiamondOk ds) (hW : RowsWf sel rows) :
    CountCheck sel ds rows ↔ ds.routing = rowsRouting (flattenRows sel rows) := by
  have hFnd := rowsWf_facets_nodup hW
  have hkeys : ((flattenRows sel rows).map Prod.fst).Nodup := by
    rw [flattenRows_keys]; exact hW.nodup
  have hRsome : ∀ fb ∈ rows, ∀ x ∈ sel fb.1, rowsRouting (flattenRows sel rows) x = some fb :=
    fun fb hfb x hx => rowsRouting_of_mem hkeys (mem_flattenRows.mpr ⟨hfb, hx⟩)
  constructor
  · -- counting gives exact routing
    rintro ⟨hlen, hrow⟩
    have hlive : ∀ fb ∈ rows, (ds.facetToSelectors fb.1).selectors ≠ [] := by
      intro fb hfb h0
      have := (hrow fb hfb).1
      rw [h0, List.length_nil] at this
      exact hW.nonempty fb hfb (List.eq_nil_of_length_eq_zero this.symm)
    have hnz : ∀ fb ∈ rows, fb.1 ≠ 0 := by
      intro fb hfb h0
      have := hlive fb hfb
      rw [h0, hI.zeroNoSels] at this
      exact this rfl
    have hperm : (rows.map Prod.fst).Perm ds.facets := by
      refine (hFnd.subperm fun f hf => ?_).perm_of_length_le (by simp [hlen])
      obtain ⟨fb, hfb, rfl⟩ := List.mem_map.mp hf
      exact hI.mem_facets.mpr (hlive fb hfb)
    have hsel : ∀ fb ∈ rows, ∀ y ∈ (ds.facetToSelectors fb.1).selectors, y ∈ sel fb.1 := by
      intro fb hfb y hy
      have hsub : sel fb.1 ⊆ (ds.facetToSelectors fb.1).selectors := fun z hz =>
        hI.mem_sels.mpr ⟨((hrow fb hfb).2 z hz).1, hnz fb hfb⟩
      have hp := ((rowsWf_sel_nodup hW hfb).subperm hsub).perm_of_length_le
        (by rw [(hrow fb hfb).1])
      exact hp.mem_iff.mpr hy
    funext x
    by_cases hx : ∃ fb ∈ rows, x ∈ sel fb.1
    · obtain ⟨fb, hfb, hxs⟩ := hx
      rw [hRsome fb hfb x hxs]
      obtain ⟨h1, h2⟩ := (hrow fb hfb).2 x hxs
      exact routing_eq_some.mpr ⟨h1, hnz fb hfb, h2⟩
    · simp only [not_exists, not_and] at hx
      rw [rowsRouting_eq_none.mpr (by
        rw [flattenRows_keys, List.mem_flatMap]; rintro ⟨fb, hfb, hxs⟩; exact hx fb hfb hxs)]
      rw [routing_eq_none]
      by_contra hg
      have hxg : x ∈ (ds.facetToSelectors (ds.selectorToFacet x).facetAddress).selectors :=
        hI.mem_sels.mpr ⟨rfl, hg⟩
      obtain ⟨fb, hfb, hfbg⟩ := List.mem_map.mp
        (hperm.mem_iff.mpr (hI.mem_facets.mpr (List.ne_nil_of_mem hxg)))
      exact hx fb hfb (hsel fb hfb x (hfbg ▸ hxg))
  · -- exact routing gives counting
    intro hR
    have hrt : ∀ y, ds.routing y = rowsRouting (flattenRows sel rows) y := fun y => congrFun hR y
    have hmem : ∀ fb ∈ rows, ∀ y, y ∈ (ds.facetToSelectors fb.1).selectors ↔ y ∈ sel fb.1 := by
      intro fb hfb y
      rw [hI.mem_routing]
      constructor
      · rintro ⟨b, hb⟩
        rw [hrt y] at hb
        exact (mem_flattenRows.mp (mem_of_rowsRouting hb)).2
      · intro hy
        exact ⟨fb.2, by rw [hrt y, hRsome fb hfb y hy]⟩
    refine ⟨?_, fun fb hfb => ⟨?_, fun x hx => ?_⟩⟩
    · have hiff : ∀ f, f ∈ ds.facets ↔ f ∈ rows.map Prod.fst := by
        intro f
        rw [hI.mem_facets]
        constructor
        · intro hne
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ hne
          obtain ⟨b, hb⟩ := hI.mem_routing.mp hy
          rw [hrt y] at hb
          exact List.mem_map.mpr ⟨_, (mem_flattenRows.mp (mem_of_rowsRouting hb)).1, rfl⟩
        · intro hf
          obtain ⟨fb, hfb, rfl⟩ := List.mem_map.mp hf
          obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil _ (hW.nonempty fb hfb)
          exact List.ne_nil_of_mem ((hmem fb hfb y).mpr hy)
      rw [((List.perm_ext_iff_of_nodup hI.facets_nodup hFnd).mpr hiff).length_eq,
        List.length_map]
    · exact ((List.perm_ext_iff_of_nodup (hI.sels_nodup _) (rowsWf_sel_nodup hW hfb)).mpr
        (hmem fb hfb)).length_eq
    · have := hrt x
      rw [hRsome fb hfb x hx] at this
      obtain ⟨h1, _, h2⟩ := routing_eq_some.mp this
      exact ⟨h1, h2⟩

/-! ## The system's cuts, on routing -/

@[simp] lemma DWorld.toWorld_relRows (D : DWorld) (R : Address) :
    D.toWorld.relRows R = flattenRows D.selectors (D.genesisFacets R) := rfl
@[simp] lemma DWorld.toWorld_relVersion (D : DWorld) : D.toWorld.relVersion = D.relVersion := rfl
@[simp] lemma DWorld.toWorld_tr (D : DWorld) : D.toWorld.tr = D.tr := rfl

lemma addAll_append (ρ : Routing) (A B : ReleaseRows) :
    addAll ρ (A ++ B) = (addAll ρ A).bind fun σ => addAll σ B := by
  induction A generalizing ρ with
  | nil => simp [addAll]
  | cons hd tl ih =>
    obtain ⟨x, r⟩ := hd
    simp only [List.cons_append, addAll]
    cases addSel ρ x r with
    | none => rfl
    | some ρ' => simp [ih]

lemma removeAll_append (ρ : Routing) (A B : List Selector) :
    removeAll ρ (A ++ B) = (removeAll ρ A).bind fun σ => removeAll σ B := by
  induction A generalizing ρ with
  | nil => simp [removeAll]
  | cons x tl ih =>
    simp only [List.cons_append, removeAll]
    cases removeSel ρ x with
    | none => rfl
    | some ρ' => simp [ih]

lemma diamondCut_append (ds : DiamondStorage) (A B : List FacetCut) :
    diamondCut ds (A ++ B) = (diamondCut ds A).bind fun d => diamondCut d B := by
  induction A generalizing ds with
  | nil => simp [diamondCut]
  | cons c tl ih =>
    simp only [List.cons_append, diamondCut]
    cases facetCut ds c with
    | none => rfl
    | some d => simp [ih]

lemma fresh_routing : DiamondStorage.fresh.routing = emptyRouting := by
  funext x; simp [DiamondStorage.routing, DiamondStorage.fresh, SelectorToFacet.zero, emptyRouting]

/-- One `Add` cut per row installs the flattened rows. -/
lemma installCuts_routing (sel : Address → List Selector) :
    ∀ (rows : List FacetRow) (ds d : DiamondStorage),
      diamondCut ds (rows.map fun fb => (⟨fb.1, .add, fb.2, sel fb.1⟩ : FacetCut)) = some d →
      addAll ds.routing (flattenRows sel rows) = some d.routing := by
  intro rows
  induction rows with
  | nil => intro ds d h; simp [diamondCut] at h; subst h; rfl
  | cons fb rs ih =>
    intro ds d h
    simp only [List.map_cons, diamondCut] at h
    cases h1 : facetCut ds ⟨fb.1, .add, fb.2, sel fb.1⟩ with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      unfold facetCut at h1
      split_ifs at h1 with hne
      have hadd := addFunctions_routing h1
      simp only [Prod.mk.eta] at hadd
      simp only [flattenRows, List.flatMap_cons] at ih ⊢
      rw [addAll_append, hadd, Option.bind_some]
      exact ih d1 d h

/-- One `Remove` cut per item removes the concatenated selector lists. -/
lemma removeCuts_routing {α : Type} (g : α → List Selector) :
    ∀ (l : List α) (ds d : DiamondStorage),
      diamondCut ds (l.map fun a => (⟨0, .remove, false, g a⟩ : FacetCut)) = some d →
      removeAll ds.routing (l.flatMap g) = some d.routing := by
  intro l
  induction l with
  | nil => intro ds d h; simp [diamondCut] at h; subst h; rfl
  | cons a tl ih =>
    intro ds d h
    simp only [List.map_cons, diamondCut] at h
    cases h1 : facetCut ds ⟨0, .remove, false, g a⟩ with
    | none => rw [h1] at h; simp at h
    | some d1 =>
      rw [h1, Option.bind_some] at h
      unfold facetCut at h1
      split_ifs at h1 with hne
      rw [List.flatMap_cons, removeAll_append, removeFunctions_routing h1, Option.bind_some]
      exact ih d1 d h

/-- **The derived cuts, behind the guard, do what `applyDerived` does.** -/
lemma transitionCuts_routing {D : DWorld} {A B : Address} {ds d : DiamondStorage}
    (hguard : ds.routing = rowsRouting (D.rows A))
    (h : diamondCut ds (deriveFacetCuts D A B) = some d) :
    applyDerived ds.routing (D.rows A) (D.rows B) = some d.routing := by
  unfold deriveFacetCuts at h
  split_ifs at h with heq
  · simp only [diamondCut, Option.some.injEq] at h
    subst h
    have hgf : D.genesisFacets A = D.genesisFacets B := by
      have := congrArg (List.map Prod.fst) heq
      simpa [List.map_map, Function.comp_def] using this
    simp [applyDerived, hgf]
  · rw [diamondCut_append] at h
    cases h1 : diamondCut ds ((D.genesisFacets A).map
        fun fb => (⟨0, .remove, false, D.selectors fb.1⟩ : FacetCut)) with
    | none => rw [h1] at h; simp at h
    | some dm =>
      rw [h1, Option.bind_some] at h
      have hrm := removeCuts_routing (fun fb : FacetRow => D.selectors fb.1) _ ds dm h1
      rw [← flattenRows_keys] at hrm
      have hadd := installCuts_routing D.selectors _ dm d h
      by_cases hAB : D.rows A = D.rows B
      · -- byte-different rows with the same routing: the reinstall changes nothing
        have hdm : dm.routing = emptyRouting := by
          funext y
          rw [removeAll_spec hrm y, hguard]
          split_ifs with hy
          · rfl
          · exact rowsRouting_eq_none.mpr hy
        rw [hdm] at hadd
        have hd := addAll_empty hadd
        simp only [applyDerived, hAB, ite_true, Option.some.injEq]
        rw [hguard, hd, hAB]; rfl
      · simp only [applyDerived, hAB, ite_false]
        rw [show (D.rows A).map Prod.fst = (flattenRows D.selectors (D.genesisFacets A)).map
          Prod.fst from rfl, hrm, Option.bind_some]
        exact hadd

/-- **The bootstrap reinstall, from consistent storage, installs the release.** -/
lemma bootstrapCuts_routing {D : DWorld} {R : Address} {ds ds₁ ds₂ : DiamondStorage}
    (hI : DiamondOk ds) (h1 : diamondCut ds (removeAllCuts ds) = some ds₁)
    (h2 : diamondCut ds₁ (newChainInstallations D R) = some ds₂) :
    addAll emptyRouting (D.rows R) = some ds₂.routing := by
  have hrm := removeCuts_routing (fun f => (ds.facetToSelectors f).selectors) ds.facets ds ds₁ h1
  have hemp : ds₁.routing = emptyRouting := by
    funext y
    rw [removeAll_spec hrm y]
    split_ifs with hy
    · rfl
    · cases hr : ds.routing y with
      | none => rfl
      | some fb =>
        exfalso; apply hy
        obtain ⟨f, b⟩ := fb
        have hyf : y ∈ (ds.facetToSelectors f).selectors := hI.mem_routing.mpr ⟨b, hr⟩
        exact List.mem_flatMap.mpr ⟨f, hI.mem_facets.mpr (List.ne_nil_of_mem hyf), hyf⟩
  have := installCuts_routing D.selectors (D.genesisFacets R) ds₁ ds₂ h2
  rw [hemp] at this
  exact this

/-! ## The system -/

lemma upd_some {α : Type} {chains : ChainId → Option α} {id id' : ChainId} {c' c : α}
    (h : upd chains id (some c') id' = some c) :
    (id' = id ∧ c = c') ∨ (id' ≠ id ∧ chains id' = some c) := by
  by_cases hid : id' = id
  · subst hid; simp at h; exact Or.inl ⟨rfl, h.symm⟩
  · rw [upd_ne _ _ hid] at h; exact Or.inr ⟨hid, h⟩

lemma view_set (s : DSys) (id : ChainId) (c : DChain) :
    ({ s with chains := upd s.chains id (some c) } : DSys).view =
      { s.view with chains := upd s.view.chains id (some c.view) } := by
  simp only [DSys.view]
  congr 1
  funext i
  by_cases h : i = id
  · subst h; simp
  · simp [upd_ne _ _ h]

lemma DLabel.view_isArbitrary (l : DLabel) : l.view.isArbitrary ↔ l.isArbitrary := by
  cases l <;> simp [DLabel.view, DLabel.isArbitrary, Label.isArbitrary]

/-- **Every count-checked step is a `ChainRouting` step of what the system routes.** -/
theorem countedStep_view {D : DWorld} {s s' : DSys} {l : DLabel} (hC : CtmInv D.toWorld s.ctm)
    (hS : StoreInv D s) (h : DStep D s l s') : Step D.toWorld s.view l.view s'.view := by
  cases h with
  | ctm hc _ => exact Step.ctm hc
  | @genesis id ds hnone hcut =>
    rw [view_set]
    have := installCuts_routing D.selectors (D.genesisFacets s.ctm.cur) _ ds hcut
    rw [fresh_routing] at this
    exact Step.genesis (by simp [DSys.view, hnone]) this
  | @migrateIn id ds v hv hnone hcut =>
    rw [view_set]
    have := installCuts_routing D.selectors (D.genesisFacets s.ctm.cur) _ ds hcut
    rw [fresh_routing] at this
    exact Step.migrateIn v hv (by simp [DSys.view, hnone]) this
  | @transition id c ds hc hut hcc hcut hlt =>
    rw [view_set]
    obtain ⟨_, hfrom, hrz, _⟩ := hC.slots _ hut
    have hvalid := hS.releases _ hrz
    rw [← hfrom] at hvalid
    have hguard : c.ds.routing = rowsRouting (D.rows (s.edge D c.pv).fromRel) :=
      (countCheck_iff (hS.storage id c hc) hvalid.rows).mp hcc
    exact Step.transition (c := c.view) (by simp [DSys.view, hc]) hut hguard
      (transitionCuts_routing hguard hcut) hlt
  | @bootstrapReset id c R ds₁ ds₂ hc hleg h1 h2 hlt =>
    rw [view_set]
    exact Step.bootstrapReset (c := c.view) (by simp [DSys.view, hc]) hleg
      (bootstrapCuts_routing (hS.storage id c hc) h1 h2) hlt
  | @arbitraryCut id c v ds hc =>
    rw [view_set]
    exact Step.arbitraryCut (c := c.view) v ds.routing (by simp [DSys.view, hc])

/-- A CTM writer records a release only where it installs one. -/
lemma cstep_relAt_new {W : World} {s s' : CTM} {op : Op} (h : CStep W s op s') (v : ℕ) :
    s'.relAt v = s.relAt v ∨ op.installs W = some (s'.relAt v) := by
  cases h with
  | @commit t _ _ _ _ _ _ =>
    by_cases hv : v = (W.tr t).new
    · right; subst hv; simp [Op.installs]
    · left; exact upd_ne _ _ hv
  | replace _ _ _ _ _ _ _ _ => left; rfl
  | @legacyCommit R b _ _ =>
    by_cases hv : v = W.relVersion R
    · right; subst hv; simp [Op.installs]
    · left; exact upd_ne _ _ hv
  | legacyRecut _ _ => left; rfl

theorem countedStep_storeInv {D : DWorld} {s s' : DSys} {l : DLabel} (hS : StoreInv D s)
    (h : DStep D s l s') (hl : ¬ l.isArbitrary) : StoreInv D s' := by
  cases h with
  | @ctm op c' hc hval =>
    refine ⟨fun v hv => ?_, hS.storage⟩
    rcases cstep_relAt_new hc v with h | h
    · dsimp only at hv ⊢; rw [h] at hv ⊢; exact hS.releases v hv
    · exact hval _ h
  | @genesis id ds hnone hcut =>
    refine ⟨hS.releases, fun id' c hc => ?_⟩
    rcases upd_some hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · exact diamondCut_ok _ _ _ fresh_ok hcut
    · exact hS.storage id' c hold
  | @migrateIn id ds v _ hnone hcut =>
    refine ⟨hS.releases, fun id' c hc => ?_⟩
    rcases upd_some hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · exact diamondCut_ok _ _ _ fresh_ok hcut
    · exact hS.storage id' c hold
  | @transition id c0 ds hc0 _ _ hcut _ =>
    refine ⟨hS.releases, fun id' c hc => ?_⟩
    rcases upd_some hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · exact diamondCut_ok _ _ _ (hS.storage id c0 hc0) hcut
    · exact hS.storage id' c hold
  | @bootstrapReset id c0 R ds₁ ds₂ hc0 _ h1 h2 _ =>
    refine ⟨hS.releases, fun id' c hc => ?_⟩
    rcases upd_some hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · exact diamondCut_ok _ _ _ (diamondCut_ok _ _ _ (hS.storage id c0 hc0) h1) h2
    · exact hS.storage id' c hold
  | arbitraryCut _ _ _ => exact absurd trivial hl

theorem countedStep_inv {D : DWorld} {s s' : DSys} {l : DLabel} (hI : DSysInv D s)
    (h : DStep D s l s') (hl : ¬ l.isArbitrary) : DSysInv D s' :=
  ⟨step_sysInv hI.1 (countedStep_view hI.1.1 hI.2 h) (by rwa [DLabel.view_isArbitrary]),
    countedStep_storeInv hI.2 h hl⟩

theorem countedRun_view {D : DWorld} {s s' : DSys} {ls : List DLabel} (hI : DSysInv D s)
    (h : DRun D s ls s') (hl : ∀ l ∈ ls, ¬ l.isArbitrary) :
    Run D.toWorld s.view (ls.map DLabel.view) s'.view ∧ DSysInv D s' := by
  induction h with
  | nil => exact ⟨Run.nil, hI⟩
  | cons hs _ ih =>
    have hl0 := hl _ List.mem_cons_self
    obtain ⟨hr, hI'⟩ := ih (countedStep_inv hI hs hl0) (fun l hm => hl l (List.mem_cons_of_mem _ hm))
    exact ⟨Run.cons (countedStep_view hI.1.1 hI.2 hs) hr, hI'⟩

theorem chainsRun_counted {D : DWorld} {s s' : DSys} {ls : List DLabel} (hI : DSysInv D s)
    (h : DRun D s ls s') (hl : ∀ l ∈ ls, ¬ l.isArbitrary) (id : ChainId) (c : DChain)
    (hc : s'.chains id = some c) (hrel : s'.ctm.relAt c.pv ≠ 0) :
    D.relVersion (s'.ctm.relAt c.pv) = c.pv ∧
      c.ds.routing = rowsRouting (D.rows (s'.ctm.relAt c.pv)) ∧
      CountCheck D.selectors c.ds (D.genesisFacets (s'.ctm.relAt c.pv)) ∧ DiamondOk c.ds := by
  obtain ⟨⟨hC, hch⟩, hS⟩ := (countedRun_view hI h hl).2
  have hroute := (hch id c.view (by simp [DSys.view, hc])).2 hrel
  have hok := hS.storage id c hc
  exact ⟨(hC.relAtSound _ hrel).2, hroute,
    (countCheck_iff hok (hS.releases _ hrel).rows).mpr hroute, hok⟩

/-! ## Starting states -/

lemma relAt_single_valid {D : DWorld} {R : Address} (hv : ReleaseValid D R) (v : ℕ)
    (h : upd (fun _ => (0 : Address)) (D.relVersion R) R v ≠ 0) :
    ReleaseValid D (upd (fun _ => (0 : Address)) (D.relVersion R) R v) := by
  by_cases hv' : v = D.relVersion R
  · subst hv'; simpa using hv
  · rw [upd_ne _ _ hv'] at h ⊢; exact absurd rfl h

theorem freshCounted_inv (D : DWorld) (R : Address) (hR : R ≠ 0) (hv : ReleaseValid D R) :
    DSysInv D ⟨initState D.toWorld R, fun _ => none⟩ :=
  ⟨FreshSystemSatisfiesInvariant D.toWorld R hR,
    ⟨fun v h => relAt_single_valid hv v h, fun _ _ h => by simp at h⟩⟩

theorem bootstrapCounted_inv (D : DWorld) (old : ℕ) (R : Address)
    (chains : ChainId → Option DChain) (hR : R ≠ 0) (hlt : old < D.relVersion R)
    (hv : ReleaseValid D R) (hch : ∀ id c, chains id = some c → c.pv ≤ old ∧ DiamondOk c.ds) :
    DSysInv D ⟨bootstrapState D.toWorld old R, chains⟩ := by
  refine ⟨BootstrapSystemSatisfiesInvariant D.toWorld old R _ hR hlt ?_,
    ⟨fun v h => relAt_single_valid hv v h, fun id c h => (hch id c h).2⟩⟩
  intro id c h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨c0, h0, rfl⟩ := h
  exact (hch id c0 h0).1

/-! ## Drift -/

theorem countedDrift_blocks {D : DWorld} {s : DSys} {id : ChainId} {c : DChain}
    (hC : CtmInv D.toWorld s.ctm) (hrel : ∀ v, s.ctm.relAt v ≠ 0 → ReleaseValid D (s.ctm.relAt v))
    (hc : s.chains id = some c) (hok : DiamondOk c.ds)
    (hdrift : c.ds.routing ≠ rowsRouting (D.rows (s.ctm.relAt c.pv))) :
    ¬ ∃ s', DStep D s (.transition id) s' := by
  rintro ⟨s', h⟩
  cases h with
  | @transition _ c0 ds hc0 hut hcc hcut hlt =>
    have hcc' : c0 = c := Option.some.inj (hc0.symm.trans hc)
    subst hcc'
    obtain ⟨_, hfrom, hrz, _⟩ := hC.slots _ hut
    have hvalid := hrel _ hrz
    rw [← hfrom] at hvalid
    apply hdrift
    rw [← hfrom]
    exact (countCheck_iff hok hvalid.rows).mp hcc

/-! ## The CTM part, along any run -/

/-- Along any run, break-glass cuts included, the CTM keeps `CtmInv` and every release it
records passed `validate()`: only CTM writers touch it. -/
lemma drun_ctm {D : DWorld} {s s' : DSys} {ls : List DLabel} (hC : CtmInv D.toWorld s.ctm)
    (hR : ∀ v, s.ctm.relAt v ≠ 0 → ReleaseValid D (s.ctm.relAt v)) (h : DRun D s ls s') :
    CtmInv D.toWorld s'.ctm ∧ ∀ v, s'.ctm.relAt v ≠ 0 → ReleaseValid D (s'.ctm.relAt v) := by
  induction h with
  | nil => exact ⟨hC, hR⟩
  | @cons s1 s2 s3 l ls hs _ ih =>
    apply ih
    · cases hs with
      | ctm hc _ => exact step_inv hC hc
      | _ => exact hC
    · cases hs with
      | @ctm op c' hc hval =>
        intro v hv
        rcases cstep_relAt_new hc v with h | h
        · dsimp only at hv ⊢; rw [h] at hv ⊢; exact hR v hv
        · exact hval _ h
      | _ => exact hR

/-! ## Witnesses and countermodels

`Address × Bool` is a `Fintype`, so `decide` would settle `∀ fb ∈ rows, …` by enumerating every
pair; the list instance is preferred here. -/

attribute [local instance 2000] List.decidableBAll

lemma wValid100 : ReleaseValid wDWorld 100 := ⟨by decide, ⟨by decide, by decide⟩⟩
lemma wValid200 : ReleaseValid wDWorld 200 := ⟨by decide, ⟨by decide, by decide⟩⟩

lemma wDWorld_toWorld : wDWorld.toWorld = wWorld := by
  unfold DWorld.toWorld wWorld wDWorld
  congr 1
  funext a
  unfold wGenesisFacets wRows
  by_cases h1 : a = 100
  · subst h1; decide
  · by_cases h2 : a = 200
    · subst h2; decide
    · by_cases h3 : a = 250
      · subst h3; decide
      · simp [h1, h2, h3, flattenRows]


/-! ## The properties -/

theorem ValidRowsHaveDistinctFacets : Properties.ValidRowsHaveDistinctFacets :=
  fun _ _ h => rowsWf_facets_nodup h

theorem CountCheckIffExactRouting : Properties.CountCheckIffExactRouting :=
  fun _ _ _ hI hW => countCheck_iff hI hW

theorem CountCheckWitness : Properties.CountCheckWitness :=
  ⟨_, rfl, diamondCut_ok (newChainInstallations wDWorld 100) _ _ fresh_ok rfl, wValid100,
    wValid200, by decide, by decide⟩

theorem EmptySelectorRowFoolsCountCheck : Properties.EmptySelectorRowFoolsCountCheck :=
  ⟨_, rfl, diamondCut_ok cmCuts _ _ fresh_ok rfl, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem RepeatedRowFoolsCountCheck : Properties.RepeatedRowFoolsCountCheck :=
  ⟨_, rfl, diamondCut_ok cmCuts _ _ fresh_ok rfl, by decide, by decide, by decide, by decide,
    by decide⟩

theorem CorruptStorageFoolsCountCheck : Properties.CorruptStorageFoolsCountCheck := by
  refine ⟨wValid100, by decide, by decide, by decide, fun h => ?_⟩
  have := h.selsThere 3 (by decide)
  exact absurd this (by decide)

lemma cmStore_cut : diamondCut DiamondStorage.fresh cmCuts = some cmStore := rfl

lemma cmCtm_inv : CtmInv cmWorld.toWorld cmCtm :=
  step_inv (InitSatisfiesInvariant cmWorld.toWorld 700 (by decide))
    (CStep.commit (t := 720) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide))

theorem EmptySelectorRowCarriesDriftAcrossEdge :
    Properties.EmptySelectorRowCarriesDriftAcrossEdge := by
  have hdrift : cmStore.routing ≠ rowsRouting (cmWorld.rows 700) :=
    fun h => absurd (congrFun h 2) (by decide)
  refine ⟨cmCtm_inv, diamondCut_ok cmCuts _ _ fresh_ok cmStore_cut, rfl, hdrift,
    ⟨_, DStep.transition rfl (by decide) (by decide) rfl (by decide), _, rfl, rfl, by decide,
      by decide⟩, ?_, ?_⟩
  · exact DriftBlocksTransition _ _ 0 ⟨1, cmStore.routing⟩ cmCtm_inv rfl hdrift
  · intro h
    exact h.rows.nonempty (12, false) (by decide) (by decide)

theorem CountedStepRefinesStep : Properties.CountedStepRefinesStep :=
  fun _ _ _ _ hC hS h => countedStep_view hC hS h

theorem CountedStepPreservesInvariant : Properties.CountedStepPreservesInvariant :=
  fun _ _ _ _ hI h hl => countedStep_inv hI h hl

theorem CountedRunRefinesRun : Properties.CountedRunRefinesRun :=
  fun _ _ _ _ hI h hl => countedRun_view hI h hl

theorem ChainsRunTheirVersionsReleaseCounted :
    Properties.ChainsRunTheirVersionsReleaseCounted :=
  fun _ _ _ _ hI h hl id c hc hrel => chainsRun_counted hI h hl id c hc hrel

theorem FreshCountedSystemSatisfiesInvariant :
    Properties.FreshCountedSystemSatisfiesInvariant :=
  fun D R hR hv => freshCounted_inv D R hR hv

theorem FreshChainsRunTheirVersionsReleaseCounted :
    Properties.FreshChainsRunTheirVersionsReleaseCounted := by
  intro D R s' ls hR hv h hl id c hc
  have hI := freshCounted_inv D R hR hv
  have hrun := (countedRun_view hI h hl).1
  have hl' : ∀ l ∈ ls.map DLabel.view, ¬ l.isArbitrary := by
    intro l hm
    obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hm
    rw [DLabel.view_isArbitrary]
    exact hl l0 hl0
  have hrel := (FreshChainsRunTheirVersionsRelease D.toWorld R s'.view _ hR hrun hl' id c.view
    (by simp [DSys.view, hc])).1
  exact ⟨hrel, chainsRun_counted hI h hl id c hc hrel |>.1,
    chainsRun_counted hI h hl id c hc hrel |>.2.1, chainsRun_counted hI h hl id c hc hrel |>.2.2.1⟩

theorem BootstrapCountedSystemSatisfiesInvariant :
    Properties.BootstrapCountedSystemSatisfiesInvariant :=
  fun D old R chains hR hlt hv hch => bootstrapCounted_inv D old R chains hR hlt hv hch

theorem CountedDriftBlocksTransition : Properties.CountedDriftBlocksTransition :=
  fun _ _ _ _ hC hrel hc hok hdrift => countedDrift_blocks hC hrel hc hok hdrift

theorem CountedRoutingWitness : Properties.CountedRoutingWitness := by
  have hI0 : DSysInv wDWorld wDSys0 := freshCounted_inv wDWorld 100 (by decide) wValid100
  obtain ⟨s, hrun, ⟨c0, hc0, hpv0⟩, ⟨c1, hc1, hpv1⟩, hrel2⟩ : ∃ s,
      DRun wDWorld wDSys0 [.genesis 0, .ctm (.commit 300), .transition 0, .genesis 1] s ∧
      (∃ c, s.chains 0 = some c ∧ c.pv = 2) ∧ (∃ c, s.chains 1 = some c ∧ c.pv = 2) ∧
      s.ctm.relAt 2 = 200 :=
    ⟨_, DRun.cons (DStep.genesis (s := wDSys0) (id := 0) rfl rfl)
      (DRun.cons (DStep.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)) (by intro R hR; cases hR; exact wValid200))
        (DRun.cons (DStep.transition (id := 0) rfl (by decide) (by decide) rfl (by decide))
          (DRun.cons (DStep.genesis (id := 1) rfl rfl) DRun.nil))),
      ⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩
  have hl : ∀ l ∈ [DLabel.genesis 0, .ctm (.commit 300), .transition 0, .genesis 1],
      ¬ l.isArbitrary := by
    simp [DLabel.isArbitrary]
  have hrows : wDWorld.rows 200 = wRows 200 := by rw [DWorld.rows, wDWorld_toWorld]; rfl
  have h0 := chainsRun_counted hI0 hrun hl 0 c0 hc0 (by rw [hpv0, hrel2]; decide)
  have h1 := chainsRun_counted hI0 hrun hl 1 c1 hc1 (by rw [hpv1, hrel2]; decide)
  rw [hpv0, hrel2] at h0
  rw [hpv1, hrel2] at h1
  exact ⟨wDWorld_toWorld, hI0, s, hrun, ⟨c0, hc0, hpv0, by rw [h0.2.1, hrows], h0.2.2.1⟩,
    ⟨c1, hc1, hpv1, by rw [h1.2.1, hrows]⟩, fun h => absurd (congrFun h 1) (by decide)⟩

theorem CountedBootstrapResetWitness : Properties.CountedBootstrapResetWitness := by
  have hpre : diamondCut DiamondStorage.fresh [⟨77, .add, true, [7]⟩] = some wPreStore := rfl
  have hokpre := diamondCut_ok _ _ _ fresh_ok hpre
  have hI0 : DSysInv wDWorld wBootDSys := by
    refine bootstrapCounted_inv wDWorld 0 100 _ (by decide) (by decide) wValid100 ?_
    intro id c h
    rcases upd_some h with ⟨_, rfl⟩ | ⟨_, h'⟩
    · exact ⟨le_rfl, hokpre⟩
    · simp at h'
  obtain ⟨s, hrun, ⟨c, hc, hpv⟩, hrel1⟩ : ∃ s, DRun wDWorld wBootDSys [.bootstrapReset 5] s ∧
      (∃ c, s.chains 5 = some c ∧ c.pv = 1) ∧ s.ctm.relAt 1 = 100 :=
    ⟨_, DRun.cons (DStep.bootstrapReset (s := wBootDSys) (id := 5) (R := 100) rfl (by decide)
      rfl rfl (by decide)) DRun.nil, ⟨_, rfl, rfl⟩, rfl⟩
  have hl : ∀ l ∈ [DLabel.bootstrapReset 5], ¬ l.isArbitrary := by simp [DLabel.isArbitrary]
  have h5 := chainsRun_counted hI0 hrun hl 5 c hc (by rw [hpv, hrel1]; decide)
  rw [hpv, hrel1] at h5
  have hrows : wDWorld.rows 100 = wRows 100 := by rw [DWorld.rows, wDWorld_toWorld]; rfl
  refine ⟨s, hrun, hI0, by decide, c, hc, hpv, by rw [h5.2.1, hrows], ?_, h5.2.2.1⟩
  rw [h5.2.1]; decide

theorem CountedDriftWitness : Properties.CountedDriftWitness := by
  have hI0 := freshCounted_inv wDWorld 100 (by decide) wValid100
  have hstore100 : diamondCut DiamondStorage.fresh (newChainInstallations wDWorld 100) =
      some wStore100 := rfl
  have hbg : diamondCut wStore100 [⟨99, .add, false, [9]⟩] = some wBgStore := rfl
  have hokbg := diamondCut_ok _ _ _ (diamondCut_ok _ _ _ fresh_ok hstore100) hbg
  obtain ⟨s, hrun, hc, hrel1⟩ : ∃ s,
      DRun wDWorld wDSys0 [.genesis 0, .ctm (.commit 300), .arbitraryCut 0 1 wBgStore] s ∧
      s.chains 0 = some ⟨1, wBgStore⟩ ∧ s.ctm.relAt 1 = 100 :=
    ⟨_, DRun.cons (DStep.genesis (s := wDSys0) (id := 0) rfl hstore100)
      (DRun.cons (DStep.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)) (by intro R hR; cases hR; exact wValid200))
        (DRun.cons (DStep.arbitraryCut (id := 0) 1 wBgStore rfl) DRun.nil)), rfl, rfl⟩
  obtain ⟨hC, hR⟩ := drun_ctm hI0.1.1 hI0.2.releases hrun
  have hdrift : wBgStore.routing ≠ rowsRouting (wDWorld.rows (s.ctm.relAt 1)) := by
    rw [hrel1]; exact fun h => absurd (congrFun h 9) (by decide)
  exact ⟨s, hrun, hC, hR, ⟨_, hc, hokbg, hdrift⟩, countedDrift_blocks hC hR hc hokbg hdrift⟩

end Contracts.ChainTypeManager
