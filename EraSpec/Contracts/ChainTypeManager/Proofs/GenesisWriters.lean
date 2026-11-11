import EraSpec.Contracts.ChainTypeManager.Properties.GenesisWriters
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainRouting

/-!
# Proofs: chain creation is `ChainRouting`'s genesis step

The diamond library's `Add` path is related to `ChainRouting`'s flattened `addAll` selector by
selector (`addSelectors_routing`): an `Add` of an unrouted selector to a nonzero facet is
`addSel`, and `_saveFacetIfNew` and the `facetToSelectors` bookkeeping do not touch the routing.
The converse, that a validated release's cuts succeed on a new proxy (`applyFacetCuts_rows_ok`),
needs an invariant of the selector loop (`addSelectors_ok`): every selector already on the facet
has the row's freezability, so the library's freezability check passes.

The creation path is then three calls, each read off its transcription (`createNewChain_spec`,
`migrateInNewChain_spec`). Exactness combines the two directions with the determinism of
`Step.genesis` and `Step.migrateIn`. For runs, a release that was current at some creation step
is still recorded at the end (`run_relAt_low`), so the premise on the final state reaches every
creation. The witnesses and countermodels evaluate the concrete creations with `decide`.
-/

namespace Contracts.ChainTypeManager.GenesisWriters

/-! ## The routing projection -/

lemma routing_eq_none {ds : DiamondStorage} {x : Selector} :
    ds.routing x = none ↔ (ds.selectorToFacet x).facetAddress = 0 := by
  unfold DiamondStorage.routing
  split_ifs with h <;> simp [h]

lemma routing_of_ne {ds : DiamondStorage} {x : Selector}
    (h : (ds.selectorToFacet x).facetAddress ≠ 0) :
    ds.routing x = some ((ds.selectorToFacet x).facetAddress, (ds.selectorToFacet x).isFreezable) := by
  simp [DiamondStorage.routing, h]

lemma routing_some {ds : DiamondStorage} {x : Selector} {f : Address} {b : Bool}
    (h : ds.routing x = some (f, b)) :
    (ds.selectorToFacet x).facetAddress = f ∧ (ds.selectorToFacet x).isFreezable = b ∧ f ≠ 0 := by
  unfold DiamondStorage.routing at h
  split_ifs at h with h0
  cases h
  exact ⟨rfl, rfl, h0⟩

lemma empty_routing : DiamondStorage.empty.routing = emptyRouting := by
  funext x
  simp [DiamondStorage.routing, DiamondStorage.empty, SelectorToFacet.zero, emptyRouting]

/-! ## Frames of the `Add` path -/

@[simp] lemma saveFacetIfNew_selectorToFacet (ds : DiamondStorage) (f : Address) :
    (saveFacetIfNew ds f).selectorToFacet = ds.selectorToFacet := by
  unfold saveFacetIfNew; split_ifs <;> rfl

@[simp] lemma saveFacetIfNew_isFrozen (ds : DiamondStorage) (f : Address) :
    (saveFacetIfNew ds f).isFrozen = ds.isFrozen := by
  unfold saveFacetIfNew; split_ifs <;> rfl

@[simp] lemma saveFacetIfNew_selectors (ds : DiamondStorage) (f g : Address) :
    ((saveFacetIfNew ds f).facetToSelectors g).selectors = (ds.facetToSelectors g).selectors := by
  unfold saveFacetIfNew
  split_ifs
  · by_cases hg : g = f <;> simp [upd, hg]
  · rfl

lemma saveFacetIfNew_facetToSelectors_ne (ds : DiamondStorage) {f g : Address} (hg : g ≠ f) :
    (saveFacetIfNew ds f).facetToSelectors g = ds.facetToSelectors g := by
  unfold saveFacetIfNew; split_ifs <;> simp [upd_ne _ _ hg]

lemma saveFacetIfNew_routing (ds : DiamondStorage) (f : Address) :
    (saveFacetIfNew ds f).routing = ds.routing := by
  funext x; simp [DiamondStorage.routing]

lemma pushSelector_routing (ds : DiamondStorage) {f : Address} (x : Selector) (frz : Bool)
    (hf : f ≠ 0) : (pushSelector ds f x frz).routing = upd ds.routing x (some (f, frz)) := by
  funext y
  by_cases hy : y = x <;> simp [DiamondStorage.routing, pushSelector, upd, hy, hf]

lemma addOneFunction_eq {ds ds' : DiamondStorage} {f : Address} {x : Selector} {frz : Bool}
    (h : addOneFunction ds f x frz = some ds') : ds' = pushSelector ds f x frz := by
  unfold addOneFunction at h
  split at h <;> (try split_ifs at h) <;> exact (Option.some.inj h).symm

/-! ## `Add` cuts refine `addAll` -/

lemma addAll_append : ∀ (ρ : Routing) (A B : ReleaseRows),
    addAll ρ (A ++ B) = (addAll ρ A).bind (fun σ => addAll σ B)
  | ρ, [], B => by simp [addAll]
  | ρ, (x, r) :: A, B => by
    simp only [List.cons_append, addAll]
    cases addSel ρ x r with
    | none => rfl
    | some ρ' => simp only [Option.bind_some]; exact addAll_append ρ' A B

lemma flattenCuts_cons (c : FacetCut) (cs : List FacetCut) :
    flattenCuts (c :: cs) = c.selectors.map (fun x => (x, (c.facet, c.isFreezable))) ++ flattenCuts cs := by
  simp [flattenCuts]

lemma addSelectors_routing {f : Address} {frz : Bool} (hf : f ≠ 0) :
    ∀ {xs : List Selector} {ds ds' : DiamondStorage}, addSelectors f frz ds xs = some ds' →
      addAll ds.routing (xs.map (fun x => (x, (f, frz)))) = some ds'.routing ∧
        ds'.isFrozen = ds.isFrozen
  | [], ds, ds', h => by
    cases h
    exact ⟨rfl, rfl⟩
  | x :: xs, ds, ds', h => by
    simp only [addSelectors] at h
    split_ifs at h with hx
    obtain ⟨ds1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := addOneFunction_eq h1
    obtain ⟨ih1, ih2⟩ := addSelectors_routing hf h
    refine ⟨?_, by rw [ih2]; rfl⟩
    have hn : ds.routing x = none := routing_eq_none.mpr hx
    simpa only [List.map_cons, addAll, addSel, hn, ↓reduceIte, Option.bind_some,
      ← pushSelector_routing ds x frz hf] using ih1

theorem AddCutsRefineAddAll : Properties.AddCutsRefineAddAll := by
  intro hasCode ds ds' cs h0 hadd h
  induction cs generalizing ds with
  | nil =>
    cases h
    exact ⟨by simp [flattenCuts, addAll], rfl⟩
  | cons c cs ih =>
    simp only [applyFacetCuts] at h
    split_ifs at h with hsel
    obtain ⟨ds1, h1, h⟩ := Option.bind_eq_some_iff.mp h
    simp only [applyFacetCut, hadd c List.mem_cons_self, addFunctions] at h1
    split_ifs at h1 with hcode
    have hf : c.facet ≠ 0 := by
      intro hc0
      rw [hc0, h0] at hcode
      exact absurd hcode (by decide)
    obtain ⟨a1, a2⟩ := addSelectors_routing hf h1
    obtain ⟨b1, b2⟩ := ih ds1 (fun c' hc' => hadd c' (List.mem_cons_of_mem _ hc')) h
    rw [saveFacetIfNew_routing] at a1
    exact ⟨by rw [flattenCuts_cons, addAll_append, a1, Option.bind_some]; exact b1,
      by rw [b2, a2, saveFacetIfNew_isFrozen]⟩

/-! ## `DiamondInit` -/

lemma flattenCuts_newChainInstallations (E : Env) (R : Address) :
    flattenCuts (newChainInstallations E R) = releaseRows E R := by
  simp only [flattenCuts, newChainInstallations, releaseRows, List.flatMap_map]

lemma newChainInstallations_add (E : Env) (R : Address) :
    ∀ c ∈ newChainInstallations E R, c.action = .add := by
  intro c hc
  simp only [newChainInstallations, List.mem_map] at hc
  obtain ⟨g, _, rfl⟩ := hc
  rfl

lemma hasCode_zero {E : Env} (h0 : E.code 0 = .none) : E.hasCode 0 = false := by
  simp [Env.hasCode, h0, Code.hasCode]

theorem DiamondInitWrites : Properties.DiamondInitWrites := by
  intro E c id admin st st' h
  unfold diamondInitialize at h
  split_ifs at h with hl hc
  obtain ⟨ds, h1, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨not_not.mp hl, hc, h1, rfl, rfl⟩

theorem DiamondInitInstallsTheRelease : Properties.DiamondInitInstallsTheRelease := by
  intro E c id admin st h0 h
  obtain ⟨-, -, hcut, happ, -⟩ := DiamondInitWrites E c id admin _ _ h
  obtain ⟨hadd, hfz⟩ := AddCutsRefineAddAll E.hasCode DiamondStorage.empty _ _ (hasCode_zero h0)
    (newChainInstallations_add E c.cur) hcut
  rw [empty_routing, flattenCuts_newChainInstallations] at hadd
  refine ⟨hadd, addAll_empty hadd, ?_, ?_⟩
  · rw [hfz]; rfl
  · rw [happ]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem DiamondInitCannotRerun : Properties.DiamondInitCannotRerun := by
  intro E c id admin st hl
  simp [diamondInitialize, hl]

/-! ## The genesis upgrade -/

theorem GenesisUpgradeCutIsEmpty : Properties.GenesisUpgradeCutIsEmpty :=
  fun _ _ => ⟨rfl, rfl, rfl⟩

theorem GenesisUpgradeWritesNoDiamondStorage : Properties.GenesisUpgradeWritesNoDiamondStorage := by
  intro E c st st' hcode h
  unfold adminGenesisUpgrade diamondCut genesisUpgradeCut at h
  simp only [applyFacetCuts, Option.bind_some] at h
  unfold initializeDiamondCut at h
  by_cases hz : E.genesisUpgradeOf c.cur = 0
  · simp [hz] at h
  · simp only [hz, ↓reduceIte, runInit, hcode] at h
    unfold l1GenesisUpgradeRun at h
    split_ifs at h
    simp only [Option.some.injEq] at h
    subst h
    exact ⟨rfl, rfl, rfl⟩

/-! ## The calls through the proxy -/

lemma proxyCall_spec {E : Env} {c : CTM} {st st' : ChainState} {call : ProxyCall}
    (h : proxyCall E c st call = some st') :
    ∃ f b, st.diamond.routing call.selector = some (f, b) ∧
      runFacet E c (E.code f) call st = some st' := by
  unfold proxyCall at h
  split_ifs at h with h0 h1
  exact ⟨_, _, routing_of_ne h0, h⟩

lemma pauseDeposits_spec {ts : ℕ} {st st' : ChainState} (h : pauseDeposits ts st = some st') :
    st'.diamond = st.diamond ∧ st'.app.protocolVersion = st.app.protocolVersion := by
  unfold pauseDeposits at h
  split_ifs at h
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨rfl, rfl⟩

lemma migratorForwardedBridgeMint_spec {c : CTM} {txHash batch : ℕ} {st st' : ChainState}
    (h : migratorForwardedBridgeMint c txHash batch st = some st') :
    st.app.protocolVersion = c.pv ∧ st'.diamond = st.diamond ∧
      st'.app.protocolVersion = st.app.protocolVersion := by
  unfold migratorForwardedBridgeMint at h
  split_ifs at h with hv
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨not_not.mp hv, rfl, rfl⟩

/-! ## The creation paths -/

lemma deployNewChain_spec {E : Env} {c : CTM} {id : ChainId} {admin : Address} {st : ChainState}
    (hdi : E.code (E.diamondInitOf c.cur) = .diamondInit)
    (h : deployNewChain E c id admin = some st) :
    diamondInitialize E c id admin ChainState.fresh = some st := by
  unfold deployNewChain diamondCut genesisCut at h
  simp only [applyFacetCuts, Option.bind_some] at h
  unfold initializeDiamondCut at h
  by_cases hz : E.diamondInitOf c.cur = 0
  · simp [hz] at h
  · simp only [hz, ↓reduceIte, runInit, hdi] at h
    exact h

/-- What a successful `createNewChain` leaves, read off its three calls. -/
lemma createNewChain_spec {W : World} {E : Env} {c : CTM} {id : ChainId} {admin : Address}
    {ts : ℕ} {st : ChainState} (h0 : E.code 0 = .none) (hG : GenuineRelease E W c.cur)
    (h : createNewChain E c id admin ts = some st) :
    st.app.protocolVersion = c.pv ∧ addAll emptyRouting (W.relRows c.cur) = some st.diamond.routing := by
  unfold createNewChain at h
  obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨st2, h2, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hadd, hrt, -, hpv, -⟩ :=
    DiamondInitInstallsTheRelease E c id admin st1 h0 (deployNewChain_spec hG.diamondInit h1)
  -- `genesisUpgrade()` reaches the Admin facet
  obtain ⟨f, b, hfb, hrun⟩ := proxyCall_spec h2
  rw [hG.adminFacet f b (by rw [← hrt]; exact hfb)] at hrun
  obtain ⟨hd2, -, ha2⟩ := GenesisUpgradeWritesNoDiamondStorage E c st1 st2 hG.genesisUpgrade hrun
  -- `pauseDepositsBeforeInitiatingMigration()` reaches the Migrator facet
  obtain ⟨f', b', hfb', hrun'⟩ := proxyCall_spec h
  rw [hG.migratorFacet _ (Or.inl rfl) f' b' (by rw [← hrt, ← hd2]; exact hfb')] at hrun'
  obtain ⟨hd3, hpv3⟩ := pauseDeposits_spec hrun'
  exact ⟨by rw [hpv3, ha2]; exact hpv, by rw [hd3, hd2, hG.rows]; exact hadd⟩

/-- What a successful migration-in deployment leaves. -/
lemma migrateInNewChain_spec {W : World} {E : Env} {c : CTM} {v : ℕ} {id : ChainId}
    {admin : Address} {txHash batch : ℕ} {st : ChainState} (h0 : E.code 0 = .none)
    (hG : GenuineRelease E W c.cur) (h : migrateInNewChain E c v id admin txHash batch = some st) :
    v = c.pv ∧ st.app.protocolVersion = c.pv ∧
      addAll emptyRouting (W.relRows c.cur) = some st.diamond.routing := by
  unfold migrateInNewChain at h
  split_ifs at h with hv
  obtain ⟨st1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨hadd, hrt, -, hpv, -⟩ :=
    DiamondInitInstallsTheRelease E c id admin st1 h0 (deployNewChain_spec hG.diamondInit h1)
  obtain ⟨f, b, hfb, hrun⟩ := proxyCall_spec h
  rw [hG.migratorFacet _ (Or.inr rfl) f b (by rw [← hrt]; exact hfb)] at hrun
  obtain ⟨-, hd, hpv'⟩ := migratorForwardedBridgeMint_spec hrun
  exact ⟨not_not.mp hv, by rw [hpv', hpv], by rw [hd, hG.rows]; exact hadd⟩

theorem CodeCreationIsAStep : Properties.CodeCreationIsAStep := by
  intro W E s s' l h0 hG h
  cases h with
  | @createNewChain id admin ts st hnone hc =>
    obtain ⟨hpv, hadd⟩ := createNewChain_spec h0 hG hc
    have hch : st.chain = ⟨s.ctm.pv, st.diamond.routing⟩ := by
      simp only [ChainState.chain, hpv]
    rw [hch]
    exact Step.genesis hnone hadd
  | @forwardedBridgeMint id admin v txHash batch st hnone hc =>
    obtain ⟨hv, hpv, hadd⟩ := migrateInNewChain_spec h0 hG hc
    have hch : st.chain = ⟨v, st.diamond.routing⟩ := by
      simp only [ChainState.chain, hpv, hv]
    rw [hch]
    exact Step.migrateIn v hv hnone hadd

/-! ## Enabledness: a validated release's cuts succeed on a new proxy -/

lemma pushSelector_facetToSelectors_ne (ds : DiamondStorage) {f g : Address} (x : Selector)
    (frz : Bool) (hg : g ≠ f) : (pushSelector ds f x frz).facetToSelectors g = ds.facetToSelectors g := by
  simp [pushSelector, upd_ne _ _ hg]

lemma pushSelector_selectorToFacet_ne (ds : DiamondStorage) (f : Address) {x y : Selector}
    (frz : Bool) (hy : y ≠ x) : (pushSelector ds f x frz).selectorToFacet y = ds.selectorToFacet y := by
  simp [pushSelector, upd_ne _ _ hy]

/-- **The selector loop succeeds** on distinct unrouted selectors, when every selector already on
the facet has the row's freezability; it touches only that facet's list and those selectors. -/
lemma addSelectors_ok {f : Address} {frz : Bool} :
    ∀ {xs : List Selector} {ds : DiamondStorage}, xs.Nodup →
      (∀ x ∈ xs, (ds.selectorToFacet x).facetAddress = 0) →
      (∀ y ∈ (ds.facetToSelectors f).selectors, (ds.selectorToFacet y).isFreezable = frz) →
      ∃ ds', addSelectors f frz ds xs = some ds' ∧
        (∀ g, g ≠ f → ds'.facetToSelectors g = ds.facetToSelectors g) ∧
        (∀ y, y ∉ xs → ds'.selectorToFacet y = ds.selectorToFacet y)
  | [], ds, _, _, _ => ⟨ds, rfl, fun _ _ => rfl, fun _ _ => rfl⟩
  | x :: xs, ds, hnd, hfree, hfrz => by
    rw [List.nodup_cons] at hnd
    have hx : (ds.selectorToFacet x).facetAddress = 0 := hfree x (by simp)
    have hadd : addOneFunction ds f x frz = some (pushSelector ds f x frz) := by
      unfold addOneFunction
      split
      · rfl
      · next y ys hys =>
        have hy : (ds.selectorToFacet y).isFreezable = frz := hfrz y (by rw [hys]; simp)
        simp [hy]
    obtain ⟨ds', h1, h2, h3⟩ := addSelectors_ok (f := f) (frz := frz)
      (ds := pushSelector ds f x frz) hnd.2
      (fun x' hx' => by
        have hne : x' ≠ x := fun h => hnd.1 (h ▸ hx')
        rw [pushSelector_selectorToFacet_ne _ _ _ hne]
        exact hfree x' (by simp [hx']))
      (fun y hy => by
        simp only [pushSelector, upd_same, List.mem_append, List.mem_singleton] at hy
        by_cases hyx : y = x
        · subst hyx; simp [pushSelector]
        · rw [pushSelector_selectorToFacet_ne _ _ _ hyx]
          exact hfrz y (hy.resolve_right hyx))
    refine ⟨ds', ?_, ?_, ?_⟩
    · simp only [addSelectors, hx, ↓reduceIte, hadd, Option.bind_some]; exact h1
    · intro g hg; rw [h2 g hg, pushSelector_facetToSelectors_ne _ _ _ hg]
    · intro y hy
      simp only [List.mem_cons, not_or] at hy
      rw [h3 y hy.2, pushSelector_selectorToFacet_ne _ _ _ hy.1]

/-- **A release's cuts succeed** on a diamond where none of its facets has selectors and none of
its selectors is routed, when its facet rows are distinct, have code and selectors, and route
no selector twice. -/
lemma applyFacetCuts_rows_ok (E : Env) :
    ∀ {gs : List GenesisFacet} {ds : DiamondStorage},
      (gs.map GenesisFacet.facet).Nodup →
      (∀ g ∈ gs, E.hasCode g.facet = true) →
      (∀ g ∈ gs, E.selectorsOf g.facet ≠ []) →
      (gs.flatMap (fun g => E.selectorsOf g.facet)).Nodup →
      (∀ g ∈ gs, (ds.facetToSelectors g.facet).selectors = []) →
      (∀ g ∈ gs, ∀ x ∈ E.selectorsOf g.facet, (ds.selectorToFacet x).facetAddress = 0) →
      ∃ ds', applyFacetCuts E.hasCode ds
        (gs.map (fun g => (⟨g.facet, .add, g.isFreezable, E.selectorsOf g.facet⟩ : FacetCut))) =
          some ds'
  | [], ds, _, _, _, _, _, _ => ⟨ds, rfl⟩
  | g :: gs, ds, huf, hcode, hne, hus, hfac, hfree => by
    simp only [List.map_cons, List.nodup_cons] at huf
    rw [List.flatMap_cons, List.nodup_append] at hus
    obtain ⟨hnd1, hnd2, hdisj⟩ := hus
    obtain ⟨ds1, h1, h2, h3⟩ := addSelectors_ok (f := g.facet) (frz := g.isFreezable)
      (ds := saveFacetIfNew ds g.facet) hnd1
      (fun x hx => by rw [saveFacetIfNew_selectorToFacet]; exact hfree g (by simp) x hx)
      (fun y hy => by
        rw [saveFacetIfNew_selectors, hfac g (by simp)] at hy
        simp at hy)
    obtain ⟨ds', h'⟩ := applyFacetCuts_rows_ok E (gs := gs) (ds := ds1) huf.2
      (fun g' hg' => hcode g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' => hne g' (List.mem_cons_of_mem _ hg'))
      hnd2
      (fun g' hg' => by
        have hne' : g'.facet ≠ g.facet := fun h => huf.1 (h ▸ List.mem_map_of_mem hg')
        rw [h2 _ hne', saveFacetIfNew_facetToSelectors_ne _ hne']
        exact hfac g' (List.mem_cons_of_mem _ hg'))
      (fun g' hg' x hx => by
        have hxg : x ∉ E.selectorsOf g.facet := fun hm =>
          hdisj x hm x (List.mem_flatMap.mpr ⟨g', hg', hx⟩) rfl
        rw [h3 x hxg, saveFacetIfNew_selectorToFacet]
        exact hfree g' (List.mem_cons_of_mem _ hg') x hx)
    refine ⟨ds', ?_⟩
    simp only [List.map_cons, applyFacetCuts, hne g (by simp), ↓reduceIte, applyFacetCut,
      addFunctions, hcode g (by simp), h1, Option.bind_some]
    exact h'

lemma releaseRows_fst (E : Env) (R : Address) :
    (releaseRows E R).map Prod.fst = (E.genesisFacets R).flatMap (fun g => E.selectorsOf g.facet) := by
  simp [releaseRows, List.map_flatMap, Function.comp_def]

lemma diamondInitialize_fresh_ok {E : Env} {c : CTM} {id : ChainId} {admin : Address}
    (hc : c.cur ≠ 0) (hwf : ReleaseWf E c.cur) :
    ∃ st, diamondInitialize E c id admin ChainState.fresh = some st := by
  obtain ⟨ds, h⟩ := applyFacetCuts_rows_ok E (gs := E.genesisFacets c.cur) (ds := DiamondStorage.empty)
    hwf.uniqueFacets hwf.facetsHaveCode hwf.selectorsNonempty
    (by rw [← releaseRows_fst]; exact hwf.uniqueSelectors)
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)
  simp [diamondInitialize, ChainState.fresh, newChainInstallations, h, hc]

lemma proxyCall_of_routed {E : Env} {c : CTM} {st : ChainState} {call : ProxyCall} {f : Address}
    {b : Bool} (hr : st.diamond.routing call.selector = some (f, b))
    (hfz : st.diamond.isFrozen = false) :
    proxyCall E c st call = runFacet E c (E.code f) call st := by
  obtain ⟨h1, -, h3⟩ := routing_some hr
  simp [proxyCall, h1, h3, hfz]

lemma code_ne_zero {E : Env} {a : Address} {k : Code} (h0 : E.code 0 = .none) (ha : E.code a = k)
    (hk : k.hasCode = true) : a ≠ 0 := by
  rintro rfl
  rw [h0] at ha
  subst ha
  exact absurd hk (by decide)

/-- After `DiamondInit` on a new proxy, the genesis upgrade runs and writes only the L2 upgrade
transaction hash. -/
lemma adminGenesisUpgrade_ok {E : Env} {c : CTM} {st : ChainState} (h0 : E.code 0 = .none)
    (hgu : E.code (E.genesisUpgradeOf c.cur) = .l1GenesisUpgrade)
    (hsl : st.app.settlementLayer = 0) (hh : st.app.l2SystemContractsUpgradeTxHash = 0)
    (hb : st.app.l2SystemContractsUpgradeBatchNumber = 0) :
    ∃ st', adminGenesisUpgrade E c st = some st' := by
  have hz : E.genesisUpgradeOf c.cur ≠ 0 := code_ne_zero h0 hgu rfl
  simp [adminGenesisUpgrade, diamondCut, genesisUpgradeCut, applyFacetCuts, initializeDiamondCut,
    hz, runInit, hgu, l1GenesisUpgradeRun, hsl, hh, hb]

/-- With `DiamondInit` at the release's `diamondInit()`, deploying is running it on a new proxy. -/
lemma deployNewChain_eq {E : Env} {c : CTM} {id : ChainId} {admin : Address}
    (h0 : E.code 0 = .none) (hdi : E.code (E.diamondInitOf c.cur) = .diamondInit) :
    deployNewChain E c id admin = diamondInitialize E c id admin ChainState.fresh := by
  have hz : E.diamondInitOf c.cur ≠ 0 := code_ne_zero h0 hdi rfl
  unfold deployNewChain diamondCut genesisCut
  simp only [applyFacetCuts, Option.bind_some]
  unfold initializeDiamondCut
  simp only [hz, ↓reduceIte, runInit, hdi]

lemma deployNewChain_ok {E : Env} {c : CTM} {id : ChainId} {admin : Address} {st : ChainState}
    (h0 : E.code 0 = .none) (hdi : E.code (E.diamondInitOf c.cur) = .diamondInit)
    (h : diamondInitialize E c id admin ChainState.fresh = some st) :
    deployNewChain E c id admin = some st := by
  rw [deployNewChain_eq h0 hdi]; exact h

theorem ValidatedReleaseCreatesChains : Properties.ValidatedReleaseCreatesChains := by
  intro W E c id admin ts h0 hc hG hwf hA hM
  obtain ⟨st1, h1⟩ := diamondInitialize_fresh_ok (id := id) (admin := admin) hc hwf
  obtain ⟨-, hrt, hfz, -, -, hsl, hh, hb, hp⟩ := DiamondInitInstallsTheRelease E c id admin st1 h0 h1
  obtain ⟨st2, h2⟩ := adminGenesisUpgrade_ok (c := c) h0 hG.genesisUpgrade hsl hh hb
  obtain ⟨hd2, -, ha2⟩ := GenesisUpgradeWritesNoDiamondStorage E c st1 st2 hG.genesisUpgrade h2
  obtain ⟨f, b, hfb, hfa⟩ := hA
  obtain ⟨f', b', hfb', hfm⟩ := hM
  have hp1 : proxyCall E c st1 .genesisUpgrade = some st2 := by
    rw [proxyCall_of_routed (f := f) (b := b) (by rw [hrt]; exact hfb) hfz, hfa]
    exact h2
  have hp2 : proxyCall E c st2 (.pauseDeposits ts) = runFacet E c (E.code f') (.pauseDeposits ts) st2 :=
    proxyCall_of_routed (b := b') (by rw [hd2, hrt]; exact hfb') (by rw [hd2]; exact hfz)
  rw [hfm] at hp2
  have hp0 : st2.app.pausedDepositsTimestamp = 0 := by rw [ha2]; exact hp
  unfold createNewChain
  rw [deployNewChain_ok h0 hG.diamondInit h1, Option.bind_some, hp1, Option.bind_some, hp2]
  simp [runFacet, pauseDeposits, hp0]

theorem ValidatedReleaseMigratesChainsIn : Properties.ValidatedReleaseMigratesChainsIn := by
  intro W E c id admin txHash batch h0 hc hG hwf hM
  obtain ⟨st1, h1⟩ := diamondInitialize_fresh_ok (id := id) (admin := admin) hc hwf
  obtain ⟨-, hrt, hfz, hpv, -⟩ := DiamondInitInstallsTheRelease E c id admin st1 h0 h1
  obtain ⟨f, b, hfb, hfm⟩ := hM
  have hp : proxyCall E c st1 (.forwardedBridgeMint txHash batch) =
      runFacet E c (E.code f) (.forwardedBridgeMint txHash batch) st1 :=
    proxyCall_of_routed (b := b) (by rw [hrt]; exact hfb) hfz
  rw [hfm] at hp
  unfold migrateInNewChain
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  rw [deployNewChain_ok h0 hG.diamondInit h1, Option.bind_some, hp]
  simp [runFacet, migratorForwardedBridgeMint, hpv]

/-! ## Exactness -/

/-- `Step.genesis` is deterministic. -/
lemma step_genesis_inv {W : World} {s s' : Sys} {id : ChainId} (h : Step W s (.genesis id) s') :
    s.chains id = none ∧ ∃ ρ, addAll emptyRouting (W.relRows s.ctm.cur) = some ρ ∧
      s' = { s with chains := upd s.chains id (some ⟨s.ctm.pv, ρ⟩) } := by
  cases h with
  | genesis hnone hadd => exact ⟨hnone, _, hadd, rfl⟩

/-- `Step.migrateIn` is deterministic. -/
lemma step_migrateIn_inv {W : World} {s s' : Sys} {id : ChainId} (h : Step W s (.migrateIn id) s') :
    s.chains id = none ∧ ∃ ρ, addAll emptyRouting (W.relRows s.ctm.cur) = some ρ ∧
      s' = { s with chains := upd s.chains id (some ⟨s.ctm.pv, ρ⟩) } := by
  cases h with
  | migrateIn v hv hnone hadd => subst hv; exact ⟨hnone, _, hadd, rfl⟩

theorem GenesisStepIsExact : Properties.GenesisStepIsExact := by
  intro W E s s' id h0 hc hG hwf hA hM
  refine ⟨CodeCreationIsAStep W E s s' _ h0 hG, fun h => ?_⟩
  obtain ⟨hnone, ρ, hadd, rfl⟩ := step_genesis_inv h
  obtain ⟨st, hst⟩ := ValidatedReleaseCreatesChains W E s.ctm id 0 0 h0 hc hG hwf hA hM
  obtain ⟨hpv, hadd'⟩ := createNewChain_spec h0 hG hst
  have hρ : st.diamond.routing = ρ := Option.some.inj (hadd'.symm.trans hadd)
  have hch : st.chain = ⟨s.ctm.pv, ρ⟩ := by simp only [ChainState.chain, hpv, hρ]
  simpa only [hch] using CodeCreation.createNewChain (E := E) (s := s) hnone hst

theorem MigrateInStepIsExact : Properties.MigrateInStepIsExact := by
  intro W E s s' id h0 hc hG hwf hM
  refine ⟨CodeCreationIsAStep W E s s' _ h0 hG, fun h => ?_⟩
  obtain ⟨hnone, ρ, hadd, rfl⟩ := step_migrateIn_inv h
  obtain ⟨st, hst⟩ := ValidatedReleaseMigratesChainsIn W E s.ctm id 0 0 0 h0 hc hG hwf hM
  obtain ⟨-, hpv, hadd'⟩ := migrateInNewChain_spec h0 hG hst
  have hρ : st.diamond.routing = ρ := Option.some.inj (hadd'.symm.trans hadd)
  have hch : st.chain = ⟨s.ctm.pv, ρ⟩ := by simp only [ChainState.chain, hpv, hρ]
  simpa only [hch] using CodeCreation.forwardedBridgeMint (E := E) (s := s) hnone hst

theorem CodeStepIsExact : Properties.CodeStepIsExact := by
  intro W E s s' l h0 hc hG hwf hA hM hF
  cases l with
  | genesis id =>
    refine ⟨fun h => ?_, fun h => CodeStep.create ((GenesisStepIsExact W E s s' id h0 hc hG hwf hA hM).mpr h)⟩
    cases h with
    | create hcc => exact (GenesisStepIsExact W E s s' id h0 hc hG hwf hA hM).mp hcc
    | other hl _ => exact absurd trivial hl
  | migrateIn id =>
    refine ⟨fun h => ?_, fun h => CodeStep.create ((MigrateInStepIsExact W E s s' id h0 hc hG hwf hF).mpr h)⟩
    cases h with
    | create hcc => exact (MigrateInStepIsExact W E s s' id h0 hc hG hwf hF).mp hcc
    | other hl _ => exact absurd trivial hl
  | _ =>
    refine ⟨fun h => ?_, fun h => CodeStep.other (fun h => h) h⟩
    cases h with
    | create hcc => cases hcc
    | other _ hs => exact hs

/-! ## Runs -/

lemma codeCreation_ctm {E : Env} {s s' : Sys} {l : Label} (h : CodeCreation E s l s') :
    s'.ctm = s.ctm := by
  cases h <;> rfl

lemma step_pv_le {W : World} {s s' : Sys} {l : Label} (h : Step W s l s') : s.ctm.pv ≤ s'.ctm.pv := by
  cases h with
  | ctm hc => exact (cstep_pv hc).1
  | _ => exact le_rfl

lemma step_relAt_low {W : World} {s s' : Sys} {l : Label} (h : Step W s l s') :
    ∀ w, w ≤ s.ctm.pv → s'.ctm.relAt w = s.ctm.relAt w := by
  intro w hw
  cases h with
  | ctm hc => exact cstep_relAt_low hc w hw
  | _ => rfl

/-- Releases recorded at or below the current version survive any run. -/
lemma run_relAt_low {W : World} {s s' : Sys} {ls : List Label} (h : Run W s ls s') :
    ∀ w, w ≤ s.ctm.pv → s'.ctm.relAt w = s.ctm.relAt w := by
  induction h with
  | nil => intro w _; rfl
  | cons hs _ ih =>
    intro w hw
    rw [ih w (le_trans hw (step_pv_le hs)), step_relAt_low hs w hw]

theorem CodeRunIsARun : Properties.CodeRunIsARun := by
  intro W E s s' ls h0 hI h hG
  induction h with
  | nil => exact Run.nil
  | @cons s s1 s2 l ls hstep _ ih =>
    cases hstep with
    | create hc =>
      have hctm : s1.ctm = s.ctm := codeCreation_ctm hc
      have hrun : Run W s1 ls s2 := ih (by rw [hctm]; exact hI) hG
      -- the release current at this creation is still recorded at the end
      have hcur : s2.ctm.relAt s.ctm.pv = s.ctm.cur := by
        rw [run_relAt_low hrun s.ctm.pv (by rw [hctm]), hctm, hI.curAtVersion]
      have hGc : GenuineRelease E W s.ctm.cur := by
        have := hG s.ctm.pv (by rw [hcur]; exact hI.curNonzero)
        rwa [hcur] at this
      exact Run.cons (CodeCreationIsAStep W E s s1 l h0 hGc hc) hrun
    | other _ hs =>
      exact Run.cons hs (ih (step_ctmInv hI hs) hG)

theorem CodeRunsKeepChainsOnTheirRelease : Properties.CodeRunsKeepChainsOnTheirRelease := by
  intro W E s s' ls h0 hI h hl hG
  exact ChainsRunTheirVersionsRelease W s s' ls hI (CodeRunIsARun W E s s' ls h0 hI.1 h hG) hl

/-! ## The witness environments -/

lemma rowsRouting_mem : ∀ {A : ReleaseRows} {x : Selector} {r : Route},
    rowsRouting A x = some r → (x, r) ∈ A
  | [], _, _, h => by simp [rowsRouting] at h
  | (y, r') :: A, x, r, h => by
    simp only [rowsRouting] at h
    split_ifs at h with hxy
    · cases h; subst hxy; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (rowsRouting_mem h)

lemma releaseRows_mem {E : Env} {R : Address} {x : Selector} {f : Address} {b : Bool}
    (h : (x, (f, b)) ∈ releaseRows E R) :
    (⟨f, b⟩ : GenesisFacet) ∈ E.genesisFacets R ∧ x ∈ E.selectorsOf f := by
  simp only [releaseRows, List.mem_flatMap, List.mem_map, Prod.mk.injEq] at h
  obtain ⟨g, hg, y, hy, rfl, rfl, rfl⟩ := h
  exact ⟨hg, hy⟩

lemma gSelectors_admin {f : Address} (h : selGenesisUpgrade ∈ gSelectors f) : f ∈ gAdminFacets := by
  unfold gSelectors at h
  split_ifs at h with h1 h2
  · exact h1
  · exact absurd h (by decide)
  · exact absurd h (by simp)

lemma gSelectors_migrator {f : Address} {x : Selector}
    (hx : x = selPauseDeposits ∨ x = selForwardedBridgeMint) (h : x ∈ gSelectors f) :
    f ∈ gMigratorFacets := by
  unfold gSelectors at h
  split_ifs at h with h1 h2
  · rcases hx with rfl | rfl <;> exact absurd h (by decide)
  · exact h2
  · exact absurd h (by simp)

lemma gCode_admin {f : Address} (h : f ∈ gAdminFacets) : gCode f = .adminFacet := by
  simp only [gAdminFacets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> rfl

lemma gCode_migrator {f : Address} (h : f ∈ gMigratorFacets) : gCode f = .migratorFacet := by
  simp only [gMigratorFacets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> rfl

/-- In any environment with the witness self-descriptions, the routed facet of an entry point is
one of the witness Admin or Migrator facets. -/
lemma g_entry_admin {E : Env} (hsel : E.selectorsOf = gSelectors) {R : Address} {f : Address}
    {b : Bool} (h : rowsRouting (releaseRows E R) selGenesisUpgrade = some (f, b)) :
    f ∈ gAdminFacets := by
  have := (releaseRows_mem (rowsRouting_mem h)).2
  rw [hsel] at this
  exact gSelectors_admin this

lemma g_entry_migrator {E : Env} (hsel : E.selectorsOf = gSelectors) {R : Address} {x : Selector}
    (hx : x = selPauseDeposits ∨ x = selForwardedBridgeMint) {f : Address} {b : Bool}
    (h : rowsRouting (releaseRows E R) x = some (f, b)) : f ∈ gMigratorFacets := by
  have := (releaseRows_mem (rowsRouting_mem h)).2
  rw [hsel] at this
  exact gSelectors_migrator hx this

/-- **Every release of the witness world is genuine.** -/
lemma gEnv_genuine (R : Address) : GenuineRelease gEnv gWorld R where
  diamondInit := rfl
  genesisUpgrade := rfl
  adminFacet := fun _ _ h => gCode_admin (g_entry_admin rfl h)
  migratorFacet := fun _ hx _ _ h => gCode_migrator (g_entry_migrator rfl hx h)
  rows := rfl

lemma gAdmin_ne {f : Address} (h : f ∈ gAdminFacets) : f ≠ 7 ∧ f ≠ 8 ∧ f ≠ 13 := by
  simp only [gAdminFacets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

lemma gMigrator_ne {f : Address} (h : f ∈ gMigratorFacets) : f ≠ 7 ∧ f ≠ 8 ∧ f ≠ 13 := by
  simp only [gMigratorFacets, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl <;> decide

lemma gReleaseWf100 : ReleaseWf gEnv 100 where
  uniqueFacets := by decide
  facetsHaveCode := by decide
  selectorsNonempty := by decide
  uniqueSelectors := by decide

lemma gReleaseWf200 : ReleaseWf gEnv 200 where
  uniqueFacets := by decide
  facetsHaveCode := by decide
  selectorsNonempty := by decide
  uniqueSelectors := by decide

/-! ## Witnesses -/

theorem GenesisWritersWitness : Properties.GenesisWritersWitness := by
  have h0 : gEnv.code 0 = .none := rfl
  have hc : (initState gWorld 100).cur ≠ 0 := by decide
  obtain ⟨st, hst⟩ := diamondInitialize_fresh_ok (c := initState gWorld 100) (id := 0) (admin := 1)
    hc gReleaseWf100
  obtain ⟨-, -, hcut, -, -⟩ := DiamondInitWrites gEnv _ 0 1 _ _ hst
  obtain ⟨-, -, -, -, -, hsl, hh, hb, -⟩ := DiamondInitInstallsTheRelease gEnv _ 0 1 st h0 hst
  obtain ⟨st', hst'⟩ := adminGenesisUpgrade_ok (c := initState gWorld 100) h0 rfl hsl hh hb
  exact ⟨h0, rfl, gEnv_genuine 100, gReleaseWf100, ⟨11, false, by decide, rfl⟩,
    ⟨12, true, by decide, rfl⟩, ⟨12, true, by decide, rfl⟩, newChainInstallations_add gEnv 100,
    ⟨_, hcut⟩, ⟨st, hst⟩, st, st', deployNewChain_ok h0 rfl hst, hst'⟩

private lemma gNodup100 : ((gWorld.relRows 100).map Prod.fst).Nodup := by decide
private lemma gNodup200 : ((gWorld.relRows 200).map Prod.fst).Nodup := by decide

/-- A code-level creation step on a validated, genuine release, with the system it leaves. -/
lemma create_step {W : World} {E : Env} {s : Sys} {id : ChainId} (h0 : E.code 0 = .none)
    (hc : s.ctm.cur ≠ 0) (hG : GenuineRelease E W s.ctm.cur) (hwf : ReleaseWf E s.ctm.cur)
    (hA : RoutesTo E s.ctm.cur selGenesisUpgrade .adminFacet)
    (hM : RoutesTo E s.ctm.cur selPauseDeposits .migratorFacet) (hnone : s.chains id = none) :
    CodeStep W E s (.genesis id)
      { s with chains := upd s.chains id (some ⟨s.ctm.pv, rowsRouting (W.relRows s.ctm.cur)⟩) } := by
  obtain ⟨st, hst⟩ := ValidatedReleaseCreatesChains W E s.ctm id 1 0 h0 hc hG hwf hA hM
  obtain ⟨hpv, hadd⟩ := createNewChain_spec h0 hG hst
  have hch : st.chain = ⟨s.ctm.pv, rowsRouting (W.relRows s.ctm.cur)⟩ := by
    simp only [ChainState.chain, hpv, addAll_empty hadd]
  exact CodeStep.create (hch ▸ CodeCreation.createNewChain (E := E) (s := s) hnone hst)

theorem CodeRunWitness : Properties.CodeRunWitness := by
  have h0 : gEnv.code 0 = .none := rfl
  have hI0 : SysInv gWorld gSys0 := FreshSystemSatisfiesInvariant gWorld 100 (by decide)
  have hA100 : RoutesTo gEnv 100 selGenesisUpgrade .adminFacet := ⟨11, false, by decide, rfl⟩
  have hM100 : RoutesTo gEnv 100 selPauseDeposits .migratorFacet := ⟨12, true, by decide, rfl⟩
  have hA200 : RoutesTo gEnv 200 selGenesisUpgrade .adminFacet := ⟨21, false, by decide, rfl⟩
  have hM200 : RoutesTo gEnv 200 selPauseDeposits .migratorFacet := ⟨22, true, by decide, rfl⟩
  have hrun := CodeRun.cons (W := gWorld) (E := gEnv)
    (create_step (s := gSys0) (id := 0) h0 (by decide) (gEnv_genuine _) gReleaseWf100 hA100 hM100 rfl)
    (CodeRun.cons (CodeStep.other (by simp [creationLabel])
        (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))))
      (CodeRun.cons (CodeStep.other (by simp [creationLabel])
          (Step.transition (id := 0) rfl (by decide) rfl
            (applyDerived_rows_eq gNodup100 gNodup200) (by decide)))
        (CodeRun.cons (create_step (id := 1) h0 (by decide) (gEnv_genuine _)
            (by exact gReleaseWf200) (by exact hA200) (by exact hM200) rfl) CodeRun.nil)))
  exact ⟨h0, hI0, _, hrun, fun _ _ => gEnv_genuine _, ⟨_, rfl, by decide, rfl⟩,
    ⟨_, rfl, by decide, rfl⟩, fun h => absurd (congrFun h 1) (by decide)⟩

/-! ## Countermodels -/

lemma fInit_code {f : Address} (h : f ≠ 7) : fInitEnv.code f = gCode f := by
  simp [fInitEnv, h]

lemma fUpgrade_code {f : Address} (h : f ≠ 8) : fUpgradeEnv.code f = gCode f := by
  simp [fUpgradeEnv, h]

lemma eCode {f : Address} (h : f ≠ 13) : eEnv.code f = gCode f := by
  simp [eEnv, h]

theorem ForeignDiamondInitBreaksGenesis : Properties.ForeignDiamondInitBreaksGenesis := by
  have hI0 : SysInv gWorld gSys0 := FreshSystemSatisfiesInvariant gWorld 100 (by decide)
  have hsome : (createNewChain fInitEnv gSys0.ctm 0 1 0).isSome = true := by decide
  obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hsome
  have hfacts : (createNewChain fInitEnv gSys0.ctm 0 1 0).map
      (fun st => (st.app.protocolVersion, st.diamond.routing 1)) = some (1, none) := by decide
  rw [hst] at hfacts
  obtain ⟨hpv, hr1⟩ := Prod.mk.inj (Option.some.inj hfacts)
  have hrow1 : rowsRouting (gWorld.relRows 100) 1 = some (11, false) := by decide
  have hrel : gSys0.ctm.relAt 1 = 100 := by decide
  have hne : st.chain.routing ≠ rowsRouting (gWorld.relRows 100) := fun h => by
    have h1 := congrFun h 1
    rw [hrow1] at h1
    exact absurd (hr1.symm.trans h1) (by simp)
  have hcc : CodeCreation fInitEnv gSys0 (.genesis 0)
      { gSys0 with chains := upd gSys0.chains 0 (some st.chain) } :=
    CodeCreation.createNewChain rfl hst
  have hnot : ¬ SysInv gWorld { gSys0 with chains := upd gSys0.chains 0 (some st.chain) } := by
    rintro ⟨-, hch⟩
    have hok : st.app.protocolVersion ≤ gSys0.ctm.pv ∧
        (gSys0.ctm.relAt st.app.protocolVersion ≠ 0 →
          st.diamond.routing = rowsRouting (gWorld.relRows (gSys0.ctm.relAt st.app.protocolVersion))) :=
      hch 0 st.chain rfl
    rw [hpv, hrel] at hok
    exact hne (hok.2 (by decide))
  refine ⟨rfl, rfl, fun f b h => ?_, fun x hx f b h => ?_, rfl, hI0, _, hcc,
    ⟨st.chain, rfl, hpv, hrel, hne⟩, hnot,
    fun hs => hnot (step_sysInv hI0 hs (fun h => h))⟩
  · rw [fInit_code (gAdmin_ne (g_entry_admin rfl h)).1]
    exact gCode_admin (g_entry_admin rfl h)
  · rw [fInit_code (gMigrator_ne (g_entry_migrator rfl hx h)).1]
    exact gCode_migrator (g_entry_migrator rfl hx h)

theorem ForeignGenesisUpgradeBreaksGenesis : Properties.ForeignGenesisUpgradeBreaksGenesis := by
  have hI0 : SysInv gWorld gSys0 := FreshSystemSatisfiesInvariant gWorld 100 (by decide)
  have hsome : (createNewChain fUpgradeEnv gSys0.ctm 0 1 0).isSome = true := by decide
  obtain ⟨st, hst⟩ := Option.isSome_iff_exists.mp hsome
  have hfacts : (createNewChain fUpgradeEnv gSys0.ctm 0 1 0).map
      (fun st => (st.app.protocolVersion, st.diamond.routing 9)) = some (1, some (99, false)) := by
    decide
  rw [hst] at hfacts
  obtain ⟨hpv, hr9⟩ := Prod.mk.inj (Option.some.inj hfacts)
  have hrow9 : rowsRouting (gWorld.relRows 100) 9 = none := by decide
  have hrel : gSys0.ctm.relAt 1 = 100 := by decide
  have hcc : CodeCreation fUpgradeEnv gSys0 (.genesis 0)
      { gSys0 with chains := upd gSys0.chains 0 (some st.chain) } :=
    CodeCreation.createNewChain rfl hst
  have hnot : ¬ SysInv gWorld { gSys0 with chains := upd gSys0.chains 0 (some st.chain) } := by
    rintro ⟨-, hch⟩
    have hok : st.app.protocolVersion ≤ gSys0.ctm.pv ∧
        (gSys0.ctm.relAt st.app.protocolVersion ≠ 0 →
          st.diamond.routing = rowsRouting (gWorld.relRows (gSys0.ctm.relAt st.app.protocolVersion))) :=
      hch 0 st.chain rfl
    rw [hpv, hrel] at hok
    have h9 := congrFun (hok.2 (by decide)) 9
    rw [hr9, hrow9] at h9
    exact absurd h9 (by simp)
  refine ⟨rfl, rfl, fun f b h => ?_, fun x hx f b h => ?_, rfl, hI0, _, hcc,
    ⟨st.chain, rfl, hpv, hr9, hrow9⟩, hnot,
    fun hs => hnot (step_sysInv hI0 hs (fun h => h))⟩
  · rw [fUpgrade_code (gAdmin_ne (g_entry_admin rfl h)).2.1]
    exact gCode_admin (g_entry_admin rfl h)
  · rw [fUpgrade_code (gMigrator_ne (g_entry_migrator rfl hx h)).2.1]
    exact gCode_migrator (g_entry_migrator rfl hx h)

theorem SelectorlessRowRevertsCreation : Properties.SelectorlessRowRevertsCreation := by
  have hG : GenuineRelease eEnv eWorld 100 :=
    { diamondInit := rfl
      genesisUpgrade := rfl
      adminFacet := fun f b h => by
        rw [eCode (gAdmin_ne (g_entry_admin rfl h)).2.2]
        exact gCode_admin (g_entry_admin rfl h)
      migratorFacet := fun x hx f b h => by
        rw [eCode (gMigrator_ne (g_entry_migrator rfl hx h)).2.2]
        exact gCode_migrator (g_entry_migrator rfl hx h)
      rows := rfl }
  refine ⟨rfl, hG, ⟨11, false, by decide, rfl⟩, ⟨12, true, by decide, rfl⟩, by decide,
    ⟨_, Step.genesis rfl (addAll_empty_eq (by decide))⟩, ?_⟩
  intro id admin ts
  have hcut : applyFacetCuts eEnv.hasCode ChainState.fresh.diamond
      (newChainInstallations eEnv (initState eWorld 100).cur) = none :=
    Option.isNone_iff_eq_none.mp (by decide)
  have hdi : diamondInitialize eEnv (initState eWorld 100) id admin ChainState.fresh = none := by
    unfold diamondInitialize
    simp [hcut]
  simp only [createNewChain, deployNewChain_eq rfl hG.diamondInit, hdi, Option.bind_none]

end Contracts.ChainTypeManager.GenesisWriters
