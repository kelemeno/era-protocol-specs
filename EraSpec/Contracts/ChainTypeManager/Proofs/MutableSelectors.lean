import EraSpec.Contracts.ChainTypeManager.Properties.MutableSelectors
import EraSpec.Contracts.ChainTypeManager.Proofs.LiveRouting

/-!
# Proofs: the routing headline needs stable `selectors()` answers

**With stable answers** (`stable_run`). A step that is not a crossing is `LiveRouting`'s step by
definition. A crossing differs from `LiveRouting`'s only in the cut, and `StableSelectors` makes
the stored cut the derived one. So a stable run is a `DRun` of the world whose facets answer `σ`,
and the headline is `LiveRouting`'s, read through that, with the answers at the end equal to `σ`.

**Without them.** A stored cut lands on the arriving release *as the facets answered when it was
derived* (`frozen_cuts_route`), while a new chain gets the release as they answer now
(`genesis_routes`). Two chains at one version with a release, routing differently, are out of
reach of every `ChainRouting` world, by `ChainsRunTheirVersionsRelease` itself
(`split_unreachable`). The countermodels compute the rest on concrete diamonds.
-/

namespace Contracts.ChainTypeManager

/-! ## The reduction to `LiveRouting` -/

lemma toDLabels_not_arbitrary :
    ∀ {ls : List MutLabel}, (∀ l ∈ ls, ¬ l.isArbitrary) →
      ∀ l ∈ MutLabel.toDLabels ls, ¬ l.isArbitrary
  | [], _ => by simp [MutLabel.toDLabels]
  | .sys l₀ :: ls, h => by
    intro l hl
    simp only [MutLabel.toDLabels, List.mem_cons] at hl
    rcases hl with rfl | hl
    · exact h (.sys l) List.mem_cons_self
    · exact toDLabels_not_arbitrary (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) l hl
  | .setSelectors _ _ :: ls, h => by
    intro l hl
    simp only [MutLabel.toDLabels] at hl
    exact toDLabels_not_arbitrary (fun l' hl' => h l' (List.mem_cons_of_mem _ hl')) l hl

/-- **One step under stable answers is a `LiveRouting` step.** -/
lemma stable_step {M : MutWorld} {σ : Address → List Selector} {s s' : MutSys} {l : DLabel}
    (hfz : ∀ t, M.FrozenUnder σ t) (hs : s.sel = σ) (h : MutStep M s (.sys l) s') :
    DStep (M.at σ) s.sys l s'.sys ∧ s'.sel = σ := by
  have hfz' : ∀ t, M.cuts t = deriveFacetCuts (M.at σ) (M.tr t).fromRel (M.tr t).newRel := hfz
  obtain ⟨sys, sel⟩ := s
  dsimp only at hs
  subst hs
  cases h with
  | live _ hd => exact ⟨hd, rfl⟩
  | transition hc hut hcc hcut hlt =>
    rw [hfz'] at hcut
    exact ⟨DStep.transition hc hut hcc hcut hlt, rfl⟩

/-- **A run under stable answers is a `LiveRouting` run.** -/
lemma stable_run {M : MutWorld} {σ : Address → List Selector} (hfz : ∀ t, M.FrozenUnder σ t) :
    ∀ {s s' : MutSys} {ls : List MutLabel}, s.sel = σ → (∀ l ∈ ls, ¬ l.isSelectorChange) →
      MutRun M s ls s' → DRun (M.at σ) s.sys (MutLabel.toDLabels ls) s'.sys ∧ s'.sel = σ := by
  intro s s' ls hs hc h
  induction h with
  | nil => exact ⟨DRun.nil, hs⟩
  | @cons s₁ s₂ s₃ l ls hstep _ ih =>
    cases l with
    | sys l₀ =>
      obtain ⟨hd, hs₂⟩ := stable_step hfz hs hstep
      obtain ⟨hr, hs₃⟩ := ih hs₂ (fun l hl => hc l (List.mem_cons_of_mem _ hl))
      exact ⟨DRun.cons hd hr, hs₃⟩
    | setSelectors f xs => exact absurd trivial (hc _ List.mem_cons_self)

/-! ## The same, asking only the transitions a run can cross -/

/-- A CTM writer leaves each `upgradeTransition` slot as it was, or holding the transition the
call records. -/
lemma cstep_ut {W : World} {s s' : CTM} {op : Op} (h : CStep W s op s') (v : ℕ) :
    s'.ut v = s.ut v ∨ (∃ t, op = .commit t ∧ s'.ut v = t) ∨
      ∃ e r, op = .replace e r ∧ s'.ut v = r := by
  cases h with
  | @commit t _ _ _ _ _ _ =>
    by_cases e : v = (W.tr t).old
    · exact Or.inr (Or.inl ⟨t, rfl, by subst e; exact upd_same _ _ _⟩)
    · exact Or.inl (upd_ne _ _ e)
  | @replace e₀ r _ _ _ _ _ _ _ _ =>
    by_cases e : v = (W.tr e₀).old
    · exact Or.inr (Or.inr ⟨e₀, r, rfl, by subst e; exact upd_same _ _ _⟩)
    · exact Or.inl (upd_ne _ _ e)
  | legacyCommit _ _ => exact Or.inl rfl
  | legacyRecut _ _ => exact Or.inl rfl

/-- **One step, with stable cuts in the slots only.** The step is a `LiveRouting` step, and the
slots afterwards hold transitions that were in a slot before or that the step records. -/
lemma stableOn_step {M : MutWorld} {σ : Address → List Selector} {s s' : MutSys} {l : DLabel}
    (hslots : ∀ v, s.sys.ctm.ut v ≠ 0 → M.FrozenUnder σ (s.sys.ctm.ut v))
    (hrec : ∀ t, (MutLabel.sys l).records = some t → M.FrozenUnder σ t)
    (hs : s.sel = σ) (h : MutStep M s (.sys l) s') :
    DStep (M.at σ) s.sys l s'.sys ∧ s'.sel = σ ∧
      ∀ v, s'.sys.ctm.ut v ≠ 0 → M.FrozenUnder σ (s'.sys.ctm.ut v) := by
  obtain ⟨sys, sel⟩ := s
  dsimp only at hs hslots
  subst hs
  cases h with
  | live _ hd =>
    refine ⟨hd, rfl, ?_⟩
    cases hd with
    | ctm hc _ =>
      intro v hv
      dsimp only at hv ⊢
      rcases cstep_ut hc v with e | ⟨t, rfl, e⟩ | ⟨e₀, r, rfl, e⟩
      · rw [e] at hv ⊢; exact hslots v hv
      · rw [e]; exact hrec t rfl
      · rw [e]; exact hrec r rfl
    | genesis _ _ => exact hslots
    | migrateIn _ _ _ _ => exact hslots
    | transition _ _ _ _ _ => exact hslots
    | bootstrapReset _ _ _ _ _ => exact hslots
    | arbitraryCut _ _ _ => exact hslots
  | @transition _ c _ hc hut hcc hcut hlt =>
    have hfz : M.cuts (sys.ctm.ut c.pv) = deriveFacetCuts (M.at sel)
        (M.tr (sys.ctm.ut c.pv)).fromRel (M.tr (sys.ctm.ut c.pv)).newRel := hslots _ hut
    rw [hfz] at hcut
    exact ⟨DStep.transition hc hut hcc hcut hlt, rfl, hslots⟩

/-- **A run, with stable cuts only for the transitions it can cross, is a `LiveRouting` run.** -/
lemma stableOn_run {M : MutWorld} {σ : Address → List Selector} :
    ∀ {s s' : MutSys} {ls : List MutLabel}, s.sel = σ → (∀ l ∈ ls, ¬ l.isSelectorChange) →
      (∀ v, s.sys.ctm.ut v ≠ 0 → M.FrozenUnder σ (s.sys.ctm.ut v)) →
      (∀ l ∈ ls, ∀ t, l.records = some t → M.FrozenUnder σ t) →
      MutRun M s ls s' → DRun (M.at σ) s.sys (MutLabel.toDLabels ls) s'.sys ∧ s'.sel = σ := by
  intro s s' ls hs hc hslots hrec h
  induction h with
  | nil => exact ⟨DRun.nil, hs⟩
  | @cons s₁ s₂ s₃ l ls hstep _ ih =>
    cases l with
    | sys l₀ =>
      obtain ⟨hd, hs₂, hslots₂⟩ :=
        stableOn_step hslots (fun t ht => hrec _ List.mem_cons_self t ht) hs hstep
      obtain ⟨hr, hs₃⟩ := ih hs₂ (fun l hl => hc l (List.mem_cons_of_mem _ hl)) hslots₂
        (fun l hl => hrec l (List.mem_cons_of_mem _ hl))
      exact ⟨DRun.cons hd hr, hs₃⟩
    | setSelectors f xs => exact absurd trivial (hc _ List.mem_cons_self)

/-! ## The CTM part, along any run -/

/-- A CTM writer's checks read versions and transition getters, not the facets' answers. -/
lemma cstep_at {M : MutWorld} {σ τ : Address → List Selector} {s s' : CTM} {op : Op}
    (h : CStep (M.at τ).toWorld s op s') : CStep (M.at σ).toWorld s op s' := by
  cases h with
  | commit h1 h2 h3 h4 h5 h6 => exact CStep.commit h1 h2 h3 h4 h5 h6
  | replace h1 h2 h3 h4 h5 h6 h7 h8 => exact CStep.replace h1 h2 h3 h4 h5 h6 h7 h8
  | legacyCommit h1 h2 => exact CStep.legacyCommit h1 h2
  | legacyRecut h1 h2 => exact CStep.legacyRecut h1 h2

/-- Along any run, answer changes and break-glass cuts included, the CTM keeps `CtmInv`: only CTM
writers touch it. -/
lemma mutRun_ctmInv {M : MutWorld} {σ : Address → List Selector} {s s' : MutSys}
    {ls : List MutLabel} (hC : CtmInv (M.at σ).toWorld s.sys.ctm) (h : MutRun M s ls s') :
    CtmInv (M.at σ).toWorld s'.sys.ctm := by
  induction h with
  | nil => exact hC
  | cons hs _ ih =>
    apply ih
    cases hs with
    | live _ hd =>
      cases hd with
      | ctm hc _ => exact step_inv hC (cstep_at hc)
      | genesis _ _ => exact hC
      | migrateIn _ _ _ _ => exact hC
      | transition _ _ _ _ _ => exact hC
      | bootstrapReset _ _ _ _ _ => exact hC
      | arbitraryCut _ _ _ => exact hC
    | transition _ _ _ _ _ => exact hC
    | setSelectors => exact hC

/-! ## What the cuts install -/

/-- A diamond created from release `R` while the facets give `D`'s answers routes `R`'s rows with
those answers. -/
lemma genesis_routes {D : DWorld} {R : Address} {ds : DiamondStorage}
    (h : diamondCut DiamondStorage.fresh (newChainInstallations D R) = some ds) :
    ds.routing = rowsRouting (D.rows R) := by
  have := installCuts_routing D.selectors (D.genesisFacets R) _ ds h
  rw [fresh_routing] at this
  exact addAll_empty this

/-- **Stored cuts land on the arriving release as the facets answered when the cuts were derived.**
From a diamond routing the departing release with the answers `σ` the transition was built under,
the stored cuts leave a diamond routing the arriving release with the same answers `σ`, whatever
the facets answer when the chain crosses. -/
lemma frozen_cuts_route {M : MutWorld} {σ : Address → List Selector} {t : Address}
    {ds d : DiamondStorage} (hfz : M.FrozenUnder σ t)
    (hguard : ds.routing = rowsRouting ((M.at σ).rows (M.tr t).fromRel))
    (h : diamondCut ds (M.cuts t) = some d) :
    d.routing = rowsRouting ((M.at σ).rows (M.tr t).newRel) := by
  have hfz' : M.cuts t = deriveFacetCuts (M.at σ) (M.tr t).fromRel (M.tr t).newRel := hfz
  rw [hfz'] at h
  have := transitionCuts_routing hguard h
  rw [hguard] at this
  exact applyDerived_rows this

/-! ## Split states are out of reach of the base models -/

/-- **Two chains at one version with a release, routing differently, are out of reach** of every
`ChainRouting` world along a run without break-glass cut from an invariant state: the headline
would give both the same routing. -/
lemma split_unreachable {s : DSys} {v : ℕ} {d₀ d₁ : DiamondStorage}
    (h₀ : s.chains 0 = some ⟨v, d₀⟩) (h₁ : s.chains 1 = some ⟨v, d₁⟩) (hrel : s.ctm.relAt v ≠ 0)
    (hne : d₀.routing ≠ d₁.routing) :
    ¬ ∃ (W : World) (s₀ : Sys) (ls : List Label), SysInv W s₀ ∧ Run W s₀ ls s.view ∧
      ∀ l ∈ ls, ¬ l.isArbitrary := by
  rintro ⟨W, s₀, ls, hI, hr, hl⟩
  have e₀ := (ChainsRunTheirVersionsRelease W s₀ s.view ls hI hr hl 0 ⟨v, d₀.routing⟩
    (by simp [DSys.view, h₀, DChain.view]) hrel).2
  have e₁ := (ChainsRunTheirVersionsRelease W s₀ s.view ls hI hr hl 1 ⟨v, d₁.routing⟩
    (by simp [DSys.view, h₁, DChain.view]) hrel).2
  exact hne (e₀.trans e₁.symm)

/-- The same for `LiveRouting`'s count-checked system, through its refinement of `ChainRouting`. -/
lemma split_unreachable_counted {s : DSys} {v : ℕ} {d₀ d₁ : DiamondStorage}
    (h₀ : s.chains 0 = some ⟨v, d₀⟩) (h₁ : s.chains 1 = some ⟨v, d₁⟩) (hrel : s.ctm.relAt v ≠ 0)
    (hne : d₀.routing ≠ d₁.routing) :
    ¬ ∃ (D : DWorld) (s₀ : DSys) (ls : List DLabel), DSysInv D s₀ ∧ DRun D s₀ ls s ∧
      ∀ l ∈ ls, ¬ l.isArbitrary := by
  rintro ⟨D, s₀, ls, hI, hr, hl⟩
  apply split_unreachable h₀ h₁ hrel hne
  refine ⟨D.toWorld, s₀.view, ls.map DLabel.view, hI.1, (countedRun_view hI hr hl).1, ?_⟩
  intro l hm
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hm
  rw [DLabel.view_isArbitrary]
  exact hl l₀ hl₀

/-! ## The properties with stable answers -/

theorem StableRunIsACountedRun : Properties.StableRunIsACountedRun :=
  fun _ _ _ _ _ hS h => stable_run hS.frozen hS.start hS.constant h

theorem CountedRunIsAStableRun : Properties.CountedRunIsAStableRun := by
  intro D s s' ls h
  refine ⟨?_, ⟨rfl, ?_, fun _ => rfl⟩, rfl⟩
  · induction h with
    | nil => exact MutRun.nil
    | cons hs _ ih =>
      refine MutRun.cons ?_ ih
      cases hs with
      | ctm hc hv => exact MutStep.live rfl (DStep.ctm hc hv)
      | genesis h1 h2 => exact MutStep.live rfl (DStep.genesis h1 h2)
      | migrateIn v hv h1 h2 => exact MutStep.live rfl (DStep.migrateIn v hv h1 h2)
      | transition hc hut hcc hcut hlt => exact MutStep.transition hc hut hcc hcut hlt
      | bootstrapReset hc hleg h1 h2 hlt =>
        exact MutStep.live rfl (DStep.bootstrapReset hc hleg h1 h2 hlt)
      | arbitraryCut v ds hc => exact MutStep.live rfl (DStep.arbitraryCut v ds hc)
  · intro l hl
    obtain ⟨l₀, _, rfl⟩ := List.mem_map.mp hl
    simp [MutLabel.isSelectorChange]

theorem ChainsRunTheirVersionsReleaseStable : Properties.ChainsRunTheirVersionsReleaseStable := by
  intro M σ s s' ls hS hI h hl id c hc hrel
  obtain ⟨hd, hsel⟩ := stable_run hS.frozen hS.start hS.constant h
  obtain ⟨h1, h2, h3, h4⟩ := chainsRun_counted hI hd (toDLabels_not_arbitrary hl) id c hc hrel
  refine ⟨h1, h2, ?_, h4⟩
  rw [hsel]
  exact h3

theorem FreshChainsRunTheirVersionsReleaseStable :
    Properties.FreshChainsRunTheirVersionsReleaseStable := by
  intro M σ R s' ls hR hv hS h hl id c hc
  obtain ⟨hd, hsel⟩ := stable_run hS.frozen hS.start hS.constant h
  obtain ⟨h1, h2, h3, h4⟩ := FreshChainsRunTheirVersionsReleaseCounted (M.at σ) R s'.sys _ hR hv
    hd (toDLabels_not_arbitrary hl) id c hc
  refine ⟨h1, h2, h3, ?_⟩
  rw [hsel]
  exact h4

theorem StableSelectorsIsStableOn : Properties.StableSelectorsIsStableOn :=
  fun _ _ _ _ hS => ⟨hS.start, hS.constant, fun _ _ => hS.frozen _, fun _ _ t _ => hS.frozen t⟩

theorem StableOnRunIsACountedRun : Properties.StableOnRunIsACountedRun :=
  fun _ _ _ _ _ hS h => stableOn_run hS.start hS.constant hS.slots hS.recorded h

theorem ChainsRunTheirVersionsReleaseStableOn :
    Properties.ChainsRunTheirVersionsReleaseStableOn := by
  intro M σ s s' ls hS hI h hl id c hc hrel
  obtain ⟨hd, hsel⟩ := stableOn_run hS.start hS.constant hS.slots hS.recorded h
  obtain ⟨h1, h2, h3, h4⟩ := chainsRun_counted hI hd (toDLabels_not_arbitrary hl) id c hc hrel
  refine ⟨h1, h2, ?_, h4⟩
  rw [hsel]
  exact h3

theorem StableRunIsARoutingRun : Properties.StableRunIsARoutingRun := by
  intro M σ s s' ls hS hI h hl
  obtain ⟨hd, _⟩ := stable_run hS.frozen hS.start hS.constant h
  have hl' := toDLabels_not_arbitrary hl
  refine ⟨hI.1, (countedRun_view hI hd hl').1, ?_, fun _ => rfl⟩
  intro l hm
  obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.mp hm
  rw [DLabel.view_isArbitrary]
  exact hl' l₀ hl₀

theorem CrossingNeedsTheAnswersNow : Properties.CrossingNeedsTheAnswersNow := by
  rintro M s id c hC hc hfail ⟨s', h⟩
  cases h with
  | live hnc _ => exact absurd hnc (by simp [DLabel.isCrossing])
  | transition hc' hut hcc _ _ =>
    obtain rfl := Option.some.inj (hc.symm.trans hc')
    have hfrom : (s.sys.edge (M.at s.sel) c.pv).fromRel = s.sys.ctm.relAt c.pv :=
      (hC.slots _ hut).2.1
    rw [hfrom] at hcc
    exact hfail hcc

/-! ## The witness world

`Address × Bool` is a `Fintype`, so `decide` would settle `∀ fb ∈ rows, …` by enumerating every
pair; the list instance is preferred here, as in `LiveRouting`. -/

attribute [local instance 2000] List.decidableBAll

/-- A release with no facet rows passes `validate()`'s facet checks vacuously. -/
lemma releaseValid_of_nil {D : DWorld} {R : Address} (h : D.genesisFacets R = []) :
    ReleaseValid D R :=
  ⟨by simp [h], by simp [h], by simp [h]⟩

/-- Every release of the witness world passes `validate()`, before and after facet `21`'s change. -/
lemma mut_valid (R : Address) :
    ReleaseValid (mutWorld.at mutSelA) R ∧ ReleaseValid (mutWorld.at mutSelB) R := by
  by_cases h1 : R = 100
  · subst h1; exact ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩
  by_cases h2 : R = 200
  · subst h2; exact ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩
  by_cases h3 : R = 250
  · subst h3; exact ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide⟩⟩
  have h0 : wGenesisFacets R = [] := by simp [wGenesisFacets, h1, h2, h3]
  exact ⟨releaseValid_of_nil h0, releaseValid_of_nil h0⟩

lemma mut_frozen (t : Address) : mutWorld.FrozenUnder mutSelA t := rfl

lemma mut_genuine300 : mutWorld.GenuineUnder mutSelA 300 :=
  ⟨by decide, ⟨by decide, by decide⟩, (mut_valid _).1, (mut_valid _).1, mut_frozen 300⟩

lemma mut_late_genuine300 : mutLateWorld.GenuineUnder mutSelA 300 :=
  ⟨by decide, ⟨by decide, by decide⟩, (mut_valid _).1, (mut_valid _).1,
    by unfold MutWorld.FrozenUnder; decide⟩

lemma mut_late_genuine600 : mutLateWorld.GenuineUnder mutSelB 600 :=
  ⟨by decide, ⟨by decide, by decide⟩, (mut_valid _).2, (mut_valid _).2,
    by unfold MutWorld.FrozenUnder; decide⟩

/-- `300` was not built under the answers after the change: its stored `Add` carries `[1, 2]`, the
one derived then carries `[1, 3]`. -/
lemma mut_not_frozenB300 : ¬ mutWorld.FrozenUnder mutSelB 300 := by
  unfold MutWorld.FrozenUnder; decide

lemma mut_store100 :
    diamondCut DiamondStorage.fresh (newChainInstallations (mutWorld.at mutSelA) 100) =
      some wStore100 := rfl

lemma mut_store100B :
    diamondCut DiamondStorage.fresh (newChainInstallations (mutWorld.at mutSelB) 100) =
      some wStore100 := rfl

lemma mut_crossed_cut : diamondCut wStore100 (mutWorld.cuts 300) = some mutCrossedStore := rfl

lemma mut_fresh_cut :
    diamondCut DiamondStorage.fresh (newChainInstallations (mutWorld.at mutSelB) 200) =
      some mutFreshStore := rfl

/-- Chain `0`, after crossing with `300`'s stored cuts, routes release `200` with the old
answers. -/
lemma mut_crossed_routes :
    mutCrossedStore.routing = rowsRouting (flattenRows mutSelA (mutWorld.genesisFacets 200)) :=
  frozen_cuts_route (mut_frozen 300) (genesis_routes mut_store100) mut_crossed_cut

/-- A chain created after the change routes release `200` with the new answers. -/
lemma mut_fresh_routes :
    mutFreshStore.routing = rowsRouting (flattenRows mutSelB (mutWorld.genesisFacets 200)) :=
  genesis_routes mut_fresh_cut

/-- The two route selector `2` differently. -/
lemma mut_split : mutCrossedStore.routing ≠ mutFreshStore.routing := by
  intro h
  have h2 := congrFun h 2
  rw [mut_crossed_routes, mut_fresh_routes] at h2
  exact absurd h2 (by decide)

/-! ## The witness -/

theorem StableSelectorsWitness : Properties.StableSelectorsWitness := by
  obtain ⟨_, hI0, s, hrun, ⟨c₀, hc₀, hpv₀, hr₀, _⟩, ⟨c₁, hc₁, hpv₁, hr₁⟩, hne⟩ :=
    CountedRoutingWitness
  obtain ⟨hmut, hstable, _⟩ := CountedRunIsAStableRun _ _ _ _ hrun
  exact ⟨hstable, hI0, ⟨s, wSelectors⟩, hmut, c₀, c₁, hc₀, hc₁, hpv₀, hpv₁, hr₀, hr₁, hne⟩

lemma mut_stable_cut :
    diamondCut DiamondStorage.fresh (newChainInstallations (mutWorld.at mutSelA) 200) =
      some mutStableStore := rfl

/-- `600` in `mutLateWorld` was not built under the starting answers: its stored `Remove` carries
`[1, 3]`, the one derived under them carries `[1, 2]`. -/
lemma mut_late_not_frozenA600 : ¬ mutLateWorld.FrozenUnder mutSelA 600 := by
  unfold MutWorld.FrozenUnder; decide

theorem StableSelectorsOnWitness : Properties.StableSelectorsOnWitness := by
  have hrun := MutRun.cons (M := mutLateWorld)
    (MutStep.live rfl (DStep.genesis (s := mutSys0.sys) (id := 0) rfl mut_store100))
    (MutRun.cons (MutStep.live rfl (DStep.ctm (CStep.commit (t := 300) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
        (by intro R hR; cases hR; exact (mut_valid _).1)))
      (MutRun.cons (MutStep.transition (id := 0) rfl (by decide) (by decide) mut_crossed_cut
          (by decide))
        (MutRun.cons (MutStep.live rfl (DStep.genesis (id := 1) rfl mut_stable_cut)) MutRun.nil)))
  have hOn : StableSelectorsOn mutLateWorld mutSelA mutSys0
      [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)] := by
    refine ⟨rfl, ?_, fun v hv => absurd rfl hv, ?_⟩
    · intro l hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl <;> exact id
    · intro l hl t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl <;> simp only [MutLabel.records, reduceCtorEq] at ht
      cases ht
      exact mut_late_genuine300.frozen
  have hI : DSysInv (mutLateWorld.at mutSelA) mutSys0.sys :=
    freshCounted_inv _ 100 (by decide) (mut_valid 100).1
  have hrows : flattenRows mutSelA (mutLateWorld.genesisFacets 200) = wRows 200 := by decide
  have hr₀ := (ChainsRunTheirVersionsReleaseStableOn _ _ _ _ _ hOn hI hrun
    (by intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl <;> exact id)
    0 ⟨2, mutCrossedStore⟩ rfl (by decide)).2.1
  have hr₁ := (ChainsRunTheirVersionsReleaseStableOn _ _ _ _ _ hOn hI hrun
    (by intro l hl
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl | rfl <;> exact id)
    1 ⟨2, mutStableStore⟩ rfl (by decide)).2.1
  rw [show (_ : DSys).ctm.relAt 2 = 200 from by decide, hrows] at hr₀ hr₁
  exact ⟨hOn, mut_late_not_frozenA600,
    fun σ hS => mut_late_not_frozenA600 (by have := hS.start; subst this; exact hS.frozen 600),
    hI, _, hrun, _, _, rfl, rfl, rfl, rfl, hr₀, hr₁, CountedRoutingWitness.2.2.choose_spec.2.2.2⟩

/-! ## The countermodels -/

theorem MutableSelectorsSplitRouting : Properties.MutableSelectorsSplitRouting := by
  have hrun := MutRun.cons (M := mutWorld)
    (MutStep.live rfl (DStep.genesis (s := mutSys0.sys) (id := 0) rfl mut_store100))
    (MutRun.cons (MutStep.live rfl (DStep.ctm (CStep.commit (t := 300) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
        (by intro R hR; cases hR; exact (mut_valid _).1)))
      (MutRun.cons (MutStep.setSelectors (f := 21) (xs := [1, 3]))
        (MutRun.cons (MutStep.transition (id := 0) rfl (by decide) (by decide) mut_crossed_cut
            (by decide))
          (MutRun.cons (MutStep.live rfl (DStep.genesis (id := 1) rfl mut_fresh_cut)) MutRun.nil))))
  refine ⟨mut_frozen, mut_genuine300, by decide, mut_valid, fun f hf => upd_ne _ _ hf, by decide,
    by decide, freshCounted_inv _ 100 (by decide) (mut_valid 100).1, rfl, _, hrun, rfl, by decide,
    ⟨_, _, rfl, rfl, rfl, rfl, mut_crossed_routes, mut_fresh_routes, mut_split⟩,
    split_unreachable (v := 2) (d₀ := mutCrossedStore) (d₁ := mutFreshStore) rfl rfl (by decide)
      mut_split,
    split_unreachable_counted (v := 2) (d₀ := mutCrossedStore) (d₁ := mutFreshStore) rfl rfl
      (by decide) mut_split⟩

theorem MutableSelectorsBlockNextEdge : Properties.MutableSelectorsBlockNextEdge := by
  have hrun := MutRun.cons (M := mutLateWorld)
    (MutStep.live rfl (DStep.genesis (s := mutSys0.sys) (id := 0) rfl mut_store100))
    (MutRun.cons (MutStep.live rfl (DStep.ctm (CStep.commit (t := 300) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
        (by intro R hR; cases hR; exact (mut_valid _).1)))
      (MutRun.cons (MutStep.setSelectors (f := 21) (xs := [1, 3]))
        (MutRun.cons (MutStep.transition (id := 0) rfl (by decide) (by decide) mut_crossed_cut
            (by decide))
          (MutRun.cons (MutStep.live rfl (DStep.genesis (id := 1) rfl mut_fresh_cut))
            (MutRun.cons (MutStep.live rfl (DStep.ctm (CStep.commit (t := 600) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide))
                (by intro R hR; cases hR; exact (mut_valid _).2)))
              MutRun.nil)))))
  have hC := mutRun_ctmInv (σ := mutSelB)
    (InitSatisfiesInvariant (mutLateWorld.at mutSelB).toWorld 100 (by decide)) hrun
  refine ⟨mut_late_genuine600, mut_late_genuine300, _, hrun, by decide, by decide,
    ⟨_, rfl, rfl, by decide, CrossingNeedsTheAnswersNow _ _ _ _ hC rfl (by decide)⟩,
    ⟨_, rfl, rfl, by decide, _,
      MutStep.transition (id := 1) rfl (by decide) (by decide) rfl (by decide), _, rfl, rfl⟩⟩

theorem StaleCutsSplitRouting : Properties.StaleCutsSplitRouting := by
  have hrun := MutRun.cons (M := mutWorld)
    (MutStep.live rfl (DStep.genesis (s := mutStaleSys0.sys) (id := 0) rfl mut_store100B))
    (MutRun.cons (MutStep.live rfl (DStep.ctm (CStep.commit (t := 300) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))
        (by intro R hR; cases hR; exact (mut_valid _).2)))
      (MutRun.cons (MutStep.transition (id := 0) rfl (by decide) (by decide) mut_crossed_cut
          (by decide))
        (MutRun.cons (MutStep.live rfl (DStep.genesis (id := 1) rfl mut_fresh_cut)) MutRun.nil)))
  refine ⟨mut_frozen, mut_not_frozenB300, freshCounted_inv _ 100 (by decide) (mut_valid 100).2,
    rfl, _, hrun, rfl, by decide, ⟨_, _, rfl, rfl, rfl, rfl, mut_split⟩,
    split_unreachable (v := 2) (d₀ := mutCrossedStore) (d₁ := mutFreshStore) rfl rfl (by decide)
      mut_split⟩

end Contracts.ChainTypeManager
