import EraSpec.Contracts.ChainTypeManager.Properties.ChainRouting
import EraSpec.Contracts.ChainTypeManager.Proofs.VersionRegistry

/-!
# Proofs: every chain on a CTM runs its version's release

The diamond-cut lemmas say what a successful `removeAll` / `addAll` leaves (`removeAll_spec`,
`addAll_spec`) — no uniqueness premise is needed, because a cut that would touch a
selector twice reverts. From them, a guarded transition maps `R_from`'s routing to
`R_new`'s (`applyDerived_rows`), and genesis installs a release's routing exactly
(`addAll_empty`). The headline is then an induction over steps, reading the release
bookkeeping off `CtmInv`.
-/

namespace Contracts.ChainTypeManager

/-! ## Release routing -/

lemma rowsRouting_eq_none {A : ReleaseRows} {y : Selector} :
    rowsRouting A y = none ↔ y ∉ A.map Prod.fst := by
  induction A with
  | nil => simp [rowsRouting]
  | cons hd rs ih =>
    obtain ⟨x, r⟩ := hd
    by_cases hyx : y = x
    · subst hyx; simp [rowsRouting]
    · simp [rowsRouting, hyx, ih]

/-! ## What a successful cut leaves -/

lemma removeAll_spec {ρ σ : Routing} {ks : List Selector} (h : removeAll ρ ks = some σ) :
    ∀ y, σ y = if y ∈ ks then none else ρ y := by
  induction ks generalizing ρ with
  | nil => simp [removeAll] at h; subst h; intro y; simp
  | cons x xs ih =>
    intro y
    simp only [removeAll, removeSel] at h
    split_ifs at h with hx
    · simp at h
    · simp only [Option.bind_some] at h
      rw [ih h y]
      by_cases hyx : y = x
      · subst hyx; simp
      · simp [hyx, upd_ne _ _ hyx]

lemma addAll_fresh {ρ σ : Routing} {B : ReleaseRows} (h : addAll ρ B = some σ) :
    ∀ y ∈ B.map Prod.fst, ρ y = none := by
  induction B generalizing ρ with
  | nil => simp
  | cons hd rs ih =>
    obtain ⟨x, r⟩ := hd
    simp only [addAll, addSel] at h
    split_ifs at h with hx
    · simp only [Option.bind_some] at h
      intro y hy
      simp only [List.map_cons, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact hx
      · have := ih h y hy
        by_cases hyx : y = x
        · subst hyx; exact hx
        · rwa [upd_ne _ _ hyx] at this
    · simp at h

lemma addAll_spec {ρ σ : Routing} {B : ReleaseRows} (h : addAll ρ B = some σ) :
    ∀ y, σ y = if y ∈ B.map Prod.fst then rowsRouting B y else ρ y := by
  induction B generalizing ρ with
  | nil => simp [addAll] at h; subst h; intro y; simp
  | cons hd rs ih =>
    obtain ⟨x, r⟩ := hd
    have hfr := addAll_fresh h
    simp only [addAll, addSel] at h
    split_ifs at h with hx
    · simp only [Option.bind_some] at h
      -- `x` is not added again later: it is routed after its own `Add`
      have hxrs : x ∉ rs.map Prod.fst := by
        intro hm
        have := addAll_fresh h x hm
        simp at this
      intro y
      rw [ih h y]
      by_cases hyx : y = x
      · subst hyx
        simp [hxrs, rowsRouting]
      · simp [hyx, upd_ne _ _ hyx, rowsRouting]
    · simp at h

lemma addAll_empty {σ : Routing} {B : ReleaseRows} (h : addAll emptyRouting B = some σ) :
    σ = rowsRouting B := by
  funext y
  rw [addAll_spec h y]
  split_ifs with hy
  · rfl
  · exact (rowsRouting_eq_none.mpr hy).symm

lemma applyDerived_spec {ρ σ : Routing} {A B : ReleaseRows} (h : applyDerived ρ A B = some σ)
    (hne : A ≠ B) : ∀ y, σ y =
      if y ∈ B.map Prod.fst then rowsRouting B y else if y ∈ A.map Prod.fst then none else ρ y := by
  simp only [applyDerived, hne, ite_false] at h
  cases hr : removeAll ρ (A.map Prod.fst) with
  | none => rw [hr] at h; simp at h
  | some τ =>
    rw [hr, Option.bind_some] at h
    intro y
    rw [addAll_spec h y, removeAll_spec hr y]

/-- **A guarded transition lands on the target release.** -/
lemma applyDerived_rows {σ : Routing} {A B : ReleaseRows}
    (h : applyDerived (rowsRouting A) A B = some σ) : σ = rowsRouting B := by
  by_cases hAB : A = B
  · subst hAB; simp [applyDerived] at h; exact h.symm
  · funext y
    rw [applyDerived_spec h hAB y]
    split_ifs with hb ha
    · rfl
    · exact (rowsRouting_eq_none.mpr hb).symm
    · rw [rowsRouting_eq_none.mpr ha, rowsRouting_eq_none.mpr hb]

/-! ## When a cut succeeds (for the witnesses) -/

lemma addAll_ok {ρ : Routing} {B : ReleaseRows} (hnd : (B.map Prod.fst).Nodup)
    (hfresh : ∀ y ∈ B.map Prod.fst, ρ y = none) : ∃ σ, addAll ρ B = some σ := by
  induction B generalizing ρ with
  | nil => exact ⟨ρ, rfl⟩
  | cons hd rs ih =>
    obtain ⟨x, r⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hx : ρ x = none := hfresh x (by simp)
    simp only [addAll, addSel, hx, ite_true, Option.bind_some]
    apply ih hnd.2
    intro y hy
    have hyx : y ≠ x := fun h => hnd.1 (h ▸ hy)
    rw [upd_ne _ _ hyx]
    exact hfresh y (by simp [hy])

lemma removeAll_ok {ρ : Routing} {ks : List Selector} (hnd : ks.Nodup)
    (hp : ∀ y ∈ ks, ρ y ≠ none) : ∃ σ, removeAll ρ ks = some σ := by
  induction ks generalizing ρ with
  | nil => exact ⟨ρ, rfl⟩
  | cons x xs ih =>
    simp only [List.nodup_cons] at hnd
    have hx : ρ x ≠ none := hp x (by simp)
    simp only [removeAll, removeSel, hx, ite_false, Option.bind_some]
    apply ih hnd.2
    intro y hy
    have hyx : y ≠ x := fun h => hnd.1 (h ▸ hy)
    rw [upd_ne _ _ hyx]
    exact hp y (by simp [hy])

lemma addAll_empty_eq {B : ReleaseRows} (hnd : (B.map Prod.fst).Nodup) :
    addAll emptyRouting B = some (rowsRouting B) := by
  obtain ⟨σ, h⟩ := addAll_ok (ρ := emptyRouting) hnd (fun _ _ => rfl)
  rw [h, addAll_empty h]

lemma applyDerived_rows_eq {A B : ReleaseRows} (hA : (A.map Prod.fst).Nodup)
    (hB : (B.map Prod.fst).Nodup) :
    applyDerived (rowsRouting A) A B = some (rowsRouting B) := by
  by_cases hAB : A = B
  · subst hAB; simp [applyDerived]
  · obtain ⟨τ, hτ⟩ := removeAll_ok hA (fun y hy => by
      rw [Ne, rowsRouting_eq_none]; exact not_not.mpr hy)
    have hτe : ∀ y, τ y = none := by
      intro y
      rw [removeAll_spec hτ y]
      split_ifs with hy
      · rfl
      · exact rowsRouting_eq_none.mpr hy
    obtain ⟨σ, hσ⟩ := addAll_ok (ρ := τ) hB (fun y _ => hτe y)
    have : applyDerived (rowsRouting A) A B = some σ := by
      simp only [applyDerived, hAB, ite_false, hτ, Option.bind_some, hσ]
    rw [this, applyDerived_rows this]

/-! ## The CTM part of the system -/

lemma step_ctmInv {W : World} {s s' : Sys} {l : Label} (hI : CtmInv W s.ctm)
    (h : Step W s l s') : CtmInv W s'.ctm := by
  cases h with
  | ctm hc => exact step_inv hI hc
  | genesis _ _ => exact hI
  | migrateIn _ _ _ _ => exact hI
  | transition _ _ _ _ _ => exact hI
  | bootstrapReset _ _ _ _ => exact hI
  | arbitraryCut _ _ _ => exact hI

lemma run_ctmInv {W : World} {s s' : Sys} {ls : List Label} (hI : CtmInv W s.ctm)
    (h : Run W s ls s') : CtmInv W s'.ctm := by
  induction h with
  | nil => exact hI
  | cons hs _ ih => exact ih (step_ctmInv hI hs)

/-- Reading the transition committed at a chain's version off the invariant. -/
lemma edge_facts {W : World} {s : CTM} (hI : CtmInv W s) {v : ℕ} (hv : s.ut v ≠ 0) :
    (W.tr (s.ut v)).fromRel = s.relAt v ∧ s.relAt v ≠ 0 ∧ v < (W.tr (s.ut v)).new ∧
    (W.tr (s.ut v)).new ≤ s.pv ∧ (W.tr (s.ut v)).newRel = s.relAt (W.tr (s.ut v)).new ∧
    s.relAt (W.tr (s.ut v)).new ≠ 0 ∧
    W.relVersion (s.relAt (W.tr (s.ut v)).new) = (W.tr (s.ut v)).new := by
  obtain ⟨_, h2, h3, h4, h5, h6⟩ := hI.slots v hv
  exact ⟨h2, h3, h4, (hI.relAtSound _ h6).1, h5, h6, (hI.relAtSound _ h6).2⟩

/-- Updating one chain: the others are untouched. -/
lemma upd_chain {chains : ChainId → Option Chain} {id id' : ChainId} {c' c : Chain}
    (h : upd chains id (some c') id' = some c) : (id' = id ∧ c = c') ∨ (id' ≠ id ∧ chains id' = some c) := by
  by_cases hid : id' = id
  · subst hid; simp at h; exact Or.inl ⟨rfl, h.symm⟩
  · rw [upd_ne _ _ hid] at h; exact Or.inr ⟨hid, h⟩

/-! ## The induction -/

theorem step_sysInv {W : World} {s s' : Sys} {l : Label} (hI : SysInv W s)
    (h : Step W s l s') (hl : ¬ l.isArbitrary) : SysInv W s' := by
  obtain ⟨hC, hch⟩ := hI
  cases h with
  | @ctm op c' hc =>
    refine ⟨step_inv hC hc, ?_⟩
    intro id c hcid
    obtain ⟨hle, hrel⟩ := hch id c hcid
    have hpv := (cstep_pv hc).1
    have hlow := cstep_relAt_low hc c.pv hle
    refine ⟨le_trans hle hpv, ?_⟩
    dsimp only at hlow ⊢
    rw [hlow]; exact hrel
  | @genesis id ρ hnone hadd =>
    refine ⟨hC, ?_⟩
    intro id' c hc
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · refine ⟨le_rfl, fun _ => ?_⟩
      dsimp only
      rw [hC.curAtVersion]; exact addAll_empty hadd
    · exact hch id' c hold
  | @migrateIn id ρ v hv hnone hadd =>
    refine ⟨hC, ?_⟩
    intro id' c hc
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · subst hv
      refine ⟨le_rfl, fun _ => ?_⟩
      dsimp only
      rw [hC.curAtVersion]; exact addAll_empty hadd
    · exact hch id' c hold
  | @transition id c0 ρ hc0 hut hguard happ hlt =>
    refine ⟨hC, ?_⟩
    intro id' c hc
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · obtain ⟨_, _, _, hle, hnr, hnz, _⟩ := edge_facts hC hut
      refine ⟨hle, fun _ => ?_⟩
      dsimp only
      rw [hguard] at happ
      rw [applyDerived_rows happ, hnr]
    · exact hch id' c hold
  | @bootstrapReset id c0 R ρ hc0 hleg hadd hlt =>
    refine ⟨hC, ?_⟩
    intro id' c hc
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · obtain ⟨_, hrel, hR⟩ := hC.bootstraps _ R hleg
      have hle := (hC.relAtSound _ (by rw [hrel]; exact hR)).1
      refine ⟨hle, fun _ => ?_⟩
      dsimp only
      rw [hrel]; exact addAll_empty hadd
    · exact hch id' c hold
  | arbitraryCut _ _ _ => exact absurd trivial hl

lemma run_sysInv {W : World} {s s' : Sys} {ls : List Label} (hI : SysInv W s)
    (h : Run W s ls s') (hl : ∀ l ∈ ls, ¬ l.isArbitrary) : SysInv W s' := by
  induction h with
  | nil => exact hI
  | cons hs _ ih =>
    exact ih (step_sysInv hI hs (hl _ (List.mem_cons_self)))
      (fun l hm => hl l (List.mem_cons_of_mem _ hm))

/-- On a chain-by-chain basis: every chain is at a version with a release. -/
def AllRegistry (s : Sys) : Prop := ∀ id c, s.chains id = some c → s.ctm.relAt c.pv ≠ 0

lemma step_allRegistry {W : World} {s s' : Sys} {l : Label} (hI : SysInv W s)
    (hA : AllRegistry s) (h : Step W s l s') (hl : ¬ l.isArbitrary) : AllRegistry s' := by
  obtain ⟨hC, hch⟩ := hI
  cases h with
  | @ctm op c' hc =>
    intro id c hcid
    have hlow := cstep_relAt_low hc c.pv (hch id c hcid).1
    dsimp only at hlow ⊢
    rw [hlow]; exact hA id c hcid
  | @genesis id ρ hnone hadd =>
    intro id' c hc
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · dsimp only; rw [hC.curAtVersion]; exact hC.curNonzero
    · exact hA id' c hold
  | @migrateIn id ρ v hv hnone hadd =>
    intro id' c hc
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · subst hv; dsimp only; rw [hC.curAtVersion]; exact hC.curNonzero
    · exact hA id' c hold
  | @transition id c0 ρ hc0 hut hguard happ hlt =>
    intro id' c hc
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · exact (edge_facts hC hut).2.2.2.2.2.1
    · exact hA id' c hold
  | @bootstrapReset id c0 R ρ hc0 hleg hadd hlt =>
    intro id' c hc
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · obtain ⟨_, hrel, hR⟩ := hC.bootstraps _ R hleg
      dsimp only; rw [hrel]; exact hR
    · exact hA id' c hold
  | arbitraryCut _ _ _ => exact absurd trivial hl

/-! ## Starting states -/

theorem FreshSystemSatisfiesInvariant : Properties.FreshSystemSatisfiesInvariant := by
  intro W R hR
  exact ⟨InitSatisfiesInvariant W R hR, fun _ _ h => by simp at h⟩

theorem BootstrapSystemSatisfiesInvariant : Properties.BootstrapSystemSatisfiesInvariant := by
  intro W old R chains hR hlt hchains
  refine ⟨BootstrapSatisfiesInvariant W old R hR hlt, ?_⟩
  intro id c hc
  have hle := hchains id c hc
  refine ⟨by simp only [bootstrapState]; omega, fun hrel => ?_⟩
  exfalso
  apply hrel
  simp only [bootstrapState]
  rw [upd_ne _ _ (by omega)]

theorem StepPreservesSysInvariant : Properties.StepPreservesSysInvariant :=
  fun _ _ _ _ hI h hl => step_sysInv hI h hl

theorem ChainsRunTheirVersionsRelease : Properties.ChainsRunTheirVersionsRelease := by
  intro W s s' ls hI h hl id c hc hrel
  obtain ⟨hC, hch⟩ := run_sysInv hI h hl
  exact ⟨(hC.relAtSound _ hrel).2, (hch id c hc).2 hrel⟩

theorem FreshChainsRunTheirVersionsRelease : Properties.FreshChainsRunTheirVersionsRelease := by
  intro W R s' ls hR h hl
  have key : ∀ {s s'' : Sys} {ls : List Label}, SysInv W s → AllRegistry s → Run W s ls s'' →
      (∀ l ∈ ls, ¬ l.isArbitrary) → SysInv W s'' ∧ AllRegistry s'' := by
    intro s s'' ls hI hA hr hl
    induction hr with
    | nil => exact ⟨hI, hA⟩
    | cons hs _ ih =>
      have hl0 := hl _ (List.mem_cons_self)
      exact ih (step_sysInv hI hs hl0) (step_allRegistry hI hA hs hl0)
        (fun l hm => hl l (List.mem_cons_of_mem _ hm))
  obtain ⟨⟨hC, hch⟩, hA⟩ := key (FreshSystemSatisfiesInvariant W R hR)
    (fun _ _ h => by simp at h) h hl
  intro id c hc
  have hrel := hA id c hc
  exact ⟨hrel, (hC.relAtSound _ hrel).2, (hch id c hc).2 hrel⟩

/-! ## One transition -/

theorem TransitionStartsAndLandsOnRelease : Properties.TransitionStartsAndLandsOnRelease := by
  intro W s s' id c hC hc h
  cases h with
  | @transition _ c0 ρ hc0 hut hguard happ hlt =>
    have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
    subst hcc
    obtain ⟨hfrom, hrz, _, hle, hnr, hnz, hver⟩ := edge_facts hC hut
    refine ⟨hrz, by rw [hguard, hfrom], ⟨(s.edge W c0.pv).new, ρ⟩, by simp, hlt, hle, hnz, hver, ?_⟩
    rw [hguard] at happ
    dsimp only
    rw [applyDerived_rows happ, hnr]

theorem DriftBlocksTransition : Properties.DriftBlocksTransition := by
  rintro W s id c hC hc hdrift ⟨s', h⟩
  cases h with
  | @transition _ c0 ρ hc0 hut hguard happ hlt =>
    have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
    subst hcc
    apply hdrift
    rw [hguard, (edge_facts hC hut).1]

/-! ## Without the guard -/

theorem UnguardedCutKeepsForeignSelectors : Properties.UnguardedCutKeepsForeignSelectors := by
  intro ρ σ A B h
  by_cases hAB : A = B
  · subst hAB
    simp [applyDerived] at h
    subst h
    exact ⟨fun _ _ _ => rfl, fun hne => absurd rfl hne⟩
  · refine ⟨fun y hA hB => ?_, fun _ y hy => ?_⟩
    · rw [applyDerived_spec h hAB y]; simp [hA, hB]
    · rw [applyDerived_spec h hAB y]; simp [hy]


/-! ## Countermodels and witnesses -/

/-- `Remove` of an unrouted selector reverts the whole cut list. -/
lemma removeAll_none {ρ : Routing} {ks : List Selector} {y : Selector} (hy : y ∈ ks)
    (hρ : ρ y = none) : removeAll ρ ks = none := by
  induction ks generalizing ρ with
  | nil => simp at hy
  | cons x xs ih =>
    simp only [removeAll, removeSel]
    split_ifs with hx
    · rfl
    · simp only [Option.bind_some]
      have hyx : y ≠ x := fun h => hx (h ▸ hρ)
      apply ih (List.mem_of_ne_of_mem hyx hy)
      rw [upd_ne _ _ hyx]; exact hρ

/-- A routing that lacks one of the departing release's selectors cannot take a
changing edge, even without the guard. -/
lemma applyDerived_none_of_missing {ρ : Routing} {A B : ReleaseRows} {y : Selector}
    (hAB : A ≠ B) (hy : y ∈ A.map Prod.fst) (hρ : ρ y = none) : applyDerived ρ A B = none := by
  simp only [applyDerived, hAB, ite_false, removeAll_none hy hρ, Option.bind_none]

/-- The unguarded cut applies when the live routing has every departing selector and
none of the arriving ones that are new. -/
lemma applyDerived_ok {ρ : Routing} {A B : ReleaseRows} (hA : (A.map Prod.fst).Nodup)
    (hB : (B.map Prod.fst).Nodup) (hroute : ∀ y ∈ A.map Prod.fst, ρ y ≠ none)
    (hfree : ∀ y ∈ B.map Prod.fst, y ∉ A.map Prod.fst → ρ y = none) :
    ∃ σ, applyDerived ρ A B = some σ := by
  by_cases hAB : A = B
  · exact ⟨ρ, by simp [applyDerived, hAB]⟩
  · obtain ⟨τ, hτ⟩ := removeAll_ok hA hroute
    obtain ⟨σ, hσ⟩ := addAll_ok (ρ := τ) hB (fun y hy => by
      rw [removeAll_spec hτ y]
      split_ifs with hyA
      · rfl
      · exact hfree y hy hyA)
    exact ⟨σ, by simp only [applyDerived, hAB, ite_false, hτ, Option.bind_some, hσ]⟩

private lemma wNodup100 : ((wWorld.relRows 100).map Prod.fst).Nodup := by decide
private lemma wNodup200 : ((wWorld.relRows 200).map Prod.fst).Nodup := by decide

theorem BreakGlassSelectorSurvivesWithoutGuard :
    Properties.BreakGlassSelectorSurvivesWithoutGuard := by
  have hrun := Run.cons (W := wWorld)
    (Step.genesis (s := wSys0) (id := 0) rfl (addAll_empty_eq wNodup100))
    (Run.cons (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))
      (Run.cons (Step.arbitraryCut (id := 0) 1 bgExtra rfl) Run.nil))
  have hC := run_ctmInv (s := wSys0) (InitSatisfiesInvariant wWorld 100 (by decide)) hrun
  obtain ⟨σ, hσ⟩ := applyDerived_ok (ρ := bgExtra) wNodup100 wNodup200 (by decide) (by decide)
  have hne : wWorld.relRows 100 ≠ wWorld.relRows 200 := by decide
  have hσ9 : σ 9 = some (99, false) := by
    rw [applyDerived_spec hσ hne 9]; decide
  refine ⟨_, hrun,
    ⟨_, rfl, rfl, by decide, fun h => absurd (congrFun h 9) (by decide), by decide, by decide,
      by decide⟩,
    ⟨σ, ⟨_, rfl, by decide, hσ, by decide⟩, hσ9⟩,
    DriftBlocksTransition _ _ _ _ hC rfl (fun h => absurd (congrFun h 9) (by decide))⟩

theorem MissingSelectorBricksTransition : Properties.MissingSelectorBricksTransition := by
  have hrun := Run.cons (W := wWorld)
    (Step.genesis (s := wSys0) (id := 0) rfl (addAll_empty_eq wNodup100))
    (Run.cons (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))
      (Run.cons (Step.arbitraryCut (id := 0) 1 bgMissing rfl) Run.nil))
  have hC := run_ctmInv (s := wSys0) (InitSatisfiesInvariant wWorld 100 (by decide)) hrun
  have hnone : applyDerived bgMissing (wWorld.relRows 100) (wWorld.relRows 200) = none :=
    applyDerived_none_of_missing (y := 2) (by decide) (by decide) (by decide)
  refine ⟨_, hrun, ⟨_, rfl, rfl, by decide, by decide⟩, ?_,
    DriftBlocksTransition _ _ _ _ hC rfl (fun h => absurd (congrFun h 2) (by decide))⟩
  rintro ⟨ρ, c, hc, _, happ, _⟩
  have hcc : c = ⟨1, bgMissing⟩ := (Option.some.inj (hc.symm.trans rfl) :)
  subst hcc
  have h2 : applyDerived bgMissing (wWorld.relRows 100) (wWorld.relRows 200) = some ρ := happ
  rw [hnone] at h2
  exact absurd h2 (by simp)

theorem ChainRoutingWitness : Properties.ChainRoutingWitness := by
  have hrun := Run.cons (W := wWorld)
    (Step.genesis (s := wSys0) (id := 0) rfl (addAll_empty_eq wNodup100))
    (Run.cons (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))
      (Run.cons (Step.transition (id := 0) rfl (by decide) rfl
          (applyDerived_rows_eq wNodup100 wNodup200) (by decide))
        (Run.cons (Step.genesis (id := 1) rfl (addAll_empty_eq wNodup200)) Run.nil)))
  exact ⟨_, hrun, FreshSystemSatisfiesInvariant wWorld 100 (by decide),
    ⟨_, rfl, by decide, rfl⟩, ⟨_, rfl, by decide, rfl⟩, by decide,
    fun h => absurd (congrFun h 1) (by decide)⟩

theorem BootstrapResetWitness : Properties.BootstrapResetWitness := by
  have hrun := Run.cons (W := wWorld)
    (Step.bootstrapReset (s := wBootSys) (id := 5) (R := 100) rfl (by decide)
      (addAll_empty_eq wNodup100) (by decide)) Run.nil
  have hinv : SysInv wWorld wBootSys := by
    refine BootstrapSystemSatisfiesInvariant wWorld 0 100 _ (by decide) (by decide) ?_
    intro id c h
    rcases upd_chain h with ⟨_, rfl⟩ | ⟨_, h'⟩
    · exact le_rfl
    · simp at h'
  exact ⟨_, hrun, hinv, ⟨_, rfl, by decide, fun h => absurd (congrFun h 7) (by decide)⟩,
    ⟨_, rfl, by decide, rfl, by decide⟩⟩

end Contracts.ChainTypeManager
