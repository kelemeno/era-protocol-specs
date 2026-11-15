import EraSpec.Contracts.ChainTypeManager.Properties.EngineGettersFaithful
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorUpgradeChain

/-!
# Proofs: what the routing headline assumes about the engine's getters

Applying the derived cut list action by action is `applyDerived` (`applyCuts_derived`), so in a
state whose slots hold derived objects a refined step is a `ChainRouting` step (`estep_step`,
`step_estep`). Derived slots are preserved by every CTM writer that installs only derived objects
(`cstep_slotsDerived`), so a refined run is an `ExecutorUpgradeChain` run step by step
(`eustep_sim`, `eurun_sim`), and the headline transfers from
`RefinedTameRunKeepsChainsOnTheirRelease`. The countermodels and the witness are one concrete run
in three engines.
-/

namespace Contracts.ChainTypeManager.EngineGetters

/-! ## The cut list -/

lemma applyCuts_append (ρ : Routing) (cs₁ cs₂ : List SelCut) :
    applyCuts ρ (cs₁ ++ cs₂) = (applyCuts ρ cs₁).bind (fun σ => applyCuts σ cs₂) := by
  induction cs₁ generalizing ρ with
  | nil => simp [applyCuts]
  | cons c cs ih =>
    simp only [List.cons_append, applyCuts]
    cases h : applySel ρ c with
    | none => simp
    | some σ => simp [ih]

lemma applyCuts_removes (ρ : Routing) (A : ReleaseRows) :
    applyCuts ρ (A.map (fun p => SelCut.remove p.1)) = removeAll ρ (A.map Prod.fst) := by
  induction A generalizing ρ with
  | nil => rfl
  | cons p A ih =>
    simp only [List.map_cons, applyCuts, applySel, removeAll]
    cases h : removeSel ρ p.1 with
    | none => simp
    | some σ => simp [ih]

lemma applyCuts_adds (ρ : Routing) (B : ReleaseRows) :
    applyCuts ρ (B.map (fun p => SelCut.add p.1 p.2)) = addAll ρ B := by
  induction B generalizing ρ with
  | nil => rfl
  | cons p B ih =>
    obtain ⟨x, r⟩ := p
    simp only [List.map_cons, applyCuts, applySel, addAll]
    cases h : addSel ρ x r with
    | none => simp
    | some σ => simp [ih]

lemma applyCuts_derived (ρ : Routing) (A B : ReleaseRows) :
    applyCuts ρ (derivedCuts A B) = applyDerived ρ A B := by
  unfold derivedCuts applyDerived
  split_ifs with hAB
  · rfl
  · rw [applyCuts_append, applyCuts_removes]
    simp only [applyCuts_adds]

theorem DerivedCutsAreApplyDerived : Properties.DerivedCutsAreApplyDerived :=
  fun ρ A B => applyCuts_derived ρ A B

/-! ## One routing step -/

lemma estep_step {W : World} {G : Engine} {s s' : Sys} {l : Label} (hD : SlotsDerived W G s.ctm)
    (h : EStep W G s l s') : Step W s l s' := by
  cases h with
  | base _ h => exact h
  | @transition id c ρ hc hut hguard happ hlt =>
    obtain ⟨hcuts, htarget⟩ := hD _ hut
    rw [hcuts, applyCuts_derived] at happ
    rw [htarget] at hlt ⊢
    exact Step.transition hc hut hguard happ hlt

lemma step_estep {W : World} {G : Engine} {s s' : Sys} {l : Label} (hD : SlotsDerived W G s.ctm)
    (h : Step W s l s') : EStep W G s l s' := by
  by_cases hl : ∃ id, l = .transition id
  · obtain ⟨id, rfl⟩ := hl
    cases h with
    | @transition _ c ρ hc hut hguard happ hlt =>
      obtain ⟨hcuts, htarget⟩ := hD _ hut
      have he := EStep.transition (G := G) hc hut hguard
        (by rw [hcuts, applyCuts_derived]; exact happ) (by rw [htarget]; exact hlt)
      rw [htarget] at he
      exact he
  · exact EStep.base (fun id hid => hl ⟨id, hid⟩) h

theorem DerivedEngineStepIsAStep : Properties.DerivedEngineStepIsAStep :=
  fun _ _ _ _ _ hD => ⟨estep_step hD, step_estep hD⟩

lemma estep_ctm_cases {W : World} {G : Engine} {s s' : Sys} {l : Label} (h : EStep W G s l s') :
    s'.ctm = s.ctm ∨ ∃ op, l = .ctm op ∧ CStep W s.ctm op s'.ctm := by
  cases h with
  | base _ h => exact step_ctm_cases h
  | transition _ _ _ _ _ => exact Or.inl rfl

/-! ## Derived slots along the CTM's writers -/

lemma cstep_slotsDerived {W : World} {G : Engine} {s s' : CTM} {op : Op}
    (hD : SlotsDerived W G s) (hcommit : ∀ t, op = .commit t → EngineDerived W G t)
    (hrepl : ∀ e r, op = .replace e r → EngineDerived W G r) (h : CStep W s op s') :
    SlotsDerived W G s' := by
  cases h with
  | @commit t _ _ _ _ _ _ =>
    intro v hv
    have hv' : upd s.ut (W.tr t).old t v ≠ 0 := hv
    show EngineDerived W G (upd s.ut (W.tr t).old t v)
    by_cases hve : v = (W.tr t).old
    · rw [hve, upd_same]
      exact hcommit t rfl
    · rw [upd_ne _ _ hve] at hv' ⊢
      exact hD v hv'
  | @replace e r _ _ _ _ _ _ _ _ =>
    intro v hv
    have hv' : upd s.ut (W.tr e).old r v ≠ 0 := hv
    show EngineDerived W G (upd s.ut (W.tr e).old r v)
    by_cases hve : v = (W.tr e).old
    · rw [hve, upd_same]
      exact hrepl e r rfl
    · rw [upd_ne _ _ hve] at hv' ⊢
      exact hD v hv'
  | legacyCommit _ _ => exact hD
  | legacyRecut _ _ => exact hD

/-! ## Refined runs are `ExecutorUpgradeChain` runs -/

private lemma efstep_sim {X : XConfig} {G : Engine} {s s' : XState} {f : FCall}
    (hD : SlotsDerived X.W G s.sys.ctm) (h : EFStep X G s f s') (hk : f.KeepsCtmCode)
    (hI : ∀ t, FInstalls t f → EngineDerived X.W G t) :
    FStep X s f s' ∧ SlotsDerived X.W G s'.sys.ctm := by
  cases h with
  | @sys l sys' he =>
    refine ⟨FStep.sys (estep_step hD he), ?_⟩
    show SlotsDerived X.W G sys'.ctm
    rcases estep_ctm_cases he with heq | ⟨op, rfl, hc⟩
    · rw [heq]
      exact hD
    · exact cstep_slotsDerived hD (fun t ht => hI t (by subst ht; rfl))
        (fun e r hr => hI r (by subst hr; rfl)) hc
  | upgradeProxy h1 h2 h3 => exact ⟨FStep.upgradeProxy h1 h2 h3, hD⟩
  | swapCtm _ _ => exact hk.elim

private lemma efrun_sim {X : XConfig} {G : Engine} {s s' : XState} {calls : List FCall}
    (h : EFRun X G s calls s') :
    SlotsDerived X.W G s.sys.ctm → (∀ f ∈ calls, f.KeepsCtmCode) →
    (∀ t, (∃ f ∈ calls, FInstalls t f) → EngineDerived X.W G t) →
    FRun X s calls s' ∧ SlotsDerived X.W G s'.sys.ctm := by
  induction h with
  | nil => intro hD _ _; exact ⟨FRun.nil, hD⟩
  | cons hstep _ ih =>
    intro hD hk hI
    obtain ⟨hf1, hD1⟩ := efstep_sim hD hstep (hk _ List.mem_cons_self)
      (fun t ht => hI t ⟨_, List.mem_cons_self, ht⟩)
    obtain ⟨hf2, hD2⟩ := ih hD1 (fun f hf => hk f (List.mem_cons_of_mem _ hf))
      (fun t ⟨f, hf, ht⟩ => hI t ⟨f, List.mem_cons_of_mem _ hf, ht⟩)
    exact ⟨FRun.cons hf1 hf2, hD2⟩

private lemma eustep_sim {X : XConfig} {G : Engine} {s s' : XState} {u : ULabel}
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) (hD : SlotsDerived X.W G s.sys.ctm)
    (h : EUStep X G s u s') (hk : u.toX.KeepsCtmCode X)
    (hI : ∀ t, Installs t u → EngineDerived X.W G t) :
    UStep X s u s' ∧ SlotsDerived X.W G s'.sys.ctm := by
  cases h with
  | x hnu hnf hx =>
    refine ⟨UStep.x hnu hx, ?_⟩
    cases hx with
    | @infra T J c' happ hc =>
      have hk' : ∀ r ∈ T.rows, r.proxy ≠ X.ctmProxy := hk
      have hJ : J X.ctmProxy = s.impl X.ctmProxy :=
        ProxyUpgradeCurrent.UnmovedProxiesFrame X.rc s.impl J T.rows hf happ.2.2 X.ctmProxy hk'
      show SlotsDerived X.W G c'
      rw [hc hJ]
      exact hD
    | @commit t sys' hs _ _ =>
      show SlotsDerived X.W G sys'.ctm
      rcases step_ctm_cases hs with heq | ⟨op, hop, hc⟩
      · rw [heq]
        exact hD
      · cases hop
        exact cstep_slotsDerived hD (fun t' ht' => hI t' (by cases ht'; rfl))
          (fun _ _ hr => by cases hr) hc
    | upgradeChain _ => exact absurd trivial hnu
    | forward _ => exact absurd rfl (hnf _)
    | @env l sys' he hs =>
      show SlotsDerived X.W G sys'.ctm
      rcases step_ctm_cases hs with heq | ⟨op, rfl, _⟩
      · rw [heq]
        exact hD
      · exact he.elim
  | forward hr =>
    obtain ⟨hfr, hD'⟩ := efrun_sim hr hD hk (fun t ⟨f, hf, ht⟩ => hI t ⟨f, hf, ht⟩)
    exact ⟨UStep.x (fun h => h) (XStep.forward hfr), hD'⟩
  | @upgradeChain t id c sys' h0 hslot hc hpv he =>
    refine ⟨UStep.upgradeChain h0 hslot hc hpv (estep_step hD he), ?_⟩
    show SlotsDerived X.W G sys'.ctm
    rcases estep_ctm_cases he with heq | ⟨op, hop, _⟩
    · rw [heq]
      exact hD
    · cases hop
  | @adminUpgrade id old c sys' hc hpv he =>
    refine ⟨UStep.adminUpgrade hc hpv (estep_step hD he), ?_⟩
    show SlotsDerived X.W G sys'.ctm
    rcases estep_ctm_cases he with heq | ⟨op, hop, _⟩
    · rw [heq]
      exact hD
    · cases hop

private lemma eurun_sim {X : XConfig} {G : Engine} {s s' : XState} {us : List ULabel}
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) (h : EURun X G s us s') :
    SlotsDerived X.W G s.sys.ctm → (∀ u ∈ us, u.toX.KeepsCtmCode X) →
    (∀ t, (∃ u ∈ us, Installs t u) → EngineDerived X.W G t) →
    URun X s us s' ∧ SlotsDerived X.W G s'.sys.ctm := by
  induction h with
  | nil => intro hD _ _; exact ⟨URun.nil, hD⟩
  | cons hstep _ ih =>
    intro hD hk hI
    obtain ⟨h1, hD1⟩ := eustep_sim hf hD hstep (hk _ List.mem_cons_self)
      (fun t ht => hI t ⟨_, List.mem_cons_self, ht⟩)
    obtain ⟨h2, hD2⟩ := ih hD1 (fun u hu => hk u (List.mem_cons_of_mem _ hu))
      (fun t ⟨u, hu, ht⟩ => hI t ⟨u, List.mem_cons_of_mem _ hu, ht⟩)
    exact ⟨URun.cons h1 h2, hD2⟩

theorem DerivedEngineRunIsAUpgradeChainRun : Properties.DerivedEngineRunIsAUpgradeChainRun :=
  fun _ _ _ _ _ hf hD h hk hI => eurun_sim hf h hD hk hI

private lemma xtame_keeps {X : XConfig} {x : XLabel} (ht : x.Tame X) : x.KeepsCtmCode X := by
  cases x with
  | infra T => exact ht
  | forward calls =>
    have ht' : ∀ c ∈ calls, c.Tame := ht
    intro c hc
    have htc := ht' c hc
    cases c with
    | sys _ => trivial
    | upgradeProxy _ _ => trivial
    | swapCtm _ _ => exact htc.elim
  | commit _ => trivial
  | upgradeChain _ => trivial
  | env _ => trivial

theorem DerivedEngineTameRunKeepsChainsOnTheirRelease :
    Properties.DerivedEngineTameRunKeepsChainsOnTheirRelease := by
  intro X G s s' us hf hI hD h ht hinst
  obtain ⟨hu, _⟩ := eurun_sim hf h hD (fun u hu => xtame_keeps (ht u hu)) hinst
  exact RefinedTameRunKeepsChainsOnTheirRelease X s s' us hf hI hu ht

/-! ## The concrete run, in any engine -/

private lemma eurun_snoc {X : XConfig} {G : Engine} {s s1 s2 : XState} {us : List ULabel}
    {u : ULabel} (h : EURun X G s us s1) (h' : EUStep X G s1 u s2) :
    EURun X G s (us ++ [u]) s2 := by
  induction h with
  | nil => exact EURun.cons h' EURun.nil
  | cons hs _ ih => exact EURun.cons hs (ih h')

/-- Create chain `0`, commit `300`, and forward its replacement by `400`. No edge is crossed, so
the engine does not matter. -/
private lemma e_prefix (G : Engine) :
    ∃ s, EURun wX G wX0 [.x (.env (.genesis 0)), .x (.commit 300),
        .x (.forward [.sys (.ctm (.replace 300 400))])] s ∧
      s.sys.chains 0 = some ⟨1, rowsRouting (wWorld.relRows 100)⟩ ∧ s.sys.ctm.ut 1 = 400 ∧
      s.sys.ctm.pv = 2 ∧ s.sys.ctm.cur = 200 ∧ s.sys.ctm.relAt 2 = 200 := by
  have hc : CStep wWorld (initState wWorld 100) (.commit 300) _ :=
    CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨p1, p2⟩ := ExecutorPostcheckPasses _ _ _ _ hc
  exact ⟨_, EURun.cons (X := wX) (G := G) (s := wX0)
    (EUStep.x (l := .env (.genesis 0)) (fun h => h) (fun _ h => by cases h)
      (XStep.env trivial (Step.genesis (id := 0) rfl (addAll_empty_eq xNodup100))))
    (EURun.cons (EUStep.x (l := .commit 300) (fun h => h) (fun _ h => by cases h)
        (XStep.commit (Step.ctm hc) p1 p2))
      (EURun.cons (EUStep.forward (EFRun.cons (EFStep.sys (EStep.base (fun _ h => by cases h)
          (Step.ctm (CStep.replace (e := 300) (r := 400) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide))))) EFRun.nil))
        EURun.nil)),
    rfl, by decide, by decide, by decide, by decide⟩

/-- Chain `0`, at version 1 on release `100`, crosses a slot-1 object `t` departing from release
`100`, by the engine's getters. -/
private lemma e_cross {G : Engine} {S : Sys} {t : Address} {ρ : Routing}
    (hch : S.chains 0 = some ⟨1, rowsRouting (wWorld.relRows 100)⟩) (hut : S.ctm.ut 1 = t)
    (ht0 : t ≠ 0) (hfrom : (wWorld.tr t).fromRel = 100)
    (happ : applyCuts (rowsRouting (wWorld.relRows 100)) (G.cuts t) = some ρ)
    (hlt : 1 < G.target t) :
    ∃ sys', EStep wWorld G S (.transition 0) sys' ∧ sys'.ctm = S.ctm ∧
      sys'.chains 0 = some ⟨G.target t, ρ⟩ := by
  refine ⟨_, EStep.transition (c := ⟨1, rowsRouting (wWorld.relRows 100)⟩) (ρ := ρ) hch ?_ ?_ ?_ ?_,
    rfl, ?_⟩
  · show S.ctm.ut 1 ≠ 0
    rw [hut]
    exact ht0
  · show rowsRouting (wWorld.relRows 100) =
      rowsRouting (wWorld.relRows (wWorld.tr (S.ctm.ut 1)).fromRel)
    rw [hut, hfrom]
  · show applyCuts (rowsRouting (wWorld.relRows 100)) (G.cuts (S.ctm.ut 1)) = some ρ
    rw [hut]
    exact happ
  · show 1 < G.target (S.ctm.ut 1)
    rw [hut]
    exact hlt
  · show upd S.chains 0 (some ⟨G.target (S.ctm.ut 1), ρ⟩) 0 = some ⟨G.target t, ρ⟩
    rw [hut, upd_same]

/-- `wReplaceRun` in any engine whose `400` applies from release `100` and lands above version 1. -/
private lemma e_run (G : Engine) {ρ : Routing}
    (happ : applyCuts (rowsRouting (wWorld.relRows 100)) (G.cuts 400) = some ρ)
    (hlt : 1 < G.target 400) :
    ∃ s, EURun wX G wX0 wReplaceRun s ∧ s.sys.chains 0 = some ⟨G.target 400, ρ⟩ ∧
      s.sys.ctm.pv = 2 ∧ s.sys.ctm.cur = 200 ∧ s.sys.ctm.relAt 2 = 200 := by
  obtain ⟨s3, hpre, hch, hut, hpv, hcur, hrel2⟩ := e_prefix G
  obtain ⟨sys4, hstep, hctm, hch4⟩ := e_cross (G := G) hch hut (by decide) (by decide) happ hlt
  refine ⟨{ s3 with sys := sys4 }, eurun_snoc hpre (EUStep.upgradeChain (t := 400) (id := 0)
    (by decide) (by rw [show (wX.W.tr 400).old = 1 from rfl]; exact hut) hch (by decide) hstep),
    hch4, ?_, ?_, ?_⟩
  · show sys4.ctm.pv = 2
    rw [hctm]
    exact hpv
  · show sys4.ctm.cur = 200
    rw [hctm]
    exact hcur
  · show sys4.ctm.relAt 2 = 200
    rw [hctm]
    exact hrel2

private lemma genuine_derived : ∀ t, EngineDerived wWorld wGenuineEngine t :=
  fun _ => ⟨rfl, rfl⟩

private lemma replaceRun_tame : ∀ u ∈ wReplaceRun, u.Tame wX := by
  intro u hu
  simp only [wReplaceRun, List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · intro f hf
    rw [List.mem_singleton.mp hf]
    simp [FCall.Tame, Label.isArbitrary]
  · trivial

private lemma happ_derived (G : Engine)
    (hG : G.cuts 400 = derivedCuts (wWorld.relRows 100) (wWorld.relRows 200)) :
    applyCuts (rowsRouting (wWorld.relRows 100)) (G.cuts 400) =
      some (rowsRouting (wWorld.relRows 200)) := by
  rw [hG, applyCuts_derived]
  exact applyDerived_rows_eq xNodup100 xNodup200

/-! ## Certificates: the countermodels and the witness -/

theorem ForeignCutsBreakTheHeadline : Properties.ForeignCutsBreakTheHeadline := by
  have h9 : rowsRouting (wWorld.relRows 200) 9 = none := by decide
  have hcuts : wForeignCuts.cuts 400 =
      derivedCuts (wWorld.relRows 100) (wWorld.relRows 200) ++ [SelCut.add 9 (99, false)] := rfl
  have happ : applyCuts (rowsRouting (wWorld.relRows 100)) (wForeignCuts.cuts 400) =
      some (upd (rowsRouting (wWorld.relRows 200)) 9 (some (99, false))) := by
    rw [hcuts, applyCuts_append, applyCuts_derived, applyDerived_rows_eq xNodup100 xNodup200,
      Option.bind_some]
    simp [applyCuts, applySel, addSel, h9]
  obtain ⟨s, hrun, hch, _, _, hrel2⟩ := e_run wForeignCuts happ (by decide)
  have hc2 : s.sys.chains 0 =
      some ⟨2, upd (rowsRouting (wWorld.relRows 200)) 9 (some (99, false))⟩ := hch
  have hne : upd (rowsRouting (wWorld.relRows 200)) 9 (some (99, false)) ≠
      rowsRouting (wWorld.relRows 200) := fun h => absurd (congrFun h 9) (by decide)
  obtain ⟨sG, hrunG, hchG, _⟩ :=
    e_run wGenuineEngine (happ_derived wGenuineEngine rfl) (by decide)
  have hkG : ∀ u ∈ wReplaceRun, u.toX.KeepsCtmCode wX := fun u hu => xtame_keeps (replaceRun_tame u hu)
  have huG := (eurun_sim ProxyUpgradeCurrent.wConfig_frames hrunG (fun _ hv => (hv rfl).elim) hkG
    (fun t _ => genuine_derived t)).1
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wX0_inv, fun _ hv => (hv rfl).elim, replaceRun_tame,
    ?_, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, fun h => absurd h.1 (by decide),
    ⟨s, hrun, ⟨_, hc2, rfl, hrel2, upd_same (rowsRouting (wWorld.relRows 200)) 9 (some (99, false)),
      hne⟩, ?_⟩, sG, huG, _, hchG, rfl, rfl⟩
  · rintro t ⟨u, hu, hi⟩
    simp only [wReplaceRun, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl | rfl | rfl
    · exact hi.elim
    · exact Or.inl hi.symm
    · obtain ⟨f, hf, hfi⟩ := hi
      rw [List.mem_singleton.mp hf] at hfi
      exact Or.inr hfi.symm
    · exact hi.elim
  · intro hI
    have h1 : s.sys.ctm.relAt 2 ≠ 0 →
        upd (rowsRouting (wWorld.relRows 200)) 9 (some (99, false)) =
          rowsRouting (wWorld.relRows (s.sys.ctm.relAt 2)) := (hI.2 0 _ hc2).2
    rw [hrel2] at h1
    exact hne (h1 (by decide))

theorem ForeignTargetBreaksTheHeadline : Properties.ForeignTargetBreaksTheHeadline := by
  obtain ⟨s, hrun, hch, hpv, hcur, _⟩ :=
    e_run wForeignTarget (happ_derived wForeignTarget rfl) (by decide)
  have hc3 : s.sys.chains 0 = some ⟨3, rowsRouting (wWorld.relRows 200)⟩ := hch
  have hc600 : CStep wWorld s.sys.ctm (.commit 600) _ :=
    CStep.commit (t := 600) (by decide) (by rw [hcur]; decide) (by rw [hpv]; decide) (by decide)
      (by decide) (by decide)
  obtain ⟨p1, p2⟩ := ExecutorPostcheckPasses _ _ _ _ hc600
  have h5 : EUStep wX wForeignTarget s (.x (.commit 600)) _ :=
    EUStep.x (fun h => h) (fun _ h => by cases h) (XStep.commit (Step.ctm hc600) p1 p2)
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wX0_inv, fun _ hv => (hv rfl).elim, ?_, ⟨rfl, rfl⟩,
    fun h => absurd h.2 (by decide), rfl, s, _, hrun, ⟨_, hc3, rfl, hpv, rfl⟩, ?_, h5, _, hc3, rfl,
    ?_, fun h => absurd (congrFun h 1) (by decide)⟩
  · intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact replaceRun_tame u hu
    · rw [List.mem_singleton.mp hu]
      trivial
  · intro hI
    exact absurd (hI.2 0 _ hc3).1 (by rw [hpv]; decide)
  · show upd s.sys.ctm.relAt (wWorld.tr 600).new (wWorld.tr 600).newRel 3 = 250
    exact upd_same _ _ _

theorem EngineGettersWitness : Properties.EngineGettersWitness := by
  obtain ⟨s, hrun, hch, _, _, hrel2⟩ :=
    e_run wGenuineEngine (happ_derived wGenuineEngine rfl) (by decide)
  exact ⟨ProxyUpgradeCurrent.wConfig_frames, wX0_inv, genuine_derived, fun _ hv => (hv rfl).elim,
    replaceRun_tame, s, hrun, _, hch, rfl, hrel2, rfl⟩

end Contracts.ChainTypeManager.EngineGetters
