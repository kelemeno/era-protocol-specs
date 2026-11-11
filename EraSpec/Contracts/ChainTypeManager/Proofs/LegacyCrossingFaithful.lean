import EraSpec.Contracts.ChainTypeManager.Properties.LegacyCrossingFaithful
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorUpgradeChain
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocalExecutor

/-!
# Proofs: the executor headlines once pre-v35 chains cross opaque legacy edges themselves

A chain-side crossing writes exactly what `Step.arbitraryCut` writes (`cross_arbitrary`) and
leaves the CTM and every proxy alone (`crossStep_ctm`). So:

* the CTM-only results carry over through a generic preservation lemma (`lrun_ctm`), built on
  `ExecutorUpgradeChain`'s `xstep_ctm`;
* a refined run that keeps the CTM's code is a routing run (`lrun_sysRun`), and the per-chain
  headline transfers from `ChainRunsItsVersionsRelease`;
* `SysInv` survives a crossing exactly when the crossing lands consistently (`CrossKeepsSysInvIff`),
  and survives every executor step by `ExecutorForward`'s `xstep_keeps`.

The countermodel and the witness are concrete runs on the bootstrap witness systems.
-/

namespace Contracts.ChainTypeManager.LegacyCrossing

/-! ## One crossing -/

lemma crossStep_ctm {s s' : Sys} {id : ChainId} {v : ℕ} {ρ : Routing}
    (h : CrossStep s id v ρ s') : s'.ctm = s.ctm := by
  cases h
  rfl

/-- A chain-side crossing is `ChainRouting`'s break-glass step with the same data. -/
lemma cross_arbitrary {W : World} {s s' : Sys} {id : ChainId} {v : ℕ} {ρ : Routing}
    (h : CrossStep s id v ρ s') : Step W s (.arbitraryCut id v ρ) s' := by
  cases h with
  | mk hc _ _ => exact Step.arbitraryCut v ρ hc

theorem CrossIsABreakGlassStep : Properties.CrossIsABreakGlassStep :=
  fun _ _ _ _ _ _ h => cross_arbitrary h

theorem CrossKeepsSysInvIff : Properties.CrossKeepsSysInvIff := by
  intro W s s' id v ρ hI h
  cases h with
  | mk hc hleg hlt =>
    constructor
    · intro hI'
      exact hI'.2 id ⟨v, ρ⟩ (by simp [landAt])
    · intro hok
      refine ⟨hI.1, ?_⟩
      intro id' c' hc'
      rcases upd_chain (chains := s.chains) hc' with ⟨_, rfl⟩ | ⟨_, hold⟩
      · exact hok
      · exact hI.2 id' c' hold

/-! ## Executor steps and crossings: what a step keeps -/

lemma lstep_keeps {X : XConfig} {s s' : XState} {l : LLabel}
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) (hI : SysInv X.W s.sys)
    (h : LStep X s l s') (ht : l.ExecTame X) (hok : l.LandsOk X.W s.sys) : Keeps X s s' := by
  cases h with
  | u hu => exact xstep_keeps hf hI (ustep_toX hu) ht
  | @cross id v ρ sys' hc =>
    refine ⟨(CrossKeepsSysInvIff X.W s.sys sys' id v ρ hI hc).mpr hok, ?_, rfl⟩
    show s.sys.ctm.pv ≤ sys'.ctm.pv
    rw [crossStep_ctm hc]

lemma lrunOk_keeps {X : XConfig} {s s' : XState} {ls : List LLabel}
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) (h : LRunOk X s ls s') :
    SysInv X.W s.sys → (∀ l ∈ ls, l.ExecTame X) → Keeps X s s' := by
  induction h with
  | nil => intro hI _; exact ⟨hI, le_rfl, rfl⟩
  | cons hstep hok _ ih =>
    intro hI ht
    have h₁ := lstep_keeps hf hI hstep (ht _ List.mem_cons_self) hok
    exact keeps_trans h₁ (ih h₁.1 (fun l hl => ht l (List.mem_cons_of_mem _ hl)))

lemma lrunOk_lrun {X : XConfig} {s s' : XState} {ls : List LLabel} (h : LRunOk X s ls s') :
    LRun X s ls s' := by
  induction h with
  | nil => exact LRun.nil
  | cons hstep _ _ ih => exact LRun.cons hstep ih

theorem LandingRunPreservesSysInv : Properties.LandingRunPreservesSysInv := by
  intro X s s' ls hf hI h ht
  obtain ⟨hI', hpv, himpl⟩ := lrunOk_keeps hf h hI ht
  exact ⟨hI', hpv, himpl, fun id c hc hrel =>
    ⟨(hI'.1.relAtSound _ hrel).2, (hI'.2 id c hc).2 hrel⟩⟩

/-! ## Crossing-free runs are `ExecutorUpgradeChain` runs -/

lemma lrun_map_u {X : XConfig} (us : List ULabel) :
    ∀ {s s' : XState}, LRun X s (us.map LLabel.u) s' → URun X s us s' := by
  induction us with
  | nil => intro s s' h; cases h; exact URun.nil
  | cons u us ih =>
    intro s s' h
    rw [List.map_cons] at h
    cases h with
    | cons hstep hrest =>
      cases hstep with
      | u hu => exact URun.cons hu (ih hrest)

lemma urun_map_u {X : XConfig} {s s' : XState} {us : List ULabel} (h : URun X s us s') :
    LRun X s (us.map LLabel.u) s' := by
  induction h with
  | nil => exact LRun.nil
  | cons hs _ ih => exact LRun.cons (LStep.u hs) ih

lemma tame_crossFree {X : XConfig} : ∀ {ls : List LLabel}, (∀ l ∈ ls, l.Tame X) →
    ∃ us : List ULabel, ls = us.map LLabel.u ∧ ∀ u ∈ us, u.Tame X
  | [], _ => ⟨[], rfl, fun _ h => by simp at h⟩
  | l :: ls, ht => by
    obtain ⟨us, hus, hut⟩ := tame_crossFree (X := X) (ls := ls)
      (fun l' hl' => ht l' (List.mem_cons_of_mem _ hl'))
    cases l with
    | u u =>
      refine ⟨u :: us, by rw [hus]; rfl, ?_⟩
      intro u' hu'
      rcases List.mem_cons.mp hu' with rfl | hu'
      · exact ht _ List.mem_cons_self
      · exact hut u' hu'
    | cross id v ρ => exact False.elim (ht _ List.mem_cons_self)

theorem CrossFreeRunsAreUpgradeChainRuns : Properties.CrossFreeRunsAreUpgradeChainRuns :=
  fun _ _ _ us => ⟨lrun_map_u us, urun_map_u⟩

theorem TameRefinedRunKeepsChainsOnTheirRelease :
    Properties.TameRefinedRunKeepsChainsOnTheirRelease := by
  intro X s s' ls hf hI h ht
  obtain ⟨us, rfl, hut⟩ := tame_crossFree ht
  have hu : URun X s us s' := lrun_map_u us h
  obtain ⟨hI', hpv, himpl⟩ :=
    TameRunPreservesSysInv X s s' _ hf hI (urun_toX hu) (tame_toX hut)
  exact ⟨⟨us, rfl, hu, hut⟩, hI', hpv, himpl,
    RefinedTameRunKeepsChainsOnTheirRelease X s s' us hf hI hu hut⟩

/-! ## Refined runs as routing runs -/

private lemma run_app {W : World} {s s₁ s₂ : Sys} {xs ys : List Label}
    (h₁ : Run W s xs s₁) (h₂ : Run W s₁ ys s₂) : Run W s (xs ++ ys) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact Run.cons hs (ih h₂)

lemma lstep_sysRun {X : XConfig} {s s' : XState} {l : LLabel}
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) (h : LStep X s l s') (hk : l.KeepsCtmCode X) :
    Run X.W s.sys l.sysLabels s'.sys := by
  cases h with
  | u hu =>
    have hr := ExecutorRunIsARoutingRun X s s' _ hf (XRun.cons (ustep_toX hu) XRun.nil)
      (fun x hx => by rw [List.mem_singleton.mp hx]; exact hk)
    simpa [LLabel.sysLabels] using hr
  | cross hc => exact Run.cons (cross_arbitrary hc) Run.nil

lemma lrun_sysRun {X : XConfig} {s s' : XState} {ls : List LLabel}
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) (h : LRun X s ls s')
    (hk : ∀ l ∈ ls, l.KeepsCtmCode X) : Run X.W s.sys (ls.flatMap LLabel.sysLabels) s'.sys := by
  induction h with
  | nil => exact Run.nil
  | cons hs _ ih =>
    rw [List.flatMap_cons]
    exact run_app (lstep_sysRun hf hs (hk _ List.mem_cons_self))
      (ih (fun l hl => hk l (List.mem_cons_of_mem _ hl)))

theorem CrossRunIsARoutingRun : Properties.CrossRunIsARoutingRun :=
  fun _ _ _ _ hf h hk => lrun_sysRun hf h hk

theorem ChainRunsItsVersionsReleaseAcrossCrossings :
    Properties.ChainRunsItsVersionsReleaseAcrossCrossings := by
  intro X s s' ls id hf hC hok h hk hlast
  exact ChainRunsItsVersionsRelease X.W s.sys s'.sys _ id hC hok (lrun_sysRun hf h hk) hlast

/-! ## Executor-tame runs: where the break-glass labels come from -/

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

lemma ltame_keeps {X : XConfig} {l : LLabel} (ht : l.ExecTame X) : l.KeepsCtmCode X := by
  cases l with
  | u u => exact xtame_keeps (x := u.toX) ht
  | cross _ _ _ => trivial

/-- A tame executor step takes no break-glass routing step. -/
private lemma xstep_noArb {X : XConfig} {s s' : XState} {x : XLabel}
    (h : XStep X s x s') (ht : x.Tame X) : ∀ l ∈ x.sysLabels, ¬ l.isArbitrary := by
  cases h with
  | infra _ _ => intro l hl; simp [XLabel.sysLabels] at hl
  | commit _ _ _ =>
    intro l hl
    simp only [XLabel.sysLabels, List.mem_singleton] at hl
    subst hl
    simp [Label.isArbitrary]
  | upgradeChain _ =>
    intro l hl
    simp only [XLabel.sysLabels, List.mem_singleton] at hl
    subst hl
    simp [Label.isArbitrary]
  | @forward _ calls _ =>
    have ht' : ∀ c ∈ calls, c.Tame := ht
    intro l hl
    simp only [XLabel.sysLabels, List.mem_filterMap] at hl
    obtain ⟨c, hc, hcl⟩ := hl
    have htc := ht' c hc
    cases c with
    | sys l' =>
      simp only [FCall.sys?, Option.some.injEq] at hcl
      subst hcl
      exact htc
    | upgradeProxy _ _ => simp [FCall.sys?] at hcl
    | swapCtm _ _ => simp [FCall.sys?] at hcl
  | env he _ =>
    intro l hl
    simp only [XLabel.sysLabels, List.mem_singleton] at hl
    subst hl
    exact env_not_arbitrary he

/-- In an executor-tame refined step, a break-glass routing step is a chain-side crossing's. -/
private lemma lstep_arb {X : XConfig} {s s' : XState} {l : LLabel} (h : LStep X s l s')
    (ht : l.ExecTame X) :
    ∀ l' ∈ l.sysLabels, l'.isArbitrary → ∃ id v ρ, l = .cross id v ρ ∧ l' = .arbitraryCut id v ρ := by
  cases h with
  | u hu =>
    intro l' hl' harb
    exact absurd harb (xstep_noArb (ustep_toX hu) ht l' hl')
  | @cross id v ρ _ _ =>
    intro l' hl' _
    simp only [LLabel.sysLabels, List.mem_singleton] at hl'
    exact ⟨id, v, ρ, rfl, hl'⟩

private lemma lrun_arb {X : XConfig} {s s' : XState} {ls : List LLabel} (h : LRun X s ls s')
    (ht : ∀ l ∈ ls, l.ExecTame X) :
    ∀ l' ∈ ls.flatMap LLabel.sysLabels, l'.isArbitrary →
      ∃ id v ρ, LLabel.cross id v ρ ∈ ls ∧ l' = .arbitraryCut id v ρ := by
  induction h with
  | nil => intro l' hl'; simp at hl'
  | cons hs _ ih =>
    intro l' hl' harb
    rw [List.flatMap_cons, List.mem_append] at hl'
    rcases hl' with hl' | hl'
    · obtain ⟨id, v, ρ, hl, hl'e⟩ := lstep_arb hs (ht _ List.mem_cons_self) l' hl' harb
      exact ⟨id, v, ρ, by rw [← hl]; exact List.mem_cons_self, hl'e⟩
    · obtain ⟨id, v, ρ, hm, hl'e⟩ := ih (fun l hl => ht l (List.mem_cons_of_mem _ hl)) l' hl' harb
      exact ⟨id, v, ρ, List.mem_cons_of_mem _ hm, hl'e⟩

theorem ExecTamePremiseImpliesChainLocal : Properties.ExecTamePremiseImpliesChainLocal := by
  intro X s s' ls h ht
  refine ⟨fun l hl => ltame_keeps (ht l hl), ?_⟩
  intro id hno pre l post hls hw _ harb
  obtain ⟨id', v, ρ, hm, rfl⟩ := lrun_arb h ht l (by rw [hls]; simp) harb
  have hid : id' = id := hw
  subst hid
  exact hno v ρ hm

/-! ## The CTM along refined runs -/

section Preservation

variable {X : XConfig} {Q : CTM → Prop} {G : Address → Address → Prop}

lemma lstep_ctm
    (hQ : ∀ c op c', Q c → (∀ e r, op = .replace e r → G e r) →
      CStep X.W c op c' → Q c')
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) {s s' : XState} {l : LLabel}
    (h : LStep X s l s') (ht : l.ExecTame X) (hG : ∀ e r, l.ForwardsReplace e r → G e r)
    (hq : Q s.sys.ctm) : Q s'.sys.ctm := by
  cases h with
  | u hu => exact xstep_ctm hQ hf (ustep_toX hu) ht hG hq
  | @cross _ _ _ sys' hc =>
    show Q sys'.ctm
    rw [crossStep_ctm hc]
    exact hq

lemma lrun_ctm
    (hQ : ∀ c op c', Q c → (∀ e r, op = .replace e r → G e r) →
      CStep X.W c op c' → Q c')
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) {s s' : XState} {ls : List LLabel}
    (h : LRun X s ls s') :
    (∀ l ∈ ls, l.ExecTame X) → (∀ e r, (∃ l ∈ ls, l.ForwardsReplace e r) → G e r) →
    Q s.sys.ctm → Q s'.sys.ctm := by
  induction h with
  | nil => intro _ _ hq; exact hq
  | cons hstep _ ih =>
    intro ht hG hq
    exact ih (fun l hl => ht l (List.mem_cons_of_mem _ hl))
      (fun e r ⟨l, hl, hfr⟩ => hG e r ⟨l, List.mem_cons_of_mem _ hl, hfr⟩)
      (lstep_ctm hQ hf hstep (ht _ List.mem_cons_self)
        (fun e r hfr => hG e r ⟨_, List.mem_cons_self, hfr⟩) hq)

end Preservation

theorem MisreportingSlotStaysFrozenAcrossCrossings :
    Properties.MisreportingSlotStaysFrozenAcrossCrossings := by
  intro X s s' ls v hf hI hv hmis h ht
  have hQ : ∀ c op c', (CtmInv X.W c ∧ c.ut v = s.sys.ctm.ut v) →
      (∀ e r, op = .replace e r → True) →
      CStep X.W c op c' → (CtmInv X.W c' ∧ c'.ut v = s.sys.ctm.ut v) := by
    rintro c op c' ⟨hIc, hcv⟩ _ hs
    refine ⟨step_inv hIc hs, ?_⟩
    rw [cstep_frozen hIc (by rw [hcv]; exact hv) (by rw [hcv]; exact hmis) hs, hcv]
  obtain ⟨_, hfrozen⟩ :=
    lrun_ctm (G := fun _ _ => True) hQ hf h ht (fun _ _ _ => trivial) ⟨hI, rfl⟩
  refine ⟨hfrozen, ?_⟩
  rintro id c hc hpv ⟨t, s'', h'⟩
  obtain ⟨c0, hc0, hrep, _⟩ := (UpgradeChainEnabledIff X s' id).mp ⟨t, s'', h'⟩
  have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
  subst hcc
  rw [hpv, hfrozen] at hrep
  exact hmis hrep

theorem GenuineReplacementsKeepUpgradeChainLiveAcrossCrossings :
    Properties.GenuineReplacementsKeepUpgradeChainLiveAcrossCrossings := by
  intro X s s' ls hf hI hrep h ht hgen
  have hQ : ∀ c op c', (CtmInv X.W c ∧ SlotsReport X.W c) →
      (∀ e r, op = .replace e r → (X.W.tr r).old = X.W.relVersion (X.W.tr r).fromRel) →
      CStep X.W c op c' → (CtmInv X.W c' ∧ SlotsReport X.W c') :=
    fun _ _ _ hc hg hs => ⟨step_inv hc.1 hs, cstep_slotsReport hc.1 hc.2 hg hs⟩
  obtain ⟨_, hrep'⟩ := lrun_ctm hQ hf h ht hgen ⟨hI, hrep⟩
  refine ⟨hrep', fun id s'' => ⟨?_, ?_⟩⟩
  · rintro ⟨t, h'⟩
    cases h' with
    | @upgradeChain _ _ c _ _ _ hc _ hstep => exact ⟨_, UStep.adminUpgrade hc rfl hstep⟩
  · rintro ⟨old, h'⟩
    cases h' with
    | @adminUpgrade _ _ c _ hc _ hstep =>
      exact ⟨_, upgradeChain_of_transition hc (hrep' _ (transition_facts hc hstep).1) hstep⟩

/-! ## The countermodel -/

/-- The bootstrap witness system satisfies `SysInv`. -/
lemma wBootSys_inv : SysInv wWorld wBootSys := by
  refine BootstrapSystemSatisfiesInvariant wWorld 0 100 _ (by decide) (by decide) ?_
  intro id c h
  rcases upd_chain h with ⟨_, rfl⟩ | ⟨_, h'⟩
  · exact le_rfl
  · simp at h'

theorem ChainSideCrossingBreaksTameHeadline : Properties.ChainSideCrossingBreaksTameHeadline := by
  have hrecut : CStep wWorld wBootSys.ctm (.legacyRecut 0) _ :=
    CStep.legacyRecut (s := wBootSys.ctm) (v := 0) rfl (by decide)
  have hsys1 : Step wWorld wBootSys (.ctm (.legacyRecut 0)) _ := Step.ctm hrecut
  have h1 : LStep wX wLX0 (.u (.x (.forward [.sys (.ctm (.legacyRecut 0))]))) _ :=
    LStep.u (UStep.x (fun h => h) (XStep.forward (FRun.cons (FStep.sys hsys1) FRun.nil)))
  have hI1 := step_sysInv wBootSys_inv hsys1 (by simp [Label.isArbitrary])
  have h2 := LStep.cross (X := wX) (s := { wLX0 with sys := { wBootSys with
      ctm := { wBootSys.ctm with legacy := upd wBootSys.ctm.legacy 0 LegacyCut.opaque } } })
    (CrossStep.mk (id := 5) (v := 1) (ρ := bgExtra) (c := ⟨0, upd emptyRouting 7 (some (77, true))⟩)
      rfl (by decide) (by decide))
  have hrun : LRun wX wLX0 wRecutRun _ := LRun.cons h1 (LRun.cons h2 LRun.nil)
  have hne : bgExtra ≠ rowsRouting (wWorld.relRows 100) := fun h => absurd (congrFun h 9) (by decide)
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wBootSys_inv, ?_, ?_, _, _, h1, hI1, h2, hrun,
    ⟨_, rfl, rfl, by decide, hne⟩, ?_, ?_, ?_, ?_⟩
  · intro l hl
    simp only [wRecutRun, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · intro c hc
      rw [List.mem_singleton.mp hc]
      simp [FCall.Tame, Label.isArbitrary]
    · trivial
  · intro l hl
    simp only [wRecutRun, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · intro c hc
      rw [List.mem_singleton.mp hc]
      trivial
    · trivial
  · intro hI
    exact hne ((hI.2 5 _ rfl).2 (by decide))
  · intro h
    exact h [.ctm (.legacyRecut 0)] (.arbitraryCut 5 1 bgExtra) [] rfl rfl (by simp) trivial
  · rintro ⟨xs, hx, htx⟩
    exact hne (TameRunKeepsChainsOnTheirRelease wX wLX0 _ xs ProxyUpgradeCurrent.wConfig_frames
      wBootSys_inv hx htx 5 _ rfl (by decide)).2
  · rintro ⟨us, hu, htu⟩
    exact hne (RefinedTameRunKeepsChainsOnTheirRelease wX wLX0 _ us
      ProxyUpgradeCurrent.wConfig_frames wBootSys_inv hu htu 5 _ rfl (by decide)).2

/-! ## The witness -/

/-- `Enabledness`'s lagging bootstrap system satisfies `SysInv`. -/
lemma wLagSys_inv : SysInv wWorld wLagSys := by
  refine BootstrapSystemSatisfiesInvariant wWorld 1 200 _ (by decide) (by decide) ?_
  intro id c h
  rcases upd_chain h with ⟨_, rfl⟩ | ⟨_, h'⟩
  · exact le_rfl
  · rcases upd_chain h' with ⟨_, rfl⟩ | ⟨_, h''⟩
    · exact Nat.zero_le _
    · simp at h''

theorem LegacyCatchUpWitness : Properties.LegacyCatchUpWitness := by
  have hcross : CrossStep wLagSys 5 1 wPreRoute (landAt wLagSys 5 1 wPreRoute) :=
    CrossStep.mk (c := ⟨0, upd emptyRouting 7 (some (77, true))⟩) rfl (by decide) (by decide)
  have h1 : LStep wX wLagX0 (.cross 5 1 wPreRoute) { wLagX0 with sys := landAt wLagSys 5 1 wPreRoute } :=
    LStep.cross hcross
  have hok1 : (LLabel.cross 5 1 wPreRoute).LandsOk wX.W wLagX0.sys :=
    ⟨by decide, fun h => absurd (by decide) h⟩
  have hreset : Step wWorld (landAt wLagSys 5 1 wPreRoute) (.bootstrapReset 5) _ :=
    Step.bootstrapReset (c := ⟨1, wPreRoute⟩) (R := 200) rfl (by decide)
      (addAll_empty_eq xNodup200) (by decide)
  have h2 : LStep wX { wLagX0 with sys := landAt wLagSys 5 1 wPreRoute }
      (.u (.x (.env (.bootstrapReset 5)))) _ :=
    LStep.u (UStep.x (fun h => h) (XStep.env trivial hreset))
  have hrun : LRunOk wX wLagX0 wCatchUpRun _ := LRunOk.cons h1 hok1 (LRunOk.cons h2 trivial LRunOk.nil)
  have htame : ∀ l ∈ wCatchUpRun, l.ExecTame wX := by
    intro l hl
    simp only [wCatchUpRun, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> trivial
  refine ⟨wLagSys_inv, by decide, ?_, ?_, htame, _, hrun,
    (LandingRunPreservesSysInv wX wLagX0 _ _ ProxyUpgradeCurrent.wConfig_frames wLagSys_inv hrun
      htame).1, _, rfl, by decide, by decide, rfl⟩
  · rintro ⟨s', h⟩
    cases h with
    | transition _ hut _ _ _ => exact hut rfl
  · rintro ⟨s', h⟩
    cases h with
    | @bootstrapReset _ c0 R ρ hc0 hleg _ _ =>
      have hcc : c0 = ⟨0, upd emptyRouting 7 (some (77, true))⟩ :=
        (Option.some.inj (hc0.symm.trans rfl) :)
      subst hcc
      have h0 : LegacyCut.opaque = LegacyCut.bootstrap R := hleg
      cases h0

end Contracts.ChainTypeManager.LegacyCrossing
