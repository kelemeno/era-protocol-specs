import EraSpec.Contracts.ChainTypeManager.Properties.ChainLocalExecutor
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocal
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorForward

/-!
# Proofs: the per-chain headline across the CTM executor's transactions

An executor transaction that keeps the CTM's code relates its states' routing systems by a
`ChainRouting` run of its routing steps (`xstep_sysRun`): an infrastructure transition naming
no CTM-proxy row leaves the CTM alone by the row library's frame
(`ProxyUpgradeCurrent.UnmovedProxiesFrame`), and a `forward` is its CTM calls in order
(`frun_sysRun`). The per-chain headline then transfers from `ChainRunsItsVersionsRelease`.
-/

namespace Contracts.ChainTypeManager

/-! ## Executor runs as routing runs -/

private lemma run_append' {W : World} {s s₁ s₂ : Sys} {xs ys : List Label}
    (h₁ : Run W s xs s₁) (h₂ : Run W s₁ ys s₂) : Run W s (xs ++ ys) s₂ := by
  induction h₁ with
  | nil => exact h₂
  | cons hs _ ih => exact Run.cons hs (ih h₂)

private lemma frun_sysRun {X : XConfig} {s s' : XState} {cs : List FCall}
    (h : FRun X s cs s') (hk : ∀ c ∈ cs, c.KeepsCtmCode) :
    Run X.W s.sys (cs.filterMap FCall.sys?) s'.sys := by
  induction h with
  | nil => exact Run.nil
  | cons hstep _ ih =>
    have ih' := ih (fun c hc => hk c (List.mem_cons_of_mem _ hc))
    cases hstep with
    | sys hs => exact Run.cons hs ih'
    | upgradeProxy _ _ _ => exact ih'
    | swapCtm _ _ => exact (hk _ List.mem_cons_self).elim

private lemma xstep_sysRun {X : XConfig} {s s' : XState} {x : XLabel}
    (hf : ProxyUpgradeCurrent.ReinitFrames X.rc) (h : XStep X s x s') (hk : x.KeepsCtmCode X) :
    Run X.W s.sys x.sysLabels s'.sys := by
  cases h with
  | @infra T J c' happ hc =>
    have hk' : ∀ r ∈ T.rows, r.proxy ≠ X.ctmProxy := hk
    have hJ : J X.ctmProxy = s.impl X.ctmProxy :=
      ProxyUpgradeCurrent.UnmovedProxiesFrame X.rc s.impl J T.rows hf happ.2.2 X.ctmProxy hk'
    have hc' := hc hJ
    subst hc'
    exact Run.nil
  | commit hs _ _ => exact Run.cons hs Run.nil
  | upgradeChain hs => exact Run.cons hs Run.nil
  | forward hr => exact frun_sysRun hr hk
  | env _ hs => exact Run.cons hs Run.nil

/-! ## Tame runs -/

private lemma tame_keeps {X : XConfig} {x : XLabel} (ht : x.Tame X) : x.KeepsCtmCode X := by
  cases x with
  | infra T => exact ht
  | forward calls =>
    intro c hc
    have htc : c.Tame := ht c hc
    cases c with
    | swapCtm _ _ => exact htc.elim
    | _ => trivial
  | _ => trivial

private lemma xstep_sysLabels_tame {X : XConfig} {s s' : XState} {x : XLabel}
    (h : XStep X s x s') (ht : x.Tame X) : ∀ l ∈ x.sysLabels, ¬ l.isArbitrary := by
  cases h with
  | infra _ _ => intro l hl; simp [XLabel.sysLabels] at hl
  | commit _ _ _ | upgradeChain _ =>
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
    | sys l' => cases hcl; exact htc
    | _ => simp [FCall.sys?] at hcl
  | env he _ =>
    intro l hl
    simp only [XLabel.sysLabels, List.mem_singleton] at hl
    subst hl
    exact env_not_arbitrary he

private lemma xrun_sysLabels_tame {X : XConfig} {s s' : XState} {xs : List XLabel}
    (h : XRun X s xs s') (ht : ∀ x ∈ xs, x.Tame X) :
    ∀ l ∈ xs.flatMap XLabel.sysLabels, ¬ l.isArbitrary := by
  induction h with
  | nil => intro l hl; simp at hl
  | cons hx _ ih =>
    intro l hl
    rw [List.flatMap_cons, List.mem_append] at hl
    rcases hl with hl | hl
    · exact xstep_sysLabels_tame hx (ht _ List.mem_cons_self) l hl
    · exact ih (fun x hx' => ht x (List.mem_cons_of_mem _ hx')) l hl

/-! ## Certificates -/

theorem ExecutorRunIsARoutingRun : Properties.ExecutorRunIsARoutingRun := by
  intro X s s' xs hf h hk
  induction h with
  | nil => exact Run.nil
  | cons hx _ ih =>
    rw [List.flatMap_cons]
    exact run_append' (xstep_sysRun hf hx (hk _ List.mem_cons_self))
      (ih (fun x hx' => hk x (List.mem_cons_of_mem _ hx')))

theorem ChainRunsItsVersionsReleaseAcrossExecutorRuns :
    Properties.ChainRunsItsVersionsReleaseAcrossExecutorRuns := by
  intro X s s' xs id hf hC hok h hk hlast
  exact ChainRunsItsVersionsRelease X.W s.sys s'.sys _ id hC hok
    (ExecutorRunIsARoutingRun X s s' xs hf h hk) hlast

theorem TamePremiseImpliesChainLocal : Properties.TamePremiseImpliesChainLocal := by
  intro X s s' xs h ht
  exact ⟨fun x hx => tame_keeps (ht x hx),
    fun id => GlobalPremiseImpliesChainLocal _ (xrun_sysLabels_tame h ht) id⟩

/-! ## Witness -/

theorem ExecutorChainLocalWitness : Properties.ExecutorChainLocalWitness := by
  have hc : CStep wWorld (initState wWorld 100) (.commit 300) _ :=
    CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨p1, p2⟩ := ExecutorPostcheckPasses _ _ _ _ hc
  have hC : CtmInv wWorld _ := step_inv (InitSatisfiesInvariant wWorld 100 (by decide)) hc
  have hstuck : XRun wX wX0 wExecStuckRun _ :=
    XRun.cons (XStep.env (l := .genesis 0) trivial
        (Step.genesis (id := 0) rfl (addAll_empty_eq xNodup100)))
    (XRun.cons (XStep.env (l := .genesis 1) trivial
        (Step.genesis (id := 1) rfl (addAll_empty_eq xNodup100)))
    (XRun.cons (XStep.forward (FRun.cons (FStep.sys (Step.arbitraryCut (id := 0) 1 bgExtra rfl))
        (FRun.cons (FStep.sys (Step.arbitraryCut (id := 1) 1 bgExtra rfl)) FRun.nil)))
    (XRun.cons (XStep.commit (Step.ctm hc) p1 p2) XRun.nil)))
  have hlast0 : LastWriteNotBreakGlass 0
      ((wExecStuckRun ++ wExecRepairRun).flatMap XLabel.sysLabels) :=
    lastWriteNotBreakGlass_snoc (l := .transition 0) rfl (fun h => h)
      [.genesis 0, .genesis 1, .arbitraryCut 0 1 bgExtra, .arbitraryCut 1 1 bgExtra,
        .ctm (.commit 300), .arbitraryCut 0 1 (rowsRouting (wRows 100))]
  have hlast1 : ¬ LastWriteNotBreakGlass 1
      ((wExecStuckRun ++ wExecRepairRun).flatMap XLabel.sysLabels) := by
    intro h
    exact h [.genesis 0, .genesis 1, .arbitraryCut 0 1 bgExtra] (.arbitraryCut 1 1 bgExtra)
      [.ctm (.commit 300), .arbitraryCut 0 1 (rowsRouting (wRows 100)), .transition 0] rfl rfl
      (by simp [Label.writesChain]) trivial
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wX0_inv, ?_,
    ⟨.forward [.sys (.arbitraryCut 0 1 bgExtra), .sys (.arbitraryCut 1 1 bgExtra)],
      by simp [wExecStuckRun], fun h => h _ List.mem_cons_self trivial⟩,
    hlast0, hlast1, _, _, hstuck, ?_,
    XRun.cons (XStep.forward (FRun.cons
        (FStep.sys (Step.arbitraryCut (id := 0) 1 (rowsRouting (wRows 100)) rfl)) FRun.nil))
      (XRun.cons (XStep.upgradeChain (Step.transition (id := 0) rfl (by decide) rfl
          (applyDerived_rows_eq xNodup100 xNodup200) (by decide))) XRun.nil),
    ⟨_, rfl, by decide, rfl⟩, ⟨_, rfl, rfl, by decide, ?_⟩⟩
  · simp [wExecStuckRun, wExecRepairRun, XLabel.KeepsCtmCode, FCall.KeepsCtmCode]
  · rintro ⟨s'', h⟩
    cases h with
    | upgradeChain hs =>
      exact DriftBlocksTransition wWorld _ 0 ⟨1, bgExtra⟩ hC rfl
        (fun h => absurd (congrFun h 9) (by decide)) ⟨_, hs⟩
  · exact fun h => absurd (congrFun h 9) (by decide)

theorem CtmSwapBreaksChainLocal : Properties.CtmSwapBreaksChainLocal := by
  have hc : CStep wWorld (initState wWorld 100) (.commit 300) _ :=
    CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨p1, p2⟩ := ExecutorPostcheckPasses _ _ _ _ hc
  have hrun := XRun.cons (X := wX) (s := wX0)
    (XStep.env (l := .genesis 0) trivial (Step.genesis (id := 0) rfl (addAll_empty_eq xNodup100)))
    (XRun.cons (XStep.commit (Step.ctm hc) p1 p2)
      (XRun.cons (XStep.upgradeChain (Step.transition (id := 0) rfl (by decide) rfl
          (applyDerived_rows_eq xNodup100 xNodup200) (by decide))) XRun.nil))
  refine ⟨ProxyUpgradeCurrent.wConfig_frames, wX0_inv, ?_, fun h => h _ List.mem_cons_self,
    lastWriteNotBreakGlass_snoc (l := .transition 0) rfl (fun h => h)
      [.genesis 0, .ctm (.commit 300)],
    _, _, hrun,
    XStep.forward (FRun.cons (FStep.swapCtm (c' := initState wWorld 100) rfl trivial) FRun.nil),
    _, rfl, by decide⟩
  simp [XLabel.KeepsCtmCode]

end Contracts.ChainTypeManager
