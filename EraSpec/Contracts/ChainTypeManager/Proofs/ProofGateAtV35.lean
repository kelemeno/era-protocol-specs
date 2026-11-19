import EraSpec.Contracts.ChainTypeManager.Properties.ProofGateAtV35
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocal
import EraSpec.Contracts.ChainTypeManager.Proofs.Enabledness
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorForward

/-!
# Proofs: the routing system at `draft/v0.35.0`, with the second-proof-system gate

A v35 step is a `ChainRouting` step plus a `ProofEffect`, and the only condition a
`ProofEffect` adds is `GateHolds` (`proofEffect_gate`, `gate_proofEffect`). So the routing results are
the `ChainRouting` and `ChainLocal` theorems applied to the run's projection (`RunIsARun`). The enabledness
results are `Enabledness`'s plus the gate. The invariant `ProofInv` is an induction in
which only `permanentlyRequireSecondProofSystem` needs `DisablingNeverEnablesMultiProof`. The
countermodels are concrete runs on the `ChainRouting` witness world.
-/

namespace Contracts.ChainTypeManager.ProofGateAtV35

open Contracts.ChainTypeManager

/-! ## The gate a step passes -/

/-- The condition a `ProofEffect` imposes is `GateHolds`. -/
lemma proofEffect_gate {W : World} {P : ProofWorld} {s : Sys35} {l : Label}
    {pr' : ChainId → ProofState} (h : ProofEffect W P s.sys s.proof l pr') : GateHolds W P s l := by
  cases h with
  | ctm => trivial
  | genesis => trivial
  | migrateIn => trivial
  | @transition id c hc hg =>
      intro c' hc' hreq
      rw [hc] at hc'
      cases hc'
      exact hg hreq
  | @bootstrapReset id c R hc hleg hg =>
      intro c' R' hc' hleg' hreq
      rw [hc] at hc'
      cases hc'
      rw [hleg] at hleg'
      cases hleg'
      exact hg hreq
  | arbitraryCut _ => trivial

/-- Every `ChainRouting` step whose gate holds has a `ProofEffect`. A break-glass cut can always
leave the requirement off. -/
lemma gate_proofEffect {W : World} {P : ProofWorld} {s : Sys35} {l : Label} {sys' : Sys}
    (hs : Step W s.sys l sys') (hg : GateHolds W P s l) :
    ∃ pr', ProofEffect W P s.sys s.proof l pr' := by
  cases hs with
  | ctm _ => exact ⟨_, ProofEffect.ctm⟩
  | genesis _ _ => exact ⟨_, ProofEffect.genesis⟩
  | migrateIn _ _ _ _ => exact ⟨_, ProofEffect.migrateIn⟩
  | @transition id c ρ hc _ _ _ _ => exact ⟨_, ProofEffect.transition hc (hg c hc)⟩
  | @bootstrapReset id c R ρ hc hleg _ _ =>
      exact ⟨_, ProofEffect.bootstrapReset hc hleg (hg c R hc hleg)⟩
  | arbitraryCut _ _ _ =>
      exact ⟨_, ProofEffect.arbitraryCut (p := ⟨false, 0, 0⟩) (fun h => absurd h (by decide))⟩

theorem StepIsTheUngatedStepPlusTheGate : Properties.StepIsTheUngatedStepPlusTheGate := by
  intro W P s l sys'
  constructor
  · rintro ⟨pr', h⟩
    cases h with
    | routing hs he => exact ⟨hs, proofEffect_gate he⟩
  · rintro ⟨hs, hg⟩
    obtain ⟨pr', he⟩ := gate_proofEffect hs hg
    exact ⟨pr', Step35.routing hs he⟩

/-! ## The projection and the lift -/

private lemma run_append {W : World} {s s' s'' : Sys} {l1 l2 : List Label}
    (h1 : Run W s l1 s') (h2 : Run W s' l2 s'') : Run W s (l1 ++ l2) s'' := by
  induction h1 with
  | nil => exact h2
  | cons hs _ ih => exact Run.cons hs (ih h2)

/-- One v35 step is its routing steps. -/
lemma step35_routing {W : World} {P : ProofWorld} {s s' : Sys35} {l : Label35}
    (h : Step35 W P s l s') : Run W s.sys l.routingSteps s'.sys := by
  cases h with
  | routing hs _ => exact Run.cons hs Run.nil
  | requireSecondProofSystem _ _ _ => exact Run.nil
  | setProofSystems _ => exact Run.nil

theorem RunIsARun : Properties.RunIsARun := by
  intro W P s s' ls h
  induction h with
  | nil => exact Run.nil
  | cons hs _ ih =>
      rw [List.flatMap_cons]
      exact run_append (step35_routing hs) ih

/-- A run without break-glass cuts projects to a routing run without them. -/
lemma routing_no_arbitrary {ls : List Label35} (hl : ∀ l ∈ ls, ¬ l.isArbitrary) :
    ∀ l ∈ ls.flatMap Label35.routingSteps, ¬ l.isArbitrary := by
  intro l hm
  obtain ⟨x, hx, hlx⟩ := List.mem_flatMap.mp hm
  cases x with
  | routing l' =>
      simp only [Label35.routingSteps, List.mem_singleton] at hlx
      subst hlx
      exact hl _ hx
  | requireSecondProofSystem _ => simp [Label35.routingSteps] at hlx
  | setProofSystems _ _ => simp [Label35.routingSteps] at hlx

/-- With the requirement off everywhere, every `ChainRouting` step has a `ProofEffect` that keeps
it off. -/
lemma lift_proofEffect {W : World} {P : ProofWorld} {s : Sys} {l : Label} {sys' : Sys}
    {pr : ChainId → ProofState} (hs : Step W s l sys') (hpr : ∀ id, (pr id).required = false) :
    ∃ pr', ProofEffect W P s pr l pr' ∧ ∀ id, (pr' id).required = false := by
  have hupd : ∀ (id : ChainId) (p : ProofState), p.required = false →
      ∀ id', (upd pr id p id').required = false := by
    intro id p hp id'
    by_cases h : id' = id
    · subst h
      simp [hp]
    · rw [upd_ne _ _ h]
      exact hpr id'
  cases hs with
  | ctm _ => exact ⟨pr, ProofEffect.ctm, hpr⟩
  | genesis _ _ => exact ⟨_, ProofEffect.genesis, hupd _ _ rfl⟩
  | migrateIn _ _ _ _ => exact ⟨_, ProofEffect.migrateIn, hupd _ _ rfl⟩
  | @transition id c ρ hc _ _ _ _ =>
      refine ⟨_, ProofEffect.transition hc ?_, hupd _ _ (hpr id)⟩
      intro h
      exact absurd ((hpr id).symm.trans h) (by decide)
  | @bootstrapReset id c R ρ hc hleg _ _ =>
      refine ⟨_, ProofEffect.bootstrapReset hc hleg ?_, hupd _ _ (hpr id)⟩
      intro h
      exact absurd ((hpr id).symm.trans h) (by decide)
  | @arbitraryCut id c v ρ _ =>
      refine ⟨_, ProofEffect.arbitraryCut (p := pr id) ?_, hupd _ _ (hpr id)⟩
      intro h
      exact absurd ((hpr id).symm.trans h) (by decide)

theorem UngatedRunsAreRunsWithoutTheRequirement :
    Properties.UngatedRunsAreRunsWithoutTheRequirement := by
  intro W P s s' ls pr h hpr
  induction h generalizing pr with
  | nil => exact ⟨pr, Run35.nil, hpr⟩
  | cons hs _ ih =>
      obtain ⟨pr1, he, hpr1⟩ := lift_proofEffect (P := P) hs hpr
      obtain ⟨pr2, hrun, hpr2⟩ := ih pr1 hpr1
      exact ⟨pr2, Run35.cons (Step35.routing hs he) hrun, hpr2⟩

/-! ## The routing headline at v35 -/

theorem ChainsRunTheirVersionsRelease : Properties.ChainsRunTheirVersionsRelease := by
  intro W P s s' ls hI h hl
  exact Contracts.ChainTypeManager.ChainsRunTheirVersionsRelease W s.sys s'.sys _ hI
    (RunIsARun W P s s' ls h) (routing_no_arbitrary hl)

theorem FreshChainsRunTheirVersionsRelease : Properties.FreshChainsRunTheirVersionsRelease := by
  intro W P R pr s' ls hR h hl
  exact Contracts.ChainTypeManager.FreshChainsRunTheirVersionsRelease W R s'.sys _ hR
    (RunIsARun W P _ s' ls h) (routing_no_arbitrary hl)

theorem ChainRunsItsVersionsRelease : Properties.ChainRunsItsVersionsRelease := by
  intro W P s s' ls id hC hok h hlast
  exact Contracts.ChainTypeManager.ChainRunsItsVersionsRelease W s.sys s'.sys _ id hC hok
    (RunIsARun W P s s' ls h) hlast

/-! ## Enabledness at v35 -/

theorem TransitionEnabledIff : Properties.TransitionEnabledIff := by
  intro W P s id c hC hc
  have e561 := Contracts.ChainTypeManager.TransitionEnabledIff W s.sys id c hC hc
  constructor
  · rintro ⟨⟨sys', pr'⟩, h⟩
    obtain ⟨hs, hg⟩ := (StepIsTheUngatedStepPlusTheGate W P s _ sys').mp ⟨pr', h⟩
    exact ⟨e561.mp ⟨sys', hs⟩, hg c hc⟩
  · rintro ⟨hcond, hgate⟩
    obtain ⟨sys', hs⟩ := e561.mpr hcond
    have hg : GateHolds W P s (.transition id) := by
      intro c' hc' hreq
      rw [hc] at hc'
      cases hc'
      exact hgate hreq
    obtain ⟨pr', h⟩ := (StepIsTheUngatedStepPlusTheGate W P s _ sys').mpr ⟨hs, hg⟩
    exact ⟨_, h⟩

theorem UpgradesStayEnabled : Properties.UpgradesStayEnabled := by
  intro W P s s' ls hI hW h hl id c hc hut hwf hgate
  exact Step35.routing
    (Contracts.ChainTypeManager.UpgradesStayEnabled W s.sys s'.sys _ hI hW
      (RunIsARun W P s s' ls h) (routing_no_arbitrary hl) id c hc hut hwf)
    (ProofEffect.transition hc hgate)

theorem ValidatedRunsKeepEverythingEnabled : Properties.ValidatedRunsKeepEverythingEnabled := by
  intro W P s s' ls hI hR h hl hwf
  obtain ⟨h1, h2⟩ := Contracts.ChainTypeManager.ValidatedRunsKeepEverythingEnabled W s.sys s'.sys
    _ hI hR (RunIsARun W P s s' ls h) (routing_no_arbitrary hl) hwf
  refine ⟨fun id c hc hut hgate => ⟨_, Step35.routing (h1 id c hc hut)
    (ProofEffect.transition hc hgate)⟩, fun id hn => ?_⟩
  obtain ⟨hg, hm⟩ := h2 id hn
  exact ⟨⟨_, Step35.routing hg ProofEffect.genesis⟩, ⟨_, Step35.routing hm ProofEffect.migrateIn⟩⟩

/-! ## What #2628 guarantees -/

/-- A routing step leaves the chains it does not write alone. -/
private lemma step_chains_frame {W : World} {s s' : Sys} {l : Label} {id : ChainId}
    (h : Step W s l s') (hw : ¬ l.writesChain id) : s'.chains id = s.chains id := by
  cases h with
  | ctm _ => rfl
  | @genesis id' _ _ _ => exact upd_ne _ _ (fun e => hw e.symm)
  | @migrateIn id' _ _ _ _ _ => exact upd_ne _ _ (fun e => hw e.symm)
  | @transition id' _ _ _ _ _ _ _ => exact upd_ne _ _ (fun e => hw e.symm)
  | @bootstrapReset id' _ _ _ _ _ _ _ => exact upd_ne _ _ (fun e => hw e.symm)
  | @arbitraryCut id' _ _ _ _ => exact upd_ne _ _ (fun e => hw e.symm)

/-- A routing step never unregisters a chain. -/
private lemma step_chains_some {W : World} {s s' : Sys} {l : Label} {id : ChainId} {c : Chain}
    (h : Step W s l s') (hc : s.chains id = some c) : ∃ c', s'.chains id = some c' := by
  by_cases hw : l.writesChain id
  · cases h with
    | ctm _ => exact absurd hw (fun h => h)
    | @genesis id' _ _ _ =>
        have e : id = id' := hw.symm
        subst e
        exact ⟨_, upd_same _ _ _⟩
    | @migrateIn id' _ _ _ _ _ =>
        have e : id = id' := hw.symm
        subst e
        exact ⟨_, upd_same _ _ _⟩
    | @transition id' _ _ _ _ _ _ _ =>
        have e : id = id' := hw.symm
        subst e
        exact ⟨_, upd_same _ _ _⟩
    | @bootstrapReset id' _ _ _ _ _ _ _ =>
        have e : id = id' := hw.symm
        subst e
        exact ⟨_, upd_same _ _ _⟩
    | @arbitraryCut id' _ _ _ _ =>
        have e : id = id' := hw.symm
        subst e
        exact ⟨_, upd_same _ _ _⟩
  · exact ⟨c, (step_chains_frame h hw).trans hc⟩

/-- A v35 step never unregisters a chain. -/
lemma step35_chains_some {W : World} {P : ProofWorld} {s s' : Sys35} {l : Label35} {id : ChainId}
    {c : Chain} (h : Step35 W P s l s') (hc : s.sys.chains id = some c) :
    ∃ c', s'.sys.chains id = some c' := by
  cases h with
  | routing hs _ => exact step_chains_some hs hc
  | requireSecondProofSystem _ _ _ => exact ⟨c, hc⟩
  | setProofSystems _ => exact ⟨c, hc⟩

/-- A `ProofEffect` leaves the chains its step does not write alone. -/
private lemma effect_frame {W : World} {P : ProofWorld} {s : Sys} {pr pr' : ChainId → ProofState}
    {l : Label} {id : ChainId} (h : ProofEffect W P s pr l pr') (hw : ¬ l.writesChain id) :
    pr' id = pr id := by
  cases h with
  | ctm => rfl
  | @genesis id' => exact upd_ne _ _ (fun e => hw e.symm)
  | @migrateIn id' => exact upd_ne _ _ (fun e => hw e.symm)
  | @transition id' _ _ _ => exact upd_ne _ _ (fun e => hw e.symm)
  | @bootstrapReset id' _ _ _ _ _ => exact upd_ne _ _ (fun e => hw e.symm)
  | @arbitraryCut id' _ _ _ _ => exact upd_ne _ _ (fun e => hw e.symm)

/-- The chain a `ProofEffect`'s step writes passes the cut check afterwards. -/
private lemma effect_gate_at {W : World} {P : ProofWorld} {s : Sys} {pr pr' : ChainId → ProofState}
    {l : Label} {id : ChainId} (h : ProofEffect W P s pr l pr') (hw : l.writesChain id) :
    ProofGate P (pr' id) := by
  cases h with
  | ctm => exact absurd hw (fun h => h)
  | @genesis id' =>
      have e : id = id' := hw.symm
      subst e
      intro hr
      simp [ProofState.fresh] at hr
  | @migrateIn id' =>
      have e : id = id' := hw.symm
      subst e
      intro hr
      simp [ProofState.fresh] at hr
  | @transition id' _ _ hg =>
      have e : id = id' := hw.symm
      subst e
      rw [upd_same]
      exact hg
  | @bootstrapReset id' _ _ _ _ hg =>
      have e : id = id' := hw.symm
      subst e
      rw [upd_same]
      exact hg
  | @arbitraryCut id' _ _ _ hg =>
      have e : id = id' := hw.symm
      subst e
      rw [upd_same]
      exact hg

private lemma step_proofInv {W : World} {P : ProofWorld} {s s' : Sys35} {l : Label35}
    (hD : DisablingNeverEnablesMultiProof P) (hI : ProofInv P s) (h : Step35 W P s l s') :
    ProofInv P s' := by
  cases h with
  | @routing l sys' pr' hs he =>
      intro id c hc
      dsimp only at hc ⊢
      by_cases hw : l.writesChain id
      · exact effect_gate_at he hw
      · rw [effect_frame he hw]
        exact hI id c ((step_chains_frame hs hw).symm.trans hc)
  | @requireSecondProofSystem id' c' hc' _ hm =>
      intro id c hc
      dsimp only at hc ⊢
      by_cases e : id = id'
      · subst e
        rw [upd_same]
        intro _
        exact hD _ _ hm
      · rw [upd_ne _ _ e]
        exact hI id c hc
  | @setProofSystems id' c' m hc' =>
      intro id c hc
      dsimp only at hc ⊢
      by_cases e : id = id'
      · subst e
        rw [upd_same]
        exact hI id c' hc'
      · rw [upd_ne _ _ e]
        exact hI id c hc

theorem RequiringChainsKeepAMultiProofVerifier :
    Properties.RequiringChainsKeepAMultiProofVerifier := by
  intro W P s s' ls hD hI h
  induction h with
  | nil => exact hI
  | cons hs _ ih => exact ih (step_proofInv hD hI hs)

theorem RequirementWriters : Properties.RequirementWriters := by
  intro W P s s' l id c h hc hne
  cases h with
  | @routing l sys' pr' hs he =>
      dsimp only at hne
      by_cases hw : l.writesChain id
      · cases he with
        | ctm => exact absurd hw (fun h => h)
        | @genesis id' =>
            have e : id = id' := hw.symm
            subst e
            cases hs with
            | genesis hn _ => rw [hc] at hn; cases hn
        | @migrateIn id' =>
            have e : id = id' := hw.symm
            subst e
            cases hs with
            | migrateIn _ _ hn _ => rw [hc] at hn; cases hn
        | @transition id' _ _ _ =>
            have e : id = id' := hw.symm
            subst e
            exact absurd (by simp [ProofState.install]) hne
        | @bootstrapReset id' _ _ _ _ _ =>
            have e : id = id' := hw.symm
            subst e
            exact absurd (by simp [ProofState.install]) hne
        | @arbitraryCut id' v ρ _ _ =>
            have e : id = id' := hw.symm
            subst e
            exact Or.inr ⟨v, ρ, rfl⟩
      · exact absurd (by rw [effect_frame he hw]) hne
  | @requireSecondProofSystem id' c' _ _ _ =>
      dsimp only at hne ⊢
      by_cases e : id = id'
      · subst e
        exact Or.inl ⟨rfl, by simp⟩
      · exact absurd (by rw [upd_ne _ _ e]) hne
  | @setProofSystems id' c' m _ =>
      dsimp only at hne
      by_cases e : id = id'
      · subst e
        exact absurd (by simp) hne
      · exact absurd (by rw [upd_ne _ _ e]) hne

theorem RequirementIsPermanentWithoutBreakGlass :
    Properties.RequirementIsPermanentWithoutBreakGlass := by
  intro W P s s' ls id c h hc hreq hno
  induction h generalizing c with
  | nil => exact hreq
  | @cons s1 s2 s3 l ls hs _ ih =>
      have hreq2 : (s2.proof id).required = true := by
        by_contra hne
        rcases RequirementWriters W P s1 s2 l id c hs hc (by rw [hreq]; exact hne) with
          ⟨_, h2⟩ | ⟨v, ρ, hl⟩
        · exact hne h2
        · exact hno v ρ (by rw [hl]; exact List.mem_cons_self)
      obtain ⟨c2, hc2⟩ := step35_chains_some hs hc
      exact ih c2 hc2 hreq2 (fun v ρ hm => hno v ρ (List.mem_cons_of_mem _ hm))


/-! ## The witness states

`wGateSetup` from `wSys35`: chains `0` and `1` at version 1 on release `100`, chain `0` requiring
its second proof system with release `100`'s verifier, and `300` committed. -/

/-- The routing system after `wGateSetup`. -/
private def gSys : Sys :=
  ⟨⟨2, 200, upd (fun _ => 0) 1 300, fun _ => LegacyCut.none, upd (upd (fun _ => 0) 1 100) 2 200⟩,
    upd (upd (fun _ => none) 0 (some ⟨1, rowsRouting (wRows 100)⟩)) 1
      (some ⟨1, rowsRouting (wRows 100)⟩)⟩

/-- The proof-system fields after `wGateSetup`. -/
private def gProof (P : ProofWorld) : ChainId → ProofState :=
  upd (upd (upd (fun _ => ⟨false, 0, 0⟩) 0 ⟨false, P.relVerifier 100, 0⟩) 1
    ⟨false, P.relVerifier 100, 0⟩) 0 ⟨true, P.relVerifier 100, 0⟩

/-- The CTM's commit of `300` in the setup. -/
private lemma gCommit : CStep wWorld wSys0.ctm (.commit 300) gSys.ctm :=
  CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- `wGateSetup` reaches `⟨gSys, gProof P⟩` in every proof world whose release `100` ships a
verifier in multi-proof mode with nothing disabled. -/
private lemma gSetup_run (P : ProofWorld) (h : P.multi (P.relVerifier 100) 0 = true) :
    Run35 wWorld P wSys35 wGateSetup ⟨gSys, gProof P⟩ :=
  Run35.cons (Step35.routing (Step.genesis (s := wSys0) (id := 0) rfl (addAll_empty_eq xNodup100))
      ProofEffect.genesis)
    (Run35.cons (Step35.routing (Step.genesis (id := 1) rfl (addAll_empty_eq xNodup100))
        ProofEffect.genesis)
      (Run35.cons (Step35.requireSecondProofSystem (id := 0) (c := ⟨1, rowsRouting (wRows 100)⟩)
          rfl rfl h)
        (Run35.cons (Step35.routing (Step.ctm gCommit) ProofEffect.ctm) Run35.nil)))

private lemma gSys_chains {id : ChainId} {c : Chain} (h : gSys.chains id = some c) :
    (id = 0 ∨ id = 1) ∧ c = ⟨1, rowsRouting (wRows 100)⟩ := by
  simp only [gSys, upd] at h
  split_ifs at h with h1 h0
  · exact ⟨Or.inr h1, (Option.some.inj h).symm⟩
  · exact ⟨Or.inl h0, (Option.some.inj h).symm⟩

/-- Both chains' `ChainRouting` transitions across `300` after the setup. -/
private lemma gSys_transition (id : ChainId) (hid : id = 0 ∨ id = 1) :
    Step wWorld gSys (.transition id)
      { gSys with chains := upd gSys.chains id (some ⟨2, rowsRouting (wRows 200)⟩) } := by
  rcases hid with rfl | rfl
  · exact Step.transition (s := gSys) (id := 0) rfl (by decide) rfl
      (applyDerived_rows_eq xNodup100 xNodup200) (by decide)
  · exact Step.transition (s := gSys) (id := 1) rfl (by decide) rfl
      (applyDerived_rows_eq xNodup100 xNodup200) (by decide)

private lemma gSetup_noArb : ∀ l ∈ wGateSetup, ¬ l.isArbitrary := by
  intro l hl
  simp only [wGateSetup, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with h | h | h | h <;> subst h <;> exact fun h => h

/-! ## Countermodels and witnesses -/

theorem GateStrandsRequiringChain : Properties.GateStrandsRequiringChain := by
  have hrun := gSetup_run wProofPlonk rfl
  have hI0 : SysInv wWorld wSys0 := FreshSystemSatisfiesInvariant wWorld 100 (by decide)
  have hW0 : ChainsOnWfReleases wWorld wSys0 :=
    (StartingStatesMeetLivenessPremises wWorld 100).2.2.1
  refine ⟨⟨gSys, gProof wProofPlonk⟩, hrun, hI0, hW0, gSetup_noArb, ?_,
    ⟨⟨1, rowsRouting (wRows 100)⟩, rfl, rfl, rfl, rfl, xNodup200, rfl, ?_⟩, ?_, ?_⟩
  · intro id c hc hr
    obtain ⟨hid, _⟩ := gSys_chains hc
    rcases hid with rfl | rfl
    · rfl
    · exact absurd hr (by decide)
  · exact Contracts.ChainTypeManager.UpgradesStayEnabled wWorld wSys0 gSys _ hI0 hW0
      (RunIsARun wWorld wProofPlonk _ _ _ hrun) (routing_no_arbitrary gSetup_noArb) 0 _ rfl
      (by decide) xNodup200
  · rintro ⟨⟨sys', pr'⟩, h⟩
    obtain ⟨_, hg⟩ := (StepIsTheUngatedStepPlusTheGate wWorld wProofPlonk
      ⟨gSys, gProof wProofPlonk⟩ _ sys').mp ⟨pr', h⟩
    exact absurd (hg _ rfl rfl) (by decide)
  · exact ⟨_, Step35.routing (gSys_transition 1 (Or.inr rfl))
      (ProofEffect.transition (c := ⟨1, rowsRouting (wRows 100)⟩) rfl
        (fun h => absurd h (by decide)))⟩

/-- The routing system after the break-glass cut of `BreakGlassClearsTheRequirement`. -/
private def gBgSys : Sys :=
  ⟨gSys.ctm, upd gSys.chains 0 (some ⟨1, rowsRouting (wRows 100)⟩)⟩

/-- The routing system after chain `0` then crosses `300`. -/
private def gBgEndSys : Sys :=
  ⟨gSys.ctm, upd gBgSys.chains 0 (some ⟨2, rowsRouting (wRows 200)⟩)⟩

theorem BreakGlassClearsTheRequirement : Properties.BreakGlassClearsTheRequirement := by
  have hrun := gSetup_run wProofPlonk rfl
  -- the break-glass cut: same version and routing, requirement off, verifier `51` kept
  have hbg : Step35 wWorld wProofPlonk ⟨gSys, gProof wProofPlonk⟩
      (.routing (.arbitraryCut 0 1 (rowsRouting (wRows 100))))
      ⟨gBgSys, upd (gProof wProofPlonk) 0 ⟨false, 51, 0⟩⟩ :=
    Step35.routing (Step.arbitraryCut (s := gSys) (c := ⟨1, rowsRouting (wRows 100)⟩) 1 _ rfl)
      (ProofEffect.arbitraryCut (fun h => absurd h (by decide)))
  have hstep : Step wWorld gBgSys (.transition 0) gBgEndSys :=
    Step.transition (s := gBgSys) (id := 0) (c := ⟨1, rowsRouting (wRows 100)⟩) rfl (by decide) rfl
      (applyDerived_rows_eq xNodup100 xNodup200) (by decide)
  exact ⟨_, _, hrun, rfl, hbg, rfl, _,
    Step35.routing hstep (ProofEffect.transition (c := ⟨1, rowsRouting (wRows 100)⟩) rfl
      (fun h => absurd h (by decide))),
    ⟨_, rfl, rfl, rfl⟩, rfl⟩

theorem MaskPremiseNeeded : Properties.MaskPremiseNeeded := by
  refine ⟨fun h => absurd (h 54 ziskBit (by decide)) (by decide), fun id c hc => by
    simp [wSys35, wSys0] at hc, ?_⟩
  have hrun : Run35 wWorld wProofOdd wSys35 wZiskOffFirstRun
      ⟨⟨wSys0.ctm, upd (fun _ => none) 0 (some ⟨1, rowsRouting (wRows 100)⟩)⟩,
        upd (upd (upd (fun _ => ⟨false, 0, 0⟩) 0 ⟨false, 54, 0⟩) 0 ⟨false, 54, ziskBit⟩) 0
          ⟨true, 54, ziskBit⟩⟩ :=
    Run35.cons (Step35.routing (Step.genesis (s := wSys0) (id := 0) rfl
        (addAll_empty_eq xNodup100)) ProofEffect.genesis)
      (Run35.cons (Step35.setProofSystems (c := ⟨1, rowsRouting (wRows 100)⟩) rfl)
        (Run35.cons (Step35.requireSecondProofSystem (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl
          (by decide)) Run35.nil))
  refine ⟨_, hrun, rfl, fun h => ?_⟩
  exact absurd (h 0 ⟨1, rowsRouting (wRows 100)⟩ rfl rfl) (by decide)

theorem RequirementDoesNotPinTheCurrentProofMode :
    Properties.RequirementDoesNotPinTheCurrentProofMode := by
  have hrun : Run35 wWorld wProofMulti wSys35 wZiskOffRun
      ⟨⟨wSys0.ctm, upd (fun _ => none) 0 (some ⟨1, rowsRouting (wRows 100)⟩)⟩,
        upd (upd (upd (fun _ => ⟨false, 0, 0⟩) 0 ⟨false, 51, 0⟩) 0 ⟨true, 51, 0⟩) 0
          ⟨true, 51, ziskBit⟩⟩ :=
    Run35.cons (Step35.routing (Step.genesis (s := wSys0) (id := 0) rfl
        (addAll_empty_eq xNodup100)) ProofEffect.genesis)
      (Run35.cons (Step35.requireSecondProofSystem (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl
          (by decide))
        (Run35.cons (Step35.setProofSystems (c := ⟨1, rowsRouting (wRows 100)⟩) rfl) Run35.nil))
  refine ⟨_, hrun, rfl, fun id c hc hr => ?_, by decide, by decide⟩
  by_cases h0 : id = 0
  · subst h0
    decide
  · exfalso
    simp [upd, h0] at hc

/-- The routing system after `wGateSetup` and chain `0`'s transition. -/
private def gMidSys : Sys :=
  ⟨gSys.ctm, upd gSys.chains 0 (some ⟨2, rowsRouting (wRows 200)⟩)⟩

/-- The routing system after `wGateRun`. -/
private def gEndSys : Sys :=
  ⟨gSys.ctm, upd gMidSys.chains 1 (some ⟨2, rowsRouting (wRows 200)⟩)⟩

/-- The proof-system fields after `wGateRun` with `wProofMulti`. -/
private def gEndProof : ChainId → ProofState :=
  upd (upd (gProof wProofMulti) 0 ⟨true, 53, 0⟩) 1 ⟨false, 53, 0⟩

/-- Chain `0`'s transition after the setup, with `wProofMulti`: verifier `53` installed. -/
private lemma gT0_multi : Step35 wWorld wProofMulti ⟨gSys, gProof wProofMulti⟩
    (.routing (.transition 0)) ⟨gMidSys, upd (gProof wProofMulti) 0 ⟨true, 53, 0⟩⟩ :=
  Step35.routing (gSys_transition 0 (Or.inl rfl))
    (ProofEffect.transition (c := ⟨1, rowsRouting (wRows 100)⟩) rfl (fun _ => by decide))

/-- Chain `1`'s transition after that. -/
private lemma gT1_multi : Step35 wWorld wProofMulti
    ⟨gMidSys, upd (gProof wProofMulti) 0 ⟨true, 53, 0⟩⟩ (.routing (.transition 1))
    ⟨gEndSys, gEndProof⟩ :=
  Step35.routing (Step.transition (s := gMidSys) (id := 1) (c := ⟨1, rowsRouting (wRows 100)⟩)
      rfl (by decide) rfl (applyDerived_rows_eq xNodup100 xNodup200) (by decide))
    (ProofEffect.transition (c := ⟨1, rowsRouting (wRows 100)⟩) rfl
      (fun h => absurd h (by decide)))

private lemma gRun_multi : Run35 wWorld wProofMulti wSys35 wGateRun ⟨gEndSys, gEndProof⟩ := by
  have hsetup := gSetup_run wProofMulti rfl
  have ht0 := gT0_multi
  have ht1 := gT1_multi
  cases hsetup with
  | cons h1 r1 => cases r1 with
    | cons h2 r2 => cases r2 with
      | cons h3 r3 => cases r3 with
        | cons h4 r4 => cases r4 with
          | nil => exact Run35.cons h1 (Run35.cons h2 (Run35.cons h3 (Run35.cons h4
              (Run35.cons ht0 (Run35.cons ht1 Run35.nil)))))

theorem ProofGateWitness : Properties.ProofGateWitness := by
  have hI0 : SysInv wWorld wSys0 := FreshSystemSatisfiesInvariant wWorld 100 (by decide)
  have hL := StartingStatesMeetLivenessPremises wWorld 100
  refine ⟨hI0, hL.2.2.1, hL.1 xNodup100, fun id c hc => by simp [wSys35, wSys0] at hc,
    fun _ => rfl, fun v m h => ?_, _, gRun_multi, ?_, ?_, ?_, rfl, rfl, rfl, ?_⟩
  · simp only [wProofMulti, decide_eq_true_eq] at h ⊢
    exact ⟨h.1, trivial⟩
  · intro l hl
    simp only [wGateRun, wGateSetup, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hl
    rcases hl with h | h | h | h | h | h <;> subst h <;> exact fun h => h
  · intro l hl
    simp only [wGateRun, wGateSetup, List.cons_append, List.nil_append, List.flatMap_cons,
      Label35.routingSteps, List.flatMap_nil, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hl
    rcases hl with h | h | h | h | h <;> subst h
    all_goals first | trivial | exact xNodup200
  · intro id hid
    interval_cases id
    · exact ⟨_, rfl, rfl, rfl⟩
    · exact ⟨_, rfl, rfl, rfl⟩
  · intro id c hc hr
    by_cases h1 : id = 1
    · subst h1
      exact absurd hr (by decide)
    · by_cases h0 : id = 0
      · subst h0
        decide
      · exfalso
        simp [gEndSys, gMidSys, gSys, upd, h0, h1] at hc

/-- The routing labels of `wGateSetup` install only well-formed releases. -/
private lemma gSetup_installsWf :
    ∀ l ∈ wGateSetup.flatMap Label35.routingSteps, l.InstallsWf wWorld := by
  intro l hl
  simp only [wGateSetup, List.flatMap_cons, Label35.routingSteps, List.flatMap_nil,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hl
  rcases hl with h | h | h <;> subst h
  all_goals first | trivial | exact xNodup200

theorem RequiringChainCanCrossWitness : Properties.RequiringChainCanCrossWitness := by
  have hI0 : SysInv wWorld wSys0 := FreshSystemSatisfiesInvariant wWorld 100 (by decide)
  have hL := StartingStatesMeetLivenessPremises wWorld 100
  have hrun := gSetup_run wProofMulti rfl
  have hC : CtmInv wWorld gSys.ctm := run_ctmInv hI0.1 (RunIsARun wWorld wProofMulti _ _ _ hrun)
  refine ⟨hI0, hL.2.2.1, hL.1 xNodup100, gSetup_noArb, gSetup_installsWf,
    ⟨gSys, gProof wProofMulti⟩, ⟨1, rowsRouting (wRows 100)⟩, hrun, hC, rfl, rfl, by decide, rfl,
    xNodup100, xNodup200, rfl, by decide, ?_⟩
  exact gT0_multi

theorem RequirementLifecycleWitness : Properties.RequirementLifecycleWitness := by
  have h2 : Run35 wWorld wProofMulti wSys35 [.routing (.genesis 0), .routing (.genesis 1)] _ :=
    Run35.cons (Step35.routing (Step.genesis (s := wSys0) (id := 0) rfl (addAll_empty_eq xNodup100))
        ProofEffect.genesis)
      (Run35.cons (Step35.routing (Step.genesis (id := 1) rfl (addAll_empty_eq xNodup100))
        ProofEffect.genesis) Run35.nil)
  refine ⟨⟨_, _, ⟨1, rowsRouting (wRows 100)⟩, h2,
      Step35.requireSecondProofSystem (id := 0) (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl
        (by decide), rfl, rfl, rfl⟩,
    ⟨gSys, gProof wProofMulti⟩, ⟨gEndSys, gEndProof⟩, ⟨1, rowsRouting (wRows 100)⟩,
    gSetup_run wProofMulti rfl, Run35.cons gT0_multi (Run35.cons gT1_multi Run35.nil), rfl, rfl,
    ?_, rfl⟩
  intro v ρ h
  simp at h

theorem PerChainHeadlineAtV35Witness : Properties.PerChainHeadlineAtV35Witness := by
  have hrun : Run35 wWorld wProofMulti wSys35 wGateLocalRun _ :=
    Run35.cons (Step35.routing (Step.genesis (s := wSys0) (id := 0) rfl (addAll_empty_eq xNodup100))
      ProofEffect.genesis)
    (Run35.cons (Step35.routing (Step.genesis (id := 1) rfl (addAll_empty_eq xNodup100))
      ProofEffect.genesis)
    (Run35.cons (Step35.requireSecondProofSystem (id := 0) (c := ⟨1, rowsRouting (wRows 100)⟩) rfl
      rfl (by decide))
    (Run35.cons (Step35.routing (Step.arbitraryCut (id := 0) 1 bgExtra rfl)
      (ProofEffect.arbitraryCut (p := ⟨true, 51, 0⟩) (fun _ => by decide)))
    (Run35.cons (Step35.routing (Step.arbitraryCut (id := 1) 1 bgExtra rfl)
      (ProofEffect.arbitraryCut (p := ⟨false, 51, 0⟩) (fun h => absurd h (by decide))))
    (Run35.cons (Step35.routing (Step.arbitraryCut (id := 0) 1 (rowsRouting (wRows 100)) rfl)
      (ProofEffect.arbitraryCut (p := ⟨true, 51, 0⟩) (fun _ => by decide)))
    (Run35.cons (Step35.routing (Step.ctm (CStep.commit (t := 300) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide))) ProofEffect.ctm)
    (Run35.cons (Step35.routing (Step.transition (id := 0) rfl (by decide) rfl
        (applyDerived_rows_eq xNodup100 xNodup200) (by decide))
      (ProofEffect.transition rfl (fun _ => by decide))) Run35.nil)))))))
  have hD : DisablingNeverEnablesMultiProof wProofMulti := by
    intro v m h
    simp only [wProofMulti, decide_eq_true_eq] at h ⊢
    exact ⟨h.1, trivial⟩
  have hP0 : ProofInv wProofMulti wSys35 := fun id c hc => by simp [wSys35, wSys0] at hc
  have hlast0 : LastWriteNotBreakGlass 0 (wGateLocalRun.flatMap Label35.routingSteps) :=
    lastWriteNotBreakGlass_snoc (l := .transition 0) rfl (fun h => h)
      [.genesis 0, .genesis 1, .arbitraryCut 0 1 bgExtra, .arbitraryCut 1 1 bgExtra,
        .arbitraryCut 0 1 (rowsRouting (wRows 100)), .ctm (.commit 300)]
  have hlast1 : ¬ LastWriteNotBreakGlass 1 (wGateLocalRun.flatMap Label35.routingSteps) := by
    intro h
    exact h [.genesis 0, .genesis 1, .arbitraryCut 0 1 bgExtra] (.arbitraryCut 1 1 bgExtra)
      [.arbitraryCut 0 1 (rowsRouting (wRows 100)), .ctm (.commit 300), .transition 0] rfl rfl
      (by simp [Label.writesChain]) trivial
  refine ⟨_, hrun, FreshSystemSatisfiesInvariant wWorld 100 (by decide), rfl,
    ⟨.routing (.arbitraryCut 0 1 bgExtra),
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      trivial⟩,
    hlast0, hlast1, ⟨_, rfl, by decide, by decide, rfl⟩, rfl, by decide,
    RequiringChainsKeepAMultiProofVerifier wWorld wProofMulti _ _ _ hD hP0 hrun,
    ⟨_, rfl, rfl, by decide, ?_⟩⟩
  exact fun h => absurd (congrFun h 9) (by decide)

theorem UngatedRunLiftWitness : Properties.UngatedRunLiftWitness := by
  refine ⟨rfl, fun _ => rfl, gEndSys, RunIsARun wWorld wProofMulti _ _ _ gRun_multi, ?_⟩
  intro id hid
  interval_cases id
  · exact ⟨_, rfl, rfl⟩
  · exact ⟨_, rfl, rfl⟩

/-! ## `ChainRouting`, `Enabledness` and `ChainLocal` step results over v35 steps -/

/-- The routing step of a v35 routing step. -/
lemma step35_step {W : World} {P : ProofWorld} {s s' : Sys35} {l : Label}
    (h : Step35 W P s (.routing l) s') : Step W s.sys l s'.sys := by
  cases h with
  | routing hs _ => exact hs

theorem StepPreservesSysInvariant : Properties.StepPreservesSysInvariant := by
  intro W P s s' l hI h hl
  cases h with
  | routing hs _ => exact Contracts.ChainTypeManager.StepPreservesSysInvariant W _ _ _ hI hs hl
  | requireSecondProofSystem _ _ _ => exact hI
  | setProofSystems _ => exact hI

theorem TransitionStartsAndLandsOnRelease : Properties.TransitionStartsAndLandsOnRelease := by
  intro W P s s' id c hC hc h
  have hbase := Contracts.ChainTypeManager.TransitionStartsAndLandsOnRelease W s.sys s'.sys id c
    hC hc (step35_step h)
  refine ⟨hbase.1, hbase.2.1, hbase.2.2, ?_⟩
  cases h with
  | routing _ he =>
      cases he with
      | @transition _ c' hc' _ =>
          rw [hc] at hc'
          cases hc'
          simp [ProofState.install]

theorem DriftBlocksTransition : Properties.DriftBlocksTransition := by
  rintro W P s id c hC hc hd ⟨s', h⟩
  exact Contracts.ChainTypeManager.DriftBlocksTransition W s.sys id c hC hc hd ⟨_, step35_step h⟩

theorem RepeatedSelectorBlocksTheEdge : Properties.RepeatedSelectorBlocksTheEdge := by
  rintro W P s id c hc hne hdup ⟨s', h⟩
  exact Contracts.ChainTypeManager.RepeatedSelectorBlocksTheEdge W s.sys id c hc hne hdup
    ⟨_, step35_step h⟩

theorem NewChainEnabledIff : Properties.NewChainEnabledIff := by
  intro W P s id
  obtain ⟨hg, hm⟩ := Contracts.ChainTypeManager.NewChainEnabledIff W s.sys id
  constructor
  · constructor
    · rintro ⟨s', h⟩
      exact hg.mp ⟨_, step35_step h⟩
    · intro hcond
      obtain ⟨sys', hs⟩ := hg.mpr hcond
      exact ⟨_, Step35.routing hs ProofEffect.genesis⟩
  · constructor
    · rintro ⟨s', h⟩
      exact hm.mp ⟨_, step35_step h⟩
    · intro hcond
      obtain ⟨sys', hs⟩ := hm.mpr hcond
      exact ⟨_, Step35.routing hs ProofEffect.migrateIn⟩

theorem BootstrapResetEnabledIff : Properties.BootstrapResetEnabledIff := by
  intro W P s id c hC hc
  have hbase := Contracts.ChainTypeManager.BootstrapResetEnabledIff W s.sys id c hC hc
  constructor
  · rintro ⟨s', h⟩
    cases h with
    | routing hs he =>
        obtain ⟨R, hl, hwf⟩ := hbase.mp ⟨_, hs⟩
        exact ⟨R, hl, hwf, fun hr => proofEffect_gate (s := s) he c R hc hl hr⟩
  · rintro ⟨R, hl, hwf, hgate⟩
    obtain ⟨sys', hs⟩ := hbase.mpr ⟨R, hl, hwf⟩
    exact ⟨_, Step35.routing hs (ProofEffect.bootstrapReset hc hl hgate)⟩

theorem ChainsStayOnWfReleases : Properties.ChainsStayOnWfReleases := by
  intro W P s s' ls hI hW h hl
  exact Contracts.ChainTypeManager.ChainsStayOnWfReleases W s.sys s'.sys _ hI hW
    (RunIsARun W P s s' ls h) (routing_no_arbitrary hl)

theorem StepsElsewhereKeepChainOk : Properties.StepsElsewhereKeepChainOk := by
  intro W P s s' l id hok h hw
  cases h with
  | @routing l' _ _ hs _ =>
      exact Contracts.ChainTypeManager.StepsElsewhereKeepChainOk W _ _ l' id hok hs
        (hw l' (List.mem_singleton_self _))
  | requireSecondProofSystem _ _ _ => exact hok
  | setProofSystems _ => exact hok

theorem NonCutWriteLandsOnRelease : Properties.NonCutWriteLandsOnRelease := by
  intro W P s s' l id hC h hw hl
  exact Contracts.ChainTypeManager.NonCutWriteLandsOnRelease W s.sys s'.sys l id hC
    (step35_step h) hw hl

theorem NewChainRunsItsVersionsRelease : Properties.NewChainRunsItsVersionsRelease := by
  intro W P s s' ls id hC hn h hlast
  exact Contracts.ChainTypeManager.NewChainRunsItsVersionsRelease W s.sys s'.sys _ id hC hn
    (RunIsARun W P s s' ls h) hlast

theorem RepairCutRestoresChainOk : Properties.RepairCutRestoresChainOk := by
  intro W P s id v hC hreg hv
  obtain ⟨⟨sys', hs⟩, hall⟩ := Contracts.ChainTypeManager.RepairCutRestoresChainOk W s.sys id v hC
    hreg hv
  refine ⟨?_, fun s' h => hall s'.sys (step35_step h)⟩
  obtain ⟨pr', he⟩ := gate_proofEffect (P := P) (s := s) hs (by unfold repairCut; trivial)
  exact ⟨_, Step35.routing hs he⟩

theorem OnlyRepairCutsLandOnARelease : Properties.OnlyRepairCutsLandOnARelease := by
  intro W P s s' id v ρ h hland
  exact Contracts.ChainTypeManager.OnlyRepairCutsLandOnARelease W s.sys s'.sys id v ρ
    (step35_step h) hland

/-- A break-glass cut is of a registered chain. -/
private lemma arbitraryCut_registered {W : World} {s sys' : Sys} {id : ChainId} {v : ℕ}
    {ρ : Routing} (h : Step W s (.arbitraryCut id v ρ) sys') : ∃ c, s.chains id = some c := by
  cases h with
  | arbitraryCut _ _ hc => exact ⟨_, hc⟩

theorem RepairEnablesTransition : Properties.RepairEnablesTransition := by
  intro W P s s' id v hC hv h hut hn1 hn2 hgate
  have hs := step35_step h
  obtain ⟨s'', hstep, hland⟩ := Contracts.ChainTypeManager.RepairEnablesTransition W s.sys s'.sys
    id v hC hv hs hut hn1 hn2
  obtain ⟨hctm, -, c0, hc0, hpv, -⟩ :=
    (Contracts.ChainTypeManager.RepairCutRestoresChainOk W s.sys id v hC
      (arbitraryCut_registered hs) hv).2 s'.sys hs
  have harr : arrivingVerifier W P s'.sys c0 = P.relVerifier (s.sys.edge W v).newRel := by
    simp only [arrivingVerifier, Sys.edge, hctm, hpv]
  refine ⟨⟨s'', _⟩, Step35.routing hstep (ProofEffect.transition hc0 ?_), hland⟩
  intro hreq
  show P.multi (arrivingVerifier W P s'.sys c0) 0 = true
  rw [harr]
  exact hgate hreq

end Contracts.ChainTypeManager.ProofGateAtV35
