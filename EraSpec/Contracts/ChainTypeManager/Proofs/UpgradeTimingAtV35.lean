import EraSpec.Contracts.ChainTypeManager.Properties.UpgradeTimingAtV35
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTiming
import EraSpec.Contracts.ChainTypeManager.Proofs.ProofGateAtV35

/-!
# Proofs: who may upgrade a chain, and when, at `draft/v0.35.0`

A v35 timed step is an `UpgradeTiming` step plus the `ProofEffect` of its routing step, so
`ProofGateAtV35`'s two lemmas (`proofEffect_gate`, `gate_proofEffect`) give the step
characterization. The `UpgradeTiming` results then transfer: necessary conditions through the
projection `TimedRunIsATimedRun`, exact ones through `UnflaggedChainsUpgradeAsAtE561`. The
countermodel and the witness are concrete runs over `UpgradeTiming`'s witness configuration.
-/

namespace Contracts.ChainTypeManager.UpgradeTimingAtV35

open Contracts.ChainTypeManager
open Contracts.ChainTypeManager.ProofGateAtV35

/-! ## The v35 timed step and run -/

/-- The routing step of a timed step, if it has one, and the gate it adds. -/
private lemma timedEffect_gate {T : TimedConfig} {P : ProofWorld} {s : TimedSys35} {l : TimedLabel}
    {pr' : ChainId → ProofState} (h : TimedProofEffect T P s.timed s.proof l pr') :
    TimedGateHolds T P s l := by
  cases h with
  | upgrade he => exact proofEffect_gate (s := s.routing) he
  | base he => exact proofEffect_gate (s := s.routing) he
  | setUpgradeTimestamp => trivial
  | swapNotifier => trivial
  | setAux => trivial

private lemma gate_timedEffect {T : TimedConfig} {P : ProofWorld} {s : TimedSys35} {l : TimedLabel}
    {t' : TimedSys} (hs : TimedStep T s.timed l t') (hg : TimedGateHolds T P s l) :
    ∃ pr', TimedProofEffect T P s.timed s.proof l pr' := by
  cases l with
  | upgrade id path caller τ =>
      obtain ⟨hr, _, _⟩ := Contracts.ChainTypeManager.UpgradeIsATransition T s.timed t' id path
        caller τ hs
      obtain ⟨pr', he⟩ := gate_proofEffect (s := s.routing) hr hg
      exact ⟨pr', TimedProofEffect.upgrade he⟩
  | base l =>
      cases hs with
      | base _ hr =>
          obtain ⟨pr', he⟩ := gate_proofEffect (s := s.routing) hr hg
          exact ⟨pr', TimedProofEffect.base he⟩
  | setUpgradeTimestamp _ _ _ => exact ⟨_, TimedProofEffect.setUpgradeTimestamp⟩
  | swapNotifier _ => exact ⟨_, TimedProofEffect.swapNotifier⟩
  | setAux _ _ => exact ⟨_, TimedProofEffect.setAux⟩

theorem TimedStepIsTheE561StepPlusTheGate : Properties.TimedStepIsTheE561StepPlusTheGate := by
  intro T P s l t'
  constructor
  · rintro ⟨pr', h⟩
    cases h with
    | timed hs he => exact ⟨hs, timedEffect_gate he⟩
  · rintro ⟨hs, hg⟩
    obtain ⟨pr', he⟩ := gate_timedEffect hs hg
    exact ⟨pr', TimedStep35.timed hs he⟩

private lemma timedRun_append {T : TimedConfig} {s s' s'' : TimedSys} {l1 l2 : List TimedLabel}
    (h1 : TimedRun T s l1 s') (h2 : TimedRun T s' l2 s'') : TimedRun T s (l1 ++ l2) s'' := by
  induction h1 with
  | nil => exact h2
  | cons hs _ ih => exact TimedRun.cons hs (ih h2)

private lemma timedStep35_timed {T : TimedConfig} {P : ProofWorld} {s s' : TimedSys35}
    {l : TimedLabel35} (h : TimedStep35 T P s l s') : TimedRun T s.timed l.timedSteps s'.timed := by
  cases h with
  | timed hs _ => exact TimedRun.cons hs TimedRun.nil
  | requireSecondProofSystem _ _ _ _ _ => exact TimedRun.nil
  | setProofSystems _ => exact TimedRun.nil

theorem TimedRunIsATimedRun : Properties.TimedRunIsATimedRun := by
  intro T P s s' ls h
  induction h with
  | nil => exact TimedRun.nil
  | cons hs _ ih =>
      rw [List.flatMap_cons]
      exact timedRun_append (timedStep35_timed hs) ih

/-- With the requirement off everywhere, every timed step has a `TimedProofEffect` that keeps it
off. -/
private lemma lift_timedEffect {T : TimedConfig} {P : ProofWorld} {s t' : TimedSys} {l : TimedLabel}
    {pr : ChainId → ProofState} (hs : TimedStep T s l t') (hpr : ∀ id, (pr id).required = false) :
    ∃ pr', TimedProofEffect T P s pr l pr' ∧ ∀ id, (pr' id).required = false := by
  cases l with
  | upgrade id path caller τ =>
      obtain ⟨hr, _, _⟩ := Contracts.ChainTypeManager.UpgradeIsATransition T s t' id path caller
        τ hs
      obtain ⟨pr', he, h'⟩ := lift_proofEffect (P := P) hr hpr
      exact ⟨pr', TimedProofEffect.upgrade he, h'⟩
  | base l =>
      cases hs with
      | base _ hr =>
          obtain ⟨pr', he, h'⟩ := lift_proofEffect (P := P) hr hpr
          exact ⟨pr', TimedProofEffect.base he, h'⟩
  | setUpgradeTimestamp _ _ _ => exact ⟨_, TimedProofEffect.setUpgradeTimestamp, hpr⟩
  | swapNotifier _ => exact ⟨_, TimedProofEffect.swapNotifier, hpr⟩
  | setAux _ _ => exact ⟨_, TimedProofEffect.setAux, hpr⟩

theorem E561TimedRunsAreRunsWithoutTheRequirement :
    Properties.E561TimedRunsAreRunsWithoutTheRequirement := by
  intro T P s s' ls pr h hpr
  induction h generalizing pr with
  | nil => exact ⟨pr, TimedRun35.nil, hpr⟩
  | cons hs _ ih =>
      obtain ⟨pr1, he, hpr1⟩ := lift_timedEffect (P := P) hs hpr
      obtain ⟨pr2, hrun, hpr2⟩ := ih pr1 hpr1
      exact ⟨pr2, TimedRun35.cons (TimedStep35.timed hs he) hrun, hpr2⟩

theorem UnflaggedChainsUpgradeAsAtE561 : Properties.UnflaggedChainsUpgradeAsAtE561 := by
  intro T P s id path caller τ t' hreq
  rw [TimedStepIsTheE561StepPlusTheGate T P s _ t']
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  intro c _ hr
  exact absurd (hreq.symm.trans hr) (by decide)

theorem TimedRunKeepsChainsOnTheirRelease : Properties.TimedRunKeepsChainsOnTheirRelease := by
  intro T P s s' ls hI h hl
  refine Contracts.ChainTypeManager.TimedRunKeepsChainsOnTheirRelease T s.timed s'.timed _ hI
    (TimedRunIsATimedRun T P s s' ls h) ?_
  intro l hm
  obtain ⟨x, hx, hlx⟩ := List.mem_flatMap.mp hm
  cases x with
  | timed l' =>
      simp only [TimedLabel35.timedSteps, List.mem_singleton] at hlx
      subst hlx
      exact hl _ hx
  | requireSecondProofSystem _ _ => simp [TimedLabel35.timedSteps] at hlx
  | setProofSystems _ _ => simp [TimedLabel35.timedSteps] at hlx

/-! ## The proof-system guarantees along timed runs -/

private lemma run35_append {W : World} {P : ProofWorld} {s s' s'' : Sys35} {l1 l2 : List Label35}
    (h1 : Run35 W P s l1 s') (h2 : Run35 W P s' l2 s'') : Run35 W P s (l1 ++ l2) s'' := by
  induction h1 with
  | nil => exact h2
  | cons hs _ ih => exact Run35.cons hs (ih h2)

/-- One v35 timed step is its `ProofGateAtV35` steps. -/
private lemma timedStep35_gate {T : TimedConfig} {P : ProofWorld} {s s' : TimedSys35}
    {l : TimedLabel35} (h : TimedStep35 T P s l s') :
    Run35 T.X.W P s.routing l.gateSteps s'.routing := by
  cases h with
  | @timed l t' pr' hs he =>
      cases he with
      | @upgrade id path caller τ pr' he' =>
          obtain ⟨hr, _, _⟩ := Contracts.ChainTypeManager.UpgradeIsATransition T s.timed t' id
            path caller τ hs
          exact Run35.cons (Step35.routing (s := s.routing) hr he') Run35.nil
      | @base l pr' he' =>
          cases hs with
          | base _ hr => exact Run35.cons (Step35.routing (s := s.routing) hr he') Run35.nil
      | setUpgradeTimestamp =>
          cases hs with
          | setUpgradeTimestamp _ _ _ _ => exact Run35.nil
      | swapNotifier =>
          cases hs with
          | swapNotifier => exact Run35.nil
      | setAux =>
          cases hs with
          | setAux => exact Run35.nil
  | requireSecondProofSystem hc _ _ hreq hm =>
      exact Run35.cons (Step35.requireSecondProofSystem (s := s.routing) hc hreq hm) Run35.nil
  | setProofSystems hc =>
      exact Run35.cons (Step35.setProofSystems (s := s.routing) hc) Run35.nil

theorem TimedRunIsAProofGateRun : Properties.TimedRunIsAProofGateRun := by
  intro T P s s' ls h
  induction h with
  | nil => exact Run35.nil
  | cons hs _ ih =>
      rw [List.flatMap_cons]
      exact run35_append (timedStep35_gate hs) ih

theorem TimedRunsKeepAMultiProofVerifier : Properties.TimedRunsKeepAMultiProofVerifier := by
  intro T P s s' ls hD hI h
  exact RequiringChainsKeepAMultiProofVerifier T.X.W P s.routing s'.routing _ hD hI
    (TimedRunIsAProofGateRun T P s s' ls h)

theorem TimedRequirementWriters : Properties.TimedRequirementWriters := by
  intro T P s s' l id c h hc hne
  cases h with
  | @timed l t' pr' hs he =>
      dsimp only at hne
      cases he with
      | @upgrade id' path caller τ pr' he' =>
          obtain ⟨hr, _, _⟩ := Contracts.ChainTypeManager.UpgradeIsATransition T s.timed t' id'
            path caller τ hs
          rcases RequirementWriters T.X.W P s.routing ⟨t'.sys, pr'⟩ _ id c
            (Step35.routing (s := s.routing) hr he') hc hne with ⟨hl, _⟩ | ⟨v, ρ, hl⟩
          · cases hl
          · cases hl
      | @base l pr' he' =>
          cases hs with
          | @base _ sys' _ hr =>
              rcases RequirementWriters T.X.W P s.routing ⟨sys', pr'⟩ _ id c
                (Step35.routing (s := s.routing) hr he') hc hne with ⟨hl, _⟩ | ⟨v, ρ, hl⟩
              · cases hl
              · cases hl
                exact Or.inr ⟨v, ρ, rfl⟩
      | setUpgradeTimestamp => exact absurd rfl hne
      | swapNotifier => exact absurd rfl hne
      | setAux => exact absurd rfl hne
  | @requireSecondProofSystem id' caller c' _ hcaller hsl _ _ =>
      dsimp only at hne ⊢
      by_cases e : id = id'
      · subst e
        exact Or.inl ⟨caller, rfl, hcaller, hsl, by simp⟩
      · exact absurd (by rw [upd_ne _ _ e]) hne
  | @setProofSystems id' c' m _ =>
      dsimp only at hne
      by_cases e : id = id'
      · subst e
        exact absurd (by simp) hne
      · exact absurd (by rw [upd_ne _ _ e]) hne

theorem TimedRequirementIsPermanentWithoutBreakGlass :
    Properties.TimedRequirementIsPermanentWithoutBreakGlass := by
  intro T P s s' ls id c h hc hreq hno
  refine RequirementIsPermanentWithoutBreakGlass T.X.W P s.routing s'.routing _ id c
    (TimedRunIsAProofGateRun T P s s' ls h) hc hreq ?_
  intro v ρ hm
  obtain ⟨x, hx, hlx⟩ := List.mem_flatMap.mp hm
  cases x with
  | timed l =>
      simp only [TimedLabel35.gateSteps, List.mem_map] at hlx
      obtain ⟨l', hl', he⟩ := hlx
      cases he
      cases l with
      | upgrade _ _ _ _ => simp [TimedLabel.untimed] at hl'
      | base l'' =>
          simp only [TimedLabel.untimed, List.mem_singleton] at hl'
          subst hl'
          exact hno v ρ hx
      | setUpgradeTimestamp _ _ _ => simp [TimedLabel.untimed] at hl'
      | swapNotifier _ => simp [TimedLabel.untimed] at hl'
      | setAux _ _ => simp [TimedLabel.untimed] at hl'
  | requireSecondProofSystem _ _ => simp [TimedLabel35.gateSteps] at hlx
  | setProofSystems _ _ => simp [TimedLabel35.gateSteps] at hlx

/-! ## The NatSpec of `upgradeChain`, at v35 -/

/-- An upgrade writes neither `DiamondAux` nor the notifier. -/
private lemma upgrade_shape {T : TimedConfig} {s t' : TimedSys} {id : ChainId} {path : UpgradePath}
    {caller : Address} {τ : ℕ} (h : TimedStep T s (.upgrade id path caller τ) t') :
    t' = { s with sys := t'.sys } := by
  obtain ⟨_, ha, hn⟩ := Contracts.ChainTypeManager.UpgradeIsATransition T s t' id path caller τ h
  cases s
  cases t'
  simp only at ha hn
  subst ha hn
  rfl

theorem ExecutorPathIgnoresNotifier : Properties.ExecutorPathIgnoresNotifier := by
  intro T P s id t caller τ n
  have e561 := Contracts.ChainTypeManager.ExecutorPathIgnoresNotifier T s.timed id t caller τ n
  have part1 : ∀ (sys' : Sys) (pr' : ChainId → ProofState),
      TimedStep35 T P s (.timed (.upgrade id (.executor t) caller τ))
          ⟨{ s.timed with sys := sys' }, pr'⟩ ↔
        TimedStep35 T P ⟨{ s.timed with notifier := n }, s.proof⟩
          (.timed (.upgrade id (.executor t) caller τ))
          ⟨{ s.timed with notifier := n, sys := sys' }, pr'⟩ := by
    intro sys' pr'
    constructor
    · intro h
      cases h with
      | timed hs he =>
          cases he with
          | upgrade he' =>
              exact TimedStep35.timed ((e561.1 sys').mp hs) (TimedProofEffect.upgrade he')
    · intro h
      cases h with
      | timed hs he =>
          cases he with
          | upgrade he' =>
              exact TimedStep35.timed ((e561.1 sys').mpr hs) (TimedProofEffect.upgrade he')
  refine ⟨part1, ⟨?_, ?_⟩⟩
  · rintro ⟨⟨t', pr'⟩, h⟩
    have hs : TimedStep T s.timed (.upgrade id (.executor t) caller τ) t' := by
      cases h with
      | timed hs _ => exact hs
    have ht := upgrade_shape hs
    rw [ht] at h
    exact ⟨_, (part1 t'.sys pr').mp h⟩
  · rintro ⟨⟨t', pr'⟩, h⟩
    have hs : TimedStep T { s.timed with notifier := n } (.upgrade id (.executor t) caller τ) t' := by
      cases h with
      | timed hs _ => exact hs
    have ht := upgrade_shape hs
    rw [ht] at h
    exact ⟨_, (part1 t'.sys pr').mpr h⟩

theorem ProofGateBindsEveryPath : Properties.ProofGateBindsEveryPath := by
  intro T P s s' id path caller τ c h hc hreq
  cases h with
  | timed hs he =>
      cases he with
      | upgrade he' =>
          cases he' with
          | @transition _ c' hc' hg =>
              rw [hc] at hc'
              cases hc'
              refine ⟨hg hreq, ?_⟩
              simp [ProofState.install]

theorem UpgradeChainEnabledIffTimed : Properties.UpgradeChainEnabledIffTimed := by
  intro T P s id t caller τ
  have e561 := Contracts.ChainTypeManager.UpgradeChainEnabledIffTimed T s.timed id t caller τ
  -- the edge a chain at `t.oldProtocolVersion()` crosses, when `t` is committed there, is `t`
  have hedge : ∀ c : Chain, c.pv = (T.X.W.tr t).old → s.timed.sys.ctm.ut (T.X.W.tr t).old = t →
      arrivingVerifier T.X.W P s.timed.sys c = P.relVerifier (T.X.W.tr t).newRel := by
    intro c hv hut
    simp only [arrivingVerifier, Sys.edge]
    rw [hv, hut]
  constructor
  · rintro ⟨⟨t', pr'⟩, h⟩
    cases h with
    | timed hs he =>
        have hcond := e561.mp ⟨t', hs⟩
        refine ⟨hcond, fun hreq => ?_⟩
        obtain ⟨_, hut, _, ⟨c, hc, hv⟩, _⟩ := hcond
        cases he with
        | upgrade he' =>
            cases he' with
            | @transition _ c' hc' hg =>
                rw [hc] at hc'
                cases hc'
                rw [← hedge c hv hut]
                exact hg hreq
  · rintro ⟨hcond, hgate⟩
    obtain ⟨t', hs⟩ := e561.mpr hcond
    obtain ⟨_, hut, _, ⟨c, hc, hv⟩, _⟩ := hcond
    refine ⟨_, TimedStep35.timed hs (TimedProofEffect.upgrade (ProofEffect.transition hc ?_))⟩
    intro hreq
    show P.multi (arrivingVerifier T.X.W P s.timed.sys c) 0 = true
    rw [hedge c hv hut]
    exact hgate hreq

/-! ## Not at any time, at v35 -/

theorem NotAtAnyTime : Properties.NotAtAnyTime := by
  intro P
  obtain ⟨s0, hrun, hut, hts, hc, hown, hadm, h9o, h9a, h9, h10o, h10a⟩ :=
    Contracts.ChainTypeManager.NotAtAnyTime
  obtain ⟨pr', hrun35, hpr'⟩ := E561TimedRunsAreRunsWithoutTheRequirement wTiming P wTimingSys0 s0
    wTimingSetup (fun _ => ⟨false, 0, 0⟩) hrun (fun _ => rfl)
  -- a v35 step from `⟨s0, pr'⟩` is an `UpgradeTiming` step from `s0`
  have proj : ∀ l s', TimedStep35 wTiming P ⟨s0, pr'⟩ (.timed l) s' → ∃ t', TimedStep wTiming s0 l t' := by
    intro l s' h
    cases h with
    | timed hs _ => exact ⟨_, hs⟩
  -- and every `UpgradeTiming` upgrade of chain `0` from `s0` is one at v35
  have lift : ∀ path caller τ, (∃ t', TimedStep wTiming s0 (.upgrade 0 path caller τ) t') →
      ∃ s', TimedStep35 wTiming P ⟨s0, pr'⟩ (.timed (.upgrade 0 path caller τ)) s' := by
    rintro path caller τ ⟨t', h⟩
    obtain ⟨pr'', h'⟩ := (UnflaggedChainsUpgradeAsAtE561 wTiming P ⟨s0, pr'⟩ 0 path caller τ t'
      (hpr' 0)).mpr h
    exact ⟨_, h'⟩
  refine ⟨⟨s0, pr'⟩, hrun35, hut, hts, hc, hown, hadm, ?_, ?_, ?_, lift _ _ _ h10o, lift _ _ _ h10a⟩
  · rintro t ⟨s', h⟩
    obtain ⟨t', h'⟩ := proj _ _ h
    exact h9o t ⟨t', h'⟩
  · rintro t ⟨s', h⟩
    obtain ⟨t', h'⟩ := proj _ _ h
    exact h9a t ⟨t', h'⟩
  · rintro path caller ⟨s', h⟩
    obtain ⟨t', h'⟩ := proj _ _ h
    exact h9 path caller ⟨t', h'⟩

/-! ## The countermodel and the witness

The setup `wTimingGateSetup` from `wTimingSys35`. Its timed states are `UpgradeTiming`'s
setup states; the proof-system fields are chain `0`'s, with release `100`'s verifier. -/

/-- The routing system after the setup (`UpgradeTiming`'s `tSetupSys`). -/
private def tgSys : Sys :=
  ⟨⟨2, 200, upd (fun _ => 0) 1 300, fun _ => LegacyCut.none, upd (upd (fun _ => 0) 1 100) 2 200⟩,
    upd (fun _ => none) 0 (some ⟨1, rowsRouting (wRows 100)⟩)⟩

/-- The timed state after the genesis of chain `0`. -/
private def tg1 : TimedSys :=
  ⟨⟨wSys0.ctm, upd (fun _ => none) 0 (some ⟨1, rowsRouting (wRows 100)⟩)⟩, wTimingSys0.aux,
    wTimingSys0.notifier⟩

/-- The timed state after chain `0` is configured. -/
private def tg2 : TimedSys := ⟨tg1.sys, upd tg1.aux 0 wTimingAux, tg1.notifier⟩

/-- The timed state after the commit of `300`. -/
private def tg4 : TimedSys := ⟨tgSys, tg2.aux, tg2.notifier⟩

/-- The timed state after the setup. -/
private def tgTimed : TimedSys := ⟨tgSys, tg2.aux, setNotifierEntry tg2.notifier 0 1 12⟩

/-- The proof-system fields after the setup. -/
private def tgProof (P : ProofWorld) : ChainId → ProofState :=
  upd (upd (fun _ => ⟨false, 0, 0⟩) 0 ⟨false, P.relVerifier 100, 0⟩) 0 ⟨true, P.relVerifier 100, 0⟩

private lemma tgCommit : CStep wWorld wSys0.ctm (.commit 300) tgSys.ctm :=
  CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The setup runs in every proof world whose release `100` ships a verifier in multi-proof mode
with nothing disabled. -/
private lemma tgSetup_run (P : ProofWorld) (h : P.multi (P.relVerifier 100) 0 = true) :
    TimedRun35 wTiming P wTimingSys35 wTimingGateSetup ⟨tgTimed, tgProof P⟩ :=
  TimedRun35.cons (TimedStep35.timed (TimedStep.base (s := wTimingSys0) (l := .genesis 0)
      (fun h => h) (Step.genesis (s := wSys0) rfl (addAll_empty_eq xNodup100)))
      (TimedProofEffect.base ProofEffect.genesis))
    (TimedRun35.cons (TimedStep35.timed (TimedStep.setAux (s := tg1)) TimedProofEffect.setAux)
      (TimedRun35.cons (TimedStep35.requireSecondProofSystem (c := ⟨1, rowsRouting (wRows 100)⟩)
          rfl rfl rfl rfl h)
        (TimedRun35.cons (TimedStep35.timed (TimedStep.base (s := tg2) (l := .ctm (.commit 300))
            (fun h => h) (Step.ctm tgCommit)) (TimedProofEffect.base ProofEffect.ctm))
          (TimedRun35.cons (TimedStep35.timed (TimedStep.setUpgradeTimestamp (s := tg4)
              (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl (by decide) (Or.inl (by decide)))
              TimedProofEffect.setUpgradeTimestamp)
            TimedRun35.nil))))

/-- Chain `0`'s routing transition after the setup. -/
private lemma tg_transition : Step wWorld tgSys (.transition 0)
    ⟨tgSys.ctm, upd tgSys.chains 0 (some ⟨2, rowsRouting (wRows 200)⟩)⟩ :=
  Step.transition (s := tgSys) (id := 0) rfl (by decide) rfl
    (applyDerived_rows_eq xNodup100 xNodup200) (by decide)

theorem OwnerCannotUpgradeARequiringChainToAPlonkRelease :
    Properties.OwnerCannotUpgradeARequiringChainToAPlonkRelease := by
  have hcond : ∀ τ, 10 ≤ τ →
      ((2 = wTiming.execOwner ∨ 2 = (tgTimed.aux 0).admin) ∧
        tgTimed.sys.ctm.ut (wTiming.X.W.tr 300).old = 300 ∧ wTiming.X.rc.self = wTiming.ctmOwner ∧
        (∃ c, tgTimed.sys.chains 0 = some c ∧ c.pv = (wTiming.X.W.tr 300).old) ∧
        (wTiming.sched 300).upgradeTimestamp ≤ τ ∧
        (tgTimed.aux 0).committed = (tgTimed.aux 0).executed ∧
        (∀ w, (tgTimed.aux 0).slVersion = some w → (wTiming.X.W.tr 300).new ≤ w) ∧
        ∃ sys', Step wTiming.X.W tgTimed.sys (.transition 0) sys') := by
    intro τ hτ
    exact ⟨Or.inl rfl, rfl, rfl, ⟨_, rfl, rfl⟩, hτ, rfl, (fun w hw => by cases hw),
      ⟨_, tg_transition⟩⟩
  refine ⟨⟨tgTimed, tgProof wProofPlonk⟩, tgSetup_run wProofPlonk rfl, rfl, rfl,
    fun τ hτ => ⟨hcond τ hτ, ?_⟩, ?_⟩
  · exact (Contracts.ChainTypeManager.UpgradeChainEnabledIffTimed wTiming tgTimed 0 300 2 τ).mpr
      (hcond τ hτ)
  · rintro path caller τ ⟨s', h⟩
    have := (ProofGateBindsEveryPath wTiming wProofPlonk _ _ 0 path caller τ
      ⟨1, rowsRouting (wRows 100)⟩ h rfl rfl).1
    exact absurd this (by decide)

/-- The state after the witness's `upgradeChain(300, 0)`. -/
private def tgEnd : TimedSys35 :=
  ⟨⟨⟨tgSys.ctm, upd tgSys.chains 0 (some ⟨2, rowsRouting (wRows 200)⟩)⟩, tgTimed.aux,
      tgTimed.notifier⟩,
    upd (tgProof wProofMulti) 0 ⟨true, 53, 0⟩⟩

theorem UpgradeTimingAtV35Witness : Properties.UpgradeTimingAtV35Witness := by
  have hup : TimedStep35 wTiming wProofMulti ⟨tgTimed, tgProof wProofMulti⟩
      (.timed (.upgrade 0 (.executor 300) 3 10)) tgEnd :=
    TimedStep35.timed (TimedStep.executor (s := tgTimed) (Or.inr rfl) (by decide) rfl
        ⟨Or.inr (Or.inl rfl), ⟨_, rfl, rfl⟩, fun _ h => absurd rfl h, rfl, tg_transition,
          by decide, fun w hw => by cases hw⟩)
      (TimedProofEffect.upgrade (ProofEffect.transition (c := ⟨1, rowsRouting (wRows 100)⟩) rfl
        (fun _ => by decide)))
  have hrun : TimedRun35 wTiming wProofMulti wTimingSys35
      (wTimingGateSetup ++ [.timed (.upgrade 0 (.executor 300) 3 10)]) tgEnd := by
    have hs := tgSetup_run wProofMulti rfl
    cases hs with
    | cons h1 r1 => cases r1 with
      | cons h2 r2 => cases r2 with
        | cons h3 r3 => cases r3 with
          | cons h4 r4 => cases r4 with
            | cons h5 r5 => cases r5 with
              | nil => exact TimedRun35.cons h1 (TimedRun35.cons h2 (TimedRun35.cons h3
                  (TimedRun35.cons h4 (TimedRun35.cons h5 (TimedRun35.cons hup TimedRun35.nil)))))
  refine ⟨FreshSystemSatisfiesInvariant wWorld 100 (by decide), _, hrun, ?_, ⟨_, rfl, rfl, rfl⟩,
    rfl, rfl, rfl⟩
  intro l hl
  simp only [wTimingGateSetup, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hl
  rcases hl with h | h | h | h | h | h <;> subst h <;> exact fun h => h

end Contracts.ChainTypeManager.UpgradeTimingAtV35
