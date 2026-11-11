import EraSpec.Contracts.ChainTypeManager.Properties.UpgradeTiming
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorForward

/-!
# Proofs: who may upgrade a chain, and when

Every upgrade step, whatever its path, carries one `DiamondUpgrade` record: the gates of
the diamond's `upgradeChainFromVersion` plus `ChainRouting`'s transition step
(`upgrade_inv`). The refinement results read the transition step off it. The gate results
read one field each. The CTM's own address passes the notifier gate vacuously, which is
the whole of the exemption (`diamond_exempt`). The countermodel and the witnesses are
concrete runs over the `ChainRouting` witness world.
-/

namespace Contracts.ChainTypeManager

/-! ## Reading an upgrade step -/

/-- Every upgrade step is one diamond call, at some version and with some caller at the
diamond, and changes only the routing system. -/
private lemma upgrade_inv {T : TimedConfig} {s s' : TimedSys} {id : ChainId}
    {path : UpgradePath} {caller : Address} {τ : ℕ}
    (h : TimedStep T s (.upgrade id path caller τ) s') :
    ∃ v c' sys', DiamondUpgrade T s id v c' τ sys' ∧ s' = { s with sys := sys' } := by
  cases h with
  | direct d => exact ⟨_, _, _, d, rfl⟩
  | ctm _ d => exact ⟨_, _, _, d, rfl⟩
  | executor _ _ _ d => exact ⟨_, _, _, d, rfl⟩

/-- The diamond call does not read the notifier when the caller is the chain's admin or its
CTM. -/
private lemma diamond_exempt {T : TimedConfig} {s : TimedSys} {id : ChainId} {v : ℕ}
    {caller : Address} {τ : ℕ} {sys' : Sys} (n : ChainId → ℕ → ℕ)
    (hc : caller = (s.aux id).admin ∨ caller = T.X.ctmProxy)
    (d : DiamondUpgrade T s id v caller τ sys') :
    DiamondUpgrade T { s with notifier := n } id v caller τ sys' :=
  ⟨d.authorized, d.atVersion, fun h1 h2 => (hc.elim h1 h2).elim, d.batchesExecuted, d.routing,
    d.manifestTime, d.settlementLayer⟩

/-- Both time gates are lower bounds. -/
private lemma diamond_later {T : TimedConfig} {s : TimedSys} {id : ChainId} {v : ℕ}
    {caller : Address} {τ τ' : ℕ} {sys' : Sys} (d : DiamondUpgrade T s id v caller τ sys')
    (hle : τ ≤ τ') : DiamondUpgrade T s id v caller τ' sys' :=
  ⟨d.authorized, d.atVersion,
    fun h1 h2 => ⟨(d.notifierGate h1 h2).1, le_trans (d.notifierGate h1 h2).2 hle⟩,
    d.batchesExecuted, d.routing, le_trans d.manifestTime hle, d.settlementLayer⟩

/-! ## The timed model refines the untimed one -/

theorem UpgradeIsATransition : Properties.UpgradeIsATransition := by
  intro T s s' id path caller τ h
  obtain ⟨_, _, _, d, rfl⟩ := upgrade_inv h
  exact ⟨d.routing, rfl, rfl⟩

private lemma run_append_routing {W : World} {s s' s'' : Sys} {l1 l2 : List Label}
    (h1 : Run W s l1 s') (h2 : Run W s' l2 s'') : Run W s (l1 ++ l2) s'' := by
  induction h1 with
  | nil => exact h2
  | cons hs _ ih => exact Run.cons hs (ih h2)

private lemma timedStep_untimed {T : TimedConfig} {s s' : TimedSys} {l : TimedLabel}
    (h : TimedStep T s l s') : Run T.X.W s.sys l.untimed s'.sys := by
  cases h with
  | direct d | ctm _ d | executor _ _ _ d => exact Run.cons d.routing Run.nil
  | base _ hs => exact Run.cons hs Run.nil
  | _ => exact Run.nil

theorem TimedRunIsARun : Properties.TimedRunIsARun := by
  intro T s s' ls h
  induction h with
  | nil => exact Run.nil
  | cons hs _ ih =>
      rw [List.flatMap_cons]
      exact run_append_routing (timedStep_untimed hs) ih

theorem TimedRunKeepsChainsOnTheirRelease : Properties.TimedRunKeepsChainsOnTheirRelease := by
  intro T s s' ls hI h hl
  refine ChainsRunTheirVersionsRelease T.X.W s.sys s'.sys _ hI (TimedRunIsARun T s s' ls h) ?_
  intro l hm
  obtain ⟨x, hx, hlx⟩ := List.mem_flatMap.mp hm
  cases x with
  | upgrade _ _ _ _ =>
      simp only [TimedLabel.untimed, List.mem_singleton] at hlx
      subst hlx
      exact fun h => h
  | base l' =>
      simp only [TimedLabel.untimed, List.mem_singleton] at hlx
      subst hlx
      exact hl _ hx
  | _ => simp [TimedLabel.untimed] at hlx

theorem TimedUpgradeChainIsAnXStep : Properties.TimedUpgradeChainIsAnXStep := by
  intro T s s' id t caller τ impl h
  cases h with
  | executor _ _ _ d => exact XStep.upgradeChain d.routing

/-! ## The chain sees the CTM as the caller -/

theorem CtmPathIsADiamondCallByTheCtm : Properties.CtmPathIsADiamondCallByTheCtm := by
  intro T s s' id v caller τ
  constructor
  · intro h
    cases h with
    | ctm hc d => exact ⟨hc, TimedStep.direct d⟩
  · rintro ⟨hc, h⟩
    cases h with
    | direct d => exact TimedStep.ctm hc d

theorem ExecutorPathIsACtmCallByTheExecutor :
    Properties.ExecutorPathIsACtmCallByTheExecutor := by
  intro T s s' id t caller τ
  constructor
  · intro h
    cases h with
    | executor hc hut hown d => exact ⟨hc, hut, TimedStep.ctm hown d⟩
  · rintro ⟨hc, hut, h⟩
    cases h with
    | ctm hown d => exact TimedStep.executor hc hut hown d

/-- One direction of the notifier independence of the executor path, for any state. -/
private lemma executor_renotify {T : TimedConfig} {s : TimedSys} {id : ChainId}
    {t caller : Address} {τ : ℕ} {s' : TimedSys} (n : ChainId → ℕ → ℕ)
    (h : TimedStep T s (.upgrade id (.executor t) caller τ) s') :
    TimedStep T { s with notifier := n } (.upgrade id (.executor t) caller τ)
      { s' with notifier := n } := by
  cases h with
  | executor hc hut hown d =>
      exact TimedStep.executor hc hut hown (diamond_exempt n (Or.inr rfl) d)

theorem ExecutorPathIgnoresNotifier : Properties.ExecutorPathIgnoresNotifier := by
  intro T s id t caller τ n
  refine ⟨fun sys' => ⟨fun h => executor_renotify n h, fun h => ?_⟩, ⟨?_, ?_⟩⟩
  · exact executor_renotify (s := { s with notifier := n }) s.notifier h
  · rintro ⟨s', h⟩
    exact ⟨_, executor_renotify n h⟩
  · rintro ⟨s', h⟩
    exact ⟨_, executor_renotify (s := { s with notifier := n }) s.notifier h⟩

/-! ## The chain's own schedule -/

/-- One direction of the notifier independence of a direct call by the admin or the CTM. -/
private lemma direct_renotify {T : TimedConfig} {s : TimedSys} {id : ChainId} {v : ℕ}
    {caller : Address} {τ : ℕ} {s' : TimedSys} (n : ChainId → ℕ → ℕ)
    (hc : caller = (s.aux id).admin ∨ caller = T.X.ctmProxy)
    (h : TimedStep T s (.upgrade id (.direct v) caller τ) s') :
    TimedStep T { s with notifier := n } (.upgrade id (.direct v) caller τ)
      { s' with notifier := n } := by
  cases h with
  | direct d => exact TimedStep.direct (diamond_exempt n hc d)

theorem AdminAndCtmSkipTheNotifier : Properties.AdminAndCtmSkipTheNotifier := by
  intro T s id v caller τ n sys' hc
  exact ⟨fun h => direct_renotify n hc h,
    fun h => direct_renotify (s := { s with notifier := n }) s.notifier hc h⟩

theorem OtherCallersNeedTheNotifier : Properties.OtherCallersNeedTheNotifier := by
  intro T s s' id v caller τ h ha hc
  cases h with
  | direct d =>
      refine ⟨?_, d.notifierGate ha hc⟩
      rcases d.authorized with h1 | h1 | h1
      · exact absurd h1 ha
      · exact absurd h1 hc
      · exact h1

theorem NotifierWrittenOnlyByItsChainAdmin : Properties.NotifierWrittenOnlyByItsChainAdmin := by
  intro T s s' l id v h hne
  cases h with
  | @setUpgradeTimestamp id' caller ts c hc hcaller hts _ =>
      by_cases hid : id = id'
      · subst hid
        by_cases hv : v = c.pv
        · subst hv
          left
          exact ⟨caller, ts, c, rfl, hcaller, hc, rfl, hts, by simp [setNotifierEntry]⟩
        · exact absurd (by simp [setNotifierEntry, upd_ne _ _ hv]) hne
      · exact absurd (by simp [setNotifierEntry, upd_ne _ _ hid]) hne
  | swapNotifier => exact Or.inr ⟨_, rfl⟩
  | _ => exact absurd rfl hne

/-! ## The engine's gates bind every path -/

theorem ManifestTimestampGates : Properties.ManifestTimestampGates := by
  intro T s s' id path caller τ h
  obtain ⟨v, _, _, d, _⟩ := upgrade_inv h
  obtain ⟨c, hc, hv⟩ := d.atVersion
  refine ⟨c, hc, ?_⟩
  rw [hv]
  exact d.manifestTime

theorem EveryPathNeedsExecutedBatches : Properties.EveryPathNeedsExecutedBatches := by
  intro T s s' id path caller τ h
  obtain ⟨_, _, _, d, _⟩ := upgrade_inv h
  exact d.batchesExecuted

theorem EveryPathNeedsTheSettlementLayerAhead :
    Properties.EveryPathNeedsTheSettlementLayerAhead := by
  intro T s s' id path caller τ w h hw
  obtain ⟨v, _, _, d, _⟩ := upgrade_inv h
  obtain ⟨c, hc, hv⟩ := d.atVersion
  refine ⟨c, hc, ?_⟩
  rw [hv]
  exact d.settlementLayer w hw

theorem UpgradeStaysEnabledLater : Properties.UpgradeStaysEnabledLater := by
  intro T s s' id path caller τ τ' h hle
  cases h with
  | direct d => exact TimedStep.direct (diamond_later d hle)
  | ctm hc d => exact TimedStep.ctm hc (diamond_later d hle)
  | executor hc hut hown d => exact TimedStep.executor hc hut hown (diamond_later d hle)

/-! ## The repaired NatSpec -/

theorem UpgradeChainEnabledIffTimed : Properties.UpgradeChainEnabledIffTimed := by
  intro T s id t caller τ
  constructor
  · rintro ⟨s', h⟩
    cases h with
    | executor hc hut hown d =>
        obtain ⟨c, hc', hv⟩ := d.atVersion
        refine ⟨hc, hut, hown, ⟨c, hc', hv⟩, ?_, d.batchesExecuted, ?_, ⟨_, d.routing⟩⟩
        · have h1 := d.manifestTime
          rwa [hut] at h1
        · intro w hw
          have h1 := d.settlementLayer w hw
          simp only [Sys.edge] at h1
          rwa [hut] at h1
  · rintro ⟨hc, hut, hown, ⟨c, hc', hv⟩, hts, hb, hsl, sys', hstep⟩
    refine ⟨_, TimedStep.executor hc hut hown
      ⟨Or.inr (Or.inl rfl), ⟨c, hc', hv⟩, fun _ h => absurd rfl h, hb, hstep, ?_, ?_⟩⟩
    · rw [hut]
      exact hts
    · intro w hw
      simp only [Sys.edge]
      rw [hut]
      exact hsl w hw

/-! ## The departing version's deadline -/

theorem ValidEdgeHasNoDeadTime : Properties.ValidEdgeHasNoDeadTime := by
  intro T d s v τ hut hd hval
  obtain ⟨_, hle⟩ := hval
  have hdl : versionDeadline T d s v = some (T.sched (s.ut v)).deadline := by
    simp [versionDeadline, hd, hut]
  refine ⟨?_, ?_⟩
  · by_cases h : τ ≤ (T.sched (s.ut v)).deadline
    · left
      intro x hx
      rw [hdl] at hx
      cases hx
      exact h
    · right
      omega
  · intro x hx
    rw [hdl] at hx
    cases hx
    exact hle

/-! ## The countermodel and the witnesses

All concrete states are over the `ChainRouting` witness world. `tSetup` is the state
`wTimingSetup` reaches: chain `0` at version 1 on release `100` with `wTimingAux`, transition
`300` committed, and the chain's own entry for version 1 at `12`. -/

/-- The routing system after the setup. -/
private def tSetupSys : Sys :=
  ⟨⟨2, 200, upd (fun _ => 0) 1 300, fun _ => LegacyCut.none, upd (upd (fun _ => 0) 1 100) 2 200⟩,
    upd (fun _ => none) 0 (some ⟨1, rowsRouting (wRows 100)⟩)⟩

/-- The timed state after the setup. -/
private def tSetup : TimedSys :=
  ⟨tSetupSys, upd (fun _ => ⟨0, fun _ => false, 0, 0, none⟩) 0 wTimingAux,
    setNotifierEntry (fun _ _ => 0) 0 1 12⟩

private lemma tSetup_run : TimedRun wTiming wTimingSys0 wTimingSetup tSetup :=
  TimedRun.cons (TimedStep.base (l := .genesis 0) (fun h => h)
      (Step.genesis rfl (addAll_empty_eq xNodup100)))
    (TimedRun.cons TimedStep.setAux
      (TimedRun.cons (TimedStep.base (l := .ctm (.commit 300)) (fun h => h)
          (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide))))
        (TimedRun.cons (TimedStep.setUpgradeTimestamp (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl
            (by decide) (Or.inl (by decide)))
          TimedRun.nil)))

/-- Chain `0`'s routing transition after the setup. -/
private lemma tSetup_transition : Step wWorld tSetupSys (.transition 0)
    { tSetupSys with chains := upd tSetupSys.chains 0 (some ⟨2, rowsRouting (wRows 200)⟩) } :=
  Step.transition (s := tSetupSys) (id := 0) rfl (by decide) rfl
    (applyDerived_rows_eq xNodup100 xNodup200) (by decide)

private lemma tSetupSys_chain0 {c : Chain} (hc : tSetupSys.chains 0 = some c) : c.pv = 1 := by
  have : c = ⟨1, rowsRouting (wRows 100)⟩ := (Option.some.inj (hc.symm.trans rfl) :)
  subst this
  rfl

/-- Before the manifest's time nobody upgrades chain `0`, by any path. -/
private lemma tSetup_none_before (aux : ChainId → DiamondAux) (n : ChainId → ℕ → ℕ) {τ : ℕ}
    (hτ : τ < 10) (path : UpgradePath) (caller : Address) :
    ¬ ∃ s', TimedStep wTiming ⟨tSetupSys, aux, n⟩ (.upgrade 0 path caller τ) s' := by
  rintro ⟨s', h⟩
  obtain ⟨c, hc, hle⟩ := ManifestTimestampGates _ _ _ _ _ _ _ h
  have hpv := tSetupSys_chain0 hc
  have h300 : (wTiming.sched (tSetupSys.ctm.ut c.pv)).upgradeTimestamp = 10 := by
    rw [hpv]
    rfl
  change (wTiming.sched (tSetupSys.ctm.ut c.pv)).upgradeTimestamp ≤ τ at hle
  omega

/-- `upgradeChain(300, 0)` from any state with the setup's routing, once its gates pass. -/
private lemma tSetup_exec (aux : ChainId → DiamondAux) (n : ChainId → ℕ → ℕ) {caller : Address}
    {τ : ℕ} (hc : caller = 2 ∨ caller = (aux 0).admin) (hτ : 10 ≤ τ)
    (hb : (aux 0).committed = (aux 0).executed) (hsl : ∀ w, (aux 0).slVersion = some w → 2 ≤ w) :
    ∃ s', TimedStep wTiming ⟨tSetupSys, aux, n⟩ (.upgrade 0 (.executor 300) caller τ) s' :=
  (UpgradeChainEnabledIffTimed wTiming ⟨tSetupSys, aux, n⟩ 0 300 caller τ).mpr
    ⟨hc, rfl, rfl, ⟨_, rfl, rfl⟩, hτ, hb, hsl, ⟨_, tSetup_transition⟩⟩

theorem NotAtAnyTime : Properties.NotAtAnyTime := by
  refine ⟨tSetup, tSetup_run, by decide, rfl, ⟨_, rfl, rfl⟩, rfl, rfl,
    fun t => tSetup_none_before _ _ (by decide) _ _,
    fun t => tSetup_none_before _ _ (by decide) _ _,
    fun path caller => tSetup_none_before _ _ (by decide) path caller, ?_, ?_⟩
  · exact tSetup_exec _ _ (Or.inl rfl) le_rfl rfl (fun w hw => by cases hw)
  · exact tSetup_exec _ _ (Or.inr rfl) le_rfl rfl (fun w hw => by cases hw)

theorem UpgradeChainIsNotTimeIndependent : Properties.UpgradeChainIsNotTimeIndependent := by
  obtain ⟨s, _, _, _, _, _, hadm, h9o, h9a, _, h10o, h10a⟩ := NotAtAnyTime
  refine ⟨fun H => h9o 300 (H wTiming s 0 300 10 9 h10o), fun H => h9a 300 ?_⟩
  have h := H wTiming s 0 300 10 9 (by rw [hadm]; exact h10a)
  rwa [hadm] at h

/-- The routing system after `replaceUpgradeTransition(300, 400)` in the setup state. -/
private def tReplSys : Sys :=
  ⟨{ tSetupSys.ctm with ut := upd tSetupSys.ctm.ut 1 400 }, tSetupSys.chains⟩

/-- The timed state after the replacement. -/
private def tRepl : TimedSys := { tSetup with sys := tReplSys }

private lemma tRepl_step : TimedStep wTiming tSetup (.base (.ctm (.replace 300 400))) tRepl :=
  TimedStep.base (fun h => h) (Step.ctm (CStep.replace (s := tSetupSys.ctm) (e := 300) (r := 400)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)))

/-- Chain `0`'s routing transition after the replacement. -/
private lemma tRepl_transition : Step wWorld tReplSys (.transition 0)
    { tReplSys with chains := upd tReplSys.chains 0 (some ⟨2, rowsRouting (wRows 200)⟩) } :=
  Step.transition (s := tReplSys) (id := 0) rfl (by decide) rfl
    (applyDerived_rows_eq xNodup100 xNodup200) (by decide)

theorem ReplacementMovesTheTimeGate : Properties.ReplacementMovesTheTimeGate := by
  refine ⟨tSetup, tRepl, tSetup_run, tRepl_step, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    rfl, tSetup_exec _ _ (Or.inl rfl) (by decide) rfl (fun w hw => by cases hw), ?_, ?_⟩
  · rintro path caller ⟨s'', h⟩
    obtain ⟨c, hc, hle⟩ := ManifestTimestampGates _ _ _ _ _ _ _ h
    have hpv : c.pv = 1 := tSetupSys_chain0 hc
    have h15 : (wTiming.sched (tReplSys.ctm.ut c.pv)).upgradeTimestamp = 15 := by
      rw [hpv]
      rfl
    change (wTiming.sched (tReplSys.ctm.ut c.pv)).upgradeTimestamp ≤ 12 at hle
    omega
  · exact (UpgradeChainEnabledIffTimed wTiming tRepl 0 400 2 15).mpr
      ⟨Or.inl rfl, rfl, rfl, ⟨_, rfl, rfl⟩, by decide, rfl, (fun w hw => by cases hw),
        ⟨_, tRepl_transition⟩⟩

theorem DeadlineOverrideOpensDeadTime : Properties.DeadlineOverrideOpensDeadTime := by
  have hc : CStep wWorld (initState wWorld 100) (.commit 300) _ :=
    CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hval : ValidSchedule wTiming 300 := ⟨by decide, by decide⟩
  refine ⟨_, CRun.cons hc CRun.nil, by decide, hval, fun τ => ?_, fun h => ?_, by decide⟩
  · exact (ValidEdgeHasNoDeadTime wTiming (fun _ => 0) _ 1 τ (by decide) rfl hval).1
  · have h1 := h 1 rfl
    omega

theorem EachGateIsLoadBearing : Properties.EachGateIsLoadBearing := by
  refine ⟨tSetup, tSetup_run, rfl, rfl, rfl, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the validator waits for the chain's own time
  · rintro ⟨s', h⟩
    have := OtherCallersNeedTheNotifier _ _ _ _ _ _ _ h (by decide) (by decide)
    exact absurd this.2.2 (by decide)
  · exact ⟨_, TimedStep.direct ⟨Or.inr (Or.inr rfl), ⟨_, rfl, rfl⟩,
      fun _ _ => ⟨by decide, by decide⟩, rfl, tSetup_transition, by decide,
      fun w hw => by cases hw⟩⟩
  · rintro ⟨s', h⟩
    have := OtherCallersNeedTheNotifier _ _ _ _ _ _ _ h (by decide) (by decide)
    exact this.2.1 rfl
  -- neither the executor nor the admin does
  · exact tSetup_exec _ _ (Or.inl rfl) (by decide) rfl (fun w hw => by cases hw)
  · exact ⟨_, TimedStep.direct ⟨Or.inl rfl, ⟨_, rfl, rfl⟩, fun h _ => absurd rfl h, rfl,
      tSetup_transition, by decide, fun w hw => by cases hw⟩⟩
  -- an unexecuted batch blocks every path
  · rintro path caller τ ⟨s', h⟩
    have := EveryPathNeedsExecutedBatches _ _ _ _ _ _ _ h
    exact absurd this (by decide)
  -- a settlement layer behind the target blocks every path
  · rintro path caller τ ⟨s', h⟩
    obtain ⟨c, hc, hle⟩ := EveryPathNeedsTheSettlementLayerAhead _ _ _ _ _ _ _ 1 h rfl
    have hpv := tSetupSys_chain0 hc
    have h2 : (tSetupSys.edge wWorld c.pv).new = 2 := by
      rw [hpv]
      rfl
    change (tSetupSys.edge wWorld c.pv).new ≤ 1 at hle
    omega
  -- one at the target does not
  · exact tSetup_exec _ _ (Or.inl rfl) le_rfl rfl (fun w hw => by cases hw; decide)

theorem UpgradeTimingWitness : Properties.UpgradeTimingWitness := by
  have hrun : TimedRun wTiming wTimingSys0 wTimingRun _ :=
    TimedRun.cons (TimedStep.base (l := .genesis 0) (fun h => h)
        (Step.genesis rfl (addAll_empty_eq xNodup100)))
    (TimedRun.cons TimedStep.setAux
    (TimedRun.cons (TimedStep.base (l := .genesis 1) (fun h => h)
        (Step.genesis rfl (addAll_empty_eq xNodup100)))
    (TimedRun.cons TimedStep.setAux
    (TimedRun.cons (TimedStep.base (l := .genesis 2) (fun h => h)
        (Step.genesis rfl (addAll_empty_eq xNodup100)))
    (TimedRun.cons TimedStep.setAux
    (TimedRun.cons (TimedStep.base (l := .ctm (.commit 300)) (fun h => h)
        (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide))))
    (TimedRun.cons (TimedStep.setUpgradeTimestamp (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl
        (by decide) (Or.inl (by decide)))
    (TimedRun.cons (TimedStep.executor (Or.inr rfl) (by decide) rfl
        ⟨Or.inr (Or.inl rfl), ⟨_, rfl, rfl⟩, fun _ h => absurd rfl h, rfl,
          Step.transition rfl (by decide) rfl (applyDerived_rows_eq xNodup100 xNodup200)
            (by decide), by decide, fun w hw => by cases hw⟩)
    (TimedRun.cons (TimedStep.ctm rfl
        ⟨Or.inr (Or.inl rfl), ⟨_, rfl, rfl⟩, fun _ h => absurd rfl h, rfl,
          Step.transition rfl (by decide) rfl (applyDerived_rows_eq xNodup100 xNodup200)
            (by decide), by decide, fun w hw => by cases hw⟩)
    (TimedRun.cons (TimedStep.direct
        ⟨Or.inr (Or.inr rfl), ⟨_, rfl, rfl⟩, fun _ _ => ⟨by decide, by decide⟩, rfl,
          Step.transition rfl (by decide) rfl (applyDerived_rows_eq xNodup100 xNodup200)
            (by decide), by decide, fun w hw => by cases hw⟩)
    TimedRun.nil))))))))))
  refine ⟨FreshSystemSatisfiesInvariant wWorld 100 (by decide), ?_, _, hrun, rfl, by decide,
    by decide, ?_⟩
  · intro l hl
    simp only [wTimingRun, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> exact fun h => h
  · intro id hid
    interval_cases id <;> exact ⟨_, rfl, rfl, rfl⟩

end Contracts.ChainTypeManager
