import EraSpec.Contracts.ChainTypeManager.Properties.UpgradeTimingStrong
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTiming
import EraSpec.Contracts.ChainTypeManager.Proofs.Enabledness

/-!
# Proofs: no dead time along timed runs

A timed run is a routing run of its labels' untimed images (`TimedRunIsARun`). An upgrade's
image is a transition, which writes no slot and installs no release. So each premise on timed
labels becomes the same premise on routing labels (`untimed_lift`), and the two slot facts are
carried by induction over routing runs: valid schedules (`run_slotSchedulesValid`, no invariant
needed) and pinned deadlines (`run_keepsDeadline`, under `CtmInv`, because a commit writes only
the empty slot of the current version).

The headline combines three results. `ValidatedRunsKeepEverythingEnabled` gives the routing
transition at the end of the run. `ReachableSlotsHaveValidSchedules` gives the slot's valid
schedule. The remaining gates of `DiamondUpgrade` come from the chain's premises
(`upgrades_of_gates`). Then split on whether `τ` is past the deadline: a valid schedule puts the
upgrade timestamp at or before it.

The witnesses run over the `UpgradeTiming` witness world. A run with no upgrade reads no
schedule, so the same run reaches the same state under each variant of `wTiming`
(`timedRun_reconfig`). Each countermodel reads one gate off an upgrade step
(`ManifestTimestampGates`, `EveryPathNeedsExecutedBatches`,
`EveryPathNeedsTheSettlementLayerAhead`, and `DriftBlocksTransition` through
`UpgradeIsATransition`).
-/

namespace Contracts.ChainTypeManager

/-! ## From timed labels to routing labels -/

/-- A premise on every label of a timed run gives one on every label of its untimed image,
provided it holds of every transition and passes from a base step to its routing label. -/
private lemma untimed_lift {P : Label → Prop} {Q : TimedLabel → Prop}
    (htr : ∀ id, P (.transition id)) (hbase : ∀ l, Q (.base l) → P l)
    {ls : List TimedLabel} (h : ∀ x ∈ ls, Q x) : ∀ l ∈ ls.flatMap TimedLabel.untimed, P l := by
  intro l hl
  obtain ⟨x, hx, hlx⟩ := List.mem_flatMap.mp hl
  cases x with
  | upgrade id _ _ _ =>
      simp only [TimedLabel.untimed, List.mem_singleton] at hlx
      subst hlx
      exact htr id
  | base l' =>
      simp only [TimedLabel.untimed, List.mem_singleton] at hlx
      subst hlx
      exact hbase _ (h _ hx)
  | setUpgradeTimestamp _ _ _ => simp [TimedLabel.untimed] at hlx
  | swapNotifier _ => simp [TimedLabel.untimed] at hlx
  | setAux _ _ => simp [TimedLabel.untimed] at hlx

/-! ## Every reachable slot has a valid schedule -/

/-- One CTM writer keeps every slot's schedule valid, given what it records. -/
private lemma cstep_slotSchedulesValid {T : TimedConfig} {W : World} {s s' : CTM} {op : Op}
    (hV : SlotSchedulesValid T s) (h : CStep W s op s') (hop : op.CommitsValidSchedule T) :
    SlotSchedulesValid T s' := by
  intro v hv
  cases h with
  | @commit t _ _ _ _ _ _ =>
      dsimp only at hv ⊢
      by_cases hvo : v = (W.tr t).old
      · subst hvo
        simp only [upd_same]
        exact hop
      · rw [upd_ne _ _ hvo] at hv ⊢
        exact hV v hv
  | @replace e r _ _ _ _ _ _ _ _ =>
      dsimp only at hv ⊢
      by_cases hvo : v = (W.tr e).old
      · subst hvo
        simp only [upd_same]
        exact hop
      · rw [upd_ne _ _ hvo] at hv ⊢
        exact hV v hv
  | legacyCommit _ _ => exact hV v hv
  | legacyRecut _ _ => exact hV v hv

private lemma step_slotSchedulesValid {T : TimedConfig} {W : World} {s s' : Sys} {l : Label}
    (hV : SlotSchedulesValid T s.ctm) (h : Step W s l s') (hl : l.CommitsValidSchedule T) :
    SlotSchedulesValid T s'.ctm := by
  cases h with
  | ctm hc => exact cstep_slotSchedulesValid hV hc hl
  | genesis _ _ => exact hV
  | migrateIn _ _ _ _ => exact hV
  | transition _ _ _ _ _ => exact hV
  | bootstrapReset _ _ _ _ => exact hV
  | arbitraryCut _ _ _ => exact hV

private lemma run_slotSchedulesValid {T : TimedConfig} {W : World} {s s' : Sys}
    {ls : List Label} (hV : SlotSchedulesValid T s.ctm) (h : Run W s ls s')
    (hl : ∀ l ∈ ls, l.CommitsValidSchedule T) : SlotSchedulesValid T s'.ctm := by
  induction h with
  | nil => exact hV
  | cons hs _ ih =>
      exact ih (step_slotSchedulesValid hV hs (hl _ List.mem_cons_self))
        (fun l hm => hl l (List.mem_cons_of_mem _ hm))

theorem ReachableSlotsHaveValidSchedules : Properties.ReachableSlotsHaveValidSchedules := by
  intro T s s' ls hV h hl
  exact run_slotSchedulesValid hV (TimedRunIsARun T s s' ls h)
    (untimed_lift (fun _ => trivial) (fun _ h => h) hl)

/-! ## The headline -/

/-- What `protocolVersionDeadline(v)` returns for a version with a committed edge and no
override: the committed transition's pinned deadline. -/
private lemma versionDeadline_committed {T : TimedConfig} {d : ℕ → ℕ} {s : CTM} {v : ℕ}
    (hut : s.ut v ≠ 0) (hd : d v = 0) :
    versionDeadline T d s v = some (T.sched (s.ut v)).deadline := by
  simp [versionDeadline, hd, hut]

/-- With every gate of the diamond passing, the chain's admin can upgrade it directly and the
CTM's owner through the CTM, both landing it on the arriving release. -/
private lemma upgrades_of_gates {T : TimedConfig} {s : TimedSys} {id : ChainId} {c : Chain}
    {τ : ℕ} (hc : s.sys.chains id = some c)
    (hb : (s.aux id).committed = (s.aux id).executed)
    (hsl : ∀ w, (s.aux id).slVersion = some w → (s.sys.edge T.X.W c.pv).new ≤ w)
    (hstep : Step T.X.W s.sys (.transition id) (s.sys.crossEdge T.X.W id c))
    (hτ : (T.sched (s.sys.ctm.ut c.pv)).upgradeTimestamp ≤ τ) :
    TimedStep T s (.upgrade id (.direct c.pv) (s.aux id).admin τ)
        { s with sys := s.sys.crossEdge T.X.W id c } ∧
      TimedStep T s (.upgrade id (.ctm c.pv) T.ctmOwner τ)
        { s with sys := s.sys.crossEdge T.X.W id c } :=
  ⟨TimedStep.direct ⟨Or.inl rfl, ⟨c, hc, rfl⟩, fun h => absurd rfl h, hb, hstep, hτ, hsl⟩,
    TimedStep.ctm rfl
      ⟨Or.inr (Or.inl rfl), ⟨c, hc, rfl⟩, fun _ h => absurd rfl h, hb, hstep, hτ, hsl⟩⟩

theorem ValidatedTimedRunsHaveNoDeadTime : Properties.ValidatedTimedRunsHaveNoDeadTime := by
  intro T d s s' ls hI hR hV h hl hw hv id c hc hut hd hb hsl
  have hrun := TimedRunIsARun T s s' ls h
  have hl' : ∀ l ∈ ls.flatMap TimedLabel.untimed, ¬ l.isArbitrary :=
    untimed_lift (fun _ h => h) (fun _ h => h) hl
  have hw' : ∀ l ∈ ls.flatMap TimedLabel.untimed, l.InstallsWf T.X.W :=
    untimed_lift (fun _ => trivial) (fun _ h => h) hw
  have hstep := (ValidatedRunsKeepEverythingEnabled T.X.W s.sys s'.sys _ hI hR hrun hl' hw').1
    id c hc hut
  obtain ⟨_, hle⟩ := ReachableSlotsHaveValidSchedules T s s' ls hV h hv c.pv hut
  have hdl := versionDeadline_committed (T := T) hut hd
  have hact : ∀ τ, τ ≤ (T.sched (s'.sys.ctm.ut c.pv)).deadline →
      ProtocolVersionActive T d s'.sys.ctm c.pv τ := by
    intro τ hτ x hx
    rw [hdl] at hx
    cases hx
    exact hτ
  have hcross := fun τ (hτ : (T.sched (s'.sys.ctm.ut c.pv)).upgradeTimestamp ≤ τ) =>
    upgrades_of_gates (T := T) hc hb hsl hstep hτ
  have hwin : ∀ τ, ProtocolVersionActive T d s'.sys.ctm c.pv τ ∨
      (TimedStep T s' (.upgrade id (.direct c.pv) (s'.aux id).admin τ)
          { s' with sys := s'.sys.crossEdge T.X.W id c } ∧
        TimedStep T s' (.upgrade id (.ctm c.pv) T.ctmOwner τ)
          { s' with sys := s'.sys.crossEdge T.X.W id c }) := by
    intro τ
    by_cases hτ : τ ≤ (T.sched (s'.sys.ctm.ut c.pv)).deadline
    · exact Or.inl (hact τ hτ)
    · exact Or.inr (hcross τ (by omega))
  refine ⟨fun τ hdead => ?_, hwin, hact _ hle, hcross _ le_rfl⟩
  obtain ⟨c', hc', hna, hno⟩ := hdead
  rw [hc] at hc'
  cases hc'
  rcases hwin τ with hA | ⟨hD, _⟩
  · exact hna hA
  · exact hno _ _ ⟨_, hD⟩

/-! ## The deadline does not move -/

/-- One CTM writer keeps a committed slot committed, with the same pinned deadline, provided a
replacement keeps the deadline. A commit cannot reach a committed slot: it writes the slot of the
current version, and every committed slot lies below it. -/
private lemma cstep_keepsDeadline {T : TimedConfig} {W : World} {s s' : CTM} {op : Op}
    (hI : CtmInv W s) (h : CStep W s op s') (hop : op.KeepsDeadline T) {v : ℕ}
    (hv : s.ut v ≠ 0) :
    s'.ut v ≠ 0 ∧ (T.sched (s'.ut v)).deadline = (T.sched (s.ut v)).deadline := by
  cases h with
  | @commit t _ _ hpv _ _ _ =>
      have hlt := (hI.slots v hv).1
      have hvo : v ≠ (W.tr t).old := by omega
      dsimp only
      rw [upd_ne _ _ hvo]
      exact ⟨hv, rfl⟩
  | @replace e r _ hr0 hslot _ _ _ _ _ =>
      dsimp only
      by_cases hvo : v = (W.tr e).old
      · subst hvo
        simp only [upd_same]
        rw [hslot]
        exact ⟨hr0, hop⟩
      · rw [upd_ne _ _ hvo]
        exact ⟨hv, rfl⟩
  | legacyCommit _ _ => exact ⟨hv, rfl⟩
  | legacyRecut _ _ => exact ⟨hv, rfl⟩

private lemma step_keepsDeadline {T : TimedConfig} {W : World} {s s' : Sys} {l : Label}
    (hI : CtmInv W s.ctm) (h : Step W s l s') (hl : l.KeepsDeadline T) {v : ℕ}
    (hv : s.ctm.ut v ≠ 0) :
    s'.ctm.ut v ≠ 0 ∧ (T.sched (s'.ctm.ut v)).deadline = (T.sched (s.ctm.ut v)).deadline := by
  cases h with
  | ctm hc => exact cstep_keepsDeadline hI hc hl hv
  | genesis _ _ => exact ⟨hv, rfl⟩
  | migrateIn _ _ _ _ => exact ⟨hv, rfl⟩
  | transition _ _ _ _ _ => exact ⟨hv, rfl⟩
  | bootstrapReset _ _ _ _ => exact ⟨hv, rfl⟩
  | arbitraryCut _ _ _ => exact ⟨hv, rfl⟩

private lemma run_keepsDeadline {T : TimedConfig} {W : World} {s s' : Sys} {ls : List Label}
    (hI : CtmInv W s.ctm) (h : Run W s ls s') (hl : ∀ l ∈ ls, l.KeepsDeadline T) {v : ℕ}
    (hv : s.ctm.ut v ≠ 0) :
    s'.ctm.ut v ≠ 0 ∧ (T.sched (s'.ctm.ut v)).deadline = (T.sched (s.ctm.ut v)).deadline := by
  induction h with
  | nil => exact ⟨hv, rfl⟩
  | cons hs _ ih =>
      obtain ⟨hv1, hd1⟩ := step_keepsDeadline hI hs (hl _ List.mem_cons_self) hv
      obtain ⟨hv2, hd2⟩ :=
        ih (step_ctmInv hI hs) (fun l hm => hl l (List.mem_cons_of_mem _ hm)) hv1
      exact ⟨hv2, hd2.trans hd1⟩

theorem SameDeadlineReplacementsFixTheDeadline :
    Properties.SameDeadlineReplacementsFixTheDeadline := by
  intro T d s s' ls hI h hl v hv
  obtain ⟨hv', hdl⟩ := run_keepsDeadline hI (TimedRunIsARun T s s' ls h)
    (untimed_lift (fun _ => trivial) (fun _ h => h) hl) hv
  have heq : versionDeadline T d s'.sys.ctm v = versionDeadline T d s.sys.ctm v := by
    simp [versionDeadline, hv', hv, hdl]
  refine ⟨hv', heq, fun τ => ?_⟩
  unfold ProtocolVersionActive
  rw [heq]

/-! ## The witness states

`dSetup` is the state the run `wTimingSetup` reaches, under `wTiming` and under each of its two
variants, since no step of that run reads a schedule. In it chain `0` is at version 1 on release
`100` with `wTimingAux`, transition `300` is committed, and the chain's own notifier entry for
version 1 is `12`. `dRepl` is the state after `replaceUpgradeTransition(300, 400)`. -/

/-- The routing system after the setup. -/
private def dSetupSys : Sys :=
  ⟨⟨2, 200, upd (fun _ => 0) 1 300, fun _ => LegacyCut.none, upd (upd (fun _ => 0) 1 100) 2 200⟩,
    upd (fun _ => none) 0 (some ⟨1, rowsRouting (wRows 100)⟩)⟩

/-- The timed state after the setup. -/
private def dSetup : TimedSys :=
  ⟨dSetupSys, upd (fun _ => ⟨0, fun _ => false, 0, 0, none⟩) 0 wTimingAux,
    setNotifierEntry (fun _ _ => 0) 0 1 12⟩

/-- The routing system after the replacement. -/
private def dReplSys : Sys :=
  ⟨{ dSetupSys.ctm with ut := upd dSetupSys.ctm.ut 1 400 }, dSetupSys.chains⟩

/-- The timed state after the replacement. -/
private def dRepl : TimedSys := { dSetup with sys := dReplSys }

/-- A timed step that is not an upgrade reads no schedule and no owner, so it is a step under
every configuration with the same executor configuration. -/
private lemma timedStep_reconfig {T T' : TimedConfig} (hX : T'.X = T.X) {s s' : TimedSys}
    {l : TimedLabel} (h : TimedStep T s l s')
    (hl : ∀ id path caller τ, l ≠ .upgrade id path caller τ) : TimedStep T' s l s' := by
  cases h with
  | direct _ => exact absurd rfl (hl _ _ _ _)
  | ctm _ _ => exact absurd rfl (hl _ _ _ _)
  | executor _ _ _ _ => exact absurd rfl (hl _ _ _ _)
  | base hnt hs => exact TimedStep.base hnt (hX ▸ hs)
  | setUpgradeTimestamp hc ha hts hcom => exact TimedStep.setUpgradeTimestamp hc ha hts hcom
  | swapNotifier => exact TimedStep.swapNotifier
  | setAux => exact TimedStep.setAux

private lemma timedRun_reconfig {T T' : TimedConfig} (hX : T'.X = T.X) {s s' : TimedSys}
    {ls : List TimedLabel} (h : TimedRun T s ls s')
    (hl : ∀ l ∈ ls, ∀ id path caller τ, l ≠ .upgrade id path caller τ) :
    TimedRun T' s ls s' := by
  induction h with
  | nil => exact TimedRun.nil
  | cons hs _ ih =>
      exact TimedRun.cons (timedStep_reconfig hX hs (hl _ List.mem_cons_self))
        (ih (fun l hm => hl l (List.mem_cons_of_mem _ hm)))

/-- The run `wTimingSetup`. -/
private lemma dSetup_run : TimedRun wTiming wTimingSys0 wTimingSetup dSetup :=
  TimedRun.cons (TimedStep.base (l := .genesis 0) (fun h => h)
      (Step.genesis rfl (addAll_empty_eq xNodup100)))
    (TimedRun.cons TimedStep.setAux
      (TimedRun.cons (TimedStep.base (l := .ctm (.commit 300)) (fun h => h)
          (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide))))
        (TimedRun.cons (TimedStep.setUpgradeTimestamp (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl
            (by decide) (Or.inl (by decide)))
          TimedRun.nil)))

/-- The run `wTimingSetup` has no upgrade. -/
private lemma dSetup_no_upgrade :
    ∀ l ∈ wTimingSetup, ∀ id path caller τ, l ≠ TimedLabel.upgrade id path caller τ := by
  intro l hl id path caller τ heq
  simp only [wTimingSetup, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;> cases heq

/-- The run `wTimingSetup` under either variant of `wTiming`. -/
private lemma dSetup_run_bad : TimedRun wBadSchedTiming wTimingSys0 wTimingSetup dSetup :=
  timedRun_reconfig (T := wTiming) (T' := wBadSchedTiming) rfl dSetup_run dSetup_no_upgrade

private lemma dSetup_run_short : TimedRun wShortDeadlineTiming wTimingSys0 wTimingSetup dSetup :=
  timedRun_reconfig (T := wTiming) (T' := wShortDeadlineTiming) rfl dSetup_run dSetup_no_upgrade

/-- `replaceUpgradeTransition(300, 400)` in the setup state. -/
private lemma dRepl_step : TimedStep wTiming dSetup (.base (.ctm (.replace 300 400))) dRepl :=
  TimedStep.base (fun h => h) (Step.ctm (CStep.replace (s := dSetupSys.ctm) (e := 300) (r := 400)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)))

private lemma dRepl_step_short :
    TimedStep wShortDeadlineTiming dSetup (.base (.ctm (.replace 300 400))) dRepl :=
  timedStep_reconfig (T := wTiming) (T' := wShortDeadlineTiming) rfl dRepl_step
    (fun _ _ _ _ heq => by cases heq)

/-- The routing system after a break-glass cut adds selector `9` to chain `0` in the setup
state. -/
private def dDriftSys : Sys :=
  { dSetupSys with chains := upd dSetupSys.chains 0 (some ⟨1, bgExtra⟩) }

/-- The setup state satisfies the CTM invariant. -/
private lemma dSetup_ctmInv : CtmInv wWorld dSetupSys.ctm :=
  run_ctmInv (s := wSys0) (InitSatisfiesInvariant wWorld 100 (by decide))
    (TimedRunIsARun _ _ _ _ dSetup_run)

private lemma dSetupSys_chain0 {c : Chain} (hc : dSetupSys.chains 0 = some c) :
    c = ⟨1, rowsRouting (wRows 100)⟩ :=
  (Option.some.inj (hc.symm.trans rfl) :)

/-- Version 1's deadline in the setup state without an override: `300`'s pinned deadline. -/
private lemma dSetup_deadline (f : Address → TransitionSchedule) :
    versionDeadline ⟨wX, f, 1, 2⟩ (fun _ => 0) dSetupSys.ctm 1 = some (f 300).deadline :=
  versionDeadline_committed (s := dSetupSys.ctm) (v := 1) (by decide) rfl

/-- Version 1's deadline after the replacement without an override: `400`'s pinned deadline. -/
private lemma dRepl_deadline (f : Address → TransitionSchedule) :
    versionDeadline ⟨wX, f, 1, 2⟩ (fun _ => 0) dReplSys.ctm 1 = some (f 400).deadline :=
  versionDeadline_committed (s := dReplSys.ctm) (v := 1) (by decide) rfl

private lemma active_of {T : TimedConfig} {d : ℕ → ℕ} {s : CTM} {v τ x : ℕ}
    (h : versionDeadline T d s v = some x) (hx : τ ≤ x) : ProtocolVersionActive T d s v τ := by
  intro y hy
  rw [h] at hy
  cases hy
  exact hx

private lemma not_active_of {T : TimedConfig} {d : ℕ → ℕ} {s : CTM} {v τ x : ℕ}
    (h : versionDeadline T d s v = some x) (hx : x < τ) : ¬ ProtocolVersionActive T d s v τ :=
  fun ha => absurd (ha x h) (by omega)

/-- Before transition `300`'s upgrade time nobody upgrades chain `0` in a state with the setup's
routing, by any path. -/
private lemma dSetup_none_before {T : TimedConfig} (aux : ChainId → DiamondAux)
    (n : ChainId → ℕ → ℕ) {τ : ℕ} (hτ : τ < (T.sched 300).upgradeTimestamp)
    (path : UpgradePath) (caller : Address) :
    ¬ ∃ s', TimedStep T ⟨dSetupSys, aux, n⟩ (.upgrade 0 path caller τ) s' := by
  rintro ⟨s', h⟩
  obtain ⟨c, hc, hle⟩ := ManifestTimestampGates _ _ _ _ _ _ _ h
  have hcc := dSetupSys_chain0 hc
  subst hcc
  change (T.sched 300).upgradeTimestamp ≤ τ at hle
  omega

/-- Every label of `wTimingSetup` meets the run premises of the headline. -/
private lemma dSetup_labels : ∀ l ∈ wTimingSetup,
    ¬ l.isArbitrary ∧ l.InstallsWf wTiming.X.W ∧ l.CommitsValidSchedule wTiming := by
  intro l hl
  simp only [wTimingSetup, List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact ⟨fun h => h, trivial, trivial⟩
  · exact ⟨fun h => h, trivial, trivial⟩
  · exact ⟨fun h => h, xNodup200, (⟨by decide, by decide⟩ : ValidSchedule wTiming 300)⟩
  · exact ⟨fun h => h, trivial, trivial⟩

/-- A run extended by one step. -/
private lemma timedRun_snoc {T : TimedConfig} {s s' s'' : TimedSys} {ls : List TimedLabel}
    {l : TimedLabel} (h : TimedRun T s ls s') (hs : TimedStep T s' l s'') :
    TimedRun T s (ls ++ [l]) s'' := by
  induction h with
  | nil => exact TimedRun.cons hs TimedRun.nil
  | cons hs' _ ih => exact TimedRun.cons hs' (ih hs)

/-- The labels of `wTimingSetup` followed by a `DiamondAux` write meet the run premises. -/
private lemma dSetup_aux_labels (a : DiamondAux) : ∀ l ∈ wTimingSetup ++ [.setAux 0 a],
    ¬ l.isArbitrary ∧ l.InstallsWf wTiming.X.W ∧ l.CommitsValidSchedule wTiming := by
  intro l hl
  rcases List.mem_append.mp hl with h | h
  · exact dSetup_labels l h
  · simp only [List.mem_singleton] at h
    subst h
    exact ⟨fun h => h, trivial, trivial⟩

/-! ## The premises are needed -/

theorem ValidScheduleAloneLeavesDeadTime : Properties.ValidScheduleAloneLeavesDeadTime := by
  have hdl := dSetup_deadline wTimingSched
  refine ⟨⟨by decide, by decide⟩, by decide, dSetup_aux_labels _,
    ⟨_, timedRun_snoc dSetup_run (TimedStep.setAux (id := 0) (a := wSlBehindAux)),
      rfl, rfl, rfl, rfl, ⟨_, rfl, not_active_of hdl (by decide), ?_⟩⟩,
    dSetup_aux_labels _,
    ⟨_, timedRun_snoc dSetup_run (TimedStep.setAux (id := 0) (a := wPendingBatchAux)),
      rfl, by decide, rfl, ⟨_, rfl, not_active_of hdl (by decide), ?_⟩⟩⟩
  -- the settlement layer is behind the target
  · rintro path caller ⟨s', h⟩
    obtain ⟨c, hc, hle⟩ := EveryPathNeedsTheSettlementLayerAhead _ _ _ _ _ _ _ 1 h rfl
    have hcc := dSetupSys_chain0 hc
    subst hcc
    exact absurd hle (by decide)
  -- a committed batch is not executed
  · rintro path caller ⟨s', h⟩
    exact absurd (EveryPathNeedsExecutedBatches _ _ _ _ _ _ _ h) (by decide)

theorem NoDeadTimeNeedsItsOtherPremises : Properties.NoDeadTimeNeedsItsOtherPremises := by
  have hov : versionDeadline wTiming (upd (fun _ => 0) 1 1) dSetupSys.ctm 1 = some 1 := by
    simp [versionDeadline, upd]
  refine ⟨dSetup, dSetup_run, ⟨_, rfl, rfl⟩, rfl, rfl, rfl,
    ⟨_, rfl, not_active_of hov (by decide),
      fun path caller => dSetup_none_before _ _ (by decide) path caller⟩,
    ⟨fun h => absurd h.2 (by decide), dSetup_run_bad,
      ⟨_, rfl, not_active_of (dSetup_deadline _) (by decide),
        fun path caller => dSetup_none_before _ _ (by decide) path caller⟩⟩,
    { dSetup with sys := dDriftSys }, TimedStep.base (l := .arbitraryCut 0 1 bgExtra) (fun h => h)
      (Step.arbitraryCut (s := dSetupSys) (id := 0) 1 bgExtra rfl),
    ⟨_, rfl, not_active_of (dSetup_deadline wTimingSched) (by decide), ?_⟩⟩
  rintro path caller ⟨s'', h⟩
  exact DriftBlocksTransition wWorld dDriftSys 0 ⟨1, bgExtra⟩ dSetup_ctmInv rfl
    (fun h => absurd (congrFun h 9) (by decide)) ⟨_, (UpgradeIsATransition _ _ _ _ _ _ _ h).1⟩

/-! ## Witnesses -/

theorem ReplacementDeadlineWitness : Properties.ReplacementDeadlineWitness := by
  refine ⟨dSetup, dRepl, dSetup_run, dSetup_ctmInv, rfl, dRepl_step, rfl,
    dSetup_deadline _, dRepl_deadline _, dSetup_run_short, dRepl_step_short,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    fun h => (by decide : ¬ (wShortDeadlineTiming.sched 400).deadline =
      (wShortDeadlineTiming.sched 300).deadline) h,
    dRepl_deadline _, active_of (dSetup_deadline _) (by decide),
    not_active_of (dRepl_deadline _) (by decide)⟩

theorem NoDeadTimeWitness : Properties.NoDeadTimeWitness := by
  have hI : SysInv wTiming.X.W wTimingSys0.sys :=
    FreshSystemSatisfiesInvariant wWorld 100 (by decide)
  have hR : RecordedReleasesWf wTiming.X.W wTimingSys0.sys.ctm :=
    (StartingStatesMeetLivenessPremises wWorld 100).1 xNodup100
  have hV : SlotSchedulesValid wTiming wTimingSys0.sys.ctm := fun _ hv => absurd rfl hv
  have hrun : TimedRun wTiming wTimingSys0 wTimingSetup dSetup := dSetup_run
  obtain ⟨hnd, -, -, hts, -⟩ :=
    ValidatedTimedRunsHaveNoDeadTime wTiming (fun _ => 0) wTimingSys0 dSetup wTimingSetup
      hI hR hV hrun (fun l hl => (dSetup_labels l hl).1) (fun l hl => (dSetup_labels l hl).2.1)
      (fun l hl => (dSetup_labels l hl).2.2) 0 ⟨1, rowsRouting (wRows 100)⟩ rfl (by decide) rfl
      rfl (fun w hw => by cases hw)
  have hdl := dSetup_deadline wTimingSched
  refine ⟨hI, hR, hV, dSetup_labels, dSetup, hrun, ⟨_, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl,
    ⟨active_of hdl (by decide), fun path caller => dSetup_none_before _ _ (by decide) path caller⟩,
    ⟨active_of hdl (by decide), _, UpgradeStaysEnabledLater _ _ _ _ _ _ _ _ hts (by decide)⟩,
    ⟨not_active_of hdl (by decide), _, UpgradeStaysEnabledLater _ _ _ _ _ _ _ _ hts (by decide)⟩,
    hnd⟩

end Contracts.ChainTypeManager
