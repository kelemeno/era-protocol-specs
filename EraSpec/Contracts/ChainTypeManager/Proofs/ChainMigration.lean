import EraSpec.Contracts.ChainTypeManager.Properties.ChainMigration
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainRouting

/-!
# Proofs: a returning chain keeps its diamond, drift included

Migration steps leave the routing system unchanged, so every routing result lifts along
`MRun` by the `ChainRouting` induction. The drift witnesses are concrete runs.
-/

namespace Contracts.ChainTypeManager

theorem MigrationLeavesRoutingAlone : Properties.MigrationLeavesRoutingAlone := by
  intro W s s' l h hl
  cases h with
  | base _ => exact absurd rfl (hl _)
  | @migrateOut _ c hc _ hv =>
    exact ⟨rfl, fun id hid => by cases hid⟩
  | @migrateReturn id c hc _ hv =>
    refine ⟨rfl, fun id' hid => ?_⟩
    cases hid
    exact ⟨c, hc, hv⟩
  | migrateRecover _ _ => exact ⟨rfl, fun id hid => by cases hid⟩

/-- A step that leaves a registered chain's diamond alone. -/
private lemma keep {chains : ChainId → Option Chain} {id id' : ChainId} {c c' : Chain}
    {x : Option Chain} (hne : id' ≠ id) (hc : chains id = some c)
    (h' : upd chains id' x id = some c') (hcc : c' ≠ c) : False := by
  rw [upd_ne _ _ (Ne.symm hne), hc] at h'
  exact hcc (Option.some.inj h').symm

theorem OnlyUpgradesAndCutsWriteADiamond : Properties.OnlyUpgradesAndCutsWriteADiamond := by
  intro W s s' l id c c' h hc hc' hcc
  cases h with
  | @base _ s1 hs =>
    cases hs with
    | ctm _ => exact absurd (Option.some.inj (hc.symm.trans hc')).symm hcc
    | @genesis id' ρ hnone _ =>
      by_cases hid : id' = id
      · subst hid; rw [hc] at hnone; exact Option.noConfusion hnone
      · exact (keep hid hc hc' hcc).elim
    | @migrateIn id' ρ v _ hnone _ =>
      by_cases hid : id' = id
      · subst hid; rw [hc] at hnone; exact Option.noConfusion hnone
      · exact (keep hid hc hc' hcc).elim
    | @transition id' _ _ _ _ _ _ _ =>
      by_cases hid : id' = id
      · exact hid
      · exact (keep hid hc hc' hcc).elim
    | @bootstrapReset id' _ _ _ _ _ _ _ =>
      by_cases hid : id' = id
      · exact hid
      · exact (keep hid hc hc' hcc).elim
    | @arbitraryCut id' _ _ _ _ =>
      by_cases hid : id' = id
      · exact hid
      · exact (keep hid hc hc' hcc).elim
  | migrateOut _ _ _ => exact absurd (Option.some.inj (hc.symm.trans hc')).symm hcc
  | migrateReturn _ _ _ => exact absurd (Option.some.inj (hc.symm.trans hc')).symm hcc
  | migrateRecover _ _ => exact absurd (Option.some.inj (hc.symm.trans hc')).symm hcc

lemma mstep_sysInv {W : World} {s s' : MSys} {l : MLabel} (hI : SysInv W s.sys)
    (h : MStep W s l s') (hl : ¬ l.isArbitrary) : SysInv W s'.sys := by
  cases h with
  | base hs => exact step_sysInv hI hs hl
  | migrateOut _ _ _ => exact hI
  | migrateReturn _ _ _ => exact hI
  | migrateRecover _ _ => exact hI

lemma mrun_sysInv {W : World} {s s' : MSys} {ls : List MLabel} (hI : SysInv W s.sys)
    (h : MRun W s ls s') (hl : ∀ l ∈ ls, ¬ l.isArbitrary) : SysInv W s'.sys := by
  induction h with
  | nil => exact hI
  | cons hs _ ih =>
    exact ih (mstep_sysInv hI hs (hl _ (List.mem_cons_self _ _)))
      (fun l hm => hl l (List.mem_cons_of_mem _ hm))

theorem ChainsRunTheirVersionsReleaseAcrossMigration :
    Properties.ChainsRunTheirVersionsReleaseAcrossMigration := by
  intro W s s' ls hI h hl id c hc hrel
  obtain ⟨hC, hch⟩ := mrun_sysInv hI h hl
  exact ⟨(hC.relAtSound _ hrel).2, (hch id c hc).2 hrel⟩

/-! ## Witnesses -/

private lemma mNodup100 : ((wWorld.relRows 100).map Prod.fst).Nodup := by decide
private lemma mNodup200 : ((wWorld.relRows 200).map Prod.fst).Nodup := by decide

lemma mrun_snoc {W : World} {s s1 s2 : MSys} {ls : List MLabel} {l : MLabel}
    (h : MRun W s ls s1) (h' : MStep W s1 l s2) : MRun W s (ls ++ [l]) s2 := by
  induction h with
  | nil => exact MRun.cons h' MRun.nil
  | cons hs _ ih => exact MRun.cons hs (ih h')

/-- The system after the drift round trip. -/
private def sTrip : MSys :=
  ⟨⟨initState wWorld 100, upd (upd (fun _ => none) 0 (some ⟨1, rowsRouting (wWorld.relRows 100)⟩)) 0
      (some ⟨1, bgExtra⟩)⟩, upd (upd (fun _ => false) 0 true) 0 false⟩

/-- Chain `0` created on the fresh witness system, then cut by `bgExtra`, then out and back. -/
private lemma roundTrip : MRun wWorld wMSys0
    [.base (.genesis 0), .base (.arbitraryCut 0 1 bgExtra), .migrateOut 0, .migrateReturn 0] sTrip :=
  MRun.cons (MStep.base (Step.genesis (s := wSys0) (id := 0) (ρ := rowsRouting (wWorld.relRows 100))
      rfl (addAll_empty_eq mNodup100)))
    (MRun.cons (MStep.base (Step.arbitraryCut (id := 0) 1 bgExtra rfl))
      (MRun.cons (MStep.migrateOut (c := ⟨1, bgExtra⟩) rfl rfl rfl)
        (MRun.cons (MStep.migrateReturn (c := ⟨1, bgExtra⟩) rfl (by simp [upd]) rfl) MRun.nil)))

private lemma sTrip_chain : sTrip.sys.chains 0 = some ⟨1, bgExtra⟩ := by simp [sTrip, upd]

theorem DriftSurvivesMigrationRoundTrip : Properties.DriftSurvivesMigrationRoundTrip := by
  refine ⟨⟨_, roundTrip, by simp [sTrip, upd], by decide, ⟨1, bgExtra⟩, sTrip_chain, rfl, rfl,
    fun h => absurd (congrFun h 9) (by decide)⟩, ?_⟩
  exact ⟨_, MRun.cons (MStep.base (Step.migrateIn (s := wSys0) (id := 0)
      (ρ := rowsRouting (wWorld.relRows 100)) 1 rfl rfl (addAll_empty_eq mNodup100))) MRun.nil,
    _, rfl, by decide, rfl⟩

theorem DriftedReturnerIsStuck : Properties.DriftedReturnerIsStuck := by
  have hC : CtmInv wWorld (initState wWorld 100) := InitSatisfiesInvariant wWorld 100 (by decide)
  have hC' := step_inv hC (CStep.commit (W := wWorld) (s := initState wWorld 100) (t := 300)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  refine ⟨_, mrun_snoc roundTrip (MStep.base (Step.ctm (CStep.commit (t := 300) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)))), rfl,
    ⟨⟨1, bgExtra⟩, sTrip_chain, rfl⟩, ?_, ?_⟩
  · rintro ⟨s', h⟩
    cases h with
    | base hs =>
      refine DriftBlocksTransition wWorld _ 0 ⟨1, bgExtra⟩ ?_ ?_
        (fun h => absurd (congrFun h 9) (by decide)) ⟨_, hs⟩
      · exact hC'
      · exact sTrip_chain
  · rintro ⟨s', h⟩
    cases h with
    | @migrateOut _ c hc _ hv =>
      have hcc : c = ⟨1, bgExtra⟩ := Option.some.inj (hc.symm.trans sTrip_chain)
      subst hcc
      exact absurd hv (by decide)

theorem MigrationRoundTripWitness : Properties.MigrationRoundTripWitness := by
  refine ⟨_, MRun.cons (MStep.base (Step.genesis (s := wSys0) (id := 0) rfl
      (addAll_empty_eq mNodup100)))
    (MRun.cons (MStep.migrateOut (c := ⟨1, rowsRouting (wRows 100)⟩) rfl rfl rfl)
      (MRun.cons (MStep.migrateReturn (c := ⟨1, rowsRouting (wRows 100)⟩) rfl
          rfl rfl)
        (MRun.cons (MStep.base (Step.ctm (CStep.commit (t := 300) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide))))
          (MRun.cons (MStep.base (Step.transition (id := 0) (c := ⟨1, rowsRouting (wRows 100)⟩)
              rfl (by decide) rfl (applyDerived_rows_eq mNodup100 mNodup200)
              (by decide))) MRun.nil)))),
    FreshSystemSatisfiesInvariant wWorld 100 (by decide), _, rfl, by decide, rfl⟩

end Contracts.ChainTypeManager
