import EraSpec.Contracts.ChainTypeManager.Properties.ChainLocal
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainMigration

/-!
# Proofs: one chain at a time, and the break-glass repair

Two per-chain predicates carry the argument: chain `id` is consistent with its CTM (`OkAt`,
the per-chain slice of `SysInv`), and chain `id` is on its version's release (`OnRel`). Steps
that do not write `id` preserve both, with no invariant needed (`step_frame`, `okAt_step`,
`onRel_step`): CTM writers only raise the version and never rewrite a reached version's release
(`cstep_pv`, `cstep_relAt_low`). Under the CTM invariant, a write that is not a cut, and a
repair cut, establish `OnRel` from any state (`onRel_of_write`, `onRel_of_repair`). A run whose
last write of `id` is not a cut splits at that write (`exists_last_write`, `run_split`), and the
rest is the frame lemma along the writer-free tail. The CTM invariant itself holds along every
run (`run_ctmInv`), cuts included. The unique-selector countermodel rests on a successful cut
list naming each selector once (`removeAll_nodup`, `addAll_nodup`).
-/

namespace Contracts.ChainTypeManager

/-! ## The last-write premise on concrete lists -/

lemma lastWriteNotBreakGlass_nil {id : ChainId} : LastWriteNotBreakGlass id [] := by
  intro pre l post h
  cases pre <;> simp at h

lemma lastWriteNotBreakGlass_cons {id : ChainId} {l : Label} {ls : List Label} :
    LastWriteNotBreakGlass id (l :: ls) ↔
      LastWriteNotBreakGlass id ls ∧
        ((∀ l' ∈ ls, ¬ l'.writesChain id) → l.writesChain id → ¬ l.isArbitrary) := by
  constructor
  · intro h
    exact ⟨fun pre l' post hls hw hpost => h (l :: pre) l' post (by rw [hls]; rfl) hw hpost,
      fun hpost hw => h [] l ls rfl hw hpost⟩
  · rintro ⟨h, hl⟩ pre l' post hls hw hpost
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hls
      obtain ⟨rfl, rfl⟩ := hls
      exact hl hpost hw
    | cons x pre' =>
      simp only [List.cons_append, List.cons.injEq] at hls
      obtain ⟨rfl, hls⟩ := hls
      exact h pre' l' post hls hw hpost

/-- A run whose final step writes chain `id` and is not a cut meets the premise for `id`. -/
lemma lastWriteNotBreakGlass_snoc {id : ChainId} {l : Label} (hw : l.writesChain id)
    (hl : ¬ l.isArbitrary) : ∀ ls : List Label, LastWriteNotBreakGlass id (ls ++ [l]) := by
  intro ls
  induction ls with
  | nil =>
    exact lastWriteNotBreakGlass_cons.mpr ⟨lastWriteNotBreakGlass_nil, fun _ _ => hl⟩
  | cons x xs ih =>
    rw [List.cons_append, lastWriteNotBreakGlass_cons]
    refine ⟨ih, fun hpost _ => ?_⟩
    exact absurd hw (hpost l (by simp))

/-! ## Splitting a run at its last write -/

private lemma exists_last_write {id : ChainId} {ls : List Label}
    (h : ∃ l ∈ ls, l.writesChain id) :
    ∃ pre l post, ls = pre ++ l :: post ∧ l.writesChain id ∧ ∀ l' ∈ post, ¬ l'.writesChain id := by
  induction ls with
  | nil => obtain ⟨_, hl, _⟩ := h; simp at hl
  | cons x xs ih =>
    by_cases hx : ∃ l ∈ xs, l.writesChain id
    · obtain ⟨pre, l, post, rfl, hw, hpost⟩ := ih hx
      exact ⟨x :: pre, l, post, rfl, hw, hpost⟩
    · obtain ⟨l, hl, hw⟩ := h
      have hx' : ∀ l' ∈ xs, ¬ l'.writesChain id := fun l' hl' hw' => hx ⟨l', hl', hw'⟩
      rcases List.mem_cons.mp hl with rfl | hl'
      · exact ⟨[], l, xs, rfl, hw, hx'⟩
      · exact absurd hw (hx' l hl')

private lemma run_split {W : World} {s s' : Sys} {pre post : List Label} {l : Label}
    (h : Run W s (pre ++ l :: post) s') :
    ∃ s₁ s₂, Run W s pre s₁ ∧ Step W s₁ l s₂ ∧ Run W s₂ post s' := by
  induction pre generalizing s with
  | nil =>
    cases h with
    | cons hs hr => exact ⟨s, _, Run.nil, hs, hr⟩
  | cons x xs ih =>
    cases h with
    | cons hs hr =>
      obtain ⟨s₁, s₂, h1, h2, h3⟩ := ih hr
      exact ⟨s₁, s₂, Run.cons hs h1, h2, h3⟩

/-! ## The two per-chain predicates -/

/-- Chain `id`, if registered, is consistent with its CTM. -/
private def OkAt (W : World) (s : Sys) (id : ChainId) : Prop :=
  ∀ c, s.chains id = some c → ChainOk W s c

/-- Chain `id` is registered, not ahead of its CTM, and routes the release of its version. -/
private def OnRel (W : World) (s : Sys) (id : ChainId) : Prop :=
  ∃ c, s.chains id = some c ∧ c.pv ≤ s.ctm.pv ∧ s.ctm.relAt c.pv ≠ 0 ∧
    c.routing = rowsRouting (W.relRows (s.ctm.relAt c.pv))

private lemma okAt_of_onRel {W : World} {s : Sys} {id : ChainId} (h : OnRel W s id) :
    OkAt W s id := by
  obtain ⟨c, hc, hle, _, hrt⟩ := h
  intro c' hc'
  have hcc : c' = c := Option.some.inj (hc'.symm.trans hc)
  subst hcc
  exact ⟨hle, fun _ => hrt⟩

/-! ## Steps that do not write the chain -/

/-- A step that does not write chain `id` leaves its entry alone, and changes the CTM, if at
all, by one writer. -/
private lemma step_frame {W : World} {s s' : Sys} {l : Label} {id : ChainId}
    (h : Step W s l s') (hw : ¬ l.writesChain id) :
    s'.chains id = s.chains id ∧ (s'.ctm = s.ctm ∨ ∃ op, CStep W s.ctm op s'.ctm) := by
  cases h with
  | ctm hc => exact ⟨rfl, Or.inr ⟨_, hc⟩⟩
  | @genesis id' ρ _ _ =>
    simp only [Label.writesChain] at hw
    exact ⟨upd_ne _ _ (fun h => hw h.symm), Or.inl rfl⟩
  | @migrateIn id' ρ v _ _ _ =>
    simp only [Label.writesChain] at hw
    exact ⟨upd_ne _ _ (fun h => hw h.symm), Or.inl rfl⟩
  | @transition id' _ _ _ _ _ _ _ =>
    simp only [Label.writesChain] at hw
    exact ⟨upd_ne _ _ (fun h => hw h.symm), Or.inl rfl⟩
  | @bootstrapReset id' _ _ _ _ _ _ _ =>
    simp only [Label.writesChain] at hw
    exact ⟨upd_ne _ _ (fun h => hw h.symm), Or.inl rfl⟩
  | @arbitraryCut id' _ v ρ _ =>
    simp only [Label.writesChain] at hw
    exact ⟨upd_ne _ _ (fun h => hw h.symm), Or.inl rfl⟩

private lemma okAt_step {W : World} {s s' : Sys} {l : Label} {id : ChainId}
    (h : Step W s l s') (hw : ¬ l.writesChain id) (hok : OkAt W s id) : OkAt W s' id := by
  obtain ⟨hch, hctm⟩ := step_frame h hw
  intro c hc
  rw [hch] at hc
  obtain ⟨hle, hrel⟩ := hok c hc
  rcases hctm with hctm | ⟨op, hcs⟩
  · unfold ChainOk; rw [hctm]; exact ⟨hle, hrel⟩
  · have hlow := cstep_relAt_low hcs c.pv hle
    refine ⟨le_trans hle (cstep_pv hcs).1, ?_⟩
    rw [hlow]; exact hrel

private lemma onRel_step {W : World} {s s' : Sys} {l : Label} {id : ChainId}
    (h : Step W s l s') (hw : ¬ l.writesChain id) (hon : OnRel W s id) : OnRel W s' id := by
  obtain ⟨hch, hctm⟩ := step_frame h hw
  obtain ⟨c, hc, hle, hnz, hrt⟩ := hon
  refine ⟨c, by rw [hch]; exact hc, ?_⟩
  rcases hctm with hctm | ⟨op, hcs⟩
  · rw [hctm]; exact ⟨hle, hnz, hrt⟩
  · have hlow := cstep_relAt_low hcs c.pv hle
    rw [hlow]; exact ⟨le_trans hle (cstep_pv hcs).1, hnz, hrt⟩

/-- A run that does not write chain `id` leaves its entry alone. -/
private lemma run_frame_chain {W : World} {s s' : Sys} {ls : List Label} {id : ChainId}
    (h : Run W s ls s') (hw : ∀ l ∈ ls, ¬ l.writesChain id) : s'.chains id = s.chains id := by
  induction h with
  | nil => rfl
  | cons hs _ ih =>
    rw [ih (fun l hl => hw l (List.mem_cons_of_mem _ hl)),
      (step_frame hs (hw _ List.mem_cons_self)).1]

private lemma run_okAt {W : World} {s s' : Sys} {ls : List Label} {id : ChainId}
    (h : Run W s ls s') (hw : ∀ l ∈ ls, ¬ l.writesChain id) (hok : OkAt W s id) :
    OkAt W s' id := by
  induction h with
  | nil => exact hok
  | cons hs _ ih =>
    exact ih (fun l hl => hw l (List.mem_cons_of_mem _ hl))
      (okAt_step hs (hw _ List.mem_cons_self) hok)

private lemma run_onRel {W : World} {s s' : Sys} {ls : List Label} {id : ChainId}
    (h : Run W s ls s') (hw : ∀ l ∈ ls, ¬ l.writesChain id) (hon : OnRel W s id) :
    OnRel W s' id := by
  induction h with
  | nil => exact hon
  | cons hs _ ih =>
    exact ih (fun l hl => hw l (List.mem_cons_of_mem _ hl))
      (onRel_step hs (hw _ List.mem_cons_self) hon)

/-! ## Writes that land the chain on a release -/

private lemma onRel_of_write {W : World} {s s' : Sys} {l : Label} {id : ChainId}
    (hC : CtmInv W s.ctm) (h : Step W s l s') (hw : l.writesChain id) (hl : ¬ l.isArbitrary) :
    OnRel W s' id := by
  cases h with
  | ctm _ => exact hw.elim
  | @genesis id' ρ _ hadd =>
    simp only [Label.writesChain] at hw
    subst hw
    refine ⟨⟨s.ctm.pv, ρ⟩, by simp, le_rfl, ?_, ?_⟩
    · dsimp only; rw [hC.curAtVersion]; exact hC.curNonzero
    · dsimp only; rw [hC.curAtVersion]; exact addAll_empty hadd
  | @migrateIn id' ρ v hv _ hadd =>
    simp only [Label.writesChain] at hw
    subst hw hv
    refine ⟨⟨s.ctm.pv, ρ⟩, by simp, le_rfl, ?_, ?_⟩
    · dsimp only; rw [hC.curAtVersion]; exact hC.curNonzero
    · dsimp only; rw [hC.curAtVersion]; exact addAll_empty hadd
  | @transition id' c0 ρ _ hut hguard happ _ =>
    simp only [Label.writesChain] at hw
    subst hw
    obtain ⟨_, _, _, hle, hnr, hnz, _⟩ := edge_facts hC hut
    refine ⟨⟨(s.edge W c0.pv).new, ρ⟩, by simp, hle, hnz, ?_⟩
    dsimp only
    rw [hguard] at happ
    rw [applyDerived_rows happ, hnr]
  | @bootstrapReset id' c0 R ρ _ hleg hadd _ =>
    simp only [Label.writesChain] at hw
    subst hw
    obtain ⟨_, hrel, hR⟩ := hC.bootstraps _ R hleg
    have hle := (hC.relAtSound _ (by rw [hrel]; exact hR)).1
    refine ⟨⟨W.relVersion R, ρ⟩, by simp, hle, ?_, ?_⟩
    · dsimp only; rw [hrel]; exact hR
    · dsimp only; rw [hrel]; exact addAll_empty hadd
  | arbitraryCut _ _ _ => exact absurd trivial hl

private lemma onRel_of_repair {W : World} {s s' : Sys} {id : ChainId} {v : ℕ}
    (hC : CtmInv W s.ctm) (hv : s.ctm.relAt v ≠ 0) (h : Step W s (repairCut W s id v) s') :
    OnRel W s' id := by
  unfold repairCut at h
  cases h with
  | arbitraryCut _ _ _ =>
    exact ⟨⟨v, rowsRouting (W.relRows (s.ctm.relAt v))⟩, by simp, (hC.relAtSound v hv).1, hv,
      rfl⟩

/-- A chain at a committed version that routes exactly that version's release can cross the
edge, if both releases list each selector once. -/
private lemma transition_of_onRelease {W : World} {s : Sys} {id : ChainId} {c : Chain}
    (hC : CtmInv W s.ctm) (hc : s.chains id = some c) (hut : s.ctm.ut c.pv ≠ 0)
    (hrt : c.routing = rowsRouting (W.relRows (s.ctm.relAt c.pv)))
    (hA : ((W.relRows (s.ctm.relAt c.pv)).map Prod.fst).Nodup)
    (hB : ((W.relRows (s.edge W c.pv).newRel).map Prod.fst).Nodup) :
    Step W s (.transition id) { s with chains :=
      (upd s.chains id (some ⟨(s.edge W c.pv).new, rowsRouting (W.relRows (s.edge W c.pv).newRel)⟩)) } := by
  obtain ⟨hfrom, _, hlt, _, _, _, _⟩ := edge_facts hC hut
  have hfrom' : (s.edge W c.pv).fromRel = s.ctm.relAt c.pv := hfrom
  have hguard : c.routing = rowsRouting (W.relRows (s.edge W c.pv).fromRel) := by
    rw [hrt, hfrom']
  have hA' : ((W.relRows (s.edge W c.pv).fromRel).map Prod.fst).Nodup := by
    rw [hfrom']; exact hA
  refine Step.transition hc hut hguard ?_ hlt
  rw [hguard]
  exact applyDerived_rows_eq hA' hB

/-! ## A cut that succeeds names each selector once -/

/-- A successful list of `Remove` cuts names each selector once: the second `Remove` of a
selector finds it unrouted. -/
private lemma removeAll_nodup {ρ σ : Routing} {ks : List Selector}
    (h : removeAll ρ ks = some σ) : ks.Nodup := by
  induction ks generalizing ρ with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [removeAll, removeSel] at h
    split_ifs at h with hx
    · simp at h
    · simp only [Option.bind_some] at h
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ih h⟩
      rw [removeAll_none hm (upd_same ρ x none)] at h
      simp at h

/-- A successful list of `Add` cuts names each selector once: the second `Add` of a selector
finds it routed. -/
private lemma addAll_nodup {ρ σ : Routing} {B : ReleaseRows} (h : addAll ρ B = some σ) :
    (B.map Prod.fst).Nodup := by
  induction B generalizing ρ with
  | nil => exact List.nodup_nil
  | cons hd rs ih =>
    obtain ⟨x, r⟩ := hd
    simp only [addAll, addSel] at h
    split_ifs at h with hx
    · simp only [Option.bind_some] at h
      simp only [List.map_cons]
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ih h⟩
      have := addAll_fresh h x hm
      simp at this
    · simp at h

/-! ## Certificates: one step -/

theorem StepsElsewhereKeepChainOk : Properties.StepsElsewhereKeepChainOk :=
  fun _ _ _ _ _ hok h hw => okAt_step h hw hok

theorem NonCutWriteLandsOnRelease : Properties.NonCutWriteLandsOnRelease :=
  fun _ _ _ _ _ hC h hw hl => onRel_of_write hC h hw hl

/-! ## Certificates: the per-chain headline -/

theorem ChainRunsItsVersionsRelease : Properties.ChainRunsItsVersionsRelease := by
  intro W s s' ls id hC hok h hlast c hc
  have hC' := run_ctmInv hC h
  have hfinal : OkAt W s' id := by
    by_cases hex : ∃ l ∈ ls, l.writesChain id
    · obtain ⟨pre, l, post, rfl, hw, hpost⟩ := exists_last_write hex
      obtain ⟨s₁, s₂, h1, h2, h3⟩ := run_split h
      have hC₁ := run_ctmInv hC h1
      exact okAt_of_onRel (run_onRel h3 hpost
        (onRel_of_write hC₁ h2 hw (hlast pre l post rfl hw hpost)))
    · exact run_okAt h (fun l hl hw => hex ⟨l, hl, hw⟩) hok
  obtain ⟨hle, hrel⟩ := hfinal c hc
  exact ⟨hle, fun hnz => ⟨(hC'.relAtSound _ hnz).2, hrel hnz⟩⟩

theorem GlobalPremiseImpliesChainLocal : Properties.GlobalPremiseImpliesChainLocal := by
  intro ls hno id pre l post hls _ _
  exact hno l (by rw [hls]; simp)

/-! ## Certificates: across migration -/

theorem MigrationRunIsARoutingRun : Properties.MigrationRunIsARoutingRun := by
  intro W s s' ls h
  induction h with
  | nil => exact Run.nil
  | cons hs _ ih =>
    cases hs with
    | base hstep => exact Run.cons hstep ih
    | migrateOut _ _ _ => exact ih
    | migrateReturn _ _ _ => exact ih
    | migrateRecover _ _ => exact ih

theorem ChainRunsItsVersionsReleaseAcrossMigration :
    Properties.ChainRunsItsVersionsReleaseAcrossMigration := by
  intro W s s' ls id hC hok h hlast
  exact ChainRunsItsVersionsRelease W s.sys s'.sys _ id hC hok
    (MigrationRunIsARoutingRun W s s' ls h) hlast

/-! ## Certificates: the repair -/

theorem RepairCutRestoresChainOk : Properties.RepairCutRestoresChainOk := by
  intro W s id v hC ⟨c, hc⟩ hv
  refine ⟨⟨_, Step.arbitraryCut v _ hc⟩, ?_⟩
  intro s' h
  unfold repairCut at h
  cases h with
  | arbitraryCut _ _ _ =>
    exact ⟨rfl, fun id' hne => upd_ne _ _ hne, ⟨v, _⟩, by simp, rfl,
      ⟨(hC.relAtSound v hv).1, fun _ => rfl⟩, rfl⟩

theorem OnlyRepairCutsLandOnARelease : Properties.OnlyRepairCutsLandOnARelease := by
  intro W s s' id v ρ h hland
  cases h with
  | arbitraryCut _ _ _ =>
    obtain ⟨c, hc', hnz, hrt⟩ := hland
    simp only [upd_same, Option.some.injEq] at hc'
    subst hc'
    refine ⟨hnz, ?_⟩
    have hρ : ρ = rowsRouting (W.relRows (s.ctm.relAt v)) := hrt
    rw [hρ]
    rfl

theorem LastWriteDecidesTheRouting : Properties.LastWriteDecidesTheRouting := by
  intro W s s₁ s₂ s' pre post l id hC h1 h2 h3 hw hpost hcase
  have hC₁ := run_ctmInv hC h1
  have hon₂ : OnRel W s₂ id := by
    rcases hcase with hl | ⟨v, hv, rfl⟩
    · exact onRel_of_write hC₁ h2 hw hl
    · exact onRel_of_repair hC₁ hv h2
  have hC' := run_ctmInv (step_ctmInv hC₁ h2) h3
  obtain ⟨c, hc, hle, hnz, hrt⟩ := run_onRel h3 hpost hon₂
  exact ⟨c, hc, hle, hnz, (hC'.relAtSound _ hnz).2, hrt⟩

theorem NewChainRunsItsVersionsRelease : Properties.NewChainRunsItsVersionsRelease := by
  intro W s s' ls id hC hnone h hlast c hc
  by_cases hex : ∃ l ∈ ls, l.writesChain id
  · obtain ⟨pre, l, post, rfl, hw, hpost⟩ := exists_last_write hex
    obtain ⟨s₁, s₂, h1, h2, h3⟩ := run_split h
    obtain ⟨c', hc', hle, hnz, hver, hrt⟩ := LastWriteDecidesTheRouting W s s₁ s₂ s' pre post l id
      hC h1 h2 h3 hw hpost (Or.inl (hlast pre l post rfl hw hpost))
    have hcc : c = c' := Option.some.inj (hc.symm.trans hc')
    subst hcc
    exact ⟨hle, hnz, hver, hrt⟩
  · rw [run_frame_chain h (fun l hl hw => hex ⟨l, hl, hw⟩), hnone] at hc
    exact absurd hc (by simp)

theorem RepairEnablesTransition : Properties.RepairEnablesTransition := by
  intro W s s' id v hC hv h hut hA hB
  unfold repairCut at h
  cases h with
  | arbitraryCut _ _ _ =>
    obtain ⟨_, _, hlt, _, hnr, hnz, _⟩ := edge_facts hC hut
    refine ⟨_, transition_of_onRelease (c := ⟨v, rowsRouting (W.relRows (s.ctm.relAt v))⟩)
      hC (by simp) hut rfl hA hB,
      ⟨(s.edge W v).new, rowsRouting (W.relRows (s.edge W v).newRel)⟩, by simp, hlt, rfl, hnz, ?_⟩
    dsimp only
    rw [hnr]

theorem RepeatedSelectorBlocksTheEdge : Properties.RepeatedSelectorBlocksTheEdge := by
  rintro W s id c hc hne hdup ⟨s', h⟩
  cases h with
  | @transition _ c0 ρ hc0 _ _ happ _ =>
    have hcc : c0 = c := Option.some.inj (hc0.symm.trans hc)
    subst hcc
    simp only [applyDerived, hne, ite_false] at happ
    cases hr : removeAll c0.routing ((W.relRows (s.edge W c0.pv).fromRel).map Prod.fst) with
    | none => rw [hr] at happ; simp at happ
    | some τ =>
      rw [hr, Option.bind_some] at happ
      rcases hdup with hd | hd
      · exact hd (removeAll_nodup hr)
      · exact hd (addAll_nodup happ)

/-! ## Witnesses -/

private lemma lNodup100 : ((wWorld.relRows 100).map Prod.fst).Nodup := by decide
private lemma lNodup200 : ((wWorld.relRows 200).map Prod.fst).Nodup := by decide

theorem ChainLocalWitness : Properties.ChainLocalWitness := by
  have hrun : Run wWorld wSys0 wLocalRun _ :=
    Run.cons (Step.genesis (s := wSys0) (id := 0) rfl (addAll_empty_eq lNodup100))
    (Run.cons (Step.genesis (id := 1) rfl (addAll_empty_eq lNodup100))
    (Run.cons (Step.arbitraryCut (id := 0) 1 bgExtra rfl)
    (Run.cons (Step.arbitraryCut (id := 1) 1 bgExtra rfl)
    (Run.cons (Step.arbitraryCut (id := 0) 1 (rowsRouting (wRows 100)) rfl)
    (Run.cons (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))
    (Run.cons (Step.transition (id := 0) rfl (by decide) rfl
        (applyDerived_rows_eq lNodup100 lNodup200) (by decide)) Run.nil))))))
  have hlast0 : LastWriteNotBreakGlass 0 wLocalRun :=
    lastWriteNotBreakGlass_snoc (l := .transition 0) rfl (fun h => h)
      [.genesis 0, .genesis 1, .arbitraryCut 0 1 bgExtra, .arbitraryCut 1 1 bgExtra,
        .arbitraryCut 0 1 (rowsRouting (wRows 100)), .ctm (.commit 300)]
  have hlast1 : ¬ LastWriteNotBreakGlass 1 wLocalRun := by
    intro h
    exact h [.genesis 0, .genesis 1, .arbitraryCut 0 1 bgExtra] (.arbitraryCut 1 1 bgExtra)
      [.arbitraryCut 0 1 (rowsRouting (wRows 100)), .ctm (.commit 300), .transition 0] rfl rfl
      (by simp [Label.writesChain]) trivial
  refine ⟨_, hrun, FreshSystemSatisfiesInvariant wWorld 100 (by decide), rfl,
    ⟨.arbitraryCut 0 1 bgExtra, by simp [wLocalRun], trivial⟩, hlast0, hlast1,
    ⟨_, rfl, by decide, by decide, rfl⟩, ⟨_, rfl, rfl, by decide, ?_⟩⟩
  exact fun h => absurd (congrFun h 9) (by decide)

theorem ChainLocalPremiseNotNecessary : Properties.ChainLocalPremiseNotNecessary := by
  refine ⟨_, _,
    Run.cons (Step.genesis (s := wSys0) (id := 0) rfl (addAll_empty_eq lNodup100))
      (Run.cons (Step.arbitraryCut (id := 0) 2 (rowsRouting (wRows 200)) rfl) Run.nil),
    Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)),
    ?_, ⟨_, rfl, fun hok => absurd hok.1 (by decide)⟩,
    ⟨_, rfl, rfl, by decide, ⟨by decide, fun _ => rfl⟩, rfl⟩⟩
  intro h
  exact h [.genesis 0] (.arbitraryCut 0 2 (rowsRouting (wRows 200))) [.ctm (.commit 300)] rfl rfl
    (by simp [Label.writesChain]) trivial

theorem RepairUnsticksDriftedReturner : Properties.RepairUnsticksDriftedReturner := by
  have hstuck : MRun wWorld wMSys0 wStuckRun _ :=
    MRun.cons (MStep.base (Step.genesis (s := wSys0) (id := 0)
        (ρ := rowsRouting (wWorld.relRows 100)) rfl (addAll_empty_eq lNodup100)))
    (MRun.cons (MStep.base (Step.arbitraryCut (id := 0) 1 bgExtra rfl))
    (MRun.cons (MStep.migrateOut (c := ⟨1, bgExtra⟩) rfl rfl rfl)
    (MRun.cons (MStep.migrateReturn (c := ⟨1, bgExtra⟩) rfl (by simp [upd]) rfl)
    (MRun.cons (MStep.base (Step.ctm (CStep.commit (t := 300) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)))) MRun.nil))))
  have hC := run_ctmInv (InitSatisfiesInvariant wWorld 100 (by decide))
    (MigrationRunIsARoutingRun _ _ _ _ hstuck)
  have hlast : LastWriteNotBreakGlass 0 ((wStuckRun ++ wUnstickRun).filterMap MLabel.base?) :=
    lastWriteNotBreakGlass_snoc (l := .transition 0) rfl (fun h => h)
      [.genesis 0, .arbitraryCut 0 1 bgExtra, .ctm (.commit 300),
        .arbitraryCut 0 1 (rowsRouting (wRows 100))]
  refine ⟨_, _, hstuck, FreshSystemSatisfiesInvariant wWorld 100 (by decide), ?_, hC, by decide,
    by decide, lNodup100, ?_, rfl,
    MRun.cons (MStep.base (Step.arbitraryCut (id := 0) 1 (rowsRouting (wRows 100)) rfl))
      (MRun.cons (MStep.base (Step.transition (id := 0) rfl (by decide) rfl
          (applyDerived_rows_eq lNodup100 lNodup200) (by decide)))
        (MRun.cons (MStep.migrateOut rfl (by simp [upd]) (by decide)) MRun.nil)),
    hlast, by simp [upd], _, rfl, by decide, rfl⟩
  · rintro ⟨s'', h⟩
    cases h with
    | base hs =>
      exact DriftBlocksTransition wWorld _ 0 ⟨1, bgExtra⟩ hC (by simp [upd])
        (fun h => absurd (congrFun h 9) (by decide)) ⟨_, hs⟩
  · decide

private lemma dNodup100 : ((wDupWorld.relRows 100).map Prod.fst).Nodup := by decide

theorem RepairNeedsUniqueSelectors : Properties.RepairNeedsUniqueSelectors := by
  have hrun : Run wDupWorld wDupSys0 [.genesis 0, .ctm (.commit 800), .ctm (.commit 900)] _ :=
    Run.cons (Step.genesis (s := wDupSys0) (id := 0) rfl (addAll_empty_eq dNodup100))
    (Run.cons (Step.ctm (CStep.commit (t := 800) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)))
    (Run.cons (Step.ctm (CStep.commit (t := 900) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))) Run.nil))
  have hC := run_ctmInv (InitSatisfiesInvariant wDupWorld 100 (by decide)) hrun
  refine ⟨_, _, hrun, FreshSystemSatisfiesInvariant wDupWorld 100 (by decide),
    RepeatedSelectorBlocksTheEdge wDupWorld _ 0 _ rfl (by decide) (Or.inr (by decide)),
    hC, by decide, by decide, Step.arbitraryCut (id := 0) 2 _ rfl, by decide, by decide,
    RepeatedSelectorBlocksTheEdge wDupWorld _ 0 _ rfl (by decide) (Or.inl (by decide))⟩

end Contracts.ChainTypeManager
