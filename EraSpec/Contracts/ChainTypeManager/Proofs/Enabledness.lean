import EraSpec.Contracts.ChainTypeManager.Properties.Enabledness
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainRouting

/-!
# Proofs: when a chain can upgrade, be deployed, or cross the bootstrap edge

Two facts about the diamond cut carry everything. A `Remove` list or an `Add` list that names
a selector twice reverts, whatever routing it starts from (`removeAll_nodup`, `addAll_nodup`).
From a release's own routing, the derived cuts of a changing edge apply exactly when both
releases list each selector once (`applyDerived_rows_iff`). The one-step results then read
the remaining guards off `CtmInv` (`edge_facts`). The run results carry
`ChainsOnWfReleases`, `RecordedReleasesWf`, `DepartedBelow` and `ChainsAtDepartedVersions`
step by step, next to `SysInv`.
-/

namespace Contracts.ChainTypeManager

/-! ## A cut that names a selector twice reverts -/

/-- A successful `Remove` list names each selector once: after its first removal a selector
is unrouted, and removing it again reverts. -/
lemma removeAll_nodup {ρ τ : Routing} {ks : List Selector} (h : removeAll ρ ks = some τ) :
    ks.Nodup := by
  induction ks generalizing ρ with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    simp only [removeAll, removeSel] at h
    split_ifs at h with hx
    · simp at h
    · simp only [Option.bind_some] at h
      refine List.nodup_cons.mpr ⟨fun hm => ?_, ih h⟩
      rw [removeAll_none (ρ := upd ρ x none) hm (by simp)] at h
      simp at h

/-- A successful `Add` list names each selector once: after its first addition a selector is
routed, and adding it again reverts. -/
lemma addAll_nodup {ρ σ : Routing} {B : ReleaseRows} (h : addAll ρ B = some σ) :
    (B.map Prod.fst).Nodup := by
  induction B generalizing ρ with
  | nil => exact List.nodup_nil
  | cons hd rs ih =>
    obtain ⟨x, r⟩ := hd
    simp only [addAll, addSel] at h
    split_ifs at h with hx
    · simp only [Option.bind_some] at h
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => ?_, ih h⟩
      have := addAll_fresh h x hm
      simp at this
    · simp at h

/-- From the departing release's own routing, a changing edge's derived cuts apply exactly when
both releases list each selector once. -/
lemma applyDerived_rows_iff {A B : ReleaseRows} (hAB : A ≠ B) :
    (∃ σ, applyDerived (rowsRouting A) A B = some σ) ↔
      (A.map Prod.fst).Nodup ∧ (B.map Prod.fst).Nodup := by
  constructor
  · rintro ⟨σ, h⟩
    simp only [applyDerived, hAB, ite_false] at h
    obtain ⟨τ, hr, h⟩ := Option.bind_eq_some_iff.mp h
    exact ⟨removeAll_nodup hr, addAll_nodup h⟩
  · rintro ⟨hA, hB⟩
    exact ⟨_, applyDerived_rows_eq hA hB⟩

/-- Well-formedness depends on a release's rows only. -/
lemma releaseWf_of_rows {W : World} {a b : Address} (h : W.relRows a = W.relRows b)
    (ha : ReleaseWf W a) : ReleaseWf W b := by
  unfold ReleaseWf at ha ⊢
  rwa [← h]

/-! ## One step -/

theorem TransitionEnabled : Properties.TransitionEnabled := by
  intro W s id c hC hc hok hut hA hB
  obtain ⟨hfrom, hrz, hlt, -⟩ := edge_facts hC hut
  have hguard : c.routing = rowsRouting (W.relRows (s.edge W c.pv).fromRel) := by
    rw [hok.2 hrz, hfrom]
  unfold Sys.crossEdge
  exact Step.transition hc hut hguard (by rw [hguard]; exact applyDerived_rows_eq hA hB) hlt

theorem TransitionEnabledIff : Properties.TransitionEnabledIff := by
  intro W s id c hC hc
  constructor
  · rintro ⟨s', h⟩
    cases h with
    | @transition _ c0 ρ hc0 hut hguard happ hlt =>
      obtain rfl : c0 = c := Option.some.inj (hc0.symm.trans hc)
      have hfrom := (edge_facts hC hut).1
      refine ⟨hut, by rw [hguard, hfrom], ?_⟩
      by_cases hAB : W.relRows (s.edge W c0.pv).fromRel = W.relRows (s.edge W c0.pv).newRel
      · exact Or.inl hAB
      · rw [hguard] at happ
        exact Or.inr ((applyDerived_rows_iff hAB).mp ⟨ρ, happ⟩)
  · rintro ⟨hut, hroute, hwf⟩
    obtain ⟨hfrom, -, hlt, -⟩ := edge_facts hC hut
    have hguard : c.routing = rowsRouting (W.relRows (s.edge W c.pv).fromRel) := by
      rw [hroute, hfrom]
    rcases hwf with hAB | ⟨hA, hB⟩
    · exact ⟨_, Step.transition (ρ := c.routing) hc hut hguard (by simp [applyDerived, hAB]) hlt⟩
    · exact ⟨_, Step.transition hc hut hguard
        (by rw [hguard]; exact applyDerived_rows_eq hA hB) hlt⟩

theorem NewChainEnabled : Properties.NewChainEnabled := by
  intro W s id hnone hwf
  exact ⟨Step.genesis hnone (addAll_empty_eq hwf),
    Step.migrateIn s.ctm.pv rfl hnone (addAll_empty_eq hwf)⟩

theorem NewChainEnabledIff : Properties.NewChainEnabledIff := by
  intro W s id
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨s', h⟩
    cases h with
    | genesis hnone hadd => exact ⟨hnone, addAll_nodup hadd⟩
  · rintro ⟨hnone, hwf⟩
    exact ⟨_, (NewChainEnabled W s id hnone hwf).1⟩
  · rintro ⟨s', h⟩
    cases h with
    | migrateIn v hv hnone hadd => exact ⟨hnone, addAll_nodup hadd⟩
  · rintro ⟨hnone, hwf⟩
    exact ⟨_, (NewChainEnabled W s id hnone hwf).2⟩

theorem BootstrapResetEnabledIff : Properties.BootstrapResetEnabledIff := by
  intro W s id c hC hc
  constructor
  · rintro ⟨s', h⟩
    cases h with
    | @bootstrapReset _ c0 R ρ hc0 hleg hadd hlt =>
      obtain rfl : c0 = c := Option.some.inj (hc0.symm.trans hc)
      exact ⟨R, hleg, addAll_nodup hadd⟩
  · rintro ⟨R, hleg, hwf⟩
    exact ⟨_, Step.bootstrapReset hc hleg (addAll_empty_eq hwf) (hC.bootstraps _ R hleg).1⟩

/-! ## Chains stay on well-formed releases -/

lemma step_chainsOnWf {W : World} {s s' : Sys} {l : Label} (hI : SysInv W s)
    (hW : ChainsOnWfReleases W s) (h : Step W s l s') (hl : ¬ l.isArbitrary) :
    ChainsOnWfReleases W s' := by
  obtain ⟨hC, hch⟩ := hI
  cases h with
  | @ctm op c' hc =>
    intro id c hcid hrel
    dsimp only at hrel ⊢
    rw [cstep_relAt_low hc c.pv (hch id c hcid).1] at hrel ⊢
    exact hW id c hcid hrel
  | @genesis id ρ hnone hadd =>
    intro id' c hc hrel
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · dsimp only
      rw [hC.curAtVersion]
      exact addAll_nodup hadd
    · exact hW id' c hold hrel
  | @migrateIn id ρ v hv hnone hadd =>
    intro id' c hc hrel
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · subst hv
      dsimp only
      rw [hC.curAtVersion]
      exact addAll_nodup hadd
    · exact hW id' c hold hrel
  | @transition id c0 ρ hc0 hut hguard happ hlt =>
    intro id' c hc hrel
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · obtain ⟨hfrom, hrz, _, _, hnr, _, _⟩ := edge_facts hC hut
      dsimp only
      rw [← hnr]
      by_cases hAB : W.relRows (s.edge W c0.pv).fromRel = W.relRows (s.edge W c0.pv).newRel
      · -- the empty-cut shortcut: the arriving release routes as the departing one
        have hdep : ReleaseWf W (s.edge W c0.pv).fromRel := by
          rw [hfrom]; exact hW id c0 hc0 hrz
        exact releaseWf_of_rows hAB hdep
      · rw [hguard] at happ
        exact ((applyDerived_rows_iff hAB).mp ⟨ρ, happ⟩).2
    · exact hW id' c hold hrel
  | @bootstrapReset id c0 R ρ hc0 hleg hadd hlt =>
    intro id' c hc hrel
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · obtain ⟨_, hrelR, _⟩ := hC.bootstraps _ R hleg
      dsimp only
      rw [hrelR]
      exact addAll_nodup hadd
    · exact hW id' c hold hrel
  | arbitraryCut _ _ _ => exact absurd trivial hl

lemma run_chainsOnWf {W : World} {s s' : Sys} {ls : List Label} (hI : SysInv W s)
    (hW : ChainsOnWfReleases W s) (h : Run W s ls s') (hl : ∀ l ∈ ls, ¬ l.isArbitrary) :
    ChainsOnWfReleases W s' := by
  induction h with
  | nil => exact hW
  | cons hs _ ih =>
    have hl0 := hl _ List.mem_cons_self
    exact ih (step_sysInv hI hs hl0) (step_chainsOnWf hI hW hs hl0)
      (fun l hm => hl l (List.mem_cons_of_mem _ hm))

theorem ChainsStayOnWfReleases : Properties.ChainsStayOnWfReleases :=
  fun _ _ _ _ hI hW h hl => run_chainsOnWf hI hW h hl

theorem UpgradesStayEnabled : Properties.UpgradesStayEnabled := by
  intro W s s' ls hI hW h hl id c hc hut hB
  have hW' := run_chainsOnWf hI hW h hl
  obtain ⟨hC, hch⟩ := run_sysInv hI h hl
  obtain ⟨hfrom, hrz, -⟩ := edge_facts hC hut
  exact TransitionEnabled W s' id c hC hc (hch id c hc) hut
    (by rw [hfrom]; exact hW' id c hc hrz) hB

/-! ## Validated installs -/

lemma cstep_recordedWf {W : World} {s s' : CTM} {op : Op} (hR : RecordedReleasesWf W s)
    (h : CStep W s op s') (hop : op.InstallsWf W) : RecordedReleasesWf W s' := by
  intro v hv
  cases h with
  | @commit t _ _ _ _ _ _ =>
    dsimp only at hv ⊢
    by_cases hvn : v = (W.tr t).new
    · subst hvn; simp only [upd_same]; exact hop
    · rw [upd_ne _ _ hvn] at hv ⊢; exact hR v hv
  | @legacyCommit R b _ _ =>
    dsimp only at hv ⊢
    by_cases hvn : v = W.relVersion R
    · subst hvn; simp only [upd_same]; exact hop
    · rw [upd_ne _ _ hvn] at hv ⊢; exact hR v hv
  | _ => exact hR v hv

lemma step_recordedWf {W : World} {s s' : Sys} {l : Label} (hR : RecordedReleasesWf W s.ctm)
    (h : Step W s l s') (hl : l.InstallsWf W) : RecordedReleasesWf W s'.ctm := by
  cases h with
  | ctm hc => exact cstep_recordedWf hR hc hl
  | _ => exact hR

lemma run_recordedWf {W : World} {s s' : Sys} {ls : List Label} (hR : RecordedReleasesWf W s.ctm)
    (h : Run W s ls s') (hl : ∀ l ∈ ls, l.InstallsWf W) : RecordedReleasesWf W s'.ctm := by
  induction h with
  | nil => exact hR
  | cons hs _ ih =>
    exact ih (step_recordedWf hR hs (hl _ List.mem_cons_self))
      (fun l hm => hl l (List.mem_cons_of_mem _ hm))

/-- With every installed release well-formed, so are the two releases of every committed edge
and the current release. -/
lemma recorded_edge_wf {W : World} {s : CTM} (hC : CtmInv W s) (hR : RecordedReleasesWf W s)
    {v : ℕ} (hv : s.ut v ≠ 0) :
    ReleaseWf W (W.tr (s.ut v)).fromRel ∧ ReleaseWf W (W.tr (s.ut v)).newRel := by
  obtain ⟨hfrom, hrz, _, _, hnr, hnz, _⟩ := edge_facts hC hv
  exact ⟨by rw [hfrom]; exact hR _ hrz, by rw [hnr]; exact hR _ hnz⟩

lemma recorded_cur_wf {W : World} {s : CTM} (hC : CtmInv W s) (hR : RecordedReleasesWf W s) :
    ReleaseWf W s.cur := by
  have := hR s.pv (by rw [hC.curAtVersion]; exact hC.curNonzero)
  rwa [hC.curAtVersion] at this

theorem ValidatedRunsKeepEverythingEnabled :
    Properties.ValidatedRunsKeepEverythingEnabled := by
  intro W s s' ls hI hR h hl hv
  have hR' := run_recordedWf hR h hv
  obtain ⟨hC, hch⟩ := run_sysInv hI h hl
  refine ⟨fun id c hc hut => ?_, fun id hnone => ?_⟩
  · obtain ⟨hA, hB⟩ := recorded_edge_wf hC hR' hut
    exact TransitionEnabled W s' id c hC hc (hch id c hc) hut hA hB
  · exact NewChainEnabled W s' id hnone (recorded_cur_wf hC hR')

/-! ## No chain left behind -/

/-- A writer never forgets that a version was left: a filled slot stays filled, a recorded
legacy cut stays recorded. -/
lemma cstep_departed_mono {W : World} {s s' : CTM} {op : Op} (h : CStep W s op s') (v : ℕ)
    (hv : s.ut v ≠ 0 ∨ s.legacy v ≠ LegacyCut.none) :
    s'.ut v ≠ 0 ∨ s'.legacy v ≠ LegacyCut.none := by
  cases h with
  | @commit t ht0 _ _ _ _ _ =>
    dsimp only
    by_cases hvo : v = (W.tr t).old
    · subst hvo; left; simpa using ht0
    · rw [upd_ne _ _ hvo]; exact hv
  | @replace e r _ hr0 _ _ _ _ _ _ =>
    dsimp only
    by_cases hvo : v = (W.tr e).old
    · subst hvo; left; simpa using hr0
    · rw [upd_ne _ _ hvo]; exact hv
  | @legacyCommit R b _ _ =>
    dsimp only
    by_cases hvp : v = s.pv
    · subst hvp; right; cases b <;> simp
    · rw [upd_ne _ _ hvp]; exact hv
  | @legacyRecut v0 _ _ =>
    dsimp only
    by_cases hv0 : v = v0
    · subst hv0; right; simp
    · rw [upd_ne _ _ hv0]; exact hv

/-- A version edge records a way out of the version it leaves. -/
lemma cstep_departs {W : World} {s s' : CTM} {op : Op} (h : CStep W s op s') (hlt : s.pv < s'.pv) :
    s'.ut s.pv ≠ 0 ∨ s'.legacy s.pv ≠ LegacyCut.none := by
  cases h with
  | @commit t ht0 _ hpv _ _ _ =>
    left; dsimp only; rw [hpv]; simpa using ht0
  | @legacyCommit R b _ _ =>
    right; dsimp only; cases b <;> simp
  | _ => exact absurd hlt (lt_irrefl _)

lemma cstep_departedBelow {W : World} {s s' : CTM} {op : Op} (hC : CtmInv W s)
    (hD : DepartedBelow s) (h : CStep W s op s') : DepartedBelow s' := by
  intro v hv hlt
  have hmono := cstep_departed_mono h v
  cases h with
  | @commit t ht0 _ hpv hnew _ _ =>
    dsimp only at hv hlt hmono ⊢
    have hvn : v ≠ (W.tr t).new := by omega
    rw [upd_ne _ _ hvn] at hv
    have hle := (hC.relAtSound v hv).1
    by_cases hvp : v = s.pv
    · subst hvp; left; rw [hpv]; simpa using ht0
    · exact hmono (hD v hv (by omega))
  | @legacyCommit R b _ hnew =>
    dsimp only at hv hlt hmono ⊢
    have hvn : v ≠ W.relVersion R := by omega
    rw [upd_ne _ _ hvn] at hv
    have hle := (hC.relAtSound v hv).1
    by_cases hvp : v = s.pv
    · subst hvp; right; cases b <;> simp
    · exact hmono (hD v hv (by omega))
  | _ => exact hmono (hD v hv hlt)

lemma step_departedBelow {W : World} {s s' : Sys} {l : Label} (hC : CtmInv W s.ctm)
    (hD : DepartedBelow s.ctm) (h : Step W s l s') : DepartedBelow s'.ctm := by
  cases h with
  | ctm hc => exact cstep_departedBelow hC hD hc
  | _ => exact hD

lemma step_chainsAtDeparted {W : World} {s s' : Sys} {l : Label} (hI : SysInv W s)
    (hD : DepartedBelow s.ctm) (hA : ChainsAtDepartedVersions s) (h : Step W s l s')
    (hl : ¬ l.isArbitrary) : ChainsAtDepartedVersions s' := by
  obtain ⟨hC, hch⟩ := hI
  cases h with
  | @ctm op c' hc =>
    intro id c hcid hlt
    dsimp only at hlt ⊢
    have hle := (hch id c hcid).1
    by_cases hvp : c.pv = s.ctm.pv
    · rw [hvp] at hlt ⊢; exact cstep_departs hc hlt
    · exact cstep_departed_mono hc c.pv (hA id c hcid (by omega))
  | @genesis id ρ hnone hadd =>
    intro id' c hc hlt
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · exact absurd hlt (lt_irrefl _)
    · exact hA id' c hold hlt
  | @migrateIn id ρ v hv hnone hadd =>
    intro id' c hc hlt
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · subst hv; exact absurd hlt (lt_irrefl _)
    · exact hA id' c hold hlt
  | @transition id c0 ρ hc0 hut hguard happ hlt0 =>
    intro id' c hc hlt
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · obtain ⟨_, _, _, _, _, hnz, _⟩ := edge_facts hC hut
      exact hD _ hnz hlt
    · exact hA id' c hold hlt
  | @bootstrapReset id c0 R ρ hc0 hleg hadd hlt0 =>
    intro id' c hc hlt
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, hold⟩
    · obtain ⟨_, hrelR, hR⟩ := hC.bootstraps _ R hleg
      exact hD _ (by rw [hrelR]; exact hR) hlt
    · exact hA id' c hold hlt
  | arbitraryCut _ _ _ => exact absurd trivial hl

lemma run_departed {W : World} {s s' : Sys} {ls : List Label} (hI : SysInv W s)
    (hD : DepartedBelow s.ctm) (hA : ChainsAtDepartedVersions s) (h : Run W s ls s')
    (hl : ∀ l ∈ ls, ¬ l.isArbitrary) : DepartedBelow s'.ctm ∧ ChainsAtDepartedVersions s' := by
  induction h with
  | nil => exact ⟨hD, hA⟩
  | cons hs _ ih =>
    have hl0 := hl _ List.mem_cons_self
    exact ih (step_sysInv hI hs hl0) (step_departedBelow hI.1 hD hs)
      (step_chainsAtDeparted hI hD hA hs hl0) (fun l hm => hl l (List.mem_cons_of_mem _ hm))

theorem BehindChainsCanCatchUp : Properties.BehindChainsCanCatchUp := by
  intro W s s' ls hI hR hD hA h hl hv id c hc hlt
  have hR' := run_recordedWf hR h hv
  have hA' := (run_departed hI hD hA h hl).2
  obtain ⟨hC, hch⟩ := run_sysInv hI h hl
  by_cases hut : s'.ctm.ut c.pv = 0
  · have hleg : s'.ctm.legacy c.pv ≠ LegacyCut.none :=
      (hA' id c hc hlt).resolve_left (not_not.mpr hut)
    right
    cases hL : s'.ctm.legacy c.pv with
    | none => exact absurd hL hleg
    | bootstrap R =>
      left
      obtain ⟨_, hrelR, hR0⟩ := hC.bootstraps _ R hL
      have hwf : ReleaseWf W R := by
        have := hR' _ (by rw [hrelR]; exact hR0)
        rwa [hrelR] at this
      exact ⟨R, rfl, (BootstrapResetEnabledIff W s' id c hC hc).mpr ⟨R, hL, hwf⟩⟩
    | «opaque» =>
      refine Or.inr ⟨rfl, fun hT => ?_, fun hB => ?_⟩
      · exact ((TransitionEnabledIff W s' id c hC hc).mp hT).1 hut
      · obtain ⟨R, hR, -⟩ := (BootstrapResetEnabledIff W s' id c hC hc).mp hB
        rw [hL] at hR
        cases hR
  · left
    obtain ⟨hA0, hB0⟩ := recorded_edge_wf hC hR' hut
    exact TransitionEnabled W s' id c hC hc (hch id c hc) hut hA0 hB0

/-! ## Starting states -/

theorem StartingStatesMeetLivenessPremises : Properties.StartingStatesMeetLivenessPremises := by
  intro W R
  -- both starting states record a release at their own version only
  have only_top :
      ∀ w, upd (fun _ => (0 : Address)) (W.relVersion R) R w ≠ 0 → w = W.relVersion R := by
    intro w hw
    by_contra hne
    exact hw (by rw [upd_ne _ _ hne])
  refine ⟨fun hwf v hv => ?_, fun v hv hlt => ?_, fun id c hc => by simp at hc,
    fun id c hc => by simp at hc, fun old chains hold hchains => ⟨fun hwf v hv => ?_,
      fun v hv hlt => ?_, fun id c hc hrel => ?_, fun id c hc hlt => ?_⟩⟩
  · simp only [initState] at hv ⊢
    rw [only_top v hv]; simpa using hwf
  · simp only [initState] at hv hlt
    exact absurd (only_top v hv) (by omega)
  · simp only [bootstrapState] at hv ⊢
    rw [only_top v hv]; simpa using hwf
  · simp only [bootstrapState] at hv hlt
    exact absurd (only_top v hv) (by omega)
  · simp only [bootstrapState] at hrel
    have := hchains id c hc
    exact absurd (only_top _ hrel) (by omega)
  · have hle := hchains id c hc
    simp only [bootstrapState]
    right
    by_cases hco : c.pv = old
    · rw [hco]; simp
    · rw [upd_ne _ _ hco]
      have : c.pv < old := by omega
      simp [this]

/-! ## Countermodels -/

private lemma dNodup100 : ((wEnDupWorld.relRows 100).map Prod.fst).Nodup := by decide
private lemma dNodup200 : ((wEnDupWorld.relRows 200).map Prod.fst).Nodup := by decide
private lemma dDup260 : ¬ ((wEnDupWorld.relRows 260).map Prod.fst).Nodup := by decide
private lemma dDup150 : ¬ ((wEnDupWorld.relRows 150).map Prod.fst).Nodup := by decide

theorem DuplicateSelectorBricksEdge : Properties.DuplicateSelectorBricksEdge := by
  have hI0 : SysInv wEnDupWorld wEnDupSys0 := FreshSystemSatisfiesInvariant wEnDupWorld 100 (by decide)
  have hL := StartingStatesMeetLivenessPremises wEnDupWorld 100
  have hrun := Run.cons (W := wEnDupWorld)
    (Step.genesis (s := wEnDupSys0) (id := 0) rfl (addAll_empty_eq dNodup100))
    (Run.cons (Step.ctm (CStep.commit (t := 700) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))) Run.nil)
  have hl : ∀ l ∈ [Label.genesis 0, .ctm (.commit 700)], ¬ l.isArbitrary := by
    simp [Label.isArbitrary]
  have hI := run_sysInv hI0 hrun hl
  refine ⟨⟨by decide, by decide⟩, hI0, hL.1 dNodup100, hL.2.2.1, _, hrun, hl, hI, dDup260,
    ⟨_, rfl, rfl, rfl, hI.2 0 _ rfl, dNodup100, dDup260⟩, ?_, rfl, ?_, ?_⟩
  · rintro ⟨s', hs'⟩
    rcases (TransitionEnabledIff _ _ 0 _ hI.1 rfl).mp ⟨s', hs'⟩ with ⟨_, _, hAB | ⟨_, hB⟩⟩
    · exact absurd hAB (by decide)
    · exact dDup260 hB
  · rintro ⟨s', hs'⟩
    exact dDup260 ((NewChainEnabledIff _ _ 1).1.mp ⟨s', hs'⟩).2
  · rintro ⟨s', hs'⟩
    exact dDup260 ((NewChainEnabledIff _ _ 1).2.mp ⟨s', hs'⟩).2

theorem DepartingDuplicateBlocksTransition :
    Properties.DepartingDuplicateBlocksTransition := by
  have hI0 : SysInv wEnDupWorld wDupDepSys := by
    refine ⟨InitSatisfiesInvariant wEnDupWorld 150 (by decide), ?_⟩
    intro id c hc
    simp only [wDupDepSys] at hc
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, h'⟩
    · exact ⟨by decide, fun _ => rfl⟩
    · simp at h'
  have hrun := Run.cons (W := wEnDupWorld)
    (Step.ctm (s := wDupDepSys) (CStep.commit (t := 800) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide))) Run.nil
  have hI := run_sysInv hI0 hrun (by simp [Label.isArbitrary])
  refine ⟨⟨by decide, by decide⟩, hI0, fun hW => dDup150 (hW 0 _ rfl (by decide)),
    ⟨_, hrun, hI, ⟨_, rfl, rfl, rfl, hI.2 0 _ rfl, dDup150, dNodup200⟩, ?_⟩, ?_⟩
  · rintro ⟨s', hs'⟩
    rcases (TransitionEnabledIff _ _ 0 _ hI.1 rfl).mp ⟨s', hs'⟩ with ⟨_, _, hAB | ⟨hA, _⟩⟩
    · exact absurd hAB (by decide)
    · exact dDup150 hA
  · rintro ⟨s', hs'⟩
    exact dDup150 ((NewChainEnabledIff _ _ 0).1.mp ⟨s', hs'⟩).2

/-! ## Witnesses -/

private lemma eNodup100 : ((wWorld.relRows 100).map Prod.fst).Nodup := by decide
private lemma eNodup200 : ((wWorld.relRows 200).map Prod.fst).Nodup := by decide
private lemma eNodup250 : ((wWorld.relRows 250).map Prod.fst).Nodup := by decide

theorem EnablednessWitness : Properties.EnablednessWitness := by
  have hI0 : SysInv wWorld wSys0 := FreshSystemSatisfiesInvariant wWorld 100 (by decide)
  have hL := StartingStatesMeetLivenessPremises wWorld 100
  have hrun := Run.cons (W := wWorld)
    (Step.genesis (s := wSys0) (id := 0) rfl (addAll_empty_eq eNodup100))
    (Run.cons (Step.ctm (CStep.commit (t := 300) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))) Run.nil)
  have hl : ∀ l ∈ [Label.genesis 0, .ctm (.commit 300)], ¬ l.isArbitrary ∧ l.InstallsWf wWorld := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨id, trivial⟩, ⟨id, eNodup200⟩⟩
  have hI := run_sysInv hI0 hrun (fun l hm => (hl l hm).1)
  obtain ⟨hT, hN⟩ := ValidatedRunsKeepEverythingEnabled _ _ _ _ hI0 (hL.1 eNodup100) hrun
    (fun l hm => (hl l hm).1) (fun l hm => (hl l hm).2)
  exact ⟨hI0, hL.1 eNodup100, hL.2.2.1, _, hrun, hl, hI,
    ⟨_, rfl, rfl, hI.2 0 _ rfl, by decide, eNodup100, eNodup200, by decide, hT 0 _ rfl (by decide)⟩,
    rfl, eNodup200, hN 1 rfl⟩

theorem CatchUpWitness : Properties.CatchUpWitness := by
  have hchains : ∀ id c, wLagSys.chains id = some c → c.pv ≤ 1 := by
    intro id c hc
    rcases upd_chain hc with ⟨_, rfl⟩ | ⟨_, h'⟩
    · exact le_rfl
    · rcases upd_chain h' with ⟨_, rfl⟩ | ⟨_, h''⟩
      · exact Nat.zero_le _
      · simp at h''
  have hI0 : SysInv wWorld wLagSys :=
    BootstrapSystemSatisfiesInvariant wWorld 1 200 wLagSys.chains (by decide) (by decide) hchains
  have hL := (StartingStatesMeetLivenessPremises wWorld 200).2.2.2.2 1 wLagSys.chains
    (by decide) hchains
  have hrun := Run.cons (W := wWorld)
    (Step.genesis (s := wLagSys) (id := 0) rfl (addAll_empty_eq eNodup200))
    (Run.cons (Step.ctm (CStep.commit (t := 600) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide))) Run.nil)
  have hl : ∀ l ∈ [Label.genesis 0, .ctm (.commit 600)], ¬ l.isArbitrary ∧ l.InstallsWf wWorld := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨⟨id, trivial⟩, ⟨id, eNodup250⟩⟩
  have hI := run_sysInv hI0 hrun (fun l hm => (hl l hm).1)
  obtain ⟨hT, -⟩ := ValidatedRunsKeepEverythingEnabled _ _ _ _ hI0 (hL.1 eNodup200) hrun
    (fun l hm => (hl l hm).1) (fun l hm => (hl l hm).2)
  refine ⟨eNodup200, by decide, hchains, rfl, hI0, hL.1 eNodup200, hL.2.1, hL.2.2.2, _, hrun, hl,
    rfl, ⟨_, rfl, rfl, hT 0 _ rfl (by decide)⟩,
    ⟨_, rfl, rfl, rfl, (BootstrapResetEnabledIff _ _ 6 _ hI.1 rfl).mpr ⟨200, rfl, eNodup200⟩⟩,
    ⟨_, rfl, rfl, rfl, ?_, ?_⟩⟩
  · rintro ⟨s', hs'⟩
    exact ((TransitionEnabledIff _ _ 5 _ hI.1 rfl).mp ⟨s', hs'⟩).1 rfl
  · rintro ⟨s', hs'⟩
    obtain ⟨R, hR, -⟩ := (BootstrapResetEnabledIff _ _ 5 _ hI.1 rfl).mp ⟨s', hs'⟩
    have h0 : LegacyCut.opaque = LegacyCut.bootstrap R := hR
    cases h0

end Contracts.ChainTypeManager
