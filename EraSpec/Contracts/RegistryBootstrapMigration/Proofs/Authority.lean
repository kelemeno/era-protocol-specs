import EraSpec.Contracts.RegistryBootstrapMigration.Properties.Authority

/-!
# Proofs: the bootstrap does not park authority on itself

`migrate()`'s post-state is a closed form (`MigrateStep` has one constructor), so the
properties of `migrate()` and of the bundle are computations on it. The run properties are
inductions over transactions.
-/

namespace Contracts.RegistryBootstrapMigration

/-! ## The closed form of `migrate()` -/

lemma migrate_eq {K : Config} {s s' : AState} (h : MigrateStep K s s') :
    s' = executorAccept K (handOn K (claim K s)) := by
  cases h; rfl

lemma migrate_guards {K : Config} {s s' : AState} (h : MigrateStep K s s') :
    s.executed = false ∧ (claim K s).ctmOwner = K.M ∧ s.paOwner = K.M ∧ ExecutorAuthorities K ∧
      s.ctmPv = K.m.expectedPv ∧ K.notifierOk = true ∧ K.m.expectedPv < K.m.newPv := by
  cases h with
  | mk h1 h2 h3 h4 h5 h6 h7 _ => exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

lemma executorAccept_genuine {K : Config} {e : ExecView} (he : K.exec K.m.E = some e)
    (hg : e.genuineAccept = true) (t : AState) :
    executorAccept K t = { t with ctmOwner := K.m.E, ctmPending := 0 } := by
  simp [executorAccept, he, hg]

lemma executorAccept_nongenuine {K : Config} {e : ExecView} (he : K.exec K.m.E = some e)
    (hg : e.genuineAccept = false) (t : AState) : executorAccept K t = t := by
  simp [executorAccept, he, hg]

/-- The executor is not the migration: the migration answers no executor getter. -/
lemma exec_ne_mig {K : Config} {a : Address} {e : ExecView} (he : K.exec a = some e) :
    a ≠ K.M := by
  intro h; subst h; rw [K.migNoExec] at he; exact Option.noConfusion he

lemma executorAuthorities_E {K : Config} (h : ExecutorAuthorities K) :
    ∃ e, K.exec K.m.E = some e := by
  obtain ⟨e, _, he, _⟩ := h; exact ⟨e, he⟩

/-! ## `migrate()` itself -/

theorem MigrateLeavesNothingParked : Properties.MigrateLeavesNothingParked := by
  intro K s s' hgen h
  obtain ⟨_, _, _, hA, _, hN, _⟩ := migrate_guards h
  obtain ⟨e, he⟩ := executorAuthorities_E hA
  have hEM := exec_ne_mig he
  rw [migrate_eq h, executorAccept_genuine he (hgen e he)]
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · rintro (h1 | h2 | h3)
    · exact hEM h1
    · exact K.migNonzero h2.symm
    · exact hEM h3
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, hA, hN⟩

theorem MigrateIsOneShot : Properties.MigrateIsOneShot := by
  intro K s s' h
  have hx : s'.executed = true := by
    rw [migrate_eq h]
    unfold executorAccept
    split
    · split <;> rfl
    · rfl
  refine ⟨hx, ?_⟩
  rintro ⟨s'', h'⟩
  have := (migrate_guards h').1
  rw [hx] at this
  exact Bool.noConfusion this

lemma step_spent {K : Config} {s s' : AState} {l : Label} (hx : s.executed = true)
    (h : AStep K s l s') : s'.executed = true ∧ l ≠ .migrate ∧ l ≠ .bundle := by
  cases h with
  | nominate _ => exact ⟨hx, by simp, by simp⟩
  | accept _ _ => exact ⟨hx, by simp, by simp⟩
  | transferPA _ _ => exact ⟨hx, by simp, by simp⟩
  | legacyMove _ => exact ⟨hx, by simp, by simp⟩
  | migrate hm =>
    have := (migrate_guards hm).1; rw [hx] at this; exact Bool.noConfusion this
  | bundle _ _ hm _ =>
    have := (migrate_guards hm).1; simp only at this; rw [hx] at this; exact Bool.noConfusion this

theorem NoReparkingAfterMigrate : Properties.NoReparkingAfterMigrate := by
  intro K s s' ls hx hp h hl
  induction h with
  | nil => exact hp
  | @cons s1 s2 s3 l ls hs _ ih =>
    have hl0 : ¬ l.handsToMigration K := hl l (List.mem_cons_self _ _)
    have hx2 := (step_spent hx hs).1
    apply ih hx2 _ (fun l' hm => hl l' (List.mem_cons_of_mem _ hm))
    simp only [ParkedOnMigration, not_or] at hp ⊢
    obtain ⟨ho, hpe, hpa⟩ := hp
    cases hs with
    | @nominate x _ =>
      exact ⟨ho, fun h => hl0 (by simp [Label.handsToMigration]; exact h), hpa⟩
    | accept _ _ => exact ⟨hpe, fun h => K.migNonzero h.symm, hpa⟩
    | @transferPA x _ _ =>
      exact ⟨ho, hpe, fun h => hl0 (by simp [Label.handsToMigration]; exact h)⟩
    | legacyMove _ => exact ⟨ho, hpe, hpa⟩
    | migrate hm => exact absurd rfl (step_spent hx (AStep.migrate hm)).2.1
    | bundle a b hm c => exact absurd rfl (step_spent hx (AStep.bundle a b hm c)).2.2

/-! ## The bundle -/

theorem ValidateAppliedExcludesParking : Properties.ValidateAppliedExcludesParking := by
  rintro K s ⟨_, _, _, ho, hpe, hpa, hA, _⟩
  obtain ⟨e, he⟩ := executorAuthorities_E hA
  have hEM := exec_ne_mig he
  refine ⟨?_, hpe⟩
  rintro (h1 | h2 | h3)
  · exact hEM (ho ▸ h1)
  · exact K.migNonzero (hpe ▸ h2).symm
  · exact hEM (hpa ▸ h3)

theorem BundleNeverParks : Properties.BundleNeverParks := by
  intro K s s' h
  cases h with
  | bundle _ _ _ hv =>
    have hnp := (ValidateAppliedExcludesParking K s' hv).1
    obtain ⟨_, _, _, ho, hpe, hpa, _⟩ := hv
    exact ⟨ho, hpe, hpa, hnp⟩

/-! ## Countermodels and frames -/

theorem ParkedCTMLeavesOnlyByNomineeAccept : Properties.ParkedCTMLeavesOnlyByNomineeAccept := by
  intro K s s' l ho hx h
  cases h with
  | nominate hne => exact absurd ho hne
  | accept _ hpM => exact Or.inr ⟨rfl, rfl, hpM⟩
  | transferPA _ _ => exact Or.inl ⟨ho, rfl⟩
  | legacyMove hne => exact absurd ho hne
  | migrate hm =>
    have := (migrate_guards hm).1; rw [hx] at this; exact Bool.noConfusion this
  | bundle hne _ _ _ => exact absurd ho hne

theorem ProxyAdminLeavesMigrationOnlyByMigrate :
    Properties.ProxyAdminLeavesMigrationOnlyByMigrate := by
  intro K s s' l hpa h
  cases h with
  | nominate _ => exact Or.inl hpa
  | accept _ _ => exact Or.inl hpa
  | transferPA hne _ => exact absurd hpa hne
  | legacyMove _ => exact Or.inl hpa
  | migrate _ => exact Or.inr rfl
  | bundle _ hne _ _ => exact absurd hpa hne

private lemma wAuth (g : Bool) : ExecutorAuthorities (wConfig g) :=
  ⟨⟨9, 0, 1, 2, g⟩, ⟨9, 0, 0, 0, true⟩, by simp [wConfig, wExec, wManifest],
    by simp [wConfig, wExec, wManifest], rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The governance hand-over, then `migrate()`, in the witness configuration. -/
private lemma wMigrate (g : Bool) :
    MigrateStep (wConfig g) { wPre with ctmPending := 50, paOwner := 50 }
      (executorAccept (wConfig g) (handOn (wConfig g)
        (claim (wConfig g) { wPre with ctmPending := 50, paOwner := 50 }))) :=
  MigrateStep.mk rfl (by cases g <;> decide) rfl (wAuth g) rfl rfl (by cases g <;> decide)
    (by cases g <;> decide)

theorem NonGenuineExecutorParksTheCTM : Properties.NonGenuineExecutorParksTheCTM := by
  have hcomp : executorAccept (wConfig false) (handOn (wConfig false)
      (claim (wConfig false) { wPre with ctmPending := 50, paOwner := 50 })) =
      ⟨50, 3, 3, 35, 60, true⟩ := by decide
  refine ⟨_, wMigrate false, by rw [hcomp], by rw [hcomp], by rw [hcomp],
    by rw [hcomp]; exact Or.inl rfl, ?_, ?_⟩
  · rw [hcomp]; rintro ⟨_, _, _, ho, _⟩; exact absurd ho (by decide)
  · rintro ⟨s'', h⟩
    cases h with
    | bundle _ _ hm hv =>
      rw [migrate_eq hm] at hv
      obtain ⟨_, _, _, ho, _⟩ := hv
      exact absurd ho (by decide)

theorem SplitBundleParksProxyAdmin : Properties.SplitBundleParksProxyAdmin := by
  have hrun : ARun (wConfig true) wPreDrift [.nominate 50, .transferPA 50] ⟨9, 50, 50, 33, 0, false⟩ :=
    ARun.cons (AStep.nominate (by decide))
      (ARun.cons (AStep.transferPA (by decide) (by decide)) ARun.nil)
  refine ⟨_, hrun, rfl, Or.inr (Or.inr rfl), ?_, ?_⟩
  · rintro ⟨s', h⟩
    have := (migrate_guards h).2.2.2.2.1
    exact absurd this (by decide)
  · rintro ⟨s', h⟩
    cases h with
    | bundle _ _ hm _ =>
      have := (migrate_guards hm).2.2.2.2.1
      exact absurd this (by decide)

/-! ## Witnesses -/

theorem MigrateWitness : Properties.MigrateWitness := by
  have hrun : ARun (wConfig true) wPre [.nominate 50, .transferPA 50]
      { wPre with ctmPending := 50, paOwner := 50 } :=
    ARun.cons (AStep.nominate (by decide))
      (ARun.cons (AStep.transferPA (by decide) (by decide)) ARun.nil)
  have hcomp : executorAccept (wConfig true) (handOn (wConfig true)
      (claim (wConfig true) { wPre with ctmPending := 50, paOwner := 50 })) =
      ⟨3, 0, 3, 35, 60, true⟩ := by decide
  refine ⟨_, _, hrun, rfl, rfl, wMigrate true, ?_⟩
  rw [hcomp]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem BundleWitness : Properties.BundleWitness := by
  have hcomp : executorAccept (wConfig true) (handOn (wConfig true)
      (claim (wConfig true) { wPre with ctmPending := 50, paOwner := 50 })) =
      ⟨3, 0, 3, 35, 60, true⟩ := by decide
  refine ⟨_, AStep.bundle (by decide) (by decide) (wMigrate true) ?_, ?_, ?_⟩
  · rw [hcomp]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, wAuth true, rfl⟩
  · rw [hcomp]
  · rw [hcomp]

theorem ParkedFramesFire : Properties.ParkedFramesFire := by
  have hcomp : executorAccept (wConfig false) (handOn (wConfig false)
      (claim (wConfig false) { wPre with ctmPending := 50, paOwner := 50 })) =
      ⟨50, 3, 3, 35, 60, true⟩ := by decide
  have hm : MigrateStep (wConfig false) { wPre with ctmPending := 50, paOwner := 50 }
      ⟨50, 3, 3, 35, 60, true⟩ := hcomp ▸ wMigrate false
  refine ⟨⟨_, _, hm, rfl, rfl, AStep.accept (by decide) (by decide), rfl⟩, ?_⟩
  · refine ⟨⟨9, 50, 50, 33, 0, false⟩, ARun.cons (AStep.nominate (by decide))
      (ARun.cons (AStep.transferPA (by decide) (by decide)) ARun.nil), rfl, ?_⟩
    rintro ⟨s', h⟩
    cases h with
    | transferPA hne _ => exact hne rfl

end Contracts.RegistryBootstrapMigration
