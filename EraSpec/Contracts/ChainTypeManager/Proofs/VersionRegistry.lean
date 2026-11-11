import EraSpec.Contracts.ChainTypeManager.Properties.VersionRegistry

/-!
# Proofs: the CTM's protocol version and transition registry

One invariant, `CtmInv`, carries everything: `step_inv` shows each writer preserves it,
and the properties read it off. Write-once-per-commit needs no invariant at all — only
that a commit writes the slot of the current version and then moves past it
(`run_departure_ge`). The witness and the countermodel are concrete runs over
`wWorld`, checked by `decide`.
-/

namespace Contracts.ChainTypeManager

/-! ## Point updates -/

@[simp] lemma upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

lemma upd_ne {α β : Type} [DecidableEq α] (f : α → β) {x a : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

/-! ## One step -/

lemma cstep_pv {W : World} {s s' : CTM} {op : Op} (h : CStep W s op s') :
    s.pv ≤ s'.pv ∧ (op.isEdge = true → s.pv < s'.pv) ∧ (op.isEdge = false → s'.pv = s.pv) := by
  cases h with
  | commit _ _ hpv hlt _ _ =>
      dsimp only
      refine ⟨by omega, fun _ => by omega, fun h => by simp [Op.isEdge] at h⟩
  | replace _ _ _ _ _ _ _ _ =>
      exact ⟨le_rfl, fun h => by simp [Op.isEdge] at h, fun _ => rfl⟩
  | legacyCommit _ hlt =>
      dsimp only
      refine ⟨by omega, fun _ => hlt, fun h => by simp [Op.isEdge] at h⟩
  | legacyRecut _ _ =>
      exact ⟨le_rfl, fun h => by simp [Op.isEdge] at h, fun _ => rfl⟩

/-- Releases already recorded at or below the current version never change. -/
lemma cstep_relAt_low {W : World} {s s' : CTM} {op : Op} (h : CStep W s op s') :
    ∀ w, w ≤ s.pv → s'.relAt w = s.relAt w := by
  intro w hw
  cases h with
  | commit _ _ hpv hlt _ _ =>
      dsimp only
      exact upd_ne _ _ (by omega)
  | replace _ _ _ _ _ _ _ _ => rfl
  | legacyCommit _ hlt =>
      dsimp only
      exact upd_ne _ _ (by omega)
  | legacyRecut _ _ => rfl

/-- **The invariant is preserved by every writer.** -/
theorem step_inv {W : World} {s s' : CTM} {op : Op} (hI : CtmInv W s)
    (h : CStep W s op s') : CtmInv W s' := by
  have hlow := cstep_relAt_low h
  have hpvle := (cstep_pv h).1
  cases h with
  | @commit t ht0 hfrom hpv hlt hnr hver =>
    -- the new release is recorded only at the new version, above everything committed
    have relAt'_eq : ∀ w, w ≠ (W.tr t).new → upd s.relAt (W.tr t).new (W.tr t).newRel w = s.relAt w :=
      fun w hw => upd_ne _ _ hw
    refine ⟨hnr, by simp, ?_, ?_, ?_⟩
    · intro w hw
      dsimp only at hw ⊢
      by_cases hwn : w = (W.tr t).new
      · subst hwn
        simp only [upd_same] at hw ⊢
        exact ⟨le_rfl, hver⟩
      · rw [relAt'_eq w hwn] at hw ⊢
        have := hI.relAtSound w hw
        exact ⟨by omega, this.2⟩
    · intro v hv
      dsimp only at hv ⊢
      by_cases hvo : v = (W.tr t).old
      · subst hvo
        simp only [upd_same]
        have hcur : s.relAt s.pv = s.cur := hI.curAtVersion
        have hne : (W.tr t).old ≠ (W.tr t).new := by omega
        refine ⟨hlt, ?_, ?_, hlt, by simp, by simp [hnr]⟩
        · rw [relAt'_eq _ hne, ← hpv, hcur, hfrom]
        · rw [relAt'_eq _ hne, ← hpv, hcur]; exact hI.curNonzero
      · rw [upd_ne _ _ hvo] at hv ⊢
        obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.slots v hv
        have hnew_le : (W.tr (s.ut v)).new ≤ s.pv := (hI.relAtSound _ h6).1
        have hv_ne : v ≠ (W.tr t).new := by omega
        have hw_ne : (W.tr (s.ut v)).new ≠ (W.tr t).new := by omega
        refine ⟨by omega, ?_, ?_, h4, ?_, ?_⟩
        · rw [relAt'_eq _ hv_ne]; exact h2
        · rw [relAt'_eq _ hv_ne]; exact h3
        · rw [relAt'_eq _ hw_ne]; exact h5
        · rw [relAt'_eq _ hw_ne]; exact h6
    · intro v R hb
      obtain ⟨h1, h2, h3⟩ := hI.bootstraps v R hb
      have : W.relVersion R ≤ s.pv := by
        have := (hI.relAtSound _ (by rw [h2]; exact h3)).1; exact this
      refine ⟨h1, ?_, h3⟩
      dsimp only
      rw [relAt'_eq _ (by omega)]; exact h2
  | @replace e r he0 hr0 hslot hre hfrom hge hcur hon =>
    refine ⟨hI.curNonzero, hI.curAtVersion, hI.relAtSound, ?_, hI.bootstraps⟩
    intro v hv
    dsimp only at hv ⊢
    by_cases hvo : v = (W.tr e).old
    · subst hvo
      simp only [upd_same]
      have he : s.ut (W.tr e).old ≠ 0 := by rw [hslot]; exact he0
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.slots _ he
      rw [hslot] at h2 h4 h5 h6
      refine ⟨h1, by rw [hfrom, h2], h3, by omega, ?_⟩
      by_cases hp : (W.tr r).new = s.pv
      · have hc := hcur hp
        rw [hc, hp, hI.curAtVersion]
        exact ⟨rfl, hI.curNonzero⟩
      · obtain ⟨hut, hnr⟩ := hon hp
        obtain ⟨_, k2, k3, _, _, _⟩ := hI.slots _ hut
        rw [hnr, k2]
        exact ⟨rfl, k3⟩
    · rw [upd_ne _ _ hvo] at hv ⊢
      exact hI.slots v hv
  | @legacyCommit R b hR hlt =>
    have relAt'_eq : ∀ w, w ≠ W.relVersion R → upd s.relAt (W.relVersion R) R w = s.relAt w :=
      fun w hw => upd_ne _ _ hw
    refine ⟨hR, by simp, ?_, ?_, ?_⟩
    · intro w hw
      dsimp only at hw ⊢
      by_cases hwn : w = W.relVersion R
      · subst hwn; exact ⟨le_rfl, by simp⟩
      · rw [relAt'_eq w hwn] at hw ⊢
        have := hI.relAtSound w hw
        exact ⟨by omega, this.2⟩
    · intro v hv
      dsimp only at hv ⊢
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hI.slots v hv
      have hnew_le : (W.tr (s.ut v)).new ≤ s.pv := (hI.relAtSound _ h6).1
      refine ⟨by omega, ?_, ?_, h4, ?_, ?_⟩
      · rw [relAt'_eq _ (by omega)]; exact h2
      · rw [relAt'_eq _ (by omega)]; exact h3
      · rw [relAt'_eq _ (by omega)]; exact h5
      · rw [relAt'_eq _ (by omega)]; exact h6
    · intro v R' hb
      dsimp only at hb ⊢
      by_cases hvp : v = s.pv
      · subst hvp
        simp only [upd_same] at hb
        cases b
        · simp at hb
        · simp only [ite_true, LegacyCut.bootstrap.injEq] at hb
          subst hb
          exact ⟨hlt, by simp, hR⟩
      · rw [upd_ne _ _ hvp] at hb
        obtain ⟨h1, h2, h3⟩ := hI.bootstraps v R' hb
        have : W.relVersion R' ≤ s.pv := (hI.relAtSound _ (by rw [h2]; exact h3)).1
        exact ⟨h1, by rw [relAt'_eq _ (by omega)]; exact h2, h3⟩
  | @legacyRecut v0 hut hleg =>
    refine ⟨hI.curNonzero, hI.curAtVersion, hI.relAtSound, hI.slots, ?_⟩
    intro v R hb
    dsimp only at hb
    by_cases hv : v = v0
    · subst hv; simp at hb
    · rw [upd_ne _ _ hv] at hb
      exact hI.bootstraps v R hb

lemma run_inv {W : World} {s s' : CTM} {ops : List Op} (hI : CtmInv W s)
    (h : CRun W s ops s') : CtmInv W s' := by
  induction h with
  | nil => exact hI
  | cons hs _ ih => exact ih (step_inv hI hs)

/-! ## Starting states -/

theorem InitSatisfiesInvariant : Properties.InitSatisfiesInvariant := by
  intro W R hR
  refine ⟨hR, by simp [initState], ?_, ?_, ?_⟩
  · intro w hw
    simp only [initState] at hw ⊢
    by_cases hwv : w = W.relVersion R
    · subst hwv; simp
    · rw [upd_ne _ _ hwv] at hw; exact absurd rfl hw
  · intro v hv; exact absurd rfl hv
  · intro v R' hb; simp [initState] at hb

theorem BootstrapSatisfiesInvariant : Properties.BootstrapSatisfiesInvariant := by
  intro W old R hR hlt
  refine ⟨hR, by simp [bootstrapState], ?_, ?_, ?_⟩
  · intro w hw
    simp only [bootstrapState] at hw ⊢
    by_cases hwv : w = W.relVersion R
    · subst hwv; simp
    · rw [upd_ne _ _ hwv] at hw; exact absurd rfl hw
  · intro v hv; exact absurd rfl hv
  · intro v R' hb
    simp only [bootstrapState] at hb ⊢
    by_cases hvo : v = old
    · subst hvo
      simp only [upd_same, LegacyCut.bootstrap.injEq] at hb
      subst hb
      exact ⟨hlt, by simp, hR⟩
    · rw [upd_ne _ _ hvo] at hb
      split_ifs at hb

theorem StepPreservesInvariant : Properties.StepPreservesInvariant :=
  fun _ _ _ _ hI h => step_inv hI h

/-! ## The current release -/

theorem CurrentReleaseIsVersionsRelease : Properties.CurrentReleaseIsVersionsRelease := by
  intro W s s' ops hI h
  have hI' := run_inv hI h
  refine ⟨hI'.curNonzero, ?_⟩
  have := (hI'.relAtSound s'.pv (by rw [hI'.curAtVersion]; exact hI'.curNonzero)).2
  rwa [hI'.curAtVersion] at this

/-! ## Versions only go up -/

theorem VersionStrictlyIncreasesOnEdges : Properties.VersionStrictlyIncreasesOnEdges :=
  fun _ _ _ _ h => cstep_pv h

theorem VersionsIncreaseAlongRuns : Properties.VersionsIncreaseAlongRuns := by
  intro W s s' ops h
  induction h with
  | nil => exact ⟨le_rfl, fun h => by simp at h⟩
  | @cons s s1 s2 op ops hs _ ih =>
    obtain ⟨h1, h2, _⟩ := cstep_pv hs
    refine ⟨le_trans h1 ih.1, fun hany => ?_⟩
    simp only [List.any_cons, Bool.or_eq_true] at hany
    rcases hany with he | he
    · exact lt_of_lt_of_le (h2 he) ih.1
    · exact lt_of_le_of_lt h1 (ih.2 he)

/-! ## Writing `upgradeTransition` -/

theorem CommitWritesOnlyEmptySlots : Properties.CommitWritesOnlyEmptySlots := by
  intro W s s' t hI h
  cases h with
  | commit _ _ hpv _ _ _ =>
    by_contra hne
    have := (hI.slots _ hne).1
    omega

/-- A commit departs from the version it finds. -/
lemma commit_departure {W : World} {s s' : CTM} {op : Op} {v : ℕ}
    (h : CStep W s op s') (hd : op.commitDeparture W = some v) : v = s.pv ∧ s.pv < s'.pv := by
  cases h with
  | commit _ _ hpv hlt _ _ =>
    simp only [Op.commitDeparture, Option.some.injEq] at hd
    dsimp only
    omega
  | replace _ _ _ _ _ _ _ _ => simp [Op.commitDeparture] at hd
  | legacyCommit _ _ => simp [Op.commitDeparture] at hd
  | legacyRecut _ _ => simp [Op.commitDeparture] at hd

/-- Every commit in a run departs at or above the run's starting version. -/
lemma run_departure_ge {W : World} {s s' : CTM} {ops : List Op} (h : CRun W s ops s') :
    ∀ op ∈ ops, ∀ v, op.commitDeparture W = some v → s.pv ≤ v := by
  induction h with
  | nil => intro op hop; simp at hop
  | @cons s s1 _ op ops hs _ ih =>
    intro op' hop v hd
    rcases List.mem_cons.mp hop with rfl | hrest
    · exact le_of_eq (commit_departure hs hd).1.symm
    · exact le_trans (cstep_pv hs).1 (ih op' hrest v hd)

theorem CommitWritesEachSlotOnce : Properties.CommitWritesEachSlotOnce := by
  intro W s s' ops h
  induction h with
  | nil => intro _; simp
  | @cons s s1 s2 op ops hs hr ih =>
    intro v
    rw [List.countP_cons]
    by_cases hd : op.commitDeparture W = some v
    · have ⟨hv, hlt⟩ := commit_departure hs hd
      have hzero : ops.countP (fun op => decide (op.commitDeparture W = some v)) = 0 := by
        rw [List.countP_eq_zero]
        intro op' hop' hd'
        have := run_departure_ge hr op' hop' v (of_decide_eq_true hd')
        omega
      simp [hd, hzero]
    · simp only [hd, decide_false]
      exact ih v

theorem OnlyCommitOrReplaceWritesSlots : Properties.OnlyCommitOrReplaceWritesSlots := by
  intro W s s' op v hI h hne
  have hI0 := hI
  cases h with
  | @commit t ht0 hfrom hpv hlt hnr hver =>
    dsimp only at hne
    by_cases hvo : v = (W.tr t).old
    · subst hvo
      left
      refine ⟨t, rfl, rfl, ?_, by simp⟩
      by_contra hz
      have := (hI0.slots _ hz).1
      omega
    · rw [upd_ne _ _ hvo] at hne; exact absurd rfl hne
  | @replace e r he0 hr0 hslot _ _ _ _ _ =>
    dsimp only at hne
    by_cases hvo : v = (W.tr e).old
    · subst hvo
      right
      exact ⟨e, r, rfl, rfl, hslot, by simp, hr0⟩
    · rw [upd_ne _ _ hvo] at hne; exact absurd rfl hne
  | legacyCommit _ _ => exact absurd rfl hne
  | legacyRecut _ _ => exact absurd rfl hne

/-! ## Transitions chain -/

theorem TransitionsChain : Properties.TransitionsChain := by
  intro W s hI v hv
  obtain ⟨_, h2, h3, h4, h5, h6⟩ := hI.slots v hv
  have hw := hI.relAtSound _ h6
  have hfv := (hI.relAtSound _ h3).2
  refine ⟨h2, by rw [h2]; exact hfv, h4, hw.1, h5, by rw [h5]; exact hw.2, ?_, ?_⟩
  · intro hp; rw [h5, hp, hI.curAtVersion]
  · intro hnext
    rw [(hI.slots _ hnext).2.1, h5]

theorem ExecutorPostcheckPasses : Properties.ExecutorPostcheckPasses := by
  intro W s s' t h
  cases h with
  | commit _ _ _ _ _ _ => exact ⟨by simp, le_rfl⟩

theorem SlotsDepartFromTheirVersion : Properties.SlotsDepartFromTheirVersion := by
  intro W s s' ops hI hold hgen h
  induction h with
  | nil => exact hold
  | @cons s s1 s2 op ops hs _ ih =>
    apply ih (step_inv hI hs) _ (fun e r hm => hgen e r (List.mem_cons_of_mem _ hm))
    intro v hv
    cases hs with
    | @commit t _ _ _ _ _ _ =>
      dsimp only at hv ⊢
      by_cases hvo : v = (W.tr t).old
      · subst hvo; simp
      · rw [upd_ne _ _ hvo] at hv ⊢; exact hold v hv
    | @replace e r he0 _ hslot _ hfrom _ _ _ =>
      dsimp only at hv ⊢
      by_cases hvo : v = (W.tr e).old
      · subst hvo
        simp only [upd_same]
        have he : s.ut (W.tr e).old ≠ 0 := by rw [hslot]; exact he0
        obtain ⟨_, k2, k3, _, _, _⟩ := hI.slots _ he
        rw [hslot] at k2
        rw [hgen e r (List.mem_cons_self), hfrom, k2]
        exact (hI.relAtSound _ k3).2
      · rw [upd_ne _ _ hvo] at hv ⊢; exact hold v hv
    | legacyCommit _ _ => exact hold v hv
    | legacyRecut _ _ => exact hold v hv

/-! ## Witnesses -/

theorem VersionRegistryWitness : Properties.VersionRegistryWitness := by
  refine ⟨_, CRun.cons (CStep.commit ?_ ?_ ?_ ?_ ?_ ?_)
    (CRun.cons (CStep.commit ?_ ?_ ?_ ?_ ?_ ?_)
      (CRun.cons (CStep.replace ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) CRun.nil)),
    InitSatisfiesInvariant _ _ (by decide),
    by decide, by decide, by decide, by decide, by decide, ⟨by decide, by decide⟩, by decide⟩
  all_goals decide

theorem NonGenuineReplacementBreaksSlotVersion :
    Properties.NonGenuineReplacementBreaksSlotVersion := by
  refine ⟨_, CRun.cons (CStep.commit ?_ ?_ ?_ ?_ ?_ ?_)
    (CRun.cons (CStep.replace ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_) CRun.nil),
    by decide, by decide, fun h => absurd h.1 (by decide)⟩
  all_goals decide

end Contracts.ChainTypeManager
