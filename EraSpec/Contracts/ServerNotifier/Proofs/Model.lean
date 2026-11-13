import EraSpec.Contracts.ServerNotifier.Properties.Model

/-!
# Proofs: who can set a chain's upgrade timestamp

Run-level results are inductions on `Reach`; one-step results are case analyses of `Step`.
The witnesses use concrete CTM views (`viewOf admin`) and environments that answer at one
address only (`envAt`).
-/

namespace Contracts.ServerNotifier

/-- A CTM view naming `admin` as every chain's admin, at version `3`, with a transition
scheduled from every version. -/
private def viewOf (admin : Address) : CtmView :=
  { chainAdmin := fun _ => admin
    protocolVersion := fun _ => 3
    upgradeTransition := fun _ => 1
    upgradeCutHash := fun _ => 0
    zkChain := fun _ => 0
    migrationNumber := fun _ => 0
    readyForMigration := fun _ => false }

/-- An environment with one contract, at `a ≠ 0`, answering `V`. -/
private def envAt (a : Address) (ha : a ≠ 0) (V : CtmView) : Env :=
  { ctm := fun x => if x = a then some V else none
    zeroNoCode := by simp [Ne.symm ha]
    checkerOk := fun _ _ _ => false }

private lemma envAt_ctm (a : Address) (ha : a ≠ 0) (V : CtmView) :
    (envAt a ha V).ctm a = some V := by simp [envAt]

theorem TimestampWritesAuthorized : Properties.TimestampWritesAuthorized := by
  intro s₀ s h0 hR
  induction hR with
  | refl => exact ⟨by simp [h0], fun c v h => absurd rfl h⟩
  | @step E s s' l _ hs ih =>
    obtain ⟨hA, hT⟩ := ih
    cases hs with
    | init _ _ _ _ => exact ⟨hA, hT⟩
    | setCTM _ _ _ => exact ⟨hA, hT⟩
    | setChecker _ _ => exact ⟨hA, hT⟩
    | migrate _ _ _ _ _ => exact ⟨hA, hT⟩
    | transferOwnership _ _ => exact ⟨hA, hT⟩
    | acceptOwnership _ _ => exact ⟨hA, hT⟩
    | renounceOwnership _ _ => exact ⟨hA, hT⟩
    | @setTs caller c t V _ hV hadm ht hsch _ =>
      refine ⟨?_, ?_⟩
      · intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact hA w hw
        · rw [List.mem_singleton] at hw
          subst hw
          refine ⟨?_, ht, hadm, rfl, hsch⟩
          intro hz
          have := E.zeroNoCode
          rw [show s.ctm = 0 from hz] at hV
          rw [hV] at this
          cases this
      · intro c' v' hne
        by_cases hcv : c' = c ∧ v' = V.protocolVersion c
        · obtain ⟨rfl, rfl⟩ := hcv
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl,
            by simp [setEntry]⟩
        · have hsame : setEntry s.ts c (V.protocolVersion c) t c' v' = s.ts c' v' := by
            simp [setEntry, hcv]
          have hne' : s.ts c' v' ≠ s₀.ts c' v' := by
            intro h
            apply hne
            show setEntry s.ts c (V.protocolVersion c) t c' v' = _
            rw [hsame, h]
          obtain ⟨w, hw, h1, h2, h3⟩ := hT c' v' hne'
          refine ⟨w, List.mem_append_left _ hw, h1, h2, ?_⟩
          show w.value = setEntry s.ts c (V.protocolVersion c) t c' v'
          rw [hsame, h3]

theorem TimestampNeverResetToZero : Properties.TimestampNeverResetToZero := by
  intro s s' c v hR h
  induction hR with
  | refl => exact h
  | step _ hs ih =>
    cases hs with
    | init _ _ _ _ => exact ih
    | setCTM _ _ _ => exact ih
    | setChecker _ _ => exact ih
    | migrate _ _ _ _ _ => exact ih
    | transferOwnership _ _ => exact ih
    | acceptOwnership _ _ => exact ih
    | renounceOwnership _ _ => exact ih
    | setTs _ _ _ ht _ _ =>
      show setEntry _ _ _ _ c v ≠ 0
      unfold setEntry
      split_ifs
      · exact ht
      · exact ih

theorem OnlyOwnerConfigures : Properties.OnlyOwnerConfigures := by
  intro E s s' l hs
  cases hs with
  | init _ _ _ _ => exact ⟨fun h => absurd rfl h, fun h => absurd rfl h, id⟩
  | setCTM _ hc ha =>
    subst hc
    exact ⟨fun _ => ⟨rfl, ha⟩, fun h => absurd rfl h, fun _ => ha⟩
  | setChecker _ hc =>
    subst hc
    exact ⟨fun h => absurd rfl h, fun _ => ⟨_, _, rfl⟩, id⟩
  | setTs _ _ _ _ _ _ => exact ⟨fun h => absurd rfl h, fun h => absurd rfl h, id⟩
  | migrate _ _ _ _ _ => exact ⟨fun h => absurd rfl h, fun h => absurd rfl h, id⟩
  | transferOwnership _ _ => exact ⟨fun h => absurd rfl h, fun h => absurd rfl h, id⟩
  | acceptOwnership _ _ => exact ⟨fun h => absurd rfl h, fun h => absurd rfl h, id⟩
  | renounceOwnership _ _ => exact ⟨fun h => absurd rfl h, fun h => absurd rfl h, id⟩

/-- `Initializable._initialized` is never cleared. -/
private lemma initialized_mono {s s' : State} (hR : Reach s s') (h : s.initialized = true) :
    s'.initialized = true := by
  induction hR with
  | refl => exact h
  | step _ hs ih =>
    cases hs with
    | init _ _ _ _ => rfl
    | setCTM _ _ _ => exact ih
    | setChecker _ _ => exact ih
    | setTs _ _ _ _ _ _ => exact ih
    | migrate _ _ _ _ _ => exact ih
    | transferOwnership _ _ => exact ih
    | acceptOwnership _ _ => exact ih
    | renounceOwnership _ _ => exact ih

theorem InitializeOnce : Properties.InitializeOnce := by
  intro E E' s s' s'' s''' c o c' o' h1 hR h2
  have hi : s'.initialized = true := by
    cases h1 with
    | init _ _ _ _ => rfl
  have hi'' := initialized_mono hR hi
  cases h2 with
  | init _ hf _ _ => rw [hi''] at hf; exact Bool.noConfusion hf

theorem MigrationEventsAuthorized : Properties.MigrationEventsAuthorized := by
  intro s₀ s h0 hR
  induction hR with
  | refl => simp [h0]
  | step _ hs ih =>
    cases hs with
    | init _ _ _ _ => exact ih
    | setCTM _ _ _ => exact ih
    | setChecker _ _ => exact ih
    | setTs _ _ _ _ _ _ => exact ih
    | transferOwnership _ _ => exact ih
    | acceptOwnership _ _ => exact ih
    | renounceOwnership _ _ => exact ih
    | migrate _ _ hadm _ hready =>
      intro e he
      rcases List.mem_append.1 he with he | he
      · exact ih e he
      · rw [List.mem_singleton] at he
        subst he
        exact ⟨hadm, rfl, hready⟩

theorem OwnerRedirectsTimestampAuthority : Properties.OwnerRedirectsTimestampAuthority := by
  refine ⟨envAt 9 (by decide) (viewOf 10), envAt 77 (by decide) (viewOf 20),
    ⟨true, true, 20, 0, 9, fun _ _ => 0, fun _ => 0, [], []⟩, _, _, viewOf 10, 5,
    envAt_ctm _ _ _, rfl, rfl,
    .setCTM (by decide) rfl (by decide),
    .setTs (V := viewOf 20) (by decide) (envAt_ctm _ _ _) rfl (by decide)
      (Or.inl (by decide)) (Or.inl rfl),
    3, ?_⟩
  simp [setEntry, viewOf]

theorem ZeroCheckLoadBearing : Properties.ZeroCheckLoadBearing := by
  refine ⟨envAt 9 (by decide) (viewOf 7),
    ⟨true, true, 5, 0, 9, fun _ _ => 1000, fun _ => 0, [], []⟩, _, .setTs 7 1 0, 1, 3,
    .setTs (V := viewOf 7) (by decide) (envAt_ctm _ _ _) rfl (Or.inl (by decide)) (Or.inl rfl),
    by decide, ?_⟩
  simp [setEntry, viewOf]

theorem ScheduleWitness : Properties.ScheduleWitness := by
  refine ⟨_, .step (.step (.step .refl
      (.init (E := envAt 9 (by decide) (viewOf 7)) (caller := 4) (o := 5)
        (by decide) rfl rfl (by decide)))
      (.setCTM (E := envAt 9 (by decide) (viewOf 7)) (a := 9) (by decide) rfl (by decide)))
      (.setTs (E := envAt 9 (by decide) (viewOf 7)) (V := viewOf 7) (c := 1) (t := 1000)
        (by decide) (envAt_ctm _ _ _) rfl (by decide) (Or.inl (by decide)) (Or.inl rfl)),
    ?_, rfl, rfl⟩
  simp [setEntry, viewOf]

end Contracts.ServerNotifier
