import EraSpec.Contracts.AdminFacet.Properties.PriorityMode
import EraSpec.Contracts.AdminFacet.Proofs.Access

/-!
# Proofs: priority mode

Each `Properties.X` of `EraSpec.Contracts.AdminFacet.Properties.PriorityMode` is proved as `X`.
-/

namespace Contracts.AdminFacet

section StepLemmas

variable {K : Config} {w w' : World} {l : Label}

theorem step_stage1 (h : Step K w l w') (hc : l.runsCut = false) (hi : Stage1Inv w.st) :
    Stage1Inv w'.st := by
  cases h with
  | call hs => exact exec_stage1 (call_exec hs) hc hi
  | env => exact hi
  | foreign hf => exact hf.stage1 hi

/-- The one-way relation between two states. -/
def OneWay (s s' : State) : Prop :=
  (s.isPermanentRollup = true → s'.isPermanentRollup = true) ∧
  (s.secondProofSystemRequired = true → s'.secondProofSystemRequired = true) ∧
  (s.priorityMode.canBeActivated = true →
    s'.priorityMode.canBeActivated = true ∧
    s'.feeParams.pricingMode = s.feeParams.pricingMode ∧
    s'.feeParams.priorityTxMaxPubdata = s.feeParams.priorityTxMaxPubdata ∧
    s'.feeParams.maxPubdataPerBatch = s.feeParams.maxPubdataPerBatch ∧
    s'.feeParams.maxL2GasPerBatch = s.feeParams.maxL2GasPerBatch)

theorem OneWay.refl (s : State) : OneWay s s := by
  simp [OneWay]

theorem OneWay.trans {s₁ s₂ s₃ : State} (h₁ : OneWay s₁ s₂) (h₂ : OneWay s₂ s₃) :
    OneWay s₁ s₃ := by
  obtain ⟨a₁, b₁, c₁⟩ := h₁
  obtain ⟨a₂, b₂, c₂⟩ := h₂
  refine ⟨fun h => a₂ (a₁ h), fun h => b₂ (b₁ h), fun h => ?_⟩
  obtain ⟨d₁, e₁, f₁, g₁, i₁⟩ := c₁ h
  obtain ⟨d₂, e₂, f₂, g₂, i₂⟩ := c₂ d₁
  exact ⟨d₂, e₂.trans e₁, f₂.trans f₁, g₂.trans g₁, i₂.trans i₁⟩

theorem step_oneWay (h : Step K w l w') (hc : l.runsCut = false) : OneWay w.st w'.st := by
  cases h with
  | call hs => exact exec_oneWay (call_exec hs) hc
  | env => exact OneWay.refl _
  | foreign hf =>
    refine ⟨hf.2, fun h => by rw [hf.secondProofSystemRequired]; exact h, fun h => ?_⟩
    rw [hf.priorityMode, hf.feeParams]
    exact ⟨h, rfl, rfl, rfl, rfl⟩

theorem step_activated (h : Step K w l w') (hc : l.runsCut = false) :
    w'.st.priorityMode.activated = w.st.priorityMode.activated ∨
      (∃ a τ, l = .call ⟨a, τ, .activatePriorityMode⟩ ∧ w'.st.priorityMode.activated = true) ∨
      (∃ τ, l = .call ⟨w.st.chainTypeManager, τ, .deactivatePriorityMode⟩ ∧
        w'.st.priorityMode.activated = false) := by
  cases h with
  | @call c s' hs =>
    rcases exec_activated (call_exec hs) hc with h1 | ⟨he, h2⟩ | ⟨he, hsnd, h2⟩
    · exact Or.inl h1
    · right; left; refine ⟨c.sender, c.time, ?_, h2⟩
      rcases c with ⟨a, τ, en⟩; simp only at he; subst he; rfl
    · right; right; refine ⟨c.time, ?_, h2⟩
      rcases c with ⟨a, τ, en⟩; simp only at he hsnd; subst he hsnd; rfl
  | env => exact Or.inl rfl
  | foreign hf => exact Or.inl (by rw [hf.priorityMode])

end StepLemmas

theorem stage1_inv_holds_along_runs : Properties.Stage1InvHoldsAlongRuns := by
  refine ⟨fun s h1 h2 => by simp [Stage1Inv, h1, h2], ?_⟩
  intro K w w' ls hr hnc hi
  exact Run.preserve (fun w => Stage1Inv w.st)
    (fun _ _ _ hs hc hw => step_stage1 hs hc hw) hr hnc hi

theorem one_way_flags_along_runs : Properties.OneWayFlagsAlongRuns := by
  intro K w w' ls hr
  suffices H : (∀ l ∈ ls, l.runsCut = false) → OneWay w.st w'.st from H
  induction hr with
  | nil => intro _; exact OneWay.refl _
  | cons hs _ ih =>
    intro hnc
    exact (step_oneWay hs (hnc _ List.mem_cons_self)).trans
      (ih (fun l hl => hnc l (List.mem_cons_of_mem _ hl)))

theorem activate_priority_mode_exact : Properties.ActivatePriorityModeExact := by
  intro K e s s' a τ
  simp only [call, exec, onlySettlementLayer, onlyL1, revertBatches, req_eq_some, le_refl,
    true_and, Option.some.injEq]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10.symm⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10.symm⟩

theorem priority_mode_toggles_only_by_its_entries :
    Properties.PriorityModeTogglesOnlyByItsEntries := by
  intro K w w' ls hr
  induction hr with
  | nil => intro _; exact ⟨fun h1 h2 => by simp_all, fun h1 h2 => by simp_all⟩
  | @cons w w₁ w₂ l ls hs _ ih =>
    intro hnc
    have hl : l.runsCut = false := hnc l List.mem_cons_self
    obtain ⟨iha, ihd⟩ := ih (fun l' hl' => hnc l' (List.mem_cons_of_mem _ hl'))
    have hctm1 := step_ctm hs hl
    refine ⟨fun h0 h2 => ?_, fun h0 h2 => ?_⟩
    · cases h1 : w₁.st.priorityMode.activated
      · obtain ⟨a, τ, hm⟩ := iha h1 h2
        exact ⟨a, τ, List.mem_cons_of_mem _ hm⟩
      · rcases step_activated hs hl with h | ⟨a, τ, rfl, _⟩ | ⟨τ, _, h3⟩
        · simp_all
        · exact ⟨a, τ, List.mem_cons_self⟩
        · simp_all
    · cases h1 : w₁.st.priorityMode.activated
      · rcases step_activated hs hl with h | ⟨a, τ, _, h3⟩ | ⟨τ, rfl, _⟩
        · simp_all
        · simp_all
        · exact ⟨τ, List.mem_cons_self⟩
      · obtain ⟨τ, hm⟩ := ihd h1 h2
        exact ⟨τ, by rw [← hctm1]; exact List.mem_cons_of_mem _ hm⟩

/-! ## Witness -/

/-- The environment of the witness: the `RollupDAManager` allows every pair. -/
def pmEnv : Env := { nullEnv with isPairAllowed := fun _ _ => true }

/-- After the Mailbox enqueued one priority transaction at time `100`. -/
def pm1 : State :=
  { freshState with ptNextLeafIndex := 1, requestTimestamp := fun i => if i = 0 then 100 else 0 }
/-- After `makePermanentRollup`. -/
def pm2 : State := { pm1 with isPermanentRollup := true }
/-- After `permanentlyAllowPriorityMode`. -/
def pm3 : State :=
  { pm2 with transactionFilterer := 0, priorityMode := ⟨true, false, 0, 0⟩ }
/-- After `activatePriorityMode`. -/
def pm4 : State := { pm3 with priorityMode := ⟨true, true, 0, 0⟩ }

theorem priority_mode_witness : Properties.PriorityModeWitness := by
  refine ⟨nullConfig, ⟨freshState, pmEnv⟩, ⟨pm4, pmEnv⟩,
    [.foreign pm1, .call ⟨1, 0, .makePermanentRollup⟩, .call ⟨1, 0, .permanentlyAllowPriorityMode⟩,
     .call ⟨7, 100 + PRIORITY_EXPIRATION, .activatePriorityMode⟩], ?_, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · refine Run.cons (w₁ := ⟨pm1, pmEnv⟩) (Step.foreign ⟨rfl, fun h => h⟩) ?_
    refine Run.cons (w₁ := ⟨pm2, pmEnv⟩) (Step.call rfl) ?_
    refine Run.cons (w₁ := ⟨pm3, pmEnv⟩) (Step.call rfl) ?_
    refine Run.cons (Step.call ?_) (Run.nil _)
    simp [call, exec, req, onlySettlementLayer, onlyL1, revertBatches, pm4, pm3, pm2, pm1,
      freshState, State.firstUnprocessed, nullConfig]
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> rfl
  · simp [Stage1Inv, pm4, pm3, pm2, pm1, freshState]

/-! ## Countermodels -/

/-- A chain with priority mode allowed, governance's filterer `0` installed, filtering off. -/
def stage1State : State :=
  { freshState with priorityMode := ⟨true, false, 0, 0⟩ }

theorem stage1State_inv : Stage1Inv stage1State := by
  simp [Stage1Inv, stage1State, freshState]

theorem unguarded_filterer_breaks_stage1 : Properties.UnguardedFiltererBreaksStage1 :=
  ⟨nullConfig, nullEnv, stage1State, { stage1State with transactionFilterer := 5 }, 5, 0,
    stage1State_inv, rfl, by simp [Stage1Inv, stage1State, freshState], rfl⟩

theorem unguarded_l1_filtering_breaks_stage1 : Properties.UnguardedL1FilteringBreaksStage1 :=
  ⟨nullConfig, nullEnv, stage1State, { stage1State with l1TxFiltering := true }, 0,
    stage1State_inv, rfl, by simp [Stage1Inv, stage1State, freshState], rfl⟩

/-! ## Certificates -/

theorem Stage1InvHoldsAlongRuns : Properties.Stage1InvHoldsAlongRuns :=
  stage1_inv_holds_along_runs
theorem OneWayFlagsAlongRuns : Properties.OneWayFlagsAlongRuns :=
  one_way_flags_along_runs
theorem ActivatePriorityModeExact : Properties.ActivatePriorityModeExact :=
  activate_priority_mode_exact
theorem PriorityModeTogglesOnlyByItsEntries : Properties.PriorityModeTogglesOnlyByItsEntries :=
  priority_mode_toggles_only_by_its_entries
theorem PriorityModeWitness : Properties.PriorityModeWitness :=
  priority_mode_witness
theorem UnguardedFiltererBreaksStage1 : Properties.UnguardedFiltererBreaksStage1 :=
  unguarded_filterer_breaks_stage1
theorem UnguardedL1FilteringBreaksStage1 : Properties.UnguardedL1FilteringBreaksStage1 :=
  unguarded_l1_filtering_breaks_stage1

end Contracts.AdminFacet
