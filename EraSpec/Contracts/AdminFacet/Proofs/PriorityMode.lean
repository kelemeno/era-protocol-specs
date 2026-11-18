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

/-! ## No facet call blocks a due activation -/

/-- Every condition of `activatePriorityMode` at time `τ` except that priority mode is inactive. -/
def ActivationReady (K : Config) (s : State) (τ : ℕ) : Prop :=
  ¬ (s.frozen = true ∧ s.freezable Entry.activatePriorityMode.sel = true) ∧
  K.onL1 = true ∧ s.priorityMode.canBeActivated = true ∧ s.isPermanentRollup = true ∧
  ActivationQueueReady s τ

theorem activate_ok_iff {K : Config} {e : Env} {s : State} {a : Address} {τ : ℕ} :
    (∃ s', call K e s ⟨a, τ, .activatePriorityMode⟩ = some s') ↔
      ActivationReady K s τ ∧ s.priorityMode.activated = false := by
  constructor
  · rintro ⟨s', h⟩
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _⟩ :=
      (activate_priority_mode_exact K e s s' a τ).1 h
    exact ⟨⟨h1, h3, h5, h6, h2, h7, h8, h9⟩, h4⟩
  · rintro ⟨⟨h1, h3, h5, h6, h2, h7, h8, h9⟩, h4⟩
    exact ⟨_, (activate_priority_mode_exact K e s _ a τ).2
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, rfl⟩⟩

theorem ActivationReady.mono {K : Config} {s : State} {τ τ' : ℕ} (h : ActivationReady K s τ)
    (hτ : τ ≤ τ') : ActivationReady K s τ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, le_trans h7 hτ, h8⟩

section StepLemmas

variable {K : Config} {w w' : World} {l : Label}

theorem step_freezable (h : Step K w l w') (hc : l.runsCut = false) :
    w'.st.freezable = w.st.freezable := by
  cases h with
  | call hs => exact (exec_fixed (call_exec hs) hc).2.2.2.1
  | env => rfl
  | foreign hf => exact hf.freezable

/-- One step without a cut keeps `ActivationReady`, if a foreign write keeps the queue ready and
the step is not a CTM call that could freeze a freezable activation selector. -/
theorem step_activationReady {τ : ℕ} (h : Step K w l w') (hc : l.runsCut = false)
    (hf : ∀ s', l = .foreign s' → ActivationQueueReady s' τ)
    (hz : w.st.freezable Entry.activatePriorityMode.sel = false ∨
      ∀ c, l = .call c → c.sender ≠ w.st.chainTypeManager)
    (hr : ActivationReady K w.st τ) : ActivationReady K w'.st τ := by
  obtain ⟨h1, h2, h3, h4, hq⟩ := hr
  cases h with
  | @call c s' hs =>
    have he := call_exec hs
    obtain ⟨hp, _, hcb⟩ := exec_oneWay he hc
    obtain ⟨_, _, _, hfz, _⟩ := exec_fixed he hc
    obtain ⟨hsl, hrt, hst, hun, hex, hcm⟩ := exec_queue he hc
    obtain ⟨q1, q2, q3, q4⟩ := hq
    refine ⟨?_, h2, (hcb h3).1, hp h4, ?_⟩
    · show ¬ (s'.frozen = true ∧ s'.freezable Entry.activatePriorityMode.sel = true)
      rw [hfz]
      rcases exec_frozen he hc with hfr | ⟨_, hsnd, _, _⟩ | ⟨_, _, _, hfr⟩
      · rw [hfr]; exact h1
      · rcases hz with hz | hz
        · simp [hz]
        · exact absurd hsnd (hz c rfl)
      · simp [hfr]
    · show ActivationQueueReady s' τ
      have hfu : s'.firstUnprocessed = w.st.firstUnprocessed := by
        simp only [State.firstUnprocessed, hst, hun]
      refine ⟨hsl ▸ q1, ?_, ?_, ?_⟩
      · rw [hfu, hrt]; exact q2
      · rw [hfu, hrt]; exact q3
      · rcases hcm with hcm | ⟨_, hcm⟩
        · rw [hcm, hex]; exact q4
        · rw [hcm, hex]
  | env => exact ⟨h1, h2, h3, h4, hq⟩
  | @foreign s' hfo =>
    refine ⟨?_, h2, ?_, hfo.2 h4, hf s' rfl⟩
    · show ¬ (s'.frozen = true ∧ s'.freezable Entry.activatePriorityMode.sel = true)
      rw [hfo.frozen, hfo.freezable]; exact h1
    · show s'.priorityMode.canBeActivated = true
      rw [hfo.priorityMode]; exact h3

end StepLemmas

/-- Along a run without cuts whose foreign writes keep the queue ready, `ActivationReady` holds
throughout, if the activation selector is not freezable or the CTM sends none of the calls. -/
theorem run_activationReady {K : Config} {τ : ℕ} {w w' : World} {ls : List Label}
    (hr : Run K w ls w') (hnc : ∀ l ∈ ls, l.runsCut = false)
    (hf : ∀ s', Label.foreign s' ∈ ls → ActivationQueueReady s' τ)
    (hz : w.st.freezable Entry.activatePriorityMode.sel = false ∨
      ∀ c, Label.call c ∈ ls → c.sender ≠ w.st.chainTypeManager)
    (h0 : ActivationReady K w.st τ) : ActivationReady K w'.st τ := by
  induction hr with
  | nil => exact h0
  | @cons w w₁ w₂ l ls hs _ ih =>
    have hl : l.runsCut = false := hnc l List.mem_cons_self
    have h1 : ActivationReady K w₁.st τ := by
      refine step_activationReady hs hl (fun s' hs' => hf s' (hs' ▸ List.mem_cons_self)) ?_ h0
      rcases hz with hz | hz
      · exact Or.inl hz
      · exact Or.inr (fun c hc => hz c (hc ▸ List.mem_cons_self))
    refine ih (fun l' hl' => hnc l' (List.mem_cons_of_mem _ hl'))
      (fun s' hs' => hf s' (List.mem_cons_of_mem _ hs')) ?_ h1
    rw [step_freezable hs hl, step_ctm hs hl]
    rcases hz with hz | hz
    · exact Or.inl hz
    · exact Or.inr (fun c hc => hz c (List.mem_cons_of_mem _ hc))

theorem no_facet_call_blocks_due_activation : Properties.NoFacetCallBlocksDueActivation := by
  intro K w w' ls a τ h0 hr hnc hf hz
  obtain ⟨hready, _⟩ := activate_ok_iff.1 h0
  have hend := run_activationReady hr hnc hf hz hready
  cases hact : w'.st.priorityMode.activated
  · right
    intro b τ' hτ
    exact activate_ok_iff.2 ⟨hend.mono hτ, hact⟩
  · exact Or.inl rfl

/-! ## Witnesses -/

/-- The environment of the witnesses: the `RollupDAManager` allows every pair. -/
def pmEnv : Env := { nullEnv with isPairAllowed := fun _ _ => true }

/-- After the Mailbox enqueued one priority transaction at time `100`. -/
def pm1 : State := queuedState
/-- After `makePermanentRollup`. -/
def pm2 : State := { pm1 with isPermanentRollup := true }
/-- After `permanentlyAllowPriorityMode`. -/
def pm3 : State :=
  { pm2 with transactionFilterer := 0, priorityMode := ⟨true, false, 0, 0⟩ }
/-- After `activatePriorityMode`. -/
def pm4 : State := { pm3 with priorityMode := ⟨true, true, 0, 0⟩ }

/-- The time at which the priority transaction of `pm1` has been pending for `PRIORITY_EXPIRATION`. -/
abbrev pmDue : ℕ := 100 + PRIORITY_EXPIRATION

theorem pm3_activates : call nullConfig pmEnv pm3 ⟨7, pmDue, .activatePriorityMode⟩ = some pm4 := by
  simp [call, exec, req, onlySettlementLayer, onlyL1, revertBatches, pm4, pm3, pm2, pm1,
    queuedState, freshState, State.firstUnprocessed, nullConfig]

theorem priority_mode_witness : Properties.PriorityModeWitness := by
  refine ⟨nullConfig, ⟨freshState, pmEnv⟩, ⟨pm4, pmEnv⟩,
    [.foreign pm1, .call ⟨1, 0, .makePermanentRollup⟩, .call ⟨1, 0, .permanentlyAllowPriorityMode⟩,
     .call ⟨7, pmDue, .activatePriorityMode⟩], ?_, ?_, ?_, rfl, rfl, rfl, rfl, ?_, 7, pmDue,
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    by decide, by decide⟩
  · refine Run.cons (w₁ := ⟨pm1, pmEnv⟩) (Step.foreign ⟨rfl, fun h => h⟩) ?_
    refine Run.cons (w₁ := ⟨pm2, pmEnv⟩) (Step.call rfl) ?_
    refine Run.cons (w₁ := ⟨pm3, pmEnv⟩) (Step.call rfl) ?_
    exact Run.cons (Step.call pm3_activates) (Run.nil _)
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> rfl
  · simp [Stage1Inv, freshState]
  · simp [Stage1Inv, pm4, pm3, pm2, pm1, queuedState, freshState]

/-- A permanent rollup with one queued priority transaction, filterer `5`, batches executed `1`,
verified `2`, committed `3`, and the L2 upgrade in batch `3`. -/
def pmB0 : State :=
  { queuedState with
    isPermanentRollup := true
    transactionFilterer := 5
    totalBatchesExecuted := 1
    totalBatchesVerified := 2
    totalBatchesCommitted := 3
    upgradeBatchNumber := 3 }
/-- After the CTM's `setPriorityModeTransactionFilterer(42)`. -/
def pmB1 : State := { pmB0 with priorityMode := ⟨false, false, 0, 42⟩ }
/-- After `permanentlyAllowPriorityMode`. -/
def pmB2 : State := { pmB1 with transactionFilterer := 42, priorityMode := ⟨true, false, 0, 42⟩ }
/-- After `activatePriorityMode`. -/
def pmB3 : State :=
  { pmB2 with
    priorityMode := ⟨true, true, 0, 42⟩
    totalBatchesCommitted := 1
    totalBatchesVerified := 1
    upgradeBatchNumber := 0 }

theorem pmB0_setFilterer :
    call nullConfig pmEnv pmB0 ⟨9, 0, .setPriorityModeTransactionFilterer 42⟩ = some pmB1 := by
  simp [call, exec, req, onlySettlementLayer, onlyL1, pmB1, pmB0, queuedState, freshState,
    nullConfig]

theorem pmB1_allow :
    call nullConfig pmEnv pmB1 ⟨1, 0, .permanentlyAllowPriorityMode⟩ = some pmB2 := by
  simp [call, exec, req, onlySettlementLayer, onlyL1, pmB2, pmB1, pmB0, queuedState, freshState,
    State.firstUnprocessed, State.priorityTreeSize, nullConfig]

theorem pmB2_activates :
    call nullConfig pmEnv pmB2 ⟨7, pmDue, .activatePriorityMode⟩ = some pmB3 := by
  simp [call, exec, req, onlySettlementLayer, onlyL1, revertBatches, pmB3, pmB2, pmB1, pmB0,
    queuedState, freshState, State.firstUnprocessed, nullConfig]

theorem priority_mode_activation_reverts_batches_witness :
    Properties.PriorityModeActivationRevertsBatchesWitness := by
  refine ⟨nullConfig, ⟨pmB0, pmEnv⟩, ⟨pmB3, pmEnv⟩,
    [.call ⟨9, 0, .setPriorityModeTransactionFilterer 42⟩,
     .call ⟨1, 0, .permanentlyAllowPriorityMode⟩, .call ⟨7, pmDue, .activatePriorityMode⟩], 42,
    ?_, ?_, ?_, rfl, rfl, List.mem_cons_self, by decide, by decide, by decide, by decide,
    by decide, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · refine Run.cons (w₁ := ⟨pmB1, pmEnv⟩) (Step.call pmB0_setFilterer) ?_
    refine Run.cons (w₁ := ⟨pmB2, pmEnv⟩) (Step.call pmB1_allow) ?_
    exact Run.cons (Step.call pmB2_activates) (Run.nil _)
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> rfl
  · simp [Stage1Inv, pmB0, queuedState, freshState]
  · simp [Stage1Inv, pmB3, pmB2, pmB1, pmB0, queuedState, freshState]

/-- `pm4` after the CTM's `deactivatePriorityMode`. -/
def pm5 : State := { pm4 with priorityMode := ⟨true, false, 0, 0⟩ }

theorem priority_mode_deactivation_witness : Properties.PriorityModeDeactivationWitness := by
  refine ⟨nullConfig, ⟨pm4, pmEnv⟩, ⟨pm5, pmEnv⟩, [.call ⟨9, 0, .deactivatePriorityMode⟩],
    Run.cons (Step.call rfl) (Run.nil _), ?_, ?_, rfl, rfl, ?_⟩
  · intro l hl; simp at hl; subst hl; rfl
  · simp [Stage1Inv, pm4, pm3, pm2, pm1, queuedState, freshState]
  · simp [Stage1Inv, pm5, pm4, pm3, pm2, pm1, queuedState, freshState]

/-- A stage-1 chain: permanent rollup, second proof system required, priority mode allowed; its
fee parameters price L2 gas at `100` (validium pricing, unit capacities, unit multiplier). -/
def feeStage1State : State :=
  { freshState with
    isPermanentRollup := true
    secondProofSystemRequired := true
    priorityMode := ⟨true, false, 0, 0⟩
    feeParams := ⟨1, 0, 1, 1, 1, 100⟩
    multNominator := 1
    multDenominator := 1 }

/-- `feeStage1State` after the admin raised `minimalL2GasPrice` to `120` at time `1000`. -/
def feeStage1State' : State :=
  { feeStage1State with feeParams := ⟨1, 0, 1, 1, 1, 120⟩, lastFeeParamsUpdate := 1000 }

theorem one_way_flags_witness : Properties.OneWayFlagsWitness := by
  refine ⟨nullConfig, ⟨feeStage1State, nullEnv⟩, ⟨feeStage1State', nullEnv⟩,
    [.call ⟨1, 1000, .changeFeeParams ⟨1, 0, 1, 1, 1, 120⟩⟩], ?_, ?_, rfl, rfl, rfl, ?_⟩
  · refine Run.cons (Step.call ?_) (Run.nil _)
    simp [call, exec, req, onlyL1, nullConfig, minUpdateIntervalPassed, priceChangeWithinBound,
      safeDerivedL2GasPrice, deriveL2GasPriceFromParams, feeStage1State', feeStage1State,
      freshState, REQUIRED_L2_GAS_PRICE_PER_PUBDATA, MAX_PRICE_CHANGE_NUMERATOR,
      MAX_PRICE_CHANGE_DENOMINATOR]
  · intro l hl; simp at hl; subst hl; rfl
  · simp [feeStage1State', feeStage1State]

/-- `pm3` after the admin set an allowed DA pair. -/
def dueS1 : State := { pm3 with l1DAValidator := 3, l2DAScheme := 2 }
/-- `dueS1` after another facet committed a batch. -/
def dueS2 : State := { dueS1 with totalBatchesCommitted := 1 }
/-- `dueS2` after the admin nominated `2`. -/
def dueS3 : State := { dueS2 with pendingAdmin := 2 }
/-- `pmEnv` after the Bridgehub's ownership moved to `5`. -/
def dueEnv : Env := { pmEnv with bridgehubOwner := 5 }

theorem due_activation_survives_witness : Properties.DueActivationSurvivesWitness := by
  refine ⟨nullConfig, ⟨pm3, pmEnv⟩, ⟨dueS3, dueEnv⟩,
    [.call ⟨1, 0, .setDAValidatorPair 3 2⟩, .env dueEnv, .foreign dueS2,
     .call ⟨1, 0, .setPendingAdmin 2⟩], 7, pmDue, pm4,
    { dueS3 with priorityMode := ⟨true, true, 0, 0⟩, totalBatchesCommitted := 0 }, pm3_activates,
    ?_, ?_, ?_, rfl, ?_,
    ⟨_, List.mem_cons_self⟩, ⟨dueEnv, by simp⟩, ⟨dueS2, by simp⟩, by decide, rfl, ?_⟩
  · refine Run.cons (w₁ := ⟨dueS1, pmEnv⟩) (Step.call rfl) ?_
    refine Run.cons (Step.env _) ?_
    refine Run.cons (Step.foreign ⟨rfl, fun h => h⟩) ?_
    exact Run.cons (Step.call rfl) (Run.nil _)
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl <;> rfl
  · intro s' hs'
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq, Label.foreign.injEq,
      false_or] at hs'
    subst hs'
    simp [ActivationQueueReady, dueS2, dueS1, pm3, pm2, pm1, queuedState, freshState,
      State.firstUnprocessed]
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, Label.call.injEq, reduceCtorEq,
      false_or] at hc
    rcases hc with rfl | rfl <;> decide
  · simp [call, exec, req, onlySettlementLayer, onlyL1, revertBatches, dueS3, dueS2, dueS1, pm3,
      pm2, pm1, queuedState, freshState, State.firstUnprocessed, nullConfig]

/-! ## Countermodels -/

/-- `pm3` with every selector of the diamond marked freezable. -/
def freezablePm3 : State := { pm3 with freezable := fun _ => true }

theorem ctm_freeze_blocks_activation : Properties.CTMFreezeBlocksActivation := by
  refine ⟨nullConfig, ⟨freezablePm3, pmEnv⟩, ⟨{ freezablePm3 with frozen := true }, pmEnv⟩,
    [.call ⟨9, 0, .freezeDiamond⟩], 7, pmDue,
    { freezablePm3 with priorityMode := ⟨true, true, 0, 0⟩ }, ?_, rfl,
    Run.cons (Step.call rfl) (Run.nil _), ?_, ?_, ?_, rfl, ?_⟩
  · simp [call, exec, req, onlySettlementLayer, onlyL1, revertBatches, freezablePm3, pm3, pm2,
      pm1, queuedState, freshState, State.firstUnprocessed, nullConfig]
  · intro l hl; simp at hl; subst hl; rfl
  · intro s' hs'; simp at hs'
  · intro c hc; simp at hc; subst hc; rfl
  · simp [call, req, freezablePm3]

/-- After `permanentlyAllowPriorityMode` on `pm1`, without `makePermanentRollup`. -/
def allowedNotPermanent : State :=
  { pm1 with transactionFilterer := 0, priorityMode := ⟨true, false, 0, 0⟩ }

theorem activation_needs_permanent_rollup : Properties.ActivationNeedsPermanentRollup := by
  refine ⟨nullConfig, ⟨freshState, pmEnv⟩, ⟨allowedNotPermanent, pmEnv⟩,
    [.foreign pm1, .call ⟨1, 0, .permanentlyAllowPriorityMode⟩], 7, pmDue,
    ?_, ?_, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, ?_⟩
  · refine Run.cons (w₁ := ⟨pm1, pmEnv⟩) (Step.foreign ⟨rfl, fun h => h⟩) ?_
    exact Run.cons (Step.call rfl) (Run.nil _)
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> rfl
  · simp [ActivationQueueReady, allowedNotPermanent, pm1, queuedState, freshState,
      State.firstUnprocessed]
  · simp [call, exec, req, onlySettlementLayer, onlyL1, allowedNotPermanent, pm1, queuedState,
      freshState, nullConfig]

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
theorem NoFacetCallBlocksDueActivation : Properties.NoFacetCallBlocksDueActivation :=
  no_facet_call_blocks_due_activation
theorem OneWayFlagsAlongRuns : Properties.OneWayFlagsAlongRuns :=
  one_way_flags_along_runs
theorem ActivatePriorityModeExact : Properties.ActivatePriorityModeExact :=
  activate_priority_mode_exact
theorem PriorityModeTogglesOnlyByItsEntries : Properties.PriorityModeTogglesOnlyByItsEntries :=
  priority_mode_toggles_only_by_its_entries
theorem PriorityModeWitness : Properties.PriorityModeWitness :=
  priority_mode_witness
theorem PriorityModeDeactivationWitness : Properties.PriorityModeDeactivationWitness :=
  priority_mode_deactivation_witness
theorem PriorityModeActivationRevertsBatchesWitness :
    Properties.PriorityModeActivationRevertsBatchesWitness :=
  priority_mode_activation_reverts_batches_witness
theorem OneWayFlagsWitness : Properties.OneWayFlagsWitness :=
  one_way_flags_witness
theorem DueActivationSurvivesWitness : Properties.DueActivationSurvivesWitness :=
  due_activation_survives_witness
theorem CTMFreezeBlocksActivation : Properties.CTMFreezeBlocksActivation :=
  ctm_freeze_blocks_activation
theorem ActivationNeedsPermanentRollup : Properties.ActivationNeedsPermanentRollup :=
  activation_needs_permanent_rollup
theorem UnguardedFiltererBreaksStage1 : Properties.UnguardedFiltererBreaksStage1 :=
  unguarded_filterer_breaks_stage1
theorem UnguardedL1FilteringBreaksStage1 : Properties.UnguardedL1FilteringBreaksStage1 :=
  unguarded_l1_filtering_breaks_stage1

end Contracts.AdminFacet
