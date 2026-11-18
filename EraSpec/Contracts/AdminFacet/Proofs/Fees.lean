import EraSpec.Contracts.AdminFacet.Properties.Fees
import EraSpec.Contracts.AdminFacet.Proofs.PriorityMode

/-!
# Proofs: fee inputs

Each `Properties.X` of `EraSpec.Contracts.AdminFacet.Properties.Fees` is proved as `X`.
-/

namespace Contracts.AdminFacet

theorem set_pubdata_pricing_mode_exact : Properties.SetPubdataPricingModeExact := by
  intro K e s a τ m hfz
  simp only [Entry.sel] at hfz
  simp only [call, exec, req, onlyL1, Entry.sel, hfz, not_false_eq_true, ite_true]
  by_cases h1 : a = s.admin <;> by_cases h2 : K.onL1 = true <;>
    by_cases h3 : s.priorityMode.canBeActivated = false <;> simp [h1, h2, h3]

/-! ## The one-day spacing of fee updates -/

/-- The later of the two fee-update stamps, which `_enforceMinUpdateInterval` reads. -/
def feeStamp (s : State) : ℕ := max s.lastFeeParamsUpdate s.lastTokenMultiplierUpdate

theorem Foreign.feeStamp_eq {s s' : State} (h : Foreign s s') :
    feeStamp s' = feeStamp s := by
  have h1 : s'.lastFeeParamsUpdate = s.lastFeeParamsUpdate := by
    simpa [State.owned] using congrArg Owned.lastFeeParamsUpdate h.1
  have h2 : s'.lastTokenMultiplierUpdate = s.lastTokenMultiplierUpdate := by
    simpa [State.owned] using congrArg Owned.lastTokenMultiplierUpdate h.1
  simp [feeStamp, h1, h2]

/-- A fee update that passes the interval check on a state stamped at `t > 0` or later comes at
least a day after `t`. -/
theorem interval_after_stamp {s : State} {t τ : ℕ} (ht : 0 < t) (hM : t ≤ feeStamp s)
    (hp : minUpdateIntervalPassed s τ = true) : t + PRICE_UPDATE_INTERVAL ≤ τ := by
  unfold minUpdateIntervalPassed at hp
  unfold feeStamp at hM
  have hne : max s.lastFeeParamsUpdate s.lastTokenMultiplierUpdate ≠ 0 := by omega
  simp only [ne_eq, hne, not_false_eq_true, decide_true, Bool.true_and, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not, not_lt] at hp
  omega

/-- One step without a cut keeps the stamp at or above `t > 0`, and a fee update in it comes at
least a day after `t`. -/
theorem step_feeStamp {K : Config} {w w' : World} {l : Label} {t : ℕ} (h : Step K w l w')
    (hc : l.runsCut = false) (ht : 0 < t) (hM : t ≤ feeStamp w.st) :
    t ≤ feeStamp w'.st ∧
      ∀ d, l = .call d → d.entry.isFeeUpdate = true → t + PRICE_UPDATE_INTERVAL ≤ d.time := by
  cases h with
  | @call c s' hs =>
    have he := call_exec hs
    obtain ⟨hno, hyes⟩ := exec_feeStamps he hc
    cases hf : c.entry.isFeeUpdate
    · obtain ⟨h1, h2⟩ := hno hf
      refine ⟨?_, fun d hd hd' => ?_⟩
      · show t ≤ feeStamp s'
        simpa [feeStamp, h1, h2] using hM
      · cases hd; rw [hf] at hd'; cases hd'
    · obtain ⟨hp, hτ⟩ := hyes hf
      have hd := interval_after_stamp ht hM hp
      refine ⟨?_, fun d hd' _ => ?_⟩
      · show t ≤ feeStamp s'
        unfold feeStamp; omega
      · cases hd'; exact hd
  | env => exact ⟨hM, fun d hd => by cases hd⟩
  | foreign hf =>
    refine ⟨?_, fun d hd => by cases hd⟩
    rw [Foreign.feeStamp_eq hf]; exact hM

theorem run_feeStamp {K : Config} {w w' : World} {ls : List Label} {t : ℕ}
    (hr : Run K w ls w') (hnc : ∀ l ∈ ls, l.runsCut = false) (ht : 0 < t)
    (hM : t ≤ feeStamp w.st) :
    ∀ d, Label.call d ∈ ls → d.entry.isFeeUpdate = true → t + PRICE_UPDATE_INTERVAL ≤ d.time := by
  induction hr with
  | nil => intro d hd; cases hd
  | @cons w w₁ w₂ l ls hs _ ih =>
    obtain ⟨hM₁, hl⟩ := step_feeStamp hs (hnc l List.mem_cons_self) ht hM
    intro d hd hfee
    rcases List.mem_cons.1 hd with hd | hd
    · exact hl d hd.symm hfee
    · exact ih (fun l' hl' => hnc l' (List.mem_cons_of_mem _ hl')) hM₁ d hd hfee

theorem fee_updates_at_least_a_day_apart : Properties.FeeUpdatesAtLeastADayApart := by
  intro K w w' c ls hfee hτ hr hnc
  cases hr with
  | cons hs hr =>
    cases hs with
    | @call _ s' hc =>
      have hstamp : c.time ≤ feeStamp s' :=
        ((exec_feeStamps (call_exec hc) (by
          rcases c with ⟨_, _, en⟩; cases en <;> simp_all [Entry.isFeeUpdate, Entry.runsCut])).2
          hfee).2
      exact run_feeStamp hr hnc (Nat.pos_of_ne_zero hτ) hstamp

/-! ## The price-change bound -/

/-- What `priceChangeWithinBound` (`_enforcePriceChangeBound` not reverting) says about the two
prices it compares. -/
theorem priceChangeWithinBound_spec {s : State} {oF nF : FeeParams} {oN oD nN nD : ℕ}
    (h : priceChangeWithinBound s oF nF oN oD nN nD = true) :
    (safeDerivedL2GasPrice oF oN oD = 0 ∧ s.priorityTreeSize = 0) ∨
    (safeDerivedL2GasPrice nF nN nD ≤
        safeDerivedL2GasPrice oF oN oD * MAX_PRICE_CHANGE_NUMERATOR /
          MAX_PRICE_CHANGE_DENOMINATOR ∧
     safeDerivedL2GasPrice oF oN oD * MAX_PRICE_CHANGE_DENOMINATOR /
        MAX_PRICE_CHANGE_NUMERATOR ≤ safeDerivedL2GasPrice nF nN nD) := by
  unfold priceChangeWithinBound at h
  by_cases h0 : safeDerivedL2GasPrice oF oN oD = 0 ∧ s.priorityTreeSize = 0
  · exact Or.inl h0
  · right
    simp only [h0, ite_false, Bool.and_eq_true, decide_eq_true_eq] at h
    exact h

theorem stage_one_fee_update_within_price_bound :
    Properties.StageOneFeeUpdateWithinPriceBound := by
  intro K e s s' c h hfee hcb
  have h := call_exec h
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp only [Entry.isFeeUpdate, reduceCtorEq] at hfee
  case changeFeeParams fp =>
    simp only [exec, onlyL1, req_eq_some, Option.some.injEq] at h
    obtain ⟨_, _, _, _, _, hb, rfl⟩ := h
    exact priceChangeWithinBound_spec (hb hcb).1
  case setTokenMultiplier n d =>
    simp only [exec, onlyL1, req_eq_some, Option.some.injEq] at h
    obtain ⟨_, _, _, _, hb, rfl⟩ := h
    exact priceChangeWithinBound_spec (hb hcb)

/-! ## Only fee updates move the fee inputs on a stage-1 chain -/

/-- A non-cut call other than a fee update, on a state with priority mode allowed, writes neither
the fee parameters nor the multiplier. -/
theorem exec_feeInputs {K : Config} {e : Env} {s s' : State} {c : Call}
    (h : exec K e s c = some s') (hc : c.entry.runsCut = false)
    (hf : c.entry.isFeeUpdate = false) (hcb : s.priorityMode.canBeActivated = true) :
    s'.feeParams = s.feeParams ∧ s'.multNominator = s.multNominator ∧
      s'.multDenominator = s.multDenominator := by
  suffices H : Holds (fun s' => s'.feeParams = s.feeParams ∧ s'.multNominator = s.multNominator ∧
      s'.multDenominator = s.multDenominator) (exec K e s c) from H s' h
  rcases c with ⟨snd, τ, en⟩
  cases en <;> simp only [Entry.runsCut, Entry.isFeeUpdate, reduceCtorEq] at hc hf <;>
    simp (config := { contextual := true }) [exec, onlyL1, onlySettlementLayer,
      noUnverifiedBatches, revertBatches, hcb]

theorem step_feeInputs {K : Config} {w w' : World} {l : Label} (h : Step K w l w')
    (hc : l.runsCut = false) (hf : ∀ c, l = .call c → c.entry.isFeeUpdate = false)
    (hcb : w.st.priorityMode.canBeActivated = true) :
    w'.st.feeParams = w.st.feeParams ∧ w'.st.multNominator = w.st.multNominator ∧
      w'.st.multDenominator = w.st.multDenominator := by
  cases h with
  | @call c s' hs => exact exec_feeInputs (call_exec hs) hc (hf c rfl) hcb
  | env => exact ⟨rfl, rfl, rfl⟩
  | foreign hfo =>
    refine ⟨hfo.feeParams, ?_, ?_⟩
    · simpa [State.owned] using congrArg Owned.multNominator hfo.1
    · simpa [State.owned] using congrArg Owned.multDenominator hfo.1

theorem stage_one_fee_inputs_move_only_by_fee_updates :
    Properties.StageOneFeeInputsMoveOnlyByFeeUpdates := by
  intro K w w' ls hr
  induction hr with
  | nil => intro _ _ _; exact ⟨rfl, rfl, rfl, rfl⟩
  | @cons w w₁ w₂ l ls hs _ ih =>
    intro hnc hcb hf
    have hl : l.runsCut = false := hnc l List.mem_cons_self
    obtain ⟨h1, h2, h3⟩ :=
      step_feeInputs hs hl (fun c hc => hf c (hc ▸ List.mem_cons_self)) hcb
    have hcb1 : w₁.st.priorityMode.canBeActivated = true := ((step_oneWay hs hl).2.2 hcb).1
    obtain ⟨i1, i2, i3, _⟩ := ih (fun l' hl' => hnc l' (List.mem_cons_of_mem _ hl')) hcb1
      (fun c hc => hf c (List.mem_cons_of_mem _ hc))
    refine ⟨i1.trans h1, i2.trans h2, i3.trans h3, ?_⟩
    unfold State.derivedGasPrice
    rw [i1, i2, i3, h1, h2, h3]

/-! ## Witnesses -/

theorem pricing_mode_change_witness : Properties.PricingModeChangeWitness :=
  ⟨nullConfig, nullEnv, { freshState with frozen := true },
    { freshState with frozen := true, feeParams := ⟨1, 0, 0, 0, 0, 0⟩ }, 0, 1, rfl, rfl, rfl,
    by decide⟩

/-- `freshState` after the admin's `changeFeeParams` at time `1000`. -/
def feeS1 : State :=
  { freshState with feeParams := ⟨0, 0, 0, 0, 0, 5⟩, lastFeeParamsUpdate := 1000 }
/-- `feeS1` after another facet committed a batch. -/
def feeS2 : State := { feeS1 with totalBatchesCommitted := 1 }
/-- `feeS2` after the CTM's `setTokenMultiplier(2, 1)` one day later. -/
def feeS3 : State :=
  { feeS2 with
    multNominator := 2
    multDenominator := 1
    lastTokenMultiplierUpdate := 1000 + PRICE_UPDATE_INTERVAL }

theorem fee_updates_witness : Properties.FeeUpdatesWitness := by
  refine ⟨nullConfig, ⟨freshState, nullEnv⟩, ⟨feeS3, ownerEnv⟩,
    ⟨1, 1000, .changeFeeParams ⟨0, 0, 0, 0, 0, 5⟩⟩,
    ⟨9, 1000 + PRICE_UPDATE_INTERVAL, .setTokenMultiplier 2 1⟩,
    [.env ownerEnv, .foreign feeS2, .call ⟨9, 1000 + PRICE_UPDATE_INTERVAL, .setTokenMultiplier 2 1⟩],
    rfl, by decide, ?_, ?_, ⟨ownerEnv, by simp⟩, ⟨feeS2, by simp⟩, by simp, rfl, rfl⟩
  · refine Run.cons (w₁ := ⟨feeS1, nullEnv⟩) (Step.call rfl) ?_
    refine Run.cons (Step.env _) ?_
    refine Run.cons (Step.foreign ⟨rfl, fun h => h⟩) ?_
    refine Run.cons (Step.call ?_) (Run.nil _)
    simp [call, exec, req, onlyL1, nullConfig, minUpdateIntervalPassed, feeS3, feeS2, feeS1,
      freshState]
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> rfl

/-- A chain with priority mode allowed whose fee inputs price L2 gas at `100`: validium pricing,
batch overhead `10` L1 gas, unit capacities, and a base-token multiplier `10 / 10^9` (so the
reference L1 gas price converts to `10`). -/
def boundedFeeState : State :=
  { freshState with
    priorityMode := ⟨true, false, 0, 0⟩
    feeParams := ⟨1, 10, 1, 1, 1, 0⟩
    multNominator := 10
    multDenominator := 10 ^ 9 }

theorem boundedFeeState_price : boundedFeeState.derivedGasPrice = 100 := by
  simp [State.derivedGasPrice, boundedFeeState, safeDerivedL2GasPrice, deriveL2GasPriceFromParams,
    REQUIRED_L2_GAS_PRICE_PER_PUBDATA]

/-- `boundedFeeState` after the admin's `changeFeeParams` raising `minimalL2GasPrice` to `20` at
time `1000`: the derived price becomes `120`. -/
def boundedFeeParamsUpdated : State :=
  { boundedFeeState with feeParams := ⟨1, 10, 1, 1, 1, 20⟩, lastFeeParamsUpdate := 1000 }

/-- `boundedFeeState` after the admin's `setTokenMultiplier(11, 10^9)` at time `1000`: the
derived price becomes `110`. -/
def boundedMultiplierUpdated : State :=
  { boundedFeeState with
    multNominator := 11
    multDenominator := 10 ^ 9
    lastTokenMultiplierUpdate := 1000 }

theorem stage_one_fee_update_witness : Properties.StageOneFeeUpdateWitness := by
  refine ⟨nullConfig, nullEnv, boundedFeeState, boundedFeeParamsUpdated, boundedMultiplierUpdated,
    1, 1000, ⟨1, 10, 1, 1, 1, 20⟩, 11, 10 ^ 9, rfl, by rw [boundedFeeState_price]; decide,
    ?_, ?_, ?_, ?_⟩
  · simp [call, exec, req, onlyL1, nullConfig, minUpdateIntervalPassed, priceChangeWithinBound,
      safeDerivedL2GasPrice, deriveL2GasPriceFromParams, boundedFeeParamsUpdated, boundedFeeState,
      freshState, REQUIRED_L2_GAS_PRICE_PER_PUBDATA, MAX_PRICE_CHANGE_NUMERATOR,
      MAX_PRICE_CHANGE_DENOMINATOR]
  · rw [boundedFeeState_price]
    simp [State.derivedGasPrice, boundedFeeParamsUpdated, boundedFeeState, safeDerivedL2GasPrice,
      deriveL2GasPriceFromParams, REQUIRED_L2_GAS_PRICE_PER_PUBDATA]
  · simp [call, exec, req, onlyL1, nullConfig, minUpdateIntervalPassed, priceChangeWithinBound,
      safeDerivedL2GasPrice, deriveL2GasPriceFromParams, boundedMultiplierUpdated,
      boundedFeeState, freshState, REQUIRED_L2_GAS_PRICE_PER_PUBDATA, MAX_PRICE_CHANGE_NUMERATOR,
      MAX_PRICE_CHANGE_DENOMINATOR]
  · rw [boundedFeeState_price]
    simp [State.derivedGasPrice, boundedMultiplierUpdated, boundedFeeState, safeDerivedL2GasPrice,
      deriveL2GasPriceFromParams, REQUIRED_L2_GAS_PRICE_PER_PUBDATA]

/-- `boundedFeeState` after the admin nominated `2`. -/
def stageOneNominated : State := { boundedFeeState with pendingAdmin := 2 }
/-- `stageOneNominated` after the Mailbox enqueued a priority transaction. -/
def stageOneQueued : State := { stageOneNominated with ptNextLeafIndex := 1 }

theorem stage_one_fee_inputs_witness : Properties.StageOneFeeInputsWitness := by
  refine ⟨nullConfig, ⟨boundedFeeState, nullEnv⟩, ⟨stageOneQueued, ownerEnv⟩,
    [.call ⟨1, 0, .setPendingAdmin 2⟩, .env ownerEnv, .foreign stageOneQueued], ?_, ?_, rfl,
    by rw [boundedFeeState_price]; decide, ?_, ⟨_, List.mem_cons_self⟩, ⟨ownerEnv, by simp⟩,
    ⟨stageOneQueued, by simp⟩, ?_⟩
  · refine Run.cons (w₁ := ⟨stageOneNominated, nullEnv⟩) (Step.call rfl) ?_
    refine Run.cons (Step.env _) ?_
    exact Run.cons (Step.foreign ⟨rfl, fun h => h⟩) (Run.nil _)
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl <;> rfl
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false, Label.call.injEq, reduceCtorEq] at hc
    subst hc; rfl
  · simp [State.priorityTreeSize, stageOneQueued, stageOneNominated, boundedFeeState, freshState]

/-! ## Countermodels -/

/-- `boundedFeeState` with priority mode not allowed and one unprocessed priority transaction. -/
def unboundedFeeState : State :=
  { boundedFeeState with priorityMode := ⟨false, false, 0, 0⟩, ptNextLeafIndex := 1 }

theorem price_bound_needs_priority_mode_allowed :
    Properties.PriceBoundNeedsPriorityModeAllowed := by
  refine ⟨nullConfig, nullEnv, unboundedFeeState,
    { unboundedFeeState with feeParams := ⟨1, 10, 1, 1, 1, 1000⟩, lastFeeParamsUpdate := 1000 },
    1000, ⟨1, 10, 1, 1, 1, 1000⟩, rfl, ?_, ?_, ?_, ?_⟩
  · simp [State.derivedGasPrice, unboundedFeeState, boundedFeeState, safeDerivedL2GasPrice,
      deriveL2GasPriceFromParams, REQUIRED_L2_GAS_PRICE_PER_PUBDATA]
  · simp [State.priorityTreeSize, unboundedFeeState, boundedFeeState, freshState]
  · simp [call, exec, req, onlyL1, nullConfig, minUpdateIntervalPassed, unboundedFeeState,
      boundedFeeState, freshState]
  · simp [State.derivedGasPrice, unboundedFeeState, boundedFeeState, safeDerivedL2GasPrice,
      deriveL2GasPriceFromParams, REQUIRED_L2_GAS_PRICE_PER_PUBDATA, MAX_PRICE_CHANGE_NUMERATOR,
      MAX_PRICE_CHANGE_DENOMINATOR]

/-- A chain with priority mode not allowed, rollup pricing and unit multiplier: the derived price
is `17 * 10^9 / 800` rounded up, `21250000`. -/
def rollupPricedState : State :=
  { freshState with feeParams := ⟨0, 0, 1, 1, 1, 0⟩, multNominator := 1, multDenominator := 1 }

theorem pricing_mode_moves_price_without_priority_mode :
    Properties.PricingModeMovesPriceWithoutPriorityMode := by
  refine ⟨nullConfig, ⟨rollupPricedState, nullEnv⟩,
    ⟨{ rollupPricedState with feeParams := ⟨1, 0, 1, 1, 1, 0⟩ }, nullEnv⟩,
    [.call ⟨1, 0, .setPubdataPricingMode 1⟩], Run.cons (Step.call rfl) (Run.nil _), ?_, rfl, ?_,
    ⟨0, 1, List.mem_cons_self⟩, ?_⟩
  · intro l hl; simp at hl; subst hl; rfl
  · intro c hc; simp at hc; subst hc; rfl
  · simp [State.derivedGasPrice, rollupPricedState, safeDerivedL2GasPrice,
      deriveL2GasPriceFromParams, REQUIRED_L2_GAS_PRICE_PER_PUBDATA]

theorem fee_update_at_time_zero_not_spaced : Properties.FeeUpdateAtTimeZeroNotSpaced := by
  refine ⟨nullConfig, ⟨freshState, nullEnv⟩,
    ⟨{ freshState with feeParams := ⟨0, 0, 0, 0, 0, 6⟩ }, nullEnv⟩,
    ⟨1, 0, .changeFeeParams ⟨0, 0, 0, 0, 0, 5⟩⟩, ⟨1, 0, .changeFeeParams ⟨0, 0, 0, 0, 0, 6⟩⟩,
    rfl, rfl, rfl, ?_, by decide⟩
  refine Run.cons (w₁ := ⟨{ freshState with feeParams := ⟨0, 0, 0, 0, 0, 5⟩ }, nullEnv⟩)
    (Step.call rfl) ?_
  exact Run.cons (Step.call rfl) (Run.nil _)

/-! ## Certificates -/

theorem SetPubdataPricingModeExact : Properties.SetPubdataPricingModeExact :=
  set_pubdata_pricing_mode_exact
theorem FeeUpdatesAtLeastADayApart : Properties.FeeUpdatesAtLeastADayApart :=
  fee_updates_at_least_a_day_apart
theorem StageOneFeeUpdateWithinPriceBound : Properties.StageOneFeeUpdateWithinPriceBound :=
  stage_one_fee_update_within_price_bound
theorem StageOneFeeInputsMoveOnlyByFeeUpdates :
    Properties.StageOneFeeInputsMoveOnlyByFeeUpdates :=
  stage_one_fee_inputs_move_only_by_fee_updates
theorem PricingModeChangeWitness : Properties.PricingModeChangeWitness :=
  pricing_mode_change_witness
theorem FeeUpdatesWitness : Properties.FeeUpdatesWitness :=
  fee_updates_witness
theorem StageOneFeeUpdateWitness : Properties.StageOneFeeUpdateWitness :=
  stage_one_fee_update_witness
theorem StageOneFeeInputsWitness : Properties.StageOneFeeInputsWitness :=
  stage_one_fee_inputs_witness
theorem FeeUpdateAtTimeZeroNotSpaced : Properties.FeeUpdateAtTimeZeroNotSpaced :=
  fee_update_at_time_zero_not_spaced
theorem PriceBoundNeedsPriorityModeAllowed : Properties.PriceBoundNeedsPriorityModeAllowed :=
  price_bound_needs_priority_mode_allowed
theorem PricingModeMovesPriceWithoutPriorityMode :
    Properties.PricingModeMovesPriceWithoutPriorityMode :=
  pricing_mode_moves_price_without_priority_mode

end Contracts.AdminFacet
