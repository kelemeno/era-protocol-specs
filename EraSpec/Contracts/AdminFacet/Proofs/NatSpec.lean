import EraSpec.Contracts.AdminFacet.Properties.NatSpec
import EraSpec.Contracts.AdminFacet.Proofs.PriorityMode

/-!
# Proofs: the two `IAdmin` NatSpec statements the code does not match

Each `Properties.X` of `EraSpec.Contracts.AdminFacet.Properties.NatSpec` is proved as `X`.
-/

namespace Contracts.AdminFacet

theorem pricing_mode_ignores_batches : Properties.PricingModeIgnoresBatches := by
  intro K e s a τ m hfz
  simp only [Entry.sel] at hfz
  simp only [call, exec, req, onlyL1, Entry.sel, hfz, not_false_eq_true, ite_true]
  by_cases h1 : a = s.admin <;> by_cases h2 : K.onL1 = true <;>
    by_cases h3 : s.priorityMode.canBeActivated = false <;> simp [h1, h2, h3]

/-- A chain with five committed, verified and executed batches. -/
def liveState : State :=
  { freshState with
    totalBatchesCommitted := 5
    totalBatchesVerified := 5
    totalBatchesExecuted := 5 }

theorem pricing_mode_changes_after_first_batch : Properties.PricingModeChangesAfterFirstBatch :=
  ⟨nullConfig, nullEnv, liveState,
    { liveState with feeParams := { liveState.feeParams with pricingMode := 1 } }, 0, 1,
    by decide, by decide, rfl, by decide⟩

/-- After `permanentlyAllowPriorityMode` on `pm1`, without `makePermanentRollup`. -/
def nsAllowed : State :=
  { pm1 with transactionFilterer := 0, priorityMode := ⟨true, false, 0, 0⟩ }

theorem activation_natspec_conditions_insufficient :
    Properties.ActivationNatSpecConditionsInsufficient := by
  refine ⟨nullConfig, ⟨freshState, pmEnv⟩, ⟨nsAllowed, pmEnv⟩,
    [.foreign pm1, .call ⟨1, 0, .permanentlyAllowPriorityMode⟩], 7, 100 + PRIORITY_EXPIRATION,
    ?_, ?_, rfl, rfl, rfl, rfl, by decide, by decide, rfl, rfl, rfl, ?_⟩
  · refine Run.cons (w₁ := ⟨pm1, pmEnv⟩) (Step.foreign ⟨rfl, fun h => h⟩) ?_
    exact Run.cons (Step.call rfl) (Run.nil _)
  · intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl <;> rfl
  · simp [call, exec, req, onlySettlementLayer, onlyL1, nsAllowed, pm1, freshState,
      nullConfig]

/-! ## Certificates -/

theorem PricingModeIgnoresBatches : Properties.PricingModeIgnoresBatches :=
  pricing_mode_ignores_batches
theorem PricingModeChangesAfterFirstBatch : Properties.PricingModeChangesAfterFirstBatch :=
  pricing_mode_changes_after_first_batch
theorem ActivationNatSpecConditionsInsufficient :
    Properties.ActivationNatSpecConditionsInsufficient :=
  activation_natspec_conditions_insufficient

end Contracts.AdminFacet
