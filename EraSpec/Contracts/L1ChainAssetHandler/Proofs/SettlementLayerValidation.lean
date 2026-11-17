import EraSpec.Contracts.L1ChainAssetHandler.Properties.SettlementLayerValidation

namespace Contracts.L1ChainAssetHandler.SettlementLayerValidation

/-! ## The function -/

@[simp] lemma upd_self {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by
  simp [upd]

lemma upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by
  simp [upd, h]

theorem IsValidUnrolled : Properties.IsValidUnrolled := by
  refine ⟨fun l1 mn ivs b X k hmn h2 => ?_, fun l1 mn ivs b X k hmn => ?_⟩
  · interval_cases mn
    · simp [isValidSettlementLayer, scanIntervals, closedForm, maxMigrations, numToSL]
    · simp only [isValidSettlementLayer, maxMigrations, numToSL, closedForm]
      simp [List.range', scanIntervals]
      split_ifs <;> simp_all
    · simp only [isValidSettlementLayer, maxMigrations, numToSL, closedForm]
      simp [List.range', scanIntervals, h2]
      split_ifs <;> simp_all
  · simp only [isValidSettlementLayer, maxMigrations]
    rw [if_neg (by omega)]

end Contracts.L1ChainAssetHandler.SettlementLayerValidation
