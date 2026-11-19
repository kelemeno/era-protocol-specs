import EraSpec.Contracts.AdminFacet.Properties.ExecutorBridge

/-!
# Proofs: the facet model's `_revertBatches` is the pipeline model's

Proof of `../Properties/ExecutorBridge.lean`: both transcriptions check `n ≤ committed` and
`executed ≤ n`, then write the same three fields; unfolding both and splitting on the checks.
-/

namespace Contracts.AdminFacet

theorem RevertBatchesAgreesWithExecutorModel :
    Properties.RevertBatchesAgreesWithExecutorModel := by
  intro a x n he hv hc hu
  unfold revertBatches Contracts.ExecutorFacet.revertBatches
    Contracts.ExecutorFacet.revertBatchesWith req
  rw [he, hv, hc, hu]
  by_cases h1 : n ≤ x.totalBatchesCommitted
  · have h1' : ¬ x.totalBatchesCommitted < n := by omega
    by_cases h2 : x.totalBatchesExecuted ≤ n
    · have h3 : ¬ n < x.totalBatchesExecuted := by omega
      simp only [h1, h2, h1', h3, ite_true, ite_false, Option.isSome_some, true_and, and_false]
      intro a' x' ha hx
      cases ha; cases hx
      exact ⟨rfl, rfl, rfl, rfl⟩
    · have h2' : (false = false ∧ n < x.totalBatchesExecuted) := ⟨rfl, by omega⟩
      simp [h1, h2, h1', h2']
  · have h1' : x.totalBatchesCommitted < n := by omega
    simp [h1, h1']

end Contracts.AdminFacet
