import EraSpec.Contracts.AdminFacet.Specs.AdminFacet
import EraSpec.Contracts.ExecutorFacet.Specs.Pipeline

/-!
# Properties: the facet model's `_revertBatches` is the pipeline model's

`ZKChainBase._revertBatches` (`state-transition/chain-deps/facets/ZKChainBase.sol:317-337` at
`b17415d20`) is transcribed twice: in this folder's `Specs/AdminFacet.lean` (`revertBatches`,
which `activatePriorityMode` calls) and in `../ExecutorFacet/Specs/Pipeline.lean`
(`revertBatches`, which `revertBatchesSharedBridge` and the pipeline's `activatePriorityMode`
call). The statement below says the two transcriptions are the same function on the fields both
models keep: the three batch counters and the L2 upgrade batch number. Proof:
`../Proofs/ExecutorBridge.lean`. No hash premise.
-/

namespace Contracts.AdminFacet

/-- **THE TWO `_revertBatches` TRANSCRIPTIONS AGREE.** Take a state `a` of the facet model and a
state `x` of the pipeline model that agree on `totalBatchesExecuted`, `totalBatchesVerified`,
`totalBatchesCommitted` and the L2 upgrade batch number. For every `n`, `_revertBatches(n)`
succeeds in one model iff it succeeds in the other, and on success the two results agree again
on those four fields. Neither transcription writes any other field (here by its definition, a
`{ s with … }` update of three fields; in the pipeline model `RevertBatchesEffect`). -/
def Properties.RevertBatchesAgreesWithExecutorModel : Prop :=
  ∀ (a : State) (x : Contracts.ExecutorFacet.State) (n : ℕ),
    a.totalBatchesExecuted = x.totalBatchesExecuted →
    a.totalBatchesVerified = x.totalBatchesVerified →
    a.totalBatchesCommitted = x.totalBatchesCommitted →
    a.upgradeBatchNumber = x.l2SystemContractsUpgradeBatchNumber →
      ((revertBatches a n).isSome = (Contracts.ExecutorFacet.revertBatches x n).isSome)
      ∧ ∀ a' x', revertBatches a n = some a' → Contracts.ExecutorFacet.revertBatches x n = some x' →
          a'.totalBatchesExecuted = x'.totalBatchesExecuted
          ∧ a'.totalBatchesVerified = x'.totalBatchesVerified
          ∧ a'.totalBatchesCommitted = x'.totalBatchesCommitted
          ∧ a'.upgradeBatchNumber = x'.l2SystemContractsUpgradeBatchNumber

end Contracts.AdminFacet
