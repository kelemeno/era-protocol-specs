import EraSpec.Contracts.IndexedMerkleTree.History.Properties.PinnedGate
import EraSpec.Contracts.IndexedMerkleTree.Proofs.ReclaimGateFaithful

/-!
# History proofs: the deployed reclaim gate at the interop pin `c67894b9`

Proofs of `EraSpec.Contracts.IndexedMerkleTree.History.Properties.PinnedGate`, from the lemmas of
the canonical `Proofs/ReclaimGateFaithful.lean`.
-/

namespace IMTAbstract.ReclaimGateFaithful.History

open Clear IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree
open IMTAbstract.ReclaimGateFaithful

theorem PinnedGateAcceptsEveryValueBelowCapacity :
    Properties.PinnedGateAcceptsEveryValueBelowCapacity :=
  pinned_gate_accepts_every_value_below_capacity

theorem PinnedGateAcceptsEveryValueOffPowersOfTwo :
    Properties.PinnedGateAcceptsEveryValueOffPowersOfTwo :=
  pinned_gate_accepts_every_value_off_powers_of_two

theorem PinnedCounterexampleMeetsCapstoneHypotheses :
    Properties.PinnedCounterexampleMeetsCapstoneHypotheses :=
  pinned_counterexample_meets_capstone_hypotheses

theorem PinnedReclaimDichotomyReadingFails : Properties.PinnedReclaimDichotomyReadingFails :=
  pinned_reclaim_dichotomy_reading_fails

theorem PinnedDeliveryFinalityReadingFails : Properties.PinnedDeliveryFinalityReadingFails :=
  pinned_delivery_finality_reading_fails

end IMTAbstract.ReclaimGateFaithful.History
