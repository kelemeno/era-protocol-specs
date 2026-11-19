import EraSpec.Contracts.MessageVerification.Properties.Refinement
import EraSpec.Contracts.MessageRoot.Proofs.Model

/-!
# Proofs: the status proof against the canonical chain-batch-root and `MessageRoot` models

`efficientHash keccak` and `ChainBatchRootTree.node keccak` hash the same 64-byte string, so the
two roots differ only in how the reserved node is written; the documented value equates them.
The `MessageRoot` side is `Contracts.MessageRoot.FinalNodeAcceptsIff` with its pre-v31 fallback
excluded by the premise.
-/

namespace Contracts.MessageVerification

open Contracts.MessageHashing
open MerkleSpec MerkleSpec.Verifier

theorem chain_batch_root_is_compute (keccak : Keccak)
    (hdoc : Contracts.ChainBatchRootTree.ReservedSubtreeDocumented keccak) (a b c d : UInt256) :
    chainBatchRoot (efficientHash keccak) a b c d =
      Contracts.ChainBatchRootTree.compute keccak a b c d := by
  unfold Contracts.ChainBatchRootTree.compute
  rw [hdoc]
  rfl

theorem status_proof_at_message_root (keccak : Keccak) (cfg : Contracts.MessageRoot.Config)
    (env : Contracts.MessageRoot.Env) (s : Contracts.MessageRoot.State) (c n : ℕ) (ℓ : L2Log)
    (j : ℕ) (sibs : ℕ → UInt256) (k : ℕ) (hn : 0 < n)
    (hauth : cfg.v31Upgrade c ≤ n ∨ s.chainBatchRoots c n ≠ 0) :
    LogProofAccepted keccak (s.chainBatchRoots c n) ℓ j sibs k ↔
      logLeaf keccak ℓ ≠ keccak logDefaultPre ∧ k < 256 ∧ j < 2 ^ k
        ∧ Contracts.MessageRoot.finalNodeAccepts cfg env s c n
            (walkPure (efficientHash keccak) sibs 0 k j (logLeaf keccak ℓ)) = some true := by
  rw [Contracts.MessageRoot.FinalNodeAcceptsIff]
  unfold LogProofAccepted
  constructor
  · rintro ⟨h1, h2, h3, hw, hR⟩
    exact ⟨h1, h2, h3, hn, hw ▸ hR, Or.inl hw.symm⟩
  · rintro ⟨h1, h2, h3, -, hw0, hR | ⟨hz, hv, -⟩⟩
    · exact ⟨h1, h2, h3, hR.symm, hR ▸ hw0⟩
    · rcases hauth with hauth | hauth
      · exact absurd hv (by omega)
      · exact absurd hz hauth

theorem ChainBatchRootIsCompute : Properties.ChainBatchRootIsCompute :=
  fun keccak hdoc a b c d => chain_batch_root_is_compute keccak hdoc a b c d
theorem StatusProofAtMessageRoot : Properties.StatusProofAtMessageRoot :=
  fun keccak cfg env s c n ℓ j sibs k hn hauth =>
    status_proof_at_message_root keccak cfg env s c n ℓ j sibs k hn hauth

end Contracts.MessageVerification
