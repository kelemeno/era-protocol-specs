import EraSpec.Contracts.MessageVerification.Specs.Refinement

/-!
# Properties: the status proof against the canonical chain-batch-root and `MessageRoot` models

Statements about `EraSpec.Contracts.MessageVerification.Specs.Refinement`; proofs are in
`EraSpec.Contracts.MessageVerification.Proofs.Refinement`.

* `ChainBatchRootIsCompute`: with keccak as the node hash, this folder's `chainBatchRoot` is
  `ChainBatchRootTree.compute`, given the documented value of `RESERVED_SUBTREE_NODE`
  (`ChainBatchRootTree.ReservedSubtreeDocumented`, a premise on two keccak inputs).  So the
  status-proof results, stated over `chainBatchRoot`, are about the root `ChainBatchRootTree`
  models.
* `StatusProofAtMessageRoot`: for a batch `n > 0` whose root the canonical `MessageRoot` storage
  is authoritative for (`n` at or above `v31UpgradeChainBatchNumber[c]`, or a root recorded at
  `n`), `LogProofAccepted` against `R = chainBatchRoots[c][n]` is exactly the default-leaf and
  bounds checks followed by the canonical model's final-node verdict on the walk's result.  So the
  status-proof results, stated for an abstract `R`, apply to the root the L1 contract compares.
-/

namespace Contracts.MessageVerification

open Contracts.MessageHashing
open MerkleSpec MerkleSpec.Verifier

/-- **THE TWO CHAIN BATCH ROOTS AGREE.** Under the documented value of `RESERVED_SUBTREE_NODE`,
`chainBatchRoot (efficientHash keccak) a b c d = ChainBatchRootTree.compute keccak a b c d` for all
four leaves. -/
def Properties.ChainBatchRootIsCompute : Prop :=
  ∀ keccak : Keccak, Contracts.ChainBatchRootTree.ReservedSubtreeDocumented keccak →
    ∀ a b c d : UInt256,
      chainBatchRoot (efficientHash keccak) a b c d = Contracts.ChainBatchRootTree.compute keccak a b c d

/-- **THE STATUS PROOF AGAINST THE L1 `MessageRoot`.** For any canonical `MessageRoot` storage `s`,
configuration and call environment, chain `c` and batch `n > 0` with `v31UpgradeChainBatchNumber[c]
≤ n` or a nonzero recorded root at `n`: a log proof is accepted against `R = chainBatchRoots[c][n]`
exactly when its leaf is not the default leaf hash, `k < 256`, `j < 2^k`, and the canonical
model's final-node check accepts the walk's result for `(c, n)`. -/
def Properties.StatusProofAtMessageRoot : Prop :=
  ∀ (keccak : Keccak) (cfg : Contracts.MessageRoot.Config) (env : Contracts.MessageRoot.Env)
    (s : Contracts.MessageRoot.State) (c n : ℕ) (ℓ : L2Log) (j : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    0 < n → (cfg.v31Upgrade c ≤ n ∨ s.chainBatchRoots c n ≠ 0) →
      (LogProofAccepted keccak (s.chainBatchRoots c n) ℓ j sibs k ↔
        logLeaf keccak ℓ ≠ keccak logDefaultPre ∧ k < 256 ∧ j < 2 ^ k
          ∧ Contracts.MessageRoot.finalNodeAccepts cfg env s c n
              (walkPure (efficientHash keccak) sibs 0 k j (logLeaf keccak ℓ)) = some true)

end Contracts.MessageVerification
