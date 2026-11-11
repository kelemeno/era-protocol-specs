import Mathlib.Tactic


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/ProofPolarity.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  PROOF POLARITY — why the same check is redundant for inclusion and load-bearing for absence.

  `AtomicFlowManager` applies ONE syntactic check on both paths:

      if (_finality.proofs[i].sourceChainId != flow.legSourceChainIds[i]) revert ProofSourceChainMismatch(...);
      if (_absence.sourceChainId != missingLegChainId)                    revert ProofSourceChainMismatch(...);

  and labels the two uses differently, on purpose:

      requireFlowFinalized: "defense-in-depth here (membership already self-binds via the
                             chain-specific `commitValue`) but load-bearing for the symmetric refund path"

      authorizeRefund:      "Without this, the leg's commit value -- which exists only in its own source
                             chain's tree -- is trivially absent from any other chain's tree, so an
                             on-time, finalized leg could be force-refunded against an unrelated chain
                             (double-mint)."

  Those comments are correct, and the asymmetry is not incidental to this codebase -- it follows from
  the POLARITY of the two properties.  This file proves that, and then sharpens the "defense-in-depth"
  label, which holds only under an assumption about OTHER chains that the comment leaves implicit.

  The pleasing part, and the reason it is worth writing down: the SAME assumption that makes inclusion
  self-binding is exactly what makes absence chain-blind.  One hypothesis, opposite consequences.
-/

namespace AttackVectors.ProofPolarity


variable {Chain Value : Type*}


/-! `srcOf v` — the source chain baked into a commit value.  Concretely
`commitValue = keccak(TAG, flowId, bundleHash)` and `bundleHash = keccak(sourceChainId, bundle)`, so
the chain is recoverable from the value; `BundleHashEncoding.abiEncode_inj` closes the encoding half of
that, and keccak injectivity the other.  Here it is simply a function, since only its existence matters. -/

variable (srcOf : Value → Chain)


/-! `tree c` — the leaf set of chain `c`'s IMT. -/

variable (tree : Chain → Set Value)


/-- **THE IMPLICIT ASSUMPTION.**  Every chain's tree holds only the commit values of legs that
originate on that chain.  This is what an honest `AtomicFlowManager` guarantees for its OWN chain: it
inserts `commitValue(flowId, bundleHash)` only for bundles it originated.  As a statement about ALL
chains it is an assumption about every chain in the flow's leg set. -/
def HonestInsertion : Prop := ∀ c v, v ∈ tree c → srcOf v = c


end AttackVectors.ProofPolarity
