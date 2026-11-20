import Mathlib.Tactic


/- EXTRACTED from contracts-formal-verification (`specs/specs/AttackVectors/ProofPolarity.lean`) — protocol-level,
   no EVM semantics.  The sibling copy is still the one that repo builds against; see
   PROVENANCE.md for the pending migration and the drift risk it carries. -/

/-
  PROOF POLARITY — why the same check is redundant for inclusion and load-bearing for absence.

  `AtomicFlowManager` (era-contracts `b17415d20`, `atomic-interop/AtomicFlowManager.sol`) applies
  ONE syntactic check on both paths:

      if (_finality.proofs[i].sourceChainId != preimage.legSourceChainIds[i]) revert ProofSourceChainMismatch(...);  // :198-200
      if (_absence.sourceChainId != missingLegChainId)                         revert ProofSourceChainMismatch(...);  // :228-230

  and labels the two uses differently, on purpose:

      requireFlowFinalized (:192-194): "The per-proof source-chain check is defense-in-depth here
                             (inclusion self-binds via the chain-specific commit value) but
                             load-bearing on the symmetric refund path."

      authorizeRefund (:221-223): "a commit value is trivially absent from any OTHER chain's tree,
                             so an unbound proof would allow a double-mint refund of a finalized flow."

  (The extraction pin `c67894b9` carried the same two checks with longer comments.)

  Those comments are correct, and the asymmetry is not incidental to this codebase -- it follows from
  the POLARITY of the two properties.  This file proves that, and then sharpens the "defense-in-depth"
  label, which holds only under an assumption about OTHER chains that the comment leaves implicit.

  The pleasing part, and the reason it is worth writing down: the SAME assumption that makes inclusion
  self-binding is exactly what makes absence chain-blind.  One hypothesis, opposite consequences.

  Correction (ProofPolarityFaithful).  This file writes a leg's chain as one value `srcOf v`,
  but both checks compare the proof's chain with the flow's DECLARED chain
  `legSourceChainIds[i]`.  With the two kept apart the finality-side check is load-bearing
  exactly for misdeclared legs: `AttackVectors.ProofPolarityFaithful.UncheckedDoubleMintIffMisdeclared`
  (per leg) and `FlowDoubleMintIffSomeMisdeclared` (per flow).  At `b17415d20` `append` binds the
  declared chain to the committing one (`AtomicFlowManager.sol:140-146`), so on trees written only
  by it the identification holds and the check is redundant (`UpgradeExcludesMisdeclared`,
  `UpgradeCheckARedundant`).  The pinned `append` did not bind them, and there the "defense-in-depth"
  reading was false (`AttackVectors.ProofPolarityFaithful.History.PinnedMisdeclaredDoubleMint`,
  History).
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
