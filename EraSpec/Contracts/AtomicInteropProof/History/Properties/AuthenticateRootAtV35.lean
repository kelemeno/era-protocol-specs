import EraSpec.Contracts.AtomicInteropProof.History.Specs.AuthenticateRootAtV35

/-!
# Properties (History): the v35 `_authenticateRoot` refactor, compared with the pin

Statements over `../Specs/AuthenticateRootAtV35.lean` and the current
`../../Specs/AuthenticateRootAtV35.lean`, proved in `../Proofs/AuthenticateRootAtV35.lean`.

**History.** A comparison with `_authenticateRoot` at `c67894b9`, not a claim about `b17415d20`
alone. They record that the `b17415d20` refactor changed nothing the pin-era results relied on:

* `AuthenticateRootRefactorExactV35`: the v35 `_authenticateRoot` and the pin's are the same
  function of their inputs (same reverts, same returned triple).
* `EndBranchRefactorExactV35`: up to the last-batch check, the v35 end branch and the pin's accept
  the same proofs with the same values.
-/

namespace AttackVectors.AuthenticateRootAtV35.History

open MerkleSpec MerkleSpec.Verifier

/-- **THE REFACTOR IS EXACT.** The v35 `_authenticateRoot` (positional read,
`AtomicInteropProof.sol:155-189`) and the pin's (re-parse, `:256-290@c67894b9`) agree on every
input: same reverts, same returned triple. -/
def Properties.AuthenticateRootRefactorExactV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (src batch leafIndex imtRoot : UInt256)
    (w : Proof),
    authenticateRootV35 E roots src batch leafIndex imtRoot w
      = authenticateRootPin E roots src batch leafIndex imtRoot w

/-- **THE END BRANCH IS UNCHANGED.** Up to the last-batch check, the v35 end branch (`_authenticateRoot`
against leaf 3, `readAggregationHopPath` with its new final-node revert, the zero cascade) and the
pin's accept exactly the same proofs, with the same returned triple and the same hop path. -/
def Properties.EndBranchRefactorExactV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 src batch imtRoot : UInt256) (w : Proof)
    (sl : SLRef) (hop : HopPath),
    EndBranchPassesV35 E roots z0 src batch imtRoot w sl hop
      ↔ EndBranchPassesPin E roots z0 src batch imtRoot w sl hop

end AttackVectors.AuthenticateRootAtV35.History
