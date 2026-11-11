import Mathlib.Tactic

import EraSpec.Contracts.AtomicInteropProof.Specs.ProofPolarity
import EraSpec.Protocol.MultichainGate.Specs.Model

/-!
# Spec: `AtomicFlowManager`'s two proof gates, with and without the source-chain comparison

Source, in the pinned era-contracts tree (`c67894b9`):
`contracts/atomic-interop/AtomicFlowManager.sol`.  Both gates compare the proof's chain with the
leg's DECLARED source chain before verifying the proof against that chain's tree:

    // requireFlowFinalized, per leg i
    if (_finality.proofs[i].sourceChainId != flow.legSourceChainIds[i]) revert ProofSourceChainMismatch(...);
    AtomicInteropProof.verifyInclusion(_finality.proofs[i], value, flow.deadline, ...);

    // authorizeRefund, for the missing leg
    if (_absence.sourceChainId != missingLegChainId) revert ProofSourceChainMismatch(...);
    AtomicInteropProof.verifyTimeoutAbsence(_absence, value, _flow.deadline, ...);

`ProofPolarity` states the consequences of `HonestInsertion` as set facts (`v ∈ tree c` /
`v ∉ tree c`).  None of its statements mentions a gate, so the claims about what the comparison
buys on each path are not stated there.  This file names the four gates.  On each path, the
prover names the proof's chain `c`.  The CHECKED gate requires `c` to equal the declared chain;
the UNCHECKED gate is the same code with the comparison deleted.  The statements in
`../Properties/ProofPolarityStrong.lean` are about these gates.

The second section connects the abstract `tree` to real commitment-tree states.  `liveKeys T c`
is the set of nonzero keys of chain `c`'s `L2InteropCommitmentTree` state.  On valid states,
`Contracts.Protocol.BoundGate` / `UnboundGate` (IMT low-leaf non-inclusion witnesses,
`EraSpec.Protocol.MultichainGate`) coincide with the checked / unchecked absence gates over
`liveKeys T`.  So the abstract statements transfer to contract states.

Model boundaries.  A proof is identified with the set fact it establishes.  The Merkle
authentication of roots, the deadline and timeout branches (`TimeoutSoundness`), and the
settlement-layer check are not modelled here.  `srcOf` is the abstract source chain of a commit
value, as in `ProofPolarity`.  `HonestInsertion srcOf (liveKeys T)` is a premise about one
concrete family of states: no nonzero key sits in the tree of a chain other than its source.
It is not a hash premise.
-/

namespace AttackVectors.ProofPolarity


variable {Chain Value : Type*}


/-! ## The four gates over the abstract trees -/

/-- **`requireFlowFinalized`'S PER-LEG GATE, AS DEPLOYED.**  The prover names the proof's chain
`c` (`_finality.proofs[i].sourceChainId`), the contract requires `c` to be the leg's declared
chain (`flow.legSourceChainIds[i]`), and the membership proof is checked against `c`'s tree. -/
def CheckedInclusionGate (tree : Chain → Set Value) (declared c : Chain) (v : Value) : Prop :=
  c = declared ∧ v ∈ tree c


/-- The finality gate with the comparison deleted: a membership proof against whichever chain
`c` the prover names. -/
def UncheckedInclusionGate (tree : Chain → Set Value) (c : Chain) (v : Value) : Prop :=
  v ∈ tree c


/-- **`authorizeRefund`'S ABSENCE GATE, AS DEPLOYED.**  The prover names the proof's chain `c`
(`_absence.sourceChainId`), the contract requires `c` to be the missing leg's declared chain
(`legSourceChainIds[_missingLegIndex]`), and the absence is checked against `c`'s tree. -/
def CheckedAbsenceGate (tree : Chain → Set Value) (declared c : Chain) (v : Value) : Prop :=
  c = declared ∧ v ∉ tree c


/-- The refund gate with the comparison deleted.  This is the surface of the double-mint attack
named in `authorizeRefund`'s comment: an absence proof against whichever chain `c` the prover
names. -/
def UncheckedAbsenceGate (tree : Chain → Set Value) (c : Chain) (v : Value) : Prop :=
  v ∉ tree c


/-! ## The commitment-tree states behind `tree` -/

/-- **THE ABSTRACT TREE OF A FAMILY OF CONTRACT STATES.**  The nonzero keys of chain `c`'s
`L2InteropCommitmentTree` state `T c`, read through the projection `toAbs` that
`Contracts.Protocol.ofChains` uses.  The sentinel `0` is dropped: `setup` seeds it into EVERY
valid tree, and `InsertGuard.nonzero` keeps it from ever being a commit value. -/
def liveKeys (T : Contracts.Protocol.Chain → Contracts.InteropCommitmentTree.Tree)
    (c : Contracts.Protocol.Chain) : Set UInt256 :=
  {v | v ≠ 0 ∧ v ∈ IMTAbstract.keys (Contracts.InteropCommitmentTree.toAbs (T c))}


end AttackVectors.ProofPolarity
