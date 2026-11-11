# AtomicFlowManager

Source: `contracts/atomic-interop/AtomicFlowManager.sol` in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| FlowCanonical | [Specs/FlowCanonical.lean](Specs/FlowCanonical.lean) | [Properties/FlowCanonical.lean](Properties/FlowCanonical.lean) | [Proofs/FlowCanonical.lean](Proofs/FlowCanonical.lean) |
| RecoveryLimits | [Specs/RecoveryLimits.lean](Specs/RecoveryLimits.lean) | [Properties/RecoveryLimits.lean](Properties/RecoveryLimits.lean) | [Proofs/RecoveryLimits.lean](Proofs/RecoveryLimits.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |

The full flow gate spans `AtomicInteropProof`, the commitment tree, and the
handler. Its multi-chain composition lives in `../../Protocol/`. Implementation
refinement and the known generator mismatch are recorded in
`../../Refinement.lean`; this folder does not certify the compiled contract.
