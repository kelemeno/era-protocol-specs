# AtomicFlowManager

Source: `contracts/atomic-interop/AtomicFlowManager.sol` in the pinned era-contracts tree.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| FlowCanonical | [Specs/FlowCanonical.lean](Specs/FlowCanonical.lean) | [Properties/FlowCanonical.lean](Properties/FlowCanonical.lean) | [Proofs/FlowCanonical.lean](Proofs/FlowCanonical.lean) |
| FlowCanonicalAtHead (`3605e82`) | [Specs/FlowCanonicalAtHead.lean](Specs/FlowCanonicalAtHead.lean) | [Properties/FlowCanonicalAtHead.lean](Properties/FlowCanonicalAtHead.lean) | [Proofs/FlowCanonicalAtHead.lean](Proofs/FlowCanonicalAtHead.lean) |
| RecoveryLimits | [Specs/RecoveryLimits.lean](Specs/RecoveryLimits.lean) | [Properties/RecoveryLimits.lean](Properties/RecoveryLimits.lean) | [Proofs/RecoveryLimits.lean](Proofs/RecoveryLimits.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |

`FlowCanonicalAtHead` (namespace `Contracts.FlowCanonicalAtHead`) models
`_validateAndComputeFlowId` and `_checkFlowId` at era-contracts `main` `3605e82`, next to
the pin's `FlowCanonical`, which is unchanged. At that commit the preimage is one struct
with a version byte, two checks are new (version `0x01`, at most eight legs), and one
function serves `append`, `requireFlowFinalized` and `authorizeRefund`. The function and
`append` are the same text at `draft/v0.35.0` (`d9f6789`).

- The pin's `Valid` is still necessary and no longer sufficient
  (`AcceptedPreimageIsValid`, `ValidNoLongerSufficient`); acceptance is exactly `Valid`
  plus the version plus the cap (`AcceptedIffValidVersionCap`, `ValidateIsSomeIffAccepted`).
- An accepted preimage is canonical and gives each leg one declared source chain
  (`AcceptedPreimageIsCanonical`, `DeclaredSourceChainUnique`, `ListedLegIsDeclared`).
- A preimage the new checks reject is rejected on all three paths
  (`NewChecksRejectOnEveryPath`); the gate verifies at most eight proofs
  (`AcceptedHasAtMostMaxLegs`).
- Recorded, but unfoldings with no content of their own: `SharedValidationNoDrift` (the
  model has one function because the source has one), `CheckedFlowsAgreeOrClash` and
  `DifferentVersionsShareAnIdOnlyByClash` (two different preimages with one id are a
  `PreimageClash` by definition). Their use is in `Protocol/InteropAtomicity`
  `FlowBindingAtHead`, where both preimages come from one run's log.
- `keccak256(abi.encode(preimage))` is the free parameter `enc`; no property of it is
  assumed. `PreimageHashInjOnSatisfiable` and `HonestPreimageHashNoClash` show the bounded
  premise and the clash disjunct are not empty; `FlowCanonicalAtHeadWitness` is the
  satisfiability witness.

The full flow gate spans `AtomicInteropProof`, the commitment tree, and the
handler. Its multi-chain composition lives in `../../Protocol/`. Implementation
refinement and the known generator mismatch are recorded in
`../../Refinement.lean`; this folder does not certify the compiled contract.
