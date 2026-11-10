# Provenance and local ownership

## Origin of copied material

Twenty-six modules were selectively copied from the `contracts-formal-verification`
repository at the time of extraction. The original selection was mechanical: a
transitive classification of its `specs/` tree found modules reachable without
`generated.*` (solc output) or any `Clear.*` module other than `Clear.UInt256`.
The source tree then contained roughly 2,700 spec modules. The table records the
origin of each copied proof entry point; it is historical provenance, not a live
link or dependency.

| current proof entry point (imports its spec and properties) | came from |
|---|---|
| `EraSpec/Core/FinBits.lean` | `specs/FinBits.lean` |
| `EraSpec/Contracts/FullMerkle/Proofs/Model.lean` | `specs/MerkleSpec.lean` |
| `EraSpec/Contracts/Merkle/Proofs/ProofSound.lean` | `specs/MerkleProofSound.lean` |
| `EraSpec/Contracts/FullMerkle/Proofs/CachedHashInjectivity.lean` | `specs/MerkleCachedInj.lean` |
| `EraSpec/Contracts/IndexedMerkleTree/Proofs/Model.lean` | `specs/IMTAbstract.lean` |
| `EraSpec/Contracts/AtomicFlowManager/Proofs/FlowCanonical.lean` | `specs/AttackVectors/FlowCanonical.lean` |
| `EraSpec/Contracts/AtomicFlowManager/Proofs/RecoveryLimits.lean` | `specs/AttackVectors/RecoveryLimits.lean` |
| `EraSpec/Contracts/IndexedMerkleTree/Proofs/InsertGuard.lean` | `specs/AttackVectors/InsertGuard.lean` |
| `EraSpec/Contracts/IndexedMerkleTree/Proofs/ResetAndZero.lean` | `specs/AttackVectors/ResetAndZero.lean` |
| `EraSpec/Contracts/InteropHandlerBase/Proofs/BundleStatusMachine.lean` | `specs/AttackVectors/BundleStatusMachine.lean` |
| `EraSpec/Contracts/InteropHandlerBase/Proofs/SelfCallAuthority.lean` | `specs/AttackVectors/SelfCallAuthority.lean` |
| `EraSpec/Contracts/L2InteropHandler/Proofs/AtomicSourceBinding.lean` | `specs/AttackVectors/AtomicSourceBinding.lean` |
| `EraSpec/Contracts/InteropDataEncoding/Proofs/BundleHashEncoding.lean` | `specs/AttackVectors/BundleHashEncoding.lean` |
| `EraSpec/Contracts/FullMerkle/Proofs/CapacityInvariant.lean` | `specs/AttackVectors/CapacityInvariant.lean` |
| `EraSpec/Contracts/FullMerkle/Proofs/TreeShape.lean` | `specs/AttackVectors/TreeShape.lean` |
| `EraSpec/Contracts/Merkle/Proofs/RootBinding.lean` | `specs/AttackVectors/RootBinding.lean` |
| `EraSpec/Contracts/Merkle/Proofs/RootForgery.lean` | `specs/AttackVectors/RootForgery.lean` |
| `EraSpec/Contracts/AtomicInteropProof/Proofs/TimeoutSoundness.lean` | `specs/AttackVectors/TimeoutSoundness.lean` |
| `EraSpec/Contracts/AtomicInteropProof/Proofs/ProofPolarity.lean` | `specs/AttackVectors/ProofPolarity.lean` |
| `EraSpec/Contracts/AtomicInteropProof/Proofs/LastBatchInRoot.lean` | `specs/AttackVectors/LastBatchInRoot.lean` |
| `EraSpec/Contracts/AtomicInteropProof/Proofs/StaleSnapshot.lean` | `specs/AttackVectors/StaleSnapshot.lean` |
| `EraSpec/Contracts/AtomicInteropProof/Proofs/Timestamps.lean` | `specs/AttackVectors/Timestamps.lean` |
| `EraSpec/Protocol/DestinationCapstone.lean` | `specs/AttackVectors/DestinationCapstone.lean` |
| `EraSpec/Protocol/FlowAtomicity.lean` | `specs/AttackVectors/FlowAtomicity.lean` |
| `EraSpec/Protocol/LocalHonesty.lean` | `specs/AttackVectors/LocalHonesty.lean` |
| `EraSpec/Protocol/NoTheft.lean` | `specs/AttackVectors/NoTheft.lean` |


The copied material is maintained as local code in this repository. Contract
modules have since been split into specifications, named property statements, and
proofs. Public theorem names and namespaces were retained where applicable, and
proof bodies were adjusted locally to reference the named propositions. Lean builds
and checks these local modules against this repository's Mathlib dependency.

`EraSpec/Core/Word.lean` is a separate historical case: it originated as a trimmed
copy of Clear's `UInt256.lean`, with the word type and arithmetic retained and EVM
opcodes and byte serialization omitted. It is now a local definition. It is not a
shared module with Clear, and identical origins do not establish a connection
between theorem statements in the two repositories.

Material authored for this repository includes the AtomicFlowManager and
L2InteropCommitmentTree state-machine models, `Protocol/Spec.lean`,
`Core/PreparedApplication.lean`, `Examples/BurnMintBridge/*`, and `Refinement.lean`.
The `BridgedStandardERC20`, `NativeTokenVaultBase`, and protocol
`AssetBridgePreparation` developments were also authored locally; they do not
import the historical compiled contracts or their proof files.
Their initializer, registration, and invariant-composition extensions were also
authored here against the same source pin; historical compiled proofs supply
none of their assumptions or implementation correspondence.
The reference bridge is illustrative, not a transcription or verification of the
deployed asset router or token vault.

### Ported from the `claude/proof-attempt-4f3778` line

That branch used an older flat `Contracts/`, `Properties/`, `Proofs/` layout. Its
new material was ported here without changing any statement: the commitment-tree
`Reaches`, `HintSearch` and `TreeRoot` topics; `Merkle` `Verifier` (was
`Core/MerkleVerifier.lean`); `AtomicInteropProof` `LastLeaf` (was
`Core/LastLeaf.lean`); and `Protocol/InteropAtomicity/` (`Atomicity`, `Timeout`,
`Refund`). Its restatements of the commitment-tree, flow-manager and protocol
theorems duplicated properties already split out here, so they were dropped.
Properties became `Properties.X` in the model's namespace, with certificates at
`X`, as the audit requires. `HashAssumptionsUnsatisfiable` was added during the
port; it shows that the line's `HashAssumptions` premise cannot hold.

## Implementation correspondence remains open

The abstract proofs establish properties of the definitions and assumptions in
this repository. They do not establish that Solidity source or deployed bytecode
implements those definitions. Connecting each relevant source path, including
success and failure behavior, to these models is a separate open work item. The
older repository's compiled proofs are not imported, depended upon, or claimed as
supplying that correspondence.

## Pinned source context

* Lean `v4.9.1`; Mathlib `09d33efc68d3ad52db77b731d7253675395a14aa`.
* Source context for the original extraction: era-contracts commit
  `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`. Contract-specific models were
  reviewed against the Solidity files at that source pin, including
  `contracts/common/libraries/IndexedMerkleTree.sol`,
  `contracts/atomic-interop/L2InteropCommitmentTree.sol`,
  `contracts/atomic-interop/AtomicFlowManager.sol`, and
  `contracts/atomic-interop/libraries/AtomicInteropProof.sol`.

These pins describe reproducibility and historical source context. They do not
imply current Solidity correspondence; that must be established independently.
