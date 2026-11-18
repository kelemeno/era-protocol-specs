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
L2InteropCommitmentTree state-machine models, `Protocol/MultichainGate/` (was `Protocol/Spec.lean`),
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
new material was ported here: the commitment-tree `Reaches`, `HintSearch` and
`TreeRoot` topics; `Merkle` `Verifier` (was `Core/MerkleVerifier.lean`);
`AtomicInteropProof` `LastLeaf` (was `Core/LastLeaf.lean`);
`Protocol/InteropAtomicity/` (`Atomicity`, `Timeout`, `Refund`); and the bridge and
upgrade models `NativeTokenVaultBase` `RegistryAndEscrow`, `AssetRouterBase`
`HandlerRegistration` and `ProxyUpgradeRowLib` `Rows`. Properties became
`Properties.X` in the model's namespace, with certificates at `X`, as the audit
requires. Models and statements were compared mechanically with the originals and
are unchanged, with four exceptions that only remove a premise the proof never used
(so each becomes stronger): `SubsetFlowPassesUncheckedGate`,
`SelfOnlyGateAdmitsMixedOutcome`, `StaleRootRefundsDeliveredLeg` (dropped
`HashAssumptions`) and `PerChainIsolationFails` (dropped `IdAssumptions` and
`thisChain ≠ 0`). Added: the unsatisfiability theorems for `HashAssumptions`, both
`IdAssumptions`, `FlowHashInj` and `CommitValueInj` (see ASSUMPTIONS.md).

That branch also restated base theorems as separate properties. The
commitment-tree and flow-manager restatements duplicate properties already split
out here and were dropped. Its nine `Properties.Protocol` statements (bound gate,
`ChainsNoDoubleSpend`, the unbound-gate countermodel) were dropped too; their
counterparts are the split `Protocol/MultichainGate/` properties (the old
`Protocol/Spec.lean` is now a compatibility import of it).

### Authored in round 5

All of the following were written in this repository against the pins below; none
is copied, and none imports the historical compiled contracts or their proofs. Each
is a new `Specs/`, `Properties/`, `Proofs/` topic, except that `ResolutionCorrespondence`
and `ExecutorRowsUnvalidated` have properties and proofs only.

* At era-contracts `c67894b9`:
  - `AssetRouterBase`: `AtomicRecovery`, `AllWriters`, `VaultMintGate`,
    `CounterpartGate`, `HandlerRegistrationRuns`, `PausedRecovery`.
  - `NativeTokenVaultBase`: `Resolution` (with `ResolutionCorrespondence`),
    `RegistrationUnified`, `Reinitialization`, `LegacyFallback`, `Pause`.
  - `BridgedStandardERC20`: `Reinitialization`, `LegacyFallback`. The OpenZeppelin
    v4.9 lines `Reinitialization` cites were read from a v4.9.6 copy, because the
    pinned tree's submodules are not checked out (see that spec's header).
  - `InteropCenter` (new contract folder): `Dispatch`.
  - `InteropDataEncoding` `BundleHashPinned`; `InteropHandlerBase` `Reentrancy`;
    `L2InteropHandler` `SourceBindingReduced`;
    `L2InteropCommitmentTree` `CachedRoot`, `InitOnce`, `PublishedRootCommits`;
    `FullMerkle` `CachedNodes`; `Merkle` `RootForgeryPinned`.
  - `Protocol/InteropAtomicity` `FlowBinding`, `OncePerLeg`, `Pause`, `SharedCommitment`,
    `Operational`; `Protocol/AssetBridgePreparation` `RegistryCorrespondence`,
    `Reinitialization`, `Resolution`, `ResolutionEvidence`, `FullRecovery`;
    `Examples/BurnMintBridge` `EndBranch`.
  - `Codegen/Calls.lean` (single module) and `Codegen/VaultPreparationSlice/`, which
    transcribes the vault's registered bridged-token `bridgeBurn` branch.
* At `feat/upgrade-simplification` commit `e561b9cc2`:
  - `ChainTypeManager`: `DiamondStorage`, `LiveRouting`, `DuplicateSelectorScan`,
    `DuplicateSelectorCheck`, `Enabledness`, `ChainLocal`, `ChainLocalExecutor`,
    `UpgradeTiming`, `ExecutorRowsUnvalidated`, `ExecutorUpgradeChain`, `GenesisWriters`.
  - `ProxyUpgradeRowLib` `RowsUnvalidated`, which reuses the `RowsCurrent` model at
    that commit unchanged.
  - `RegistryBootstrapMigration` `Forward`, citing the OpenZeppelin v4.9 submodules
    that commit pins (`2d081f2`, `dc44c9f`).
* At era-contracts `main` commit `3605e82`:
  - `L2InteropCommitmentTree` `PaddingAtHead`: the tree with the padding constant
    `IMT_EMPTY_LEAF_HASH` (`common/Config.sol:87-90`,
    `common/libraries/IndexedMerkleTree.sol`, `Merkle.sol`, `FullMerkle.sol`,
    `atomic-interop/L2InteropCommitmentTree.sol`). The five files are byte-identical at
    `main` `70096e2`. On draft/v0.35.0 (`d9f6789` and `b17415d20`) the three library
    files are byte-identical, the constant is the same declaration (`Config.sol:138-141`),
    and the contract differs only in its error imports. `Merkle.sol` and `FullMerkle.sol`
    are byte-identical to `c67894b9`.
* At `draft/v0.35.0` commit `b17415d20` (first written against `d9f678900`; every Solidity
  file it cites is the same at both commits, and the cited lines of
  `protocol-docs/interop-gating.md` are `b17415d20`'s):
  - `Protocol/InteropAtomicity` `LegSourceFilterAtV35`: the receive filter
    `_checkLegSourceAllowed` and the `L2Bridgehub.isPeerAllowed` writers, added to the
    pin's `FlowBinding` and `OncePerLeg` models. Only the filter is taken from that
    commit; the tree, proof checks and manager stay the pin's models.
* At era-contracts `main` commit `3605e82` (a moving branch, outside the source pin):
  - `AtomicFlowManager` `FlowCanonicalAtHead`; `Protocol/InteropAtomicity`
    `FlowBindingAtHead`. Both sit next to the pin models, which are unchanged, and cite
    `atomic-interop/AtomicFlowManager.sol`, `atomic-interop/IAtomicInterop.sol`,
    `atomic-interop/L2InteropCommitmentTree.sol`,
    `atomic-interop/libraries/AtomicInteropProof.sol`,
    `common/libraries/IndexedMerkleTree.sol`, `interop/InteropCenter.sol` and
    `interop/interop-handler/L2InteropHandler.sol` at that commit. `main` at `70096e2`
    changes nothing under `l1-contracts/contracts` since `3605e82`.
  - `FlowBindingAtHead`'s `RunAtV35` and the "Other heads" section of
    `FlowCanonicalAtHead` cite `draft/v0.35.0` at `b17415d20` (`AtomicFlowManager.sol`,
    `L2InteropHandler.sol`, `InteropCenter.sol`, `core/bridgehub/L2Bridgehub.sol`);
    `d9f6789` has the same text in the `atomic-interop/` and `interop/` files.
* At `draft/v0.35.0` commit `b17415d20` (`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`,
  2026-11-16; contains #2654, `95b5c469d`, and #2669, `9775be946`):
  - `ChainTypeManager` `ExecutorEngineAtV35`: `applyInfrastructureUpgrade` through
    `ProxyUpgradeExecutorBase` and `DefaultProxyUpgradeEngine`. First written at `d9f6789`
    (2026-11-06) and re-read at `b17415d20`; its Specs header lists what changed between the
    two. It reuses the `e561b9cc2` models `ExecutorForward` and `RowsCurrent`; of those, only
    the function bodies its header names were re-read at `b17415d20`.

Source findings from this work are listed in [REVIEW.md](REVIEW.md); they are reported
to the maintainer of this repo, not yet confirmed upstream.

## Implementation correspondence remains open

The abstract proofs establish properties of the definitions and assumptions in
this repository. They do not establish that Solidity source or deployed bytecode
implements those definitions. Connecting each relevant source path, including
success and failure behavior, to these models is a separate open work item. The
older repository's compiled proofs are not imported, depended upon, or claimed as
supplying that correspondence.

## Pinned source context

* Lean `v4.35.0` (`lean-toolchain`); Mathlib `v4.35.0`, locked at
  `56a005855ea17e0b0958f73ec801ae140b0a1679` in `lake-manifest.json`. Commit `9f9ab8f`
  ported the package from Lean `v4.9.1` / Mathlib
  `09d33efc68d3ad52db77b731d7253675395a14aa`; only `EraSpec/Core/Word.lean` changed
  (`Fin.ofNat` takes the modulus explicitly, and the `Fin` ring instance is registered
  globally as the older build had it).
* Source context for the original extraction: era-contracts commit
  `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`. Contract-specific models were
  reviewed against the Solidity files at that source pin, including
  `contracts/common/libraries/IndexedMerkleTree.sol`,
  `contracts/atomic-interop/L2InteropCommitmentTree.sol`,
  `contracts/atomic-interop/AtomicFlowManager.sol`, and
  `contracts/atomic-interop/libraries/AtomicInteropProof.sol`.
* `EraSpec/Contracts/NativeTokenVaultBase/*/RegistryAndEscrow.lean` and
  `EraSpec/Contracts/AssetRouterBase/*/HandlerRegistration.lean` were authored in
  this repository's earlier flat layout (branch `claude/proof-attempt-4f3778`) and
  ported to the per-contract layout. Their quotations match
  `contracts/bridge/ntv/NativeTokenVaultBase.sol`,
  `contracts/bridge/ntv/L1NativeTokenVault.sol`,
  `contracts/bridge/asset-router/AssetRouterBase.sol` and the encodings in
  `contracts/common/libraries/DataEncoding.sol` (`encodeNTVAssetId`,
  `encodeAssetId`, `assetIdCheck`) at the pin above. Re-read all four when the pin
  moves. Each models one writer of its mappings; other writers exist at the pin (see
  the two READMEs).
* `EraSpec/Contracts/ProxyUpgradeRowLib/` is **outside** that pin. It models
  `l1-contracts/contracts/upgrades/registry/libraries/ProxyUpgradeRowLib.sol` on
  branch `feat/upgrade-simplification` of the zksync-era `contracts` repository
  (formerly `claude/musing-clarke-8b5f2c`). The branch moves. The model's header and
  commit cite no source commit. The library was found unchanged at
  `612a71cccb65d6db97674997b21427a50bec6206` (last library change `ae0698588`), so
  treat the model as a snapshot at that commit. The library has changed since; see
  that contract's README. `Specs/RowsCurrent.lean` and `Specs/RowsUnvalidated.lean` model the
  library at `e561b9cc2` instead.
* `EraSpec/Contracts/ChainTypeManager/` models the CTM's version/transition registry and
  chain facet routing on the same branch, pinned at commit `e561b9cc2` (read-only);
  sources are under `l1-contracts/contracts/upgrades/registry/` and the
  `ChainTypeManager`, `Admin`, `DefaultUpgrade`, `BootstrapUpgrade` and `DiamondInit`
  contracts. Specs docstrings quote the transcribed guards with file:line at that commit.
  `Specs/MutableSelectors.lean` is the exception: it cites era-contracts commit
  `b17415d2068065a4a3e3f0e7a14a2e96f54212e5` (branch `draft/v0.35.0`), and its header says
  where the code it reuses from the other topics sits at that commit.
* `EraSpec/Contracts/RegistryBootstrapMigration/` (bootstrap authority) is pinned at
  `e561b9cc2` too. `EraSpec/Contracts/EcosystemUpgradeExecutor/` (the coordinator and
  its timer) is pinned at **`afa407085`**, because the coordinator and
  `GovernanceUpgradeTimer` were deleted from the branch before `e561b9cc2`
  (`f64622022d`, `469310c94e`); it describes a design that no longer exists at the
  newer pin.
* `EraSpec/Protocol/InteropAtomicity/Specs/RootImport.lean` models the destination gate at
  `c67894b9`. Its cross-pin paragraph also cites era-contracts commits
  `3605e82dbdca5b60bd7bc6bde14ebb52a6b09b73` (branch `main`, label `head-main-3605e82`)
  and `d9f678900e1bc8286412b78f56d4a9f443983c29` (branch `draft/v0.35.0`, label
  `head-v35-d9f6789`), with `e561b9cc2` (label `upgrade-e561b9cc2`), to record what
  changes at those commits. The model itself stays pinned at `c67894b9`.
* Three topics model the current heads instead of `c67894b9`: era-contracts
  `70096e2ea6eeb5373992e178064c4b26dcf6436a` (branch `main`, label `head-main-70096e2`) and
  `b17415d2068065a4a3e3f0e7a14a2e96f54212e5` (branch `draft/v0.35.0`, label
  `head-v35-b17415d`). They are `L2InteropCommitmentTree` `HintSearchAtHead`,
  `Protocol/InteropAtomicity` `OncePerLegAtHead` and `NativeTokenVaultBase`
  `EscrowLedgerAtHead`. They were first written against `3605e82` and `d9f6789`; every
  Solidity file they cite is unchanged between those commits and the heads above, on each
  branch. Line numbers are `main`'s unless a spec marks them as `draft/v0.35.0`'s, and
  `protocol-docs/bridging.md` is cited at `main`.

These pins describe reproducibility and historical source context. They do not
imply current Solidity correspondence; that must be established independently.
