-- Foundations with no corresponding Solidity contract or library
import EraSpec.Core.Word
import EraSpec.Core.FinBits
import EraSpec.Core.PreparedApplication
import EraSpec.Core.Simulation

-- Asset bridge: locally specified initialized representation-token ledger
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Model
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Initialization
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Initialization
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RepresentationPreparation
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.PreparationGuards

-- Asset bridge: the vault's registry and escrow ledger, and the router's handler
-- table (registry-wide models; see the contract READMEs for how they relate)
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistryAndEscrow
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.ModelCorrespondence
import EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistration

-- Registry-driven upgrades: the proxy row state machine (a snapshot of a moving
-- branch outside the pinned era-contracts tree; see PROVENANCE.md), at 612a71ccc and at
-- e561b9cc2
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.Rows
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrent

-- Registry-driven upgrades: the CTM's version state, its transition registry, and the facet
-- routing of its chains (a snapshot of a moving branch at e561b9cc2; see the folder README)
import EraSpec.Contracts.ChainTypeManager.Proofs.VersionRegistry
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainRouting
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainMigration
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorForward

-- Registry-driven upgrades: who holds the CTM domain's authority across the bootstrap edge
-- (e561b9cc2), and the staged coordinator with its timer (afa407085; deleted by e561b9cc2)
import EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Authority
import EraSpec.Contracts.EcosystemUpgradeExecutor.Proofs.Lifecycle
import EraSpec.Contracts.EcosystemUpgradeExecutor.Proofs.LifecycleStrong

-- AtomicFlowManager: abstract lifecycle, canonical flows, recovery limits
import EraSpec.Contracts.AtomicFlowManager.Proofs.Model
import EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonical
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimits
import EraSpec.Contracts.AtomicFlowManager.Proofs.ModelStrong
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsStrong

-- AtomicInteropProof: finalization, timeout, source binding, and proof snapshots
import EraSpec.Contracts.AtomicInteropProof.Proofs.TimeoutSoundness
import EraSpec.Contracts.AtomicInteropProof.Proofs.ProofPolarity
import EraSpec.Contracts.AtomicInteropProof.Proofs.ProofPolarityStrong
import EraSpec.Contracts.AtomicInteropProof.Proofs.TimeoutSoundnessStrong
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastBatchInRoot
import EraSpec.Contracts.AtomicInteropProof.Proofs.StaleSnapshot
import EraSpec.Contracts.AtomicInteropProof.Proofs.Timestamps
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeaf

-- IndexedMerkleTree: abstract list model and insertion requirements
import EraSpec.Contracts.IndexedMerkleTree.Proofs.Model
import EraSpec.Contracts.IndexedMerkleTree.Proofs.InsertGuard
import EraSpec.Contracts.IndexedMerkleTree.Proofs.ResetAndZero

-- L2InteropCommitmentTree: the wrapper's indexed state machine, batches, hint search, and root
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Model
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.Reaches
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearch
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight

-- Interop handlers and the bundle encoding library
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachine
import EraSpec.Contracts.InteropHandlerBase.Proofs.SelfCallAuthority
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineFaithful
import EraSpec.Contracts.InteropHandlerBase.Proofs.SelfCallAuthorityFaithful
import EraSpec.Contracts.InteropHandlerBase.Proofs.ValueLedgerFaithful
import EraSpec.Contracts.L2InteropHandler.Proofs.AtomicSourceBinding
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashEncoding

-- Solidity Merkle libraries: capacity, padding, root authentication, and the verifier
import EraSpec.Contracts.FullMerkle.Proofs.Model
import EraSpec.Contracts.FullMerkle.Proofs.CachedHashInjectivity
import EraSpec.Contracts.FullMerkle.Proofs.CapacityInvariant
import EraSpec.Contracts.FullMerkle.Proofs.TreeShape
import EraSpec.Contracts.Merkle.Proofs.ProofSound
import EraSpec.Contracts.Merkle.Proofs.RootBinding
import EraSpec.Contracts.Merkle.Proofs.RootForgery
import EraSpec.Contracts.Merkle.Proofs.Verifier
import EraSpec.Contracts.Merkle.Proofs.PathCollision

-- Guarantees that compose several contracts or source chains
import EraSpec.Protocol.Spec
import EraSpec.Protocol.MultichainGate.Proofs.Model
import EraSpec.Protocol.LocalHonesty
import EraSpec.Protocol.NoTheft
import EraSpec.Protocol.FlowAtomicity
import EraSpec.Protocol.DestinationCapstone
import EraSpec.Protocol.InteropAtomicity.Proofs.Atomicity
import EraSpec.Protocol.InteropAtomicity.Proofs.Timeout
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund
import EraSpec.Protocol.InteropAtomicity.Proofs.SourceHeight
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Model
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Initialization

-- Lean-to-Solidity generation: a restricted contract language, its emitter, and
-- the bridged-token slice proved to refine the token model (CODE_GENERATION.md)
import EraSpec.Codegen.Lang
import EraSpec.Codegen.Emit
import EraSpec.Codegen.BridgedTokenSlice.Proofs.Refinement
import EraSpec.Codegen.BridgedTokenSlice.Proofs.AtMostOneStep
import EraSpec.Codegen.EmitRefusals.Proofs.BoolLiterals

-- Reference application, distinct from the deployed router/vault implementation
import EraSpec.Examples.BurnMintBridge.Model
import EraSpec.Examples.BurnMintBridge.ProtocolComposition

-- Obligations connecting the abstract models to compiled-code proofs
import EraSpec.Refinement

-- Proof round 5 (Lean 4.35): backlog items B1–B7, A1–A4, U1–U8, R1–R3, S1, S3, O1–O4
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Denotation
import EraSpec.Codegen.VaultPreparationSlice.Proofs.MintDataBytes
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Refinement
import EraSpec.Codegen.VaultPreparationSlice.Proofs.RevertOrder
import EraSpec.Codegen.VaultPreparationSlice.Proofs.Witnesses
import EraSpec.Codegen.VaultPreparationSlice.Proofs.AtMostOneStep
import EraSpec.Contracts.AssetRouterBase.Proofs.AllWriters
import EraSpec.Contracts.AssetRouterBase.Proofs.AllWritersStrong
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery
import EraSpec.Contracts.AssetRouterBase.Proofs.CounterpartGate
import EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistrationRuns
import EraSpec.Contracts.AssetRouterBase.Proofs.VaultMintGate
import EraSpec.Contracts.BridgedStandardERC20.Proofs.LegacyFallback
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Reinitialization
import EraSpec.Contracts.BridgedStandardERC20.Proofs.ModelStrong
import EraSpec.Contracts.BridgedStandardERC20.Proofs.ReinitializationStrong
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocal
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocalExecutor
import EraSpec.Contracts.ChainTypeManager.Proofs.DiamondStorage
import EraSpec.Contracts.ChainTypeManager.Proofs.DuplicateSelectorCheck
import EraSpec.Contracts.ChainTypeManager.Proofs.DuplicateSelectorScan
import EraSpec.Contracts.ChainTypeManager.Proofs.Enabledness
import EraSpec.Contracts.ChainTypeManager.Proofs.EngineGettersFaithful
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorRowsUnvalidated
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorUpgradeChain
import EraSpec.Contracts.ChainTypeManager.Proofs.GenesisWriters
import EraSpec.Contracts.ChainTypeManager.Proofs.LegacyCrossingFaithful
import EraSpec.Contracts.ChainTypeManager.Proofs.LiveRouting
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTiming
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTimingStrong
import EraSpec.Contracts.FullMerkle.Proofs.CachedNodes
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned
import EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CachedRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.InitOnce
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.PublishedRootCommits
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRootStrong
import EraSpec.Contracts.Merkle.Proofs.RootForgeryPinned
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.LegacyFallback
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistrationUnified
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistrationUnifiedStrong
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Reinitialization
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Resolution
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.ResolutionCorrespondence
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsUnvalidated
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsOrder
import EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Forward
import EraSpec.Examples.BurnMintBridge.Proofs.EndBranch
import EraSpec.Protocol.AssetBridgePreparation.Proofs.RegistryCorrespondence
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Reinitialization
import EraSpec.Protocol.InteropAtomicity.Proofs.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg

-- Proof round 5, wave 2: B3, B4, B5, S2, S4, A5
import EraSpec.Contracts.AssetRouterBase.Proofs.PausedRecovery
import EraSpec.Contracts.L2InteropHandler.Proofs.SourceBindingReduced
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Pause
import EraSpec.Protocol.AssetBridgePreparation.Proofs.FullRecovery
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Resolution
import EraSpec.Protocol.AssetBridgePreparation.Proofs.ResolutionEvidence
import EraSpec.Protocol.InteropAtomicity.Proofs.Operational
import EraSpec.Protocol.InteropAtomicity.Proofs.Pause
import EraSpec.Protocol.InteropAtomicity.Proofs.SharedCommitment

-- Strengthened padding-ambiguity and zero-sentinel statements (FullMerkle, Merkle, IndexedMerkleTree)
import EraSpec.Contracts.FullMerkle.Proofs.TreeShapeStrong
import EraSpec.Contracts.Merkle.Proofs.RootForgeryPinnedStrong
import EraSpec.Contracts.IndexedMerkleTree.Proofs.ModelStrong
import EraSpec.Contracts.IndexedMerkleTree.Proofs.ResetAndZeroStrong

-- Strengthened handler statements (InteropHandlerBase, L2InteropHandler)
import EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyStrong
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachineStrong
import EraSpec.Contracts.InteropHandlerBase.Proofs.SelfCallAuthorityStrong
import EraSpec.Contracts.L2InteropHandler.Proofs.AtomicSourceBindingStrong

/-!
# EraSpec — the protocol-level specification of ZKsync Era atomic interop

Importing this module brings in everything, organized for contract-by-contract review:

* `EraSpec.Core.*` — words, arithmetic, preparation, and safety-refinement composition;
  foundations without a corresponding Solidity contract or library.
* `EraSpec.Contracts.<SolidityName>.*` — each contract/library's abstract models,
  property statements, proofs, and attack countermodels together.
* `EraSpec.Protocol.*` — guarantees that compose contracts and source chains.
* `EraSpec.Examples.*` — illustrative models, not verified deployed applications.
* `EraSpec.Refinement` — what compiled-code verification still must supply.

Each contract separates Specs (definitions), Properties (named propositions), and
Proofs (theorems referencing those propositions). Public theorem names are preserved.
The environment audit checks that each property has its complete named proof.
Nothing here depends on Clear, solc output, or EVM semantics.
-/
