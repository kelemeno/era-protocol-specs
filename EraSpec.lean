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
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsAdminSlot

-- Registry-driven upgrades: the CTM's version state, its transition registry, and the facet
-- routing of its chains (a snapshot of a moving branch at e561b9cc2; see the folder README)
import EraSpec.Contracts.ChainTypeManager.Proofs.VersionRegistry
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainRouting
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainMigration
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorForward
-- applyInfrastructureUpgrade at draft/v0.35.0 (b17415d20): the engine the transition names
import EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorEngineAtV35

-- Registry-driven upgrades: who holds the CTM domain's authority across the bootstrap edge
-- (e561b9cc2), and the staged coordinator with its timer (afa407085; deleted by e561b9cc2)
import EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Authority
import EraSpec.Contracts.EcosystemUpgradeExecutor.Proofs.Lifecycle
import EraSpec.Contracts.EcosystemUpgradeExecutor.Proofs.LifecycleStrong

-- AtomicFlowManager: abstract lifecycle, canonical flows, recovery limits
import EraSpec.Contracts.AtomicFlowManager.Proofs.Model
import EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonical
import EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonicalAtHead
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimits
import EraSpec.Contracts.AtomicFlowManager.Proofs.ModelStrong
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsStrong
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsFaithful
import EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonicalAtV35

-- AtomicInteropProof: finalization, timeout, source binding, and proof snapshots
import EraSpec.Contracts.AtomicInteropProof.Proofs.TimeoutSoundness
import EraSpec.Contracts.AtomicInteropProof.Proofs.ProofPolarity
import EraSpec.Contracts.AtomicInteropProof.Proofs.ProofPolarityStrong
import EraSpec.Contracts.AtomicInteropProof.Proofs.TimeoutSoundnessStrong
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastBatchInRoot
import EraSpec.Contracts.AtomicInteropProof.Proofs.StaleSnapshot
import EraSpec.Contracts.AtomicInteropProof.Proofs.Timestamps
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeaf
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastBatchInRootOffset
import EraSpec.Contracts.AtomicInteropProof.Proofs.LastLeafFaithful
import EraSpec.Contracts.AtomicInteropProof.Proofs.ProofPolarityFaithful
import EraSpec.Contracts.AtomicInteropProof.Proofs.StaleSnapshotBranches
import EraSpec.Contracts.AtomicInteropProof.Proofs.StaleSnapshotFaithful
import EraSpec.Contracts.AtomicInteropProof.Proofs.AuthenticateRootAtV35

-- IndexedMerkleTree: abstract list model and insertion requirements
import EraSpec.Contracts.IndexedMerkleTree.Proofs.Model
import EraSpec.Contracts.IndexedMerkleTree.Proofs.InsertGuard
import EraSpec.Contracts.IndexedMerkleTree.Proofs.ResetAndZero
import EraSpec.Contracts.IndexedMerkleTree.Proofs.ReclaimGateFaithful

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
import EraSpec.Contracts.L2InteropHandler.Proofs.AtomicSourceBindingFaithful
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
import EraSpec.Contracts.Merkle.Proofs.DomainSeparation

-- L2 log leaves and the L1 status proof (MessageHashing, MessageVerification; v0.35.0 b17415d20)
import EraSpec.Contracts.MessageHashing.Proofs.LogLeafSeparation
import EraSpec.Contracts.MessageVerification.Proofs.StatusProof
import EraSpec.Contracts.MessageVerification.Proofs.StatusProofKeccak

-- DynamicIncrementalMerkle: the storage push tree (MessageRoot chain trees, priority tree), its
-- memory copy, and the chain trees as the backing of the timeout path's last-batch check
import EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.Model
import EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.MemoryLazy
import EraSpec.Contracts.DynamicIncrementalMerkle.Proofs.ChainTreeBacking

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
import EraSpec.Protocol.InteropAtomicity.Proofs.BatchPosition
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
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecoveryFaithful
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecoveryAtHead
import EraSpec.Contracts.AssetRouterBase.Proofs.CounterpartGate
import EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistrationRuns
import EraSpec.Contracts.AssetRouterBase.Proofs.VaultMintGate
import EraSpec.Contracts.BridgedStandardERC20.Proofs.LegacyFallback
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Reinitialization
import EraSpec.Contracts.BridgedStandardERC20.Proofs.ModelStrong
import EraSpec.Contracts.BridgedStandardERC20.Proofs.ReinitializationStrong
import EraSpec.Contracts.BridgedStandardERC20.Proofs.ReinitializationFaithful
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocal
import EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocalExecutor
import EraSpec.Contracts.ChainTypeManager.Proofs.CommittedEdgeExecutable
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
import EraSpec.Contracts.ChainTypeManager.Proofs.MutableSelectors
import EraSpec.Contracts.ChainTypeManager.Proofs.ProofGateAtV35
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTiming
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTimingAtV35
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTimingStrong
import EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTxNonces
import EraSpec.Contracts.ChainTypeManager.Proofs.PendingL2UpgradeAtV35
import EraSpec.Contracts.FullMerkle.Proofs.CachedNodes
import EraSpec.Contracts.InteropCenter.Proofs.Dispatch
import EraSpec.Contracts.InteropCenter.Proofs.FeeState
import EraSpec.Contracts.InteropCenter.Proofs.FeeReentry
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashPinned
import EraSpec.Contracts.InteropDataEncoding.Proofs.BundleHashAtV35
import EraSpec.Contracts.InteropHandlerBase.Proofs.Reentrancy
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CachedRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.InitOnce
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.PublishedRootCommits
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRootStrong
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.PaddingAtHead
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
import EraSpec.Examples.BurnMintBridge.Proofs.EndBranchStrong
import EraSpec.Protocol.AssetBridgePreparation.Proofs.RegistryCorrespondence
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Reinitialization
import EraSpec.Protocol.InteropAtomicity.Proofs.FlowBinding
import EraSpec.Protocol.InteropAtomicity.Proofs.FlowBindingAtHead
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLeg
import EraSpec.Protocol.InteropAtomicity.Proofs.RootImport

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
import EraSpec.Protocol.InteropAtomicity.Proofs.RefundStrong

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

-- Strengthened row-application liveness and parked-CTM exits (ProxyUpgradeRowLib, RegistryBootstrapMigration)
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsStrong
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrentStrong
import EraSpec.Contracts.RegistryBootstrapMigration.Proofs.AuthorityStrong

-- L1NativeTokenVault at draft/v0.35.0 (b17415d20): the per-chain ledger, the interop pool and
-- the interop flags (N-2)
import EraSpec.Contracts.L1NativeTokenVault.Proofs.InteropPool

-- L1NativeTokenVault at draft/v0.35.0 (b17415d20): what one chain can release under the
-- per-chain cap, the escrow ledger identity, and the bulkhead model's calls as InteropPool calls (N-3)
import EraSpec.Contracts.L1NativeTokenVault.Proofs.BulkheadIsolation
import EraSpec.Contracts.L1NativeTokenVault.Proofs.BulkheadPoolSimulation

-- Range proofs of the priority queue (b17415d20): `Merkle.calculateRootPaths` and
-- `PriorityTree.processBatch` (N-8)
import EraSpec.Contracts.Merkle.Proofs.RootPaths
import EraSpec.Contracts.PriorityTree.Proofs.SegmentBinding

-- L2 implementation tables of registry transitions (ChainTypeManager, pin b17415d20)
import EraSpec.Contracts.ChainTypeManager.Proofs.L2Derivation
import EraSpec.Contracts.ChainTypeManager.Proofs.L2Convergence

-- Data availability on ZKsync OS at v35 b17415d20: the ZKsync OS blobs validator, and what each
-- DA validator still guarantees once the committer discards its output
import EraSpec.Contracts.BlobsL1DAValidatorZKsyncOS.Proofs.Model
import EraSpec.Protocol.ZKsyncOSDA.Proofs.CommitterDA

-- Faithfulness repairs (protocol): `authorizeRefund` on the calling chain with its END branch as
-- run, the source-bound refund gate over the deployed absence verifier, per-chain flow histories
import EraSpec.Protocol.InteropAtomicity.Proofs.RefundFaithful
import EraSpec.Protocol.MultichainGate.Proofs.DeployedGate
import EraSpec.Protocol.FlowAtomicityPerChain.Proofs.Model

-- AtomicFlowManager at draft/v0.35.0 b17415d20: an authorized refund closes `append` for its flow
import EraSpec.Contracts.AtomicFlowManager.Proofs.RefundClosesAppend

-- L2 bridge configuration words across genesis and default upgrades (v0.35 head b17415d20)
import EraSpec.Protocol.L2BridgeConfig.Proofs.Consistency

-- The receive filter `_checkLegSourceAllowed` of era-contracts draft/v0.35.0 (b17415d20; the
-- cited Solidity is unchanged since d9f678900), on the pin's interop model
import EraSpec.Protocol.InteropAtomicity.Proofs.LegSourceFilterAtV35

-- ChainAdminOwnable at b17415d20: who drives its calls, what a renounce leaves, and the diamond
-- and Bridgehub admin roles it holds (backlog N-14)
import EraSpec.Contracts.ChainAdminOwnable.Proofs.Authority
import EraSpec.Contracts.ChainAdminOwnable.Proofs.AdminRoles

-- ChainBatchRootTree (pin b17415d20): the height-3 chain batch root, genesis seeding, and
-- confinement of L2-log proofs to leaf 0
import EraSpec.Contracts.ChainBatchRootTree.Proofs.Layout
import EraSpec.Contracts.ChainBatchRootTree.Proofs.GenesisSeed
import EraSpec.Contracts.ChainBatchRootTree.Proofs.LogConfinement

-- Head-pinned send path: InteropCenter at main 3605e82 (= 70096e2ea) and draft/v0.35.0 b17415d20
import EraSpec.Contracts.InteropCenter.Proofs.SendAtHead

-- Mailbox request paths and the privileged L2 senders (draft/v0.35.0 at b17415d20)
import EraSpec.Contracts.MailboxFacet.Proofs.RequestPaths
import EraSpec.Protocol.PriorityRequests.Proofs.PrivilegedSenders

-- Proxy-upgrade executor legs at draft/v0.35.0 (ProxyUpgradeExecutorBase)
import EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.CoreLegV35

-- Head re-models of pin topics (main 70096e2, draft/v0.35.0 b17415d): the unbounded IMT walk,
-- once per leg over it, and the vault escrow ledger with populateBridgedOut
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearchAtHead
import EraSpec.Protocol.InteropAtomicity.Proofs.OncePerLegAtHead
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.EscrowLedgerAtHead

-- Registry-driven upgrades at draft/v0.35.0 b17415d (d9f6789 kept for comparison): the
-- domain-holder check around a proxy-upgrade engine leg (ProxyUpgradeExecutorBase)
import EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.DomainHoldersV35

-- Second proof system (draft/v0.35.0 at b17415d20): one diamond's requirement flag and ZiSK
-- switch, and who may move them
import EraSpec.Contracts.SecondProofSystem.Proofs.FlagAuthorityV35

-- Registry-driven upgrades at draft/v0.35.0 (b17415d20): engine legs on the bootstrap's
-- authority state (RegistryBootstrapMigration)
import EraSpec.Contracts.RegistryBootstrapMigration.Proofs.AuthorityEngineV35

-- Engine-leg checks of the proxy upgrade executors at draft/v0.35.0 b17415d20 (ProxyUpgradeExecutorBase)
import EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.EngineLegV35

-- Registry-driven upgrades at draft/v0.35.0 (b17415d20): which CTM executor frames make the
-- CTM's owner calls and what the executor logs, infrastructure legs' engines included
import EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.ExecutorOwnerCallsV35

-- ServerNotifier binding under the CTM executor's engine-leg check (ProxyUpgradeExecutorBase, draft/v0.35.0 b17415d20)
import EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.NotifierBindingV35

-- Re-pinned to draft/v0.35.0 (b17415d20): the unbounded low-leaf walk of `insert`
-- (IndexedMerkleTree, and its lift to the L2InteropCommitmentTree indexed state)
import EraSpec.Contracts.IndexedMerkleTree.Proofs.UnboundedSearchAtV35
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.UnboundedSearchAtV35

-- draft/v0.35.0 (b17415d20) re-model: the commitment tree's transactions on its whole storage
import EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CommitmentTreeAtV35

-- Re-pinned to draft/v0.35.0 (b17415d20)
import EraSpec.Contracts.InteropHandlerBase.Proofs.ReentrancyAtV35

-- draft/v0.35.0 re-pins (b17415d20): the L1 asset router's handler gate
import EraSpec.Contracts.AssetRouterBase.Proofs.HandlerGateAtV35

-- draft/v0.35.0 (b17415d20): the second-proof-system gate on every chain upgrade
import EraSpec.Contracts.SecondProofSystem.Proofs.UpgradeGateV35

-- Recovery targets on the source chain and atomic-attribute routing (AtomicFlowManager, InteropCenter)
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryTargets
import EraSpec.Contracts.InteropCenter.Proofs.AtomicRouting

-- Re-pin to draft/v0.35.0 (b17415d20): the vault preparation slice on L1 with the per-chain
-- balance cap's accounting hook, and the cap's own run model
import EraSpec.Codegen.VaultPreparationSlice.Proofs.L1PerChainCapAtV35

-- Settlement-layer roots (c67894b9): MessageRootBase's historical roots, L2InteropRootStorage's
-- imports, and the timeout and refund headlines against those roots
import EraSpec.Contracts.MessageRoot.Proofs.Aggregation
import EraSpec.Contracts.L2InteropRootStorage.Proofs.Model
import EraSpec.Protocol.InteropAtomicity.Proofs.SettlementRoots

-- L2AssetTracker accounting (pin c67894b9, transferred to b17415d20/70096e2ea), and the vault's
-- deployed chain-balance hooks (L1 `bridgedOut`, L2 tracker)
import EraSpec.Contracts.L2AssetTracker.Proofs.Accounting
import EraSpec.Contracts.L2AssetTracker.Proofs.HookOrdering
import EraSpec.Contracts.L2AssetTracker.Proofs.NativeEscrow
import EraSpec.Contracts.L2AssetTracker.Proofs.LaterHeads
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.TrackerHooks
import EraSpec.Codegen.VaultPreparationSlice.Proofs.L1TrackerHooks

-- DataEncoding (c67894b9): asset ids, the deposit record hash and the burn data at byte level,
-- with the router and vault id results restated in keccak-collision form
import EraSpec.Contracts.DataEncoding.Proofs.AssetId
import EraSpec.Contracts.DataEncoding.Proofs.AssetIdRuns
import EraSpec.Contracts.DataEncoding.Proofs.AssetIdRecovery
import EraSpec.Contracts.DataEncoding.Proofs.TxDataHash
import EraSpec.Contracts.DataEncoding.Proofs.BurnDataSlice

-- Governance: the owner/security-council timelock, with re-entrant execution (draft/v0.35.0, b17415d2)
import EraSpec.Contracts.Governance.Proofs.Timelock

-- What `claimRefund` recovers: a claimed bundle is a dispatched bundle (InteropCenter, on O1's model)
import EraSpec.Contracts.InteropCenter.Proofs.ClaimBinding

-- L1 withdrawal finalization gate at draft/v0.35.0 head b17415d20: the L1 handler, the L2→L1 sender
-- keying it relies on, and their composition
import EraSpec.Contracts.L1InteropHandler.Proofs.WithdrawalGate
import EraSpec.Contracts.L1Messenger.Proofs.SenderKeying
import EraSpec.Protocol.L1WithdrawalProvenance.Proofs.Provenance

-- Interop-peer whitelist mirror and the L2 Bridgehub's baseTokenAssetId entries (b17415d20)
import EraSpec.Protocol.InteropPeerRegistry.Proofs.PeerMirror

-- Liveness of the atomic send path and of an atomic leg's routes on its destination (InteropAtomicity)
import EraSpec.Protocol.InteropAtomicity.Proofs.DispatchLiveness
import EraSpec.Protocol.InteropAtomicity.Proofs.ExecutionLiveness

-- Admin facet (draft/v0.35.0 at b17415d20): access control, admin handover, freezing, priority
-- mode, chain upgrades, fee inputs
import EraSpec.Contracts.AdminFacet.Proofs.Access
import EraSpec.Contracts.AdminFacet.Proofs.PriorityMode
import EraSpec.Contracts.AdminFacet.Proofs.Upgrade
import EraSpec.Contracts.AdminFacet.Proofs.Fees

-- L1Bridgehub at draft/v0.35.0 (b17415d20; cited files identical at d9f6789): the chain
-- registry, settlement-layer bookkeeping and the two request paths
import EraSpec.Contracts.Bridgehub.Proofs.Registry

-- Native-value atomic legs at head b17415d20: collection and refund, and runs
import EraSpec.Protocol.NativeValueLegs.Proofs.LegConservation
import EraSpec.Protocol.NativeValueLegs.Proofs.LegConservationRuns
import EraSpec.Protocol.NativeValueLegs.Proofs.RouterRecoveryFrame

-- Atomic recovery on the L2 asset tracker at v35 (b17415d20)
import EraSpec.Contracts.L2AssetTracker.Proofs.RecoveryNeutrality

-- One chain's priority tree on L1 and on its gateway across a migration out and back (b17415d20),
-- on the PriorityTree model copied from origin/cov/mailbox
import EraSpec.Protocol.PriorityMirror.Proofs.Mirror

-- L1ChainAssetHandler at draft/v0.35.0 (b17415d20): isValidSettlementLayer against the layer that
-- executed each batch, over a run of executions and one migration round trip
import EraSpec.Contracts.L1ChainAssetHandler.Proofs.SettlementLayerValidation

-- The second-proof-system requirement of one chain, its two diamonds, interop enabling and
-- settlement-layer migration (draft/v0.35.0 at b17415d2; see the folder README)
import EraSpec.Contracts.SecondProofSystem.Proofs.MigrationV35

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
