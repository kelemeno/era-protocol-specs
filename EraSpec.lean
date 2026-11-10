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
import EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistration

-- Registry-driven upgrades: the proxy row state machine (a snapshot of a moving
-- branch outside the pinned era-contracts tree; see PROVENANCE.md)
import EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.Rows

-- AtomicFlowManager: abstract lifecycle, canonical flows, recovery limits
import EraSpec.Contracts.AtomicFlowManager.Proofs.Model
import EraSpec.Contracts.AtomicFlowManager.Proofs.FlowCanonical
import EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimits

-- AtomicInteropProof: finalization, timeout, source binding, and proof snapshots
import EraSpec.Contracts.AtomicInteropProof.Proofs.TimeoutSoundness
import EraSpec.Contracts.AtomicInteropProof.Proofs.ProofPolarity
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

-- Interop handlers and the bundle encoding library
import EraSpec.Contracts.InteropHandlerBase.Proofs.BundleStatusMachine
import EraSpec.Contracts.InteropHandlerBase.Proofs.SelfCallAuthority
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
import EraSpec.Protocol.LocalHonesty
import EraSpec.Protocol.NoTheft
import EraSpec.Protocol.FlowAtomicity
import EraSpec.Protocol.DestinationCapstone
import EraSpec.Protocol.InteropAtomicity.Proofs.Atomicity
import EraSpec.Protocol.InteropAtomicity.Proofs.Timeout
import EraSpec.Protocol.InteropAtomicity.Proofs.Refund
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Model
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Initialization

-- Lean-to-Solidity generation: a restricted contract language, its emitter, and
-- the bridged-token slice proved to refine the token model (CODE_GENERATION.md)
import EraSpec.Codegen.Lang
import EraSpec.Codegen.Emit
import EraSpec.Codegen.BridgedTokenSlice.Proofs.Refinement

-- Reference application, distinct from the deployed router/vault implementation
import EraSpec.Examples.BurnMintBridge.Model
import EraSpec.Examples.BurnMintBridge.ProtocolComposition

-- Obligations connecting the abstract models to compiled-code proofs
import EraSpec.Refinement

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
