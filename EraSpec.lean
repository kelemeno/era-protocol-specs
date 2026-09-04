import EraSpec.Word

-- Core mathematics
import EraSpec.Core.FinBits
import EraSpec.Core.Merkle
import EraSpec.Core.MerkleProofSound
import EraSpec.Core.MerkleCachedInj
import EraSpec.Core.MerkleVerifier
import EraSpec.Core.IMT

-- MODEL: one abstract state machine per deployed contract, definitions only
import EraSpec.Contracts.InteropCommitmentTree
import EraSpec.Contracts.AtomicFlowManager
import EraSpec.Contracts.Protocol
import EraSpec.Contracts.TreeRoot
import EraSpec.Contracts.Atomicity
import EraSpec.Contracts.Refund

-- PROPERTIES: the statements, one `Prop` each, no proofs
import EraSpec.Properties

-- PROOFS: the proofs, and one certificate theorem per property
import EraSpec.Proofs.InteropCommitmentTree
import EraSpec.Proofs.AtomicFlowManager
import EraSpec.Proofs.Protocol
import EraSpec.Proofs.TreeRoot
import EraSpec.Proofs.Atomicity
import EraSpec.Proofs.Refund

-- The obligations that connect this package to the compiled-code proofs
import EraSpec.Refinement

-- Extracted security theorems and attack countermodels (pending migration)
import EraSpec.AttackVectors.AtomicSourceBinding
import EraSpec.AttackVectors.BundleHashEncoding
import EraSpec.AttackVectors.BundleStatusMachine
import EraSpec.AttackVectors.CapacityInvariant
import EraSpec.AttackVectors.DestinationCapstone
import EraSpec.AttackVectors.FlowAtomicity
import EraSpec.AttackVectors.FlowCanonical
import EraSpec.AttackVectors.InsertGuard
import EraSpec.AttackVectors.LastBatchInRoot
import EraSpec.AttackVectors.LocalHonesty
import EraSpec.AttackVectors.NoTheft
import EraSpec.AttackVectors.ProofPolarity
import EraSpec.AttackVectors.RecoveryLimits
import EraSpec.AttackVectors.ResetAndZero
import EraSpec.AttackVectors.RootBinding
import EraSpec.AttackVectors.RootForgery
import EraSpec.AttackVectors.SelfCallAuthority
import EraSpec.AttackVectors.StaleSnapshot
import EraSpec.AttackVectors.TimeoutSoundness
import EraSpec.AttackVectors.Timestamps
import EraSpec.AttackVectors.TreeShape

/-!
# EraSpec — the protocol-level specification of ZKsync Era atomic interop

Importing this module brings in everything.  The layers, bottom-up:

* `EraSpec.Word` — the 256-bit machine word (vendored; see its header).
* `EraSpec.Core.*` — the mathematical objects the protocol is built from: the
  Merkle fold and its verifier, the indexed Merkle tree and its order invariant.
* `EraSpec.Contracts.*` — the MODEL: one abstract state machine per deployed
  contract, plus the multi-chain composition and the hash-tree root.  Definitions
  only.
* `EraSpec.Properties.*` — the STATEMENTS: every guarantee as a `Prop`, no proofs.
  `EraSpec.Properties` is the catalogue and roadmap.
* `EraSpec.Proofs.*` — the PROOFS, each property discharged by a certificate
  theorem of exactly its type.
* `EraSpec.AttackVectors.*` — the extracted security corpus and countermodels.

Nothing here depends on Clear, on solc output, or on any model of the EVM.
-/
