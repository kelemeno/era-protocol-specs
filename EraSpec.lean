import EraSpec.Word

-- Core mathematics
import EraSpec.Core.FinBits
import EraSpec.Core.Merkle
import EraSpec.Core.MerkleProofSound
import EraSpec.Core.MerkleCachedInj
import EraSpec.Core.IMT

-- Contract state machines (one per deployed contract) and their composition
import EraSpec.Contracts.InteropCommitmentTree
import EraSpec.Contracts.AtomicFlowManager
import EraSpec.Contracts.Protocol

-- The obligations that connect this package to the compiled-code proofs
import EraSpec.Refinement

-- Security properties and attack countermodels
import EraSpec.Properties.AtomicSourceBinding
import EraSpec.Properties.BundleHashEncoding
import EraSpec.Properties.BundleStatusMachine
import EraSpec.Properties.CapacityInvariant
import EraSpec.Properties.DestinationCapstone
import EraSpec.Properties.FlowAtomicity
import EraSpec.Properties.FlowCanonical
import EraSpec.Properties.InsertGuard
import EraSpec.Properties.LastBatchInRoot
import EraSpec.Properties.LocalHonesty
import EraSpec.Properties.NoTheft
import EraSpec.Properties.ProofPolarity
import EraSpec.Properties.RecoveryLimits
import EraSpec.Properties.ResetAndZero
import EraSpec.Properties.RootBinding
import EraSpec.Properties.RootForgery
import EraSpec.Properties.SelfCallAuthority
import EraSpec.Properties.StaleSnapshot
import EraSpec.Properties.TimeoutSoundness
import EraSpec.Properties.Timestamps
import EraSpec.Properties.TreeShape

/-!
# EraSpec — the protocol-level specification of ZKsync Era atomic interop

Importing this module brings in everything.  The layers, bottom-up:

* `EraSpec.Word` — the 256-bit machine word (vendored; see its header).
* `EraSpec.Core.*` — the mathematical objects the protocol is built from: the
  Merkle fold, the indexed Merkle tree and its order invariant, bit arithmetic.
* `EraSpec.Contracts.*` — one abstract state machine per deployed contract, plus
  the multi-chain composition.  These are the specifications that
  `contracts-formal-verification` refines its compiled-code proofs against.
* `EraSpec.Properties.*` — the security theorems and the attack countermodels.

Nothing here depends on Clear, on solc output, or on any model of the EVM.
-/
