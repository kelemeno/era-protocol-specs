import EraSpec.Contracts.IndexedMerkleTree.Specs.Model

/-!
# Flow atomicity with one commitment history per source chain: definitions

`EraSpec.Protocol.FlowAtomicity` states its results over ONE history `S` for all legs of a
flow, and its header reads that as the protocol: "the interop roots are published to every
chain, so every chain of the flow verifies its legs against snapshots of the same evolving
key set".  The source keeps one key set per chain (era-contracts `c67894b9`, under
`l1-contracts/contracts/`):

* `AtomicFlowManager.append` inserts a leg's commit value into the committing chain's own
  `L2InteropCommitmentTree` (`atomic-interop/AtomicFlowManager.sol:40`, `:97-99`);
* `requireFlowFinalized` checks each leg's inclusion proof against the leg's declared
  source chain (`:122-129`): `verifyInclusion` authenticates the proof's IMT root as a leaf
  of that chain's batch (`atomic-interop/libraries/AtomicInteropProof.sol:30-37`,
  `:256-290`).

The settlement-layer root aggregates every chain's batch roots; the IMT key sets inside
them are per chain.  `Contracts.Atomicity.System.tree` is already indexed by chain.

This topic restates the `FlowAtomicity` results over one history per chain and shows what
the single-history reading gets wrong on a two-chain flow.  It is pure order theory over
`IMTAbstract`, like `FlowAtomicity`: leaf sets, not proofs.  Whether a prover can present
a leg's evidence (data availability, root import) is not addressed here
(`Contracts.Atomicity` `DataAvailable`; `Contracts.RootImport`).

**Definitions only.**  Statements: `EraSpec.Protocol.FlowAtomicityPerChain.Properties.Model`;
proofs: `EraSpec.Protocol.FlowAtomicityPerChain.Proofs.Model`.
-/

namespace AttackVectors.FlowAtomicityPerChain

open IMTAbstract

/-- A leg of a multi-chain flow: its declared source chain and its commit value. -/
structure ChainLeg where
  chain : UInt256
  value : UInt256

/-- One IMT history per chain: `S c n` is chain `c`'s leaf set at its snapshot `n`.
Snapshot indices are per chain; different chains' batches are not aligned. -/
abbrev ChainHistories := UInt256 → ℕ → Finset AbsLeaf

/-- One insert of `v` through the genesis sentinel at step 0, constant afterwards. -/
def oneInsertHistory (v : UInt256) : ℕ → Finset AbsLeaf :=
  fun m => if m = 0 then ({⟨0, 0⟩} : Finset AbsLeaf) else imtInsert {⟨0, 0⟩} ⟨0, 0⟩ v

/-- Chain `0` inserts `a` and every other chain inserts `b`, each in its first step. -/
def twoChainHistories (a b : UInt256) : ChainHistories :=
  fun c => if c = 0 then oneInsertHistory a else oneInsertHistory b

/-- A two-chain flow: leg `a` from chain `0` and leg `b` from chain `1`. -/
def twoChainFlow (a b : UInt256) : List ChainLeg := [⟨0, a⟩, ⟨1, b⟩]

end AttackVectors.FlowAtomicityPerChain
