import EraSpec.Contracts.IndexedMerkleTree.Specs.Model
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.Model

/-!
# Multi-chain refund gate: definitions

The state and gate predicates for the multi-chain model of `authorizeRefund`'s
source-chain check.  The narrative (the attack, and why the comparison

    if (_absence.sourceChainId != _flow.legSourceChainIds[_missingLegIndex]) revert;

is load-bearing) is in `EraSpec.Protocol.MultichainGate.Properties.Model`; the
proofs are in `EraSpec.Protocol.MultichainGate.Proofs.Model`.

Formerly `EraSpec/Protocol/Spec.lean`; that module now only re-exports the
proofs module, so existing imports keep working.
-/

namespace Contracts.Protocol

open IMTAbstract

/-- Chain ids, as `uint256`. -/
abbrev Chain := UInt256

/-- The multi-chain state: every chain's commitment tree, viewed abstractly.

One `Finset AbsLeaf` per chain.  The indexed layer
(`Contracts.InteropCommitmentTree.Tree`) is what each chain actually stores;
`ofChains` below projects a family of those into this model. -/
structure Protocol where
  trees : Chain → Finset AbsLeaf

/-- Every chain's tree is well-formed. -/
def AllSound (P : Protocol) : Prop := ∀ c, SoundState (P.trees c)

/-- The leg with commit value `v`, whose declared source chain is `src`, was
delivered: its value is a key of the declared source chain's tree.  Only that
chain's tree is consulted; the predicate says nothing about other chains. -/
def Delivered (P : Protocol) (src : Chain) (v : UInt256) : Prop :=
  v ∈ keys (P.trees src)

/-- A valid non-inclusion witness for `v` against chain `c`'s tree: a leaf whose
window straddles `v`.  This is what `IndexedMerkleTree.verifyNonInclusion`
accepts (modulo the Merkle path, which authenticates the leaf as belonging to
`c`'s tree — see `EraSpec.Contracts.FullMerkle.Proofs.Model`). -/
def AbsenceWitnessAt (P : Protocol) (c : Chain) (v : UInt256) : Prop :=
  ∃ W ∈ P.trees c, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **The gate WITHOUT the source-chain check**: accepts an absence witness from
whatever chain the prover names. -/
def UnboundGate (P : Protocol) (v : UInt256) : Prop :=
  ∃ c, AbsenceWitnessAt P c v

/-- **The gate WITH the source-chain check**: the witness must come from the
leg's declared source chain, as `authorizeRefund` requires. -/
def BoundGate (P : Protocol) (src : Chain) (v : UInt256) : Prop :=
  AbsenceWitnessAt P src v

/-- The attack configuration: `v` delivered on chain `0` by one guarded insert
from genesis, every other chain still at genesis. -/
def attackProtocol (v : UInt256) : Protocol where
  trees := fun c => if c = 0 then imtInsert ({⟨0, 0⟩} : Finset AbsLeaf) ⟨0, 0⟩ v
                    else ({⟨0, 0⟩} : Finset AbsLeaf)

open Contracts.InteropCommitmentTree in
/-- The `Protocol` view of a family of per-chain commitment-tree contract states:
each chain's tree is the `toAbs` projection of that chain's state. -/
def ofChains (T : Chain → Tree) : Protocol where
  trees := fun c => toAbs (T c)

/-- The attack configuration at the CONTRACT level: chain `0` has run `setup`
then `insert(v, 0)` (through the sentinel), every other chain has only run
`setup`.  Used to realize the countermodel by actual contract states rather than
by an abstract leaf set. -/
def attackChains (v : UInt256) : Chain → Contracts.InteropCommitmentTree.Tree :=
  fun c => if c = 0 then Contracts.InteropCommitmentTree.insert
                           Contracts.InteropCommitmentTree.setup v 0
           else Contracts.InteropCommitmentTree.setup

end Contracts.Protocol
