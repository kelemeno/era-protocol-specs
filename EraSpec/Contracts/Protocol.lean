import EraSpec.Core.IMT
import EraSpec.Contracts.InteropCommitmentTree

/-!
# Model: the multi-chain protocol

Atomic interop runs across many chains, each with its own commitment tree.  This
file models that composition and the two versions of the refund gate — with and
without `authorizeRefund`'s source-chain comparison.

**This file is definitions only.**  The results — that the bound gate is safe and
the unbound one is exploitable — are stated in `EraSpec.Properties.Protocol` and
proved in `EraSpec.Proofs.Protocol`.

## The gap this model exists to close

`EraSpec.Core.IMT` proves exclusivity for ONE tree: a delivered commit value has
no reclaim witness *in that tree*.  Nothing in it mentions a chain id.  So a
reader of that layer alone would reasonably conclude that the multi-chain case
had been handled — and it had not.  The concrete repo cannot close it: its proofs
are per-contract, over one deployment's storage, and a cross-chain statement has
nowhere to live there.

## The attack, precisely

`commitValue(flowId, specHash) = keccak(TAG, flowId, specHash)` — note there is
**no chain id in it**.  The value is the same number on every chain.  What makes
it chain-specific is only *where it was inserted*: a leg's `append` runs on its
own source chain, so the value enters that chain's tree and no other.

That is a one-way binding, and it cuts the wrong way for refunds.  Membership
self-binds — a value can only be *found* in the tree it was inserted into.  But
absence does not: the very same number is trivially absent from every *other*
chain's tree, because nothing ever put it there.  So an attacker with a delivered,
finalized leg can point the refund gate at an unrelated chain, prove absence
there truthfully, and collect a refund on a leg that was already delivered — a
double spend.

The only thing standing between the protocol and that attack is one comparison in
`authorizeRefund`:

    if (_absence.sourceChainId != _flow.legSourceChainIds[_missingLegIndex]) revert;

`BoundGate` is the gate with that comparison; `UnboundGate` is the gate without.
-/

namespace Contracts.Protocol

open IMTAbstract

/-- Chain ids, as `uint256`. -/
abbrev Chain := UInt256

/-- The multi-chain state: every chain's commitment tree, viewed abstractly.

One `Finset AbsLeaf` per chain.  The indexed layer
(`Contracts.InteropCommitmentTree.Tree`) is what each chain actually stores;
`toAbs` projects to this, and `ofChains` below lifts a family of real contract
states into this model. -/
structure Protocol where
  trees : Chain → Finset AbsLeaf

/-- Every chain's tree is well-formed. -/
def AllSound (P : Protocol) : Prop := ∀ c, SoundState (P.trees c)

/-- The leg with commit value `v`, whose declared source chain is `src`, was
delivered: its value is a key of ITS OWN chain's tree.  Membership self-binds, so
this is the only chain where it could be. -/
def Delivered (P : Protocol) (src : Chain) (v : UInt256) : Prop :=
  v ∈ keys (P.trees src)

/-- A valid non-inclusion witness for `v` against chain `c`'s tree: a leaf whose
window straddles `v`.  This is what `IndexedMerkleTree.verifyNonInclusion`
accepts once the Merkle path has authenticated the leaf as belonging to `c`'s
tree — `EraSpec.Contracts.TreeRoot` is where that authentication is modelled. -/
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

/-- The attack configuration: `v` delivered on chain `0`, every other chain still
at genesis.

Chain `0`'s tree is built by an actual guarded insert from genesis, not written
down by hand — so its soundness is inherited rather than asserted, and the
countermodel cannot be dismissed as a malformed state that the real contract
would never reach. -/
def attackProtocol (v : UInt256) : Protocol where
  trees := fun c => if c = 0 then imtInsert ({⟨0, 0⟩} : Finset AbsLeaf) ⟨0, 0⟩ v
                    else ({⟨0, 0⟩} : Finset AbsLeaf)

open Contracts.InteropCommitmentTree in
/-- A family of per-chain contract states, viewed as a `Protocol`. -/
def ofChains (T : Chain → Tree) : Protocol where
  trees := fun c => toAbs (T c)

end Contracts.Protocol
