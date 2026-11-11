import EraSpec.Protocol.InteropAtomicity.Specs.Refund

/-!
# Model: the honest timeout proof, and a hash under which none can be forged

`Contracts.Refund` (`Specs/Refund.lean`) and `Contracts.Timeout` (`Specs/Timeout.lean`)
state the refund side's SAFETY: a refund needs a verified timeout, and a verified
timeout means the leg missed its deadline (or a located break).  Nothing there says the
timeout gate can ever be passed.  `Properties.TimeoutProofRefundsCommittedLeg` takes
`RefundAuthorized` as a premise, so every refund-side safety result would stay true of a
gate that never fires.  This file adds the definitions the completeness statements of
`EraSpec.Protocol.InteropAtomicity.Properties.RefundStrong` are stated with.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.RefundStrong`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.RefundStrong`.

## The honest timeout proof

`verifyTimeoutAbsence`'s BEGIN branch checks an IMT non-inclusion proof against the tree
as a late batch began (`IMT_BEGIN_ROOT_LEAF_INDEX`).  The proof an honest prover builds
is the low leaf of the commit value together with `FullMerkle.merklePath` for it:
`honestBeginProof`.  Because `begin(N + 1) = end(N)`, for a late batch `N + 1` it is the
same object as `Contracts.Atomicity.honestProof … c N i`, the proof built from batch
`N`'s published data.  So the data-availability assumption `DataAvailable` covers it.
The BEGIN root of batch `0` is the genesis tree `setup`, which needs no chain data.

## A hash with no forgery against one root

The anti-vacuity witnesses for the executed-obligation milestone need a world in which
the executed obligation is live (`Committed`, so `authorizeRefund`'s per-leg guard is
open) and still no `authorizeRefund` call can pass for it.  Under an arbitrary node hash
that cannot be shown: a hash with enough collisions accepts a forged absence proof
against any root.  `sealedNodeHash` and `sealedLeafHash` are a deliberately simple pair
under which the root of the one-commit tree `insert setup 1 0` (the tree of
`Contracts.Atomicity.mixedSystem 1`'s chain `0`) has exactly one preimage and no leaf
hash is a node hash.  They are not a model of keccak: they exist so that "no forged
proof is accepted against this root" is a theorem
(`Contracts.Refund.sealed_absence_rejected`).
-/

namespace Contracts.Refund

open MerkleSpec MerkleSpec.Verifier IMTAbstract Contracts.InteropCommitmentTree
open Contracts.Atomicity

/-- The proof `FullMerkle.merklePath` yields for leaf `i` of chain `c`'s tree as batch
`N` BEGAN: the leaf, its index, and the honest sibling stream at that tree's height.  For
`N = n + 1` it is `Contracts.Atomicity.honestProof h z0 hl S c n i` (by `rfl`). -/
def honestBeginProof (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : System) (c : Chain)
    (N i : ℕ) : ImtProof :=
  ⟨(beginTree S c N).leaf i, i, honestSibs h z0 (leafHashes hl (beginTree S c N)) i,
    beginHeight S c N⟩

/-- **THE LEG MISSED ITS DEADLINE.**  Its commit value is absent from its declared source
chain's tree at every batch that settled by the deadline.  This is the conclusion of
`Contracts.Timeout.Properties.TimeoutMeansMissedDeadlineOrBreak`, named so that its
converse can be stated. -/
def LegMissedDeadline (cv : CommitValue) (S : System) (F : Flow) (leg : FlowLeg) : Prop :=
  ∀ n, S.time leg.chain n ≤ F.deadline → legValue cv F leg ∉ keys (toAbs (S.tree leg.chain n))

/-- A node hash under which `sealedNodeHash 2 4 = 1` and every other pair hashes to `3`.
Paired with `sealedLeafHash`, the root `1` of `insert setup 1 0` at height 1 has the single
preimage `(2, 4)`, the hashes of that tree's two leaves.  Not a model of keccak. -/
def sealedNodeHash : Hash := fun a b => if a = 2 ∧ b = 4 then 1 else 3

/-- The leaf hash paired with `sealedNodeHash`: the two leaves `⟨0, 1, 1⟩` and
`⟨1, 0, 0⟩` of `insert setup 1 0` hash to `2` and `4`, every other leaf to `6`.  No value of
it is a value of `sealedNodeHash`. -/
def sealedLeafHash : LeafHash := fun ℓ =>
  if ℓ = ⟨0, 1, 1⟩ then 2 else if ℓ = ⟨1, 0, 0⟩ then 4 else 6

end Contracts.Refund
