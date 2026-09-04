import EraSpec.Contracts.Atomicity
import EraSpec.Contracts.AtomicFlowManager

/-!
# Model: the refund path, composed

`Contracts.AtomicFlowManager` models the per-leg state machine with no reference to
the tree: its `authorize` step just requires the leg to be `Committed`.  That is
the right level for the no-double-refund results, but it leaves out the guard that
makes a refund *justified* — `authorizeRefund` will not move a leg unless a timeout
absence proof verifies.

This file is the composition: the same state machine with the tree-side guard
attached, so a refund and a delivery are finally statements about one system.

**This file is definitions only.**  The results are in `EraSpec.Properties.Refund`
and proved in `EraSpec.Proofs.Refund`.

## Where the two contracts meet

Exactly one place.  `authorizeRefund` runs
`AtomicInteropProof.verifyTimeoutAbsence` against the missing leg's declared source
chain, and only then loops over the flow's legs on this chain marking the committed
ones `Revertable`:

    uint256 value = AtomicInteropProof.commitValue(_flow.flowId, _flow.legBundleHashes[_missingLegIndex]);
    AtomicInteropProof.verifyTimeoutAbsence(_absence, value, _flow.deadline, _flow.settlementLayerChainId);
    // …then: for each leg of the flow, Committed -> Revertable

`append` and `claimRefund` touch no proof, so their guards are unchanged.

## What the model deliberately does not relate

The manager keys legs by `(flowId, bundleHash)`; the tree holds
`commitValue(flowId, bundleHash)`.  Those are different keyings of the same leg,
related by a keccak hash.  Nothing below needs the relation, because the
conclusion — "some leg of the flow had a verified timeout proof" — quantifies over
the flow's legs existentially.  Tying a manager key to its commit value would need
`commitValue` injectivity, which belongs with the encoding assumptions in
`AttackVectors.BundleHashEncoding`.
-/

namespace Contracts.Refund

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.AtomicFlowManager

/-- **A TIMEOUT PROOF FOR THE FLOW VERIFIED.**  `authorizeRefund` accepted an
absence proof for one of the flow's legs against that leg's declared source chain.

The contract names the leg (`_missingLegIndex`); which one it is does not matter
downstream, so the model quantifies existentially. -/
def RefundAuthorized (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) (F : Flow) : Prop :=
  ∃ leg ∈ F.legs, LegRefundable h z0 hl cv S F leg

/-- One step of a source chain's flow manager, with the tree-side guard.

`Contracts.AtomicFlowManager.Step` with one addition: `authorize` carries a
verified timeout proof.  That single extra hypothesis is what turns the
state-machine results into statements about justified refunds. -/
inductive GuardedStep (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) (F : Flow) : Manager → Manager → Prop
  | append {M f b} : AppendGuard M f b → GuardedStep h z0 hl cv S F M (M.set f b .Committed)
  | authorize {M f b} : AuthorizeGuard M f b → RefundAuthorized h z0 hl cv S F →
      GuardedStep h z0 hl cv S F M (M.set f b .Revertable)
  | claim {M f b} : ClaimGuard M f b → GuardedStep h z0 hl cv S F M (M.set f b .Reverted)

/-- Reachability over any number of guarded steps. -/
inductive GuardedReach (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) (F : Flow) : Manager → Manager → Prop
  | refl {M} : GuardedReach h z0 hl cv S F M M
  | tail {M N P} : GuardedReach h z0 hl cv S F M N → GuardedStep h z0 hl cv S F N P →
      GuardedReach h z0 hl cv S F M P

/-- No leg of this manager has been authorized for refund yet: every leg is
`Unset` or `Committed`.  True of `empty`, and the induction hypothesis of
`Properties.Refund.RefundNeedsTimeoutProof`. -/
def NoRefundYet (M : Manager) : Prop := ∀ f b, rank (M.legState f b) ≤ 1

/-- Some leg of this manager has been authorized for refund (`Revertable`) or
already refunded (`Reverted`). -/
def SomeRefund (M : Manager) : Prop := ∃ f b, 2 ≤ rank (M.legState f b)

end Contracts.Refund
