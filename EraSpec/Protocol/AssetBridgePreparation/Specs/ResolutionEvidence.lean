import EraSpec.Protocol.AssetBridgePreparation.Specs.Resolution
import EraSpec.Protocol.InteropAtomicity.Specs.Refund
import EraSpec.Protocol.MultichainGate.Specs.Model

/-!
# The resolution gate, instantiated with the protocol's own evidence

`Specs/Resolution.lean` leaves the cross-chain evidence of a delivery and a refund abstract
(`ResolutionGate`). This file supplies it from two existing protocol models, so the two-chain
results become statements about the deployed gate and refund path.

## The atomic interop gate and refund path (`Protocol/InteropAtomicity`)

* A delivery's witness is the gate evidence submitted to `requireFlowFinalized`
  (`atomic-interop/AtomicFlowManager.sol:105-131`, called at
  `interop/interop-handler/L2InteropHandler.sol:83`): for each leg of the flow, a batch and an
  IMT inclusion proof. The gate passes for entry `i` when the leg carrying it executed through
  the deployed gate on exactly that evidence (`Contracts.Atomicity.ExecutedViaBy`: the leg is one
  of the flow's, the flow id checks, and every leg's proof is accepted on time).
* A refund's witness is a logged run of every chain's manager from fresh storage
  (`Contracts.Refund.ReachLog`, which names every `authorizeRefund` call with its evidence) and
  its end state. It passes for entry `i` when that run lifted the leg's obligation past
  `Committed` (`Contracts.Refund.Refunded`): `claimRefund` requires `Revertable`
  (`AtomicFlowManager.sol:169-170`), and `authorizeRefund` (:134-162) is the only way there.
* The located break is `Contracts.Refund.RefundBreak` on the leg's obligation, relative to the
  executed flow and its gate evidence, over the manager run's own log: a logged call that marked
  the obligation, with a flow-id collision against the executed flow, or a located Merkle break
  on the executed flow's inclusion proof for the call's missing leg, or on the call's own absence
  proof. `Contracts.Refund.ExecutedObligationNeverRefundedOrBreak` is what makes the gate sound
  up to it, with no hash premise.
* `route i` names the flow and the leg that carry entry `i`. Binding a prepared burn to exactly
  one leg is the router's and the interop center's job (`REP-PUBLISH`); here it is a parameter,
  so the results hold for every binding.

The tree side is the fixed multi-chain, multi-batch history `System` of
`Protocol/InteropAtomicity` (`Wf`: every chain starts from `setup`, batches only insert,
settlement times are monotone). Refund witnesses may be any logged manager run, not one
synchronized with the two-chain trace, and the gate evidence may cite any batch: both only add
runs, so the safety results are the stronger claims.

## The multichain refund gate (`Protocol/MultichainGate`)

One snapshot of every chain's commitment tree. A delivery passes for entry `i` when the entry's
commit value is a key of its declared source chain's tree (`Contracts.Protocol.Delivered`); a
refund passes when that same chain's tree has an absence witness for it
(`Contracts.Protocol.BoundGate`): the gate with `authorizeRefund`'s source-chain check
(`AtomicFlowManager.sol:138-145`). `unboundMultichainResolutionGate` drops the check and accepts
an absence witness from any chain (`Contracts.Protocol.UnboundGate`), as the countermodel needs.
`route i` names the declared source chain and the commit value of entry `i`.

**This file is definitions only.** Statements: `../Properties/ResolutionEvidence.lean`; proofs:
`../Proofs/ResolutionEvidence.lean`.
-/

namespace AssetBridgePreparation

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Refund

/-! ## The atomic interop gate and refund path -/

/-- The flow and the leg that carry pending entry `i`. -/
abbrev ResolutionLegRoute := ℕ → Flow × FlowLeg

/-- A source refund's witness under the atomic interop evidence: the managers' state and the log of
the run that reached it. -/
abbrev InteropRefundWitness := Managers × List AuthCall

/-- **THE ATOMIC INTEROP EVIDENCE.** The destination executes entry `i` on gate evidence `ev` when
the leg carrying it executed through the deployed gate on exactly `ev`; the source refunds it on
`(Ms, log)` when the logged manager run `log` from fresh storage reached `Ms` with the leg's
obligation past `Committed`. -/
def interopResolutionGate (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (route : ResolutionLegRoute) :
    ResolutionGate GateEvidence InteropRefundWitness where
  finalize i ev := ExecutedViaBy h z0 hl cv fh S (route i).1 ev (route i).2
  recover i w := ReachLog h z0 hl cv fh S emptyManagers w.1 w.2 ∧
    Refunded w.1 (obligationOf (route i).1 (route i).2)

/-- **THE LOCATED BREAK FOR ENTRY `i`.** `RefundBreak` on the obligation of the leg carrying entry
`i`, relative to that leg's flow and the gate evidence `ev`, over the manager run's own log. -/
def interopResolutionBreak (h : Hash) (z0 : UInt256) (hl : LeafHash) (fh : FlowHash)
    (S : System) (route : ResolutionLegRoute) (i : ℕ) (ev : GateEvidence)
    (w : InteropRefundWitness) : Prop :=
  RefundBreak h z0 hl fh S (route i).1 ev (obligationOf (route i).1 (route i).2) w.2

/-! ## The multichain refund gate -/

/-- The declared source chain and the commit value of pending entry `i`. -/
abbrev ResolutionValueRoute := ℕ → UInt256 × UInt256

/-- **THE MULTICHAIN EVIDENCE, WITH THE SOURCE-CHAIN CHECK.** The destination executes entry `i`
when its commit value is delivered on its declared source chain; the source refunds it when that
chain's tree has an absence witness for it. -/
def multichainResolutionGate (T : UInt256 → Tree) (route : ResolutionValueRoute) :
    ResolutionGate Unit Unit where
  finalize i _ :=
    Contracts.Protocol.Delivered (Contracts.Protocol.ofChains T) (route i).1 (route i).2
  recover i _ :=
    Contracts.Protocol.BoundGate (Contracts.Protocol.ofChains T) (route i).1 (route i).2

/-- **THE MULTICHAIN EVIDENCE WITHOUT THE SOURCE-CHAIN CHECK**: an absence witness from any chain
refunds. -/
def unboundMultichainResolutionGate (T : UInt256 → Tree) (route : ResolutionValueRoute) :
    ResolutionGate Unit Unit where
  finalize i _ :=
    Contracts.Protocol.Delivered (Contracts.Protocol.ofChains T) (route i).1 (route i).2
  recover i _ := Contracts.Protocol.UnboundGate (Contracts.Protocol.ofChains T) (route i).2

end AssetBridgePreparation
