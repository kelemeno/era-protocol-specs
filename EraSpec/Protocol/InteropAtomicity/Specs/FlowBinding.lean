import EraSpec.Protocol.InteropAtomicity.Specs.Refund

/-!
# Model: every call that checks a flow id, logged

`Contracts.Refund.ReachLog` logs the `authorizeRefund` calls of a run.  This file adds
the other entry point that takes a flow preimage, `requireFlowFinalized`, so that the
log holds EVERY call that runs `_checkFlowId`.  A `flowId` collision can then be pinned
to two calls of the run, instead of to a flow supplied from outside it.

**This file is definitions only.**  Statements are in
`EraSpec.Protocol.InteropAtomicity.Properties.FlowBinding`, proofs in
`EraSpec.Protocol.InteropAtomicity.Proofs.FlowBinding`.

## Where a flow preimage appears on chain

Sources: the pinned era-contracts tree `c67894b9`, under `l1-contracts/contracts/`.

`AtomicFlow` (`atomic-interop/IAtomicInterop.sol:63-79`) is a `flowId` together with
the fields it hashes over.  Exactly two manager entry points take one, and both begin
with `_checkFlowId` (`atomic-interop/AtomicFlowManager.sol:247-259`):

* `requireFlowFinalized(_executingBundleHash, _finality)`
  (`AtomicFlowManager.sol:105-131`), the atomicity gate.
  `L2InteropHandler.executeAtomicBundle`
  (`interop/interop-handler/L2InteropHandler.sol:49-100`) calls it at `:83`, before it
  marks the bundle executed and runs the bundle's calls.  It is `view` and never reads
  `_state`.
* `authorizeRefund(_flow, _missingLegIndex, _absence)` (`AtomicFlowManager.sol:134-162`).

The struct's NatSpec gives the reason for the shared shape: it keeps the two paths on
one struct "so the `flowId` preimage cannot drift between them"
(`IAtomicInterop.sol:63-65`).

No other entry point takes a preimage.  `append` (`AtomicFlowManager.sol:87-102`) and
`claimRefund` (`:165-180`) take a raw `flowId`.  The `InteropCenter` passes `append` the
sender's `flowId` as an opaque attribute, and that `flowId` "must be computable
off-chain before the send" (`interop/InteropCenter.sol:634-656`).  So the flow that
the legs were committed under is not recorded on chain.  The only flows the protocol
ever sees are the ones presented to the two calls above.  That is why "the real flow"
in `Contracts.FlowBinding.Properties.ExecutedImpliesRealFlowFinalizableOrLoggedClash`
is the flow of a logged call.

## What is modelled

`RunLog` is `Contracts.Refund.ReachLog` (append, authorize and claim, on one manager per
chain) with an extra `execute` step.  Its log holds both kinds of call, most recent
first:

* `execute e`: `requireFlowFinalized` accepted the flow `e.flow` on the per-leg evidence
  `e.evidence`, and `e.leg` is the executing bundle's leg (`ExecutedViaBy`).  The step
  changes no manager state.
* `authorize a`: as in `ReachLog`.

These checks are omitted.  All of them can only reject a call:

* the handler's pause check, destination check, execution-address check and
  `bundleStatus == Unreceived` replay guard (`L2InteropHandler.sol:50-79`);
* the settlement-layer check (`AtomicFlowManager.sol:111, 136, 236-240`).

Omitting them admits more executions, never fewer, so a result that excludes an outcome
over `RunLog` is the stronger claim.  As in `ReachLog`, the tree side is the fixed
history `System`, and evidence may cite any batch of it.
-/

namespace Contracts.FlowBinding

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Refund
open Contracts.AtomicFlowManager

/-! ## The calls -/

/-- One `requireFlowFinalized(_executingBundleHash, _finality)` call, as it happened. -/
structure ExecCall where
  /-- The flow `_checkFlowId` accepted (`_finality.flow`). -/
  flow : Flow
  /-- The batch and the IMT inclusion proof submitted for each leg (`_finality.proofs`). -/
  evidence : GateEvidence
  /-- The executing bundle's leg (`_executingBundleHash`; `ManagerExecutingBundleNotInFlow`
  reverts unless it is a leg of `flow`). -/
  leg : FlowLeg

/-- The checks `requireFlowFinalized` runs, on the call's own evidence: the executing
leg is a leg of the flow, `_checkFlowId` passes, and every leg's inclusion proof verifies
against an on-time batch of its declared source chain (`AtomicFlowManager.sol:110-130`). -/
def ExecCall.Verified (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (e : ExecCall) : Prop :=
  ExecutedViaBy h z0 hl cv fh S e.flow e.evidence e.leg

/-- A call that runs `_checkFlowId`, that is, one of the two entry points that take a
flow preimage. -/
inductive CheckedCall where
  /-- `requireFlowFinalized`, reached through `executeAtomicBundle`. -/
  | execute (e : ExecCall)
  /-- `authorizeRefund`. -/
  | authorize (a : AuthCall)

/-- The flow the call presented. -/
def CheckedCall.flow : CheckedCall → Flow
  | .execute e => e.flow
  | .authorize a => a.flow

/-- The checks the call runs, on its own evidence. -/
def CheckedCall.Verified (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) : CheckedCall → Prop
  | .execute e => e.Verified h z0 hl cv fh S
  | .authorize a => a.Verified h z0 hl cv fh S

/-- The `authorizeRefund` call, when the call is one. -/
def CheckedCall.authCall? : CheckedCall → Option AuthCall
  | .execute _ => none
  | .authorize a => some a

/-- The `authorizeRefund` calls of a log, in order.  This is the log `ReachLog` keeps. -/
def authCalls (log : List CheckedCall) : List AuthCall :=
  log.filterMap CheckedCall.authCall?

/-! ## The run -/

/-- Every interleaving of every chain's manager calls and every destination's gate
calls, with each call that checks a flow id logged, most recent first.

`append`, `authorize` and `claim` are `ReachLog`'s steps, with the same guards.
`execute` is `requireFlowFinalized` passing (`ExecCall.Verified`); it reads no manager
state and writes none. -/
inductive RunLog (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) : Managers → Managers → List CheckedCall → Prop
  | refl {Ms} : RunLog h z0 hl cv fh S Ms Ms []
  | append {Ms Ns log c f b} : RunLog h z0 hl cv fh S Ms Ns log → AppendGuard (Ns c) f b →
      RunLog h z0 hl cv fh S Ms (setAt Ns c ((Ns c).set f b .Committed)) log
  | execute {Ms Ns log} (e : ExecCall) : RunLog h z0 hl cv fh S Ms Ns log →
      e.Verified h z0 hl cv fh S →
      RunLog h z0 hl cv fh S Ms Ns (.execute e :: log)
  | authorize {Ms Ns log} (a : AuthCall) : RunLog h z0 hl cv fh S Ms Ns log →
      a.Verified h z0 hl cv fh S →
      AuthorizeGuard (Ns a.leg.chain) a.flow.flowId a.leg.bundleHash →
      RunLog h z0 hl cv fh S Ms
        (setAt Ns a.leg.chain ((Ns a.leg.chain).set a.flow.flowId a.leg.bundleHash .Revertable))
        (.authorize a :: log)
  | claim {Ms Ns log c f b} : RunLog h z0 hl cv fh S Ms Ns log → ClaimGuard (Ns c) f b →
      RunLog h z0 hl cv fh S Ms (setAt Ns c ((Ns c).set f b .Reverted)) log

end Contracts.FlowBinding
