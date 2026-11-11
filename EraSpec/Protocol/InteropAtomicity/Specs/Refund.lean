import EraSpec.Protocol.InteropAtomicity.Specs.Timeout
import EraSpec.Contracts.AtomicFlowManager.Specs.Model

/-!
# Model: obligations, and the whole system's transitions

`Contracts.AtomicFlowManager` models one chain's per-leg state machine with no
reference to the tree.  `Contracts.Atomicity` models the trees with no reference to
the managers.  This file is the composition, and it is where "the same economic
obligation" becomes something one can quantify over.

**This file is definitions only.**  The results are in `EraSpec.Protocol.InteropAtomicity.Properties.Refund`
and proved in `EraSpec.Protocol.InteropAtomicity.Proofs.Refund`.

## The obligation

A leg's commitment is keyed three ways in three places, and the whole safety
question is whether they stay tied together:

| where | key |
|---|---|
| the manager's `_state` | `(flowId, bundleHash)` |
| the source chain's tree | `commitValue(flowId, bundleHash)` |
| which chain escrowed | the leg's `legSourceChainIds[i]` |

`Obligation` is the triple, `obligationOf` builds it from a flow and a leg, and
`legValue` (in `Contracts.Atomicity`) is the tree's view of the same thing.  Every
result below is about one obligation, so "delivered and refunded" is a statement
about one economic commitment rather than about two coincidentally-related keys.

## Where the binding actually lives

Only one of the three manager operations is flow-bound, and the asymmetry is
faithful:

* `append` — called by the `InteropCenter` at send time, which sees only the opaque
  `flowId`.  No `_checkFlowId`.
* `claimRefund(_flowId, _bundle)` — takes the key directly and is guarded only by
  the leg being `Revertable`.  No `_checkFlowId`.
* `authorizeRefund(_flow, _missingLegIndex, _absence)` — recomputes the flow id
  (`_checkFlowId`), verifies a timeout proof against **one** missing leg, and then
  marks **that flow's** legs on this chain `Revertable`.

So `Step.authorize` is the only constructor carrying `FlowIdChecked`, and it marks
`(F.flowId, leg.bundleHash)` for a leg of `F` on `leg.chain`.  That the timeout is
proven for one leg and refunds the flow's other legs is not sloppiness — it is the
protocol: a flow that cannot finalize cannot finalize for any of its legs.  Which
is exactly why the binding that has to hold is at *flow* granularity, and why
`_checkFlowId` is the load-bearing check rather than anything per-leg.

## Interleaving

`Managers` is a manager per chain and a `Step` may touch any chain, so `Reach`
ranges over every interleaving of every chain's calls, in any order, for any number
of flows at once.  The tree side is already a fixed multi-chain, multi-batch
history and the refund gate quantifies existentially over batches, so a timeout
proof "at some point in the history" is what the model admits — the conservative
reading, and the one that makes the exclusion result independent of when each call
happens.
-/

namespace Contracts.Refund

open MerkleSpec Contracts.InteropCommitmentTree Contracts.Atomicity Contracts.Timeout
open Contracts.AtomicFlowManager

/-- The economic obligation a leg represents: which flow it belongs to, which
bundle it is, and which chain escrowed for it. -/
structure Obligation where
  flowId : UInt256
  bundleHash : UInt256
  chain : Chain
deriving DecidableEq

/-- Keccak injectivity on the `commitValue` preimage.

Note what is *not* in it: `commitValue(flowId, bundleHash)` has no chain, so two
obligations differing only in their chain share a commit value by construction and
no collision is implied.  The chain is bound elsewhere: the gate consults the declared
source chain's tree, and `authorizeRefund` compares the proof's source chain with the leg's declared one
(`Contracts.Protocol.unbound_gate_refunds_delivered_leg` (`Protocol/MultichainGate/Properties/Model.lean`)). -/
def CommitValueInj (cv : CommitValue) : Prop :=
  ∀ f₁ b₁ f₂ b₂, cv f₁ b₁ = cv f₂ b₂ → f₁ = f₂ ∧ b₁ = b₂

/-- **A PINNED `commitValue` COLLISION.**  `cv` collides on exactly the
`(flowId, bundleHash)` inputs of the two given obligations: those inputs differ, and
their commit values are equal.  The chain plays no part, as in `CommitValueInj`.

This replaces `CommitValueInj` (unsatisfiable,
`Contracts.Refund.Properties.CommitValueInjUnsatisfiable`) in the repaired statements;
it is false for a `cv` that separates those two inputs
(`Contracts.Refund.Properties.HonestCommitValueNoClash`). -/
def CommitClash (cv : CommitValue) (o o' : Obligation) : Prop :=
  (o.flowId, o.bundleHash) ≠ (o'.flowId, o'.bundleHash)
    ∧ cv o.flowId o.bundleHash = cv o'.flowId o'.bundleHash

/-- **BOUNDED COMMIT-VALUE INJECTIVITY.**  No two obligations of the explicit finite
list `os` have a `CommitClash`.  Satisfiable whenever `os` has fewer than `2^256`
entries (`Contracts.Refund.Properties.CommitValueInjOnSatisfiable`). -/
def CommitValueInjOn (cv : CommitValue) (os : List Obligation) : Prop :=
  ∀ o ∈ os, ∀ o' ∈ os, ¬ CommitClash cv o o'

/-- A commit value that is honest about one obligation `o`: `0` on `o`'s own
`(flowId, bundleHash)`, `1` everywhere else. -/
def honestCommitValue (o : Obligation) : CommitValue :=
  fun f b => if (f, b) = (o.flowId, o.bundleHash) then 0 else 1

/-- The obligation a leg of a flow carries. -/
def obligationOf (F : Flow) (leg : FlowLeg) : Obligation :=
  ⟨F.flowId, leg.bundleHash, leg.chain⟩

/-- One `AtomicFlowManager` per source chain. -/
abbrev Managers := Chain → Manager

/-- Fresh storage everywhere. -/
def emptyManagers : Managers := fun _ => Contracts.AtomicFlowManager.empty

/-- Replace one chain's manager. -/
def setAt (Ms : Managers) (c : Chain) (M : Manager) : Managers :=
  fun x => if x = c then M else Ms x

/-- The lifecycle state of an obligation, wherever it lives. -/
def stateOf (Ms : Managers) (o : Obligation) : LegState :=
  (Ms o.chain).legState o.flowId o.bundleHash

/-- **A TIMEOUT PROOF FOR THIS FLOW VERIFIED.**  `authorizeRefund` accepted an
absence proof for one of `F`'s legs, against that leg's own declared source chain —
the `ProofSourceChainMismatch` check, whose necessity is `Contracts.Protocol.unbound_gate_refunds_delivered_leg` (`Protocol/MultichainGate/Properties/Model.lean`). -/
def RefundAuthorized (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (S : System) (F : Flow) : Prop :=
  ∃ leg ∈ F.legs, LegRefundable h z0 hl cv S F leg

/-- One protocol action, on some chain's manager.

`append` and `claim` take a raw `(flowId, bundleHash)` key on a chain, because
neither runs `_checkFlowId` and both are guarded only by the leg's own state.
`authorize` is the flow-bound one. -/
inductive Step (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) : Managers → Managers → Prop
  | append {Ms c f b} : AppendGuard (Ms c) f b →
      Step h z0 hl cv fh S Ms (setAt Ms c ((Ms c).set f b .Committed))
  | authorize {Ms F leg} : FlowIdChecked fh F → leg ∈ F.legs →
      RefundAuthorized h z0 hl cv S F →
      AuthorizeGuard (Ms leg.chain) F.flowId leg.bundleHash →
      Step h z0 hl cv fh S Ms
        (setAt Ms leg.chain ((Ms leg.chain).set F.flowId leg.bundleHash .Revertable))
  | claim {Ms c f b} : ClaimGuard (Ms c) f b →
      Step h z0 hl cv fh S Ms (setAt Ms c ((Ms c).set f b .Reverted))

/-- Every interleaving of every chain's calls. -/
inductive Reach (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) : Managers → Managers → Prop
  | refl {Ms} : Reach h z0 hl cv fh S Ms Ms
  | tail {Ms Ns Ps} : Reach h z0 hl cv fh S Ms Ns → Step h z0 hl cv fh S Ns Ps →
      Reach h z0 hl cv fh S Ms Ps

/-- The obligation has been authorized for refund, or already refunded.  `rank`
is `Contracts.AtomicFlowManager.rank`, so this is "past `Committed`". -/
def Refunded (Ms : Managers) (o : Obligation) : Prop := 2 ≤ rank (stateOf Ms o)

/-! ## The run, logged: naming each `authorizeRefund` call

`Reach` records the managers' states, not the calls that produced them, so the flow
whose timeout authorized a refund is only known to exist.  `ReachLog` is `Reach` with
every `authorize` step's evidence written to a log: the flow it checked, the leg it
marked, and the timeout evidence (missing leg, batch, absence proof) it verified.
`Contracts.Refund.Properties.ReachIffReachLog` shows the two have the same reachable
states.  A collision or break can then be pinned to a call that is in the run. -/

/-- One `authorizeRefund(_flow, _missingLegIndex, _absence)` call as it happened. -/
structure AuthCall where
  /-- The flow `_checkFlowId` accepted. -/
  flow : Flow
  /-- The leg of `flow` this call marks `Revertable` (on its own chain). -/
  leg : FlowLeg
  /-- The leg whose absence the timeout proof shows (`_missingLegIndex`). -/
  missing : FlowLeg
  /-- The batch the absence proof is against. -/
  batch : ℕ
  /-- The IMT absence proof. -/
  proof : ImtProof

/-- The checks `authorizeRefund` runs, on the call's own evidence. -/
def AuthCall.Verified (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) (a : AuthCall) : Prop :=
  FlowIdChecked fh a.flow ∧ a.leg ∈ a.flow.legs ∧ a.missing ∈ a.flow.legs
    ∧ LegRefundableBy h z0 hl cv S a.flow a.missing a.batch a.proof

/-- `Reach`, with the `authorize` calls logged, most recent first. -/
inductive ReachLog (h : Hash) (z0 : UInt256) (hl : LeafHash) (cv : CommitValue)
    (fh : FlowHash) (S : System) : Managers → Managers → List AuthCall → Prop
  | refl {Ms} : ReachLog h z0 hl cv fh S Ms Ms []
  | append {Ms Ns log c f b} : ReachLog h z0 hl cv fh S Ms Ns log → AppendGuard (Ns c) f b →
      ReachLog h z0 hl cv fh S Ms (setAt Ns c ((Ns c).set f b .Committed)) log
  | authorize {Ms Ns log} (a : AuthCall) : ReachLog h z0 hl cv fh S Ms Ns log →
      a.Verified h z0 hl cv fh S →
      AuthorizeGuard (Ns a.leg.chain) a.flow.flowId a.leg.bundleHash →
      ReachLog h z0 hl cv fh S Ms
        (setAt Ns a.leg.chain ((Ns a.leg.chain).set a.flow.flowId a.leg.bundleHash .Revertable))
        (a :: log)
  | claim {Ms Ns log c f b} : ReachLog h z0 hl cv fh S Ms Ns log → ClaimGuard (Ns c) f b →
      ReachLog h z0 hl cv fh S Ms (setAt Ns c ((Ns c).set f b .Reverted)) log

/-- **A LOCATED BREAK BEHIND A REFUND OF OBLIGATION `o`.**  Relative to a flow `F`
executed on gate evidence `ev`, and a logged run: some `authorize` call `a` IN THE LOG
that marked exactly `o` is explained by one of

* `flowIdClash` — `a`'s flow is not `F`'s preimage, and `fh` collides on the two
  flows' own `(legs, deadline)` preimages (`FlowIdClash fh F a.flow`);
* `inclusion` — `a`'s flow is `F`, and the inclusion proof `ev a.missing` that `F`'s
  gate evidence submitted for `a`'s missing leg carries a `TreeRootBreak`;
* `absence` — `a`'s flow is `F`, and `a`'s own absence proof carries a `TreeRootBreak`
  on the root its branch selects.

Every witness is named by the run (`a ∈ log`) or by the premises (`F`, `ev`). -/
inductive RefundBreak (h : Hash) (z0 : UInt256) (hl : LeafHash) (fh : FlowHash) (S : System)
    (F : Flow) (ev : GateEvidence) (o : Obligation) (log : List AuthCall) : Prop
  | flowIdClash (a : AuthCall) : a ∈ log → obligationOf a.flow a.leg = o →
      FlowIdClash fh F a.flow → RefundBreak h z0 hl fh S F ev o log
  | inclusion (a : AuthCall) : a ∈ log → obligationOf a.flow a.leg = o → a.flow = F →
      InclusionBreak h z0 hl S a.missing.chain (ev a.missing).1 (ev a.missing).2 →
      RefundBreak h z0 hl fh S F ev o log
  | absence (a : AuthCall) : a ∈ log → obligationOf a.flow a.leg = o → a.flow = F →
      AbsenceBreak h z0 hl S F.deadline a.missing.chain a.batch a.proof →
      RefundBreak h z0 hl fh S F ev o log

/-- A flow hash that checks every one-leg flow with id `0` and every other flow with id
`1`: two checked flows with different ids, for the logged-run witnesses. -/
def lengthFlowHash : FlowHash := fun l _ => if l.length = 1 then 0 else 1


end Contracts.Refund
