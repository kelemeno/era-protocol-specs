import EraSpec.Contracts.Timeout
import EraSpec.Contracts.AtomicFlowManager

/-!
# Model: obligations, and the whole system's transitions

`Contracts.AtomicFlowManager` models one chain's per-leg state machine with no
reference to the tree.  `Contracts.Atomicity` models the trees with no reference to
the managers.  This file is the composition, and it is where "the same economic
obligation" becomes something one can quantify over.

**This file is definitions only.**  The results are in `EraSpec.Properties.Refund`
and proved in `EraSpec.Proofs.Refund`.

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
no collision is implied.  The chain is bound elsewhere — membership self-binds, and
`authorizeRefund` compares the proof's source chain with the leg's declared one
(`Properties.Protocol`). -/
def CommitValueInj (cv : CommitValue) : Prop :=
  ∀ f₁ b₁ f₂ b₂, cv f₁ b₁ = cv f₂ b₂ → f₁ = f₂ ∧ b₁ = b₂

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
the `ProofSourceChainMismatch` check, whose necessity is `Properties.Protocol`. -/
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

end Contracts.Refund
