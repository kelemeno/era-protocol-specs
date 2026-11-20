import EraSpec.Contracts.IndexedMerkleTree.Specs.Model


/-!
# Contract spec: `AtomicFlowManager`

The per-leg state machine of the flow manager, and the refund guarantees that
follow from its shape alone.

Source: era-contracts `draft/v0.35.0` at `b17415d20`, `l1-contracts/contracts/atomic-interop/`.
`_state` is `AtomicFlowManager.sol:61` and `LegState` is `IAtomicInterop.sol:10-15`. The guards
and writes: `append` requires `Unset` (`:162-164`) and writes `Committed` (`:166`);
`authorizeRefund`'s loop moves each `Committed` leg of the flow to `Revertable` and skips the
others (`:238-246`); `claimRefund` requires `Revertable` (`:254-257`) and writes `Reverted`
(`:260`). No other statement writes `_state`. Every other check of the three entry points only
reverts, so leaving it out only adds runs: `Step` over-approximates the deployed calls. The
transcription of the entry points with their flow-id and leg checks is
`Contracts.FlowCanonicalAtV35` (`Specs/FlowCanonicalAtV35.lean`), whose every run is a `Reach`
run here (`Contracts.FlowCanonicalAtV35.Properties.RunV35IsPinLegRun`).

## What this file is about

`AtomicFlowManager` holds one piece of mutable state per leg:

    mapping(bytes32 flowId => mapping(bytes32 bundleHash => LegState)) _state

and three operations move it: `append` (send time), `authorizeRefund` (timeout
proven), `claimRefund` (funds returned).  Every refund guarantee the contract
offers is a property of *this* machine — no Merkle proof, no tree, no timestamp
is involved once the proof has been accepted.

That separation is worth making explicit, because the two halves fail
differently.  Whether a refund is *justified* is a question about the commitment
tree and the deadline (`EraSpec.Contracts.IndexedMerkleTree.Specs.Model`, `EraSpec.Contracts.AtomicInteropProof.Properties.TimeoutSoundness`).
Whether a justified refund can be taken *twice* is a question about this state
machine, and the answer here does not depend on the proof system at all.

## The rank argument

Rather than enumerate reachable histories, every result below comes from one
observation: the three operations only ever move a leg *up* the chain

    Unset → Committed → Revertable → Reverted

because each guards on the exact predecessor state.  So `rank` is monotone along
any run, `Reverted` is a fixed point, and no-double-refund is a corollary rather
than a separate argument.  This is the state-machine analogue of the
checked-then-set nullifier pattern, and it is why `claimRefund` needs no
reentrancy guard: the flip to `Reverted` precedes the external calls, so a
reentrant claim meets a leg that is no longer `Revertable`.  That last argument
is about the order of operations inside `claimRefund`, which `Step.claim` cannot
express because it is a single atomic transition.  It is proved over a model with
reentrant callbacks in `EraSpec.Contracts.AtomicFlowManager.Properties.ModelStrong`
(`claim_order_decides_double_payout`).
-/

namespace Contracts.AtomicFlowManager


/-! ## State -/

/-- `LegState` (`IAtomicInterop.sol:10-15`). -/
inductive LegState
  | Unset
  | Committed
  | Revertable
  | Reverted
deriving DecidableEq, Repr


/-- Position in the lifecycle.  The whole file rests on this being monotone. -/
def rank : LegState → ℕ
  | .Unset => 0
  | .Committed => 1
  | .Revertable => 2
  | .Reverted => 3


/-- The manager's state: one `LegState` per `(flowId, bundleHash)`.  Keys are
`UInt256`, mirroring `bytes32`. -/
structure Manager where
  legState : UInt256 → UInt256 → LegState


/-- Fresh storage: every leg `Unset`. -/
def empty : Manager := ⟨fun _ _ => .Unset⟩


/-- Point update of one leg. -/
def Manager.set (M : Manager) (f b : UInt256) (s : LegState) : Manager :=
  ⟨fun f' b' => if f' = f ∧ b' = b then s else M.legState f' b'⟩


/-! ## Operations

Each carries the guard its Solidity counterpart enforces.  Access control
(`onlyInteropCenter` on `append`, `onlyInteropHandler` on `requireFlowFinalized`)
is *not* modeled as a guard here: it constrains who may call, not what the state
transition does, and modeling it would need a caller-identity component that
adds nothing to the results below.  It is recorded as an obligation in
`EraSpec.Refinement` instead, where the concrete repo's `#37`-style call-site
enumeration discharges it. -/

/-- `append`: `ManagerLegAlreadyCommitted` unless the leg is `Unset` (`:162-164`). -/
def AppendGuard (M : Manager) (f b : UInt256) : Prop := M.legState f b = .Unset


/-- `authorizeRefund`, per leg: the loop `continue`s unless the leg is
`Committed` (`:241-243`), so only committed legs move.  Legs committed on other chains are
absent from this manager and are silently skipped — that is what makes the
per-leg formulation faithful. -/
def AuthorizeGuard (M : Manager) (f b : UInt256) : Prop := M.legState f b = .Committed


/-- `claimRefund`: `ManagerLegNotRevertable` unless the leg is `Revertable` (`:254-257`). -/
def ClaimGuard (M : Manager) (f b : UInt256) : Prop := M.legState f b = .Revertable


/-- One step of the manager. -/
inductive Step : Manager → Manager → Prop
  | append {M f b} : AppendGuard M f b → Step M (M.set f b .Committed)
  | authorize {M f b} : AuthorizeGuard M f b → Step M (M.set f b .Revertable)
  | claim {M f b} : ClaimGuard M f b → Step M (M.set f b .Reverted)


/-- Reflexive-transitive closure: reachability over any number of steps. -/
inductive Reach : Manager → Manager → Prop
  | refl {M} : Reach M M
  | tail {M N P} : Reach M N → Step N P → Reach M P


end Contracts.AtomicFlowManager
