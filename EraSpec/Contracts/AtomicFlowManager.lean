import EraSpec.Core.IMT

/-!
# Model: `AtomicFlowManager`

The per-leg state machine of the flow manager.

**This file is definitions only.**  The refund guarantees that follow from the
machine's shape are stated in `EraSpec.Properties.AtomicFlowManager` and proved
in `EraSpec.Proofs.AtomicFlowManager`.

## What this models

`AtomicFlowManager` holds one piece of mutable state per leg:

    mapping(bytes32 flowId => mapping(bytes32 bundleHash => LegState)) _state

and three operations move it: `append` (send time), `authorizeRefund` (timeout
proven), `claimRefund` (funds returned).  Every refund guarantee the contract
offers is a property of *this* machine — no Merkle proof, no tree, no timestamp
is involved once the proof has been accepted.

That separation is worth making explicit, because the two halves fail
differently.  Whether a refund is *justified* is a question about the commitment
tree and the deadline (`EraSpec.Core.IMT`, `EraSpec.AttackVectors.TimeoutSoundness`).
Whether a justified refund can be taken *twice* is a question about this state
machine, and the answer does not depend on the proof system at all.

## The rank argument (proved in `Proofs`)

The three operations only ever move a leg *up* the chain

    Unset → Committed → Revertable → Reverted

because each guards on the exact predecessor state.  So `rank` is monotone along
any run, `Reverted` is a fixed point, and no-double-refund is a corollary.  This
is the state-machine analogue of the checked-then-set nullifier pattern, and it
is why `claimRefund` needs no reentrancy guard: the flip to `Reverted` precedes
the external calls, so a reentrant claim meets a leg that is no longer
`Revertable`.

## Access control is not modelled

`onlyInteropCenter` on `append`, `onlyInteropHandler` on `requireFlowFinalized`:
these constrain who may call, not what the state transition does, and modelling
them would need a caller-identity component that adds nothing to the results.
Recorded as obligation O5 in `EraSpec.Refinement`.
-/

namespace Contracts.AtomicFlowManager

/-! ## State -/

/-- `LegState` from `IAtomicInterop.sol`. -/
inductive LegState
  | Unset
  | Committed
  | Revertable
  | Reverted
deriving DecidableEq, Repr

/-- Position in the lifecycle. -/
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

/-! ## Operations — each carries the guard its Solidity counterpart enforces -/

/-- `append`: `ManagerLegAlreadyCommitted` unless the leg is `Unset`. -/
def AppendGuard (M : Manager) (f b : UInt256) : Prop := M.legState f b = .Unset

/-- `authorizeRefund`, per leg: the loop `continue`s unless the leg is
`Committed`, so only committed legs move.  Legs committed on other chains are
absent from this manager and are silently skipped — that is what makes the
per-leg formulation faithful. -/
def AuthorizeGuard (M : Manager) (f b : UInt256) : Prop := M.legState f b = .Committed

/-- `claimRefund`: `ManagerLegNotRevertable` unless the leg is `Revertable`. -/
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
