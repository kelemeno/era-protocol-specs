import EraSpec.Contracts.AtomicFlowManager.Specs.Model
import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimits
import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery


/-!
# Contract spec: `AtomicFlowManager` recovery limits, on the manager's own state and across retries

Definitions for `EraSpec.Contracts.AtomicFlowManager.Properties.RecoveryLimitsStrong`; the proofs are in
`EraSpec.Contracts.AtomicFlowManager.Proofs.RecoveryLimitsStrong`.  Source:
`contracts/atomic-interop/AtomicFlowManager.sol` at era-contracts
`c67894b970a0dac6fe9144d8ebf4b0806e15a9af` (`l1-contracts/`), `claimRefund` (`:165-180`) and
`_recoverBundle` (`:219-230`).

## Why this file exists

`EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimits` reasons about one fixed list of outcomes, and about its
own copy of `LegState`.  So two of its claims cannot be stated there.  "The unrecovered calls get no second
attempt" is about the manager's later runs, and the copy is not the manager's state.  "Retrying does not help" is
about a later attempt, and the list cannot change.

`EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery` already models the loop with state.  `recoverBundle` threads
a world through the calls.  `outcomes` reads the outcome list off that threaded world.  `claimRefund` is the
manager's `claimRefund` for one leg, on `RecoveryLimits`' copy of the leg state.  This file reuses those
definitions, adding no second model of the loop, and adds:

* `toModelLeg` and `ofModelLeg`, the bijection between the copy and `Contracts.AtomicFlowManager.LegState`;
* `legClaimRefund`, which is `claimRefund(f, b)` on the manager's own state: the loop's `claimRefund` run on leg
  `(f, b)`'s state in a `Manager`, with the state it returns written back to that leg;
* `RetryStep`, the system in which one leg's claim is retried.  Other transactions change the world, the manager
  moves other legs, and the leg itself can be claimed only through `legClaimRefund` with its own bundle.
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsStrong

open Contracts.AssetRouter.AtomicRecovery (World Call claimRefund)


/-- `RecoveryLimits`' copy of the leg state, read as the manager's `LegState`. -/
def toModelLeg : AttackVectors.RecoveryLimits.LegState → LegState
  | .Unset => .Unset
  | .Committed => .Committed
  | .Revertable => .Revertable
  | .Reverted => .Reverted


/-- The manager's `LegState`, spelled as `RecoveryLimits` (and so `AtomicRecovery.claimRefund`) spells it. -/
def ofModelLeg : LegState → AttackVectors.RecoveryLimits.LegState
  | .Unset => .Unset
  | .Committed => .Committed
  | .Revertable => .Revertable
  | .Reverted => .Reverted


variable {X : Type}


/-- `claimRefund(f, b)` on the manager (`AtomicFlowManager.sol:165-180`).  It reads leg `(f, b)`'s state from `M`
and runs `AtomicRecovery.claimRefund` with the bundle's `calls` and the targets' behaviour `step`, on the world `w`.
If that succeeds, it writes the leg state it returns back to the leg.  `none` is a revert of the whole
transaction: the manager and the world are as they were. -/
def legClaimRefund (step : World X → Call → Option (World X × Bool)) (M : Manager) (f b : UInt256)
    (w : World X) (calls : List Call) : Option (Manager × World X) :=
  (claimRefund step (ofModelLeg (M.legState f b)) w calls).map fun p => (M.set f b (toModelLeg p.1), p.2)


/-- One step of the system in which leg `(f, b)`, whose bundle has calls `calls`, is claimed and claimed again.

* `env`: another transaction changes the world the bundle's targets act on, as `Env` allows.  The manager is
  untouched.  Other legs' refunds, token transfers, registry writes and the passage of time are all of this kind,
  in so far as they leave the manager alone.
* `other`: a manager step that leaves leg `(f, b)` alone.
* `claim`: a successful `claimRefund(f, b)` of the leg's own bundle, against the current world.  The bundle is
  fixed because the leg's key is the bundle's hash (`:166-167`).  A claim of `(f, b)` with different bundle bytes
  would need those bytes to hash to the same `b` under `encodeInteropBundleHash`, i.e. a keccak collision on the
  leg's bundle-hash preimage (see `InteropDataEncoding.BundleHashPinned`).  The model leaves that case out: it is
  built into this relation, not stated as a premise, and `blocked_leg_stays_revertable` relies on it.

So the leg's state can change only through `claim`.  The abstract `Step.claim` of `Specs/Model.lean` stands for
exactly this transaction with the recovery loop left out. -/
inductive RetryStep (step : World X → Call → Option (World X × Bool)) (Env : World X → World X → Prop)
    (f b : UInt256) (calls : List Call) : Manager × World X → Manager × World X → Prop
  | env {M w w'} : Env w w' → RetryStep step Env f b calls (M, w) (M, w')
  | other {M M' w} : Step M M' → M'.legState f b = M.legState f b →
      RetryStep step Env f b calls (M, w) (M', w)
  | claim {M w M' w'} : legClaimRefund step M f b w calls = some (M', w') →
      RetryStep step Env f b calls (M, w) (M', w')


end Contracts.AtomicFlowManager.RecoveryLimitsStrong
