import EraSpec.Contracts.AtomicFlowManager.Specs.RecoveryLimitsFaithful

/-!
# Model (History): the pinned refund loop over each call's `to`

Definitions for `EraSpec.Contracts.AtomicFlowManager.History.Properties.RecoveryLimitsFaithful`,
proved in `EraSpec.Contracts.AtomicFlowManager.History.Proofs.RecoveryLimitsFaithful`. The call and
decoder model (`SourceChain`, `probeAt`, `decodeBool`, `Conforms`) is the current one in
`Specs/RecoveryLimitsFaithful.lean`.

**History.** This is the record of the refund loop at era-contracts `c67894b9`
(`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), not a claim about `draft/v0.35.0` `b17415d20`. At the
pin, `_recoverBundle` (`atomic-interop/AtomicFlowManager.sol:219-230`) called
`IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)` on every call, counted the calls
that answered `true`, and reverted when none did (`:229`); `claimRefund` (`:165-180`) gated on
`Revertable` (`:169-170`) and wrote `Reverted` first (`:175`). At `b17415d20` the loop calls only
the asset router and counts nothing: that loop is `claimRefundV35` in
`Specs/RecoveryLimitsFaithful.lean`. Line numbers here are at the pin. `c.to` is what the pin's
`_processCallStarter` (`interop/InteropCenter.sol:701-751`) wrote into the bundle: for a direct
call the starter's recipient (`:745`), for an indirect call the address the indirect sender
returned (`:736`). The bundles are `Contracts.InteropCenter`'s, at the pin (`MODEL-CENTER`).

`pinnedProbe` is one iteration, `recoverLoop` the loop, `outcomes` reads a run as
`AttackVectors.RecoveryLimits.Outcome`s, and `claimRefundPinned` is the pinned claim.
-/

namespace Contracts.AtomicFlowManager.RecoveryLimitsFaithful.History

open AttackVectors.RecoveryLimits (Outcome)
open Contracts.InteropCenter (Address Word InteropCall Bundle CallStarter)

variable {W : Type}

/-! ## The loop at the pin (c67894b9) -/

/-- One iteration of the pinned `_recoverBundle` (`AtomicFlowManager.sol:224-225`):
`IAtomicRecoverable(c.to).recoverAtomicCall(destChainId, c.data)`, so the call goes to `c.to`. -/
def pinnedProbe (S : SourceChain W) (dest : Word) (w : W) (c : InteropCall) : Option (W × Bool) :=
  probeAt S dest w c.target c.data

/-- The loop of `_recoverBundle` (`AtomicFlowManager.sol:223-228`). It takes the calls in order,
each on the world the previous one left, with no `try/catch`. `some (w, n)` counts the calls that
answered `true`. -/
def recoverLoop (step : W → InteropCall → Option (W × Bool)) :
    W → List InteropCall → Option (W × ℕ)
  | w, [] => some (w, 0)
  | w, c :: cs =>
    match step w c with
    | none => none
    | some (w', b) =>
      match recoverLoop step w' cs with
      | none => none
      | some (w'', n) => some (w'', (if b then 1 else 0) + n)

/-- The outcomes the loop produces on the threaded world, as `AttackVectors.RecoveryLimits` names
them. The list stops at the first revert. -/
def outcomes (step : W → InteropCall → Option (W × Bool)) : W → List InteropCall → List Outcome
  | _, [] => []
  | w, c :: cs =>
    match step w c with
    | none => [Outcome.reverts]
    | some (w', b) => (if b then Outcome.recovered else Outcome.declined) :: outcomes step w' cs

/-- The pinned `claimRefund` of the leg whose bundle is `b`, when the leg is in state `s`
(`AtomicFlowManager.sol:165-180`). It is enabled only on a `Revertable` leg (`:169-170`). The leg
is set `Reverted` before the loop (`:175`), and the loop must recover at least one call (`:229`).
`none` is a revert of the whole transaction: the leg stays `s` and nothing the loop did persists. -/
def claimRefundPinned (S : SourceChain W) (s : LegState) (w : W) (b : Bundle) :
    Option (LegState × W) :=
  if s ≠ .Revertable then none else
  match recoverLoop (pinnedProbe S b.destinationChainId) w b.calls with
  | none => none
  | some (w', n) => if n = 0 then none else some (.Reverted, w')

/-! ## Predicates used by the statements -/

/-- No world of the source chain runs code at `a`. Examples are an EOA that never delegates to
code, and an address with nothing deployed on the source chain. -/
def NeverRunsCode (S : SourceChain W) (a : Address) : Prop := ∀ w, S.runsCode w a = false

/-- In every world, the code at `a` recovers `data` for destination `dest`: it answers `true`. -/
def AlwaysRecovers (S : SourceChain W) (a : Address) (dest : Word) (data : List UInt8) : Prop :=
  ∀ w, ∃ w', S.exec w a dest data = .returned (abiBool true) w'

/-! ## Witness data -/

/-- After the send: the two-call leg is `Committed`. -/
def mixS1 : Contracts.InteropCenter.State :=
  Contracts.InteropCenter.init.afterSend Contracts.InteropCenter.wParams mixD

/-- After `authorizeRefund`: the two-call leg is `Revertable`. -/
def mixS2 : Contracts.InteropCenter.State :=
  { mixS1 with
    manager := (mixS1.manager.set 7
      (Contracts.InteropCenter.bundleHash Contracts.InteropCenter.wParams mixD.bundle) .Revertable) }

/-- The same chain with code at `5` that answers `false`, as `IAtomicRecoverable.sol:13-15` asks of
an implementation that does not recognise the call. -/
def wSourceConforming : SourceChain Unit where
  runsCode := fun _ a => decide (a = 9) || decide (a = 5)
  exec := fun w a _ data =>
    .returned (abiBool (decide (a = 9) && decide (data = wDepositData))) w

/-- The same chain with code at `5` that has no `recoverAtomicCall`: its dispatcher reverts. -/
def wSourceNoHook : SourceChain Unit where
  runsCode := fun _ a => decide (a = 9) || decide (a = 5)
  exec := fun w a _ data =>
    if a = 9 then .returned (abiBool (decide (data = wDepositData))) w else .reverted


end Contracts.AtomicFlowManager.RecoveryLimitsFaithful.History
