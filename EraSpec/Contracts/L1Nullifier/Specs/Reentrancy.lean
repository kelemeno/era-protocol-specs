import EraSpec.Contracts.L1Nullifier.Specs.Model

/-!
# Model: calls nested inside a claim's call to the router

Source: as `Specs/Model.lean`, era-contracts branch `draft/v0.35.0` at
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`; `N` is `l1-contracts/contracts/bridge/L1Nullifier.sol`,
`R` is `l1-contracts/contracts/bridge/asset-router/L1AssetRouter.sol`.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.L1Nullifier.Properties.Reentrancy` and are proved in
`EraSpec.Contracts.L1Nullifier.Proofs.Reentrancy`.

## What is modelled

`Specs/Model.lean` takes a successful claim as one atomic step. In the source a claim is not
atomic. After `_verifyAndClearTransfer` returns (`N:169`, `:191-204`), the nullifier calls
`l1AssetRouter.bridgeConfirmTransferResult` (`N:170-176`, `:206-212`). The router then calls the
asset handler (`R:314-320`), whose payout can run code the protocol does not control, such as a
token's transfer hook or a receiving contract. That code can call the bridgehub, the router or the
nullifier before the claim returns. In `NestedRun` every claim runs such a nested sequence of calls
(its callback), itself a `NestedRun`, to any depth.

`ClaimOrder.deleteFirst` is the source order: the guards, then the delete (`N:247`, inside
`_verifyAndClearTransfer`), then the call, so the callback runs against the deleted slot.
`ClaimOrder.callFirst` reverses the delete and the call. It is not the source and is used only by a
countermodel.

## Modelling choices

* A revert is the absence of an execution, as in `Specs/Model.lean`. A reverting nested call takes
  the claim down with it, so such an execution is simply absent.
* The `nonReentrant` guards are not modelled. In the source a nested claim of the nullifier
  (`N:168`, `:190`) and a nested call of the router's `bridgeConfirmTransferResult` (`R:312`)
  revert. Here they are allowed, which adds executions.
* A nested call is any `Step` of `Specs/Model.lean`, or a nested claim. `cl` is the claim with the
  status it is checked with: `bridgeConfirmTransferResult(cl)` (`N:166-177`), or
  `bridgeRecoverFailedTransfer` of a claim whose status is set to `Failure` (`N:180-213`). The two
  entry points differ only in that status.
* The guards are read on the state before the claim. The router's `whenNotPaused` (`R:312`) is read
  when the router is entered, after the delete, which does not change the router's pause flag.
* In both orders the clear is logged when the claim makes its call, before the callback's events.
-/

namespace Contracts.L1Nullifier

/-- Where a claim's delete (`N:247`) falls relative to its call into `l1AssetRouter`. -/
inductive ClaimOrder
  /-- The source: the delete in `_verifyAndClearTransfer` (`N:247`, called at `N:169` and
  `:191-204`) comes before the call (`N:170-176`, `:206-212`). -/
  | deleteFirst
  /-- The reversed order: the call, then the delete. Not the source. -/
  | callFirst
  deriving DecidableEq

/-- The claim's call has been made and logged; its slot is not yet deleted. -/
def logClear (s : Sys) (cl : Claim) : Sys :=
  { s with log := s.log ++ [.clear cl s.n.l1AssetRouter] }

/-- The claim's delete of its slot (`N:247`) on its own. -/
def deleteSlot (s : Sys) (cl : Claim) : Sys :=
  { s with n := { s.n with depositHappened := setSlot s.n.depositHappened cl.chainId cl.l2TxHash 0 } }

/-- `NestedRun o chk env cfg s u`: successful calls in sequence from `s` to `u`, where every claim
runs a nested `NestedRun`, its callback, inside its call into the router, with the delete placed as
`o` says. -/
inductive NestedRun (o : ClaimOrder) (chk : Checks) (env : Env) (cfg : Cfg) : Sys → Sys → Prop
  | nil (s : Sys) : NestedRun o chk env cfg s s
  /-- A call of `Specs/Model.lean`, then the rest of the run. -/
  | step {s t u : Sys} {l : Label} :
      Step chk env cfg s l t → NestedRun o chk env cfg t u → NestedRun o chk env cfg s u
  /-- The source order. The guards are read on `s`, the delete and the call happen
  (`afterClaim s cl`), the callback runs from there to `n`, then the rest of the run. -/
  | claimDeleteFirst {s n u : Sys} {a : Address} {cl : Claim} :
      o = .deleteFirst → ExternalSender cfg a → ClaimOk chk env cfg s cl →
      NestedRun o chk env cfg (afterClaim s cl) n → NestedRun o chk env cfg n u →
      NestedRun o chk env cfg s u
  /-- The reversed order. The guards are read on `s`, the call happens (`logClear s cl`), the
  callback runs from there to `n` against the undeleted slot, then the delete
  (`deleteSlot n cl`), then the rest of the run. -/
  | claimCallFirst {s n u : Sys} {a : Address} {cl : Claim} :
      o = .callFirst → ExternalSender cfg a → ClaimOk chk env cfg s cl →
      NestedRun o chk env cfg (logClear s cl) n → NestedRun o chk env cfg (deleteSlot n cl) u →
      NestedRun o chk env cfg s u

end Contracts.L1Nullifier
