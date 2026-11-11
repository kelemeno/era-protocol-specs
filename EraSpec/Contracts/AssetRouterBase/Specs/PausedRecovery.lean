import EraSpec.Contracts.AssetRouterBase.Specs.AtomicRecovery

/-!
# Model: an atomic refund while the source vault is paused

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`
(`contracts/` below is `l1-contracts/contracts/`).

**This file is definitions only.**  The results are in
`EraSpec.Contracts.AssetRouterBase.Properties.PausedRecovery` and proved in
`EraSpec.Contracts.AssetRouterBase.Proofs.PausedRecovery`.

`Contracts.AssetRouter.AtomicRecovery` models `AtomicFlowManager.claimRefund`'s loop over a
bundle's calls (`atomic-interop/AtomicFlowManager.sol:165-180, 219-230`), the router's
`recoverAtomicCall` (`bridge/asset-router/L2AssetRouter.sol:281-296`) and the vault's
`bridgeRecoverFailedTransfer` (`bridge/ntv/NativeTokenVaultBase.sol:213-233`).  Its world carries
the vault's `paused()` flag, and step 1 of the vault's refund is the `whenNotPaused` modifier
(`:217`).  This file adds what writes the flag and what the results need about the other targets.

## What writes the flag

`NativeTokenVaultBase.pause()` and `unpause()` (`bridge/ntv/NativeTokenVaultBase.sol:660-668`) are
`onlyOwner`.  They call OpenZeppelin v4 `PausableUpgradeable._pause` (`whenNotPaused`, sets the
flag) and `_unpause` (`whenPaused`, clears it).  Neither entry point writes anything else.  No
other function of the vault writes the flag.  The owner is fixed configuration (`OPS-CONFIG`).

## Where the flag is read on the refund path

Only in the vault.  `claimRefund` and `recoverAtomicCall` carry no pause check.
`recoverAtomicCall` forwards every `finalizeDeposit` call to the vault, whatever the asset's
handler (`L2AssetRouter.sol:294`).  The vault's `whenNotPaused` reverts it, and nothing catches
that revert: neither the router nor the manager's loop, which makes the raw call at
`AtomicFlowManager.sol:225`.  A call that is not a `finalizeDeposit` returns `false` before reaching
the vault (`:285-287`).  Targets other than the router are arbitrary.  The results state what
they need of them: `OthersLeavePause` (they do not write the vault's flag), and for the one
result that compares a paused claim with an unpaused one, `OthersIgnorePause` (they neither read
nor write it).
-/

namespace Contracts.AssetRouter.PausedRecovery

open Contracts.AssetRouter.AtomicRecovery

variable {X : Type}

/-- The vault owner's `pause()` (`NativeTokenVaultBase.sol:661-663`): OpenZeppelin's
`whenNotPaused`, then the flag is set.  `none` is a revert. -/
def pauseVault (w : World X) : Option (World X) :=
  if w.paused = true then none else some { w with paused := true }

/-- The vault owner's `unpause()` (`NativeTokenVaultBase.sol:666-668`): OpenZeppelin's
`whenPaused`, then the flag is cleared. -/
def unpauseVault (w : World X) : Option (World X) :=
  if w.paused = true then some { w with paused := false } else none

/-- The bundle has a call to the router whose data `recoverAtomicCall` decodes as a
`finalizeDeposit` (`L2AssetRouter.sol:285-293`).  Every router-produced bundle call is one
(`routerCall`), and so is a direct call that names the router with such data. -/
def HasRouterDeposit (cfg : Config) (calls : List Call) : Prop :=
  ∃ c ∈ calls, c.target = cfg.router ∧ ∃ src a m, c.data = .finalizeDeposit src a m

/-- Targets other than the router, when they return, leave the vault's pause flag as they found
it.  Only the vault's owner can write it (`onlyOwner`, `NativeTokenVaultBase.sol:661, 666`). -/
def OthersLeavePause (other : Address → World X → Chain → CallData → Option (World X × Bool)) :
    Prop :=
  ∀ target w dest d w' b, other target w dest d = some (w', b) → w'.paused = w.paused

/-- Targets other than the router neither read nor write the vault's pause flag: running one on a
world with the flag changed is running it on the original world and changing the flag after. -/
def OthersIgnorePause (other : Address → World X → Chain → CallData → Option (World X × Bool)) :
    Prop :=
  ∀ target w dest d (p : Bool), other target { w with paused := p } dest d
    = (other target w dest d).map (fun r => ({ r.1 with paused := p }, r.2))

end Contracts.AssetRouter.PausedRecovery
