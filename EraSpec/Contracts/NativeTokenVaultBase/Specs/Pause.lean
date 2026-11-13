import EraSpec.Contracts.NativeTokenVaultBase.Specs.Resolution

/-!
# The vault's pause switch, and what an interval of pause does to pending transfers

Local specification at source pin `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`
(`l1-contracts/contracts/bridge/ntv/NativeTokenVaultBase.sol`, cited as `NTV`).  It is built on the
representation model's `State` (`Specs/RepresentationPreparation.lean`), whose `paused` field is
`PausableUpgradeable.paused()`, and on the resolution entry points (`Specs/Resolution.lean`).

## What the source does

* `pause()` (`NTV:660-663`) and `unpause()` (`NTV:665-668`) are `onlyOwner`.  They call OpenZeppelin
  v4 `PausableUpgradeable._pause`, which is `whenNotPaused` and sets the flag, and `_unpause`, which
  is `whenPaused` and clears it.  No other function of the vault writes the flag.  The source notes
  that on L2 the switch "is kept only for legacy/shared-code reasons and should not be used as an
  emergency mechanism" (`NTV:656-659`).  It is live all the same.
* Three entry points carry `whenNotPaused`, the three this package models: `bridgeBurn`
  (`NTV:315-339`, modifier at `:327`), here `prepare`; `bridgeMint` (`NTV:193-205`, at `:197`); and
  `bridgeRecoverFailedTransfer` (`NTV:213-233`, at `:217`).  `PreparationGuards.paused_preparation_rejected`
  and `ResolutionPausedRejected` show each rejects a paused vault.

## What is modelled

`vaultPause` and `vaultUnpause` are the two owner calls, with their guards, writing only the flag.
`VaultEntryCall` is one attempted call to one of the three entry points.  `VaultEntryCall.commit`
commits it the way the commit interfaces do (`transact`, `mintTransact`, `recoverTransact`): the
successor state on success, the unchanged state on failure.  `commitVaultCalls` attempts a list in
order.  Calls by other contracts during the pause, such as transfers of the token, are not
attempts on the vault.  `RecoverAfterSpending` covers ordinary transfers.  Ownership is fixed
configuration (`OPS-CONFIG`).
-/

namespace Contracts.NativeTokenVaultBase

variable {Accounting : Type}

/-- The owner's `pause()` (`NTV:660-663`): `whenNotPaused`, then the flag is set.  `none` is a
revert. -/
def vaultPause (s : State Accounting) : Option (State Accounting) :=
  if s.paused = true then none else some { s with paused := true }

/-- The owner's `unpause()` (`NTV:665-668`): `whenPaused`, then the flag is cleared. -/
def vaultUnpause (s : State Accounting) : Option (State Accounting) :=
  if s.paused = true then some { s with paused := false } else none

/-- One attempted call to one of the vault's three `whenNotPaused` entry points, on the branches
this package models. -/
inductive VaultEntryCall where
  /-- `bridgeBurn` (`NTV:315-339`) on the registered representation branch: `prepare`. -/
  | burn (r : Request)
  /-- `bridgeMint` (`NTV:193-205`) on the registered bridged branch. -/
  | mint (c : ResolutionCall)
  /-- `bridgeRecoverFailedTransfer` (`NTV:213-233`) on the registered bridged branch. -/
  | recover (c : ResolutionCall)

/-- The vault state after one attempted call: the successor on success, the original state on a
revert. -/
def VaultEntryCall.commit (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (s : State Accounting) : VaultEntryCall → State Accounting
  | .burn r => (transact hooks s r).1
  | .mint c => (mintTransact rh s c).1
  | .recover c => (recoverTransact rh s c).1

/-- Attempt the calls in order, each on the state the previous one left. -/
def commitVaultCalls (hooks : Hooks Accounting) (rh : ResolutionHooks Accounting)
    (s : State Accounting) (calls : List VaultEntryCall) : State Accounting :=
  calls.foldl (fun t c => c.commit hooks rh t) s

end Contracts.NativeTokenVaultBase
