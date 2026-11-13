import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Shared definitions of the L2 bridge models

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`.
Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.**  It holds the word aliases, the map update, and the
`Ownable2StepUpgradeable` + `PausableUpgradeable` slice that `L2AssetRouter`,
`L2NativeTokenVault` and `L2Bridgehub` all inherit
(`bridge/asset-router/AssetRouterBase.sol:37, 378-385`,
`bridge/ntv/NativeTokenVaultBase.sol:53-54, 636-643`,
`core/bridgehub/BridgehubBase.sol:544-551`).

Addresses, chain ids and asset ids are all 256-bit words.  The model never does
arithmetic on an address, so the 160-bit range of `address` plays no role.
-/

namespace Contracts.L2AssetRouter

abbrev Chain := UInt256
abbrev AssetId := UInt256
abbrev Address := UInt256

/-- One mapping write: `f[k] = v`. -/
def upd {β : Type} (f : UInt256 → β) (k : UInt256) (v : β) : UInt256 → β :=
  fun x => if x = k then v else f x

/-- The ownership and pause slots (OpenZeppelin `Ownable2StepUpgradeable`,
`PausableUpgradeable`). -/
structure Own where
  /-- `owner()`. -/
  owner : Address
  /-- `pendingOwner()`. -/
  pending : Address
  /-- `paused()`. -/
  paused : Bool

/-- The five inherited owner entry points. -/
inductive OwnerOp where
  /-- `pause()`, `onlyOwner`; `_pause` is `whenNotPaused`. -/
  | pause
  /-- `unpause()`, `onlyOwner`; `_unpause` is `whenPaused`. -/
  | unpause
  /-- `transferOwnership(newOwner)`, `onlyOwner`: records the pending owner. -/
  | transferOwnership (newOwner : Address)
  /-- `acceptOwnership()`: the pending owner takes over. -/
  | acceptOwnership
  /-- `renounceOwnership()`, `onlyOwner`.  None of the three contracts overrides it. -/
  | renounceOwnership

/-- `_transferOwnership(n)` of `Ownable2StepUpgradeable`: sets the owner and deletes the
pending owner. -/
def Own.setOwner (o : Own) (n : Address) : Own := { o with owner := n, pending := 0 }

/-- One owner entry point called by `caller`.  `none` is a revert. -/
def Own.exec (o : Own) (caller : Address) : OwnerOp → Option Own
  | .pause => if caller = o.owner ∧ o.paused = false then some { o with paused := true } else none
  | .unpause => if caller = o.owner ∧ o.paused = true then some { o with paused := false } else none
  | .transferOwnership n => if caller = o.owner then some { o with pending := n } else none
  | .acceptOwnership => if caller = o.pending then some (o.setOwner caller) else none
  | .renounceOwnership => if caller = o.owner then some (o.setOwner 0) else none

/-- Fresh storage. -/
def Own.init : Own := ⟨0, 0, false⟩

end Contracts.L2AssetRouter
