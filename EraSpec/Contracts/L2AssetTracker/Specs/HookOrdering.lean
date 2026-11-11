import EraSpec.Contracts.NativeTokenVaultBase.Specs.TrackerHooks

/-!
# Model: the order of the tracker hook and the token effect on the vault's four paths

Source: pin `c67894b9`, `NTV` = `bridge/ntv/NativeTokenVaultBase.sol`, `TRK` =
`bridge/asset-tracker/L2AssetTracker.sol`.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.L2AssetTracker.Properties.HookOrdering` and proved in
`EraSpec.Contracts.L2AssetTracker.Proofs.HookOrdering`.

## Why the order matters

The tracker's first-touch registration of a legacy token reads the token
(`TRK:327`, `:336`) and stores what it reads as the token's pre-v31 snapshot.  The source
relies on the read happening before the token moves:

* `TRK:334-335`: "here we assume that `totalSupply()` won't be affected in any way until it is
  used here, i.e. all deposits or withdrawals should firstly record the previous totalSupply";
* `NTV:454-455`: "in order to track `totalPreV31TotalSupply` correctly in L2AssetTracker, we
  have to call `_handleBridgeToChain` before any balance changes will be performed";
* `NTV:257-259` and `:293-295`: the inbound hook runs "before giving out funds to the user".

## The four paths (L2 vault, non-base asset)

* `bridgedOut`: `_handleBridgeToChain`, then `IBridgedStandardToken(token).bridgeBurn(_originalCaller,
  amount)` (`NTV:469`, `:471-472`);
* `nativeOut`: `_handleBridgeToChain`, then `_depositFunds(_originalCaller, token, amount)`,
  which moves `amount` from the depositor to the vault (`NTV:469`, `:473-476`, `:490-497`);
* `bridgedIn`: `_handleBridgeFromChain`, then `bridgeMint(receiver, amount)` (`NTV:260`,
  `:262-263`; recovery `:296`, `:304`);
* `nativeIn`: `_handleBridgeFromChain`, then `_withdrawFunds`, which moves `amount` from the vault
  to the receiver (`NTV:260`, `:264-265`; recovery `:296-298`; `L2NativeTokenVault.sol:238-241`).

The token is the token model's ledger; a native token's transfers are modelled by its
`transfer` (allowances are not modelled).  `runPath` is the source order: the hook reads the token
as it is BEFORE the effect.  `runPathEffectFirst` is the other order, for the countermodel only;
no source path runs it.

The base token's outbound path is different: the vault sends the value to the
`BaseTokenHolder`, whose `burnAndStartBridging` then calls the tracker (`NTV:463`,
`l2-system/BaseTokenHolder.sol:115-118`), so the effect precedes the hook there.  That is
harmless only because the base token never takes the first-touch path
(`Properties.BaseNeverTakesLegacyPath`).
-/

namespace Contracts.L2AssetTracker

/-- The vault's four token-moving paths. -/
inductive VaultPath where
  | bridgedOut
  | nativeOut
  | bridgedIn
  | nativeIn
deriving DecidableEq

/-- Outbound paths call `handleInitiateBridgingOnL2`. -/
def VaultPath.outbound : VaultPath → Bool
  | .bridgedOut => true
  | .nativeOut => true
  | .bridgedIn => false
  | .nativeIn => false

/-- The token effect of a path, by the vault, for `account` (the depositor on the way out, the
receiver on the way in). -/
def pathEffect (cfg : Config) (p : VaultPath) (tok : Contracts.BridgedStandardERC20.State)
    (account : Address) (amount : UInt256) : Option Contracts.BridgedStandardERC20.State :=
  match p with
  | .bridgedOut => Contracts.BridgedStandardERC20.burn tok cfg.ntv account amount
  | .nativeOut => Contracts.BridgedStandardERC20.transfer tok account cfg.ntv amount
  | .bridgedIn => Contracts.BridgedStandardERC20.mint tok cfg.ntv account amount
  | .nativeIn => Contracts.BridgedStandardERC20.transfer tok cfg.ntv account amount

/-- The tracker hook of a path, called by the vault with its stored entries for the asset
(`L2NativeTokenVault.sol:296-315`). -/
def pathHook (cfg : Config) (p : VaultPath) (st : Storage) (sl : ChainId) (reads : TokenReads)
    (chain : ChainId) (a : AssetId) (amount : UInt256) : Option Storage :=
  if p.outbound then
    handleInitiateBridgingOnL2 cfg st sl reads cfg.ntv chain a amount (cfg.ntvOriginChainId a)
  else
    handleFinalizeBridgingOnL2 cfg st sl reads cfg.ntv chain a amount (cfg.ntvOriginChainId a)
      (cfg.ntvTokenAddress a)

/-- **SOURCE ORDER**: the hook, reading the token before the effect, then the effect.  Either
failing fails the call. -/
def runPath (cfg : Config) (p : VaultPath) (st : Storage) (sl : ChainId)
    (tok : Contracts.BridgedStandardERC20.State) (chain : ChainId) (a : AssetId)
    (account : Address) (amount : UInt256) :
    Option (Storage × Contracts.BridgedStandardERC20.State) :=
  match pathHook cfg p st sl (tokenReads cfg tok) chain a amount with
  | none => none
  | some st' => (pathEffect cfg p tok account amount).map fun tok' => (st', tok')

/-- The REVERSED order, for the countermodel: the effect, then the hook reading the token after
it. -/
def runPathEffectFirst (cfg : Config) (p : VaultPath) (st : Storage) (sl : ChainId)
    (tok : Contracts.BridgedStandardERC20.State) (chain : ChainId) (a : AssetId)
    (account : Address) (amount : UInt256) :
    Option (Storage × Contracts.BridgedStandardERC20.State) :=
  match pathEffect cfg p tok account amount with
  | none => none
  | some tok' => (pathHook cfg p st sl (tokenReads cfg tok') chain a amount).map fun st' => (st', tok')

/-- The snapshot a first-touch registration takes from a token state: `MAX - balanceOf(vault)`
for a native asset, `totalSupply()` otherwise (`TRK:327-337`). -/
def legacySnapshot (cfg : Config) (a : AssetId) (tok : Contracts.BridgedStandardERC20.State) :
    SavedTotalSupply :=
  if Native cfg a then ⟨true, maxMinus (tokenReads cfg tok).ntvBalance⟩
  else ⟨true, (tokenReads cfg tok).totalSupply⟩

end Contracts.L2AssetTracker
