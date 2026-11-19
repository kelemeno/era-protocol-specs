import EraSpec.Contracts.NativeTokenVaultBase.Specs.TrackerHooks

/-!
# Model: the order of the tracker hook and the token effect on the vault's four paths

Source: `draft/v0.35.0` head `b17415d20`, `NTV` = `bridge/ntv/NativeTokenVaultBase.sol`, `TRK` =
`bridge/asset-tracker/L2AssetTracker.sol` (paths under `l1-contracts/contracts/`).  First written at
the pin `c67894b9`; the four paths, the hook calls and the quoted comments are the same at
`b17415d20` (the vault's code differs only in renamed internal getters and locals).

**This file is definitions only.**  The results are in
`EraSpec.Contracts.L2AssetTracker.Properties.HookOrdering` and proved in
`EraSpec.Contracts.L2AssetTracker.Proofs.HookOrdering`.

## Why the order matters

The tracker's first-touch registration of a legacy token reads the token
(`TRK:249`, `:258`) and stores what it reads as the token's pre-v31 snapshot.  The source
relies on the read happening before the token moves:

* `TRK:256-257`: "here we assume that `totalSupply()` won't be affected in any way until it is
  used here, i.e. all deposits or withdrawals should firstly record the previous totalSupply";
* `NTV:433-434`: "in order to track `totalPreV31TotalSupply` correctly in L2AssetTracker, we
  have to call `_handleBridgeToChain` before any balance changes will be performed";
* `NTV:237-239` and `:273-275`: the inbound hook runs "before giving out funds to the user".

## The four paths (L2 vault, non-base asset)

* `bridgedOut`: `_handleBridgeToChain`, then `IBridgedStandardToken(token).bridgeBurn(_originalCaller,
  amount)` (`NTV:447`, `:449-450`);
* `nativeOut`: `_handleBridgeToChain`, then `_depositFunds(_originalCaller, token, amount)`,
  which moves `amount` from the depositor to the vault and returns the vault's balance increase,
  and the vault's check that the increase is `amount` (`NTV:447`, `:451-454`, `:468-475`;
  `depositFunds`);
* `bridgedIn`: `_handleBridgeFromChain`, then `bridgeMint(receiver, amount)` (`NTV:240`,
  `:242-243`; recovery `:276`, `:284`);
* `nativeIn`: `_handleBridgeFromChain`, then `_withdrawFunds`, which moves `amount` from the vault
  to the receiver (`NTV:240`, `:244-245`; recovery `:276-278`; `L2NativeTokenVault.sol:196-199`).

At `b17415d20` the L2 vault's recovery first calls the tracker's view
`assertRecoveryIsAccountingNeutral` (`L2NativeTokenVault.sol:213`), which writes nothing and does
not read the token; the recovery paths here are what follows it.  The guarded recovery is
`headRecover` (`Specs/LaterHeads.lean`).

The token is the token model's ledger; a native token's transfers are modelled by its
`transfer` (allowances are not modelled, so `safeTransferFrom` is a transfer by the depositor).
`runPath` is the source order: the hook reads the token as it is BEFORE the effect.
`runPathEffectFirst` is the other order, for the countermodel only; no source path runs it.
The vault's other checks (router, pause, nonzero amount, asset id, WETH, `msg.value`)
are not part of a path.  Which path the vault takes is decided by `originChainId[_assetId] !=
block.chainid` (`NTV:225`, `:369`); `runPath` takes the path as an argument, so a statement about
every path covers combinations the vault never makes.

The base token's outbound path is different: the vault forwards the value to the
`BaseTokenHolder`, whose `burnAndStartBridging` then calls the tracker (`NTV:441`,
`l2-system/BaseTokenHolder.sol:93-96`), so there the value moves before the hook runs.  It has
no first-touch read once `initL2` has run and the base token is registered
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

/-- `_depositFunds(_originalCaller, token, amount)` and the check on its result
(`NTV:452-454`, `:468-475`): `balanceBefore = balanceOf(vault)`, the transfer from the depositor
to the vault, `balanceAfter = balanceOf(vault)`, and `require(amount == balanceAfter -
balanceBefore)`, the subtraction checked.  With the token model's `transfer` the check fails
exactly when the depositor is the vault and `amount ≠ 0`. -/
def depositFunds (cfg : Config) (tok : Contracts.BridgedStandardERC20.State) (account : Address)
    (amount : UInt256) : Option Contracts.BridgedStandardERC20.State :=
  match Contracts.BridgedStandardERC20.transfer tok account cfg.ntv amount with
  | none => none
  | some tok' =>
    if tok.balances cfg.ntv ≤ tok'.balances cfg.ntv ∧
        tok'.balances cfg.ntv - tok.balances cfg.ntv = amount.val then some tok'
    else none

/-- The token effect of a path, by the vault, for `account` (the depositor on the way out, the
receiver on the way in). -/
def pathEffect (cfg : Config) (p : VaultPath) (tok : Contracts.BridgedStandardERC20.State)
    (account : Address) (amount : UInt256) : Option Contracts.BridgedStandardERC20.State :=
  match p with
  | .bridgedOut => Contracts.BridgedStandardERC20.burn tok cfg.ntv account amount
  | .nativeOut => depositFunds cfg tok account amount
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
for a native asset, `totalSupply()` otherwise (`TRK:249-259`). -/
def legacySnapshot (cfg : Config) (a : AssetId) (tok : Contracts.BridgedStandardERC20.State) :
    SavedTotalSupply :=
  if Native cfg a then ⟨true, maxMinus (tokenReads cfg tok).ntvBalance⟩
  else ⟨true, (tokenReads cfg tok).totalSupply⟩

end Contracts.L2AssetTracker
