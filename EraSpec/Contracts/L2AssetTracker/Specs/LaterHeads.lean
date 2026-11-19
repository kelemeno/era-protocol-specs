import EraSpec.Contracts.L2AssetTracker.Specs.NativeEscrow

/-!
# Model: the tracker's step at `b17415d20`, and the recovery guard

Sources, under `l1-contracts/contracts/`: `draft/v0.35.0` at `b17415d20`, cited `TRKH` for
`bridge/asset-tracker/L2AssetTracker.sol` and `L2NTVH` for `bridge/ntv/L2NativeTokenVault.sol`;
and `main` at `70096e2ea`, whose `L2AssetTracker.sol` differs from `TRKH` in two comments only
(`:54`, `:62-63`).  `Specs/Accounting.lean` was first written at the pin `c67894b9`
(`TRK` here is the pin's file) and models the same functions plus three pin-only ones.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.L2AssetTracker.Properties.LaterHeads` and proved in
`EraSpec.Contracts.L2AssetTracker.Proofs.LaterHeads`.

## What changed in the tracker

With comments removed, `TRKH` differs from `TRK` exactly as follows; every other function, inner
function and modifier is the same code.

* `backFillZKSyncOSBaseTokenV31MigrationData`, its modifier `onlyL2BaseToken`, and
  `registerBaseTokenDuringUpgrade` are gone.
* The backfill flag's slot is `__DEPRECATED_needBaseTokenTotalSupplyBackfill` (`TRKH:61-65`),
  private, and nothing reads or writes it.
* `initL2(_l1ChainId, _baseTokenAssetId)` (`TRKH:96-99`) takes no flag and leaves that slot alone.
* Two views are new: `assertRecoveryIsAccountingNeutral(_assetId, _toChainId)` (`TRKH:176-185`)
  and `assertBaseTokenRecoveryIsAccountingNeutral(_toChainId)` (`TRKH:187-190`).
* `MAX_TOKEN_BALANCE` is imported from `common/Config.sol` (`:79`); it is still
  `type(uint256).max`.

The callers pass the same arguments as at the pin (lines at `b17415d20`; the same calls at
`70096e2ea`): the L2 vault's two hooks (`L2NTVH:279-293`), its `_registerTokenInAssetTracker`
(`:177-179`) and `registerBaseTokenIfNeeded` (`:118-123`), the base-token holder's `give` and
`burnAndStartBridging` (`l2-system/BaseTokenHolder.sol:73`, `:94`), and the genesis helper's
`initL2(l1ChainId, baseTokenBridgingData.assetId)`
(`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:356-359`).  `handleFinalizeBaseTokenBridgingOnL2`
keeps its second permitted caller, `L2BaseToken`: at `70096e2ea` the Era base token calls it as at
the pin (`l2-system/era/L2BaseTokenEra.sol:92`); the `b17415d20` tree has no Era base token, and its
`protocol-docs/bridging.md:280-281` says the ZKsync OS runtime calls it as `L2BaseToken`.  The model
lets either caller make the call with any arguments.  So a head step (`HeadOp`, `execHead`) is a step
of `Specs/Accounting.lean` without the backfill and the upgrade registration, with `initL2` that
does not write the flag; the operations kept are run by `exec` itself.  The over-approximations
of `Specs/Accounting.lean` (any permitted caller, the fixed `Config`, free token reads) carry over.

`HeadEscrowStep` is `Specs/NativeEscrow.lean`'s composed run for one native asset with the tracker
at the heads: the vault's two native paths (`runPath`; the flow functions, `_depositFunds`,
`_withdrawFunds` and the order of hook and effect are the pin's code at both heads), anyone's
`registerLegacyToken(a)` reading the token, any other call at the heads that does not touch `a`,
and a `TokenMove`.  The model boundaries of `Specs/NativeEscrow.lean` carry over.

## The recovery guard

At both heads the L2 vault overrides `_disburseFailedTransfer` (`L2NTVH:204-227`; `:235-258` at
`70096e2ea`): it first calls `assertRecoveryIsAccountingNeutral(_assetId, _chainId)`, which reverts
when `_chainId`, the destination the recovered transfer was burned for, is the tracker's
`L1_CHAIN_ID`, and, for the tracker's `BASE_TOKEN_ASSET_ID`, when the vault's origin chain for it is
this chain.  For an asset other than the vault's `BASE_TOKEN_ASSET_ID` it then runs the base
`_disburseFailedTransfer` (`bridge/ntv/NativeTokenVaultBase.sol:264-286` at `b17415d20`), which is
the pin's code, now `virtual`; the vault's base asset is refunded through the base-token holder
instead (`L2NTVH:214-217`).  Otherwise the code of `NativeTokenVaultBase.sol` differs from the pin
by one added import at both heads and, at `b17415d20`, by renamed internal getters and local
variables.

`headRecover` is the vault model's `bridgeRecoverFailedTransfer` on the registered bridged branch
(`NativeTokenVaultBase/Specs/Resolution.lean`) with the L2 hooks, behind that guard.  It describes
the heads' recovery only for an asset other than the vault's base asset (`Config.baseAssetId` of
the vault model): for that asset the heads take the base-token holder's path, which is not
modelled.  The results recover a preparation's data, whose asset the preparation's `InScope` keeps
off the vault's base asset.  The guard is a view, so it writes nothing; it reads the tracker's
storage at the time of the recovery.  The router's own checks at the heads
(`bridge/asset-router/L2AssetRouter.sol:269-303` at `b17415d20`) are not modelled.
-/

namespace Contracts.L2AssetTracker

open Contracts.NativeTokenVaultBase (State ResolutionCall L2Accounting l2ResolutionHooks
  bridgeRecoverFailedTransfer)

/-! ## The tracker's calls at the heads -/

/-- `initL2(_l1ChainId, _baseTokenAssetId)` at the heads (`TRKH:96-99`),
`reentrancyGuardInitializer onlyUpgrader`: as at the pin, except that the backfill flag's slot is
not written. -/
def initL2Head (cfg : Config) (st : Storage) (caller : Address) (l1 : ChainId) (base : AssetId) :
    Option Storage :=
  if st.guardInitialized then none
  else if caller ≠ cfg.upgrader then none
  else some { st with l1ChainId := l1, baseTokenAssetId := base, guardInitialized := true }

/-- One call at the heads, with its caller and arguments as the heads' callers supply them: the
operations of `Op` without `backfill` and `registerBaseDuringUpgrade`, and `initL2` without its
flag. -/
inductive HeadOp where
  /-- The vault's `registerNewTokenIfNeeded(a, originChainId[a])` (`L2NTVH:122`, `:178`). -/
  | registerNewToken (a : AssetId)
  /-- Anyone's `registerLegacyToken(a)` (`TRKH:121-130`), with the token's reads at that moment. -/
  | registerLegacy (reads : TokenReads) (a : AssetId)
  /-- The vault's `handleInitiateBridgingOnL2(toChain, a, amount, originChainId[a])`. -/
  | initiate (reads : TokenReads) (toChain : ChainId) (a : AssetId) (amount : UInt256)
  /-- The holder's `handleInitiateBaseTokenBridgingOnL2(toChain, amount)`. -/
  | initiateBase (reads : TokenReads) (toChain : ChainId) (amount : UInt256)
  /-- The vault's `handleFinalizeBridgingOnL2(fromChain, a, amount, originChainId[a],
  tokenAddress[a])`. -/
  | finalize (reads : TokenReads) (fromChain : ChainId) (a : AssetId) (amount : UInt256)
  /-- `handleFinalizeBaseTokenBridgingOnL2(fromChain, amount)` by a permitted caller. -/
  | finalizeBase (reads : TokenReads) (caller : Address) (fromChain : ChainId) (amount : UInt256)
  /-- The upgrader's `initL2(initL1ChainId, initBaseAssetId)`. -/
  | initL2
  /-- The chain's settlement layer becomes `c` (migration; not a tracker call). -/
  | setSettlementLayer (c : ChainId)

/-- The successor of one call at the heads, or `none` if it reverts.  Every operation but `initL2`
is the pin's operation, run by `exec`: its code is unchanged. -/
def execHead (cfg : Config) (sys : Sys) : HeadOp → Option Sys
  | .registerNewToken a => exec cfg sys (.registerNewToken a)
  | .registerLegacy reads a => exec cfg sys (.registerLegacy reads a)
  | .initiate reads toChain a amount => exec cfg sys (.initiate reads toChain a amount)
  | .initiateBase reads toChain amount => exec cfg sys (.initiateBase reads toChain amount)
  | .finalize reads fromChain a amount => exec cfg sys (.finalize reads fromChain a amount)
  | .finalizeBase reads caller fromChain amount =>
      exec cfg sys (.finalizeBase reads caller fromChain amount)
  | .initL2 =>
      (initL2Head cfg sys.st cfg.upgrader cfg.initL1ChainId cfg.initBaseAssetId).map fun st =>
        { sys with st := st }
  | .setSettlementLayer c => exec cfg sys (.setSettlementLayer c)

/-- One successful call at the heads. -/
def HeadStep (cfg : Config) (sys sys' : Sys) : Prop := ∃ op, execHead cfg sys op = some sys'

/-- Any number of successful calls at the heads. -/
abbrev HeadReach (cfg : Config) : Sys → Sys → Prop := Relation.ReflTransGen (HeadStep cfg)

/-! ## The composed run with a native token, at the heads -/

/-- The calls at the heads that read the token of `a` or record a flow of `a`, as
`Op.TouchesAsset`: `registerLegacyToken(a)` and the vault's two flow hooks for `a`. -/
def HeadOp.TouchesAsset (a : AssetId) : HeadOp → Prop
  | .registerLegacy _ b => b = a
  | .initiate _ _ b _ => b = a
  | .finalize _ _ b _ => b = a
  | _ => False

/-- One step of the composed run for asset `a` with the tracker at the heads: `EscrowStep` with
calls at the heads in place of the pin's. -/
inductive HeadEscrowStep (cfg : Config) (a : AssetId) : EscrowSys → EscrowSys → Prop
  /-- The vault's outbound native path: the hook reading the token, then the deposit. -/
  | nativeOut {e : EscrowSys} {st' : Storage} {tok' : Contracts.BridgedStandardERC20.State}
      (chain : ChainId) (account : Address) (amount : UInt256) :
      runPath cfg .nativeOut e.sys.st e.sys.sl e.tok chain a account amount = some (st', tok') →
      HeadEscrowStep cfg a e ⟨{ e.sys with st := st', audit := e.sys.audit.addOut a amount }, tok'⟩
  /-- The vault's inbound native path: the hook reading the token, then the withdrawal. -/
  | nativeIn {e : EscrowSys} {st' : Storage} {tok' : Contracts.BridgedStandardERC20.State}
      (chain : ChainId) (account : Address) (amount : UInt256) :
      runPath cfg .nativeIn e.sys.st e.sys.sl e.tok chain a account amount = some (st', tok') →
      HeadEscrowStep cfg a e ⟨{ e.sys with st := st', audit := e.sys.audit.addIn a amount }, tok'⟩
  /-- Anyone's `registerLegacyToken(a)` at the heads (`TRKH:121-130`), reading the token as it
  is. -/
  | registerLegacy {e : EscrowSys} {sys' : Sys} :
      execHead cfg e.sys (.registerLegacy (tokenReads cfg e.tok) a) = some sys' →
      HeadEscrowStep cfg a e ⟨sys', e.tok⟩
  /-- Any other successful call at the heads. -/
  | tracker {e : EscrowSys} {sys' : Sys} (op : HeadOp) :
      ¬ op.TouchesAsset a → execHead cfg e.sys op = some sys' →
      HeadEscrowStep cfg a e ⟨sys', e.tok⟩
  /-- A change of the ledger the vault does not make. -/
  | token {e : EscrowSys} {tok' : Contracts.BridgedStandardERC20.State} :
      TokenMove cfg e.tok tok' → HeadEscrowStep cfg a e ⟨e.sys, tok'⟩

/-- Any number of composed steps at the heads. -/
abbrev HeadEscrowReach (cfg : Config) (a : AssetId) : EscrowSys → EscrowSys → Prop :=
  Relation.ReflTransGen (HeadEscrowStep cfg a)

/-! ## The recovery guard -/

/-- `assertRecoveryIsAccountingNeutral(_assetId, _toChainId)` (`TRKH:176-185`) does not revert:
the destination is not the tracker's `L1_CHAIN_ID`, and if the asset is the tracker's
`BASE_TOKEN_ASSET_ID`, the vault's origin chain for it is not this chain. -/
def RecoveryAccountingNeutral (cfg : Config) (st : Storage) (a : AssetId) (toChain : ChainId) :
    Prop :=
  toChain ≠ st.l1ChainId ∧ (a = st.baseTokenAssetId → ¬ Native cfg a)

instance (cfg : Config) (st : Storage) (a : AssetId) (toChain : ChainId) :
    Decidable (RecoveryAccountingNeutral cfg st a toChain) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The L2 vault's `bridgeRecoverFailedTransfer` at the heads, on the registered bridged branch
the vault model covers, for an asset other than the vault's base asset: the tracker's guard,
reading the tracker storage at the time of the recovery, then the pin's recovery with the L2 hooks
(`L2NTVH:204-227`). -/
def headRecover (cfg : Config) (s : State L2Accounting) (c : ResolutionCall) :
    Option (State L2Accounting) :=
  if RecoveryAccountingNeutral cfg s.accounting.st c.assetId c.chain then
    bridgeRecoverFailedTransfer (l2ResolutionHooks cfg) s c
  else none

end Contracts.L2AssetTracker
