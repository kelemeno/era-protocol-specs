import EraSpec.Protocol.NativeValueLegs.Specs.LegConservationRuns

/-!
# Model at head: `L2AssetRouter.recoverAtomicCall` through the vault

Source: era-contracts `draft/v0.35.0` at `b17415d20`; paths are relative to
`l1-contracts/contracts/`.

**This file is definitions only.**  The statements are in
`EraSpec.Protocol.NativeValueLegs.Properties.RouterRecoveryFrame` and are proved in
`EraSpec.Protocol.NativeValueLegs.Proofs.RouterRecoveryFrame`.

`LegConservation` leaves the recovery of router-produced calls abstract (`Params.routerRecover`) and
asks it to leave the leg's asset alone (`RecoveryFramesOthers`).  This file gives that code at head,
with the vault's branch spelled out, so that the premise reduces to the code that stays abstract:
handlers other than the vault, and the vault's deploy branch.

## The code

    // L2AssetRouter.recoverAtomicCall (bridge/asset-router/L2AssetRouter.sol:269-303)
    require(_destChainId != L1_CHAIN_ID, RecoverToL1NotSupported());                       // :275
    if (_callData.length < 4 || bytes4(_callData[:4]) != finalizeDeposit.selector) return false; // :284-286
    (, bytes32 assetId, bytes memory mintData) = abi.decode(_callData[4:], (uint256, bytes32, bytes)); // :290
    address assetHandler = assetHandlerAddress[assetId];                                    // :299
    require(assetHandler != address(0), AssetHandlerDoesNotExist(assetId));                // :300
    IL2AssetHandler(assetHandler).bridgeRecoverFailedTransfer(_destChainId, assetId, mintData); // :301

For the vault, `NativeTokenVaultBase.bridgeRecoverFailedTransfer` (`bridge/ntv/NativeTokenVaultBase.sol:195-214`)
decodes `(originalCaller, remoteReceiver, originToken, amount, erc20Metadata)`
(`common/libraries/DataEncoding.sol:101-118`) and runs `_disburseFailedTransfer` with the L2
override (`bridge/ntv/L2NativeTokenVault.sol:204-227`, base body `NativeTokenVaultBase.sol:264-286`),
as `LegConservation.vaultRefund` does for the base-token refund's own mint data, here with the
decoded data: the tracker's neutrality check, then the holder for the base token, otherwise the
tracker's `handleFinalizeBridgingOnL2` and the escrow, the registered token's `bridgeMint`, or, for a
bridged asset with no local token, `_ensureAndSaveTokenDeployed` and `bridgeMint` (`:280-284`).

## What is modelled

* `CallData.finalizeDeposit` is call data whose selector is `finalizeDeposit` and whose outer
  `abi.decode` succeeds; `CallData.other raw` is any other bytes, and `RecoveryCode.isFinalizeSelector`
  says whether they carry the selector (then the outer decode failed and the call reverts, `:290`).
* `RecoveryCode.decodeMint` is `decodeBridgeMintData` on the inner bytes (`none` reverts).
* Abstract: a handler other than the vault (`RecoveryCode.custom`), and the vault's deploy branch
  (`RecoveryCode.deploy`: metadata decoding, `assetIdCheck`, CREATE2 deployment, the registry write
  and the mint), which writes the registry that this model keeps as configuration.
* `onlyAtomicFlowManager`, `nonReentrant`, the vault's `onlyAssetRouter` and `requireZeroValue` pass
  on this path (the manager calls the router, the router the vault, with no value) and are omitted.
-/

namespace Contracts.NativeValueLegs

/-- Decoded bridge-mint data (`DataEncoding.decodeBridgeMintData`, `DataEncoding.sol:101-118`). -/
structure MintData where
  /-- `originalCaller`: the refund's receiver. -/
  originalCaller : Address
  /-- `remoteReceiver`: decoded and dropped by the refund. -/
  remoteReceiver : Address
  /-- `originToken`: read only by the deploy branch. -/
  originToken : Address
  /-- `amount`. -/
  amount : ℕ
  /-- `erc20Metadata`: read only by the deploy branch. -/
  metadata : Bytes

/-- What the head router recovery leaves to other code and to the ABI. -/
structure RecoveryCode where
  /-- `DataEncoding.decodeBridgeMintData` on the inner bytes; `none` reverts. -/
  decodeMint : Bytes → Option MintData
  /-- The raw call data starts with the `finalizeDeposit` selector. -/
  isFinalizeSelector : Bytes → Bool
  /-- `IL2AssetHandler(h).bridgeRecoverFailedTransfer(d, a, mintBytes)` for a handler `h` other than
  the vault; `none` reverts. -/
  custom : Address → World → Chain → AssetId → Bytes → Option World
  /-- The vault's deploy branch for a bridged asset with no local token, after the tracker call:
  `_ensureAndSaveTokenDeployed(a, originToken, metadata)` and `bridgeMint`
  (`NativeTokenVaultBase.sol:280-284`); `none` reverts. -/
  deploy : World → Chain → AssetId → MintData → Option World

/-- `NativeTokenVaultBase.bridgeRecoverFailedTransfer(d, a, mintBytes)` called by the router with no
value (`:195-214`), with the L2 `_disburseFailedTransfer` (`L2NativeTokenVault.sol:204-227`). -/
def vaultRecover (cfg : Config) (code : RecoveryCode) (w : World) (d : Chain) (a : AssetId)
    (mintBytes : Bytes) : Option World :=
  -- `whenNotPaused` (:199)
  if w.ntvPaused = true then none else
  -- `decodeBridgeMintData(_data)` (:201-202)
  match code.decodeMint mintBytes with
  | none => none
  | some md =>
    -- `assertRecoveryIsAccountingNeutral(a, d)` (L2NativeTokenVault.sol:213)
    if ¬ RecoveryNeutral cfg a d then none
    -- the base token: `recoverBaseToken(originalCaller, amount, d)` (L2NativeTokenVault.sol:214-216)
    else if a = cfg.baseAsset then holderRecover cfg w md.originalCaller md.amount d
    -- `_handleBridgeFromChain(d, a, amount)` (:276)
    else (trackerFinalize cfg w d a md.amount).bind fun w₁ =>
      -- native: `_withdrawFunds` from the escrow (:277-278), which reverts with no token address
      -- (as in `LegConservation.vaultRefund`)
      if cfg.originOf a = cfg.thisChain then
        (if cfg.tokenOf a = 0 then none
         else if w₁.bal a cfg.ntv < md.amount then none
         else some (moveToken w₁ a cfg.ntv md.originalCaller md.amount))
      -- bridged, no local token: deploy, then mint (:280-284)
      else if cfg.tokenOf a = 0 then code.deploy w₁ d a md
      -- bridged: `bridgeMint(originalCaller, amount)` (:284)
      else some (mintToken w₁ a md.originalCaller md.amount)

/-- `L2AssetRouter.recoverAtomicCall(d, data)` called by the manager (`L2AssetRouter.sol:269-303`). -/
def headRouterRecover (cfg : Config) (code : RecoveryCode) (w : World) (d : Chain) :
    CallData → Option World
  | .other raw =>
    -- `RecoverToL1NotSupported` (:275); not `finalizeDeposit`: `return false` (:284-286); the
    -- selector with undecodable arguments reverts (:290)
    if d = cfg.l1Chain then none else if code.isFinalizeSelector raw = true then none else some w
  | .finalizeDeposit _ a m =>
    if d = cfg.l1Chain then none
    -- `AssetHandlerDoesNotExist` (:299-300)
    else if w.handler a = 0 then none
    -- the handler's `bridgeRecoverFailedTransfer` (:301)
    else if w.handler a = cfg.ntv then vaultRecover cfg code w d a m
    else code.custom (w.handler a) w d a m

/-- The parameters of `LegConservation` with the head router recovery. -/
def headParams (cfg : Config) (code : RecoveryCode)
    (customBurn : Address → World → Chain → AssetId → Address → ℕ → Option World) : Params :=
  ⟨cfg, headRouterRecover cfg code, customBurn⟩

/-- **THE FRAME PREMISE ON THE REMAINING ABSTRACT CODE.**  A handler other than the vault, and the
vault's deploy branch, when they recover an asset other than `A`, leave `A`'s footprint and tracker
registration alone. -/
def CodeFramesOthers (cfg : Config) (code : RecoveryCode) (A : AssetId) : Prop :=
  (∀ h w d a m w', a ≠ A → code.custom h w d a m = some w' → Frames cfg A w w') ∧
    (∀ w d a md w', a ≠ A → code.deploy w d a md = some w' → Frames cfg A w w')

/-- Neither a handler other than the vault, nor the vault's deploy branch, clears a tracker
registration. -/
def CodeRegMono (code : RecoveryCode) : Prop :=
  (∀ h w d a m w', code.custom h w d a m = some w' → RegMono w w') ∧
    (∀ w d a md w', code.deploy w d a md = some w' → RegMono w w')

/-! ## Witness data -/

/-- Witness recovery code: mint data always decodes to `(5, 5, 0, 1, [1])`; no raw data carries the
selector; a handler other than the vault mints one unit of the asset to `8`; the deploy branch mints
the data's amount to its original caller. -/
def wCode : RecoveryCode where
  decodeMint := fun _ => some ⟨5, 5, 0, 1, [1]⟩
  isFinalizeSelector := fun _ => false
  custom := fun _ w _ a _ => some (mintToken w a 8 1)
  deploy := fun w _ a md => some (mintToken w a md.originalCaller md.amount)

end Contracts.NativeValueLegs
