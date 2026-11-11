import EraSpec.Contracts.BridgedStandardERC20.Specs.LegacyFallback
import EraSpec.Contracts.NativeTokenVaultBase.Specs.ModelCorrespondence

/-!
# The legacy fallback's asset id against the vault's registry

`BridgedStandardERC20`'s `onlyNTV` fallback
(`Contracts/BridgedStandardERC20/Specs/LegacyFallback.lean`) writes a legacy token's `assetId`
slot to `encodeNTVAssetId(L1_CHAIN_ID, originToken)`. It reads only the token's own
`originToken` slot and the L2 vault's `L1_CHAIN_ID`. It does not read the vault's registry.
This file asks when that id is the vault's id for the token, in the registry model
`Contracts.NativeTokenVault` (`Specs/RegistryAndEscrow.lean`).

**This file is definitions only.** Statements are in
`EraSpec.Contracts.NativeTokenVaultBase.Properties.LegacyFallback`.

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`,
`l1-contracts/contracts/bridge/ntv/NativeTokenVaultBase.sol` unless another file is named.

## The vault side

The vault's id for a token `T` is `assetId[T]` (:85). The registry model's `Valid.idShape`
says a registered id is `encodeNTVAssetId(originChain, originToken)` of the pair it records.

The vault calls a token's `bridgeMint` / `bridgeBurn`, and so can trigger the fallback, only on
its bridged branch, where `originChainId[assetId] != block.chainid`: `_bridgeMintToken`
(:245, :262-263), `_disburseFailedTransfer` (:221, :297-304) and `_getTokenAndBridgeToChain`
(:389, :471-472). For a token native to this chain it escrows instead (`_depositFunds` :474,
`_withdrawFunds` :265, :298). `VaultBridgesToken` names that condition.

## What writes a legacy token's registry entry at the pin

Nothing that can record it as bridged. `_setNewTokenStorage` (:588-598) is the only writer of
`assetId[token]` in this file, and it is reached from two places:

* `_unsafeRegisterNativeToken` (:515-522), from `_registerToken` (:133-142), which is reached
  from the permissionless `registerToken` (:129-131), `ensureTokenIsRegistered` (:145-152) and
  `tryRegisterTokenFromBurnData` (:341-355). It records the pair `(block.chainid, token)` as
  native. It checks only WETH, that the token has code and that it has no id (:138-140), and has
  no legacy-token check, so on a legacy token with no id it records it as native to this chain.
  This is the registry model's `registerNative`.
* `_ensureAndSaveTokenDeployedInner` (:573-586), for a token deployed by that same call. A
  legacy token is already deployed, so this path cannot record it (`VM-DEPLOY`).

`L2NativeTokenVault.updateL2` (`bridge/ntv/L2NativeTokenVault.sol:170-172`) writes the maps for
the base token only. The comments at :200 and :439 refer to `setLegacyTokenAssetId`, which is
not in the pinned source, and `bridge/asset-tracker/L2AssetTracker.sol:310` states the
expectation that all legacy tokens have their origin chain set in the vault. So a legacy token's
bridged registry entry was written before the pin, and whether it records
`(L1_CHAIN_ID, originToken)` depends on that history (`OPS-CONFIG`), not on pinned code.

## Encodings and the origin token

`legacyEnv e l1` runs the fallback with `encodeNTVAssetId` taken to be the registry model's
`e` on the zero-extended address (`widen`). Both are
`keccak256(abi.encode(chainId, L2_NATIVE_TOKEN_VAULT_ADDR, token))`
(`common/libraries/DataEncoding.sol:151-153`), and ABI-encoding an address zero-extends it.

The registry model's `originToken` is not storage. For a bridged asset it stands for the
token's own `originToken()` getter (`Specs/RegistryAndEscrow.lean`, and `Refinement.lean` O9).
Under that reading the vault's recorded origin token for a legacy token is the token's
`originToken` slot, which the fallback does not change, and only the recorded origin chain can
differ (`Properties.LegacyAssetIdAgreesIffL1OriginOn`). The general statements do not assume
the reading.
-/

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain Vault NtvAssetId)

/-- The fallback's environment for `L1_CHAIN_ID = l1`, with the registry model's encoding on the
zero-extended address. -/
def legacyEnv (e : NtvAssetId) (l1 : Chain) : BridgedStandardERC20.LegacyEnv :=
  ⟨l1, fun c t => e c (widen t)⟩

/-- The pair the fallback hashes: `(L1_CHAIN_ID, originToken)`, as registry-model words. -/
def legacyPair (l1 : Chain) (ot : Address) : Chain × NativeTokenVault.Address :=
  (l1, widen ot)

/-- The vault's id for the token at `T`: `assetId[T]` (:85). Zero means none. -/
def vaultIdOf (V : Vault) (T : Address) : NativeTokenVault.AssetId :=
  V.assetOf (widen T)

/-- The (origin chain, origin token) pair the vault records for that id. -/
def recordedPair (V : Vault) (T : Address) : Chain × NativeTokenVault.Address :=
  (V.originChain (vaultIdOf V T), V.originToken (vaultIdOf V T))

/-- The vault registered the token at `T` under origin chain `l1` and origin token `ot`. -/
def RecordsLegacyPair (V : Vault) (T : Address) (l1 : Chain) (ot : Address) : Prop :=
  vaultIdOf V T ≠ 0 ∧ recordedPair V T = legacyPair l1 ot

/-- The token's own `assetId` slot is the vault's id for the token at `T`. -/
def AssetIdAgrees (V : Vault) (T : Address) (tok : BridgedStandardERC20.State) : Prop :=
  vaultIdOf V T = tok.config.assetId

/-- The vault has an id for the token at `T` and it is not native to this chain. This is the
condition under which the vault's own flows call the token's `bridgeMint` / `bridgeBurn`
(:245, :262-263, :297-304, :471-472) rather than escrowing it. -/
def VaultBridgesToken (thisChain : Chain) (V : Vault) (T : Address) : Prop :=
  vaultIdOf V T ≠ 0 ∧ ¬ NativeTokenVault.Native thisChain V (vaultIdOf V T)

/-- The two ways the fallback's id can equal the vault's id for `T` without the vault recording
the legacy pair, each pinned to the two named pairs: the legacy pair hashes to the unset
sentinel while `T` has no id; or `T` has an id whose recorded pair differs from the legacy pair
yet hashes to the same id. -/
def LegacyIdBreak (e : NtvAssetId) (V : Vault) (T : Address) (l1 : Chain) (ot : Address) :
    Prop :=
  (e l1 (widen ot) = 0 ∧ vaultIdOf V T = 0) ∨
  (vaultIdOf V T ≠ 0 ∧ recordedPair V T ≠ legacyPair l1 ot ∧
    e (recordedPair V T).1 (recordedPair V T).2 = e l1 (widen ot))

/-! ## Preparation of a legacy token

`prepare` (`Specs/RepresentationPreparation.lean`) calls the nonlegacy `burn`, which refuses a
legacy token, so none of its results covers the first preparation of one. `prepareLegacy` is
`prepare` verbatim except that the token call is the deployed `bridgeBurn`, with both `onlyNTV`
branches (`_getTokenAndBridgeToChain`, :469-472). As in `prepare`, the accounting hook runs
first and sees the token before the call, so before the fallback. -/

variable {Accounting : Type}

/-- `prepare`, with the token's deployed `bridgeBurn` in place of the nonlegacy `burn`. -/
def prepareLegacy (env : BridgedStandardERC20.LegacyEnv) (hooks : Hooks Accounting)
    (s : State Accounting) (r : Request) : Option (Result Accounting) :=
  if InScope s r ∧ EntryAllowed s r then
    match hooks.account s.accounting s.token r.destinationChain r.assetId r.data.amount with
    | none => none
    | some accounted =>
      if r.msgValue = 0 then
        match BridgedStandardERC20.bridgeBurn env s.token s.config.vault r.depositor
            r.data.amount with
        | none => none
        | some burned =>
          if burned.config.originToken ≠ 0 ∧ s.config.originChainId ≠ 0 then
            match hooks.metadata burned s.config.originChainId with
            | none => none
            | some metadata =>
              some ⟨{ s with token := burned, accounting := accounted },
                mintData r burned metadata⟩
          else none
      else none
  else none

/-- The accounting hook does not read the token's configuration (vault, origin token, asset id):
changing it changes nothing. The deployed hook, `_handleBridgeToChain` →
`L2AssetTracker.handleInitiateBridgingOnL2` (`bridge/ntv/L2NativeTokenVault.sol:296-302`,
`bridge/asset-tracker/L2AssetTracker.sol:221-250, :309-340`), reads the token only through
`totalSupply()` and `balanceOf`, never `nativeTokenVault()` or `assetId()`. -/
def HookIgnoresTokenConfig (hooks : Hooks Accounting) : Prop :=
  ∀ (acc : Accounting) (tok : BridgedStandardERC20.State) (cfg : BridgedStandardERC20.Config)
    (chain asset amount : UInt256),
    hooks.account acc { tok with config := cfg } chain asset amount =
      hooks.account acc tok chain asset amount

end Contracts.NativeTokenVaultBase
