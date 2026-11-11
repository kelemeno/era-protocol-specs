import EraSpec.Contracts.BridgedStandardERC20.Specs.Reinitialization
import EraSpec.Contracts.BridgedStandardERC20.Specs.LegacyFallback

/-!
# BridgedStandardERC20: every modelled entry point, with both branches of `onlyNTV`

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`,
`l1-contracts/contracts/bridge/BridgedStandardERC20.sol` (cited as `:N`).

**This file is definitions only.** The results are in
`EraSpec.Contracts.BridgedStandardERC20.Properties.ReinitializationStrong` and are proved in
`EraSpec.Contracts.BridgedStandardERC20.Proofs.ReinitializationStrong`.

## Why another step relation

`StorageStep` (`Specs/Reinitialization.lean`) takes its `bridgeMint` and `bridgeBurn` from the
nonlegacy ledger `Step`, whose `mint` and `burn` require a nonzero vault. On a state whose
`nativeTokenVault` slot is zero it therefore has no bridge call at all, while the deployed token's
`onlyNTV` (:52-64) runs its legacy prologue there (:54-61): it writes `nativeTokenVault :=
L2_NATIVE_TOKEN_VAULT_ADDR` and `assetId := encodeNTVAssetId(L1_CHAIN_ID(), originToken)` and then
lets the L2 vault mint or burn. Such states arise at a nonzero version: `bridgeInitialize` has no
caller guard and records its caller, which may be `0`, as the vault (:90), and a
`reinitializeToken` at version 1 on a fresh proxy leaves the vault zero
(`Properties.ReinitializeOnFreshProxyBlocksBridgeInitialize`). The legacy tokens the branch exists
for (:50-51) were initialized before the vault slot was written, so they are expected to be in
such a state as well; their history before the implementation upgrade is not modelled.

`DeployedStorageStep env` is `StorageStep` with its ledger calls taken from `LegacyStep env`
(`Specs/LegacyFallback.lean`) instead: `bridgeMint` and `bridgeBurn` run the `onlyNTV` prologue and
then the nonlegacy `mint` / `burn` on its result, and `transfer` is unchanged. `bridgeInitialize`
and `reinitializeToken` are the same calls as in `StorageStep`, and neither reads the vault slot.

## Modelling choices

* `env : LegacyEnv` is fixed for a run, as in `Specs/LegacyFallback.lean`: it is what
  `L2NativeTokenVault(L2_NATIVE_TOKEN_VAULT_ADDR).L1_CHAIN_ID()` returns and the
  `encodeNTVAssetId` encoder. No property of the encoder is assumed.
* Every other choice (`TokenStorage`, the revert-is-`none` convention, the arbitrary beacon-owner
  answer, `_initializing` not modelled) is that of `Specs/Reinitialization.lean`.
* The legacy branch does not look at the version, so on a fresh proxy (version 0) the L2 vault's
  bridge calls also succeed before any `bridgeInitialize`, as they would on the deployed token.
  The vault's atomic deploy-and-initialize (`NativeTokenVaultBase.sol:629-630`) keeps such calls
  out of the deployment flow; the statements about these runs start at a nonzero version or right
  after `bridgeInitialize`.
* Still outside the model: a beacon `upgradeTo`, permits and allowances, events.
-/

namespace Contracts.BridgedStandardERC20

/-- One successful call of a modelled entry point of the deployed token: `StorageStep`, with
`bridgeMint` and `bridgeBurn` running both branches of `onlyNTV` (:52-64). -/
inductive DeployedStorageStep (env : LegacyEnv) : TokenStorage → TokenStorage → Prop
  /-- `bridgeInitialize` by any caller. -/
  | bridgeInitialize {s t : TokenStorage} {caller : Address} {assetId : UInt256}
      {originToken : Address} {decoded : Option Metadata} :
      initializeStorage s caller assetId originToken decoded = some t →
      DeployedStorageStep env s t
  /-- `reinitializeToken` by any caller, whatever the beacon reports as its owner. -/
  | reinitialize {s t : TokenStorage} {beaconOwner : Option Address} {caller : Address}
      {getters : Getters} {name symbol : Text} {version : UInt8} :
      reinitializeToken beaconOwner s caller getters name symbol version = some t →
      DeployedStorageStep env s t
  /-- `bridgeMint` or `bridgeBurn` with the `onlyNTV` prologue, or `transfer`, as `LegacyStep`. -/
  | ledger {s : TokenStorage} {token : State} :
      LegacyStep env s.token token → DeployedStorageStep env s { s with token := token }

/-- Any number of `DeployedStorageStep`s. -/
inductive DeployedStorageReach (env : LegacyEnv) : TokenStorage → TokenStorage → Prop
  | refl {s} : DeployedStorageReach env s s
  | tail {s t u} : DeployedStorageReach env s t → DeployedStorageStep env t u →
      DeployedStorageReach env s u

end Contracts.BridgedStandardERC20
