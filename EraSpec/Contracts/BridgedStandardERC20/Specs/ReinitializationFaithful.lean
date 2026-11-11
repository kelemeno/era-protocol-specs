import EraSpec.Contracts.BridgedStandardERC20.Specs.Reinitialization
import EraSpec.Contracts.BridgedStandardERC20.Specs.LegacyFallback

/-!
# BridgedStandardERC20: the token's runs, with both branches of `onlyNTV`

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`,
`l1-contracts/contracts/bridge/BridgedStandardERC20.sol` (cited as `:N`). At `e561b9cc2` the
file differs from the pin in comments only, so the code read here is the same there.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.BridgedStandardERC20.Properties.ReinitializationFaithful` and are proved in
`EraSpec.Contracts.BridgedStandardERC20.Proofs.ReinitializationFaithful`.

## What `StorageStep` leaves out

`StorageStep` (`Specs/Reinitialization.lean`) takes its `bridgeMint` and `bridgeBurn` steps from
the nonlegacy ledger model `Step`, whose `MintAllowed` and `BurnAllowed` require a nonzero vault
(`Specs/Model.lean`). So on storage whose `nativeTokenVault` slot is zero it has no bridge call.
The token has one. `onlyNTV` (:52-64) first runs

    if (ntv == address(0)) {
        ntv = L2_NATIVE_TOKEN_VAULT_ADDR;
        nativeTokenVault = L2_NATIVE_TOKEN_VAULT_ADDR;                                 // :56
        assetId = DataEncoding.encodeNTVAssetId(
            L2NativeTokenVault(L2_NATIVE_TOKEN_VAULT_ADDR).L1_CHAIN_ID(), originToken); // :57-60
    }

and only then `require(msg.sender == ntv)` (:62). So a call by the L2 vault passes that check, and
when its mint or burn succeeds the call commits both writes. A nonzero version does not rule this
branch out. Storage with a nonzero version and a zero vault slot arises in three ways:

* a legacy token, which the modifier's NatSpec places on L2s (:50-51). It was initialized by code
  that did not write `nativeTokenVault`, so its `_initialized` slot is nonzero and its vault slot
  is zero;
* a fresh proxy after the beacon owner's `reinitializeToken(…, 1)`, at version 1
  (`Properties.ReinitializeOnFreshProxyBlocksBridgeInitialize`);
* a fresh proxy after `bridgeInitialize` with `msg.sender == address(0)`, which writes that
  sender to the vault slot (:90).

So `Properties.InitializedIdentityIsFixed`, whose only premise is a nonzero version, is a
statement about `StorageStep`'s runs, not about the token's.

## The refined model

`LegacyStorageStep env` is `StorageStep` with the ledger constructor's `Step` replaced by
`LegacyStep env` (`Specs/LegacyFallback.lean`). There `bridgeMint` and `bridgeBurn` are the
`onlyNTV` prologue `legacyFallback` followed by the nonlegacy `mint` and `burn`, and `transfer`
is unchanged. `bridgeInitialize` and `reinitializeToken` are the same calls on the same storage
as in `StorageStep`.

* `env : LegacyEnv` is what `L1_CHAIN_ID()` returns, together with the encoder
  `encodeNTVAssetId`. As in `LegacyFallback`, it is fixed for a run and the call is assumed not
  to revert (`MODEL-LEGACY`, `DEP-RESULTS`). No property of the encoder is assumed. From a nonzero
  version the prologue commits at most once on a run: until it does the identity is the starting
  one, and afterwards the vault is nonzero and the identity is fixed
  (`Properties.InitializedIdentityFixedOrFallback`,
  `Properties.InitializedNonlegacyIdentityIsFixed`). So on such a run only one committed call
  reads `L1_CHAIN_ID()`.
* A failed call is `none` and commits nothing, the prologue's writes included (`VM-REVERT`,
  `MODEL-COMMIT`).
* `LegacyStorageCallStep` and `LegacyStorageRun` are the same runs, labelled with the
  `StorageCall` of each call, as `StorageCallStep` and `StorageRun` are for `StorageStep`.

Still outside the model, as in `Specs/Reinitialization.lean`: a beacon `upgradeTo`, allowances
and permit signatures, events, and `_initializing`.
-/

namespace Contracts.BridgedStandardERC20

/-- One successful call of a modelled entry point, with both branches of `onlyNTV`:
`StorageStep` with `LegacyStep env` as its ledger step. -/
inductive LegacyStorageStep (env : LegacyEnv) : TokenStorage → TokenStorage → Prop
  /-- `bridgeInitialize` by any caller, as in `StorageStep`. -/
  | bridgeInitialize {s t : TokenStorage} {caller : Address} {assetId : UInt256}
      {originToken : Address} {decoded : Option Metadata} :
      initializeStorage s caller assetId originToken decoded = some t →
      LegacyStorageStep env s t
  /-- `reinitializeToken` by any caller, whatever the beacon reports as its owner, as in
  `StorageStep`. -/
  | reinitialize {s t : TokenStorage} {beaconOwner : Option Address} {caller : Address}
      {getters : Getters} {name symbol : Text} {version : UInt8} :
      reinitializeToken beaconOwner s caller getters name symbol version = some t →
      LegacyStorageStep env s t
  /-- `bridgeMint` or `bridgeBurn` through either branch of `onlyNTV` (:52-64), or `transfer`:
  a `LegacyStep`. On a zero vault slot the bridge calls run the prologue (:54-61) first. -/
  | ledger {s : TokenStorage} {token : State} :
      LegacyStep env s.token token → LegacyStorageStep env s { s with token := token }

/-- Any number of `LegacyStorageStep`s, all with the same environment. -/
inductive LegacyStorageReach (env : LegacyEnv) : TokenStorage → TokenStorage → Prop
  | refl {s} : LegacyStorageReach env s s
  | tail {s t u} : LegacyStorageReach env s t → LegacyStorageStep env t u →
      LegacyStorageReach env s u

/-- `LegacyStorageStep`, labelled with the entry point it used. -/
inductive LegacyStorageCallStep (env : LegacyEnv) :
    TokenStorage → StorageCall → TokenStorage → Prop
  | bridgeInitialize {s t : TokenStorage} {caller : Address} {assetId : UInt256}
      {originToken : Address} {decoded : Option Metadata} :
      initializeStorage s caller assetId originToken decoded = some t →
      LegacyStorageCallStep env s .bridgeInitialize t
  | reinitialize {s t : TokenStorage} {beaconOwner : Option Address} {caller : Address}
      {getters : Getters} {name symbol : Text} {version : UInt8} :
      reinitializeToken beaconOwner s caller getters name symbol version = some t →
      LegacyStorageCallStep env s .reinitializeToken t
  | ledger {s : TokenStorage} {token : State} :
      LegacyStep env s.token token →
      LegacyStorageCallStep env s .ledger { s with token := token }

/-- A run of `LegacyStorageCallStep`s, with the list of entry points its calls used, in order. -/
inductive LegacyStorageRun (env : LegacyEnv) :
    TokenStorage → List StorageCall → TokenStorage → Prop
  | nil {s} : LegacyStorageRun env s [] s
  | cons {s t u : TokenStorage} {call : StorageCall} {calls : List StorageCall} :
      LegacyStorageCallStep env s call t → LegacyStorageRun env t calls u →
      LegacyStorageRun env s (call :: calls) u

end Contracts.BridgedStandardERC20
