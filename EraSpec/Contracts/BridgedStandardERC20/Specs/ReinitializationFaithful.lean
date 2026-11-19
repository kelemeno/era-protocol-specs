import EraSpec.Contracts.BridgedStandardERC20.Specs.ReinitializationStrong

/-!
# BridgedStandardERC20: the deployed token's runs, labelled call by call

Source: era-contracts `draft/v0.35.0` head `b17415d20`,
`l1-contracts/contracts/bridge/BridgedStandardERC20.sol` (cited as `:N`). The token has the same code
at the old interop pin `c67894b9` and at `main` `70096e2ea`, with rewritten comments there.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.BridgedStandardERC20.Properties.ReinitializationFaithful` and are proved in
`EraSpec.Contracts.BridgedStandardERC20.Proofs.ReinitializationFaithful`.

## What this file is for

`Specs/Reinitialization.lean` counts calls along `StorageRun`, whose `bridgeMint` and `bridgeBurn`
are only the nonlegacy branch of `onlyNTV`: on a zero vault slot it has no bridge call, where the
deployed token runs the legacy branch (:51-58). `Specs/ReinitializationStrong.lean` adds that
branch (`DeployedStorageStep`, `DeployedStorageReach`) and restates the identity results over it.
The counting results (`VersionCountsInitializations`, `LifetimeVersionCallBound`,
`LifetimeBoundIsTight`, `BridgeInitializeAtMostOnce`) remain statements about `StorageRun`. This
file labels the deployed runs call by call, so that those results, and the number of calls that
take the legacy branch, can be stated over them.

## The labels

* `DeployedStorageCall` records the entry point of a successful call and, for `bridgeMint` and
  `bridgeBurn`, the branch of `onlyNTV` it took. The branch is decided by the vault slot when the
  call starts (`address ntv = nativeTokenVault; if (ntv == address(0))`, :50-51), so the label of
  a bridge call is a function of the storage it starts from (`deployedBridgeCallLabel`).
* A step labelled `legacyBridgeCall` is a successful call that ran the legacy branch: it called
  `L2NativeTokenVault(L2_NATIVE_TOKEN_VAULT_ADDR).L1_CHAIN_ID()` (:55), and its writes to the vault
  and asset-id slots (:53-57) were committed with it. A call that reverts is not a step and has no
  label: its writes are rolled back (`VM-REVERT`, `MODEL-COMMIT`).
* `DeployedStorageCall.entryPoint` drops the branch and maps the three ledger labels to
  `StorageCall.ledger`, so `versionCalls` and `initializeCalls` (`Specs/Reinitialization.lean`)
  count a deployed run through it. `legacyBranchCalls` counts the `legacyBridgeCall` labels.
* `DeployedStorageCallStep env` is `DeployedStorageStep env` with a label: `bridgeInitialize` and
  `reinitializeToken` as there, and its ledger step split into the three `LegacyStep` calls
  (`Specs/LegacyFallback.lean`). `DeployedStorageRun env` chains such steps, with one `env` for the
  whole run, and records their labels in order.

The modelling choices are those of `Specs/ReinitializationStrong.lean`: `env` is what
`L1_CHAIN_ID()` returns and the `encodeNTVAssetId` encoder, fixed for the run (`MODEL-LEGACY`);
`bridgeInitialize` and `reinitializeToken` take any caller and any beacon-owner answer;
`_initializing` is not modelled; a beacon `upgradeTo`, permits, allowances and events are outside
the model.
-/

namespace Contracts.BridgedStandardERC20

/-- The entry point of one successful call of the deployed token and, for `bridgeMint` and
`bridgeBurn`, the branch of `onlyNTV` it took. -/
inductive DeployedStorageCall
  /-- `bridgeInitialize` (:82-130). -/
  | bridgeInitialize
  /-- `reinitializeToken` (:139-155). -/
  | reinitializeToken
  /-- `bridgeMint` (:158-161) or `bridgeBurn` (:164-167) started on a nonzero vault slot:
  `onlyNTV` only checks the caller (:59). -/
  | bridgeCall
  /-- `bridgeMint` or `bridgeBurn` started on a zero vault slot: `onlyNTV`'s legacy branch
  (:51-58) ran, calling `L1_CHAIN_ID()` and writing the vault and asset-id slots. -/
  | legacyBridgeCall
  /-- `transfer`, which does not pass through `onlyNTV`. Its arbitrary owner also covers the
  ledger effect of `transferFrom`. -/
  | transfer
deriving DecidableEq

/-- The label of a successful `bridgeMint` or `bridgeBurn` that starts on storage `s`: the legacy
branch exactly when the vault slot is zero (:50-51). -/
def deployedBridgeCallLabel (s : TokenStorage) : DeployedStorageCall :=
  if s.token.config.vault = 0 then .legacyBridgeCall else .bridgeCall

/-- The `StorageCall` of a call: its entry point, with `bridgeMint`, `bridgeBurn` and `transfer`
all the `ledger` entry point, as in `StorageCallStep`. -/
def DeployedStorageCall.entryPoint : DeployedStorageCall → StorageCall
  | .bridgeInitialize => .bridgeInitialize
  | .reinitializeToken => .reinitializeToken
  | .bridgeCall => .ledger
  | .legacyBridgeCall => .ledger
  | .transfer => .ledger

/-- `DeployedStorageStep`, labelled with the call it made. -/
inductive DeployedStorageCallStep (env : LegacyEnv) :
    TokenStorage → DeployedStorageCall → TokenStorage → Prop
  /-- `bridgeInitialize` by any caller, as in `DeployedStorageStep`. -/
  | bridgeInitialize {s t : TokenStorage} {caller : Address} {assetId : UInt256}
      {originToken : Address} {decoded : Option Metadata} :
      initializeStorage s caller assetId originToken decoded = some t →
      DeployedStorageCallStep env s .bridgeInitialize t
  /-- `reinitializeToken` by any caller, whatever the beacon reports as its owner, as in
  `DeployedStorageStep`. -/
  | reinitialize {s t : TokenStorage} {beaconOwner : Option Address} {caller : Address}
      {getters : Getters} {name symbol : Text} {version : UInt8} :
      reinitializeToken beaconOwner s caller getters name symbol version = some t →
      DeployedStorageCallStep env s .reinitializeToken t
  /-- `bridgeMint` through `onlyNTV`, either branch (`LegacyStep.bridgeMint`). -/
  | bridgeMint {s : TokenStorage} {token : State} {caller recipient : Address}
      {amount : UInt256} :
      bridgeMint env s.token caller recipient amount = some token →
      DeployedStorageCallStep env s (deployedBridgeCallLabel s) { s with token := token }
  /-- `bridgeBurn` through `onlyNTV`, either branch (`LegacyStep.bridgeBurn`). -/
  | bridgeBurn {s : TokenStorage} {token : State} {caller owner : Address} {amount : UInt256} :
      bridgeBurn env s.token caller owner amount = some token →
      DeployedStorageCallStep env s (deployedBridgeCallLabel s) { s with token := token }
  /-- `transfer` (`LegacyStep.transfer`, the nonlegacy model's `transfer`). -/
  | transfer {s : TokenStorage} {token : State} {owner recipient : Address} {amount : UInt256} :
      transfer s.token owner recipient amount = some token →
      DeployedStorageCallStep env s .transfer { s with token := token }

/-- A run of `DeployedStorageCallStep`s, all with the same environment, with the list of the
labels of its calls, in order. -/
inductive DeployedStorageRun (env : LegacyEnv) :
    TokenStorage → List DeployedStorageCall → TokenStorage → Prop
  | nil {s} : DeployedStorageRun env s [] s
  | cons {s t u : TokenStorage} {call : DeployedStorageCall} {calls : List DeployedStorageCall} :
      DeployedStorageCallStep env s call t → DeployedStorageRun env t calls u →
      DeployedStorageRun env s (call :: calls) u

/-- How many of the calls took `onlyNTV`'s legacy branch, and so called `L1_CHAIN_ID()`. -/
def legacyBranchCalls : List DeployedStorageCall → ℕ
  | [] => 0
  | .legacyBridgeCall :: calls => legacyBranchCalls calls + 1
  | .bridgeInitialize :: calls => legacyBranchCalls calls
  | .reinitializeToken :: calls => legacyBranchCalls calls
  | .bridgeCall :: calls => legacyBranchCalls calls
  | .transfer :: calls => legacyBranchCalls calls

end Contracts.BridgedStandardERC20
