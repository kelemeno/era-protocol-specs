import EraSpec.Contracts.BridgedStandardERC20.Specs.ReinitializationStrong

/-!
# Properties: the token's identity along runs with both branches of `onlyNTV`

Statements about `EraSpec.Contracts.BridgedStandardERC20.Specs.ReinitializationStrong`. Proofs are
in `EraSpec.Contracts.BridgedStandardERC20.Proofs.ReinitializationStrong`.

`InitializedIdentityIsFixed` and `FreshProxyLifecycle` (`Properties/Reinitialization.lean`) are
stated over `StorageReach`, whose bridge calls all revert on a zero vault. With a zero vault they
hold only for that reason: on the deployed token the L2 vault's first `bridgeMint` or `bridgeBurn`
there takes the legacy branch of `onlyNTV` (:54-61) and rewrites the vault and the asset id. This
file states them over the deployed token's runs (`DeployedStorageReach`), which add that branch.

## What holds

* **The deployed runs extend the modelled ones** (`DeployedRunsIncludeModelledRuns`), keep the
  ledger invariant and never lower the version (`DeployedRunsPreserveLedger`). From a state with a
  nonzero version and a nonzero vault they are exactly the modelled runs
  (`DeployedRunsAreModelledOnceVaultSet`), so every `StorageReach` result from such a state holds
  for the deployed token.
* **`InitializedIdentityIsFixed`, repaired:** with a nonzero version *and a nonzero vault*, the
  identity never changes along a deployed run (`DeployedInitializedIdentityIsFixed`). Without the
  vault premise, it changes at most once, and only to the fallback configuration computed from the
  stored origin token (`DeployedInitializedIdentityAtMostFallback`).
* **`FreshProxyLifecycle`, repaired:** after `bridgeInitialize` on a fresh proxy by a *nonzero*
  caller (the vault, in the deployment flow) the deployed runs are the modelled runs
  (`DeployedFreshProxyRunsAreModelled`), so the identity is for ever the one bound, the ledger is
  `WellFormed` and `bridgeInitialize` stays closed (`DeployedFreshProxyLifecycle`). For any caller,
  the identity is the bound one or, only for caller `0`, the fallback's
  (`DeployedFreshProxyLifecycleAnyCaller`).

## Countermodels: without the premises, the readings are false

* On every storage with a zero vault, whatever its version, ledger and metadata, the L2 vault's
  zero-amount `bridgeBurn` succeeds and changes the identity, and nothing else
  (`DeployedZeroVaultIdentityRewritten`). So, for every environment, the identity is not fixed
  along deployed runs from a nonzero version without a nonzero vault
  (`DeployedIdentityNotFixedWithoutVault`). One such storage is left by the beacon owner's
  `reinitializeToken(…, 1)` on a fresh proxy, whoever that owner is
  (`DeployedReinitOnFreshProxyIdentity`, the deployed counterpart of
  `ReinitializeOnFreshProxyBlocksBridgeInitialize`); no zero caller is needed.
* `bridgeInitialize` by caller `0` succeeds on a fresh proxy, and the next bridge call by the L2
  vault replaces the bound vault and asset id (`DeployedFreshProxyZeroCallerRewritten`). So, for
  every environment, the identity `bridgeInitialize` bound does not last along deployed runs
  without a nonzero caller (`DeployedFreshProxyLifecycleNeedsNonzeroCaller`). In the deployment
  flow the caller is the vault, so this case is not expected there; `FreshProxyLifecycle` had no
  premise excluding it.

`DeployedLifecycleWitness` shows the premises are satisfiable, with a run that changes the storage.
No property of the asset-id encoder `env.assetIdFor` is assumed anywhere.
-/

namespace Contracts.BridgedStandardERC20

/-! ## The deployed runs and the modelled runs -/

/-- **EVERY MODELLED RUN IS A RUN OF THE DEPLOYED TOKEN.** For every environment, a `StorageReach`
run is a `DeployedStorageReach` run. So the statements below, which are about every deployed run,
cover every modelled run too. -/
def Properties.DeployedRunsIncludeModelledRuns : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), StorageReach s t → DeployedStorageReach env s t

/-- **THE DEPLOYED RUNS KEEP THE LEDGER INVARIANT.** Along any run of the deployed token, both
`onlyNTV` branches included, `WellFormed` is kept and the version never decreases. -/
def Properties.DeployedRunsPreserveLedger : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), WellFormed s.token → DeployedStorageReach env s t →
    WellFormed t.token ∧ s.version.toNat ≤ t.version.toNat

/-- **ONCE INITIALIZED WITH A NONZERO VAULT, THE DEPLOYED RUNS ARE THE MODELLED RUNS.** From a
storage with a nonzero version and a nonzero vault, the deployed token's runs are exactly the
`StorageReach` runs: the legacy branch of `onlyNTV` never runs, so every `StorageReach` result from
such a storage holds for the deployed token. -/
def Properties.DeployedRunsAreModelledOnceVaultSet : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), s.version ≠ 0 → s.token.config.vault ≠ 0 →
    (DeployedStorageReach env s t ↔ StorageReach s t)

/-! ## `InitializedIdentityIsFixed`, on the deployed token -/

/-- **ONCE INITIALIZED WITH A NONZERO VAULT, THE IDENTITY IS FIXED.** From any storage with a
nonzero version and a nonzero vault, along any run of the deployed token (both `onlyNTV`
branches), the vault, the asset id and the origin token never change, and the version stays
nonzero. No ledger premise. The vault premise cannot be dropped
(`DeployedIdentityNotFixedWithoutVault`). -/
def Properties.DeployedInitializedIdentityIsFixed : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), s.version ≠ 0 → s.token.config.vault ≠ 0 →
    DeployedStorageReach env s t → t.token.config = s.token.config ∧ t.version ≠ 0

/-- **ONCE INITIALIZED, THE IDENTITY CHANGES AT MOST ONCE, AND ONLY TO THE FALLBACK'S.** From any
storage with a nonzero version, along any run of the deployed token, the version stays nonzero and
the identity is the starting one or, only if the starting vault is zero, `fallbackConfig`: the L2
vault, the starting origin token, and `encodeNTVAssetId(L1_CHAIN_ID, originToken)`. That vault is
nonzero, so from a storage with the fallback identity `DeployedInitializedIdentityIsFixed` applies:
the identity changes at most once. No ledger premise. -/
def Properties.DeployedInitializedIdentityAtMostFallback : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), s.version ≠ 0 → DeployedStorageReach env s t →
    (t.token.config = s.token.config ∨
      (s.token.config.vault = 0 ∧ t.token.config = fallbackConfig env s.token.config)) ∧
    t.version ≠ 0

/-- **ON A ZERO VAULT, ONE BRIDGE CALL REWRITES THE IDENTITY.** On every storage whose vault slot is
zero, whatever its version, ledger and metadata, the L2 vault's `bridgeBurn` of zero tokens from
any nonzero account succeeds on the deployed token. It leaves the balances, the supply, the version
and the metadata as they were and replaces the identity by `fallbackConfig`, which differs from it
(its vault is the L2 vault). -/
def Properties.DeployedZeroVaultIdentityRewritten : Prop :=
  ∀ (env : LegacyEnv) (s : TokenStorage) (owner : Address), s.token.config.vault = 0 →
    owner ≠ 0 →
    bridgeBurn env s.token l2NativeTokenVaultAddr owner 0 =
      some { s.token with config := fallbackConfig env s.token.config } ∧
    DeployedStorageStep env s
      { s with token := { s.token with config := fallbackConfig env s.token.config } } ∧
    fallbackConfig env s.token.config ≠ s.token.config

/-- **WITHOUT A NONZERO VAULT THE IDENTITY IS NOT FIXED.** For every environment, the conclusion
of `InitializedIdentityIsFixed` fails for the deployed token: some storage with a nonzero version
has a deployed run that changes its identity. -/
def Properties.DeployedIdentityNotFixedWithoutVault : Prop :=
  ∀ env : LegacyEnv, ¬ ∀ s t : TokenStorage, s.version ≠ 0 → DeployedStorageReach env s t →
    t.token.config = s.token.config

/-- **A REINITIALIZED FRESH PROXY BECOMES A LEGACY TOKEN.** The beacon owner's
`reinitializeToken(…, 1)` on a fresh proxy succeeds, whoever the owner is (as in
`ReinitializeOnFreshProxyBlocksBridgeInitialize`). Along every deployed run after it,
`bridgeInitialize` never succeeds and the identity is the zero one or `fallbackConfig` of it (the
L2 vault, origin token `0`, asset id `encodeNTVAssetId(L1_CHAIN_ID, 0)`). A deployed step does
install the latter (the L2 vault's zero-amount `bridgeBurn`), so the identity changes although the
version is nonzero and no call came from address `0` (for a nonzero owner). -/
def Properties.DeployedReinitOnFreshProxyIdentity : Prop :=
  ∀ (env : LegacyEnv) (owner : Address) (getters : Getters) (name symbol : Text),
    ∃ s, reinitializeToken (some owner) freshStorage owner getters name symbol 1 = some s ∧
      (∀ t, DeployedStorageReach env s t →
        (t.token.config = ⟨0, 0, 0⟩ ∨ t.token.config = fallbackConfig env ⟨0, 0, 0⟩) ∧
        ∀ (caller : Address) (assetId : UInt256) (originToken : Address)
          (decoded : Option Metadata),
          initializeStorage t caller assetId originToken decoded = none) ∧
      ∃ t, DeployedStorageStep env s t ∧ t.token.config = fallbackConfig env ⟨0, 0, 0⟩ ∧
        t.token.config ≠ s.token.config

/-! ## `FreshProxyLifecycle`, on the deployed token -/

/-- **AFTER A NONZERO-CALLER `bridgeInitialize`, THE DEPLOYED RUNS ARE THE MODELLED RUNS.** After a
successful `bridgeInitialize` on a fresh proxy by a nonzero caller (the vault, in the deployment
flow), the legacy branch of `onlyNTV` never runs: the deployed token's runs from there are exactly
the `StorageReach` runs. -/
def Properties.DeployedFreshProxyRunsAreModelled : Prop :=
  ∀ (env : LegacyEnv) (caller : Address) (assetId : UInt256) (originToken : Address)
    (metadata : Metadata) (s t : TokenStorage),
    caller ≠ 0 →
    initializeStorage freshStorage caller assetId originToken (some metadata) = some s →
    (DeployedStorageReach env s t ↔ StorageReach s t)

/-- **A FRESH PROXY'S IDENTITY IS THE ONE A NONZERO CALLER'S `bridgeInitialize` BOUND, FOR EVER.**
After a successful `bridgeInitialize` on a fresh proxy by a nonzero caller and any run of the
deployed token after it (both `onlyNTV` branches), the vault is that call's caller, the asset id
and origin token are its arguments, the ledger is `WellFormed`, and no `bridgeInitialize` can
succeed. The caller premise cannot be dropped (`DeployedFreshProxyLifecycleNeedsNonzeroCaller`). -/
def Properties.DeployedFreshProxyLifecycle : Prop :=
  ∀ (env : LegacyEnv) (caller : Address) (assetId : UInt256) (originToken : Address)
    (metadata : Metadata) (s t : TokenStorage),
    caller ≠ 0 →
    initializeStorage freshStorage caller assetId originToken (some metadata) = some s →
    DeployedStorageReach env s t →
    t.token.config = ⟨caller, originToken, assetId⟩ ∧ WellFormed t.token ∧
    ∀ (caller' : Address) (assetId' : UInt256) (originToken' : Address)
      (decoded : Option Metadata),
      initializeStorage t caller' assetId' originToken' decoded = none

/-- **FOR ANY CALLER: THE BOUND IDENTITY OR, FOR CALLER `0` ONLY, THE FALLBACK'S.** After a
successful `bridgeInitialize` on a fresh proxy and any run of the deployed token after it, the
identity is the one bound or, only if the caller was `0`, the L2 vault with the bound origin
token and the asset id `encodeNTVAssetId(L1_CHAIN_ID, originToken)` in place of the bound one;
the ledger is `WellFormed` and no `bridgeInitialize` can succeed. -/
def Properties.DeployedFreshProxyLifecycleAnyCaller : Prop :=
  ∀ (env : LegacyEnv) (caller : Address) (assetId : UInt256) (originToken : Address)
    (metadata : Metadata) (s t : TokenStorage),
    initializeStorage freshStorage caller assetId originToken (some metadata) = some s →
    DeployedStorageReach env s t →
    (t.token.config = ⟨caller, originToken, assetId⟩ ∨
      (caller = 0 ∧ t.token.config =
        ⟨l2NativeTokenVaultAddr, originToken, env.assetIdFor env.l1ChainId originToken⟩)) ∧
    WellFormed t.token ∧
    ∀ (caller' : Address) (assetId' : UInt256) (originToken' : Address)
      (decoded : Option Metadata),
      initializeStorage t caller' assetId' originToken' decoded = none

/-- **WITH CALLER `0`, THE BOUND IDENTITY IS REPLACED BY THE NEXT BRIDGE CALL.** For every
environment, asset id, nonzero origin token and decoded metadata, `bridgeInitialize` by caller `0`
on a fresh proxy succeeds, and one deployed step after it (the L2 vault's zero-amount
`bridgeBurn`) installs the L2 vault and `encodeNTVAssetId(L1_CHAIN_ID, originToken)`, which is not
the identity that call bound. -/
def Properties.DeployedFreshProxyZeroCallerRewritten : Prop :=
  ∀ (env : LegacyEnv) (assetId : UInt256) (originToken : Address) (metadata : Metadata),
    originToken ≠ 0 →
    ∃ s t, initializeStorage freshStorage 0 assetId originToken (some metadata) = some s ∧
      DeployedStorageStep env s t ∧
      t.token.config =
        ⟨l2NativeTokenVaultAddr, originToken, env.assetIdFor env.l1ChainId originToken⟩ ∧
      t.token.config ≠ ⟨0, originToken, assetId⟩

/-- **WITHOUT A NONZERO CALLER THE BOUND IDENTITY DOES NOT LAST.** For every environment, the
identity conclusion of `FreshProxyLifecycle` fails for the deployed token: some successful
`bridgeInitialize` on a fresh proxy is followed by a deployed run that changes the identity it
bound. -/
def Properties.DeployedFreshProxyLifecycleNeedsNonzeroCaller : Prop :=
  ∀ env : LegacyEnv, ¬ ∀ (caller : Address) (assetId : UInt256) (originToken : Address)
    (metadata : Metadata) (s t : TokenStorage),
    initializeStorage freshStorage caller assetId originToken (some metadata) = some s →
    DeployedStorageReach env s t → t.token.config = ⟨caller, originToken, assetId⟩

/-! ## Witness -/

/-- **THE PREMISES ARE SATISFIABLE.** For every environment: `bridgeInitialize` on a fresh proxy by
the nonzero caller `1`, for asset `5` and origin token `9`, gives a storage with a nonzero version,
a nonzero vault and a `WellFormed` ledger; from it some deployed run reaches a storage at version
2 with one unit in circulation and the identity it started with (the proof uses the vault's
one-unit `bridgeMint` to account `4`, then the beacon owner `7`'s reinitialization to version 2;
the statement names only the run's endpoints). And
`bridgeInitialize` by caller `0` with the same arguments succeeds, at a nonzero version with a
zero vault (the premise of `DeployedZeroVaultIdentityRewritten`). -/
def Properties.DeployedLifecycleWitness : Prop :=
  ∀ env : LegacyEnv, ∃ s t : TokenStorage,
    initializeStorage freshStorage 1 5 9 (some emptyMetadata) = some s ∧
    s.version ≠ 0 ∧ s.token.config.vault ≠ 0 ∧ WellFormed s.token ∧
    DeployedStorageReach env s t ∧ t.version = 2 ∧ t.token.totalSupply = 1 ∧
    t.token.config = ⟨1, 9, 5⟩ ∧
    ∃ s₀, initializeStorage freshStorage 0 5 9 (some emptyMetadata) = some s₀ ∧
      s₀.version ≠ 0 ∧ s₀.token.config.vault = 0

end Contracts.BridgedStandardERC20
