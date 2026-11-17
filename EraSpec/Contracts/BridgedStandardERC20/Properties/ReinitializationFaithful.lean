import EraSpec.Contracts.BridgedStandardERC20.Specs.ReinitializationFaithful

/-!
# Properties: the token's runs, with both branches of `onlyNTV`

Statements about `EraSpec.Contracts.BridgedStandardERC20.Specs.ReinitializationFaithful`.
Proofs are in `EraSpec.Contracts.BridgedStandardERC20.Proofs.ReinitializationFaithful`. Every
statement holds for every `LegacyEnv`: nothing is assumed about the value `L1_CHAIN_ID()`
returns or about the encoder. There is no hash premise.

## The refinement

* It adds runs and removes none (`StorageReachIsLegacyStorageReach`,
  `StorageRunIsLegacyStorageRun`).
* From a nonzero version and a nonzero vault, the two models have exactly the same runs
  (`InitializedNonlegacyRunsAgree`). So from such storage every `Reinitialization` result about
  `StorageReach` is also a result about the token.

## `InitializedIdentityIsFixed`, read on the token

* On any storage with a zero vault slot, at any version, the L2 vault's `bridgeMint` succeeds
  when the supply leaves room. It installs `fallbackConfig`, which is a different identity
  (`LegacyBridgeCallRewritesIdentity`). So the statement of `InitializedIdentityIsFixed`, taken
  over these runs, is false for every environment
  (`InitializedIdentityIsFixedFailsOnLegacyTokens`).
* What holds instead, under the same premise: the identity is the starting one, or the
  fallback's if the vault started at zero, and the version stays nonzero
  (`InitializedIdentityFixedOrFallback`). Both cases occur, so the statement is exact. The origin
  token never changes (`InitializedOriginTokenIsFixed`). If the starting vault is also nonzero,
  the identity is fixed (`InitializedNonlegacyIdentityIsFixed`). This is
  `InitializedIdentityIsFixed` with the premise it needs.

## The other results about runs

* `RunsPreserveLedger`, `StorageRunsAreReach`, `VersionCountsInitializations`,
  `LifetimeVersionCallBound`, `LifetimeBoundIsTight` and `BridgeInitializeAtMostOnce` hold
  unchanged on the refined runs (`LegacyStorageRunsPreserveLedger`, `LegacyStorageRunsAreReach`,
  `LegacyVersionCountsInitializations`, `LegacyLifetimeVersionCallBound`,
  `LegacyLifetimeBoundIsTight`, `LegacyBridgeInitializeAtMostOnce`). The prologue writes neither
  the version nor the ledger.
* `FreshProxyLifecycle` needs a nonzero initializing caller
  (`FreshProxyLifecycleNonzeroCaller`). With caller zero, the L2 vault's first bridge call
  rewrites the identity that `bridgeInitialize` bound (`ZeroCallerInitializationTakesFallback`).
  In the deployment flow the caller is the vault, a contract, so it is nonzero.
* After the beacon owner reinitializes a fresh proxy to version 1, `bridgeInitialize` stays
  closed for ever. But the identity does not stay zero, and the L2 vault can mint
  (`ReinitializedFreshProxyTakesFallback`). `ReinitializeOnFreshProxyBlocksBridgeInitialize`
  says otherwise, but only of the `StorageStep` runs.

`LegacyStorageWitness` meets the premises of the statements above, on both branches.
-/

namespace Contracts.BridgedStandardERC20

/-! ## The refinement -/

/-- **EVERY `StorageStep` RUN IS A RUN OF THE TOKEN.** For every environment, the refined model
has every run of `StorageReach`. -/
def Properties.StorageReachIsLegacyStorageReach : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), StorageReach s t → LegacyStorageReach env s t

/-- **THE SAME, FOR LABELLED RUNS.** Every `StorageRun` is a `LegacyStorageRun` with the same
list of entry points. -/
def Properties.StorageRunIsLegacyStorageRun : Prop :=
  ∀ (env : LegacyEnv) (s : TokenStorage) (calls : List StorageCall) (t : TokenStorage),
    StorageRun s calls t → LegacyStorageRun env s calls t

/-- **FROM A NONZERO VERSION AND A NONZERO VAULT, THE TWO MODELS HAVE THE SAME RUNS.** From such
storage the prologue never runs: `bridgeInitialize` is closed, so nothing writes the vault slot
back to zero. -/
def Properties.InitializedNonlegacyRunsAgree : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), s.version ≠ 0 → s.token.config.vault ≠ 0 →
    (LegacyStorageReach env s t ↔ StorageReach s t)

/-! ## `InitializedIdentityIsFixed`, read on the token -/

/-- **ON A ZERO VAULT SLOT THE L2 VAULT'S FIRST BRIDGE CALL REWRITES THE IDENTITY, AT ANY
VERSION.** On any storage whose vault slot is zero, the L2 vault's `bridgeMint` to a nonzero
recipient succeeds when the supply leaves room. It keeps the version and the metadata, has the
nonlegacy mint effect on the ledger, and installs `fallbackConfig`: vault
`L2_NATIVE_TOKEN_VAULT_ADDR`, asset id `encodeNTVAssetId(L1_CHAIN_ID, originToken)`, origin token
unchanged. That identity differs from the starting one. `StorageStep` has no such step. -/
def Properties.LegacyBridgeCallRewritesIdentity : Prop :=
  ∀ (env : LegacyEnv) (s : TokenStorage) (recipient : Address) (amount : UInt256),
    s.token.config.vault = 0 → recipient ≠ 0 →
    s.token.totalSupply + amount.val < UInt256.size →
    ∃ t, LegacyStorageStep env s t ∧ t.version = s.version ∧ t.metadata = s.metadata ∧
      t.token = mintEffect { s.token with config := fallbackConfig env s.token.config }
        recipient amount ∧
      t.token.config = fallbackConfig env s.token.config ∧ t.token.config ≠ s.token.config

/-- **`InitializedIdentityIsFixed` IS FALSE OF THE TOKEN.** Take its statement and replace
`StorageReach` by the token's runs, `LegacyStorageReach env`. The result is false for every
environment. -/
def Properties.InitializedIdentityIsFixedFailsOnLegacyTokens : Prop :=
  ∀ env : LegacyEnv, ¬ ∀ s t : TokenStorage, s.version ≠ 0 → LegacyStorageReach env s t →
    t.token.config = s.token.config ∧ t.version ≠ 0

/-! ## What holds instead -/

/-- **ONCE THE VERSION IS NONZERO, THE IDENTITY IS THE STARTING ONE OR THE FALLBACK'S.** From any
storage with a nonzero version, along any run of the token, the vault, asset id and origin token
are those at the start, or, only if the vault started at zero, `fallbackConfig` computed from the
starting origin token. The version stays nonzero. No ledger premise. Both cases occur (the empty
run, and `LegacyBridgeCallRewritesIdentity`), so the statement is exact. Since `fallbackConfig`
has a nonzero vault, the identity changes at most once. -/
def Properties.InitializedIdentityFixedOrFallback : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), s.version ≠ 0 → LegacyStorageReach env s t →
    (t.token.config = s.token.config ∨
      (s.token.config.vault = 0 ∧ t.token.config = fallbackConfig env s.token.config)) ∧
    t.version ≠ 0

/-- **WITH A NONZERO VERSION AND A NONZERO VAULT, THE IDENTITY IS FIXED.** This is
`InitializedIdentityIsFixed` with the premise it needs, over the token's runs. From any storage
with a nonzero version and a nonzero vault, along any run, the vault, the asset id and the origin
token never change, and the version stays nonzero. -/
def Properties.InitializedNonlegacyIdentityIsFixed : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), s.version ≠ 0 → s.token.config.vault ≠ 0 →
    LegacyStorageReach env s t → t.token.config = s.token.config ∧ t.version ≠ 0

/-- **ONCE THE VERSION IS NONZERO, THE ORIGIN TOKEN NEVER CHANGES**, with no vault premise. -/
def Properties.InitializedOriginTokenIsFixed : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), s.version ≠ 0 → LegacyStorageReach env s t →
    t.token.config.originToken = s.token.config.originToken

/-! ## The other results about runs -/

/-- **`RunsPreserveLedger`, ON THE TOKEN'S RUNS.** Along any run with both `onlyNTV` branches,
`WellFormed` is kept and the version never decreases. -/
def Properties.LegacyStorageRunsPreserveLedger : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage), WellFormed s.token → LegacyStorageReach env s t →
    WellFormed t.token ∧ s.version.toNat ≤ t.version.toNat

/-- **`FreshProxyLifecycle`, ON THE TOKEN'S RUNS, FOR A NONZERO CALLER.** After a successful
`bridgeInitialize` on a fresh proxy by a nonzero caller, and any run after it, the vault is that
caller, the asset id and origin token are the call's arguments, the ledger is `WellFormed`, and no
`bridgeInitialize` can succeed. `ZeroCallerInitializationTakesFallback` shows that the caller
premise is needed. -/
def Properties.FreshProxyLifecycleNonzeroCaller : Prop :=
  ∀ (env : LegacyEnv) (caller : Address) (assetId : UInt256) (originToken : Address)
    (metadata : Metadata) (s t : TokenStorage), caller ≠ 0 →
    initializeStorage freshStorage caller assetId originToken (some metadata) = some s →
    LegacyStorageReach env s t →
    t.token.config = ⟨caller, originToken, assetId⟩ ∧ WellFormed t.token ∧
    ∀ (caller' : Address) (assetId' : UInt256) (originToken' : Address)
      (decoded : Option Metadata),
      initializeStorage t caller' assetId' originToken' decoded = none

/-- **WITH CALLER ZERO, THE BOUND IDENTITY DOES NOT LAST.** If `bridgeInitialize` on a fresh
proxy is called with `msg.sender == address(0)`, it succeeds, with any asset id and any nonzero
origin token. The L2 vault's one-unit `bridgeMint` to account `4` then succeeds and replaces the
bound identity `⟨0, originToken, assetId⟩` by `fallbackConfig`. So `FreshProxyLifecycle`'s
statement, over the token's runs, fails at caller zero. -/
def Properties.ZeroCallerInitializationTakesFallback : Prop :=
  ∀ (env : LegacyEnv) (assetId : UInt256) (originToken : Address) (metadata : Metadata),
    originToken ≠ 0 →
    ∃ s t, initializeStorage freshStorage 0 assetId originToken (some metadata) = some s ∧
      LegacyStorageStep env s t ∧
      t.token.config = fallbackConfig env ⟨0, originToken, assetId⟩ ∧
      t.token.config ≠ ⟨0, originToken, assetId⟩ ∧
      t.token.totalSupply = 1 ∧ WellFormed t.token

/-- **A FRESH PROXY REINITIALIZED AT VERSION 1: `bridgeInitialize` IS LOCKED OUT, THE L2 VAULT IS
NOT.** The beacon owner's `reinitializeToken(…, 1)` on a fresh proxy succeeds. Along every run of
the token after it, `bridgeInitialize` never succeeds, and the identity is zero or
`fallbackConfig env ⟨0, 0, 0⟩` (vault `L2_NATIVE_TOKEN_VAULT_ADDR`, origin token zero, asset id
`encodeNTVAssetId(L1_CHAIN_ID, 0)`). The L2 vault's one-unit `bridgeMint` succeeds there and
installs that identity. -/
def Properties.ReinitializedFreshProxyTakesFallback : Prop :=
  ∀ (env : LegacyEnv) (owner : Address) (getters : Getters) (name symbol : Text),
    ∃ t, reinitializeToken (some owner) freshStorage owner getters name symbol 1 = some t ∧
      (∀ u, LegacyStorageReach env t u →
        (u.token.config = ⟨0, 0, 0⟩ ∨ u.token.config = fallbackConfig env ⟨0, 0, 0⟩) ∧
        ∀ (caller : Address) (assetId : UInt256) (originToken : Address)
          (decoded : Option Metadata),
          initializeStorage u caller assetId originToken decoded = none) ∧
      ∃ u, LegacyStorageStep env t u ∧ u.token.config = fallbackConfig env ⟨0, 0, 0⟩ ∧
        u.token.totalSupply = 1

/-! ## Counting calls on the token's runs -/

/-- **THE LABELLED RUNS ARE THE RUNS.** -/
def Properties.LegacyStorageRunsAreReach : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage),
    LegacyStorageReach env s t ↔ ∃ calls, LegacyStorageRun env s calls t

/-- **`VersionCountsInitializations`, ON THE TOKEN'S RUNS.** Along any run, the version rises by
exactly the number of `bridgeInitialize` and `reinitializeToken` calls in it. -/
def Properties.LegacyVersionCountsInitializations : Prop :=
  ∀ (env : LegacyEnv) (s : TokenStorage) (calls : List StorageCall) (t : TokenStorage),
    LegacyStorageRun env s calls t → t.version.toNat = s.version.toNat + versionCalls calls

/-- **`LifetimeVersionCallBound`, ON THE TOKEN'S RUNS.** Along any run from a fresh proxy, at most
255 calls are `bridgeInitialize` or `reinitializeToken`. -/
def Properties.LegacyLifetimeVersionCallBound : Prop :=
  ∀ (env : LegacyEnv) (calls : List StorageCall) (t : TokenStorage),
    LegacyStorageRun env freshStorage calls t → versionCalls calls ≤ 255

/-- **`LifetimeBoundIsTight`, ON THE TOKEN'S RUNS.** For every environment, one
`bridgeInitialize` followed by 254 `reinitializeToken` calls all succeed from a fresh proxy,
ending at version 255. -/
def Properties.LegacyLifetimeBoundIsTight : Prop :=
  ∀ env : LegacyEnv, ∃ (calls : List StorageCall) (t : TokenStorage),
    LegacyStorageRun env freshStorage calls t ∧
    initializeCalls calls = 1 ∧ versionCalls calls = 255 ∧ t.version = 255

/-- **`BridgeInitializeAtMostOnce`, ON THE TOKEN'S RUNS.** `bridgeInitialize` succeeds at most
once in any run, and not at all in a run that starts at a nonzero version. -/
def Properties.LegacyBridgeInitializeAtMostOnce : Prop :=
  ∀ (env : LegacyEnv) (s : TokenStorage) (calls : List StorageCall) (t : TokenStorage),
    LegacyStorageRun env s calls t →
    initializeCalls calls ≤ 1 ∧ (s.version ≠ 0 → initializeCalls calls = 0)

/-! ## Witness -/

/-- **THE PREMISES ARE SATISFIABLE, ON BOTH BRANCHES.** For every environment:

* **Nonlegacy.** On a fresh proxy, `bridgeInitialize` by the vault `1` for asset `5` and origin
  token `9` gives storage with a nonzero version and a nonzero vault. From there, a run of the
  token (the vault's one-unit `bridgeMint` to account `4`, then the beacon owner `7`'s
  reinitialization to version 2) ends with identity `⟨1, 9, 5⟩`, version 2 and one unit in
  circulation. This meets the premises of `InitializedNonlegacyIdentityIsFixed`,
  `InitializedNonlegacyRunsAgree`, `FreshProxyLifecycleNonzeroCaller` and
  `LegacyStorageRunsPreserveLedger`.
* **Legacy.** Take `WellFormed` storage at version 1, with vault and asset-id slots zero, origin
  token `9`, and one unit held by account `4`. The nonlegacy model refuses the L2 vault's
  one-unit `bridgeBurn` from `4`. The token accepts it: the call installs `fallbackConfig` and
  empties the ledger. Then the beacon owner `7` reinitializes to version 2, and the identity
  stays the fallback's. This meets the premises of `InitializedIdentityFixedOrFallback` and
  `InitializedOriginTokenIsFixed` with the fallback case taken, and those of
  `LegacyBridgeCallRewritesIdentity` (recipient `4`, amount `1`). -/
def Properties.LegacyStorageWitness : Prop :=
  ∀ env : LegacyEnv,
    (∃ s t : TokenStorage,
      initializeStorage freshStorage 1 5 9 (some emptyMetadata) = some s ∧
      s.version ≠ 0 ∧ s.token.config.vault ≠ 0 ∧ WellFormed s.token ∧
      LegacyStorageReach env s t ∧
      t.version = 2 ∧ t.token.totalSupply = 1 ∧ t.token.config = ⟨1, 9, 5⟩) ∧
    (∃ s u t : TokenStorage,
      WellFormed s.token ∧ s.version = 1 ∧ s.token.config = ⟨0, 9, 0⟩ ∧
      s.token.balances 4 = 1 ∧ s.token.totalSupply + (1 : UInt256).val < UInt256.size ∧
      burn s.token l2NativeTokenVaultAddr 4 1 = none ∧
      LegacyStorageStep env s u ∧ u.token.config = fallbackConfig env s.token.config ∧
      u.token.totalSupply = 0 ∧
      LegacyStorageStep env u t ∧ LegacyStorageReach env s t ∧ t.version = 2 ∧
      t.token.config = fallbackConfig env s.token.config ∧ t.token.config ≠ s.token.config)

end Contracts.BridgedStandardERC20
