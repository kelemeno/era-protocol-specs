import EraSpec.Contracts.BridgedStandardERC20.Specs.ReinitializationFaithful

/-!
# Properties: counting the deployed token's calls

Statements about `EraSpec.Contracts.BridgedStandardERC20.Specs.ReinitializationFaithful`. Proofs are
in `EraSpec.Contracts.BridgedStandardERC20.Proofs.ReinitializationFaithful`. Every statement holds
for every `LegacyEnv`: nothing is assumed about the value `L1_CHAIN_ID()` returns or about the
encoder. There is no hash premise.

The identity results over the deployed token's runs are in
`Properties/ReinitializationStrong.lean`. This file adds the counting results.

## The labelled runs

* They are the deployed runs (`DeployedStorageRunsAreReach`).
* The `StorageRun`s are exactly the labelled deployed runs in which no call takes the legacy branch,
  with the same entry points (`ModelledRunsAreDeployedRunsWithoutLegacyCall`). So the run results
  of `Properties/Reinitialization.lean` cover exactly those deployed runs.

## `Reinitialization`'s counting results, on every deployed run

No call on either branch of `onlyNTV`, and no `transfer`, writes the version. So each counting
result of `Properties/Reinitialization.lean`, stated there over `StorageRun`, holds over every
deployed run, with the calls counted through `DeployedStorageCall.entryPoint`:

* the version rises by exactly the number of `bridgeInitialize` and `reinitializeToken` calls
  (`DeployedVersionCountsInitializations`);
* from a fresh proxy there are at most 255 of them (`DeployedLifetimeVersionCallBound`), a bound
  that is reached (`DeployedLifetimeBoundIsTight`);
* `bridgeInitialize` succeeds at most once, and never in a run that starts at a nonzero version
  (`DeployedBridgeInitializeAtMostOnce`).

## How many calls take the legacy branch

* In any deployed run, at most as many as the run's `bridgeInitialize` calls, plus one if the
  vault slot is zero at the start (`DeployedLegacyBranchBound`). With
  `DeployedBridgeInitializeAtMostOnce`, at most two.
* From a nonzero version, exactly one if the vault slot is zero at the start and nonzero at the
  end, and none otherwise (`DeployedLegacyBranchCountExact`). So on such a run at most one
  committed call reads `L1_CHAIN_ID()`.
* From a fresh proxy the bound of two is reached (`DeployedLegacyBranchTwiceFromFreshProxy`): the
  version premise of `DeployedLegacyBranchCountExact` cannot be dropped. That run calls the token
  before `bridgeInitialize` and initializes it with caller `0`; the vault's deploy-and-initialize
  (`NativeTokenVaultBase.sol:629-630`) does neither.

`DeployedCountingWitness` meets the premises above with a run on each branch of `onlyNTV`. Its
legacy run ends at a storage that `StorageReach` does not reach from the run's start.
-/

namespace Contracts.BridgedStandardERC20

/-! ## The labelled runs -/

/-- **THE LABELLED RUNS ARE THE DEPLOYED RUNS.** For every environment, a storage is reachable by
deployed steps exactly when some labelled deployed run leads there. -/
def Properties.DeployedStorageRunsAreReach : Prop :=
  ∀ (env : LegacyEnv) (s t : TokenStorage),
    DeployedStorageReach env s t ↔ ∃ calls, DeployedStorageRun env s calls t

/-- **THE MODELLED RUNS ARE THE DEPLOYED RUNS WITHOUT A LEGACY CALL.** For every environment, a
`StorageRun` with entry points `calls` leads from `s` to `t` exactly when a labelled deployed run
from `s` to `t` does whose labels have those entry points and none of which is
`legacyBridgeCall`. -/
def Properties.ModelledRunsAreDeployedRunsWithoutLegacyCall : Prop :=
  ∀ (env : LegacyEnv) (s : TokenStorage) (calls : List StorageCall) (t : TokenStorage),
    StorageRun s calls t ↔
      ∃ calls', DeployedStorageRun env s calls' t ∧
        calls'.map DeployedStorageCall.entryPoint = calls ∧ legacyBranchCalls calls' = 0

/-! ## `Reinitialization`'s counting results, on every deployed run -/

/-- **THE VERSION COUNTS THE CALLS THAT WRITE IT, ON EVERY DEPLOYED RUN.** Along any labelled
deployed run, both `onlyNTV` branches included, the version rises by exactly the number of
`bridgeInitialize` and `reinitializeToken` calls in it. -/
def Properties.DeployedVersionCountsInitializations : Prop :=
  ∀ (env : LegacyEnv) (s : TokenStorage) (calls : List DeployedStorageCall) (t : TokenStorage),
    DeployedStorageRun env s calls t →
    t.version.toNat = s.version.toNat + versionCalls (calls.map DeployedStorageCall.entryPoint)

/-- **AT MOST 255 VERSION-WRITING CALLS IN A DEPLOYED PROXY'S LIFE.** Along any labelled deployed
run from a fresh proxy, at most 255 calls are `bridgeInitialize` or `reinitializeToken`. -/
def Properties.DeployedLifetimeVersionCallBound : Prop :=
  ∀ (env : LegacyEnv) (calls : List DeployedStorageCall) (t : TokenStorage),
    DeployedStorageRun env freshStorage calls t →
    versionCalls (calls.map DeployedStorageCall.entryPoint) ≤ 255

/-- **THE BOUND IS REACHED ON THE DEPLOYED TOKEN.** For every environment, some labelled deployed
run from a fresh proxy has one `bridgeInitialize` call and 255 version-writing calls in all, and
ends at version 255. -/
def Properties.DeployedLifetimeBoundIsTight : Prop :=
  ∀ env : LegacyEnv, ∃ (calls : List DeployedStorageCall) (t : TokenStorage),
    DeployedStorageRun env freshStorage calls t ∧
    initializeCalls (calls.map DeployedStorageCall.entryPoint) = 1 ∧
    versionCalls (calls.map DeployedStorageCall.entryPoint) = 255 ∧ t.version = 255

/-- **`bridgeInitialize` SUCCEEDS AT MOST ONCE IN ANY DEPLOYED RUN**, interleaved with any
reinitializations and any calls on either `onlyNTV` branch, and not at all in a run that starts
at a nonzero version. -/
def Properties.DeployedBridgeInitializeAtMostOnce : Prop :=
  ∀ (env : LegacyEnv) (s : TokenStorage) (calls : List DeployedStorageCall) (t : TokenStorage),
    DeployedStorageRun env s calls t →
    initializeCalls (calls.map DeployedStorageCall.entryPoint) ≤ 1 ∧
    (s.version ≠ 0 → initializeCalls (calls.map DeployedStorageCall.entryPoint) = 0)

/-! ## How many calls take the legacy branch -/

/-- **THE LEGACY BRANCH RUNS AT MOST ONCE PER `bridgeInitialize`, PLUS ONCE FROM A ZERO VAULT.**
Along any labelled deployed run, from any storage, the number of calls that take `onlyNTV`'s legacy
branch is at most the number of `bridgeInitialize` calls in the run, plus one if the vault slot is
zero at the start. A legacy call leaves a nonzero vault slot, and only `bridgeInitialize` (with
caller `0`, :90) writes it back to zero. With `DeployedBridgeInitializeAtMostOnce`, no run has more
than two legacy calls; `DeployedLegacyBranchTwiceFromFreshProxy` has two. -/
def Properties.DeployedLegacyBranchBound : Prop :=
  ∀ (env : LegacyEnv) (s : TokenStorage) (calls : List DeployedStorageCall) (t : TokenStorage),
    DeployedStorageRun env s calls t →
    legacyBranchCalls calls ≤
      (if s.token.config.vault = 0 then 1 else 0) +
        initializeCalls (calls.map DeployedStorageCall.entryPoint)

/-- **ONCE INITIALIZED, THE LEGACY BRANCH RUNS ONCE IF THE VAULT SLOT GOES FROM ZERO TO NONZERO,
AND NEVER OTHERWISE.** Along any labelled deployed run from a nonzero version, the number of calls
that take `onlyNTV`'s legacy branch is 1 if the vault slot is zero at the start and nonzero at the
end, and 0 otherwise. So at most one committed call of such a run reads `L1_CHAIN_ID()`. Both
values occur (`DeployedCountingWitness`). -/
def Properties.DeployedLegacyBranchCountExact : Prop :=
  ∀ (env : LegacyEnv) (s : TokenStorage) (calls : List DeployedStorageCall) (t : TokenStorage),
    s.version ≠ 0 → DeployedStorageRun env s calls t →
    legacyBranchCalls calls =
      if s.token.config.vault = 0 ∧ t.token.config.vault ≠ 0 then 1 else 0

/-- **FROM A FRESH PROXY, TWO CALLS CAN TAKE THE LEGACY BRANCH.** For every environment, a labelled
deployed run from a fresh proxy makes a call on the legacy branch, then `bridgeInitialize`, then a
call on the legacy branch again, and ends at version 1 with the identity
`fallbackConfig env ⟨0, 9, 5⟩` and nothing in circulation. The proof's run: the L2 vault's
`bridgeMint` of one unit to account `4`, `bridgeInitialize` by caller `0` with asset id `5` and
origin token `9` (which writes the vault slot back to zero, :90), and the L2 vault's `bridgeBurn`
of that unit. Two committed calls of the run read `L1_CHAIN_ID()`, and the model gives both the
same value. So the version premise of `DeployedLegacyBranchCountExact` cannot be dropped, and
`DeployedLegacyBranchBound` is reached. The vault's deploy-and-initialize
(`NativeTokenVaultBase.sol:629-630`) makes no call before `bridgeInitialize` and makes that call
itself, so its caller is the vault, not `0`. -/
def Properties.DeployedLegacyBranchTwiceFromFreshProxy : Prop :=
  ∀ env : LegacyEnv, ∃ t : TokenStorage,
    DeployedStorageRun env freshStorage
      [.legacyBridgeCall, .bridgeInitialize, .legacyBridgeCall] t ∧
    t.version = 1 ∧ t.token.config = fallbackConfig env ⟨0, 9, 5⟩ ∧ t.token.totalSupply = 0

/-! ## Witness -/

/-- **THE PREMISES ARE SATISFIABLE, ON BOTH BRANCHES OF `onlyNTV`.** For every environment:

* **Nonlegacy.** `bridgeInitialize` by the vault `1` for asset `5` and origin token `9` on a fresh
  proxy gives storage at version 1. From there the labelled deployed run `[bridgeCall,
  reinitializeToken]` (the proof's: the vault's one-unit `bridgeMint` to account `4`, then the
  beacon owner `7`'s reinitialization to version 2) ends at version 2 with one unit in circulation
  and identity `⟨1, 9, 5⟩`. With the initialization in front it is a labelled deployed run from the
  fresh proxy, and also a `StorageRun` with entry points `[bridgeInitialize, ledger,
  reinitializeToken]`. This meets the premises of every statement above that has premises, with a
  count of 0 in `DeployedLegacyBranchCountExact`.
* **Legacy.** Take `WellFormed` storage at version 1 with vault and asset-id slots zero, origin
  token `9`, and one unit held by account `4`. The labelled deployed run `[legacyBridgeCall,
  reinitializeToken]` from it (the proof's: the L2 vault's one-unit `bridgeBurn` from `4`, then the
  beacon owner `7`'s reinitialization to version 2) ends at version 2 with identity
  `fallbackConfig env ⟨0, 9, 0⟩` and nothing in circulation, and its end is not reachable from its
  start by `StorageReach`. This meets the premises of `DeployedVersionCountsInitializations`,
  `DeployedBridgeInitializeAtMostOnce`, `DeployedLegacyBranchBound` and
  `DeployedLegacyBranchCountExact`, with a count of 1 in the last. -/
def Properties.DeployedCountingWitness : Prop :=
  ∀ env : LegacyEnv,
    (∃ s t : TokenStorage,
      initializeStorage freshStorage 1 5 9 (some emptyMetadata) = some s ∧ s.version = 1 ∧
      DeployedStorageRun env s [.bridgeCall, .reinitializeToken] t ∧
      DeployedStorageRun env freshStorage [.bridgeInitialize, .bridgeCall, .reinitializeToken] t ∧
      StorageRun freshStorage [.bridgeInitialize, .ledger, .reinitializeToken] t ∧
      t.version = 2 ∧ t.token.totalSupply = 1 ∧ t.token.config = ⟨1, 9, 5⟩) ∧
    (∃ s t : TokenStorage,
      WellFormed s.token ∧ s.version = 1 ∧ s.token.config = ⟨0, 9, 0⟩ ∧
      s.token.balances 4 = 1 ∧ s.token.totalSupply = 1 ∧
      DeployedStorageRun env s [.legacyBridgeCall, .reinitializeToken] t ∧ ¬ StorageReach s t ∧
      t.version = 2 ∧ t.token.config = fallbackConfig env ⟨0, 9, 0⟩ ∧ t.token.totalSupply = 0)

end Contracts.BridgedStandardERC20
