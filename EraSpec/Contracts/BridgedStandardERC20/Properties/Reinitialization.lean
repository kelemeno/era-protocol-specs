import EraSpec.Contracts.BridgedStandardERC20.Specs.Reinitialization

/-!
# Properties: `reinitializeToken` rewrites metadata and nothing else

Statements about `EraSpec.Contracts.BridgedStandardERC20.Specs.Reinitialization`. Proofs are
in `EraSpec.Contracts.BridgedStandardERC20.Proofs.Reinitialization`.

## What holds

* **When the call succeeds** (`ReinitSucceedsIff`): exactly when the requested version is the
  current one plus one and the caller is the owner the beacon reports. So a version jump of
  more than one has no step (`VersionJumpHasNoStep`), nor does any other caller
  (`OnlyTheBeaconOwnerReinitializes`), nor any call on the implementation contract
  (`ImplementationNeverReinitialized`).
* **What it writes** (`ReinitExactEffect`): the version, and the metadata as
  `reinitMetadata` says. Balances, total supply, vault, asset id, origin token and
  `decimals_` are those before the call, whoever made it (`ReinitKeepsLedgerAndIdentity`), so
  `WellFormed` is kept (`ReinitPreservesWellFormed`) and every later `bridgeMint`,
  `bridgeBurn` or `transfer` has the result it had before (`ReinitLeavesLedgerCallsUnchanged`).
  The call neither reads nor writes the ledger-and-identity state
  (`ReinitIndependentOfLedger`), so it commutes with every ledger call.
* **The version counter** rises by exactly one (`ReinitVersionIncreasesByOne`), a used version
  cannot be replayed (`ReinitVersionIsSpent`), and `bridgeInitialize` stays closed
  (`ReinitKeepsInitializationClosed`).
* **The NatSpec at :146-147** ("the governor can not accidentally disable future
  reinitialization"): a successful reinitialization leaves no further one possible exactly
  when it started from version 254 (`OnlyTheStepFrom254DisablesReinitialization`). The
  `onlyNextVersion` modifier is what makes this true: without it, OpenZeppelin's
  `reinitializer` alone lets a single call jump from version 1 to 255, after which nothing can
  reinitialize the token (`WithoutNextVersionAJumpDisablesReinitialization`).
* **Along runs of every modelled entry point** (`StorageReach`), the ledger stays
  `WellFormed` and the version never falls (`RunsPreserveLedger`); once the version is nonzero
  the identity never changes (`InitializedIdentityIsFixed`). From a fresh proxy, the identity
  is for ever the one `bridgeInitialize` bound (`FreshProxyLifecycle`).
* **Counting calls** (`StorageRun`, the same runs with their entry points listed,
  `StorageRunsAreReach`): the version rises by exactly the number of `bridgeInitialize` and
  `reinitializeToken` calls (`VersionCountsInitializations`), so a proxy's whole life holds at
  most 255 of them (`LifetimeVersionCallBound`), and that bound is reached with one
  initialization and 254 reinitializations (`LifetimeBoundIsTight`). `bridgeInitialize`
  succeeds at most once in any run, and never once the version is nonzero
  (`BridgeInitializeAtMostOnce`).

## What needs more than the guards

* **The version counter is shared with `bridgeInitialize`.** On a fresh proxy, version 1 is
  "the next version", so the beacon owner's `reinitializeToken(…, 1)` succeeds there, after
  which `bridgeInitialize` can never run and the identity stays zero
  (`ReinitializeOnFreshProxyBlocksBridgeInitialize`). The vault rules this out by deploying
  and initializing in one call (`NativeTokenVaultBase.sol:629-630`, a `BeaconProxy` built with
  empty data, `OZ BeaconProxy.sol:30-32`); the token's own guards do not.

`ReinitWitness` and `LastVersionWitness` show the premises are satisfiable.
-/

namespace Contracts.BridgedStandardERC20

/-! ## One call -/

/-- **WHEN `reinitializeToken` SUCCEEDS.** Exactly when the requested version is the current
one plus one (over the naturals, so 255 has no successor) and the beacon reports the caller as
its owner. `reinitializer`'s own `_initialized < version` check is implied. -/
def Properties.ReinitSucceedsIff : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8),
    (∃ t, reinitializeToken beaconOwner s caller getters name symbol version = some t) ↔
      version.toNat = s.version.toNat + 1 ∧ beaconOwner = some caller

/-- **THE EXACT EFFECT.** A successful call keeps the ledger-and-identity state, sets the version
to the requested one, and changes the metadata only as `reinitMetadata` says: name, symbol,
getter flags, EIP-712 name and version, and the zeroed EIP-712 caches. -/
def Properties.ReinitExactEffect : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8) (t : TokenStorage),
    reinitializeToken beaconOwner s caller getters name symbol version = some t →
    t = ⟨s.token, version, reinitMetadata s.metadata getters name symbol⟩

/-- **LEDGER AND IDENTITY ARE UNTOUCHED.** After a successful call, whoever made it, every
balance, the total supply, the vault, the asset id, the origin token and `decimals_` are those
before it. -/
def Properties.ReinitKeepsLedgerAndIdentity : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8) (t : TokenStorage),
    reinitializeToken beaconOwner s caller getters name symbol version = some t →
    t.token.balances = s.token.balances ∧ t.token.totalSupply = s.token.totalSupply ∧
    t.token.config.vault = s.token.config.vault ∧
    t.token.config.assetId = s.token.config.assetId ∧
    t.token.config.originToken = s.token.config.originToken ∧
    t.metadata.decimals = s.metadata.decimals

/-- **THE LEDGER INVARIANT IS KEPT.** -/
def Properties.ReinitPreservesWellFormed : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8) (t : TokenStorage),
    WellFormed s.token →
    reinitializeToken beaconOwner s caller getters name symbol version = some t →
    WellFormed t.token

/-- **THE VAULT'S CALLS BEHAVE AS BEFORE.** After a successful call, every `bridgeMint`,
`bridgeBurn` and `transfer` has exactly the result it had before it: a mint the vault could
make is still possible, with the same effect. -/
def Properties.ReinitLeavesLedgerCallsUnchanged : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8) (t : TokenStorage),
    reinitializeToken beaconOwner s caller getters name symbol version = some t →
    ∀ (who account other : Address) (amount : UInt256),
      burn t.token who account amount = burn s.token who account amount ∧
      mint t.token who account amount = mint s.token who account amount ∧
      transfer t.token account other amount = transfer s.token account other amount

/-- **THE CALL NEITHER READS NOR WRITES THE LEDGER.** On storage that differs only in its
ledger-and-identity state, `reinitializeToken` succeeds or fails alike and writes the same
version and metadata, leaving that state as it found it. So it commutes with every
`bridgeMint`, `bridgeBurn` and `transfer`. -/
def Properties.ReinitIndependentOfLedger : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8) (token : State),
    reinitializeToken beaconOwner { s with token := token } caller getters name symbol version =
      (reinitializeToken beaconOwner s caller getters name symbol version).map
        fun t => { t with token := token }

/-- **THE VERSION RISES BY EXACTLY ONE.** -/
def Properties.ReinitVersionIncreasesByOne : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8) (t : TokenStorage),
    reinitializeToken beaconOwner s caller getters name symbol version = some t →
    s.version < t.version ∧ t.version.toNat = s.version.toNat + 1

/-- **A VERSION JUMP HAS NO STEP.** Any requested version other than the current one plus one
reverts, whoever calls. -/
def Properties.VersionJumpHasNoStep : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8),
    version.toNat ≠ s.version.toNat + 1 →
    reinitializeToken beaconOwner s caller getters name symbol version = none

/-- **ONLY THE BEACON'S OWNER REINITIALIZES.** If the beacon does not report the caller as its
owner (or the lookup reverts), the call reverts. -/
def Properties.OnlyTheBeaconOwnerReinitializes : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8),
    beaconOwner ≠ some caller →
    reinitializeToken beaconOwner s caller getters name symbol version = none

/-- **A USED VERSION IS SPENT.** After a successful call at `version`, no call at `version`
succeeds, whoever makes it. -/
def Properties.ReinitVersionIsSpent : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8) (t : TokenStorage),
    reinitializeToken beaconOwner s caller getters name symbol version = some t →
    ∀ (beaconOwner' : Option Address) (caller' : Address) (getters' : Getters)
      (name' symbol' : Text),
      reinitializeToken beaconOwner' t caller' getters' name' symbol' version = none

/-- **`bridgeInitialize` STAYS CLOSED.** After a successful reinitialization, no
`bridgeInitialize` succeeds. -/
def Properties.ReinitKeepsInitializationClosed : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8) (t : TokenStorage),
    reinitializeToken beaconOwner s caller getters name symbol version = some t →
    ∀ (caller' : Address) (assetId : UInt256) (originToken : Address) (decoded : Option Metadata),
      initializeStorage t caller' assetId originToken decoded = none

/-- **THE IMPLEMENTATION CONTRACT IS NEVER REINITIALIZED.** Its constructor set the version to
255, which has no successor. -/
def Properties.ImplementationNeverReinitialized : Prop :=
  ∀ (beaconOwner : Option Address) (caller : Address) (getters : Getters) (name symbol : Text)
    (version : UInt8),
    reinitializeToken beaconOwner disabledStorage caller getters name symbol version = none

/-- **ONLY THE STEP FROM 254 DISABLES REINITIALIZATION.** After a successful call, no further
reinitialization can ever succeed exactly when that call started from version 254 (and so
ended at 255). Every other successful call leaves the next version available. -/
def Properties.OnlyTheStepFrom254DisablesReinitialization : Prop :=
  ∀ (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (getters : Getters)
    (name symbol : Text) (version : UInt8) (t : TokenStorage),
    reinitializeToken beaconOwner s caller getters name symbol version = some t →
    ((∀ (beaconOwner' : Option Address) (caller' : Address) (getters' : Getters)
        (name' symbol' : Text) (version' : UInt8),
        reinitializeToken beaconOwner' t caller' getters' name' symbol' version' = none) ↔
      s.version = 254)

/-- **WITHOUT `onlyNextVersion`, ONE CALL CAN DISABLE REINITIALIZATION FOR EVER.** With only
OpenZeppelin's `reinitializer` check and the owner check, the beacon owner's call at version 255
succeeds on a token at version 1, and afterwards no reinitialization succeeds, with or without
the modifier. With the modifier, the same call reverts. -/
def Properties.WithoutNextVersionAJumpDisablesReinitialization : Prop :=
  ∃ s t : TokenStorage, s.version = 1 ∧
    reinitializeWithoutNextVersion (some 7) s 7 ⟨false, false, false⟩ [] [] 255 = some t ∧
    (∀ (beaconOwner : Option Address) (caller : Address) (getters : Getters)
      (name symbol : Text) (version : UInt8),
      reinitializeWithoutNextVersion beaconOwner t caller getters name symbol version = none ∧
      reinitializeToken beaconOwner t caller getters name symbol version = none) ∧
    reinitializeToken (some 7) s 7 ⟨false, false, false⟩ [] [] 255 = none

/-! ## Runs -/

/-- **EVERY MODELLED ENTRY POINT KEEPS THE LEDGER INVARIANT.** Along any run of
`bridgeInitialize`, `reinitializeToken`, `bridgeMint`, `bridgeBurn` and `transfer` calls,
`WellFormed` is kept and the version never decreases. -/
def Properties.RunsPreserveLedger : Prop :=
  ∀ (s t : TokenStorage), WellFormed s.token → StorageReach s t →
    WellFormed t.token ∧ s.version.toNat ≤ t.version.toNat

/-- **ONCE INITIALIZED, THE IDENTITY IS FIXED.** From any state with a nonzero version, along any
run, the vault, the asset id and the origin token never change, and the version stays nonzero.
No ledger premise. -/
def Properties.InitializedIdentityIsFixed : Prop :=
  ∀ (s t : TokenStorage), s.version ≠ 0 → StorageReach s t →
    t.token.config = s.token.config ∧ t.version ≠ 0

/-- **A FRESH PROXY'S IDENTITY IS THE ONE `bridgeInitialize` BOUND, FOR EVER.** After a
successful `bridgeInitialize` on a fresh proxy and any run after it, the vault is that call's
caller, the asset id and origin token are its arguments, the ledger is `WellFormed`, and no
`bridgeInitialize` can succeed. Since the vault slot stays the initializer's caller, a nonzero
caller (the vault, in the deployment flow) also keeps the unmodelled legacy branch of `onlyNTV`
(:54-61) from ever running. -/
def Properties.FreshProxyLifecycle : Prop :=
  ∀ (caller : Address) (assetId : UInt256) (originToken : Address) (metadata : Metadata)
    (s t : TokenStorage),
    initializeStorage freshStorage caller assetId originToken (some metadata) = some s →
    StorageReach s t →
    t.token.config = ⟨caller, originToken, assetId⟩ ∧ WellFormed t.token ∧
    ∀ (caller' : Address) (assetId' : UInt256) (originToken' : Address)
      (decoded : Option Metadata),
      initializeStorage t caller' assetId' originToken' decoded = none

/-! ## Counting calls -/

/-- **THE LABELLED RUNS ARE THE RUNS.** A state is reachable exactly when some run, with its list
of entry points, leads there. -/
def Properties.StorageRunsAreReach : Prop :=
  ∀ (s t : TokenStorage), StorageReach s t ↔ ∃ calls, StorageRun s calls t

/-- **THE VERSION COUNTS THE CALLS THAT WRITE IT.** Along any run, the version rises by exactly the
number of `bridgeInitialize` and `reinitializeToken` calls in it. -/
def Properties.VersionCountsInitializations : Prop :=
  ∀ (s : TokenStorage) (calls : List StorageCall) (t : TokenStorage), StorageRun s calls t →
    t.version.toNat = s.version.toNat + versionCalls calls

/-- **AT MOST 255 VERSION-WRITING CALLS IN A PROXY'S LIFE.** Along any run from a fresh proxy, at
most 255 calls are `bridgeInitialize` or `reinitializeToken`. -/
def Properties.LifetimeVersionCallBound : Prop :=
  ∀ (calls : List StorageCall) (t : TokenStorage), StorageRun freshStorage calls t →
    versionCalls calls ≤ 255

/-- **THE BOUND IS REACHED.** From a fresh proxy, one `bridgeInitialize` followed by 254
`reinitializeToken` calls all succeed, ending at version 255. -/
def Properties.LifetimeBoundIsTight : Prop :=
  ∃ (calls : List StorageCall) (t : TokenStorage), StorageRun freshStorage calls t ∧
    initializeCalls calls = 1 ∧ versionCalls calls = 255 ∧ t.version = 255

/-- **`bridgeInitialize` SUCCEEDS AT MOST ONCE IN ANY RUN**, interleaved with any
reinitializations and ledger calls, and not at all in a run that starts at a nonzero version. -/
def Properties.BridgeInitializeAtMostOnce : Prop :=
  ∀ (s : TokenStorage) (calls : List StorageCall) (t : TokenStorage), StorageRun s calls t →
    initializeCalls calls ≤ 1 ∧ (s.version ≠ 0 → initializeCalls calls = 0)

/-! ## Countermodel -/

/-- **ON A FRESH PROXY, A REINITIALIZATION LOCKS OUT `bridgeInitialize`.** Whoever owns the
beacon can call `reinitializeToken(…, 1)` on a fresh proxy, since version 1 is the next one.
It succeeds, and along every run after it the identity stays zero, `bridgeInitialize` never
succeeds, and no modelled `bridgeMint` or `bridgeBurn` succeeds. (The real token would then
reach the legacy zero-vault branch of `onlyNTV`, :54-61, which is not modelled.) The vault
avoids this by initializing in the deploying call (`NativeTokenVaultBase.sol:629-630`). -/
def Properties.ReinitializeOnFreshProxyBlocksBridgeInitialize : Prop :=
  ∀ (owner : Address) (getters : Getters) (name symbol : Text),
    ∃ t, reinitializeToken (some owner) freshStorage owner getters name symbol 1 = some t ∧
      ∀ u, StorageReach t u →
        u.token.config = ⟨0, 0, 0⟩ ∧
        (∀ (caller : Address) (assetId : UInt256) (originToken : Address)
          (decoded : Option Metadata),
          initializeStorage u caller assetId originToken decoded = none) ∧
        ∀ (who account : Address) (amount : UInt256),
          burn u.token who account amount = none ∧ mint u.token who account amount = none

/-! ## Witnesses -/

/-- **THE PREMISES ARE SATISFIABLE.** From a fresh proxy, `bridgeInitialize` by the vault `1`
for asset `5` and origin token `9`, then a run (a one-unit `bridgeMint` to account `4`) to a
`WellFormed` state with one unit in circulation. There the beacon owner `7` reinitializes to
version 2 with a new name; afterwards the vault's one-unit `bridgeBurn` still succeeds and
empties the ledger, and version 3 is available. -/
def Properties.ReinitWitness : Prop :=
  ∃ s₁ s t : TokenStorage,
    initializeStorage freshStorage 1 5 9 (some emptyMetadata) = some s₁ ∧
    StorageReach s₁ s ∧ WellFormed s.token ∧ s.token.totalSupply = 1 ∧
    reinitializeToken (some 7) s 7 ⟨true, false, false⟩ [0x42] [0x43] 2 = some t ∧
    t.metadata.name ≠ s.metadata.name ∧ t.version = 2 ∧
    burn t.token 1 4 1 = some (empty ⟨1, 9, 5⟩) ∧
    ∃ u, reinitializeToken (some 7) t 7 ⟨false, false, false⟩ [0x44] [0x45] 3 = some u

/-- **THE OTHER SIDE OF `OnlyTheStepFrom254DisablesReinitialization`.** At version 254, the
beacon owner's reinitialization to 255 succeeds, and after it no reinitialization does. -/
def Properties.LastVersionWitness : Prop :=
  ∃ s t : TokenStorage, s.version = 254 ∧
    reinitializeToken (some 7) s 7 ⟨false, false, false⟩ [] [] 255 = some t ∧
    ∀ (beaconOwner : Option Address) (caller : Address) (getters : Getters) (name symbol : Text)
      (version : UInt8), reinitializeToken beaconOwner t caller getters name symbol version = none

end Contracts.BridgedStandardERC20
