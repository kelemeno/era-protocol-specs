import EraSpec.Contracts.BridgedStandardERC20.Specs.Initialization

/-!
# BridgedStandardERC20: `reinitializeToken`, on the token's full storage

Source: era-contracts `c67894b970a0dac6fe9144d8ebf4b0806e15a9af`,
`l1-contracts/contracts/bridge/BridgedStandardERC20.sol` (cited as `:N`), and the
OpenZeppelin v4.9 code it inherits. The pinned tree's OpenZeppelin submodules
(`lib/openzeppelin-contracts-upgradeable-v4` and `lib/openzeppelin-contracts-v4`, branch
`release-v4.9` per the pinned `.gitmodules`) are not checked out there; the library lines
below were read from a v4.9.6 copy of both and are cited as `OZ <file>:N`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.BridgedStandardERC20.Properties.Reinitialization` and are proved in
`EraSpec.Contracts.BridgedStandardERC20.Proofs.Reinitialization`.

## The entry point (:141-164)

    function reinitializeToken(
        ERC20Getters calldata _availableGetters,
        string calldata _newName,
        string calldata _newSymbol,
        uint8 _version
    ) external onlyNextVersion(_version) reinitializer(_version) {               // :148-153
        address beaconAddress = _getBeacon();                                       // :156
        require(msg.sender == UpgradeableBeacon(beaconAddress).owner(),
                Unauthorized(msg.sender));                                          // :157
        __ERC20_init_unchained(_newName, _newSymbol);                               // :159
        __ERC20Permit_init(_newName);                                               // :160
        availableGetters = _availableGetters;                                       // :161
        emit BridgeInitialize(originToken, _newName, _newSymbol, decimals_);        // :163
    }

Its guards, in the order they run:

* `onlyNextVersion(_version)` (:66-71): `require(_version == _getInitializedVersion() + 1)`.
  `_getInitializedVersion()` is the `uint8 _initialized` slot (`OZ Initializable.sol:63,
  156-158`), and Solidity 0.8 `+ 1` on `uint8` is checked: at `_initialized = 255` it panics.
  So the guard is exactly `_version = _initialized + 1` over the naturals (`NextVersion`).
* `reinitializer(_version)` (`OZ Initializable.sol:119-126`):
  `require(!_initializing && _initialized < version)`, then `_initialized = version`,
  `_initializing = true`, the body, `_initializing = false`. The `_initialized < version`
  conjunct is `ReinitializerAllowed`; it is implied by `NextVersion`, and kept so that the
  transcription is literal.
* The caller check (:156-157): `_getBeacon()` reads the ERC-1967 beacon slot
  (`OZ ERC1967Upgrade.sol:123, 128-130`) and the call asks that beacon for `owner()`.
  `beaconOwner : Option Address` is what that lookup returns: `some o` when the beacon slot
  names a contract whose `owner()` returned `o`, `none` when the call reverts (an empty slot,
  as on the implementation contract itself, or a beacon without `owner()`).

Its writes:

* `__ERC20_init_unchained` (`OZ ERC20Upgradeable.sol:59-62`) sets `_name` and `_symbol`.
* `__ERC20Permit_init(name)` (`OZ ERC20PermitUpgradeable.sol:47-49`) runs
  `__EIP712_init_unchained(name, "1")` (`OZ EIP712Upgradeable.sol:63-70`), which sets the
  EIP-712 `_name` and `_version` and zeroes the legacy caches `_hashedName` and
  `_hashedVersion` (`OZ EIP712Upgradeable.sol:40-45`). The permit domain separator is rebuilt
  from `_name` on every use (`OZ EIP712Upgradeable.sol:79-81, 162-176`), so EIP-2612
  signatures made under the old name stop verifying. Permits are not modelled.
* `availableGetters` (:30, :161).
* `_initialized` becomes `_version`; `_initializing` is set for the body and reset after it.

Nothing else is written. In particular `decimals_` (:35) is only read (:163), and the ledger
(`_balances`, `_totalSupply`), `originToken`, `nativeTokenVault` and `assetId` (:42-48) are
not touched (`reinitMetadata`, `reinitializeToken`).

## Who writes the identity slots

In the pinned implementation `originToken` is written only by `bridgeInitialize` (:87), and
`assetId` and `nativeTokenVault` only by `bridgeInitialize` (:88-90) and by the legacy branch of
`onlyNTV` (:54-61), which runs only while `nativeTokenVault` is zero. So for a token initialized
with a nonzero vault, `StorageStep` below contains every writer of those slots in the pinned
code. A beacon `upgradeTo` replaces the code itself and is outside the model.

## Modelling choices

* **`TokenStorage`** is the proxy's storage as far as this topic needs it: the existing
  ledger-and-identity `State` (balances, total supply, vault, origin token, asset id), the
  `_initialized` slot, and the metadata slots (`Metadata`). Allowances, permit nonces,
  `l2Bridge` and the ERC-1967 slots are not modelled; `reinitializeToken` writes none of them.
* **`_initializing` is not modelled.** Between transactions it is `false`: both `initializer`
  (`OZ Initializable.sol:95-98`) and `reinitializer` (`OZ Initializable.sol:124`) reset it on
  exit, and no entry point modelled here calls another one inside its body. So its
  `!_initializing` checks always pass for a top-level call; constructor-context and nested
  initializer calls are outside the model (as for `initializeToken`).
* **Strings are byte lists** (`Text`): a `string calldata` need not be valid UTF-8.
* **A revert is `none`.** As in `Specs/Model.lean`, a failed call commits nothing.
* **`bridgeInitialize` on the full storage** (`initializeStorage`) is the existing
  `initializeToken` projection plus the metadata it writes. That metadata is an input:
  `none` when the outer `DataEncoding.decodeTokenData` reverts (:97; `metadataDecoded = false`
  in `initializeToken`), else the record of decoded name/symbol/decimals and getter flags
  (:99-137), whose contents are not transcribed.
* **`StorageStep` is every entry point modelled for the token:** `bridgeInitialize`,
  `reinitializeToken` (with any beacon-owner answer and any caller, so the results do not
  depend on who governs the beacon), and the existing ledger `Step` (vault `bridgeMint` and
  `bridgeBurn` on the nonlegacy branch, and `transfer`, whose arbitrary `owner` also covers
  `transferFrom`'s ledger effect).
* **Outside the model:** the legacy `onlyNTV` fallback for a zero vault (:54-61, item B7),
  which writes `nativeTokenVault` and `assetId`; a beacon `upgradeTo`, which swaps the code of
  every bridged token at once (`OPS-CONFIG`); permit signatures and allowances; events. Because
  of the first, `StorageStep` has no bridge call on a zero vault where the deployed token has one,
  and results about `StorageReach` from such a state do not carry over to the deployed token.
  `Specs/ReinitializationStrong.lean` adds the fallback (`DeployedStorageStep`).
-/

namespace Contracts.BridgedStandardERC20

/-- `ERC20Getters` (:24-28): which of the getters `name()`, `symbol()`, `decimals()` revert
(:198-223). -/
structure Getters where
  ignoreName : Bool
  ignoreSymbol : Bool
  ignoreDecimals : Bool
deriving DecidableEq

/-- A Solidity `string`, as its bytes. -/
abbrev Text := List UInt8

/-- The token's metadata slots: the ones `reinitializeToken` writes, and `decimals_`, which it
does not. -/
structure Metadata where
  /-- `ERC20Upgradeable._name`. -/
  name : Text
  /-- `ERC20Upgradeable._symbol`. -/
  symbol : Text
  /-- `decimals_` (:35). Written only by `bridgeInitialize` (:130-135). -/
  decimals : UInt8
  /-- `availableGetters` (:30). -/
  getters : Getters
  /-- `EIP712Upgradeable._name`: the permit domain's name. -/
  eip712Name : Text
  /-- `EIP712Upgradeable._version`. -/
  eip712Version : Text
  /-- `EIP712Upgradeable._hashedName`, the legacy cache. -/
  hashedName : UInt256
  /-- `EIP712Upgradeable._hashedVersion`, the legacy cache. -/
  hashedVersion : UInt256
deriving DecidableEq

/-- The metadata of fresh proxy storage: every slot zero. -/
def emptyMetadata : Metadata := ⟨[], [], 0, ⟨false, false, false⟩, [], [], 0, 0⟩

/-- The proxy's storage for this topic: the ledger and identity of `State`, the
`Initializable._initialized` slot, and the metadata slots. -/
structure TokenStorage where
  token : State
  /-- `Initializable._initialized` (`OZ Initializable.sol:63`). -/
  version : UInt8
  metadata : Metadata

/-- The projection the existing initializer model (`Specs/Initialization.lean`) works on. -/
def TokenStorage.init (s : TokenStorage) : InitState := ⟨s.token, s.version⟩

/-- A freshly allocated proxy (`MODEL-FRESH`): the existing `freshProxy`, empty metadata. -/
def freshStorage : TokenStorage := ⟨freshProxy.token, freshProxy.version, emptyMetadata⟩

/-- The implementation contract's own storage: its constructor ran `_disableInitializers()`
(:74-77), so its version is 255 (`OZ Initializable.sol:145-151`). -/
def disabledStorage : TokenStorage :=
  ⟨disabledImplementation.token, disabledImplementation.version, emptyMetadata⟩

/-- `"1"`, the EIP-712 version `__ERC20Permit_init` writes (`OZ ERC20PermitUpgradeable.sol:48`). -/
def permitVersion : Text := [0x31]

/-- The metadata after `reinitializeToken`'s body (:159-161): name and symbol, the EIP-712
name and version, the zeroed EIP-712 caches, and the getter flags. `decimals` is kept. -/
def reinitMetadata (m : Metadata) (getters : Getters) (name symbol : Text) : Metadata :=
  { m with name := name, symbol := symbol, getters := getters,
           eip712Name := name, eip712Version := permitVersion, hashedName := 0, hashedVersion := 0 }

/-- `onlyNextVersion` (:66-71), with Solidity's checked `uint8` addition: the version must be
the current one plus one, and 255 has no successor. -/
def NextVersion (s : TokenStorage) (version : UInt8) : Prop :=
  version.toNat = s.version.toNat + 1

/-- The `_initialized < version` conjunct of `reinitializer` (`OZ Initializable.sol:120`). -/
def ReinitializerAllowed (s : TokenStorage) (version : UInt8) : Prop :=
  s.version < version

/-- All of `reinitializeToken`'s guards: `onlyNextVersion`, `reinitializer`, and the caller
being the owner the beacon reports (:157). -/
def ReinitAllowed (beaconOwner : Option Address) (s : TokenStorage) (caller : Address)
    (version : UInt8) : Prop :=
  NextVersion s version ∧ ReinitializerAllowed s version ∧ beaconOwner = some caller

instance (s : TokenStorage) (version : UInt8) : Decidable (NextVersion s version) :=
  inferInstanceAs (Decidable (_ = _))

instance (s : TokenStorage) (version : UInt8) : Decidable (ReinitializerAllowed s version) :=
  inferInstanceAs (Decidable (_ < _))

instance (beaconOwner : Option Address) (s : TokenStorage) (caller : Address) (version : UInt8) :
    Decidable (ReinitAllowed beaconOwner s caller version) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- `reinitializeToken(getters, name, symbol, version)` (:148-164), called by `caller`, with
the beacon's `owner()` lookup answering `beaconOwner`. -/
def reinitializeToken (beaconOwner : Option Address) (s : TokenStorage) (caller : Address)
    (getters : Getters) (name symbol : Text) (version : UInt8) : Option TokenStorage :=
  if ReinitAllowed beaconOwner s caller version then
    some ⟨s.token, version, reinitMetadata s.metadata getters name symbol⟩
  else none

/-- `reinitializeToken` **without** `onlyNextVersion` (:66-71): only OpenZeppelin's
`reinitializer` check and the owner check, as the function would be with the modifier
removed. Not source code; it shows what the modifier adds. -/
def reinitializeWithoutNextVersion (beaconOwner : Option Address) (s : TokenStorage)
    (caller : Address) (getters : Getters) (name symbol : Text) (version : UInt8) :
    Option TokenStorage :=
  if ReinitializerAllowed s version ∧ beaconOwner = some caller then
    some ⟨s.token, version, reinitMetadata s.metadata getters name symbol⟩
  else none

/-- `bridgeInitialize(assetId, originToken, data)` (:85-139) on the full storage: the existing
`initializeToken` projection, plus the metadata the call writes (`none`: the outer decode of
`data` reverted, :97). -/
def initializeStorage (s : TokenStorage) (caller : Address) (assetId : UInt256)
    (originToken : Address) (decoded : Option Metadata) : Option TokenStorage :=
  match decoded with
  | none => none
  | some m =>
    match initializeToken s.init caller assetId originToken true with
    | none => none
    | some i => some ⟨i.token, i.version, m⟩

/-- One successful call of a modelled entry point. -/
inductive StorageStep : TokenStorage → TokenStorage → Prop
  /-- `bridgeInitialize` by any caller. -/
  | bridgeInitialize {s t : TokenStorage} {caller : Address} {assetId : UInt256}
      {originToken : Address} {decoded : Option Metadata} :
      initializeStorage s caller assetId originToken decoded = some t → StorageStep s t
  /-- `reinitializeToken` by any caller, whatever the beacon reports as its owner. -/
  | reinitialize {s t : TokenStorage} {beaconOwner : Option Address} {caller : Address}
      {getters : Getters} {name symbol : Text} {version : UInt8} :
      reinitializeToken beaconOwner s caller getters name symbol version = some t →
      StorageStep s t
  /-- `bridgeMint`, `bridgeBurn` or `transfer`, as the existing ledger `Step`. -/
  | ledger {s : TokenStorage} {token : State} :
      Step s.token token → StorageStep s { s with token := token }

inductive StorageReach : TokenStorage → TokenStorage → Prop
  | refl {s} : StorageReach s s
  | tail {s t u} : StorageReach s t → StorageStep t u → StorageReach s u

/-! ## Runs that record which entry point each call used -/

/-- The entry point of one call. -/
inductive StorageCall
  | bridgeInitialize
  | reinitializeToken
  | ledger
deriving DecidableEq

/-- `StorageStep`, labelled with the entry point it used. -/
inductive StorageCallStep : TokenStorage → StorageCall → TokenStorage → Prop
  | bridgeInitialize {s t : TokenStorage} {caller : Address} {assetId : UInt256}
      {originToken : Address} {decoded : Option Metadata} :
      initializeStorage s caller assetId originToken decoded = some t →
      StorageCallStep s .bridgeInitialize t
  | reinitialize {s t : TokenStorage} {beaconOwner : Option Address} {caller : Address}
      {getters : Getters} {name symbol : Text} {version : UInt8} :
      reinitializeToken beaconOwner s caller getters name symbol version = some t →
      StorageCallStep s .reinitializeToken t
  | ledger {s : TokenStorage} {token : State} :
      Step s.token token → StorageCallStep s .ledger { s with token := token }

/-- A run, with the list of entry points its calls used, in order. -/
inductive StorageRun : TokenStorage → List StorageCall → TokenStorage → Prop
  | nil {s} : StorageRun s [] s
  | cons {s t u : TokenStorage} {call : StorageCall} {calls : List StorageCall} :
      StorageCallStep s call t → StorageRun t calls u → StorageRun s (call :: calls) u

/-- How many of the calls are `bridgeInitialize` or `reinitializeToken`: the calls that write the
version slot. -/
def versionCalls : List StorageCall → ℕ
  | [] => 0
  | .bridgeInitialize :: calls => versionCalls calls + 1
  | .reinitializeToken :: calls => versionCalls calls + 1
  | .ledger :: calls => versionCalls calls

/-- How many of the calls are `bridgeInitialize`. -/
def initializeCalls : List StorageCall → ℕ
  | [] => 0
  | .bridgeInitialize :: calls => initializeCalls calls + 1
  | .reinitializeToken :: calls => initializeCalls calls
  | .ledger :: calls => initializeCalls calls

end Contracts.BridgedStandardERC20
