import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `PermanentRestriction.validateCall` and its check on migrations

Source: branch `feat/upgrade-simplification` of the zksync-era `contracts` repository at
commit `e561b9cc2` (the upgrade-system snapshot, as `EraSpec.Contracts.ChainTypeManager`).
Paths are relative to `l1-contracts/contracts/`; a bare `:n` is
`governance/PermanentRestriction.sol:n`.  The functions modelled here are the same at the
pinned interop tree `c67894b9`, eight lines earlier (`validateCall` at :128,
`_getNewAdminFromMigration` at :290-357, the handler comparison at :348); the two copies
differ only in `allowL2Admin` (:115-133), which is not modelled.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.ChainAdmin.Properties.PermanentRestrictionMigration` and are proved in
`EraSpec.Contracts.ChainAdmin.Proofs.PermanentRestrictionMigration`.

## The claim under test

`PermanentRestriction` (P) is a restriction that a `ChainAdmin` consults on every call of
its `multicall` (`governance/ChainAdmin.sol:83-115`: `_validateCall` calls
`Restriction(r).validateCall(_call, msg.sender)` for every active restriction `r`, and a
revert there reverts the multicall).  Its NatSpec (:39-40):

    /// @notice This contract should be used by chains that wish to guarantee that certain security
    /// properties are preserved forever.

Migrating the chain to an L2 settlement layer installs a new admin there.  P's only check
on that is `_validateMigrationToL2` (:149-156): the decoded L2 admin must be in
`allowedL2Admins` (filled by `allowL2Admin`, :115-133, with addresses the
`L2_ADMIN_FACTORY` deploys).  The check runs only if `_getNewAdminFromMigration` reports
a migration.

## `validateCall` (:136-143)

    function validateCall(Call calldata _call, address /* _invoker */) external view override {
        _validateAsChainAdmin(_call);
        _validateMigrationToL2(_call);
        _validateRemoveRestriction(_call);
    }

All three are `view` and either return or revert; `validateCall` passes iff all three
pass.  `msg.sender` inside P is the `ChainAdmin` that consults it (`chainAdmin` below);
the invoker argument is ignored.

## `_getNewAdminFromMigration` (:298-365)

    if (_call.target != address(BRIDGE_HUB)) return (address(0), false);                 // :299-301
    if (_call.data.length < 4) return (address(0), false);                               // :303-305
    if (bytes4(_call.data[:4]) != IL1Bridgehub.requestL2TransactionTwoBridges.selector)
        return (address(0), false);                                                      // :307-309
    address sharedBridge = address(BRIDGE_HUB.assetRouter());                            // :311
    L2TransactionRequestTwoBridgesOuter memory request =
        abi.decode(_call.data[4:], (L2TransactionRequestTwoBridgesOuter));               // :315-318
    if (request.secondBridgeAddress != sharedBridge) return (address(0), false);         // :320-322
    bytes memory secondBridgeData = request.secondBridgeCalldata;                        // :324
    if (secondBridgeData.length == 0) return (address(0), false);                        // :325-327
    if (secondBridgeData[0] != NEW_ENCODING_VERSION) return (address(0), false);         // :329-331
    bytes memory encodedData = <secondBridgeData without its first byte>;               // :332-335
    (bytes32 chainAssetId, bytes memory bridgehubData) =
        abi.decode(encodedData, (bytes32, bytes));                                       // :343
    address ctmAddress = BRIDGE_HUB.ctmAssetIdToAddress(chainAssetId);                   // :348
    if (ctmAddress == address(0)) return (address(0), false);                            // :349-351
    // Almost certainly it will be Bridgehub, but we add this check just in case we have circumstances
    // that require us to use a different asset handler.                                // :353-354
    address assetHandlerAddress = IAssetRouterBase(sharedBridge).assetHandlerAddress(chainAssetId); // :355
    if (assetHandlerAddress != address(BRIDGE_HUB)) return (address(0), false);          // :356-358
    BridgehubBurnCTMAssetData memory burnData =
        abi.decode(bridgehubData, (BridgehubBurnCTMAssetData));                          // :361
    (address l2Admin, ) = abi.decode(burnData.ctmData, (address, bytes));               // :362
    return (l2Admin, true);                                                              // :364

`NEW_ENCODING_VERSION = 0x01` (`bridge/asset-router/IAssetRouterBase.sol:6`).

## Who is the CTM asset's handler

* `CTMDeploymentTracker.registerCTMAssetOnL1` and `setCtmAssetHandlerAddressOnL1`
  (`core/ctm-deployment/CTMDeploymentTracker.sol:71-80, 86-91`) register
  `BRIDGE_HUB.chainAssetHandler()` as the CTM asset's handler, not the Bridgehub.  The
  topic `CtmAssetHandlerWriters` models every writer of that slot.
* `chainAssetHandler` is a separate contract, set by `L1Bridgehub.setAddresses`
  (`core/bridgehub/L1Bridgehub.sol:268-280`).  The chain-migration entry point `bridgeBurn`
  is implemented by `ChainAssetHandlerBase` (`core/chain-asset-handler/ChainAssetHandlerBase.sol:188-254`).
  Neither `BridgehubBase` nor `L1Bridgehub` declares `bridgeBurn`, a `fallback` or a
  `receive` (the compiled ABI `l1-contracts/zkstack-out/L1Bridgehub.sol/L1Bridgehub.json`
  at both snapshots has no function with selector `0x699b0fb9` =
  `bridgeBurn(uint256,uint256,bytes32,address,bytes)` and none with `0x3408e470` =
  `getChainId()`).
* The unit test makes the check fire by mocking the router's `assetHandlerAddress` to
  return the Bridgehub
  (`l1-contracts/test/foundry/l1/unit/concrete/Governance/PermanentRestriction.t.sol:507-511`),
  so the deployed configuration is never exercised.

## What happens downstream of a migration request

When the `ChainAdmin` then makes the call, `L1Bridgehub.requestL2TransactionTwoBridges`
(`core/bridgehub/L1Bridgehub.sol:200-265`) calls `bridgehubDeposit` on the request's
second bridge (:232-238).  For the asset router that is
`L1AssetRouter.bridgehubDeposit` (`bridge/asset-router/L1AssetRouter.sol:199-234`) →
`_bridgehubDeposit` (`bridge/asset-router/AssetRouterBase.sol:118-138`, version `0x01`
only) → `_bridgehubDepositNonBaseTokenAsset` (:140-183) → `_burn` (:303-331), which
decodes the asset id from the same bytes as P (`common/libraries/DataEncoding.sol:69-75`:
`abi.decode(_dataWithVersion[1:], (bytes32, bytes))`) and calls `bridgeBurn` on
`assetHandlerAddress[_assetId]`, or on the native token vault when that is zero
(:312-330).  `burnTarget` is that address.  A successful chain migration needs that
`bridgeBurn` to return.

## Modelling choices

* **The call is bytes, as in the source; every decode is a parameter.**  Each
  `abi.decode` P performs is a field of `Abi`: a partial function from bytes to the
  decoded ABI value, `none` where the decode reverts.  The results quantify over every
  `Abi`, so they assume nothing about the ABI layout (`SOL-ABI`).  The router's calldata
  decode of `(bytes32, bytes)` is taken to be the same function as P's memory decode.
* **A revert is `false`.**  `validateCall` returns `true` when P returns and `false` when
  it reverts.  Which error is raised is not modelled.
* **Environment reads are total.**  `BRIDGE_HUB.assetRouter()`, `ctmAssetIdToAddress`,
  `assetHandlerAddress` and `getZKChain` are storage reads of deployed contracts and are
  fields of `Env`; `IZKChain(_chain).getAdmin()` is read only for a registered chain.
  `IChainAdmin(a).isRestrictionActive(this)` may revert (an address with no
  `ChainAdmin` code), so it is `Option Bool`.
* **Code facts are fields.**  `chainIdOf a` is the result of
  `_getChainIdUnffallibleCall(a)` (:272-290): `some id` iff the static call of
  `getChainId()` succeeds with 32 bytes of returndata.  `implementsBridgeBurn a` says a
  `bridgeBurn` call on `a` can return.  For the Bridgehub both are fixed by the source
  above (`VM-CALL`: a call of an undeclared selector on a contract with no `fallback`
  reverts); the properties take them as named premises.
* **State is frozen between P's check and the call.**  The `ChainAdmin` validates call
  `i` and then makes it (`governance/ChainAdmin.sol:87-91`); nothing runs in between.
  Inside the call, `bridgehubDepositBaseToken` (`core/bridgehub/L1Bridgehub.sol:207-229`)
  writes no router handler, so `_burn` reads the slot P read.
* **Not modelled:** events, `msg.value`, the error selectors, gas, the `ChainAdmin`'s
  other restrictions (topic `Restrictions` of wave-3 item W-UP-3), and what the chain
  asset handler does inside `bridgeBurn`.  At `e561b9cc2` that `bridgeBurn` reverts in
  production, because `CHAIN_MIGRATIONS_ENABLED = false` (`common/Config.sol:313`,
  enforced by `whenMigrationsEnabled`, `ChainAssetHandlerBase.sol:151-156, 201`); at the
  pin it is gated only by the runtime pause.  A future release re-enables it.
-/

namespace Contracts.ChainAdmin.PermanentRestrictionMigration

/-- Addresses, asset ids, chain ids and code hashes as 256-bit words; `0` is the zero
address and every mapping's unset value. -/
abbrev Address := UInt256
abbrev AssetId := UInt256
abbrev ChainId := UInt256
abbrev Bytes32 := UInt256

/-- Byte strings: calldata and `bytes` fields. -/
abbrev Bytes := List UInt8

/-! ## The ABI values P decodes -/

/-- `L2TransactionRequestTwoBridgesOuter` (`core/bridgehub/IBridgehubBase.sol:22-32`).  P
reads `secondBridgeAddress` and `secondBridgeCalldata`. -/
structure TwoBridgesRequest where
  chainId : ChainId
  mintValue : UInt256
  l2Value : UInt256
  l2GasLimit : UInt256
  l2GasPerPubdataByteLimit : UInt256
  refundRecipient : Address
  secondBridgeAddress : Address
  secondBridgeValue : UInt256
  secondBridgeCalldata : Bytes
  deriving DecidableEq

/-- `BridgehubBurnCTMAssetData` (`core/bridgehub/IBridgehubBase.sol:51-55`). -/
structure BurnCTMAssetData where
  chainId : ChainId
  ctmData : Bytes
  chainData : Bytes
  deriving DecidableEq

/-- Every `abi.decode` P performs, as a partial function on bytes; `none` means the decode
reverts. -/
structure Abi where
  /-- `abi.decode(b, (address))`, for `setPendingAdmin` (:193) and `removeRestriction`
  (:224). -/
  decodeAddress : Bytes → Option Address
  /-- `abi.decode(b, (L2TransactionRequestTwoBridgesOuter))` (:315-318). -/
  decodeTwoBridges : Bytes → Option TwoBridgesRequest
  /-- `abi.decode(b, (bytes32, bytes))` (:343; also the router's decode,
  `common/libraries/DataEncoding.sol:74`). -/
  decodeAssetData : Bytes → Option (AssetId × Bytes)
  /-- `abi.decode(b, (BridgehubBurnCTMAssetData))` (:361). -/
  decodeBurnData : Bytes → Option BurnCTMAssetData
  /-- `abi.decode(b, (address, bytes))` (:362). -/
  decodeAdminAndBytes : Bytes → Option (Address × Bytes)

/-- `Call` (`governance/Common.sol:9-13`). -/
structure Call where
  target : Address
  value : UInt256
  data : Bytes

/-! ## Constants -/

/-- `IAdmin.setPendingAdmin.selector` = `bytes4(keccak256("setPendingAdmin(address)"))`. -/
def setPendingAdminSelector : Bytes := [0x4d, 0xd1, 0x8b, 0xf5]

/-- `IChainAdmin.removeRestriction.selector` =
`bytes4(keccak256("removeRestriction(address)"))`. -/
def removeRestrictionSelector : Bytes := [0x69, 0xa5, 0xb9, 0x50]

/-- `IL1Bridgehub.requestL2TransactionTwoBridges.selector` =
`bytes4(keccak256("requestL2TransactionTwoBridges((uint256,uint256,uint256,uint256,uint256,address,address,uint256,bytes))"))`. -/
def requestL2TransactionTwoBridgesSelector : Bytes := [0x24, 0xfd, 0x57, 0xfb]

/-- `NEW_ENCODING_VERSION` (`bridge/asset-router/IAssetRouterBase.sol:6`). -/
def NEW_ENCODING_VERSION : UInt8 := 0x01

/-- `bytes4(_call.data[:4])`, for data of at least four bytes. -/
def selectorOf (data : Bytes) : Bytes := data.take 4

/-- `_call.data[4:]`. -/
def argsOf (data : Bytes) : Bytes := data.drop 4

/-! ## What P reads -/

/-- Everything `validateCall` reads, plus two code facts about the migration path. -/
structure Env where
  /-- `BRIDGE_HUB`, P's immutable (:45, :67). -/
  bridgehub : Address
  /-- `address(this)`, P itself. -/
  self : Address
  /-- `BRIDGE_HUB.assetRouter()` (`core/bridgehub/BridgehubBase.sol:66`). -/
  assetRouter : Address
  /-- `BRIDGE_HUB.ctmAssetIdToAddress(id)` (`core/bridgehub/BridgehubBase.sol:103`). -/
  ctmAssetIdToAddress : AssetId → Address
  /-- `assetHandlerAddress(id)` of the router at `assetRouter`
  (`bridge/asset-router/AssetRouterBase.sol:41`). -/
  assetHandlerAddress : AssetId → Address
  /-- `BRIDGE_HUB.chainAssetHandler()` (`core/bridgehub/BridgehubBase.sol:124`).  P never
  reads it; the repaired check below does. -/
  chainAssetHandler : Address
  /-- The router's `nativeTokenVault` (`bridge/asset-router/L1AssetRouter.sol:118`), which
  `_burn` calls when no handler is registered. -/
  ntv : Address
  /-- Whether a `bridgeBurn` call on the address can return (code fact; see the header). -/
  implementsBridgeBurn : Address → Bool
  /-- `_getChainIdUnffallibleCall(a)` (:272-290): `some id` iff `getChainId()` succeeds with
  32 bytes of returndata. -/
  chainIdOf : Address → Option ChainId
  /-- `BRIDGE_HUB.getZKChain(id)` (`core/bridgehub/BridgehubBase.sol:344-347`). -/
  zkChain : ChainId → Address
  /-- `IZKChain(a).getAdmin()`. -/
  adminOf : Address → Address
  /-- `a.codehash`. -/
  codehash : Address → Bytes32
  /-- `IChainAdmin(a).isRestrictionActive(r)`; `none` where the call reverts. -/
  isRestrictionActive : Address → Address → Option Bool
  /-- `allowedAdminImplementations` (:54). -/
  allowedAdminImplementations : Bytes32 → Bool
  /-- `allowedCalls`, keyed by the full calldata (:57). -/
  allowedCalls : Bytes → Bool
  /-- `selectorsToValidate` (:60). -/
  selectorsToValidate : Bytes → Bool
  /-- `allowedL2Admins` (:63). -/
  allowedL2Admins : Address → Bool

/-! ## `_getNewAdminFromMigration` -/

/-- The three outcomes of `_getNewAdminFromMigration`. -/
inductive MigrationRead where
  /-- It returns `(address(0), false)`: not a migration, nothing checked. -/
  | notMigration
  /-- It returns `(l2Admin, true)`: a migration to `l2Admin`, which `_validateMigrationToL2`
  then checks. -/
  | migration (l2Admin : Address)
  /-- One of its decodes reverts (:315-318, :343, :361, :362). -/
  | reverts
  deriving DecidableEq

/-- `_getNewAdminFromMigration` (:298-365), with the address the CTM asset's handler is
compared against as a parameter `expectedHandler`.  P compares it with
`address(BRIDGE_HUB)` (:356); `newAdminFromMigration` is that instance. -/
def newAdminFromMigrationWith (A : Abi) (E : Env) (expectedHandler : Address) (c : Call) :
    MigrationRead :=
  if c.target ≠ E.bridgehub then .notMigration
  else if c.data.length < 4 then .notMigration
  else if selectorOf c.data ≠ requestL2TransactionTwoBridgesSelector then .notMigration
  else
    match A.decodeTwoBridges (argsOf c.data) with
    | none => .reverts
    | some request =>
      if request.secondBridgeAddress ≠ E.assetRouter then .notMigration
      else
        match request.secondBridgeCalldata with
        | [] => .notMigration
        | version :: encodedData =>
          if version ≠ NEW_ENCODING_VERSION then .notMigration
          else
            match A.decodeAssetData encodedData with
            | none => .reverts
            | some (chainAssetId, bridgehubData) =>
              if E.ctmAssetIdToAddress chainAssetId = 0 then .notMigration
              else if E.assetHandlerAddress chainAssetId ≠ expectedHandler then .notMigration
              else
                match A.decodeBurnData bridgehubData with
                | none => .reverts
                | some burnData =>
                  match A.decodeAdminAndBytes burnData.ctmData with
                  | none => .reverts
                  | some (l2Admin, _) => .migration l2Admin

/-- `_getNewAdminFromMigration` as deployed: the handler must be `address(BRIDGE_HUB)`. -/
def newAdminFromMigration (A : Abi) (E : Env) (c : Call) : MigrationRead :=
  newAdminFromMigrationWith A E E.bridgehub c

/-- `_validateMigrationToL2` (:149-156), against a given expected handler: a migration must
name a whitelisted L2 admin. -/
def validateMigrationToL2With (A : Abi) (E : Env) (expectedHandler : Address) (c : Call) :
    Bool :=
  match newAdminFromMigrationWith A E expectedHandler c with
  | .notMigration => true
  | .migration l2Admin => E.allowedL2Admins l2Admin
  | .reverts => false

/-- `_validateMigrationToL2` as deployed. -/
def validateMigrationToL2 (A : Abi) (E : Env) (c : Call) : Bool :=
  validateMigrationToL2With A E E.bridgehub c

/-! ## The other two checks -/

/-- `_isAdminOfAChain(chain)` (:233-263), with `msg.sender = chainAdmin`: `chain` is a ZK
chain registered in the Bridgehub under the id it reports, and its admin is the
`ChainAdmin`. -/
def isAdminOfAChain (E : Env) (chainAdmin chain : Address) : Bool :=
  if chain = 0 then false
  else
    match E.chainIdOf chain with
    | none => false
    | some chainId =>
      if E.zkChain chainId ≠ chain then false else decide (E.adminOf chain = chainAdmin)

/-- `_validateNewAdmin` (:192-206): the new admin's code hash is allowed, and it reports P
as an active restriction. -/
def validateNewAdmin (A : Abi) (E : Env) (c : Call) : Bool :=
  match A.decodeAddress (argsOf c.data) with
  | none => false
  | some newChainAdmin =>
    E.allowedAdminImplementations (E.codehash newChainAdmin) &&
      decide (E.isRestrictionActive newChainAdmin E.self = some true)

/-- `_validateAsChainAdmin` (:160-187). -/
def validateAsChainAdmin (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) : Bool :=
  if isAdminOfAChain E chainAdmin c.target = false then true
  else if c.data.length < 4 then true
  else if selectorOf c.data = setPendingAdminSelector then validateNewAdmin A E c
  else if E.selectorsToValidate (selectorOf c.data) = false then true
  else E.allowedCalls c.data

/-- `_validateRemoveRestriction` (:211-229): a call of the `ChainAdmin` on itself must not
remove P. -/
def validateRemoveRestriction (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) : Bool :=
  if c.target ≠ chainAdmin then true
  else if c.data.length < 4 then true
  else if selectorOf c.data ≠ removeRestrictionSelector then true
  else
    match A.decodeAddress (argsOf c.data) with
    | none => false
    | some removed => decide (removed ≠ E.self)

/-! ## `validateCall` -/

/-- `validateCall` (:136-143), against a given expected handler for the migration check;
`true` iff P returns. -/
def validateCallWith (A : Abi) (E : Env) (expectedHandler chainAdmin : Address) (c : Call) :
    Bool :=
  validateAsChainAdmin A E chainAdmin c && validateMigrationToL2With A E expectedHandler c &&
    validateRemoveRestriction A E chainAdmin c

/-- **`validateCall` as deployed** (:136-143), consulted by `chainAdmin`. -/
def validateCall (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) : Bool :=
  validateCallWith A E E.bridgehub chainAdmin c

/-- **The one-line repair**: compare the handler with `BRIDGE_HUB.chainAssetHandler()`
instead of `address(BRIDGE_HUB)` at :356.  Not in the source. -/
def validateCallRepaired (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) : Bool :=
  validateCallWith A E E.chainAssetHandler chainAdmin c

/-! ## Migration requests -/

/-- `c` is a well-formed `requestL2TransactionTwoBridges` call to P's Bridgehub whose
second bridge is the Bridgehub's asset router and whose second-bridge data has version
`NEW_ENCODING_VERSION` and decodes as `(chainAssetId, bridgehubData)`.  These are the
conditions at :299-343, the ones that do not read the asset id.  The router accepts the
same data on its migration path (`bridge/asset-router/AssetRouterBase.sol:118-149`). -/
def MigrationRequest (A : Abi) (E : Env) (c : Call) (chainAssetId : AssetId)
    (bridgehubData : Bytes) : Prop :=
  c.target = E.bridgehub ∧
    ∃ (args : Bytes) (request : TwoBridgesRequest) (encodedData : Bytes),
      c.data = requestL2TransactionTwoBridgesSelector ++ args ∧
      A.decodeTwoBridges args = some request ∧
      request.secondBridgeAddress = E.assetRouter ∧
      request.secondBridgeCalldata = NEW_ENCODING_VERSION :: encodedData ∧
      A.decodeAssetData encodedData = some (chainAssetId, bridgehubData)

/-- The L2 admin P decodes from `bridgehubData` (:361-362), if both decodes succeed. -/
def burnAdmin (A : Abi) (bridgehubData : Bytes) : Option Address :=
  match A.decodeBurnData bridgehubData with
  | none => none
  | some burnData =>
    match A.decodeAdminAndBytes burnData.ctmData with
    | none => none
    | some (l2Admin, _) => some l2Admin

/-- The address the router's `_burn` calls `bridgeBurn` on for asset `chainAssetId`
(`bridge/asset-router/AssetRouterBase.sol:312-330`): the registered handler, or the native
token vault when none is registered. -/
def burnTarget (E : Env) (chainAssetId : AssetId) : Address :=
  if E.assetHandlerAddress chainAssetId = 0 then E.ntv else E.assetHandlerAddress chainAssetId

/-- The Bridgehub answers no `getChainId()`, so `_getChainIdUnffallibleCall` fails on it
(no such function and no `fallback` in `BridgehubBase` / `L1Bridgehub`; `VM-CALL`). -/
def BridgehubAnswersNoChainId (E : Env) : Prop := E.chainIdOf E.bridgehub = none

/-! ## Witness data

Bridgehub `10`, P `11`, asset router `12`, chain asset handler `13`, native token vault
`14`, the consulting `ChainAdmin` `20`, a CTM `30`, its asset id `100`, and the L2 admin
`66`, which no whitelist entry names.  The decoders are toys on short byte strings: the
call's data is the selector followed by the single byte `1`.  They only witness that the
premises can hold together; the results hold for every `Abi`. -/

/-- The witness request: second bridge `12`, second-bridge data `[0x01, 2]`. -/
def prmRequest : TwoBridgesRequest :=
  ⟨0, 0, 0, 0, 0, 0, 12, 0, [0x01, 2]⟩

/-- The witness burn data: chain `40`, CTM data `[4]`. -/
def prmBurnData : BurnCTMAssetData := ⟨40, [4], []⟩

/-- Toy decoders: `[1]` is the request, `[2]` is `(100, [3])`, `[3]` is the burn data,
`[4]` is `(66, [])`, `[5]` is the address `66`; everything else reverts. -/
def prmAbi : Abi where
  decodeAddress := fun b => if b = [5] then some 66 else none
  decodeTwoBridges := fun b => if b = [1] then some prmRequest else none
  decodeAssetData := fun b => if b = [2] then some (100, [3]) else none
  decodeBurnData := fun b => if b = [3] then some prmBurnData else none
  decodeAdminAndBytes := fun b => if b = [4] then some (66, []) else none

/-- The deployed configuration: the CTM asset `100` belongs to CTM `30` and its handler is
the chain asset handler `13`, which implements `bridgeBurn`; the Bridgehub `10` implements
neither `bridgeBurn` nor `getChainId()`; no L2 admin is whitelisted. -/
def prmEnv : Env where
  bridgehub := 10
  self := 11
  assetRouter := 12
  ctmAssetIdToAddress := fun a => if a = 100 then 30 else 0
  assetHandlerAddress := fun a => if a = 100 then 13 else 0
  chainAssetHandler := 13
  ntv := 14
  implementsBridgeBurn := fun a => decide (a = 13) || decide (a = 14)
  chainIdOf := fun _ => none
  zkChain := fun _ => 0
  adminOf := fun _ => 0
  codehash := fun _ => 0
  isRestrictionActive := fun _ _ => none
  allowedAdminImplementations := fun _ => false
  allowedCalls := fun _ => false
  selectorsToValidate := fun _ => false
  allowedL2Admins := fun _ => false

/-- The configuration P's comment at :353-354 expects: the same, but the CTM asset's
handler is the Bridgehub. -/
def prmEnvHandlerIsBridgehub : Env :=
  { prmEnv with assetHandlerAddress := fun a => if a = 100 then 10 else 0 }

/-- The deployed configuration with `66` whitelisted. -/
def prmEnvWhitelisted : Env :=
  { prmEnv with allowedL2Admins := fun a => decide (a = 66) }

/-- The witness migration call: `requestL2TransactionTwoBridges` on the Bridgehub with
argument bytes `[1]`. -/
def prmCall : Call := ⟨10, 0, requestL2TransactionTwoBridgesSelector ++ [1]⟩

end Contracts.ChainAdmin.PermanentRestrictionMigration
