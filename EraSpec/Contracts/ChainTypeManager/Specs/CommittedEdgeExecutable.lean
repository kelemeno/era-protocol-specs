import EraSpec.Contracts.ChainTypeManager.Specs.VersionRegistry

/-!
# Model: the commit-time edge checks and the chain-side upgrade checks they must imply

Source: branch `draft/v0.35.0` of the zksync-era `contracts` repository at commit
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5` (`b17415d20`). Every `file:line` below is at that
commit; paths are relative to `l1-contracts/contracts/`. The files this topic transcribes
(`VersionEdgeLib`, `L2PlanLib`, `CTMUpgradeComposer`, `L2CanonicalTransactionLib`,
`BaseZkSyncUpgrade`, `TransactionValidator`, `BytecodesSupplier`, and the CTM's commit and
replace paths) are unchanged between `d9f678900` and `b17415d20`. The registry objects do not
exist on `main` (`70096e2ea`).

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.CommittedEdgeExecutable` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.CommittedEdgeExecutable`. Namespace
`Contracts.ChainTypeManager.EdgeChecks`.

## Why this is modelled

`VersionEdgeLib` states what its check is for (`upgrades/registry/libraries/VersionEdgeLib.sol:23-29`):

    /// @notice The version-shape and schedule rules every committed CTM edge obeys, checked when the
    ///         edge's object is constructed — before governance can commit an edge that would bump the
    ///         CTM and then revert on every chain.
    ...
    /// @notice Reverts unless the edge `_oldVersion -> _newVersion` with this schedule and L2 side
    ///         is one every chain can execute.

and `L2PlanLib.build` refuses plans "L2 could not execute", among them "more factory dependencies
than `BaseZkSyncUpgrade._verifyFactoryDeps` accepts would let `applyCTMUpgrade` bump the CTM and
then fail every chain upgrade" (`upgrades/registry/libraries/L2PlanLib.sol:38-44`). The checks a
chain runs when it crosses the edge are a second, hand-written copy in
`upgrades/BaseZkSyncUpgrade.sol`. This file transcribes both copies so that "the commit-time
copy implies the chain-side copy" is a theorem, with every premise it needs named.

## Commit time

* `CTMTransition`'s constructor (`upgrades/registry/objects/CTMTransition.sol:50-122`) reads the
  edge off the two releases (:61-64), builds the final L2 plan (:80-86), and runs
  `VersionEdgeLib.requireValidEdge` with `hasL2Side = derivedPlan.deployments.length != 0`
  (:90-97). `RegistryBootstrapMigration`'s constructor does the same for the bootstrap edge
  (`upgrades/registry/bootstrap/RegistryBootstrapMigration.sol:80-92`), with the manifest's
  `expectedProtocolVersion` as the departing version. `EdgeObject` and `Constructed` are this
  part of either constructor. Their other reverts (zero addresses, the releases' `validate()`,
  `_requireL2StateKept`, the facet-cut derivation) are not modelled: `Constructed` is implied by
  a successful construction, which is the direction the results use.
* `requireValidEdge` (`VersionEdgeLib.sol:35-91`) is `requireValidEdge`.
* `L2PlanLib.build` (`L2PlanLib.sol:47-82`) is `planBuild`, with `_unsafeDeployment` (:100-112)
  as `unsafeDeployment`.
* The CTM's commit and replace paths both run `_requireExecutable`
  (`state-transition/ChainTypeManager.sol:409, :436`, defined at :449-452):

        _transition.validate();
        L2PlanLib.requirePublished(BytecodesSupplier(L1_BYTECODES_SUPPLIER), _transition.l2Plan().factoryDepHashes);

  `requirePublished` (`L2PlanLib.sol:89-97`) is `requirePublished` over the supplier state.

## Chain side

A chain crosses a registry edge through `DefaultUpgrade.upgradeFromTransition`
(`upgrades/DefaultUpgrade.sol:29-43`), whose storage part is `_upgradeFromCommittedObject`
(:65-84): it reads `(newProtocolVersion, upgradeTimestamp, newRelease)` from the object, composes
the L2 transaction with `CTMUpgradeComposer.buildL2UpgradeTxFromPlan(_object.l2Plan(), ...)`
(:76-82) and calls `BaseZkSyncUpgrade._upgrade` (`upgrades/BaseZkSyncUpgrade.sol:72-108`). On the
settlement layer that is

    (uint32 newMinorVersion, bool isPatchOnly) = _setNewProtocolVersion(_newProtocolVersion, isOnSettlementLayer); // :96
    ...
    if (isOnSettlementLayer) {
        txHash = _setL2SystemContractUpgrade(_l2ProtocolUpgradeTx, newMinorVersion, isPatchOnly);              // :103-105
    }

* `_setNewProtocolVersion` (:218-272) is `setNewProtocolVersion`.
* `_setL2SystemContractUpgrade` (:162-202) is `setL2SystemContractUpgrade`, with
  `TransactionValidator.validateL1ToL2Transaction` (`state-transition/libraries/TransactionValidator.sol:31-55`),
  `validateUpgradeTransaction` (:59-100) and `getMinimalPriorityTransactionGasLimit` (:107-131).
  `_getUpgradeTxType()` is the constant `ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE`
  (`state-transition/chain-deps/facets/ZKChainBase.sol:200-202`).
* `upgradeStoragePart` is `_upgrade` without its time gate (:82-84), its settlement-layer order
  check for a chain off its settlement layer (:89-94) and the verifier installation (:97-99;
  `_setVerifier` there also refuses a verifier outside multi-proof mode on a chain that requires
  its second proof system, :143-148). Those are not what the commit-time checks are about;
  `UpgradeTiming` models the time gate and `ProofGateAtV35` the second-proof check.
* `CTMUpgradeComposer.buildL2UpgradeTxFromPlan`
  (`upgrades/registry/libraries/CTMUpgradeComposer.sol:83-113`) is `buildL2UpgradeTxFromPlan`, with
  `L2CanonicalTransactionLib.emptyL2CanonicalTransaction` and `upgradeTransaction`
  (`state-transition/libraries/L2CanonicalTransactionLib.sol:20-40, :50-62`).

## The supplier

`BytecodesSupplier.publishEVMBytecode` (`upgrades/BytecodesSupplier.sol:37-47`) refuses a hash
already published (:40-42) and writes `evmPublishingBlock[hash] = block.number` (:44); nothing
else in the contract writes the mapping. The supplier is a proxy under the CTM-domain
`ProxyAdmin` (`upgrades/registry/libraries/ContractIdentifiers.sol:56-58` lists it among the
CTM-domain proxies), so a proxy upgrade can replace its code. `SupplierStep.implementationSwap`
is that step, as an arbitrary new value of the mapping.

## Modelling choices

* **A revert is `none`.** Every function here is pure in the model and returns `none` exactly
  when the Solidity reverts. Reverts have no effects before them, so their order is immaterial.
  Solidity 0.8 checked arithmetic is transcribed where it can revert: the `uint32` subtraction of
  minors, the `uint256` products and sums of the gas formula, and the division by
  `gasPerPubdataByteLimit`.
* **Values are `ℕ`.** `SafeCast.toUint96` is `unpackChecked` (`none` above `2^96`); `uint32(x)`
  is `x % 2^32`; `>>` is `Nat.shiftRight`. A `bytes` value is `Bytes`, a list of byte values.
* **Abstract functions** (`PlanEnv`): `generateRandomAddress` (a keccak, truncated), the
  factory-dependency list `_factoryDepHashes` (`L2PlanLib.sol:118-149`, `none` when one of its
  decodes reverts), the ABI encoding of the `L2ComplexUpgrader` call, and
  `keccak256(abi.encode(tx))`. No property of any of them is assumed.
* **The delegate calldata** is the return value of the external call to the plan's composer
  (`CTMUpgradeComposer.sol:97-103`). It is a parameter: the results hold for whatever the
  composer returns, and the composer's call reverting is outside them.
* **The chain's state** is the three storage values the two functions read and write:
  `s.protocolVersion`, `s.l2SystemContractsUpgradeTxHash` and
  `s.l2SystemContractsUpgradeBatchNumber`. `s.feeParams.priorityTxMaxPubdata` is a parameter.
-/

namespace Contracts.ChainTypeManager.EdgeChecks

/-! ## Constants (`common/Config.sol`, `common/l2-helpers/L2ContractAddresses.sol`) -/

/-- `ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE = 126` (`common/Config.sol:67`). -/
def ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE : ℕ := 126

/-- `MAX_ALLOWED_MINOR_VERSION_DELTA = 100` (`common/Config.sol:73`). -/
def MAX_ALLOWED_MINOR_VERSION_DELTA : ℕ := 100

/-- `MAX_NEW_FACTORY_DEPS = 64` (`common/Config.sol:154`). -/
def MAX_NEW_FACTORY_DEPS : ℕ := 64

/-- `REQUIRED_L2_GAS_PRICE_PER_PUBDATA = 800` (`common/Config.sol:157`). -/
def REQUIRED_L2_GAS_PRICE_PER_PUBDATA : ℕ := 800

/-- `L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS = 21000` (`common/Config.sol:168`). -/
def L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS : ℕ := 21000

/-- `L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS = 40` (`common/Config.sol:171`). -/
def L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS : ℕ := 40

/-- `MAX_NATIVE_COMPUTATIONAL_ZKSYNC_OS = 1 << 35` (`common/Config.sol:174`). -/
def MAX_NATIVE_COMPUTATIONAL_ZKSYNC_OS : ℕ := 2 ^ 35

/-- `L1_TX_INTRINSIC_PUBDATA_ZKSYNC_OS = 351` (`common/Config.sol:178`). -/
def L1_TX_INTRINSIC_PUBDATA_ZKSYNC_OS : ℕ := 351

/-- `L1_TX_NATIVE_PER_GAS = 100_000_000` (`common/Config.sol:182`). -/
def L1_TX_NATIVE_PER_GAS : ℕ := 100000000

/-- `UPGRADE_TX_MAX_GAS_LIMIT = 72_000_000` (`common/Config.sol:200`). -/
def UPGRADE_TX_MAX_GAS_LIMIT : ℕ := 72000000

/-- `L2_FORCE_DEPLOYER_ADDR = SYSTEM_CONTRACTS_OFFSET + 0x07 = 0x8007`
(`common/l2-helpers/L2ContractAddresses.sol:6, :53`). -/
def L2_FORCE_DEPLOYER_ADDR : ℕ := 0x8007

/-- `L2_COMPLEX_UPGRADER_ADDR = SYSTEM_CONTRACTS_OFFSET + 0x0f = 0x800f`
(`common/l2-helpers/L2ContractAddresses.sol:6, :65`). -/
def L2_COMPLEX_UPGRADER_ADDR : ℕ := 0x800f

/-- `BYTECODE_INFO_LENGTH = 96` (`common/libraries/ZKSyncOSBytecodeInfo.sol:12`). -/
def BYTECODE_INFO_LENGTH : ℕ := 96

/-! ## Packed versions (`common/libraries/SemVer.sol`)

The same transcription as the unmerged `Contracts.SemVer` model on branch `cov2/encodings`
(`EraSpec/Contracts/SemVer/Specs/SemVer.lean`, written at `d9f6789`; `SemVer.sol` is unchanged at
`b17415d20`), restated here under this topic's names. -/

/-- `uint32(x)`: the low 32 bits. -/
def edgeToUint32 (x : ℕ) : ℕ := x % 2 ^ 32

/-- `SemVer.unpackSemVer(v)` (`common/libraries/SemVer.sol:25-31`), as `(major, minor, patch)`:
`patch = uint32(v)` (:28), `minor = uint32(v >> SEMVER_MINOR_OFFSET)` (:29, offset `32` at :7),
`major = uint32(v >> SEMVER_MAJOR_OFFSET)` (:30, offset `64` at :12). -/
def edgeUnpackSemVer (v : ℕ) : ℕ × ℕ × ℕ :=
  (edgeToUint32 (v >>> 64), edgeToUint32 (v >>> 32), edgeToUint32 v)

/-- `SemVer.unpackSemVer(SafeCast.toUint96(v))`, as every call site below writes it.
`SafeCast.toUint96` reverts above `type(uint96).max`; `none` is that revert. -/
def unpackChecked (v : ℕ) : Option (ℕ × ℕ × ℕ) :=
  if v < 2 ^ 96 then some (edgeUnpackSemVer v) else none

/-- The major component, `uint32(v >> 64)`. -/
def majorOf (v : ℕ) : ℕ := (edgeUnpackSemVer v).1

/-- The minor component, `uint32(v >> 32)`. -/
def minorOf (v : ℕ) : ℕ := (edgeUnpackSemVer v).2.1

/-- `L2CanonicalTransactionLib.protocolUpgradeNonce(_protocolVersion)`
(`state-transition/libraries/L2CanonicalTransactionLib.sol:70-72`):
`_protocolVersion >> SEMVER_MINOR_OFFSET`. -/
def protocolUpgradeNonce (v : ℕ) : ℕ := v >>> 32

/-- A version every check below accepts the shape of: it fits a `uint96` and its major
component is zero. This is a name for the results, not a source definition. -/
def VersionWf (v : ℕ) : Prop := v < 2 ^ 96 ∧ majorOf v = 0

/-- The version shape of an edge `old → new` that both copies of the checks require: the
version increases, both versions are well formed, and the minor component moves forward by at
most `MAX_ALLOWED_MINOR_VERSION_DELTA` (the minor cannot move back once the first three hold).
This is a name for the results, not a source definition. -/
def EdgeVersionShape (old new : ℕ) : Prop :=
  old < new ∧ VersionWf old ∧ VersionWf new ∧
    minorOf new - minorOf old ≤ MAX_ALLOWED_MINOR_VERSION_DELTA

instance (v : ℕ) : Decidable (VersionWf v) := inferInstanceAs (Decidable (_ ∧ _))

instance (old new : ℕ) : Decidable (EdgeVersionShape old new) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-! ## `VersionEdgeLib.requireValidEdge` -/

/-- `VersionEdgeLib.requireValidEdge(_oldVersion, _newVersion, _oldVersionDeadline,
_upgradeTimestamp, _hasL2Side)` (`upgrades/registry/libraries/VersionEdgeLib.sol:35-91`); `some ()`
when it returns.

    if (_newVersion <= _oldVersion) { revert ProtocolVersionTooSmall(...); }                  // :44-46
    if (_oldVersionDeadline == 0) { revert TransitionDeadlineZero(); }                       // :55-57
    if (_oldVersionDeadline < _upgradeTimestamp) { revert TransitionDeadlineBeforeUpgrade(...); } // :60-62
    (uint32 oldMajor, uint32 oldMinor, ) = SemVer.unpackSemVer(SafeCast.toUint96(_oldVersion)); // :66
    (uint32 newMajor, uint32 newMinor, ) = SemVer.unpackSemVer(SafeCast.toUint96(_newVersion)); // :68
    if (oldMajor != 0) { revert PreviousProtocolMajorVersionNotZero(); }                     // :72-74
    if (newMajor != 0) { revert NewProtocolMajorVersionNotZero(); }                          // :75-77
    uint256 minorDelta = newMinor - oldMinor;                                                // :80
    if (minorDelta > MAX_ALLOWED_MINOR_VERSION_DELTA) { revert ProtocolVersionMinorDeltaTooBig(...); } // :81-83
    if (oldMinor == newMinor && _hasL2Side) { revert PatchCannotCarryL2Upgrade(); }          // :88-90

The subtraction at :80 is on `uint32` operands and reverts on underflow (checked arithmetic). -/
def requireValidEdge (old new deadline upgradeTs : ℕ) (hasL2Side : Bool) : Option Unit :=
  if new ≤ old then none else
  if deadline = 0 then none else
  if deadline < upgradeTs then none else
  match unpackChecked old, unpackChecked new with
  | some (oM, om, _), some (nM, nm, _) =>
    if oM ≠ 0 then none else
    if nM ≠ 0 then none else
    if nm < om then none else
    if MAX_ALLOWED_MINOR_VERSION_DELTA < nm - om then none else
    if om = nm ∧ hasL2Side = true then none else
    some ()
  | _, _ => none

/-! ## The L2 plan (`L2PlanLib`, `RegistryTypes.sol`) -/

/-- `IComplexUpgrader.ContractUpgradeType` (`state-transition/l2-deps/IComplexUpgrader.sol:19-23`). -/
inductive ContractUpgradeType
  /-- `__DEPRECATED_EraForceDeployment`. -/
  | deprecatedEraForceDeployment
  /-- `ZKsyncOSSystemProxyUpgrade`. -/
  | systemProxyUpgrade
  /-- `ZKsyncOSUnsafeForceDeployment`. -/
  | unsafeForceDeployment
deriving DecidableEq

/-- A Solidity `bytes` value, as its list of byte values. -/
abbrev Bytes := List ℕ

/-- `IComplexUpgrader.UniversalContractUpgradeInfo` (`IComplexUpgrader.sol:29-33`). -/
structure Deployment where
  /-- `upgradeType`. -/
  upgradeType : ContractUpgradeType
  /-- `deployedBytecodeInfo`. -/
  deployedBytecodeInfo : Bytes
  /-- `newAddress`. -/
  newAddress : ℕ
deriving DecidableEq

/-- `AuthoredL2Plan` (`upgrades/registry/RegistryTypes.sol:127-131`): the manifest's authored L2
input. -/
structure AuthoredL2Plan where
  /-- `delegateBytecodeInfo`; empty means no delegate. -/
  delegateBytecodeInfo : Bytes
  /-- `extraBytecodeInfos`. -/
  extraBytecodeInfos : List Bytes
  /-- `delegateComposer`; `0` means none. -/
  delegateComposer : ℕ
deriving DecidableEq

/-- `L2UpgradePlan` (`upgrades/registry/RegistryTypes.sol:99-104`): the final plan. -/
structure L2UpgradePlan where
  /-- `deployments`. -/
  deployments : List Deployment
  /-- `delegateTo`; `0` means none. -/
  delegateTo : ℕ
  /-- `delegateComposer`. -/
  delegateComposer : ℕ
  /-- `factoryDepHashes`. -/
  factoryDepHashes : List ℕ
deriving DecidableEq

/-! ## The L2 transaction (`common/Messaging.sol`, `L2CanonicalTransactionLib`) -/

/-- `L2CanonicalTransaction`. Fields `sender` and `recipient` are the struct's `from` and `to`;
`reserved` is the `uint256[4]` array. -/
structure L2Tx where
  /-- `txType`. -/
  txType : ℕ
  /-- `from`. -/
  sender : ℕ
  /-- `to`. -/
  recipient : ℕ
  /-- `gasLimit`. -/
  gasLimit : ℕ
  /-- `gasPerPubdataByteLimit`. -/
  gasPerPubdataByteLimit : ℕ
  /-- `maxFeePerGas`. -/
  maxFeePerGas : ℕ
  /-- `maxPriorityFeePerGas`. -/
  maxPriorityFeePerGas : ℕ
  /-- `paymaster`. -/
  paymaster : ℕ
  /-- `nonce`. -/
  nonce : ℕ
  /-- `value`. -/
  value : ℕ
  /-- `reserved[0..3]`. -/
  reserved : ℕ × ℕ × ℕ × ℕ
  /-- `data`. -/
  data : Bytes
  /-- `signature`. -/
  signature : Bytes
  /-- `factoryDeps`. -/
  factoryDeps : List ℕ
  /-- `paymasterInput`. -/
  paymasterInput : Bytes
  /-- `reservedDynamic`. -/
  reservedDynamic : Bytes
deriving DecidableEq

/-- `L2CanonicalTransactionLib.emptyL2CanonicalTransaction()` (`L2CanonicalTransactionLib.sol:20-40`):
every field zero or empty, so `txType == 0`. -/
def emptyL2CanonicalTransaction : L2Tx where
  txType := 0
  sender := 0
  recipient := 0
  gasLimit := 0
  gasPerPubdataByteLimit := 0
  maxFeePerGas := 0
  maxPriorityFeePerGas := 0
  paymaster := 0
  nonce := 0
  value := 0
  reserved := (0, 0, 0, 0)
  data := []
  signature := []
  factoryDeps := []
  paymasterInput := []
  reservedDynamic := []

/-- `L2CanonicalTransactionLib.upgradeTransaction(_protocolVersion, _complexUpgraderCalldata)`
(`L2CanonicalTransactionLib.sol:50-62`):

    transaction = emptyL2CanonicalTransaction();
    transaction.txType = ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE;
    transaction.from = uint256(uint160(L2_FORCE_DEPLOYER_ADDR));
    transaction.to = uint256(uint160(L2_COMPLEX_UPGRADER_ADDR));
    transaction.gasLimit = UPGRADE_TX_MAX_GAS_LIMIT;
    transaction.gasPerPubdataByteLimit = REQUIRED_L2_GAS_PRICE_PER_PUBDATA;
    transaction.nonce = protocolUpgradeNonce(_protocolVersion);
    transaction.data = _complexUpgraderCalldata; -/
def upgradeTransaction (v : ℕ) (calldata : Bytes) : L2Tx :=
  { emptyL2CanonicalTransaction with
    txType := ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE
    sender := L2_FORCE_DEPLOYER_ADDR
    recipient := L2_COMPLEX_UPGRADER_ADDR
    gasLimit := UPGRADE_TX_MAX_GAS_LIMIT
    gasPerPubdataByteLimit := REQUIRED_L2_GAS_PRICE_PER_PUBDATA
    nonce := protocolUpgradeNonce v
    data := calldata }

/-! ## Abstract functions -/

/-- The functions the transcription calls but this model does not compute. -/
structure PlanEnv where
  /-- `L2GenesisForceDeploymentsHelper.generateRandomAddress(info)`
  (`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:109-111`): a keccak of `bytes32(0) || info`,
  truncated to an address. -/
  randomAddress : Bytes → ℕ
  /-- `L2PlanLib._factoryDepHashes(deployments)` (`L2PlanLib.sol:118-149`): the observable hash
  of every bytecode the deployments install, deduplicated; `none` when one of its decodes
  reverts. -/
  factoryDepHashes : List Deployment → Option (List ℕ)
  /-- `abi.encodeCall(IComplexUpgrader.forceDeployAndUpgradeUniversal, (deployments, delegateTo,
  delegateCalldata))` (`CTMUpgradeComposer.sol:106-109`). -/
  encodeUpgradeCall : List Deployment → ℕ → Bytes → Bytes
  /-- `keccak256(abi.encode(tx))` (`BaseZkSyncUpgrade.sol:179, :197`). -/
  txHash : L2Tx → ℕ

/-! ## `L2PlanLib.build` -/

/-- `L2PlanLib._unsafeDeployment(_bytecodeInfo)` (`L2PlanLib.sol:100-112`): refuses an info that
is not `BYTECODE_INFO_LENGTH` bytes long (:103-105), else an `Unsafe` force deployment at the
info's derived address (:106-111). -/
def unsafeDeployment (E : PlanEnv) (info : Bytes) : Option Deployment :=
  if info.length ≠ BYTECODE_INFO_LENGTH then none
  else some ⟨.unsafeForceDeployment, info, E.randomAddress info⟩

/-- `L2PlanLib.build(_derived, _authored)` (`L2PlanLib.sol:47-82`):

    bool hasDelegate = _authored.delegateBytecodeInfo.length != 0;                       // :51
    plan.deployments = new ...[](derivedLength + (hasDelegate ? 1 : 0) + extrasLength);   // :54-56
    ... the derived deployments, then the delegate, then the extras ...                   // :57-69
    plan.delegateTo = plan.deployments[cursor].newAddress;   (only when hasDelegate)      // :63
    plan.delegateComposer = _authored.delegateComposer;                                   // :70
    plan.factoryDepHashes = _factoryDepHashes(plan.deployments);                          // :71
    if (!hasDelegate && (plan.deployments.length != 0 || plan.delegateComposer != address(0))) {
        revert L2PlanNeedsDelegate(); }                                                    // :73-75
    if (hasDelegate && plan.delegateComposer == address(0)) { revert L2PlanDelegateNeedsComposer(); } // :76-78
    if (plan.factoryDepHashes.length > MAX_NEW_FACTORY_DEPS) { revert L2PlanTooManyFactoryDeps(...); } // :79-81

`plan` is a fresh memory struct, so `delegateTo` is `address(0)` when there is no delegate. -/
def planBuild (E : PlanEnv) (derived : List Deployment) (a : AuthoredL2Plan) :
    Option L2UpgradePlan :=
  let hasDelegate : Bool := decide (a.delegateBytecodeInfo.length ≠ 0)
  let delegatePart : Option (List Deployment) :=
    if hasDelegate then (unsafeDeployment E a.delegateBytecodeInfo).map (fun d => [d]) else some []
  match delegatePart, a.extraBytecodeInfos.mapM (unsafeDeployment E) with
  | some del, some extras =>
    let deployments := derived ++ del ++ extras
    match E.factoryDepHashes deployments with
    | some fdh =>
      if hasDelegate = false ∧ (deployments.length ≠ 0 ∨ a.delegateComposer ≠ 0) then none else
      if hasDelegate = true ∧ a.delegateComposer = 0 then none else
      if MAX_NEW_FACTORY_DEPS < fdh.length then none else
      some { deployments := deployments
             delegateTo := if hasDelegate then E.randomAddress a.delegateBytecodeInfo else 0
             delegateComposer := a.delegateComposer
             factoryDepHashes := fdh }
    | none => none
  | _, _ => none

/-! ## `CTMUpgradeComposer.buildL2UpgradeTxFromPlan` -/

/-- `CTMUpgradeComposer.buildL2UpgradeTxFromPlan(_plan, _newRelease, _newProtocolVersion,
_bridgehub, _chainId)` (`CTMUpgradeComposer.sol:83-113`), with `composed` the value the plan's
composer returns for this chain (:99-103):

    if (_plan.deployments.length == 0 && _plan.delegateTo == address(0)) {
        return L2CanonicalTransactionLib.emptyL2CanonicalTransaction(); }               // :90-94
    bytes memory delegateCalldata = _plan.delegateComposer == address(0) ? bytes("")
        : IL2DelegateCalldataComposer(_plan.delegateComposer).composeDelegateCalldata(...); // :97-103
    L2CanonicalTransaction memory transaction = L2CanonicalTransactionLib.upgradeTransaction(
        _newProtocolVersion,
        abi.encodeCall(IComplexUpgrader.forceDeployAndUpgradeUniversal,
                       (_plan.deployments, _plan.delegateTo, delegateCalldata)));       // :104-110
    transaction.factoryDeps = _plan.factoryDepHashes;                                    // :111 -/
def buildL2UpgradeTxFromPlan (E : PlanEnv) (plan : L2UpgradePlan) (newVersion : ℕ)
    (composed : Bytes) : L2Tx :=
  if plan.deployments.length = 0 ∧ plan.delegateTo = 0 then emptyL2CanonicalTransaction
  else
    let delegateCalldata := if plan.delegateComposer = 0 then [] else composed
    { upgradeTransaction newVersion
        (E.encodeUpgradeCall plan.deployments plan.delegateTo delegateCalldata) with
      factoryDeps := plan.factoryDepHashes }

/-! ## The committed object -/

/-- What a committed edge object fixes at construction. For a `CTMTransition`: `old` and `new`
are the two releases' versions (`CTMTransition.sol:61-64`), `deadline` and `upgradeTimestamp`
the manifest's schedule, `derived` the table-derived deployments
`TransitionDerivationLib.deriveL2Deployments(fromRelease, newRelease)` (:81-84) and `authored`
the manifest's `l2Plan` (:85). For the bootstrap edge, `old` is the manifest's
`expectedProtocolVersion` (`RegistryBootstrapMigration.sol:87`) and `derived` the genesis
release's full table (:235-238). -/
structure EdgeObject where
  /-- The departing version: `oldProtocolVersion()` (`CTMTransition.sol:193-195`). -/
  old : ℕ
  /-- The target version: `newProtocolVersion()` (:198-200), also `upgradeTarget().0` (:223-226). -/
  new : ℕ
  /-- `oldProtocolVersionDeadline`. -/
  deadline : ℕ
  /-- `upgradeTimestamp`. -/
  upgradeTimestamp : ℕ
  /-- The table-derived deployments the constructor passes to `build`. -/
  derived : List Deployment
  /-- The manifest's authored L2 input. -/
  authored : AuthoredL2Plan

/-- The part of the constructor this topic needs passed, with `plan` the plan it stored
(`encodedL2Plan`, `CTMTransition.sol:111`, returned by `l2Plan()` at :234-236; the bootstrap
rebuilds the same plan from write-once inputs on every read, `RegistryBootstrapMigration.sol:117-120`):

    L2UpgradePlan memory derivedPlan = L2PlanLib.build(...);                     // :80-86
    bool hasL2Side = derivedPlan.deployments.length != 0;                         // :90
    VersionEdgeLib.requireValidEdge({..., _hasL2Side: hasL2Side});                // :91-97 -/
def Constructed (E : PlanEnv) (o : EdgeObject) (plan : L2UpgradePlan) : Prop :=
  planBuild E o.derived o.authored = some plan ∧
    requireValidEdge o.old o.new o.deadline o.upgradeTimestamp
      (decide (plan.deployments.length ≠ 0)) = some ()

/-- The transaction a chain composes for the object's plan, with the composer's answer
`composed` (`DefaultUpgrade.sol:76-82`). -/
def composedTx (E : PlanEnv) (o : EdgeObject) (plan : L2UpgradePlan) (composed : Bytes) : L2Tx :=
  buildL2UpgradeTxFromPlan E plan o.new composed

/-! ## The chain side (`BaseZkSyncUpgrade`) -/

/-- The chain storage the version step and the L2-transaction step read and write. -/
structure ChainUpgradeState where
  /-- `s.protocolVersion`. -/
  pv : ℕ
  /-- `s.l2SystemContractsUpgradeTxHash`; `0` means none pending. -/
  h : ℕ
  /-- `s.l2SystemContractsUpgradeBatchNumber`; `0` means not yet committed in a batch. -/
  b : ℕ
deriving DecidableEq

/-- `BaseZkSyncUpgrade._setNewProtocolVersion(_newProtocolVersion, _isOnSettlementLayer)`
(`upgrades/BaseZkSyncUpgrade.sol:218-272`), returning `(newMinorVersion, patchOnly, state)`:

    if (_newProtocolVersion <= previousProtocolVersion) { revert ProtocolVersionTooSmall(...); }    // :223-225
    (uint32 previousMajorVersion, uint32 previousMinorVersion, ) =
        SemVer.unpackSemVer(SafeCast.toUint96(previousProtocolVersion));                            // :227-229
    if (previousMajorVersion != 0) { revert PreviousProtocolMajorVersionNotZero(); }                // :230-232
    (newMajorVersion, newMinorVersion, ) = SemVer.unpackSemVer(SafeCast.toUint96(_newProtocolVersion)); // :236
    if (newMajorVersion != 0) { revert NewProtocolMajorVersionNotZero(); }                          // :237-239
    uint256 minorDelta = newMinorVersion - previousMinorVersion;                                    // :243
    if (minorDelta == 0) { patchOnly = true; }                                                      // :245-247
    if (minorDelta > MAX_ALLOWED_MINOR_VERSION_DELTA) { revert ProtocolVersionMinorDeltaTooBig(...); } // :250-252
    if (!patchOnly && _isOnSettlementLayer) {
        if (s.l2SystemContractsUpgradeTxHash != bytes32(0)) { revert PreviousUpgradeNotFinalized(...); }
        if (s.l2SystemContractsUpgradeBatchNumber != 0) { revert PreviousUpgradeNotCleaned(); } }   // :259-268
    s.protocolVersion = _newProtocolVersion;                                                        // :270 -/
def setNewProtocolVersion (c : ChainUpgradeState) (newV : ℕ) (onSL : Bool) :
    Option (ℕ × Bool × ChainUpgradeState) :=
  if newV ≤ c.pv then none else
  match unpackChecked c.pv, unpackChecked newV with
  | some (pM, pm, _), some (nM, nm, _) =>
    if pM ≠ 0 then none else
    if nM ≠ 0 then none else
    if nm < pm then none else
    if MAX_ALLOWED_MINOR_VERSION_DELTA < nm - pm then none else
    if nm - pm ≠ 0 ∧ onSL = true ∧ (c.h ≠ 0 ∨ c.b ≠ 0) then none else
    some (nm, decide (nm - pm = 0), { c with pv := newV })
  | _, _ => none

/-- `Math.ceilDiv(a, b)` (OpenZeppelin v4 `utils/math/Math.sol`): `a == 0 ? 0 : (a - 1) / b + 1`. -/
def ceilDiv (a b : ℕ) : ℕ := if a = 0 then 0 else (a - 1) / b + 1

/-- `TransactionValidator.getMinimalPriorityTransactionGasLimit(_calldataLength,
_l2GasPricePerPubdata)` (`TransactionValidator.sol:107-131`); `none` when a checked `uint256`
operation overflows:

    uint256 intrinsicGasCost = L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS;                              // :117
    intrinsicGasCost += L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * _calldataLength;        // :119
    uint256 intrinsicPubdataGasCost = L1_TX_INTRINSIC_PUBDATA_ZKSYNC_OS * _l2GasPricePerPubdata; // :123
    uint256 gasForIntrinsicNative = intrinsicPubdataGasCost +
        Math.ceilDiv(MAX_NATIVE_COMPUTATIONAL_ZKSYNC_OS, L1_TX_NATIVE_PER_GAS);              // :127-128
    return Math.max(intrinsicGasCost, gasForIntrinsicNative);                                // :130 -/
def minimalPriorityTxGasLimit (calldataLength gasPerPubdata : ℕ) : Option ℕ :=
  let floorCost := L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * calldataLength
  let intrinsicGasCost := L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS + floorCost
  let intrinsicPubdataGasCost := L1_TX_INTRINSIC_PUBDATA_ZKSYNC_OS * gasPerPubdata
  let gasForIntrinsicNative :=
    intrinsicPubdataGasCost + ceilDiv MAX_NATIVE_COMPUTATIONAL_ZKSYNC_OS L1_TX_NATIVE_PER_GAS
  if 2 ^ 256 ≤ floorCost ∨ 2 ^ 256 ≤ intrinsicGasCost ∨ 2 ^ 256 ≤ intrinsicPubdataGasCost ∨
      2 ^ 256 ≤ gasForIntrinsicNative then none
  else some (max intrinsicGasCost gasForIntrinsicNative)

/-- `TransactionValidator.validateL1ToL2Transaction(_transaction, _priorityTxMaxGasLimit,
_priorityTxMaxPubdata)` (`TransactionValidator.sol:31-55`); `true` when it returns:

    uint256 l2GasForTxBody = _transaction.gasLimit;                                       // :37
    if (l2GasForTxBody > _priorityTxMaxGasLimit) { revert TooMuchGas(); }                 // :40-42
    if (l2GasForTxBody / _transaction.gasPerPubdataByteLimit > _priorityTxMaxPubdata) {
        revert PubdataGreaterThanLimit(...); }                                            // :44-46
    if (getMinimalPriorityTransactionGasLimit(_transaction.data.length,
            _transaction.gasPerPubdataByteLimit) > l2GasForTxBody) {
        revert ValidateTxnNotEnoughGas(); }                                               // :49-54

A division by zero reverts in Solidity, so a zero `gasPerPubdataByteLimit` fails. -/
def validateL1ToL2Transaction (tx : L2Tx) (maxGas maxPubdata : ℕ) : Bool :=
  decide (tx.gasLimit ≤ maxGas) && decide (tx.gasPerPubdataByteLimit ≠ 0) &&
    decide (tx.gasLimit / tx.gasPerPubdataByteLimit ≤ maxPubdata) &&
    match minimalPriorityTxGasLimit tx.data.length tx.gasPerPubdataByteLimit with
    | some m => decide (m ≤ tx.gasLimit)
    | none => false

/-- `TransactionValidator.validateUpgradeTransaction(_transaction)` (`TransactionValidator.sol:59-100`);
`true` when it returns: `from <= type(uint16).max` (:61-63), `to <= type(uint160).max` (:64-66),
zero `paymaster`, `value`, `maxFeePerGas`, `maxPriorityFeePerGas` (:67-78), `reserved[0] == 0`
(:79-81), `reserved[1] <= type(uint160).max` (:82-84), `reserved[2] == reserved[3] == 0`
(:85-90), and empty `signature`, `paymasterInput`, `reservedDynamic` (:91-99). -/
def validateUpgradeTransaction (tx : L2Tx) : Bool :=
  decide (tx.sender ≤ 2 ^ 16 - 1) && decide (tx.recipient ≤ 2 ^ 160 - 1) && decide (tx.paymaster = 0) &&
    decide (tx.value = 0) && decide (tx.maxFeePerGas = 0) && decide (tx.maxPriorityFeePerGas = 0) &&
    decide (tx.reserved.1 = 0) && decide (tx.reserved.2.1 ≤ 2 ^ 160 - 1) &&
    decide (tx.reserved.2.2.1 = 0) && decide (tx.reserved.2.2.2 = 0) &&
    decide (tx.signature.length = 0) && decide (tx.paymasterInput.length = 0) &&
    decide (tx.reservedDynamic.length = 0)

/-- `BaseZkSyncUpgrade._setL2SystemContractUpgrade(_l2ProtocolUpgradeTx, _newMinorProtocolVersion,
_patchOnly)` (`upgrades/BaseZkSyncUpgrade.sol:162-202`), returning `(hash, state)`; `H` is
`keccak256(abi.encode(tx))` and `maxPubdata` is `s.feeParams.priorityTxMaxPubdata`:

    if (_l2ProtocolUpgradeTx.txType == 0) { return bytes32(0); }                              // :168-170
    if (_l2ProtocolUpgradeTx.txType != _getUpgradeTxType()) { revert InvalidTxType(...); }   // :172-174
    if (_patchOnly) { revert PatchCantSetUpgradeTxn(); }                                      // :175-177
    TransactionValidator.validateL1ToL2Transaction(_l2ProtocolUpgradeTx, UPGRADE_TX_MAX_GAS_LIMIT,
        s.feeParams.priorityTxMaxPubdata);                                                    // :181-185
    TransactionValidator.validateUpgradeTransaction(_l2ProtocolUpgradeTx);                   // :187
    if (_l2ProtocolUpgradeTx.nonce != _newMinorProtocolVersion) { revert L2UpgradeNonceNotEqualToNewProtocolVersion(...); } // :191-193
    _verifyFactoryDeps(_l2ProtocolUpgradeTx.factoryDeps);    // length <= MAX_NEW_FACTORY_DEPS, :195, :209-213
    bytes32 l2ProtocolUpgradeTxHash = keccak256(encodedTransaction);                          // :197
    s.l2SystemContractsUpgradeTxHash = l2ProtocolUpgradeTxHash;                               // :199 -/
def setL2SystemContractUpgrade (H : L2Tx → ℕ) (c : ChainUpgradeState) (maxPubdata : ℕ)
    (tx : L2Tx) (newMinor : ℕ) (patchOnly : Bool) : Option (ℕ × ChainUpgradeState) :=
  if tx.txType = 0 then some (0, c) else
  if tx.txType ≠ ZKSYNC_OS_SYSTEM_UPGRADE_L2_TX_TYPE then none else
  if patchOnly = true then none else
  if validateL1ToL2Transaction tx UPGRADE_TX_MAX_GAS_LIMIT maxPubdata = false then none else
  if validateUpgradeTransaction tx = false then none else
  if tx.nonce ≠ newMinor then none else
  if MAX_NEW_FACTORY_DEPS < tx.factoryDeps.length then none else
  some (H tx, { c with h := H tx })

/-- The storage part of `BaseZkSyncUpgrade._upgrade` (`BaseZkSyncUpgrade.sol:72-108`): the
version step (:96), then, on the settlement layer only, the L2-transaction step (:103-105),
returning `(txHash, state)`. Omitted: the time gate (:82-84), the settlement-layer order check
off the settlement layer (:89-94), and the verifier (:97-99). -/
def upgradeStoragePart (H : L2Tx → ℕ) (c : ChainUpgradeState) (maxPubdata newV : ℕ) (tx : L2Tx)
    (onSL : Bool) : Option (ℕ × ChainUpgradeState) :=
  match setNewProtocolVersion c newV onSL with
  | none => none
  | some (m, p, c1) => if onSL = true then setL2SystemContractUpgrade H c1 maxPubdata tx m p
                       else some (0, c1)

/-- The calldata-length condition under which an upgrade transaction with gas limit
`UPGRADE_TX_MAX_GAS_LIMIT` covers `getMinimalPriorityTransactionGasLimit`'s intrinsic gas
(`TransactionValidator.sol:117-119`): `21000 + 40 * data.length <= 72_000_000`, that is, at most
`1_799_475` bytes. No commit-time check bounds the composed calldata, whose delegate part the
composer returns at execution. This is a name for a premise, not a source definition. -/
def UpgradeCalldataFits (tx : L2Tx) : Prop :=
  L1_TX_INTRINSIC_L2_GAS_ZKSYNC_OS + L1_TX_CALLDATA_FLOOR_PRICE_L2_GAS_ZKSYNC_OS * tx.data.length ≤
    UPGRADE_TX_MAX_GAS_LIMIT

/-! ## The bytecode supplier (`upgrades/BytecodesSupplier.sol`) -/

/-- The supplier's `evmPublishingBlock` mapping (`BytecodesSupplier.sol:26`); `0` means not
published. -/
structure Supplier where
  /-- `evmPublishingBlock[hash]`. -/
  pub : ℕ → ℕ

/-- `L2PlanLib.requirePublished(_supplier, _hashes)` (`L2PlanLib.sol:89-97`): every hash has a
nonzero `evmPublishingBlock` (:93-95). -/
def requirePublished (s : Supplier) (hashes : List ℕ) : Prop :=
  ∀ x ∈ hashes, s.pub x ≠ 0

/-- The writers of the supplier's mapping. -/
inductive SupplierOp
  /-- `publishEVMBytecode(_bytecode)` with `keccak256(_bytecode) = hash`, at block `blockNumber`
  (`BytecodesSupplier.sol:37-47`; `publishEVMBytecodes`, :51-56, is a sequence of these). -/
  | publish (hash blockNumber : ℕ)
  /-- An upgrade of the supplier proxy's implementation (a CTM-domain proxy row), after which the
  mapping reads as `pub'`. -/
  | implementationSwap (pub' : ℕ → ℕ)

/-- One successful supplier step. A publication happens in a block with a positive number, as
every transaction does. -/
inductive SupplierStep : Supplier → SupplierOp → Supplier → Prop
  /-- `publishEVMBytecode`: refuses a published hash (:40-42), records the block (:44). -/
  | publish {s : Supplier} {hash blk : ℕ} :
      blk ≠ 0 → s.pub hash = 0 →
      SupplierStep s (.publish hash blk) ⟨upd s.pub hash blk⟩
  /-- A proxy implementation swap: the mapping as the new code reads it is arbitrary. -/
  | implementationSwap {s : Supplier} {f : ℕ → ℕ} :
      SupplierStep s (.implementationSwap f) ⟨f⟩

/-- A sequence of supplier steps. -/
inductive SupplierRun : Supplier → List SupplierOp → Supplier → Prop
  | nil {s : Supplier} : SupplierRun s [] s
  | cons {s s' s'' : Supplier} {op : SupplierOp} {ops : List SupplierOp} :
      SupplierStep s op s' → SupplierRun s' ops s'' → SupplierRun s (op :: ops) s''

/-- A supplier operation that is a publication (not an implementation swap). -/
def SupplierOp.IsPublish : SupplierOp → Prop
  | .publish _ _ => True
  | .implementationSwap _ => False

/-! ## Composition with the CTM's registry (`Specs/VersionRegistry.lean`)

`Specs/VersionRegistry.lean` was written at `e561b9cc2`. At `b17415d20`,
`setNewVersionUpgradeFromTransition` (`state-transition/ChainTypeManager.sol:403-418`) and
`replaceUpgradeTransition` (:424-443) make the same checks on the values `CStep` tracks: the
departure release (:405-408, :472-478), `_commitVersionEdge` (:523-537), `_recordTransition`
(:459-467), `_requireOnwardDestination` (:498-518) and `_setCurrentRelease` (:300-318).
`_requireExecutable` and `_requireSameDeadline` are additional reverts `CStep` omits. -/

/-- The constructed object behind each transition address, and the plan it stored. -/
structure EdgeWorld where
  /-- What the object fixed at construction. -/
  obj : Address → EdgeObject
  /-- The plan it stored (`l2Plan()`). -/
  plan : Address → L2UpgradePlan

/-- The CTM's view of transition `t` (its `oldProtocolVersion()` and `newProtocolVersion()`
getters) returns what the object fixed at construction (`CTMTransition.sol:63-64, :193-200`). -/
def EdgeWorld.Reports (W : World) (EW : EdgeWorld) (t : Address) : Prop :=
  (W.tr t).old = (EW.obj t).old ∧ (W.tr t).new = (EW.obj t).new

/-! ## Witness data

Packed versions `0.29.0`, `0.30.0`, `0.30.1`, `0.100.0`, `0.130.0`, and an environment whose
derived address is `0x1234`, whose factory-dependency list has one hash per deployment
(`7, 8, ...`), whose upgrade-call encoding is 100 bytes followed by the delegate calldata, and
whose transaction hash is `nonce + 1`. -/

/-- `0.29.0`. -/
def v29 : ℕ := 29 * 2 ^ 32
/-- `0.30.0`. -/
def v30 : ℕ := 30 * 2 ^ 32
/-- `0.30.1`. -/
def v30p1 : ℕ := 30 * 2 ^ 32 + 1
/-- `0.100.0`. -/
def v100 : ℕ := 100 * 2 ^ 32
/-- `0.130.0`. -/
def v130 : ℕ := 130 * 2 ^ 32

/-- The witness environment. -/
def wEnv : PlanEnv where
  randomAddress := fun _ => 0x1234
  factoryDepHashes := fun ds => some (List.range' 7 ds.length)
  encodeUpgradeCall := fun _ _ dc => List.replicate 100 0 ++ dc
  txHash := fun tx => tx.nonce + 1

/-- A 96-byte bytecode info. -/
def wInfo : Bytes := List.replicate 96 1

/-- An authored plan with a delegate (`wInfo`) and composer `0x99`, no extras. -/
def wAuthored : AuthoredL2Plan := ⟨wInfo, [], 0x99⟩

/-- The authored plan of an edge with no L2 side. -/
def wNoL2Authored : AuthoredL2Plan := ⟨[], [], 0⟩

/-- An edge `0.29.0 → 0.30.0` with an L2 side: one table-derived system-proxy deployment and the
authored delegate. -/
def wEdge : EdgeObject :=
  ⟨v29, v30, 100, 50, [⟨.systemProxyUpgrade, [5, 5], 0x8010⟩], wAuthored⟩

/-- The plan `build` returns for `wEdge`. -/
def wPlan : L2UpgradePlan :=
  ⟨[⟨.systemProxyUpgrade, [5, 5], 0x8010⟩, ⟨.unsafeForceDeployment, wInfo, 0x1234⟩], 0x1234, 0x99,
    [7, 8]⟩

/-- A patch edge `0.30.0 → 0.30.1` with no L2 side. -/
def wPatchEdge : EdgeObject := ⟨v30, v30p1, 100, 50, [], wNoL2Authored⟩

/-- The empty plan. -/
def wEmptyPlan : L2UpgradePlan := ⟨[], 0, 0, []⟩

/-- An L1-only minor edge `0.100.0 → 0.130.0` with no L2 side. -/
def wFarEdge : EdgeObject := ⟨v100, v130, 1, 0, [], wNoL2Authored⟩

/-- A plan `build` never returns: no deployments, but a nonzero `delegateTo`. -/
def wUnbuiltPlan : L2UpgradePlan := ⟨[], 0x1234, 0, []⟩

/-- Release versions of the registry witness: `100` at `0.29.0`, `200` at `0.30.0`, `250` at
`0.130.0`. -/
def wEdgeRelVersion : Address → ℕ := fun a =>
  if a = 100 then v29 else if a = 200 then v30 else if a = 250 then v130 else 0

/-- Transition getters of the registry witness: `300` (`0.29.0 → 0.30.0`, from `100` to `200`),
its genuine replacement `400`, `600` (`0.30.0 → 0.130.0`, from `200` to `250`), and `500`, which
departs from release `100` but reports `oldProtocolVersion() = 0.100.0`. -/
def wEdgeTr : Address → TransitionView := fun a =>
  if a = 300 then ⟨v29, v30, 100, 200⟩
  else if a = 400 then ⟨v29, v30, 100, 200⟩
  else if a = 500 then ⟨v100, v130, 100, 250⟩
  else if a = 600 then ⟨v30, v130, 200, 250⟩
  else ⟨0, 0, 0, 0⟩

/-- The registry witness world (routing rows are not read here). -/
def wEdgeWorld : World := ⟨wEdgeRelVersion, fun _ => [], wEdgeTr⟩

/-- The registry witness objects: `300` and `400` are `wEdge`, `500` is `wFarEdge`, `600` an
L1-only edge `0.30.0 → 0.130.0`. -/
def wEdgeObjs : EdgeWorld where
  obj := fun a =>
    if a = 300 ∨ a = 400 then wEdge
    else if a = 500 then wFarEdge
    else ⟨v30, v130, 1, 0, [], wNoL2Authored⟩
  plan := fun a => if a = 300 ∨ a = 400 then wPlan else wEmptyPlan

end Contracts.ChainTypeManager.EdgeChecks
