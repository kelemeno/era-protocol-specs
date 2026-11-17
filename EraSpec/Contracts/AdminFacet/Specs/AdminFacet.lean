import Mathlib.Data.Nat.Notation

/-!
# Model: the chain diamond's `AdminFacet`

Source: era-contracts `draft/v0.35.0` at commit `d9f678900e1bc8286412b78f56d4a9f443983c29`.
Paths are relative to `l1-contracts/contracts/`; `Admin.sol` is
`state-transition/chain-deps/facets/Admin.sol` and `ZKChainBase.sol` is
`state-transition/chain-deps/facets/ZKChainBase.sol`. Every `file:line` below is at that commit.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.AdminFacet.Properties.*` and proofs in `EraSpec.Contracts.AdminFacet.Proofs.*`.

## What is modelled

* `State`: the slice of `ZKChainStorage` (`state-transition/chain-deps/ZKChainStorage.sol`) that
  the facet reads or writes, plus the diamond's `isFrozen` flag and the per-selector
  `isFreezable` bits (`state-transition/libraries/Diamond.sol`).
* `Entry`: all 25 state-changing external functions of the facet (the two views
  `getRollupDAManager`, `ROLLUP_DA_MANAGER` change nothing). `exec` transcribes each body with
  its modifiers, guards in source order. **A revert is `none`.**
* `call`: the diamond proxy's dispatch (`state-transition/chain-deps/DiamondProxy.sol:25-36`),
  which refuses a freezable selector while the diamond is frozen, then `exec`.
* `Env`: what the facet reads from other contracts at call time — the CTM's
  `upgradeCutForVersion`, `l1GenesisUpgrade` and its `ServerNotifier`'s schedule, the Bridgehub
  owner, the `RollupDAManager`, the verifier's `getProofMode`. The environment changes freely
  between calls (`Label.env`).
* `Config.runCut`: what `Diamond.diamondCut` does to this storage, including the delegatecalled
  initializer (`Diamond.sol:109-137`). It is **arbitrary**: a cut is code chosen by the CTM.
  `genesisEffect` transcribes the one initializer this facet names itself, `L1GenesisUpgrade`
  (`upgrades/L1GenesisUpgrade.sol:31-53` through `upgrades/BaseZkSyncUpgrade.sol:72-108,162-202`
  and `upgrades/BaseZkSyncUpgradeGenesis.sol:25-82`); `GenuineGenesis` is the premise that the
  CTM's genesis address holds that code, in the one-directional form "whenever the genesis cut
  succeeds, `genesisEffect` succeeds with the same result". The real code has further reverts
  (transaction validation, the external reads that compose the transaction); the premise allows
  them.
* `Foreign`: a write by another facet (Executor, Committer, Mailbox, Migrator). A source search at
  this commit finds that those facets write only batch counters, the priority tree and its request
  timestamps, `pausedDepositsTimestamp`, `settlementLayer`, the DA pair, the L2 upgrade
  transaction's hash and batch number, and `isPermanentRollup`, which `Migrator.forwardedBridgeMint`
  may set but never clear (`Migrator.sol:234-236, 241`). Everything in `Owned` is left alone.
* `Step`/`Run`: any interleaving of calls (any sender, any block time), environment changes and
  foreign writes.

## What is not modelled

* Routing: the diamond is assumed to send the facet's selectors to this facet's code. Which code a
  cut installs is `ChainTypeManager`'s `ChainRouting` model (at `e561b9cc2`).
* The `nonReentrant` modifier of `activatePriorityMode` (the body makes no external call that
  could re-enter; the reads are views).
* Events. ABI widths: addresses, hashes and enums are `ℕ`, compared only for equality; `uint`
  fields are `ℕ`, so checked-arithmetic overflow reverts are omitted (the model admits more
  successful calls, never fewer).
* The `L2CanonicalTransaction` validation inside the genesis upgrade
  (`TransactionValidator.validateL1ToL2Transaction`/`validateUpgradeTransaction`,
  `BaseZkSyncUpgrade.sol:181-187`) and the external reads composing that transaction
  (`L1GenesisUpgrade.sol:77-104`). They only reject, and `GenuineGenesis` is stated so that extra
  rejections are allowed.
-/

namespace Contracts.AdminFacet

/-- Addresses, hashes and selectors: compared only for equality. -/
abbrev Address := ℕ

/-! ## Constants (`common/Config.sol`) -/

/-- `PRIORITY_TX_MAX_GAS_LIMIT = 1 << 24` (`Config.sol:197`). -/
abbrev PRIORITY_TX_MAX_GAS_LIMIT : ℕ := 2 ^ 24
/-- `ZKSYNC_OS_DEFAULT_MAX_TX_GAS_LIMIT = uint64(1) << 24` (`Config.sol:187`). -/
abbrev ZKSYNC_OS_DEFAULT_MAX_TX_GAS_LIMIT : ℕ := 2 ^ 24
/-- `ZKSYNC_OS_MAX_BLOCK_GAS_LIMIT = type(uint64).max / 256` (`Config.sol:194`). -/
abbrev ZKSYNC_OS_MAX_BLOCK_GAS_LIMIT : ℕ := (2 ^ 64 - 1) / 256
/-- `PRICE_UPDATE_INTERVAL = 1 days` (`Config.sol:160`). -/
abbrev PRICE_UPDATE_INTERVAL : ℕ := 86400
/-- `PRIORITY_EXPIRATION = 4 days` (`Config.sol:83`). -/
abbrev PRIORITY_EXPIRATION : ℕ := 4 * 86400
/-- `MAX_PRICE_CHANGE_NUMERATOR = 13` (`Config.sol:162`). -/
abbrev MAX_PRICE_CHANGE_NUMERATOR : ℕ := 13
/-- `MAX_PRICE_CHANGE_DENOMINATOR = 10` (`Config.sol:163`). -/
abbrev MAX_PRICE_CHANGE_DENOMINATOR : ℕ := 10
/-- `PRICE_REFERENCE_L1_GAS = 1 gwei` (`Config.sol:165`). -/
abbrev PRICE_REFERENCE_L1_GAS : ℕ := 10 ^ 9
/-- `L1_GAS_PER_PUBDATA_BYTE = 17` (`Config.sol:151`). -/
abbrev L1_GAS_PER_PUBDATA_BYTE : ℕ := 17
/-- `REQUIRED_L2_GAS_PRICE_PER_PUBDATA = 800` (`Config.sol:157`). -/
abbrev REQUIRED_L2_GAS_PRICE_PER_PUBDATA : ℕ := 800
/-- `ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE = 5` (`Config.sol:108`). -/
abbrev ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE : ℕ := 5
/-- `ProofSystem.Zisk`, the third member of `enum ProofSystem { Boojum, Airbender, Zisk }`
(`Config.sol:126-130`). -/
abbrev PROOF_SYSTEM_ZISK : ℕ := 2
/-- `PubdataPricingMode.Rollup`, the first member of the enum (`ZKChainStorage.sol`). -/
abbrev PRICING_MODE_ROLLUP : ℕ := 0
/-- `L2DACommitmentScheme.NONE`, the first member of the enum (`Config.sol:49-50`). -/
abbrev DA_SCHEME_NONE : ℕ := 0

/-! ## Storage -/

/-- `enum PubdataContent { FULL_PUBDATA, LOGS_ONLY }` (`Config.sol:58-61`). -/
inductive PubdataContent where
  | fullPubdata
  | logsOnly
  deriving DecidableEq, Repr

/-- `struct FeeParams` (`ZKChainStorage.sol:46-53`); the pricing mode is the enum's index. -/
structure FeeParams where
  pricingMode : ℕ
  batchOverheadL1Gas : ℕ
  maxPubdataPerBatch : ℕ
  maxL2GasPerBatch : ℕ
  priorityTxMaxPubdata : ℕ
  minimalL2GasPrice : ℕ
  deriving DecidableEq, Repr

/-- `struct PriorityModeInformation` (`ZKChainStorage.sol:61-66`). -/
structure PriorityModeInfo where
  canBeActivated : Bool
  activated : Bool
  permissionlessValidator : Address
  transactionFilterer : Address
  deriving DecidableEq, Repr

/-- `Diamond.DiamondCutData`: the facet cuts (opaque here), the initializer address and its
calldata. -/
structure Cut where
  facetCuts : List ℕ
  initAddress : Address
  initCalldata : ℕ
  deriving DecidableEq, Repr

/-- The storage the facet reads or writes. -/
structure State where
  /-- `s.admin`. -/
  admin : Address
  /-- `s.pendingAdmin`. -/
  pendingAdmin : Address
  /-- `s.chainTypeManager`. -/
  chainTypeManager : Address
  /-- `s.validators`. -/
  validators : Address → Bool
  /-- `Diamond.DiamondStorage.isFrozen`. -/
  frozen : Bool
  /-- `selectorToFacet[sel].isFreezable`, by selector. -/
  freezable : ℕ → Bool
  /-- `s.protocolVersion` (packed semver). -/
  protocolVersion : ℕ
  /-- `s.verifier`. -/
  verifier : Address
  /-- `s.settlementLayer`; `0` means this diamond is on its settlement layer. -/
  settlementLayer : Address
  /-- `s.priorityTxMaxGasLimit`. -/
  priorityTxMaxGasLimit : ℕ
  /-- `s.zksyncOSMaxTxGasLimit`. -/
  zksyncOSMaxTxGasLimit : ℕ
  /-- `s.zksyncOSL1TxFilteringEnabled`. -/
  l1TxFiltering : Bool
  /-- `s.zksyncOSLargeContractsEnabled`. -/
  largeContracts : Bool
  /-- `s.feeParams`. -/
  feeParams : FeeParams
  /-- `s.baseTokenGasPriceMultiplierNominator`. -/
  multNominator : ℕ
  /-- `s.baseTokenGasPriceMultiplierDenominator`. -/
  multDenominator : ℕ
  /-- `s.lastFeeParamsUpdateTimestamp`. -/
  lastFeeParamsUpdate : ℕ
  /-- `s.lastTokenMultiplierUpdateTimestamp`. -/
  lastTokenMultiplierUpdate : ℕ
  /-- `s.transactionFilterer`. -/
  transactionFilterer : Address
  /-- `s.l1DAValidator`. -/
  l1DAValidator : Address
  /-- `s.l2DACommitmentScheme` (enum index; `NONE = 0`). -/
  l2DAScheme : ℕ
  /-- `s.pubdataContent`. -/
  pubdataContent : PubdataContent
  /-- `s.isPermanentRollup`. -/
  isPermanentRollup : Bool
  /-- `s.secondProofSystemRequired`. -/
  secondProofSystemRequired : Bool
  /-- `s.disabledProofSystems` (a `uint8` mask). -/
  disabledProofSystems : ℕ
  /-- `s.priorityModeInfo`. -/
  priorityMode : PriorityModeInfo
  /-- `s.pausedDepositsTimestamp`. -/
  pausedDepositsTimestamp : ℕ
  /-- `s.priorityTree.startIndex`. -/
  ptStartIndex : ℕ
  /-- `s.priorityTree.tree._nextLeafIndex`. -/
  ptNextLeafIndex : ℕ
  /-- `s.priorityTree.unprocessedIndex`. -/
  ptUnprocessedIndex : ℕ
  /-- `s.priorityOpsRequestTimestamp`. -/
  requestTimestamp : ℕ → ℕ
  /-- `s.totalBatchesCommitted`. -/
  totalBatchesCommitted : ℕ
  /-- `s.totalBatchesVerified`. -/
  totalBatchesVerified : ℕ
  /-- `s.totalBatchesExecuted`. -/
  totalBatchesExecuted : ℕ
  /-- `s.l2SystemContractsUpgradeTxHash`. -/
  upgradeTxHash : ℕ
  /-- `s.l2SystemContractsUpgradeBatchNumber`. -/
  upgradeBatchNumber : ℕ

/-- `PriorityTree.getSize` (`state-transition/libraries/PriorityTree.sol:47-49`): the number of
unprocessed priority transactions. -/
def State.priorityTreeSize (s : State) : ℕ := s.ptNextLeafIndex - s.ptUnprocessedIndex

/-- `PriorityTree.getFirstUnprocessedPriorityTx` (`PriorityTree.sol:37-39`). -/
def State.firstUnprocessed (s : State) : ℕ := s.ptStartIndex + s.ptUnprocessedIndex

/-! ## Environment and configuration -/

/-- What the facet reads from other contracts during a call. Keyed by the CTM address where the
source asks `s.chainTypeManager`. -/
structure Env where
  /-- `IChainTypeManager(ctm).upgradeCutForVersion(v)` (`ChainTypeManager.sol:601-607`): the cut
  derived from the transition committed for edge `v`; `none` when nothing is committed (it reverts
  `NoCommittedUpgradeCutForVersion`). -/
  upgradeCutForVersion : Address → ℕ → Option Cut
  /-- `IServerNotifier(ctm.serverNotifierAddress()).protocolVersionToUpgradeTimestamp(s.chainId, v)`
  (`Admin.sol:578-581`), for this chain. -/
  upgradeTimestamp : Address → ℕ → ℕ
  /-- `IChainTypeManager(ctm).l1GenesisUpgrade()` (`ChainTypeManager.sol:322-325`). -/
  l1GenesisUpgrade : Address → Address
  /-- The hash `keccak256(abi.encode(tx))` of the L2 genesis transaction the CTM's current release
  composes for this chain at a given protocol version (`L1GenesisUpgrade.sol:35-40, 77-104`,
  `BaseZkSyncUpgrade.sol:179-199`). Arguments: the CTM address and `s.protocolVersion`; the
  chain id and the Bridgehub are fixed for one diamond. -/
  genesisTxHash : Address → ℕ → ℕ
  /-- `IOwnable(s.bridgehub).owner()` (`Admin.sol:417`). -/
  bridgehubOwner : Address
  /-- `ROLLUP_DA_MANAGER.isPairAllowed(l1, scheme)` (`Admin.sol:396, 445`). -/
  isPairAllowed : Address → ℕ → Bool
  /-- `IZKsyncOSVerifier(v).getProofMode(mask)` (`Admin.sol:122`, `ZKChainBase.sol:188-190`). -/
  getProofMode : Address → ℕ → ℕ

/-- Fixed configuration. -/
structure Config where
  /-- `block.chainid == L1_CHAIN_ID` (`Admin.sol:100-104`): fixed per deployment. -/
  onL1 : Bool
  /-- `Diamond.diamondCut(cut)` (`Diamond.sol:109-137`) on this storage, including the
  delegatecalled initializer: arbitrary; `none` is a revert. -/
  runCut : Env → Cut → State → Option State

/-! ## Entry points (`Admin.sol:646-702` lists their selectors) -/

/-- The 25 state-changing external functions, with their arguments. -/
inductive Entry where
  | setPendingAdmin (newPendingAdmin : Address)
  | acceptAdmin
  | setValidator (validator : Address) (active : Bool)
  | setPriorityTxMaxGasLimit (newLimit : ℕ)
  | setZKsyncOSMaxTxGasLimit (newLimit : ℕ)
  | setZKsyncOSL1TxFiltering (enabled : Bool)
  | setZKsyncOSLargeContractsEnabled (enabled : Bool)
  | changeFeeParams (newFeeParams : FeeParams)
  | setTokenMultiplier (nominator denominator : ℕ)
  | setPubdataPricingMode (pricingMode : ℕ)
  | setTransactionFilterer (filterer : Address)
  | setDAValidatorPair (l1DAValidator : Address) (scheme : ℕ)
  | setPubdataContent (content : PubdataContent)
  | setProofSystemStatus (proofSystem : ℕ) (enabled : Bool)
  | makePermanentRollup
  | permanentlyRequireSecondProofSystem
  | setPriorityModeTransactionFilterer (filterer : Address)
  | permanentlyAllowPriorityMode
  | deactivatePriorityMode
  | activatePriorityMode
  | upgradeChainFromVersion (chainAddress : Address) (oldProtocolVersion : ℕ)
  | executeUpgrade (cut : Cut)
  | genesisUpgrade
  | freezeDiamond
  | unfreezeDiamond

/-- Each entry's 4-byte selector, as listed in `selectors()` (`Admin.sol:646-702`). -/
def Entry.sel : Entry → ℕ
  | .upgradeChainFromVersion _ _ => 0x03129ad9
  | .acceptAdmin => 0x0e18b681
  | .setZKsyncOSLargeContractsEnabled _ => 0x120c12c2
  | .unfreezeDiamond => 0x17338945
  | .permanentlyAllowPriorityMode => 0x1b48b94a
  | .permanentlyRequireSecondProofSystem => 0x1d1178d3
  | .setTransactionFilterer _ => 0x21f603d7
  | .setTokenMultiplier _ _ => 0x235d9eb5
  | .deactivatePriorityMode => 0x23b31192
  | .setDAValidatorPair _ _ => 0x2765d079
  | .freezeDiamond => 0x27ae4c16
  | .setZKsyncOSMaxTxGasLimit _ => 0x2f257a5c
  | .setValidator _ _ => 0x4623c91d
  | .setPendingAdmin _ => 0x4dd18bf5
  | .activatePriorityMode => 0x60eae0e7
  | .changeFeeParams _ => 0x64bf8d66
  | .makePermanentRollup => 0x6e762e98
  | .executeUpgrade _ => 0xa9f6d941
  | .setPriorityTxMaxGasLimit _ => 0xbe6f11cf
  | .setPriorityModeTransactionFilterer _ => 0xc5f1f1f5
  | .genesisUpgrade => 0xd241f618
  | .setZKsyncOSL1TxFiltering _ => 0xdf16d0a3
  | .setPubdataContent _ => 0xe51935f5
  | .setPubdataPricingMode _ => 0xe76db865
  | .setProofSystemStatus _ _ => 0xf4560a66

/-- The three entries that run a diamond cut, i.e. code the facet does not contain. -/
def Entry.runsCut : Entry → Bool
  | .upgradeChainFromVersion _ _ => true
  | .executeUpgrade _ => true
  | .genesisUpgrade => true
  | _ => false

/-- One external call: `msg.sender`, `block.timestamp`, and the function with its arguments. -/
structure Call where
  sender : Address
  time : ℕ
  entry : Entry

/-! ## Helpers transcribed from the source -/

/-- `require(c)`: continue with `k` when `c` holds, else revert. -/
def req (c : Prop) [Decidable c] (k : Option State) : Option State :=
  if c then k else none

/-- `_deriveL2GasPriceFromParams` (`ZKChainBase.sol:276-300`) in `ℕ`. -/
def deriveL2GasPriceFromParams (fp : FeeParams) (n d l1GasPrice gasPerPubdata : ℕ) : ℕ :=
  let l1GasPriceConverted := l1GasPrice * n / d
  let pubdataPriceBaseToken :=
    if fp.pricingMode = PRICING_MODE_ROLLUP then L1_GAS_PER_PUBDATA_BYTE * l1GasPriceConverted
    else 0
  let batchOverheadBaseToken := fp.batchOverheadL1Gas * l1GasPriceConverted
  let fullPubdataPriceBaseToken :=
    pubdataPriceBaseToken + batchOverheadBaseToken / fp.maxPubdataPerBatch
  let l2GasPrice := fp.minimalL2GasPrice + batchOverheadBaseToken / fp.maxL2GasPerBatch
  let minL2GasPriceBaseToken := (fullPubdataPriceBaseToken + gasPerPubdata - 1) / gasPerPubdata
  max l2GasPrice minL2GasPriceBaseToken

/-- `_safeDerivedL2GasPrice` (`Admin.sol:339-356`). -/
def safeDerivedL2GasPrice (fp : FeeParams) (n d : ℕ) : ℕ :=
  if d = 0 ∨ fp.maxPubdataPerBatch = 0 ∨ fp.maxL2GasPerBatch = 0 then 0
  else deriveL2GasPriceFromParams fp n d PRICE_REFERENCE_L1_GAS REQUIRED_L2_GAS_PRICE_PER_PUBDATA

/-- `_enforcePriceChangeBound` (`Admin.sol:309-337`): `true` when it does not revert. -/
def priceChangeWithinBound (s : State) (oldFp newFp : FeeParams) (oldN oldD newN newD : ℕ) :
    Bool :=
  let oldPrice := safeDerivedL2GasPrice oldFp oldN oldD
  let newPrice := safeDerivedL2GasPrice newFp newN newD
  if oldPrice = 0 ∧ s.priorityTreeSize = 0 then true                                -- :320-322
  else
    decide (newPrice ≤ oldPrice * MAX_PRICE_CHANGE_NUMERATOR / MAX_PRICE_CHANGE_DENOMINATOR)
      && decide (oldPrice * MAX_PRICE_CHANGE_DENOMINATOR / MAX_PRICE_CHANGE_NUMERATOR ≤ newPrice)

/-- `_enforceMinUpdateInterval` (`Admin.sol:298-307`): `true` when it does not revert. -/
def minUpdateIntervalPassed (s : State) (τ : ℕ) : Bool :=
  let last := max s.lastFeeParamsUpdate s.lastTokenMultiplierUpdate
  !(decide (last ≠ 0) && decide (τ < last + PRICE_UPDATE_INTERVAL))

/-- `_revertBatches(n)` (`ZKChainBase.sol:317-337`). -/
def revertBatches (s : State) (n : ℕ) : Option State :=
  req (n ≤ s.totalBatchesCommitted) <|                                              -- :318-320
  req (s.totalBatchesExecuted ≤ n) <|                                               -- :321-323
  some { s with
    totalBatchesVerified := if n < s.totalBatchesVerified then n else s.totalBatchesVerified
    totalBatchesCommitted := n
    upgradeBatchNumber := if n < s.upgradeBatchNumber then 0 else s.upgradeBatchNumber }

/-- `_executeDiamondCut` (`Admin.sol:117-128`): the cut, then the second-proof-system recheck
against the verifier the cut leaves behind. -/
def executeDiamondCut (K : Config) (e : Env) (cut : Cut) (s : State) : Option State :=
  match K.runCut e cut s with
  | none => none
  | some s₁ =>
    req (s₁.secondProofSystemRequired = true →
        e.getProofMode s₁.verifier 0 = ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) (some s₁)

/-- `abi.encodeCall(IL1GenesisUpgrade.genesisUpgrade, ())`: the 4-byte selector of
`genesisUpgrade()`. -/
abbrev GENESIS_UPGRADE_CALLDATA : ℕ := 0xd241f618

/-- The cut `genesisUpgrade` builds (`Admin.sol:600-606`): no facet cuts, the CTM's genesis
upgrade as initializer. -/
def genesisCut (initAddress : Address) : Cut :=
  ⟨[], initAddress, GENESIS_UPGRADE_CALLDATA⟩

/-- What the genuine `L1GenesisUpgrade.genesisUpgrade` (`L1GenesisUpgrade.sol:31-53`) does when
delegatecalled into this storage. Through `_upgrade` (`BaseZkSyncUpgrade.sol:72-108`) with
`_newProtocolVersion = s.protocolVersion`, `_upgradeTimestamp = 0`, `_verifier = address(0)`:

* off the settlement layer it always reverts: `_setNewProtocolVersion` of the genesis variant
  reverts `GenesisUpgradeExpectedOnSettlementLayer` (`BaseZkSyncUpgradeGenesis.sol:62-64`);
* `SafeCast.toUint96` and the zero-major checks (`:37-50`) require `protocolVersion < 2^64`;
* the new version equals the old one, so `ProtocolVersionTooSmall` (`:30-35`) never fires;
* `patchOnly = false` (`:55`), so a pending L2 upgrade transaction or its batch number reverts
  (`:69-78`);
* the transaction's type is the upgrade type, so its hash is stored
  (`BaseZkSyncUpgrade.sol:162-202`); its nonce `protocolVersion >> 32` equals the new minor
  version exactly when the major is zero. The transaction's validation is omitted (reject-only).

The protocol version is rewritten with its own value. -/
def genesisEffect (e : Env) (s : State) : Option State :=
  req (s.settlementLayer = 0) <|
  req (s.protocolVersion < 2 ^ 64) <|
  req (s.upgradeTxHash = 0) <|
  req (s.upgradeBatchNumber = 0) <|
  some { s with upgradeTxHash := e.genesisTxHash s.chainTypeManager s.protocolVersion }

/-- The premise that the address the CTM reports as `l1GenesisUpgrade()` always holds the genuine
`L1GenesisUpgrade` code of this commit: whenever the genesis cut succeeds on a storage, so does
`genesisEffect`, with the same result. One-directional on purpose: the real code may also revert
where `genesisEffect` does not (the omitted reject-only checks), and every theorem that takes
this premise holds for it. -/
def GenuineGenesis (K : Config) : Prop :=
  ∀ (e : Env) (s s' : State),
    K.runCut e (genesisCut (e.l1GenesisUpgrade s.chainTypeManager)) s = some s' →
    genesisEffect e s = some s'

/-! ## The facet's functions -/

/-- `onlyL1` (`Admin.sol:95-104`). -/
def onlyL1 (K : Config) (k : Option State) : Option State := req (K.onL1 = true) k

/-- `onlySettlementLayer` (`ZKChainBase.sol:141-146`). -/
def onlySettlementLayer (s : State) (k : Option State) : Option State :=
  req (s.settlementLayer = 0) k

/-- `_enforceNoUnverifiedBatchesForChainConfigUpdate` (`Admin.sol:211-215`). -/
def noUnverifiedBatches (s : State) (k : Option State) : Option State :=
  req (s.totalBatchesCommitted = s.totalBatchesVerified) k

/-- The second half of `upgradeChainFromVersion` (`Admin.sol:570-589`), once the cut is read. -/
def upgradeWithCut (K : Config) (e : Env) (s : State) (c : Call) (v : ℕ) (cut : Cut) :
    Option State :=
  req (s.protocolVersion = v) <|                                                    -- :570-572
  req (c.sender ≠ s.admin ∧ c.sender ≠ s.chainTypeManager →                        -- :577-585
      e.upgradeTimestamp s.chainTypeManager v ≠ 0
        ∧ e.upgradeTimestamp s.chainTypeManager v ≤ c.time) <|
  match executeDiamondCut K e cut s with                                            -- :586
  | none => none
  | some s₁ => req (v < s₁.protocolVersion) (some s₁)                               -- :587-589

/-- The body of each function with its modifiers, in source order. `c.sender` is `msg.sender`,
`c.time` is `block.timestamp`. -/
def exec (K : Config) (e : Env) (s : State) (c : Call) : Option State :=
  match c.entry with
  -- `setPendingAdmin` (`Admin.sol:131-137`), `onlyAdmin`.
  | .setPendingAdmin a =>
    req (c.sender = s.admin) <| some { s with pendingAdmin := a }
  -- `acceptAdmin` (`Admin.sol:140-153`).
  | .acceptAdmin =>
    req (c.sender = s.pendingAdmin) <|
    some { s with admin := s.pendingAdmin, pendingAdmin := 0 }
  -- `setValidator` (`Admin.sol:156-159`), `onlyChainTypeManager`.
  | .setValidator v b =>
    req (c.sender = s.chainTypeManager) <|
    some { s with validators := fun x => if x = v then b else s.validators x }
  -- `setPriorityTxMaxGasLimit` (`Admin.sol:162-170`), `onlyChainTypeManager onlyL1`.
  | .setPriorityTxMaxGasLimit n =>
    req (c.sender = s.chainTypeManager) <| onlyL1 K <|
    req (n ≤ PRIORITY_TX_MAX_GAS_LIMIT) <|
    some { s with priorityTxMaxGasLimit := n }
  -- `setZKsyncOSMaxTxGasLimit` (`Admin.sol:173-187`), `onlyAdmin onlySettlementLayer`.
  | .setZKsyncOSMaxTxGasLimit n =>
    req (c.sender = s.admin) <| onlySettlementLayer s <|
    req (ZKSYNC_OS_DEFAULT_MAX_TX_GAS_LIMIT ≤ n) <|
    req (n ≤ ZKSYNC_OS_MAX_BLOCK_GAS_LIMIT) <|
    noUnverifiedBatches s <|
    some { s with zksyncOSMaxTxGasLimit := n }
  -- `setZKsyncOSL1TxFiltering` (`Admin.sol:190-199`), `onlyAdmin onlySettlementLayer`.
  | .setZKsyncOSL1TxFiltering b =>
    req (c.sender = s.admin) <| onlySettlementLayer s <|
    req (¬ (b = true ∧ s.priorityMode.canBeActivated = true)) <|
    noUnverifiedBatches s <|
    some { s with l1TxFiltering := b }
  -- `setZKsyncOSLargeContractsEnabled` (`Admin.sol:202-208`), `onlyAdmin onlySettlementLayer`.
  | .setZKsyncOSLargeContractsEnabled b =>
    req (c.sender = s.admin) <| onlySettlementLayer s <|
    noUnverifiedBatches s <|
    some { s with largeContracts := b }
  -- `changeFeeParams` (`Admin.sol:218-264`), `onlyAdminOrChainTypeManager onlyL1`.
  | .changeFeeParams fp =>
    req (c.sender = s.admin ∨ c.sender = s.chainTypeManager) <| onlyL1 K <|
    req (minUpdateIntervalPassed s c.time = true) <|
    req (fp.priorityTxMaxPubdata ≤ fp.maxPubdataPerBatch) <|
    req (fp.pricingMode = s.feeParams.pricingMode) <|
    req (s.priorityMode.canBeActivated = true →
        priceChangeWithinBound s s.feeParams fp s.multNominator s.multDenominator
            s.multNominator s.multDenominator = true
          ∧ fp.priorityTxMaxPubdata = s.feeParams.priorityTxMaxPubdata
          ∧ fp.maxPubdataPerBatch = s.feeParams.maxPubdataPerBatch
          ∧ fp.maxL2GasPerBatch = s.feeParams.maxL2GasPerBatch) <|
    some { s with feeParams := fp, lastFeeParamsUpdate := c.time }
  -- `setTokenMultiplier` (`Admin.sol:267-295`), `onlyAdminOrChainTypeManager onlyL1`.
  | .setTokenMultiplier n d =>
    req (c.sender = s.admin ∨ c.sender = s.chainTypeManager) <| onlyL1 K <|
    req (d ≠ 0) <|
    req (minUpdateIntervalPassed s c.time = true) <|
    req (s.priorityMode.canBeActivated = true →
        priceChangeWithinBound s s.feeParams s.feeParams s.multNominator s.multDenominator n d
          = true) <|
    some { s with multNominator := n, multDenominator := d, lastTokenMultiplierUpdate := c.time }
  -- `setPubdataPricingMode` (`Admin.sol:359-365`), `onlyAdmin onlyL1`.
  | .setPubdataPricingMode m =>
    req (c.sender = s.admin) <| onlyL1 K <|
    req (s.priorityMode.canBeActivated = false) <|
    some { s with feeParams := { s.feeParams with pricingMode := m } }
  -- `setTransactionFilterer` (`Admin.sol:368-379`), `onlyAdmin onlyL1`.
  | .setTransactionFilterer a =>
    req (c.sender = s.admin) <| onlyL1 K <|
    req (s.priorityMode.canBeActivated = false) <|
    some { s with transactionFilterer := a }
  -- `setDAValidatorPair` (`Admin.sol:387-401`), `onlyAdmin`; `_setDAValidatorPair`
  -- (`ZKChainBase.sol:307-313`).
  | .setDAValidatorPair l1 sch =>
    req (c.sender = s.admin) <|
    req (l1 ≠ 0) <|
    req (sch ≠ DA_SCHEME_NONE) <|
    req (¬ (s.isPermanentRollup = true ∧ e.isPairAllowed l1 sch = false)) <|
    some { s with l1DAValidator := l1, l2DAScheme := sch }
  -- `setPubdataContent` (`Admin.sol:404-413`), `onlyAdmin`.
  | .setPubdataContent pc =>
    req (c.sender = s.admin) <|
    req (s.isPermanentRollup = false) <|
    noUnverifiedBatches s <|
    some { s with pubdataContent := pc }
  -- `setProofSystemStatus` (`Admin.sol:416-432`): the caller is the Bridgehub owner for a disable
  -- on a chain that requires its second proof system, else the admin.
  | .setProofSystemStatus ps en =>
    req (c.sender = (if en = false ∧ s.secondProofSystemRequired = true then e.bridgehubOwner
                     else s.admin)) <|
    req (ps = PROOF_SYSTEM_ZISK) <|
    some { s with disabledProofSystems :=
      if en then s.disabledProofSystems &&& (255 - 2 ^ PROOF_SYSTEM_ZISK)
      else s.disabledProofSystems ||| 2 ^ PROOF_SYSTEM_ZISK }
  -- `makePermanentRollup` (`Admin.sol:435-451`), `onlyAdmin onlySettlementLayer`.
  | .makePermanentRollup =>
    req (c.sender = s.admin) <| onlySettlementLayer s <|
    req (s.isPermanentRollup = false) <|
    req (s.pubdataContent = .fullPubdata) <|
    req (e.isPairAllowed s.l1DAValidator s.l2DAScheme = true) <|
    some { s with isPermanentRollup := true }
  -- `permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`), `onlyAdmin onlySettlementLayer`.
  | .permanentlyRequireSecondProofSystem =>
    req (c.sender = s.admin) <| onlySettlementLayer s <|
    req (s.secondProofSystemRequired = false) <|
    req (e.getProofMode s.verifier s.disabledProofSystems
          = ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) <|
    some { s with secondProofSystemRequired := true }
  -- `setPriorityModeTransactionFilterer` (`Admin.sol:468-479`),
  -- `onlyChainTypeManager onlySettlementLayer onlyL1`.
  | .setPriorityModeTransactionFilterer a =>
    req (c.sender = s.chainTypeManager) <| onlySettlementLayer s <| onlyL1 K <|
    some { s with
      transactionFilterer := if s.priorityMode.canBeActivated then a else s.transactionFilterer
      priorityMode := { s.priorityMode with transactionFilterer := a } }
  -- `permanentlyAllowPriorityMode` (`Admin.sol:482-515`),
  -- `onlyAdmin onlySettlementLayer onlyL1`.
  | .permanentlyAllowPriorityMode =>
    req (c.sender = s.admin) <| onlySettlementLayer s <| onlyL1 K <|
    req (s.priorityMode.canBeActivated = false) <|
    req (s.l1TxFiltering = false) <|
    req (s.pausedDepositsTimestamp = 0) <|
    req (s.priorityTreeSize ≠ 0) <|
    req (s.requestTimestamp s.firstUnprocessed ≠ 0) <|
    some { s with
      transactionFilterer := s.priorityMode.transactionFilterer
      priorityMode := { s.priorityMode with canBeActivated := true } }
  -- `deactivatePriorityMode` (`Admin.sol:518-521`),
  -- `onlyPriorityMode onlyChainTypeManager onlySettlementLayer onlyL1`.
  | .deactivatePriorityMode =>
    req (s.priorityMode.activated = true) <|
    req (c.sender = s.chainTypeManager) <| onlySettlementLayer s <| onlyL1 K <|
    some { s with priorityMode := { s.priorityMode with activated := false } }
  -- `activatePriorityMode` (`Admin.sol:524-552`),
  -- `onlySettlementLayer onlyL1 notPriorityMode nonReentrant`; no caller check.
  | .activatePriorityMode =>
    onlySettlementLayer s <| onlyL1 K <|
    req (s.priorityMode.activated = false) <|
    req (s.priorityMode.canBeActivated = true) <|
    req (s.isPermanentRollup = true) <|
    req (s.requestTimestamp s.firstUnprocessed ≠ 0) <|
    req (s.requestTimestamp s.firstUnprocessed + PRIORITY_EXPIRATION ≤ c.time) <|
    revertBatches
      { s with priorityMode := { s.priorityMode with activated := true } }
      s.totalBatchesExecuted
  -- `upgradeChainFromVersion` (`Admin.sol:559-590`), `onlyAdminOrChainTypeManagerOrValidator`;
  -- the cut is read first (`:566-568`; `none` reverts).
  | .upgradeChainFromVersion _ v =>
    req (c.sender = s.admin ∨ c.sender = s.chainTypeManager ∨ s.validators c.sender = true) <|
    match e.upgradeCutForVersion s.chainTypeManager v with
    | none => none
    | some cut => upgradeWithCut K e s c v cut
  -- `executeUpgrade` (`Admin.sol:593-595`), `onlyChainTypeManager`.
  | .executeUpgrade cut =>
    req (c.sender = s.chainTypeManager) <| executeDiamondCut K e cut s
  -- `genesisUpgrade` (`Admin.sol:599-609`), `onlyChainTypeManager`.
  | .genesisUpgrade =>
    req (c.sender = s.chainTypeManager) <|
    executeDiamondCut K e (genesisCut (e.l1GenesisUpgrade s.chainTypeManager)) s
  -- `freezeDiamond` (`Admin.sol:616-626`), `onlyChainTypeManager`.
  | .freezeDiamond =>
    req (c.sender = s.chainTypeManager) <|
    req (s.frozen = false) <|
    some { s with frozen := true }
  -- `unfreezeDiamond` (`Admin.sol:629-639`), `onlyChainTypeManager`.
  | .unfreezeDiamond =>
    req (c.sender = s.chainTypeManager) <|
    req (s.frozen = true) <|
    some { s with frozen := false }

/-- A call through the diamond proxy: `require(!isFrozen || !facet.isFreezable, "q1")`
(`DiamondProxy.sol:36`), then the facet. -/
def call (K : Config) (e : Env) (s : State) (c : Call) : Option State :=
  req (¬ (s.frozen = true ∧ s.freezable c.entry.sel = true)) (exec K e s c)

/-- Who may call each entry, read off its modifiers and its explicit caller checks. -/
def Role (e : Env) (s : State) (a : Address) : Entry → Prop
  | .setPendingAdmin _ => a = s.admin
  | .acceptAdmin => a = s.pendingAdmin
  | .setValidator _ _ => a = s.chainTypeManager
  | .setPriorityTxMaxGasLimit _ => a = s.chainTypeManager
  | .setZKsyncOSMaxTxGasLimit _ => a = s.admin
  | .setZKsyncOSL1TxFiltering _ => a = s.admin
  | .setZKsyncOSLargeContractsEnabled _ => a = s.admin
  | .changeFeeParams _ => a = s.admin ∨ a = s.chainTypeManager
  | .setTokenMultiplier _ _ => a = s.admin ∨ a = s.chainTypeManager
  | .setPubdataPricingMode _ => a = s.admin
  | .setTransactionFilterer _ => a = s.admin
  | .setDAValidatorPair _ _ => a = s.admin
  | .setPubdataContent _ => a = s.admin
  | .setProofSystemStatus _ en =>
    a = (if en = false ∧ s.secondProofSystemRequired = true then e.bridgehubOwner else s.admin)
  | .makePermanentRollup => a = s.admin
  | .permanentlyRequireSecondProofSystem => a = s.admin
  | .setPriorityModeTransactionFilterer _ => a = s.chainTypeManager
  | .permanentlyAllowPriorityMode => a = s.admin
  | .deactivatePriorityMode => a = s.chainTypeManager
  | .activatePriorityMode => True
  | .upgradeChainFromVersion _ _ =>
    a = s.admin ∨ a = s.chainTypeManager ∨ s.validators a = true
  | .executeUpgrade _ => a = s.chainTypeManager
  | .genesisUpgrade => a = s.chainTypeManager
  | .freezeDiamond => a = s.chainTypeManager
  | .unfreezeDiamond => a = s.chainTypeManager

/-! ## Runs -/

/-- The fields only this facet (or a cut) writes. -/
structure Owned where
  admin : Address
  pendingAdmin : Address
  chainTypeManager : Address
  validators : Address → Bool
  frozen : Bool
  freezable : ℕ → Bool
  protocolVersion : ℕ
  verifier : Address
  priorityTxMaxGasLimit : ℕ
  zksyncOSMaxTxGasLimit : ℕ
  l1TxFiltering : Bool
  largeContracts : Bool
  feeParams : FeeParams
  multNominator : ℕ
  multDenominator : ℕ
  lastFeeParamsUpdate : ℕ
  lastTokenMultiplierUpdate : ℕ
  transactionFilterer : Address
  pubdataContent : PubdataContent
  secondProofSystemRequired : Bool
  disabledProofSystems : ℕ
  priorityMode : PriorityModeInfo

/-- The `Owned` part of a state. -/
def State.owned (s : State) : Owned :=
  ⟨s.admin, s.pendingAdmin, s.chainTypeManager, s.validators, s.frozen, s.freezable,
   s.protocolVersion, s.verifier, s.priorityTxMaxGasLimit, s.zksyncOSMaxTxGasLimit,
   s.l1TxFiltering, s.largeContracts, s.feeParams, s.multNominator, s.multDenominator,
   s.lastFeeParamsUpdate, s.lastTokenMultiplierUpdate, s.transactionFilterer, s.pubdataContent,
   s.secondProofSystemRequired, s.disabledProofSystems, s.priorityMode⟩

/-- A write by another facet (Executor, Committer, Mailbox, Migrator): the `Owned` fields are
unchanged, and `isPermanentRollup` is never cleared (`Migrator.sol:234-236, 241`). Everything else —
batch counters, priority tree, request timestamps, `pausedDepositsTimestamp`, settlement layer,
DA pair, the L2 upgrade transaction's hash and batch number — may change arbitrarily. -/
def Foreign (s s' : State) : Prop :=
  s'.owned = s.owned ∧ (s.isPermanentRollup = true → s'.isPermanentRollup = true)

/-- The chain's storage together with the environment it reads. -/
structure World where
  st : State
  env : Env

/-- A step of a run. -/
inductive Label where
  /-- A call to the facet through the diamond. -/
  | call (c : Call)
  /-- Other contracts change what the facet reads (CTM commits, notifier schedules, verifier
  swaps, ownership changes). -/
  | env (e : Env)
  /-- Another facet writes this storage, leaving the state `s'`. -/
  | foreign (s' : State)

/-- Whether a label runs a cut. -/
def Label.runsCut : Label → Bool
  | .call c => c.entry.runsCut
  | _ => false

/-- One step. -/
inductive Step (K : Config) : World → Label → World → Prop where
  | call {w : World} {c : Call} {s' : State} :
      call K w.env w.st c = some s' → Step K w (.call c) ⟨s', w.env⟩
  | env {w : World} (e : Env) : Step K w (.env e) ⟨w.st, e⟩
  | foreign {w : World} {s' : State} : Foreign w.st s' → Step K w (.foreign s') ⟨s', w.env⟩

/-- A run: a sequence of steps. -/
inductive Run (K : Config) : World → List Label → World → Prop where
  | nil (w : World) : Run K w [] w
  | cons {w w₁ w₂ : World} {l : Label} {ls : List Label} :
      Step K w l w₁ → Run K w₁ ls w₂ → Run K w (l :: ls) w₂

/-- Whether a label is a call to `upgradeChainFromVersion`. -/
def Label.isUpgrade : Label → Bool
  | .call ⟨_, _, .upgradeChainFromVersion _ _⟩ => true
  | _ => false

/-- Whether a label is a call to `executeUpgrade`. -/
def Label.isExecuteUpgrade : Label → Bool
  | .call ⟨_, _, .executeUpgrade _⟩ => true
  | _ => false

/-- Whether a label is a call to `genesisUpgrade`. -/
def Label.isGenesis : Label → Bool
  | .call ⟨_, _, .genesisUpgrade⟩ => true
  | _ => false

/-! ## Stage-1 (priority mode) invariant -/

/-- What priority mode needs to hold of the storage:

* priority mode is active only if it was allowed and the chain is a permanent rollup;
* once allowed, operator filtering of priority transactions is off and the transaction filterer
  is the one governance chose for priority mode. -/
def Stage1Inv (s : State) : Prop :=
  (s.priorityMode.activated = true →
      s.priorityMode.canBeActivated = true ∧ s.isPermanentRollup = true)
  ∧ (s.priorityMode.canBeActivated = true →
      s.l1TxFiltering = false ∧ s.transactionFilterer = s.priorityMode.transactionFilterer)

end Contracts.AdminFacet
