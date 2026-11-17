import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `ChainAdminOwnable`, the calls it makes, and the admin roles it holds

Source: era-contracts `draft/v0.35.0` at `b17415d20`. Paths are relative to
`l1-contracts/contracts/` unless they name another directory of `l1-contracts/`.
`governance/ChainAdminOwnable.sol` is byte-identical at main `70096e2ea`; there the `Admin` facet
functions below sit at `facets/Admin.sol:128-150` and `:252`, and the Bridgehub's at
`BridgehubBase.sol:140-145, 180-205`, with the same code.

The OpenZeppelin v4 libraries are the submodules `lib/openzeppelin-contracts-v4` (`OZ/` below)
and `lib/openzeppelin-contracts-upgradeable-v4` (`OZU/`), both on branch `release-v4.9`
(`.gitmodules`). Their line numbers are those of v4.9.6; the cited functions are unchanged
across v4.9.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainAdminOwnable.Properties.Authority` and
`EraSpec.Contracts.ChainAdminOwnable.Properties.AdminRoles`, proved in the matching `Proofs`
modules.

## The contract (`governance/ChainAdminOwnable.sol`)

    contract ChainAdminOwnable is IChainAdminOwnable, Ownable2Step {                     // :16
        address public tokenMultiplierSetter;                                            // :20
        constructor(_initialOwner, _initialTokenMultiplierSetter)                        // :22-30
            if (_initialOwner == 0) revert ZeroAddress(); _transferOwnership(_initialOwner);
            tokenMultiplierSetter = _initialTokenMultiplierSetter;  // may be zero
        function setTokenMultiplierSetter(x) external onlyOwner { setter = x; }          // :34-37
        function multicall(Call[] calldata _calls, bool _requireSuccess)
                external payable onlyOwner {                                             // :43-59
            if (_calls.length == 0) revert NoCallsProvided();                            // :44-46
            for (i = 0; i < _calls.length; ++i) {
                (success, ret) = _calls[i].target.call{value: _calls[i].value}(_calls[i].data); // :50
                if (_requireSuccess && !success) revert(ret);                            // :51-56
                emit CallExecuted(_calls[i], success, ret);                              // :57
            }
        }
        function setTokenMultiplier(IAdmin _chainContract, uint128 n, uint128 d) external { // :65-70
            if (msg.sender != tokenMultiplierSetter) revert Unauthorized(msg.sender);    // :66-68
            _chainContract.setTokenMultiplier(n, d);                                     // :69
        }
        receive() external payable {}                                                    // :73
    }

`Ownable2Step` (`OZ/access/Ownable2Step.sol`) adds `pendingOwner()` (:27-29),
`transferOwnership(x)` (`onlyOwner`, `_pendingOwner = x`, no zero check, :35-38),
`acceptOwnership()` (`pendingOwner() == msg.sender`, then `_transferOwnership(msg.sender)`,
:52-56) and the override `_transferOwnership` that deletes the nomination (:44-47).
`Ownable` (`OZ/access/Ownable.sol`) keeps `renounceOwnership()` (`onlyOwner`,
`_transferOwnership(address(0))`, :61-63): `ChainAdminOwnable` does not override it, so a renounce
sets both the owner and the nomination to zero.

The contract has no `fallback`. A call with non-empty calldata whose selector is none of its
functions reverts; one with empty calldata runs `receive()`.

The call at :69 is a high-level call to a function with no return values: Solidity checks that
`_chainContract` has code, then makes the call with value zero and calldata
`abi.encodeCall(IAdmin.setTokenMultiplier, (n, d))` (`multiplierData`), and a failing call
reverts `setTokenMultiplier` with it.

## Where `ChainAdminOwnable` holds authority

* **A ZK chain's admin.** `RegisterZKChain.s.sol:309-311` (`deploy-scripts/ctm/`) deploys a
  `ChainAdminOwnable` for each chain; `ChainAdmin.sol:27-28` calls it the recommended admin. The
  diamond's admin pair is written only by the `Admin` facet's `setPendingAdmin` (`onlyAdmin`,
  `facets/Admin.sol:131-137`, `ZKChainBase.sol:46-51`) and `acceptAdmin` (by the pending admin,
  `:140-153`), by `DiamondInit.initialize` when the diamond is created (`DiamondInit.sol:119`), and
  by whatever a diamond cut's initialization delegatecall writes (`libraries/Diamond.sol:318`).
  Every cut is composed by the chain type manager: `executeUpgrade` and `genesisUpgrade` are
  `onlyChainTypeManager` (`facets/Admin.sol:593-609`), and `upgradeChainFromVersion`, callable by
  the admin, the chain type manager or a validator after the upgrade timestamp (`:559-590`), runs
  the cut the chain type manager composed. `setTokenMultiplier(uint128,uint128)`, selector
  `0x235d9eb5` (`:662-663`), is `onlyAdminOrChainTypeManager onlyL1` (`:267`,
  `ZKChainBase.sol:120-125`).
* **The Bridgehub's admin.** `DeployL1CoreContracts.s.sol:86` (`deploy-scripts/ecosystem/`)
  deploys a `ChainAdminOwnable` as `bridgehubAdmin`, constructed with setter zero
  (`DeployL1CoreUtils.s.sol:117-118`). The Bridgehub (`core/bridgehub/L1Bridgehub.sol:41`, on
  `BridgehubBase`, `Ownable2StepUpgradeable`, `BridgehubBase.sol:52`) gates `createNewChain` and
  `addTokenAssetId` on `onlyOwnerOrAdmin` (`L1Bridgehub.sol:113`, `BridgehubBase.sol:139-144,
  256`). Its `admin`/`pendingAdmin` (`:82`, `:85`) are written only by `setPendingAdmin`
  (`onlyOwnerOrAdmin`, nonzero argument, `:179-188`) and `acceptAdmin` (`:191-204`). Its
  `owner`/`pendingOwner` are `OZU`'s (`OZU/access/OwnableUpgradeable.sol:40-43, 55-57, 66-68`,
  `OZU/access/Ownable2StepUpgradeable.sol:42-45, 51-54, 59-63`); `initialize` also writes the owner
  but reverts once the proxy is initialized (`reentrancyGuardInitializer`,
  `common/ReentrancyGuard.sol:43-63`). `L1Bridgehub` and its bases declare no `fallback` and no
  `receive`.

## Modelling choices

* **One inductive execution relation** `Sem cfg j S L S'`, in the style of the
  `cov/chain-admin` branch's `ChainAdmin` model: judgement `j` takes the world state `S` to `S'`
  and leaves the ghost log `L`. A revert is the absence of a derivation. A frame that reverts
  leaves nothing in the log: its writes and its log are undone together. `callFails` is a call
  that fails with no effect (a revert inside the callee, a failed value transfer, out of gas);
  any call may fail.
* **Three judgements.** `.call s c ok`: `s` makes call `c`, with low-level result `ok`. `.loop`:
  the remaining iterations of a `multicall`. `.acts`: code the model does not know, while it holds
  control. That code makes any sequence of calls, each by any sender other than the
  `ChainAdminOwnable` and the zero address. A run of top-level transactions is an `.acts`
  derivation too.
* **Callers are over-approximated.** The model does not tie a call's sender to whose code is
  running: while any unknown code runs, any address except the `ChainAdminOwnable` and zero may
  call anything, including the owner and the setter, at any depth. This covers every re-entrant
  callee and every callback.
* **Every call with `msg.sender = cfg.cao` comes from one of two rules.** Only
  `loopStep` (an iteration of `multicall`, `:50`) and `caoSetMultiplier` (`:69`) have a premise
  `Sem cfg (.call cfg.cao _ _)`; `actsCall` requires its sender to differ from `cfg.cao`. Each of
  the two rules logs the call it makes (`Event.caoCall`) with its origin: the frame's
  `msg.sender` and the `ChainAdminOwnable`'s storage when that frame was entered.
* **Ghost log.** `Event.caoCall` (every call the `ChainAdminOwnable` made in a frame that
  committed, with its low-level result), `Event.caoWrite` (every committed write to its storage,
  with the writer and the storage before), `Event.chainEntry` / `Event.hubEntry` (every committed
  call into a diamond or the Bridgehub that the model runs, with sender and selector) and
  `Event.cut` (a diamond cut). Nested frames' events come before the event of the call that
  contains them.
* **Calldata is bytes**; selectors are the real four-byte constants (`cast sig`, and the
  `Admin` facet's own table at `facets/Admin.sol:646-708`). ABI decoding is a parameter
  (`Abi`), one function per argument tuple; a decoding failure is a revert.
* **Diamonds.** `Config.isChain` marks the ZK chain diamonds, which run the `b17415d20` facets.
  Their admin pair is state. `setPendingAdmin` and `acceptAdmin` are modelled exactly. Every other
  function gated on the admin (`onlyAdmin`, `ADMIN_ONLY_SELECTORS`; `onlyAdminOrChainTypeManager`,
  `ADMIN_OR_CTM_SELECTORS`; the complete list at `b17415d20` is in `facets/Admin.sol` and
  `facets/Migrator.sol`) is modelled by its access check followed by unknown code; its other
  checks (`onlyL1`, `onlySettlementLayer`, argument checks such as `setTokenMultiplier`'s
  denominator, interval and price bound, `:268-285`) and its writes are not modelled. A cut
  (`executeUpgrade`, `genesisUpgrade`, `upgradeChainFromVersion`) leaves the admin pair arbitrary
  and then runs unknown code; for `upgradeChainFromVersion` any sender is allowed (the validator
  set and the timestamp gate are not modelled). Every other diamond function is unknown code with
  no access check, which leaves every admin pair to the rules above. That includes
  `setProofSystemStatus` (`:416-432`), whose check also admits the Bridgehub's owner, and the
  `onlyChainTypeManager` functions. The diamond's code is fixed: after a cut its functions
  are still modelled as the `b17415d20` ones, so a result that admits cuts says nothing about the
  code a cut installs. The set of diamonds is fixed too: creating one (`DiamondInit.initialize`
  writing `s.admin`, `DiamondInit.sol:119`) is not a step, so results about an admin pair concern
  diamonds that exist when the run starts.
* **The Bridgehub.** One proxy at `cfg.hub` running the `b17415d20` `L1Bridgehub`. Owner,
  nominee, admin and pending admin are state. The modelled functions are the five that write
  them; `initialize` reverts (initialized proxy); every other function of `BRIDGEHUB_SELECTORS`
  is unknown code that writes none of the four. A selector outside the table reverts. The proxy
  is OpenZeppelin's `TransparentUpgradeableProxy` (`deploy-scripts/utils/deploy/DeployUtils.sol:7,
  19-21`): calls by its admin (`cfg.hubProxyAdmin`) reach only its admin interface
  (`upgradeTo`, `upgradeToAndCall`, `changeAdmin`, `admin`, `implementation`) and otherwise revert
  (`OZ/proxy/transparent/TransparentUpgradeableProxy.sol:84-106`), never the implementation. They
  are not modelled beyond failing, so the Bridgehub's code never changes in this model.
* **Other code.** A call to any other address runs unknown code (`external`).
* **Not modelled:** ETH balances (a failed value transfer is a failed call), events other than
  the ghost log, gas, the extcodesize check before :69 (omitting it only adds runs), other
  `ChainAdminOwnable` instances (they are unknown code), the chain type manager's own admin role
  (also held by the hub's `ChainAdminOwnable`, `protocol-docs/ecosystem-deployment.md:249`), and
  the Bridgehub's `ProxyAdmin` upgrades.
-/

namespace Contracts.ChainAdminOwnable

/-! ## Words, bytes and calls -/

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- Raw calldata. -/
abbrev Bytes := List UInt8

/-- `IChainAdminOwnable.Call` (`governance/IChainAdminOwnable.sol:15-19`). -/
structure Call where
  /-- The address called. -/
  target : Address
  /-- The value sent. -/
  value : UInt256
  /-- The calldata. -/
  data : Bytes
deriving DecidableEq

/-! ## Selectors (`cast sig` of each signature) -/

/-- `transferOwnership(address)`. -/
def SEL_TRANSFER_OWNERSHIP : Bytes := [0xf2, 0xfd, 0xe3, 0x8b]
/-- `acceptOwnership()`. -/
def SEL_ACCEPT_OWNERSHIP : Bytes := [0x79, 0xba, 0x50, 0x97]
/-- `renounceOwnership()`. -/
def SEL_RENOUNCE_OWNERSHIP : Bytes := [0x71, 0x50, 0x18, 0xa6]
/-- `owner()`. -/
def SEL_OWNER : Bytes := [0x8d, 0xa5, 0xcb, 0x5b]
/-- `pendingOwner()`. -/
def SEL_PENDING_OWNER : Bytes := [0xe3, 0x0c, 0x39, 0x78]
/-- `ChainAdminOwnable.setTokenMultiplierSetter(address)`. -/
def SEL_SET_SETTER : Bytes := [0x60, 0x14, 0x41, 0x97]
/-- `ChainAdminOwnable.tokenMultiplierSetter()`. -/
def SEL_SETTER : Bytes := [0x34, 0x25, 0xeb, 0x89]
/-- `ChainAdminOwnable.multicall((address,uint256,bytes)[],bool)`. -/
def SEL_MULTICALL : Bytes := [0x69, 0x34, 0x0b, 0xeb]
/-- `ChainAdminOwnable.setTokenMultiplier(address,uint128,uint128)`. -/
def SEL_SET_MULTIPLIER_VIA : Bytes := [0x4d, 0x4a, 0x1e, 0xca]
/-- `IAdmin.setTokenMultiplier(uint128,uint128)` (`facets/Admin.sol:662-663`). -/
def SEL_SET_MULTIPLIER : Bytes := [0x23, 0x5d, 0x9e, 0xb5]
/-- `setPendingAdmin(address)`, on the diamond (`facets/Admin.sol:674-675`) and the Bridgehub. -/
def SEL_SET_PENDING_ADMIN : Bytes := [0x4d, 0xd1, 0x8b, 0xf5]
/-- `acceptAdmin()`, on the diamond (`facets/Admin.sol:650-651`) and the Bridgehub. -/
def SEL_ACCEPT_ADMIN : Bytes := [0x0e, 0x18, 0xb6, 0x81]
/-- `executeUpgrade(((address,uint8,bool,bytes4[])[],address,bytes))` (`facets/Admin.sol:682-683`). -/
def SEL_EXECUTE_UPGRADE : Bytes := [0xa9, 0xf6, 0xd9, 0x41]
/-- `genesisUpgrade()` (`facets/Admin.sol:690-691`). -/
def SEL_GENESIS_UPGRADE : Bytes := [0xd2, 0x41, 0xf6, 0x18]
/-- `upgradeChainFromVersion(address,uint256)` (`facets/Admin.sol:648-649`). -/
def SEL_UPGRADE_CHAIN_FROM_VERSION : Bytes := [0x03, 0x12, 0x9a, 0xd9]
/-- `L1Bridgehub.initialize(address)`. -/
def SEL_INITIALIZE : Bytes := [0xc4, 0xd6, 0x6d, 0xe8]

/-- The `view` functions of `ChainAdminOwnable`: `owner()`, `pendingOwner()`,
`tokenMultiplierSetter()`. -/
def CAO_VIEW_SELECTORS : List Bytes := [SEL_OWNER, SEL_PENDING_OWNER, SEL_SETTER]

/-- The diamond functions that run a cut. -/
def CUT_SELECTORS : List Bytes :=
  [SEL_EXECUTE_UPGRADE, SEL_GENESIS_UPGRADE, SEL_UPGRADE_CHAIN_FROM_VERSION]

/-- The diamond's `onlyAdmin` functions (`ZKChainBase.sol:46-51`) other than `setPendingAdmin`,
with the line of each declaration and of its entry in the facet's `selectors()` table. -/
def ADMIN_ONLY_SELECTORS : List Bytes :=
  [ -- setZKsyncOSMaxTxGasLimit(uint64) (`facets/Admin.sol:173`; `:670-671`)
    [0x2f, 0x25, 0x7a, 0x5c],
    -- setZKsyncOSL1TxFiltering(bool) (`:190`; `:692-693`)
    [0xdf, 0x16, 0xd0, 0xa3],
    -- setZKsyncOSLargeContractsEnabled(bool) (`:202`; `:652-653`)
    [0x12, 0x0c, 0x12, 0xc2],
    -- setPubdataPricingMode(uint8) (`:359`; `:696-697`)
    [0xe7, 0x6d, 0xb8, 0x65],
    -- setTransactionFilterer(address) (`:368`; `:660-661`)
    [0x21, 0xf6, 0x03, 0xd7],
    -- setDAValidatorPair(address,uint8) (`:387`; `:666-667`)
    [0x27, 0x65, 0xd0, 0x79],
    -- setPubdataContent(uint8) (`:404`; `:694-695`)
    [0xe5, 0x19, 0x35, 0xf5],
    -- makePermanentRollup() (`:435`; `:680-681`)
    [0x6e, 0x76, 0x2e, 0x98],
    -- permanentlyRequireSecondProofSystem() (`:454`; `:658-659`)
    [0x1d, 0x11, 0x78, 0xd3],
    -- permanentlyAllowPriorityMode() (`:482`; `:656-657`)
    [0x1b, 0x48, 0xb9, 0x4a],
    -- unpauseDeposits() (`facets/Migrator.sol:132`; `:392-393`)
    [0x63, 0xd8, 0x88, 0x2a] ]

/-- `setTransactionFilterer(address)`, one of `ADMIN_ONLY_SELECTORS`. -/
def SEL_SET_TRANSACTION_FILTERER : Bytes := [0x21, 0xf6, 0x03, 0xd7]

/-- `changeFeeParams((uint8,uint32,uint32,uint32,uint32,uint64))`, one of
`ADMIN_OR_CTM_SELECTORS`. -/
def SEL_CHANGE_FEE_PARAMS : Bytes := [0x64, 0xbf, 0x8d, 0x66]

/-- The diamond's `onlyAdminOrChainTypeManager` functions (`ZKChainBase.sol:120-125`). -/
def ADMIN_OR_CTM_SELECTORS : List Bytes :=
  [ -- changeFeeParams(...) (`facets/Admin.sol:218`; `:678-679`)
    SEL_CHANGE_FEE_PARAMS,
    -- setTokenMultiplier(uint128,uint128) (`:267`; `:662-663`)
    SEL_SET_MULTIPLIER,
    -- pauseDepositsBeforeInitiatingMigration() (`facets/Migrator.sol:105`; `:390-391`)
    [0x42, 0x24, 0x9f, 0x9f] ]

/-- The diamond functions the model runs with their access checks. -/
def CHAIN_MODELLED_SELECTORS : List Bytes :=
  [SEL_SET_PENDING_ADMIN, SEL_ACCEPT_ADMIN] ++ ADMIN_ONLY_SELECTORS ++ ADMIN_OR_CTM_SELECTORS ++
    CUT_SELECTORS

/-- Every external function of `L1Bridgehub` at `b17415d20`, public getters included, in
ascending order: the 51 function entries of the ABI the repository commits for it
(`l1-contracts/zkstack-out/L1Bridgehub.sol/L1Bridgehub.json`), each hashed with `cast sig`. The
list was checked against the declarations of `L1Bridgehub.sol`, `BridgehubBase.sol`,
`Ownable2StepUpgradeable` and `PausableUpgradeable`. -/
def BRIDGEHUB_SELECTORS : List Bytes :=
  [ -- forwardedBridgeBurnSetSettlementLayer(uint256,uint256)
    [0x06, 0x41, 0xe4, 0xf7],
    -- ctmAssetIdToAddress(bytes32)
    [0x07, 0x62, 0x1f, 0x84],
    -- acceptAdmin()
    [0x0e, 0x18, 0xb6, 0x81],
    -- addTokenAssetId(bytes32)
    [0x1c, 0x50, 0xcf, 0xea],
    -- setSettlementLayerStatus(uint256,bool)
    [0x1d, 0x01, 0x6d, 0x30],
    -- forwardedBridgeConfirmTransferResult(uint256,uint8)
    [0x22, 0x40, 0x92, 0x13],
    -- ctmAssetIdFromChainId(uint256)
    [0x24, 0x35, 0x8c, 0x61],
    -- requestL2TransactionTwoBridges((uint256,uint256,uint256,uint256,uint256,address,address,uint256,bytes))
    [0x24, 0xfd, 0x57, 0xfb],
    -- setCTMAssetAddress(bytes32,address)
    [0x2d, 0xbc, 0xf5, 0x5f],
    -- L1_CHAIN_ID()
    [0x2f, 0x90, 0xb1, 0x84],
    -- removeChainTypeManager(address)
    [0x33, 0x2b, 0x96, 0xdc],
    -- sharedBridge()
    [0x38, 0x72, 0x07, 0x78],
    -- unpause()
    [0x3f, 0x4b, 0xa8, 0x3a],
    -- getAllZKChains()
    [0x49, 0x70, 0x7f, 0x31],
    -- setPendingAdmin(address)
    [0x4d, 0xd1, 0x8b, 0xf5],
    -- baseToken(uint256)
    [0x59, 0xec, 0x65, 0xa2],
    -- paused()
    [0x5c, 0x97, 0x5a, 0xbb],
    -- setAddresses(address,address,address,address,address)
    [0x5d, 0xd6, 0x8a, 0xcd],
    -- createNewChain(uint256,address,bytes32,address)
    [0x5f, 0xea, 0xea, 0x89],
    -- chainRegistrationSender()
    [0x66, 0x9e, 0x1e, 0x46],
    -- settlementLayer(uint256)
    [0x67, 0x1a, 0x71, 0x31],
    -- getAllZKChainChainIDs()
    [0x68, 0xb8, 0xd3, 0x31],
    -- registerNewZKChain(uint256,address,bool)
    [0x70, 0x11, 0xbe, 0x85],
    -- chainAssetHandler()
    [0x70, 0xd8, 0xaf, 0x87],
    -- ctmAssetIdFromAddress(address)
    [0x70, 0xfc, 0xcb, 0x52],
    -- renounceOwnership()
    [0x71, 0x50, 0x18, 0xa6],
    -- l2TransactionBaseCost(uint256,uint256,uint256,uint256)
    [0x71, 0x62, 0x32, 0x74],
    -- acceptOwnership()
    [0x79, 0xba, 0x50, 0x97],
    -- pause()
    [0x84, 0x56, 0xcb, 0x59],
    -- __DEPRECATED_migrationPaused()
    [0x89, 0x16, 0x25, 0x1f],
    -- owner()
    [0x8d, 0xa5, 0xcb, 0x5b],
    -- MAX_NUMBER_OF_ZK_CHAINS()
    [0x8f, 0x8d, 0x37, 0xa8],
    -- chainTypeManager(uint256)
    [0x9d, 0x5b, 0xd3, 0xda],
    -- setAddressesV31(address)
    [0xa1, 0x72, 0x23, 0xb0],
    -- registerAlreadyDeployedZKChain(uint256,address)
    [0xb5, 0x66, 0x2c, 0x5d],
    -- chainTypeManagerIsRegistered(address)
    [0xb9, 0x3c, 0x93, 0x66],
    -- assetRouter()
    [0xbc, 0x0a, 0xac, 0x10],
    -- initialize(address)
    [0xc4, 0xd6, 0x6d, 0xe8],
    -- l1CtmDeployer()
    [0xcb, 0xe8, 0x36, 0x12],
    -- messageRoot()
    [0xd4, 0xb9, 0xf4, 0xfa],
    -- requestL2TransactionDirect((uint256,uint256,address,uint256,bytes,uint256,uint256,bytes[],address))
    [0xd5, 0x24, 0x71, 0xc1],
    -- getHyperchain(uint256)
    [0xde, 0xad, 0x6f, 0x7f],
    -- assetIdIsRegistered(bytes32)
    [0xe0, 0xab, 0x63, 0x68],
    -- pendingOwner()
    [0xe3, 0x0c, 0x39, 0x78],
    -- baseTokenAssetId(uint256)
    [0xe5, 0x2d, 0xb4, 0xca],
    -- getZKChain(uint256)
    [0xe6, 0x80, 0xc4, 0xc1],
    -- whitelistedSettlementLayers(uint256)
    [0xe9, 0x42, 0x0f, 0x8c],
    -- forwardedBridgeMint(bytes32,uint256,(bytes32,uint256,address))
    [0xf2, 0x76, 0x71, 0x29],
    -- transferOwnership(address)
    [0xf2, 0xfd, 0xe3, 0x8b],
    -- admin()
    [0xf8, 0x51, 0xa4, 0x40],
    -- addChainTypeManager(address)
    [0xff, 0x5a, 0x62, 0xa1] ]

/-- The Bridgehub functions the model runs itself: the five that write its owner, nominee, admin
or pending admin, and `initialize`, which reverts on the initialized proxy. -/
def HUB_MODELLED_SELECTORS : List Bytes :=
  [SEL_TRANSFER_OWNERSHIP, SEL_ACCEPT_OWNERSHIP, SEL_RENOUNCE_OWNERSHIP, SEL_SET_PENDING_ADMIN,
    SEL_ACCEPT_ADMIN, SEL_INITIALIZE]

/-! ## The calldata of the setter's call -/

/-- `abi.encode` of one static word: 32 bytes, big-endian. -/
def word32 (x : ℕ) : Bytes := (List.range 32).reverse.map fun i => UInt8.ofNat (x / 256 ^ i)

/-- The calldata of `_chainContract.setTokenMultiplier(n, d)` (`ChainAdminOwnable.sol:69`):
selector `0x235d9eb5`, then `abi.encode(n, d)`. -/
def multiplierData (n d : ℕ) : Bytes := SEL_SET_MULTIPLIER ++ word32 n ++ word32 d

/-! ## Configuration -/

/-- ABI decoding of the argument tuples the modelled functions take; `none` is a decoding
revert. -/
structure Abi where
  /-- `(address)`. -/
  addr : Bytes → Option Address
  /-- `(Call[], bool)`. -/
  calls : Bytes → Option (List Call × Bool)
  /-- `(address, uint128, uint128)`. -/
  multiplierArgs : Bytes → Option (Address × ℕ × ℕ)

/-- Fixed configuration. -/
structure Config where
  /-- The `ChainAdminOwnable` (`address(this)`). -/
  cao : Address
  /-- The Bridgehub proxy. -/
  hub : Address
  /-- The admin of the Bridgehub's `TransparentUpgradeableProxy`. -/
  hubProxyAdmin : Address
  /-- The ZK chain diamonds. -/
  isChain : Address → Bool
  /-- Each diamond's `s.chainTypeManager`. -/
  ctmOf : Address → Address
  /-- ABI decoding. -/
  abi : Abi

/-- The `ChainAdminOwnable` is a deployed contract (so not the zero address), distinct from the
Bridgehub, and neither is a diamond. -/
def Config.WF (cfg : Config) : Prop :=
  cfg.cao ≠ 0 ∧ cfg.cao ≠ cfg.hub ∧ cfg.isChain cfg.cao = false ∧ cfg.isChain cfg.hub = false

/-! ## State -/

/-- `ChainAdminOwnable` storage: `Ownable._owner` (`OZ/access/Ownable.sol:21`),
`Ownable2Step._pendingOwner` (`OZ/access/Ownable2Step.sol:20`) and `tokenMultiplierSetter`
(`:20`). -/
structure CaoState where
  /-- `owner()`. -/
  owner : Address
  /-- `pendingOwner()`; zero for none. -/
  pending : Address
  /-- `tokenMultiplierSetter`. -/
  setter : Address
deriving DecidableEq

/-- The storage the constructor leaves (`ChainAdminOwnable.sol:22-30`): it reverts on a zero
owner. `Ownable`'s constructor first makes the deployer the owner (`OZ/access/Ownable.sol:28-30`);
the body then moves ownership to `o` through `_transferOwnership`, which deletes the nomination. -/
def construct (o σ : Address) : Option CaoState :=
  if o = 0 then none else some ⟨o, 0, σ⟩

/-- A diamond's `s.admin` and `s.pendingAdmin` (`chain-deps/ZKChainStorage.sol`). -/
structure AdminPair where
  /-- `s.admin`. -/
  admin : Address
  /-- `s.pendingAdmin`. -/
  pending : Address
deriving DecidableEq

/-- The Bridgehub's owner, nominee (`OZU`), `admin` and `pendingAdmin`
(`BridgehubBase.sol:82, 85`). -/
structure HubState where
  /-- `owner()`. -/
  owner : Address
  /-- `pendingOwner()`. -/
  pendingOwner : Address
  /-- `admin`. -/
  admin : Address
  /-- `pendingAdmin`. -/
  pendingAdmin : Address
deriving DecidableEq

/-- The modelled storage of the whole system. -/
structure State where
  /-- The `ChainAdminOwnable`. -/
  cao : CaoState
  /-- Every diamond's admin pair. -/
  chain : Address → AdminPair
  /-- The Bridgehub. -/
  hub : HubState

/-- Write the `ChainAdminOwnable`'s storage. -/
def State.setCao (S : State) (σ : CaoState) : State := { S with cao := σ }

/-- Write one diamond's admin pair. -/
def State.setChain (S : State) (d : Address) (p : AdminPair) : State :=
  { S with chain := fun x => if x = d then p else S.chain x }

/-- Write the Bridgehub's modelled storage. -/
def State.setHub (S : State) (h : HubState) : State := { S with hub := h }

/-! ## Shared entry points -/

/-- A call of an `Ownable2Step` function that writes. -/
inductive OwnOp where
  /-- `transferOwnership(x)`. -/
  | transfer (x : Address)
  /-- `acceptOwnership()`. -/
  | accept
  /-- `renounceOwnership()`. -/
  | renounce
deriving DecidableEq

/-- Selector dispatch for the three `Ownable2Step` writers; `none` when the selector is none of
them or the argument does not decode. A function without parameters ignores trailing calldata. -/
def decodeOwnOp (abi : Abi) (d : Bytes) : Option OwnOp :=
  if d.take 4 = SEL_TRANSFER_OWNERSHIP then (abi.addr (d.drop 4)).map OwnOp.transfer
  else if d.take 4 = SEL_ACCEPT_OWNERSHIP then some .accept
  else if d.take 4 = SEL_RENOUNCE_OWNERSHIP then some .renounce
  else none

/-- `(owner, pendingOwner)` after a successful `Ownable2Step` call by `sender`; `none` is a
revert. `transferOwnership` is `onlyOwner` and only nominates (`OZ/access/Ownable2Step.sol:35-38`;
`OZU/access/Ownable2StepUpgradeable.sol:42-45`); `acceptOwnership` needs the nominee
(`OZ`: `:52-56`; `OZU`: `:59-63`); `renounceOwnership` is `onlyOwner` and goes through the
overriding `_transferOwnership(address(0))`, which also deletes the nomination
(`OZ/access/Ownable.sol:61-63`, `OZ/access/Ownable2Step.sol:44-47`;
`OZU/access/OwnableUpgradeable.sol:66-68`, `OZU/access/Ownable2StepUpgradeable.sol:51-54`). -/
def ownStep (sender owner pending : Address) : OwnOp → Option (Address × Address)
  | .transfer x => if sender = owner then some (owner, x) else none
  | .accept => if sender = pending then some (sender, 0) else none
  | .renounce => if sender = owner then some (0, 0) else none

/-- The access check of an admin-gated diamond function with selector `sel`, called by `s` on a
diamond with admin pair `p` and chain type manager `ctm`: `onlyAdmin` (`ZKChainBase.sol:46-51`)
for `ADMIN_ONLY_SELECTORS`, `onlyAdminOrChainTypeManager` (`:120-125`) for
`ADMIN_OR_CTM_SELECTORS`. -/
def chainGate (sel : Bytes) (s : Address) (p : AdminPair) (ctm : Address) : Prop :=
  (sel ∈ ADMIN_ONLY_SELECTORS ∧ s = p.admin) ∨
    (sel ∈ ADMIN_OR_CTM_SELECTORS ∧ (s = p.admin ∨ s = ctm))

/-- A call of `setPendingAdmin(x)` or `acceptAdmin()`. -/
inductive AdminOp where
  /-- `setPendingAdmin(x)`. -/
  | setPending (x : Address)
  /-- `acceptAdmin()`. -/
  | accept
deriving DecidableEq

/-- Selector dispatch for `setPendingAdmin` and `acceptAdmin`. -/
def decodeAdminOp (abi : Abi) (d : Bytes) : Option AdminOp :=
  if d.take 4 = SEL_SET_PENDING_ADMIN then (abi.addr (d.drop 4)).map AdminOp.setPending
  else if d.take 4 = SEL_ACCEPT_ADMIN then some .accept
  else none

/-- A diamond's admin pair after a successful call by `sender`: `setPendingAdmin` is `onlyAdmin`
(`facets/Admin.sol:131-137`, `ZKChainBase.sol:46-51`); `acceptAdmin` needs the pending admin, makes
it the admin and deletes the nomination (`facets/Admin.sol:140-153`). -/
def chainAdminStep (sender : Address) (p : AdminPair) : AdminOp → Option AdminPair
  | .setPending x => if sender = p.admin then some { p with pending := x } else none
  | .accept => if sender = p.pending then some ⟨p.pending, 0⟩ else none

/-- The Bridgehub's state after a successful call by `sender`: `setPendingAdmin` is
`onlyOwnerOrAdmin` and rejects zero (`BridgehubBase.sol:139-144, 179-188`); `acceptAdmin` needs
the pending admin (`:191-204`). -/
def hubAdminStep (sender : Address) (h : HubState) : AdminOp → Option HubState
  | .setPending x =>
      if (sender = h.admin ∨ sender = h.owner) ∧ x ≠ 0 then some { h with pendingAdmin := x }
      else none
  | .accept =>
      if sender = h.pendingAdmin then some { h with admin := h.pendingAdmin, pendingAdmin := 0 }
      else none

/-! ## The ghost log -/

/-- The frame a call made by the `ChainAdminOwnable` comes from. -/
inductive Origin where
  /-- Iteration `i` of `multicall(calls, _)` (`:48-58`), entered with `msg.sender = invoker`
  when the `ChainAdminOwnable`'s storage was `pre`. -/
  | multicall (invoker : Address) (pre : CaoState) (calls : List Call) (i : ℕ)
  /-- `setTokenMultiplier(chain, n, d)` (`:65-70`), entered with `msg.sender = invoker` when
  the storage was `pre`. -/
  | multiplier (invoker : Address) (pre : CaoState) (chain : Address) (n d : ℕ)
deriving DecidableEq

/-- A write to the `ChainAdminOwnable`'s storage. -/
inductive CaoWrite where
  /-- An `Ownable2Step` writer. -/
  | own (op : OwnOp)
  /-- `setTokenMultiplierSetter(x)`. -/
  | setSetter (x : Address)
deriving DecidableEq

/-- A ghost-log entry. -/
inductive Event where
  /-- The `ChainAdminOwnable` made call `c`, from `origin`, with low-level result `ok`. -/
  | caoCall (origin : Origin) (c : Call) (ok : Bool)
  /-- `invoker` called a writer of the `ChainAdminOwnable` (`w`) and it committed; `pre` is
  the storage it ran on. -/
  | caoWrite (invoker : Address) (pre : CaoState) (w : CaoWrite)
  /-- `sender` called diamond `chain` with selector `selector`, and the call committed. -/
  | chainEntry (chain sender : Address) (selector : Bytes)
  /-- A cut of diamond `chain` ran. -/
  | cut (chain : Address)
  /-- `sender` called the Bridgehub with selector `selector`, and the call committed. -/
  | hubEntry (sender : Address) (selector : Bytes)
deriving DecidableEq

/-! ## Execution -/

/-- What a `Sem` derivation describes. -/
inductive Judgement where
  /-- `sender` makes call `c`; `ok` is the low-level success flag. -/
  | call (sender : Address) (c : Call) (ok : Bool)
  /-- Iterations `i, i+1, ...` of a `multicall(calls, requireSuccess)` entered by `invoker` when
  the `ChainAdminOwnable`'s storage was `pre`. -/
  | loop (invoker : Address) (pre : CaoState) (requireSuccess : Bool) (calls : List Call) (i : ℕ)
  /-- Unknown code holding control. -/
  | acts

/-- **The execution relation.** `Sem cfg j S L S'`: judgement `j` takes `S` to `S'` and leaves
the ghost log `L`. A revert is the absence of a derivation. -/
inductive Sem (cfg : Config) : Judgement → State → List Event → State → Prop
  /-- Any call may fail, with no effect and nothing logged. -/
  | callFails {s : Address} {c : Call} {S : State} : Sem cfg (.call s c false) S [] S
  /-- `receive()` (`:73`): empty calldata, any value. -/
  | caoReceive {s : Address} {c : Call} {S : State} :
      c.target = cfg.cao → c.data = [] → Sem cfg (.call s c true) S [] S
  /-- `owner()`, `pendingOwner()`, `tokenMultiplierSetter()`: non-payable views. -/
  | caoView {s : Address} {c : Call} {S : State} :
      c.target = cfg.cao → c.value = 0 → c.data.take 4 ∈ CAO_VIEW_SELECTORS →
      Sem cfg (.call s c true) S [] S
  /-- `transferOwnership`, `acceptOwnership`, `renounceOwnership`: non-payable, `ownStep`. -/
  | caoOwn {s : Address} {c : Call} {S : State} {op : OwnOp} {o p : Address} :
      c.target = cfg.cao → c.value = 0 → decodeOwnOp cfg.abi c.data = some op →
      ownStep s S.cao.owner S.cao.pending op = some (o, p) →
      Sem cfg (.call s c true) S [.caoWrite s S.cao (.own op)]
        (S.setCao { S.cao with owner := o, pending := p })
  /-- `setTokenMultiplierSetter(x)` (`:34-37`): non-payable, `onlyOwner`. -/
  | caoSetSetter {s : Address} {c : Call} {S : State} {x : Address} :
      c.target = cfg.cao → c.value = 0 → c.data.take 4 = SEL_SET_SETTER →
      cfg.abi.addr (c.data.drop 4) = some x → s = S.cao.owner →
      Sem cfg (.call s c true) S [.caoWrite s S.cao (.setSetter x)]
        (S.setCao { S.cao with setter := x })
  /-- `multicall(cs, rs)` (`:43-59`): payable, `onlyOwner`, at least one call, then the loop,
  which starts from the storage the check read. -/
  | caoMulticall {s : Address} {c : Call} {S S' : State} {L : List Event} {cs : List Call}
      {rs : Bool} :
      c.target = cfg.cao → c.data.take 4 = SEL_MULTICALL →
      cfg.abi.calls (c.data.drop 4) = some (cs, rs) → s = S.cao.owner → cs ≠ [] →
      Sem cfg (.loop s S.cao rs cs 0) S L S' → Sem cfg (.call s c true) S L S'
  /-- `setTokenMultiplier(t, n, d)` (`:65-70`): non-payable; the caller is the setter; the call
  `t.setTokenMultiplier(n, d)` with value zero must succeed. -/
  | caoSetMultiplier {s : Address} {c : Call} {S S' : State} {L : List Event} {t : Address}
      {n d : ℕ} :
      c.target = cfg.cao → c.value = 0 → c.data.take 4 = SEL_SET_MULTIPLIER_VIA →
      cfg.abi.multiplierArgs (c.data.drop 4) = some (t, n, d) → s = S.cao.setter →
      Sem cfg (.call cfg.cao ⟨t, 0, multiplierData n d⟩ true) S L S' →
      Sem cfg (.call s c true) S
        (L ++ [.caoCall (.multiplier s S.cao t n d) ⟨t, 0, multiplierData n d⟩ true]) S'
  /-- A diamond's `setPendingAdmin` / `acceptAdmin`: non-payable, `chainAdminStep`. -/
  | chainAdmin {s : Address} {c : Call} {S : State} {op : AdminOp} {p : AdminPair} :
      cfg.isChain c.target = true → c.value = 0 → decodeAdminOp cfg.abi c.data = some op →
      chainAdminStep s (S.chain c.target) op = some p →
      Sem cfg (.call s c true) S [.chainEntry c.target s (c.data.take 4)]
        (S.setChain c.target p)
  /-- An admin-gated diamond function, among them `setTokenMultiplier(n, d)`
  (`facets/Admin.sol:267-295`): non-payable, its access check (`chainGate`), then unknown code.
  Its other checks and its writes are not modelled. -/
  | chainGated {s : Address} {c : Call} {S S' : State} {L : List Event} :
      cfg.isChain c.target = true → c.value = 0 →
      chainGate (c.data.take 4) s (S.chain c.target) (cfg.ctmOf c.target) →
      Sem cfg .acts S L S' →
      Sem cfg (.call s c true) S (.chainEntry c.target s (c.data.take 4) :: L) S'
  /-- A cut (`facets/Admin.sol:559-609`): `executeUpgrade` and `genesisUpgrade` need the chain
  type manager; `upgradeChainFromVersion` is open to any sender here. The cut leaves the admin
  pair arbitrary (`p`) and then runs unknown code. -/
  | chainCut {s : Address} {c : Call} {S S' : State} {L : List Event} {p : AdminPair} :
      cfg.isChain c.target = true → c.data.take 4 ∈ CUT_SELECTORS →
      (c.data.take 4 = SEL_UPGRADE_CHAIN_FROM_VERSION ∨ s = cfg.ctmOf c.target) →
      Sem cfg .acts (S.setChain c.target p) L S' →
      Sem cfg (.call s c true) S (.chainEntry c.target s (c.data.take 4) :: .cut c.target :: L) S'
  /-- Any other diamond function: unknown code, no access check. -/
  | chainOther {s : Address} {c : Call} {S S' : State} {L : List Event} :
      cfg.isChain c.target = true → c.data.take 4 ∉ CHAIN_MODELLED_SELECTORS →
      Sem cfg .acts S L S' →
      Sem cfg (.call s c true) S (.chainEntry c.target s (c.data.take 4) :: L) S'
  /-- The Bridgehub's `Ownable2Step` writers, through the proxy: non-payable, `ownStep`. -/
  | hubOwn {s : Address} {c : Call} {S : State} {op : OwnOp} {o p : Address} :
      c.target = cfg.hub → s ≠ cfg.hubProxyAdmin → c.value = 0 →
      decodeOwnOp cfg.abi c.data = some op →
      ownStep s S.hub.owner S.hub.pendingOwner op = some (o, p) →
      Sem cfg (.call s c true) S [.hubEntry s (c.data.take 4)]
        (S.setHub { S.hub with owner := o, pendingOwner := p })
  /-- The Bridgehub's `setPendingAdmin` / `acceptAdmin`: non-payable, `hubAdminStep`. -/
  | hubAdmin {s : Address} {c : Call} {S : State} {op : AdminOp} {h : HubState} :
      c.target = cfg.hub → s ≠ cfg.hubProxyAdmin → c.value = 0 →
      decodeAdminOp cfg.abi c.data = some op → hubAdminStep s S.hub op = some h →
      Sem cfg (.call s c true) S [.hubEntry s (c.data.take 4)] (S.setHub h)
  /-- Any other function of `L1Bridgehub`: unknown code that leaves the four modelled slots to
  the two rules above. A selector outside `BRIDGEHUB_SELECTORS` has no rule: no `fallback`. -/
  | hubOther {s : Address} {c : Call} {S S' : State} {L : List Event} :
      c.target = cfg.hub → s ≠ cfg.hubProxyAdmin → c.data.take 4 ∈ BRIDGEHUB_SELECTORS →
      c.data.take 4 ∉ HUB_MODELLED_SELECTORS → Sem cfg .acts S L S' →
      Sem cfg (.call s c true) S (.hubEntry s (c.data.take 4) :: L) S'
  /-- A call to any other address: unknown code (or none). -/
  | external {s : Address} {c : Call} {S S' : State} {L : List Event} :
      c.target ≠ cfg.cao → c.target ≠ cfg.hub → cfg.isChain c.target = false →
      Sem cfg .acts S L S' → Sem cfg (.call s c true) S L S'
  /-- The loop is done. -/
  | loopDone {inv : Address} {pre : CaoState} {rs : Bool} {cs : List Call} {i : ℕ} {S : State} :
      cs.length ≤ i → Sem cfg (.loop inv pre rs cs i) S [] S
  /-- One iteration (`:48-58`): the `ChainAdminOwnable` makes call `i`; with `requireSuccess` a
  failure reverts the whole `multicall`; the result is logged. -/
  | loopStep {inv : Address} {pre : CaoState} {rs ok : Bool} {cs : List Call} {i : ℕ} {c : Call}
      {S S1 S2 : State} {L1 L2 : List Event} :
      cs[i]? = some c → Sem cfg (.call cfg.cao c ok) S L1 S1 → (rs = true → ok = true) →
      Sem cfg (.loop inv pre rs cs (i + 1)) S1 L2 S2 →
      Sem cfg (.loop inv pre rs cs i) S (L1 ++ .caoCall (.multicall inv pre cs i) c ok :: L2) S2
  /-- Unknown code that makes no further call. -/
  | actsNil {S : State} : Sem cfg .acts S [] S
  /-- Unknown code makes a call, as any address other than the `ChainAdminOwnable` and zero. -/
  | actsCall {s : Address} {c : Call} {ok : Bool} {S S1 S2 : State} {L1 L2 : List Event} :
      s ≠ cfg.cao → s ≠ 0 → Sem cfg (.call s c ok) S L1 S1 → Sem cfg .acts S1 L2 S2 →
      Sem cfg .acts S (L1 ++ L2) S2

/-! ## Predicates the properties use -/

/-- The call `c` from `origin` is what that frame is allowed to make: a `multicall` iteration
whose `msg.sender` was the owner when the `multicall` was entered makes exactly element `i` of the
submitted list; a `setTokenMultiplier` whose `msg.sender` was the setter of that moment makes
exactly `chain.setTokenMultiplier(n, d)` with value zero. -/
def Origin.Authorized : Origin → Call → Prop
  | .multicall inv pre cs i, c => inv = pre.owner ∧ cs[i]? = some c
  | .multiplier inv pre t n d, c => inv = pre.setter ∧ c = ⟨t, 0, multiplierData n d⟩

/-- The access check a logged write passed: `acceptOwnership` by the nominee, every other writer
by the owner, both read from the storage the write ran on. -/
def CaoWrite.Guard (inv : Address) (pre : CaoState) : CaoWrite → Prop
  | .own .accept => inv = pre.pending
  | .own (.transfer _) => inv = pre.owner
  | .own .renounce => inv = pre.owner
  | .setSetter _ => inv = pre.owner

/-! ## Witness configuration

Addresses: the `ChainAdminOwnable` `1`, the Bridgehub `2`, its proxy admin `3`, one diamond `4`
whose chain type manager is `5`, the owner `6`, the setter `7`, and further actors `8`-`13`.
Arguments are encoded as 32-byte words (`word32`), and the witness decoder reads them back as big-
endian words. For `(Call[], bool)` the witness decoder maps the one-byte strings `[1]`, `[2]` and
`[3]` to the three lists below: the model's decoder is a parameter, and every result holds for
every decoder. -/

/-- The big-endian value of a byte string. -/
def wordOf (b : Bytes) : ℕ := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- Calldata `selector ++ abi.encode(x)` for one static argument. -/
def withWord (sel : Bytes) (x : ℕ) : Bytes := sel ++ word32 x

/-- The first witness `multicall`: set the diamond's pending admin to `8`, and the Bridgehub's. -/
def wCallsA : List Call :=
  [⟨4, 0, withWord SEL_SET_PENDING_ADMIN 8⟩, ⟨2, 0, withWord SEL_SET_PENDING_ADMIN 8⟩]

/-- The second witness `multicall`: call the owner `6` (empty calldata), then set the diamond's
pending admin to `12`. -/
def wCallsB : List Call := [⟨6, 0, []⟩, ⟨4, 0, withWord SEL_SET_PENDING_ADMIN 12⟩]

/-- The third witness `multicall`: set the diamond's transaction filterer to `13`, an `onlyAdmin`
function. -/
def wCallsC : List Call := [⟨4, 0, withWord SEL_SET_TRANSACTION_FILTERER 13⟩]

/-- The witness decoder. -/
def wAbi : Abi where
  addr b := some (wordOf b : Address)
  calls b :=
    if b = [1] then some (wCallsA, true) else if b = [2] then some (wCallsB, true)
    else if b = [3] then some (wCallsC, true) else none
  multiplierArgs b :=
    some ((wordOf (b.take 32) : Address), wordOf ((b.drop 32).take 32), wordOf (b.drop 64))

/-- The witness configuration. -/
def wCfg : Config where
  cao := 1
  hub := 2
  hubProxyAdmin := 3
  isChain a := decide (a = 4)
  ctmOf _ := 5
  abi := wAbi

/-- Calldata of `ChainAdminOwnable.setTokenMultiplier(t, n, d)`. -/
def viaData (t n d : ℕ) : Bytes := SEL_SET_MULTIPLIER_VIA ++ word32 t ++ word32 n ++ word32 d

/-- The start state: the `ChainAdminOwnable` as its constructor leaves it for owner `6` and setter
zero (`construct 6 0`, the arguments `DeployL1CoreUtils.s.sol:117-118` passes, with `6` as the
configured owner); it is the admin of diamond `4` and of the Bridgehub, whose owner is `9`. -/
def wS0 : State where
  cao := ⟨6, 0, 0⟩
  chain a := if a = 4 then ⟨1, 0⟩ else ⟨0, 0⟩
  hub := ⟨9, 0, 1, 0⟩

/-- After the owner set the setter to `7`. -/
def wS1 : State := wS0.setCao ⟨6, 0, 7⟩

/-- After the owner then renounced: owner and nominee zero, setter `7`. -/
def wRenounced : State := wS0.setCao ⟨0, 0, 7⟩

end Contracts.ChainAdminOwnable
