import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: the second-proof-system requirement across a settlement-layer migration (draft/v0.35.0)

Source: era-contracts `draft/v0.35.0` at commit `d9f678900e1bc8286412b78f56d4a9f443983c29`.
Paths are relative to `l1-contracts/contracts/`; `protocol-docs/` is at the repository root.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.SecondProofSystem.Properties.MigrationV35` and are proved in
`EraSpec.Contracts.SecondProofSystem.Proofs.MigrationV35`.

## What is modelled

One chain and its **two diamonds**: the one on L1 (`Sys.l1`, what `Bridgehub.getZKChain(chainId)`
returns on L1) and the one on a gateway (`Sys.gw`, `none` until the chain first arrives there).
Each diamond is projected onto the `ZKChainStorage` fields the requirement reads or writes
(`state-transition/chain-deps/ZKChainStorage.sol`): `verifier` (`:89`), `admin` (`:166`),
`pendingAdmin` (`:169`), `settlementLayer` (`:218`), `isPermanentRollup` (`:225`),
`disabledProofSystems` (`:290`) and `secondProofSystemRequired` (`:304`).

A diamond accepts the chain's batches only while its `settlementLayer` is `address(0)`:
commit, prove and execute are `onlySettlementLayer`
(`state-transition/chain-deps/facets/Committer.sol:77`, `Executor.sol:175, 220`;
`ZKChainBase.sol:141-146`). The proof format it then accepts is
`s.verifier.getProofMode(s.disabledProofSystems)` of **that** diamond (`ZKChainBase.sol:187-190`).

### The requirement, per diamond (`DCall`, `dstep`)

* `Admin.setProofSystemStatus` (`state-transition/chain-deps/facets/Admin.sol:416-432`), the only
  write of the mask:

        address authorized = !_enabled && s.secondProofSystemRequired
            ? IOwnable(s.bridgehub).owner() : s.admin;                         // :417
        if (msg.sender != authorized) revert Unauthorized(msg.sender);        // :418-420
        if (_proofSystem != ProofSystem.Zisk) revert InvalidProofSystem(..);  // :421-423
        s.disabledProofSystems = _enabled ? old & ~mask : old | mask;         // :425-430

  It carries no `onlySettlementLayer`. `s.bridgehub` is the Bridgehub of the layer the diamond
  lives on, so each layer has its own owner (`Sys.l1BridgehubOwner`, `Sys.gwBridgehubOwner`).
* `Admin.permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`), `onlyAdmin`
  (`ZKChainBase.sol:46-51`) and `onlySettlementLayer`, the only write of the flag in the tree
  (`grep secondProofSystemRequired`: `Admin.sol:121, 417, 455, 463`, `Getters.sol:115`,
  `BaseZkSyncUpgrade.sol:143`, `ZKChainStorage.sol:304`), and only to `true`:

        if (s.secondProofSystemRequired) revert SecondProofSystemAlreadyRequired(); // :455-457
        uint256 proofMode = _getProofMode();                                      // :458
        if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) revert ..;      // :459-461
        s.secondProofSystemRequired = true;                                       // :463

* `Admin.makePermanentRollup` (`Admin.sol:435-451`), `onlyAdmin onlySettlementLayer`, the only
  write of `isPermanentRollup` outside the migration (`:450`). Its pubdata and DA-pair checks
  (`:441-448`) are omitted.
* A genuine upgrade (`DCall.upgrade`): the engine's `BaseZkSyncUpgrade._setVerifier`
  (`upgrades/BaseZkSyncUpgrade.sol:133-153`, reached only for a nonzero verifier, `:97-99`):

        if (_newVerifier == IVerifier(address(0))) revert ZeroAddress();          // :139-141
        if (s.secondProofSystemRequired) {                                        // :143
            uint256 proofMode = IZKsyncOSVerifier(address(_newVerifier)).getProofMode(0); // :144
            if (proofMode != ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE) revert ..;  // :145-147
        }
        s.verifier = _newVerifier;                                                // :151

  followed by the re-check of `AdminFacet._executeDiamondCut` (`Admin.sol:117-129`, `:121-126`).
  Its callers and timing checks are omitted (`Admin.sol:559-595`).
* A break-glass cut (`DCall.breakGlassCut`): `ChainTypeManager.executeUpgrade`
  (`state-transition/ChainTypeManager.sol:626-628`, `onlyOwner`) with any other init, as a
  function of the projected storage, followed by the same re-check.
* `setPendingAdmin` / `acceptAdmin` (`Admin.sol:131-153`).

### The migration (`Call`, `step`)

The chain asset handler is the only caller of the diamond's and the CTM's migration entry points
(`onlyChainAssetHandler`, `ZKChainBase.sol:113-118`, `ChainTypeManager.sol:724, 749`). Its
`bridgeBurn` and `bridgeMint` carry `whenMigrationsEnabled`
(`core/chain-asset-handler/ChainAssetHandlerBase.sol:201, 365`):

    modifier whenMigrationsEnabled() {
        if (!_getChainMigrationsEnabled()) { revert ChainMigrationsDisabled(); }   // :151-156
    function _getChainMigrationsEnabled() internal view virtual returns (bool) {
        return CHAIN_MIGRATIONS_ENABLED;                                         // :165-167
    bool constant CHAIN_MIGRATIONS_ENABLED = false;                              // common/Config.sol:320

`Cfg.migrationsEnabled` is the value `_getChainMigrationsEnabled()` returns; `false` is the
source at `d9f6789`. Only the dev variants override it (`dev-contracts/L1ChainAssetHandlerDev.sol:37`,
`L2ChainAssetHandlerDev.sol:11`).

**Leaving** (`Call.bridgeBurnToGateway`, `Call.bridgeBurnToL1`):
`ChainAssetHandlerBase.bridgeBurn` (`:188-254`) → `Migrator.forwardedBridgeBurn`
(`state-transition/chain-deps/facets/Migrator.sol:154-209`):

    if (_originalCaller != IZKChain(zkChain).getAdmin()) revert IncorrectSender(..); // CAH :225-227
    if (s.settlementLayer != address(0)) revert AlreadyMigrated();                // Migrator :162-164
    if (_originalCaller != s.admin) revert NotChainAdmin(..);                     // :165-167
    if (s.totalBatchesCommitted != s.totalBatchesExecuted) revert NotAllBatchesExecuted(); // :203-205
    s.settlementLayer = _settlementLayer;                                         // :207
    chainBridgeMintData = abi.encode(prepareChainCommitment());                   // :208

`_settlementLayer` is the destination's diamond address on this layer, or
`L1_SETTLEMENT_LAYER_VIRTUAL_ADDRESS` (`ChainAssetHandlerBase.sol:267-273`,
`common/Config.sol:222-224`, `Cfg.l1VirtualAddress`). `ChainTypeManager.forwardedBridgeBurn`
(`ChainTypeManager.sol:721-741`) forwards the new admin and refuses `address(0)` (`:729-731`).

**The commitment** (`Commitment`, `prepareChainCommitment`): `ZKChainCommitment`
(`common/Config.sol:234-261`) has nine fields, transcribed in order. `prepareChainCommitment`
(`Migrator.sol:339-375`) fills them:

    commitment.totalBatchesCommitted = s.totalBatchesCommitted;                   // :340
    commitment.totalBatchesVerified = s.totalBatchesVerified;                     // :341
    commitment.totalBatchesExecuted = s.totalBatchesExecuted;                     // :342
    commitment.l2SystemContractsUpgradeBatchNumber = s.l2SystemContractsUpgradeBatchNumber; // :343
    commitment.l2SystemContractsUpgradeTxHash = s.l2SystemContractsUpgradeTxHash; // :344
    commitment.priorityTree = s.priorityTree.getCommitment();                     // :345
    commitment.isPermanentRollup = s.isPermanentRollup;                           // :346
    commitment.precommitmentForTheLatestBatch = bytes32(0);                       // :348
    ...  batchHashes[i] = s.storedBatchHashes[commitment.totalBatchesExecuted + i]; // :364-374

Of the projected storage it reads `isPermanentRollup` and nothing else. The other seven values
come from storage outside the projection; the model takes them as the step's `payload` argument
and overwrites fields 8 and 9. **There is no field for `secondProofSystemRequired` or for
`disabledProofSystems`.**

**Arriving** (`Call.bridgeMintOnGateway`, `Call.bridgeMintOnL1`):
`ChainAssetHandlerBase.bridgeMint` (`:361-420`):

    (address zkChain, address ctm) = IBridgehubBase(_getBridgehub()).forwardedBridgeMint(..); // :391-395
    bool contractAlreadyDeployed = zkChain != address(0);                         // :397
    if (!contractAlreadyDeployed) {
        zkChain = IChainTypeManager(ctm).forwardedBridgeMint(chainId, ctmData);   // :399
        ...
    IZKChain(zkChain).forwardedBridgeMint(bridgehubMintData.chainData, contractAlreadyDeployed); // :417

`ChainTypeManager.forwardedBridgeMint` (`ChainTypeManager.sol:746-758`) calls `_deployNewChain`
(`:674-692`), a new `DiamondProxy` whose init is `DiamondInit.initialize(chainId, admin)`
(`state-transition/chain-deps/DiamondInit.sol:52-150`). It writes `s.verifier` from the
destination CTM's current release (`:114-118`, `Cfg.gwVerifier`) and `s.admin = _admin` (`:119`),
and writes neither `secondProofSystemRequired`, `disabledProofSystems`, `isPermanentRollup` nor
`settlementLayer`, which keep the default `false` / `0` of fresh storage (`freshDiamond`).

`Migrator.forwardedBridgeMint` (`Migrator.sol:213-305`, `forwardedBridgeMint`):

    if (s.isPermanentRollup && !_commitment.isPermanentRollup) revert RemovingPermanentRestriction(); // :234-236
    s.isPermanentRollup = _commitment.isPermanentRollup;                          // :241
    if (batchesExecuted > batchesVerified) revert ..;                             // :247-249
    if (batchesVerified > batchesCommitted) revert ..;                            // :250-252
    if (_commitment.batchHashes.length != batchesCommitted - batchesExecuted + 1) revert ..; // :257-259
    if (s.settlementLayer == address(0)) revert NotMigrated();    // :280-282 (L1), :285-287 (deployed)
    s.settlementLayer = address(0);                                               // :299

It writes neither the flag nor the mask.

**A failed departure** (`Call.bridgeConfirmFailure`):
`L1ChainAssetHandler.bridgeConfirmTransferResult` (`core/chain-asset-handler/L1ChainAssetHandler.sol:122-172`),
which is **not** gated by `whenMigrationsEnabled` (`:119-120`), reaches
`Migrator.forwardedBridgeConfirmTransferResult` (`Migrator.sol:309-333`): on failure it requires
`s.settlementLayer != address(0)` (`:324-326`) and clears it (`:332`). The successful
confirmation writes nothing projected.

### Enabling interop (`Call.enableInterop`)

`L1MessageRoot.enableInterop` (`core/message-root/L1MessageRoot.sol:72-89`):

    require(msg.sender == IOwnable(BRIDGE_HUB).owner(), Unauthorized(msg.sender)); // :73
    address zkChain = IBridgehubBase(BRIDGE_HUB).getZKChain(_chainId);            // :74
    require(!interopEnabled[_chainId], InteropAlreadyEnabled(_chainId));          // :76
    if (_requireSecondProofSystem) {                                              // :81
        require(IGetters(zkChain).isSecondProofSystemRequired(), ..);             // :82
        uint256 proofMode = IGetters(zkChain).getProofMode();                     // :83
        require(proofMode == ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE, ..);        // :84
    }
    interopEnabled[_chainId] = true;                                              // :87

`zkChain` is the chain's diamond **on L1**. Nothing clears `interopEnabled`.

## In flight

A burn's mint data reaches the destination's `bridgeMint` through the asset routers (an L1→L2
priority transaction, or a proven L2→L1 message). The model keeps burned-but-unminted
migrations in `Sys.inFlight`; a mint or a failed-departure confirmation consumes one. It has no
step that mints with data no burn produced. That is an assumption on the transport
(`MODEL-SECOND-PROOF-MIGRATION` in `ASSUMPTIONS.md`), and it only matters for the positive
run-level results.

## The hypothetical repair

`Cfg.repaired = true` is **not the source**. It is the same system with one change, used only
by `RepairedCommitmentKeepsRequirement`: the commitment gets a tenth field
`secondProofSystemRequired` (`RepairedCommitment`), filled from storage like `:346`, and the
mint guards and writes it like `:234-235` and `:241` (`repairedForwardedBridgeMint`).
With `Cfg.repaired = false` the tenth field is recorded but never read (`mintWith`).

## Not modelled

* Reject-only checks on the migration path that read no projected field: the settlement-layer
  whitelist and the Bridgehub's bookkeeping (`core/bridgehub/BridgehubBase.sol:403-453`), the
  runtime pauses (`ChainAssetHandlerBase.sol:200, 204, 468-473`), the same-CTM rule
  (`:231-237`, `Migrator.sol:181-189`), the migration counter
  (`ChainAssetHandlerBase.sol:274-279, 372-384`; `MAX_ALLOWED_NUMBER_OF_MIGRATIONS = 2`,
  `common/Config.sol:329`), priority mode (`Migrator.sol:159-161`), the empty priority tree
  (`:170`), the paused-deposit window (`:172-176`, `:217-219`), the protocol-version equalities
  (`:192-198`, `:225-229`, `ChainTypeManager.sol:735-738, 754-756`), and the priority-tree
  re-initialisation (`Migrator.sol:268-292`). None of them reads the flag, the mask or the
  verifier. Omitting them only adds runs. The witness runs in
  `Properties.MigrationV35` assume they can be met.
* `enableInterop`'s registration and backfill checks (`L1MessageRoot.sol:75, 80`), omitted.
* The ZKsync OS marker. Every chain of this tree is a ZKsync OS chain
  (`ChainTypeManager.isZKsyncOS()` is `true`, `ChainTypeManager.sol:242-244`;
  `DiamondInit.sol:139` sets `s.zksyncOS = true`), and nothing on the migration path reads it.
* Facet cuts are taken to leave the entry points as they are at `d9f6789`; other installed code
  is covered only by `DCall.breakGlassCut`.
* More than one gateway, and the rest of both diamonds' storage.
-/

namespace Contracts.SecondProofSystem.MigrationV35

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- `enum ProofSystem { Boojum, Airbender, Zisk }` (`common/Config.sol:126-130`). -/
inductive ProofSystem
  | boojum
  | airbender
  | zisk
  deriving DecidableEq, Repr

/-- `uint8(_proofSystem)`. -/
def ProofSystem.toUInt8 : ProofSystem → UInt8
  | .boojum => 0
  | .airbender => 1
  | .zisk => 2

/-- `uint8(1 << uint8(_proofSystem))` (`Admin.sol:425`). -/
def ProofSystem.bit (p : ProofSystem) : UInt8 := (1 : UInt8) <<< p.toUInt8

/-- The ZiSK bit of the mask. -/
abbrev ziskBit : UInt8 := ProofSystem.zisk.bit

/-- `ZKSYNC_OS_PLONK_VERIFICATION_TYPE` (`common/Config.sol:105`). -/
def PLONK_TYPE : ℕ := 2

/-- `ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE` (`common/Config.sol:108`). -/
def MULTI_PROOF_TYPE : ℕ := 5

/-- The verifier code: `proofMode v m` is the result of `getProofMode(m)` on the verifier at
`v`; `none` is a revert. -/
structure Env where
  proofMode : Address → UInt8 → Option ℕ

/-- The projected `ZKChainStorage` of one diamond. -/
structure Diamond where
  admin : Address
  pendingAdmin : Address
  /-- `address(0)`: this diamond is the chain's settlement layer and accepts its batches. -/
  settlementLayer : Address
  verifier : Address
  isPermanentRollup : Bool
  secondProofSystemRequired : Bool
  disabledProofSystems : UInt8
  deriving DecidableEq, Repr

/-- The diamond accepts the chain's batches (`onlySettlementLayer`, `ZKChainBase.sol:141-146`). -/
def Diamond.accepts (d : Diamond) : Prop := d.settlementLayer = 0

instance (d : Diamond) : Decidable d.accepts := by unfold Diamond.accepts; infer_instance

/-- `Getters.disabledProofSystems().zisk` (`Getters.sol:119-126`): the ZiSK bit is set. -/
def ziskOff (d : Diamond) : Prop := d.disabledProofSystems &&& ziskBit ≠ 0

instance (d : Diamond) : Decidable (ziskOff d) := by unfold ziskOff; infer_instance

/-! ## The commitment -/

/-- `PriorityTreeCommitment` (`common/Config.sol:226-231`). -/
structure PriorityTreeCommitment where
  nextLeafIndex : UInt256
  startIndex : UInt256
  unprocessedIndex : UInt256
  sides : List UInt256
  deriving DecidableEq, Repr

/-- `ZKChainCommitment` (`common/Config.sol:234-261`): its nine fields, in order. Counters are
`ℕ`. -/
structure Commitment where
  totalBatchesExecuted : ℕ
  totalBatchesVerified : ℕ
  totalBatchesCommitted : ℕ
  l2SystemContractsUpgradeTxHash : UInt256
  l2SystemContractsUpgradeBatchNumber : ℕ
  batchHashes : List UInt256
  priorityTree : PriorityTreeCommitment
  isPermanentRollup : Bool
  precommitmentForTheLatestBatch : UInt256
  deriving DecidableEq, Repr

/-- **Not the source.** The commitment of the hypothetical repair: the nine source fields and
the flag. With `Cfg.repaired = false` the extra field is a record the model keeps and no code
reads. -/
structure RepairedCommitment extends Commitment where
  secondProofSystemRequired : Bool
  deriving DecidableEq, Repr

/-- `Migrator.prepareChainCommitment` (`Migrator.sol:339-375`). `payload` stands for the seven
values read from storage outside the projection (`:340-345`, `:364-374`); the order checks are
`:351-362`, and the batch-hash array has `committed - executed + 1` entries by construction
(`:364-366`). -/
def prepareChainCommitment (payload : Commitment) (d : Diamond) : Option Commitment :=
  if payload.totalBatchesExecuted > payload.totalBatchesVerified then none
  else if payload.totalBatchesVerified > payload.totalBatchesCommitted then none
  else if payload.batchHashes.length ≠
      payload.totalBatchesCommitted - payload.totalBatchesExecuted + 1 then none
  else some { payload with
    isPermanentRollup := d.isPermanentRollup,               -- :346
    precommitmentForTheLatestBatch := 0 }                   -- :348

/-- `Migrator.forwardedBridgeMint` (`Migrator.sol:213-305`) on the projection, without the
`NotMigrated` checks (`:280-282`, `:285-287`), which `step` applies. -/
def forwardedBridgeMint (c : Commitment) (d : Diamond) : Option Diamond :=
  if d.isPermanentRollup = true ∧ c.isPermanentRollup = false then none          -- :234-236
  else if c.totalBatchesExecuted > c.totalBatchesVerified then none            -- :247-249
  else if c.totalBatchesVerified > c.totalBatchesCommitted then none           -- :250-252
  else if c.batchHashes.length ≠ c.totalBatchesCommitted - c.totalBatchesExecuted + 1 then
    none                                                                       -- :257-259
  else some { d with
    isPermanentRollup := c.isPermanentRollup,                                  -- :241
    settlementLayer := 0 }                                                     -- :299

/-- **Not the source.** The repaired mint: the flag guarded like `:234-236` and written like
`:241`. -/
def repairedForwardedBridgeMint (c : RepairedCommitment) (d : Diamond) : Option Diamond :=
  if d.secondProofSystemRequired = true ∧ c.secondProofSystemRequired = false then none
  else (forwardedBridgeMint c.toCommitment d).map fun d' =>
    { d' with secondProofSystemRequired := c.secondProofSystemRequired }

/-! ## One diamond -/

/-- The calls on one diamond that touch the projection. -/
inductive DCall
  /-- `Admin.setPendingAdmin` (`Admin.sol:131-137`). -/
  | setPendingAdmin (a : Address)
  /-- `Admin.acceptAdmin` (`Admin.sol:140-153`). -/
  | acceptAdmin
  /-- `Admin.setProofSystemStatus` (`Admin.sol:416-432`). -/
  | setProofSystemStatus (p : ProofSystem) (enabled : Bool)
  /-- `Admin.permanentlyRequireSecondProofSystem` (`Admin.sol:454-465`). -/
  | permanentlyRequireSecondProofSystem
  /-- `Admin.makePermanentRollup` (`Admin.sol:435-451`). -/
  | makePermanentRollup
  /-- A genuine upgrade; `none` installs no verifier (`BaseZkSyncUpgrade.sol:97`). -/
  | upgrade (newVerifier : Option Address)
  /-- A cut whose init is not the genuine engine, as a function of the projected storage. -/
  | breakGlassCut (f : Diamond → Option Diamond)

/-- The mask `setProofSystemStatus` writes (`Admin.sol:425-430`). -/
def newMask (old : UInt8) (p : ProofSystem) (enabled : Bool) : UInt8 :=
  if enabled = true then old &&& ~~~p.bit else old ||| p.bit

/-- The caller `setProofSystemStatus` admits (`Admin.sol:417`); `owner` is
`IOwnable(s.bridgehub).owner()`. -/
def authorized (owner : Address) (d : Diamond) (enabled : Bool) : Address :=
  if (!enabled && d.secondProofSystemRequired) = true then owner else d.admin

/-- The re-check after a diamond cut (`Admin.sol:121-126`). -/
def postCutCheck (E : Env) (d : Diamond) : Option Diamond :=
  if d.secondProofSystemRequired = true ∧ E.proofMode d.verifier 0 ≠ some MULTI_PROOF_TYPE
  then none else some d

/-- One call by `c` on a diamond whose layer's Bridgehub is owned by `owner`. `none` is a
revert. -/
def dstep (E : Env) (owner c : Address) : DCall → Diamond → Option Diamond
  | .setPendingAdmin a, d =>
    if c ≠ d.admin then none else some { d with pendingAdmin := a }
  | .acceptAdmin, d =>
    if c ≠ d.pendingAdmin then none else some { d with admin := d.pendingAdmin, pendingAdmin := 0 }
  | .setProofSystemStatus p enabled, d =>
    if c ≠ authorized owner d enabled then none                                  -- :417-420
    else if p ≠ .zisk then none                                                 -- :421-423
    else some { d with disabledProofSystems := newMask d.disabledProofSystems p enabled }
  | .permanentlyRequireSecondProofSystem, d =>
    if c ≠ d.admin then none                                  -- onlyAdmin
    else if d.settlementLayer ≠ 0 then none                   -- onlySettlementLayer
    else if d.secondProofSystemRequired = true then none      -- :455-457
    else if E.proofMode d.verifier d.disabledProofSystems ≠ some MULTI_PROOF_TYPE then none
    else some { d with secondProofSystemRequired := true }    -- :463
  | .makePermanentRollup, d =>
    if c ≠ d.admin then none                                  -- onlyAdmin
    else if d.settlementLayer ≠ 0 then none                   -- onlySettlementLayer
    else if d.isPermanentRollup = true then none              -- :436-438
    else some { d with isPermanentRollup := true }            -- :450
  | .upgrade none, d => postCutCheck E d
  | .upgrade (some v), d =>
    if v = 0 then none                                        -- BaseZkSyncUpgrade.sol:139-141
    else if d.secondProofSystemRequired = true ∧ E.proofMode v 0 ≠ some MULTI_PROOF_TYPE
    then none                                                 -- :143-148
    else postCutCheck E { d with verifier := v }              -- :151, Admin.sol:121-126
  | .breakGlassCut f, d =>
    match f d with
    | none => none
    | some d' => postCutCheck E d'

/-! ## The system -/

/-- The settings of one system. -/
structure Cfg where
  /-- What `_getChainMigrationsEnabled()` returns (`ChainAssetHandlerBase.sol:165-167`);
  `CHAIN_MIGRATIONS_ENABLED = false` at `d9f6789` (`common/Config.sol:320`). -/
  migrationsEnabled : Bool
  /-- **Not the source** when `true`: the hypothetical repair. -/
  repaired : Bool
  /-- `release.verifier()` of the gateway CTM's current release (`DiamondInit.sol:114-118`). -/
  gwVerifier : Address
  /-- `L1_SETTLEMENT_LAYER_VIRTUAL_ADDRESS` (`common/Config.sol:222-224`). -/
  l1VirtualAddress : Address

/-- Where a migration is going. -/
inductive Dir
  | toGateway
  | toL1
  deriving DecidableEq, Repr

/-- A burned migration whose mint has not happened. -/
structure InFlight where
  dir : Dir
  /-- `chainData`. The source encodes `wire.toCommitment` only. -/
  wire : RepairedCommitment
  /-- `ctmData`: the admin of a newly deployed diamond (`ChainTypeManager.sol:728-740`). -/
  newAdmin : Address
  deriving DecidableEq, Repr

/-- The two layers. -/
inductive Layer
  | l1
  | gw
  deriving DecidableEq, Repr

/-- The chain's two diamonds and what L1 keeps about it. -/
structure Sys where
  /-- The chain's diamond on L1. -/
  l1 : Diamond
  /-- The chain's diamond on the gateway; `none` before its first arrival. -/
  gw : Option Diamond
  /-- Burned migrations not yet minted or confirmed failed. -/
  inFlight : List InFlight
  /-- `IOwnable(BRIDGE_HUB).owner()` on L1. -/
  l1BridgehubOwner : Address
  /-- The owner of the gateway's Bridgehub. -/
  gwBridgehubOwner : Address
  /-- `L1MessageRoot.interopEnabled[chainId]` (`L1MessageRoot.sol:49`). -/
  interopEnabled : Bool
  deriving DecidableEq, Repr

/-- The chain's diamond on a layer. -/
def Sys.diamondAt (s : Sys) : Layer → Option Diamond
  | .l1 => some s.l1
  | .gw => s.gw

/-- The owner of a layer's Bridgehub. -/
def Sys.ownerAt (s : Sys) : Layer → Address
  | .l1 => s.l1BridgehubOwner
  | .gw => s.gwBridgehubOwner

/-- What `DiamondInit.initialize` leaves in the projection of a new diamond
(`DiamondInit.sol:52-150`). -/
def freshDiamond (cfg : Cfg) (admin : Address) : Diamond :=
  { admin := admin, pendingAdmin := 0, settlementLayer := 0, verifier := cfg.gwVerifier,
    isPermanentRollup := false, secondProofSystemRequired := false, disabledProofSystems := 0 }

/-- The mint the system runs: the source's, or the repair's. -/
def mintWith (cfg : Cfg) (w : RepairedCommitment) (d : Diamond) : Option Diamond :=
  if cfg.repaired = true then repairedForwardedBridgeMint w d
  else forwardedBridgeMint w.toCommitment d

/-- The commitment a burn of diamond `d` sends: `prepareChainCommitment`, and the flag the
repair would add. -/
def wireOf (payload : Commitment) (d : Diamond) : Option RepairedCommitment :=
  (prepareChainCommitment payload d).map fun c =>
    { toCommitment := c, secondProofSystemRequired := d.secondProofSystemRequired }

/-- The calls. -/
inductive Call
  /-- A call on the chain's diamond on a layer. -/
  | diamond (L : Layer) (call : DCall)
  /-- `bridgeBurn` on L1 towards the gateway whose diamond on L1 is `sl`. -/
  | bridgeBurnToGateway (sl newAdmin : Address) (payload : Commitment)
  /-- `bridgeMint` on the gateway. -/
  | bridgeMintOnGateway (f : InFlight)
  /-- `bridgeBurn` on the gateway, back to L1. -/
  | bridgeBurnToL1 (newAdmin : Address) (payload : Commitment)
  /-- `bridgeMint` on L1. -/
  | bridgeMintOnL1 (f : InFlight)
  /-- `L1ChainAssetHandler.bridgeConfirmTransferResult` with `TxStatus.Failure`. -/
  | bridgeConfirmFailure (f : InFlight)
  /-- `L1MessageRoot.enableInterop(chainId, requireSecondProofSystem)`. -/
  | enableInterop (requireSecondProofSystem : Bool)
  /-- A layer's Bridgehub changes owner (`Ownable2StepUpgradeable`, the two steps as one). -/
  | transferBridgehubOwnership (L : Layer) (o : Address)

/-- The call runs non-genuine init code. -/
def Call.isBreakGlass : Call → Bool
  | .diamond _ (.breakGlassCut _) => true
  | _ => false

/-- The call clears the L1 diamond's `settlementLayer`. -/
def Call.returnsToL1 : Call → Bool
  | .bridgeMintOnL1 _ => true
  | .bridgeConfirmFailure _ => true
  | _ => false

/-- The call is one of the four gated by `whenMigrationsEnabled`. -/
def Call.isMigration : Call → Bool
  | .bridgeBurnToGateway _ _ _ => true
  | .bridgeMintOnGateway _ => true
  | .bridgeBurnToL1 _ _ => true
  | .bridgeMintOnL1 _ => true
  | _ => false

/-- One call by `c`. `none` is a revert. -/
def step (cfg : Cfg) (E : Env) (c : Address) : Call → Sys → Option Sys
  | .diamond .l1 call, s =>
    (dstep E s.l1BridgehubOwner c call s.l1).map fun d => { s with l1 := d }
  | .diamond .gw call, s =>
    match s.gw with
    | none => none
    | some d => (dstep E s.gwBridgehubOwner c call d).map fun d' => { s with gw := some d' }
  | .bridgeBurnToGateway sl newAdmin payload, s =>
    if cfg.migrationsEnabled = false then none                     -- CAH :201
    else if c ≠ s.l1.admin then none                              -- CAH :225-227, Migrator :165-167
    else if s.l1.settlementLayer ≠ 0 then none                    -- Migrator :162-164
    else if sl = 0 then none                                      -- a registered chain's diamond
    else if newAdmin = 0 then none                                -- ChainTypeManager.sol:729-731
    else if payload.totalBatchesCommitted ≠ payload.totalBatchesExecuted then none -- :203-205
    else match wireOf payload s.l1 with                           -- :208
      | none => none
      | some w => some { s with
          l1 := { s.l1 with settlementLayer := sl },              -- :207
          inFlight := ⟨.toGateway, w, newAdmin⟩ :: s.inFlight }
  | .bridgeMintOnGateway f, s =>
    if cfg.migrationsEnabled = false then none                     -- CAH :365
    else if f ∉ s.inFlight then none
    else if f.dir ≠ .toGateway then none
    else match s.gw with
      | none =>                                                    -- CAH :398-409
        if f.newAdmin = 0 then none                               -- DiamondInit.sol:64-66
        else if cfg.gwVerifier = 0 then none                      -- DiamondInit.sol:115-117
        else (mintWith cfg f.wire (freshDiamond cfg f.newAdmin)).map fun d =>
          { s with gw := some d, inFlight := s.inFlight.erase f }
      | some d =>
        if d.settlementLayer = 0 then none                        -- Migrator :285-287
        else (mintWith cfg f.wire d).map fun d' =>
          { s with gw := some d', inFlight := s.inFlight.erase f }
  | .bridgeBurnToL1 newAdmin payload, s =>
    if cfg.migrationsEnabled = false then none                     -- CAH :201
    else match s.gw with
      | none => none                                               -- CAH :222-224
      | some d =>
        if c ≠ d.admin then none
        else if d.settlementLayer ≠ 0 then none
        else if newAdmin = 0 then none
        else if payload.totalBatchesCommitted ≠ payload.totalBatchesExecuted then none
        else match wireOf payload d with
          | none => none
          | some w => some { s with
              gw := some { d with settlementLayer := cfg.l1VirtualAddress },
              inFlight := ⟨.toL1, w, newAdmin⟩ :: s.inFlight }
  | .bridgeMintOnL1 f, s =>
    if cfg.migrationsEnabled = false then none                     -- CAH :365
    else if f ∉ s.inFlight then none
    else if f.dir ≠ .toL1 then none
    else if s.l1.settlementLayer = 0 then none                    -- Migrator :280-282
    else (mintWith cfg f.wire s.l1).map fun d =>
      { s with l1 := d, inFlight := s.inFlight.erase f }
  | .bridgeConfirmFailure f, s =>                                  -- not gated
    if f ∉ s.inFlight then none
    else if f.dir ≠ .toGateway then none
    else if s.l1.settlementLayer = 0 then none                    -- Migrator :324-326
    else some { s with
      l1 := { s.l1 with settlementLayer := 0 },                   -- :332
      inFlight := s.inFlight.erase f }
  | .enableInterop req, s =>
    if c ≠ s.l1BridgehubOwner then none                           -- L1MessageRoot.sol:73
    else if s.interopEnabled = true then none                     -- :76
    else if req = true ∧ ¬ (s.l1.secondProofSystemRequired = true ∧
        E.proofMode s.l1.verifier s.l1.disabledProofSystems = some MULTI_PROOF_TYPE) then
      none                                                         -- :81-85
    else some { s with interopEnabled := true }                    -- :87
  | .transferBridgehubOwnership .l1 o, s =>
    if c ≠ s.l1BridgehubOwner then none else some { s with l1BridgehubOwner := o }
  | .transferBridgehubOwnership .gw o, s =>
    if c ≠ s.gwBridgehubOwner then none else some { s with gwBridgehubOwner := o }

/-- Runs: successful calls, each with its caller, each allowed by `ok` in the state it starts
from. -/
inductive Run (cfg : Cfg) (E : Env) (ok : Sys → Address → Call → Prop) :
    Sys → List (Address × Call) → Sys → Prop
  | nil (s : Sys) : Run cfg E ok s [] s
  | cons {s s' s'' : Sys} {c : Address} {call : Call} {tr : List (Address × Call)} :
      ok s c call → step cfg E c call s = some s' → Run cfg E ok s' tr s'' →
      Run cfg E ok s ((c, call) :: tr) s''

/-! ## Run predicates -/

/-- The layer on whose diamond the call turns a proof system off, if it is such a call. -/
def Call.ziskOffLayer : Call → Option Layer
  | .diamond L (.setProofSystemStatus _ false) => some L
  | _ => none

/-- The call is the waived enabling, `enableInterop(chainId, false)`. -/
def Call.isWaiver : Call → Bool
  | .enableInterop false => true
  | _ => false

/-- No break-glass cut. Every other call, by anyone, is allowed. -/
def Tame (_s : Sys) (_c : Address) (call : Call) : Prop := call.isBreakGlass = false

/-- No break-glass cut, and no proof system turned off by the owner of that layer's Bridgehub.
Every other call, by anyone, is allowed. -/
def AdminSide (s : Sys) (c : Address) (call : Call) : Prop :=
  call.isBreakGlass = false ∧
  (call.ziskOffLayer = some .l1 → c ≠ s.l1BridgehubOwner) ∧
  (call.ziskOffLayer = some .gw → c ≠ s.gwBridgehubOwner)

/-- No break-glass cut, and the chain does not come back to L1. -/
def StaysAway (_s : Sys) (_c : Address) (call : Call) : Prop :=
  call.isBreakGlass = false ∧ call.returnsToL1 = false

/-- `StaysAway`, and governance does not waive the requirement. -/
def StaysAwayNoWaiver (_s : Sys) (_c : Address) (call : Call) : Prop :=
  call.isBreakGlass = false ∧ call.returnsToL1 = false ∧ call.isWaiver = false

instance (s : Sys) (c : Address) (call : Call) : Decidable (Tame s c call) := by
  unfold Tame; infer_instance
instance (s : Sys) (c : Address) (call : Call) : Decidable (AdminSide s c call) := by
  unfold AdminSide; infer_instance
instance (s : Sys) (c : Address) (call : Call) : Decidable (StaysAway s c call) := by
  unfold StaysAway; infer_instance
instance (s : Sys) (c : Address) (call : Call) : Decidable (StaysAwayNoWaiver s c call) := by
  unfold StaysAwayNoWaiver; infer_instance

/-- A one-way flag `bit` is **kept** in `s`: every diamond of the chain that accepts its batches
has it, every migration in flight carries it (`wbit`), and the L1 diamond has it while a
departure to the gateway can still be confirmed failed. -/
def Kept (bit : Diamond → Bool) (wbit : RepairedCommitment → Bool) (s : Sys) : Prop :=
  (s.l1.accepts → bit s.l1 = true) ∧
  (∀ d, s.gw = some d → d.accepts → bit d = true) ∧
  ∀ f ∈ s.inFlight, wbit f.wire = true ∧ (f.dir = .toGateway → bit s.l1 = true)

/-- `Kept` for `isPermanentRollup`. -/
def PermanentRollupKept : Sys → Prop :=
  Kept (fun d => d.isPermanentRollup) (fun w => w.isPermanentRollup)

/-- `Kept` for `secondProofSystemRequired`. With `Cfg.repaired = false` the in-flight clause
speaks about the record the source does not send. -/
def RequirementKept : Sys → Prop :=
  Kept (fun d => d.secondProofSystemRequired) (fun w => w.secondProofSystemRequired)

/-- The chain settles on L1: its L1 diamond accepts its batches and its gateway diamond, if
any, does not. -/
def SettlesOnL1 (s : Sys) : Prop :=
  s.l1.accepts ∧ ∀ d, s.gw = some d → ¬ d.accepts

/-! ## Witness data -/

/-- `MultiProofVerifier.getProofMode` (`state-transition/verifiers/MultiProofVerifier.sol:101-109`):

    if (_disabledProofSystems & ~uint8(1 << uint8(ProofSystem.Zisk)) != 0) revert ..;   // :102-104
    return _disabledProofSystems & uint8(1 << uint8(ProofSystem.Zisk)) == 0              // :105-108
        ? ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE : ZKSYNC_OS_PLONK_VERIFICATION_TYPE; -/
def multiProofGetProofMode (m : UInt8) : Option ℕ :=
  if m &&& ~~~ziskBit ≠ 0 then none
  else if m &&& ziskBit = 0 then some MULTI_PROOF_TYPE else some PLONK_TYPE

/-- The witness verifiers: the address `20` is a single-proof verifier (PLONK for every mask);
every other address runs `MultiProofVerifier.getProofMode`. -/
def wEnv : Env := ⟨fun v m => if v = 20 then some PLONK_TYPE else multiProofGetProofMode m⟩

/-- Migrations enabled, as in the dev variants; the gateway's release ships the multi-proof
verifier at `11`. -/
def wEnabled : Cfg :=
  { migrationsEnabled := true, repaired := false, gwVerifier := 11, l1VirtualAddress := 99 }

/-- The source at `d9f6789`: `CHAIN_MIGRATIONS_ENABLED = false`. -/
def wSource : Cfg := { wEnabled with migrationsEnabled := false }

/-- The hypothetical repair, with migrations enabled. -/
def wRepaired : Cfg := { wEnabled with repaired := true }

/-- The chain on L1: admin `1`, the multi-proof verifier at `10`, ZiSK on, neither flag set. -/
def wL1 : Diamond :=
  { admin := 1, pendingAdmin := 0, settlementLayer := 0, verifier := 10,
    isPermanentRollup := false, secondProofSystemRequired := false, disabledProofSystems := 0 }

/-- The chain on L1 only; L1's Bridgehub is owned by `2`, the gateway's by `3`. -/
def w0 : Sys :=
  { l1 := wL1, gw := none, inFlight := [], l1BridgehubOwner := 2, gwBridgehubOwner := 3,
    interopEnabled := false }

/-- The storage the witness burns read: one batch, executed. -/
def wPayload : Commitment :=
  { totalBatchesExecuted := 1, totalBatchesVerified := 1, totalBatchesCommitted := 1,
    l2SystemContractsUpgradeTxHash := 0, l2SystemContractsUpgradeBatchNumber := 0,
    batchHashes := [7], priorityTree := ⟨0, 0, 0, []⟩, isPermanentRollup := false,
    precommitmentForTheLatestBatch := 0 }

/-- The admin makes the chain a permanent rollup and requires the second proof system, on L1. -/
def wRequire : List (Address × Call) :=
  [(1, .diamond .l1 .makePermanentRollup),
   (1, .diamond .l1 .permanentlyRequireSecondProofSystem)]

/-- The Bridgehub owner enables interop, with the requirement. -/
def wEnable : List (Address × Call) := [(2, .enableInterop true)]

/-- `w0` after `wRequire ++ wEnable`. -/
def w3 : Sys :=
  { w0 with
    l1 := { wL1 with isPermanentRollup := true, secondProofSystemRequired := true },
    interopEnabled := true }

/-- What the burn of `w3`'s L1 diamond puts in flight: the commitment, and the record of the
flag that the source does not send. -/
def wFlight : InFlight :=
  { dir := .toGateway,
    wire := { toCommitment := { wPayload with isPermanentRollup := true },
              secondProofSystemRequired := true },
    newAdmin := 1 }

/-- The chain migrates to the gateway whose diamond on L1 is `77`; the admin there is `1`. -/
def wLeave : List (Address × Call) :=
  [(1, .bridgeBurnToGateway 77 1 wPayload),
   (5, .bridgeMintOnGateway wFlight)]

/-- `w3` after `wLeave`, in the source: the new gateway diamond is a permanent rollup and does
not require the second proof system. -/
def w5 : Sys :=
  { w3 with
    l1 := { w3.l1 with settlementLayer := 77 },
    gw := some { freshDiamond wEnabled 1 with isPermanentRollup := true } }

/-- `w3` after `wLeave`, under the repair: the new gateway diamond has both flags. -/
def w5Repaired : Sys :=
  { w3 with
    l1 := { w3.l1 with settlementLayer := 77 },
    gw := some { freshDiamond wRepaired 1 with
      isPermanentRollup := true, secondProofSystemRequired := true } }

/-- The chain admin (`1`, not the gateway Bridgehub's owner `3`) turns ZiSK off on the gateway
diamond, and an upgrade installs the single-proof verifier `20` there. -/
def wDrop : List (Address × Call) :=
  [(1, .diamond .gw (.setProofSystemStatus .zisk false)),
   (5, .diamond .gw (.upgrade (some 20)))]

/-- The gateway diamond after `wDrop`. -/
def wDropped : Diamond :=
  { freshDiamond wEnabled 1 with
    isPermanentRollup := true, disabledProofSystems := ziskBit, verifier := 20 }

/-- `w5` after `wDrop`. -/
def w7 : Sys := { w5 with gw := some wDropped }

/-- On L1 under the ban: an upgrade to the multi-proof verifier `12`, the Bridgehub owner's
emergency ZiSK-off, and the admin turning ZiSK back on. -/
def wOnL1 : List (Address × Call) :=
  [(5, .diamond .l1 (.upgrade (some 12))),
   (2, .diamond .l1 (.setProofSystemStatus .zisk false)),
   (1, .diamond .l1 (.setProofSystemStatus .zisk true))]

/-- An unflagged chain's flight to the gateway. -/
def wFlightPlain : InFlight :=
  { dir := .toGateway, wire := { toCommitment := wPayload, secondProofSystemRequired := false },
    newAdmin := 1 }

/-- An unflagged chain migrates to the gateway and sets the requirement there. -/
def wRequireOnGateway : List (Address × Call) :=
  [(1, .bridgeBurnToGateway 77 1 wPayload),
   (5, .bridgeMintOnGateway wFlightPlain),
   (1, .diamond .gw .permanentlyRequireSecondProofSystem)]

/-- `w0` after `wRequireOnGateway`: the gateway diamond requires the second proof system, the
L1 diamond does not. -/
def wAway : Sys :=
  { w0 with
    l1 := { wL1 with settlementLayer := 77 },
    gw := some { freshDiamond wEnabled 1 with secondProofSystemRequired := true } }

/-- The flight back to L1 of a chain that set the requirement on the gateway, under the repair. -/
def wFlightBack : InFlight :=
  { dir := .toL1, wire := { toCommitment := wPayload, secondProofSystemRequired := true },
    newAdmin := 1 }

/-- Under the repair: an unflagged chain migrates to the gateway; its admin turns ZiSK off on
the L1 diamond it left and sets the requirement on the gateway; the chain comes back. -/
def wRoundTrip : List (Address × Call) :=
  [(1, .bridgeBurnToGateway 77 1 wPayload),
   (5, .bridgeMintOnGateway wFlightPlain),
   (1, .diamond .l1 (.setProofSystemStatus .zisk false)),
   (1, .diamond .gw .permanentlyRequireSecondProofSystem),
   (1, .bridgeBurnToL1 1 wPayload),
   (5, .bridgeMintOnL1 wFlightBack)]

/-- `w0` after `wRoundTrip`, under the repair. -/
def wBack : Sys :=
  { w0 with
    l1 := { wL1 with secondProofSystemRequired := true, disabledProofSystems := ziskBit },
    gw := some { freshDiamond wRepaired 1 with
      secondProofSystemRequired := true, settlementLayer := 99 } }

end Contracts.SecondProofSystem.MigrationV35
