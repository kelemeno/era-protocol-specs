import Mathlib.Tactic

/-!
# Model: `isValidSettlementLayer` against the layer that executed each batch (v35 head)

**Commit.** matter-labs/era-contracts, branch `draft/v0.35.0` at `b17415d20`. Paths are relative
to `l1-contracts/contracts/`. Files are cited as

* `L1CAH` — `core/chain-asset-handler/L1ChainAssetHandler.sol`,
* `CAH` — `core/chain-asset-handler/ChainAssetHandlerBase.sol`,
* `L2CAH` — `core/chain-asset-handler/L2ChainAssetHandler.sol`,
* `ICAH` — `core/chain-asset-handler/IChainAssetHandler.sol`,
* `MRB` — `core/message-root/MessageRootBase.sol`, `L1MR` — `core/message-root/L1MessageRoot.sol`,
* `BH` — `core/bridgehub/BridgehubBase.sol`, `L1BH` — `core/bridgehub/L1Bridgehub.sol`,
* `MIG` — `state-transition/chain-deps/facets/Migrator.sol`,
* `EXE` — `state-transition/chain-deps/facets/Executor.sol`,
* `ZKB` — `state-transition/chain-deps/facets/ZKChainBase.sol`,
* `CFG` — `common/Config.sol`.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.L1ChainAssetHandler.Properties.SettlementLayerValidation`, proofs in
`EraSpec.Contracts.L1ChainAssetHandler.Proofs.SettlementLayerValidation`.

## The function

`L1MessageRoot` accepts a proof that recurses through a settlement layer only if the L1 chain
asset handler accepts the claimed layer and layer batch for the batch (`L1MR:96-120`, the only
caller, at `L1MR:103-109`). The direct branch (`MRB:343-348`) does not call it. The function:

    function isValidSettlementLayer(uint256 _chainId, uint256 _batchNumber,
        uint256 _claimedSettlementLayer, uint256 _claimedSettlementLayerBatchNumber)
        external view returns (bool) {                                                  // L1CAH:218-223
        uint256 currentMigrationNum = migrationNumber[_chainId];                        // L1CAH:225
        require(currentMigrationNum <= MAX_ALLOWED_NUMBER_OF_MIGRATIONS, ...);          // L1CAH:229
        for (uint256 i = MIGRATION_NUMBER_L1_TO_SETTLEMENT_LAYER; i <= currentMigrationNum; ++i) {
            MigrationInterval memory interval = _migrationInterval[_chainId][i];       // L1CAH:231-232
            if (interval.settlementLayerChainId == 0) { continue; }                     // L1CAH:235-237
            if (_batchNumber <= interval.migrateToGWBatchNumber) {
                return _claimedSettlementLayer == _getL1ChainId(); }                    // L1CAH:239-242
            if (interval.isActive) {
                return _claimedSettlementLayer == interval.settlementLayerChainId &&
                    _claimedSettlementLayerBatchNumber >= interval.settlementLayerBatchLowerBound; } // :244-249
            if (_batchNumber <= interval.migrateFromGWBatchNumber) {
                return _claimedSettlementLayer == interval.settlementLayerChainId &&
                    _claimedSettlementLayerBatchNumber >= interval.settlementLayerBatchLowerBound &&
                    _claimedSettlementLayerBatchNumber <= interval.settlementLayerBatchUpperBound; } // :252-260
        }
        return _claimedSettlementLayer == _getL1ChainId();                              // L1CAH:266
    }

`MAX_ALLOWED_NUMBER_OF_MIGRATIONS = 2`, `MIGRATION_NUMBER_L1_TO_SETTLEMENT_LAYER = 1`,
`MIGRATION_NUMBER_SETTLEMENT_LAYER_TO_L1 = 2` (`CFG:323-329`). At `main` `70096e2ea` the loop
starts at index 0 (`L1ChainAssetHandler.sol:256` there), where `setHistoricalMigrationInterval`
(`:219-237` there, owner-only) records legacy Era Gateway intervals; `isValidSettlementLayerMain`
is that loop. Everything else in this file is the v35 head.

**`main` on this path (argued from source, not modelled).** Besides the loop and that writer,
`main` differs on the cited paths in reject-only checks (`isPreV31` in `isReadyForMigration`, the
pause modifier, `NotEraChain`), in `bridgeMint` skipping the L1 migration-number checks when
`migrationNumber` is 0 (`ChainAssetHandlerBase.sol:379` there; an L1 mint also needs the chain
away, `BridgehubBase.sol:442-443` there), and in one more writer of L1's counter,
`saveV31UpgradeChainBatchNumber` (`L1MessageRoot.sol:89-107` there), which needs that counter to
be 0 and the diamond's executed count to be positive. On the model's reachable states the two
counters are equal and an away chain has `migrationNumber` 1
(`Properties.CountersEqualAndAwayMeansMigrationOne`), so neither difference fires; with no legacy
interval written, `Properties.MainAgreesWithoutLegacyInterval` gives `main`'s answer.

## Every writer of the classification state (checked against `b17415d20`)

`grep -rn "_migrationInterval\|migrationNumber\[" --include='*.sol'` outside `dev-contracts/`:

* `migrationNumber[c]` (`CAH:110`): `_finalizeBridgeBurn` increments it after
  `require(currentMigrationNum < MAX_ALLOWED_NUMBER_OF_MIGRATIONS)` (`CAH:274-279`);
  `bridgeMint` sets it to the message's number (`CAH:384`), on L1 only after
  `currentMigrationNumber == 1` and message number `== 2` (`CAH:374-383`);
  `bridgeConfirmTransferResult` on failure sets it from 1 to 0 (`L1CAH:151-157`).
  (`L2CAH:125` writes the entry of the layer's own chain id, not of a migrating chain.)
* `_migrationInterval[c][i]` (`L1CAH:58`): `_recordMigrationToSL` writes index
  `_newMigrationNum`, which must be 1 (`L1CAH:286-298`), with `migrateToGWBatchNumber` the
  message root's `currentChainBatchNumber(c)` (`CAH:281`) and the lower bound the message root's
  `currentChainBatchNumber(settlementLayer)` (`L1CAH:290`); `_recordMigrationFromSL` updates
  index 1, which must be active (`L1CAH:309-319`), with the upper bound read the same way
  (`L1CAH:316-318`); the failure path deletes index 1 (`L1CAH:160`). Index 2 has no writer. On a
  settlement layer both recorders are empty (`L2CAH:136-151`).

`bridgeBurn` and `bridgeMint` carry `whenMigrationsEnabled` (`CAH:151-156`, `:201`, `:365`), and
`CHAIN_MIGRATIONS_ENABLED = false` at this commit (`CFG:320`); `bridgeConfirmTransferResult` does
not (`L1CAH:118-128`).

## The batch counters

* **Execution.** `executeBatchesSharedBridge` (`EXE:170-212`) carries `onlySettlementLayer`
  (`ZKB:141-146`: the diamond's `s.settlementLayer == address(0)`), first appends each batch's
  logs root to the local message root (`EXE:192-194` → `EXE:163-166` → `MRB:173-180`), whose
  `_recordChainBatchRoot` requires `_batchNumber == currentChainBatchNumber[c] + 1` and sets the
  counter to it (`MRB:192-196`), then requires the same number to be
  `totalBatchesExecuted + i + 1` (`EXE:66-68`) and adds the count (`EXE:201-202`). For these two
  counter checks, a call of several batches passes iff the same batches one at a time do; the
  model executes one batch per step.
* **Registration.** `createNewChain` calls `addNewChain(c, 0)` (`L1BH:134`) on a diamond whose
  `DiamondInit` starts at batch 0; `registerAlreadyDeployedZKChain` calls
  `addNewChain(c, totalBatchesExecuted)` (`L1BH:316`). Both start the two counters equal.
* **Migration.** The burn sends `batchNumber = currentChainBatchNumber(c)` (`CAH:281`) and the
  diamond's commitment with its `totalBatchesExecuted` (`MIG:208`, `:342`). The mint sets the
  destination's message-root counter to `batchNumber` (`addNewChain`, `CAH:409`, `MRB:145-150`,
  which reverts `ChainExists` for a registered chain; or `setMigratingChainBatchNumber`,
  `CAH:414`, `MRB:153-157`, which requires the counter `<= batchNumber`), and the diamond's
  counter to the commitment's (`MIG:230-240`).
* **No other writer.** `totalBatchesExecuted` is written only at `EXE:202` and `MIG:240`, and
  `currentChainBatchNumber` only at `MRB:156`, `:196` and `:282` (`_addNewChain`). Committing,
  proving and reverting batches write neither (`_revertBatches` refuses to go below the executed
  count, `ZKB:321-323`), and `bridgeConfirmTransferResult` with `TxStatus.Success` writes none of
  the state above (`L1CAH:151`, `MIG:318-320`); none of these is a step.

## What is modelled

One migrating chain `c` (`ValWorld.c`). Its classification state on L1 (`migrationNumber`,
`_migrationInterval`), L1's message-root counters (for `c` and for every settlement layer), `c`'s
L1 diamond (`totalBatchesExecuted`, whether `s.settlementLayer != 0`), its diamond and message-root
entry on each settlement layer (`SLCopy`), each layer's chain asset handler `migrationNumber[c]`,
the one migration message in each direction, and each settlement layer's open batch. Steps
(`ValLabel`, `valStep`): `c` executes a batch on L1 or on a settlement layer; a settlement layer
seals its open batch, or L1 executes its next batch; L1's `bridgeBurn` to a layer; the layer's
`bridgeMint`, or the failure of that transaction; L1's `bridgeConfirmTransferResult` of the
failure; the layer's `bridgeBurn` back to L1; L1's `bridgeMint` of the return. A revert is
`none`. `valRun` runs a list of steps.

**Ghost state.** `hist b` records, when batch `b` of `c` is executed, the chain id of the layer
whose diamond executed it and, on a settlement layer, that layer's batch open at the time. The
execution appends `b`'s root to the layer's message root (`EXE:192-194`, `MRB:199-220`); reading
that open batch as the first layer batch whose root contains `b`'s root assumes that each layer
batch commits the layer's message root as of the batch's end (the layer's system contracts, not
modelled). `total` counts executed batches. Neither is read by any guard.

## Modelling choices

* **Reject-only checks are omitted**: the pauses (`CAH:200`, `:204`, `:365-366`), the CTM asset
  id and CTM checks, the admin check, `isReadyForMigration`, the Migrator's checks other than
  those on `s.settlementLayer` (priority mode, admin, priority queue, deposit pause, CTM,
  protocol version, all batches executed, batch counts and hashes, priority tree:
  `MIG:159-205`, `:217-259`, `:270-279`), the message root's nonzero-root and write-once checks
  (`MRB:187-191`), and the executor's proof, priority and hash checks. Omitting a check that can
  only reject only adds runs, so a statement about every run of the model also covers the runs in
  which those checks pass.
* **Kept guards**, in each step's docstring with `file:line`: `whenMigrationsEnabled`, the
  bridgehub's whitelist checks (`BH:407-418`), `onlySettlementLayer` and the diamond's
  `settlementLayer` checks, the migration-number checks, both counters' consecutiveness, the
  interval checks, and `setMigratingChainBatchNumber`'s `<=`.
* **Identifiers are `ℕ`.** A diamond's `s.settlementLayer` on L1 is a Boolean (zero or not); the
  settlement layer's chain id is carried by the interval and the messages. A layer's diamond
  address is identified with its chain id.
* **The environment** (`ValEnv`) has two guarantees, each a switch: L1 executes only sealed
  batches of a settlement layer (`sealedOnly`: a layer batch is committed, hence closed, before it
  is executed), and the return message is finalized on L1 only after the layer batch that
  contains its burn was executed on L1 (`finalizedAfterExec`: `L1Nullifier` proves the message
  against the layer's stored batch root, `MRB:343-347`, which only that batch's execution writes,
  up to an inclusion-proof collision). `ValEnv.real` has both; the countermodels drop one. The
  environment also decides whether the L1 → layer transaction fails (`failSL`, any time while it
  is pending); a failure proof is consumed once and only for a failed transaction.
* **Settlement layers are honest and settle on L1.** A layer runs this code (its handler is
  `L2ChainAssetHandler`) and is whitelisted (`BH:407-409`); a whitelisted chain cannot migrate
  (`BH:416-418`), and the whitelist (`L1BH:94-100`) is fixed for the run (`ValWorld.wl`). Its own
  batches are executed on L1 in order (`slExecL1`).
* **One chain.** The handler's mappings are keyed by chain id and every writer writes the entry of
  the chain it migrates; other chains reach this model only through a settlement layer's batches
  and L1's counter of them, which `slSeal` and `slExecL1` cover.
* **`CHAIN_MIGRATIONS_ENABLED` is `ValWorld.enabled`** (`false` at this commit). The positive
  results hold for both values; the round-trip witness uses `true`.
-/

namespace Contracts.L1ChainAssetHandler.SettlementLayerValidation

/-- Point update of a mapping. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

/-- `MIGRATION_NUMBER_L1_TO_SETTLEMENT_LAYER` (`CFG:323`). -/
def numToSL : ℕ := 1

/-- `MIGRATION_NUMBER_SETTLEMENT_LAYER_TO_L1` (`CFG:326`). -/
def numToL1 : ℕ := 2

/-- `MAX_ALLOWED_NUMBER_OF_MIGRATIONS` (`CFG:329`). -/
def maxMigrations : ℕ := 2

/-- `MigrationInterval` (`ICAH:17-24`). -/
structure MigInterval where
  /-- `migrateToGWBatchNumber`: the last batch executed on L1 before leaving. -/
  toGW : ℕ
  /-- `migrateFromGWBatchNumber`: the last batch executed on the layer before returning. -/
  fromGW : ℕ
  /-- `settlementLayerBatchLowerBound`. -/
  lower : ℕ
  /-- `settlementLayerBatchUpperBound` ("Imprecise", `ICAH:12-14`). -/
  upper : ℕ
  /-- `settlementLayerChainId`; `0` marks an uninitialized interval (`L1CAH:235`). -/
  sl : ℕ
  /-- `isActive`. -/
  active : Bool
  deriving DecidableEq

/-- The zero interval, which `delete` leaves (`L1CAH:160`). -/
def MigInterval.empty : MigInterval := ⟨0, 0, 0, 0, 0, false⟩

/-- The loop of `isValidSettlementLayer` (`L1CAH:231-263`) over the intervals it visits, in
order, with the fall-through answer of `L1CAH:266` at the end. `l1` is `_getL1ChainId()`, `b` the
batch, `X` the claimed layer, `k` the claimed layer batch. -/
def scanIntervals (l1 b X k : ℕ) : List MigInterval → Bool
  | [] => decide (X = l1)
  | iv :: rest =>
    if iv.sl = 0 then scanIntervals l1 b X k rest
    else if b ≤ iv.toGW then decide (X = l1)
    else if iv.active = true then decide (X = iv.sl ∧ iv.lower ≤ k)
    else if b ≤ iv.fromGW then decide (X = iv.sl ∧ iv.lower ≤ k ∧ k ≤ iv.upper)
    else scanIntervals l1 b X k rest

/-- `isValidSettlementLayer(_chainId, b, X, k)` (`L1CAH:218-267`) for a chain whose
`migrationNumber` is `mn` and whose `_migrationInterval` row is `ivs`: the loop visits indices
`1 .. mn` (`List.range' 1 mn`). `none` is the revert `IteratedMigrationsNotSupported`
(`L1CAH:229`). -/
def isValidSettlementLayer (l1 mn : ℕ) (ivs : ℕ → MigInterval) (b X k : ℕ) : Option Bool :=
  if mn ≤ maxMigrations then some (scanIntervals l1 b X k ((List.range' numToSL mn).map ivs))
  else none

/-- The same function at `main` `70096e2ea`, whose loop starts at index 0
(`L1ChainAssetHandler.sol:254-256` there): indices `0 .. mn`. -/
def isValidSettlementLayerMain (l1 mn : ℕ) (ivs : ℕ → MigInterval) (b X k : ℕ) : Option Bool :=
  if mn ≤ maxMigrations then some (scanIntervals l1 b X k ((List.range (mn + 1)).map ivs))
  else none

/-- The answer with the loop unrolled for a row whose index-2 interval is empty, as a function of
the index-1 interval only (stated equal to `isValidSettlementLayer` in
`Properties.IsValidUnrolled`). -/
def closedForm (l1 mn : ℕ) (iv : MigInterval) (b X k : ℕ) : Bool :=
  if 1 ≤ mn ∧ iv.sl ≠ 0 then
    if b ≤ iv.toGW then decide (X = l1)
    else if iv.active = true then decide (X = iv.sl ∧ iv.lower ≤ k)
    else if b ≤ iv.fromGW then decide (X = iv.sl ∧ iv.lower ≤ k ∧ k ≤ iv.upper)
    else decide (X = l1)
  else decide (X = l1)

/-! ## The system -/

/-- Fixed configuration. -/
structure ValWorld where
  /-- `L1_CHAIN_ID` (`L1CAH:46`, `:100`). -/
  l1 : ℕ
  /-- The migrating chain. -/
  c : ℕ
  /-- `whitelistedSettlementLayers` on L1's bridgehub (`BH:407`, `:416`), fixed for the run. -/
  wl : ℕ → Bool
  /-- `_getChainMigrationsEnabled()`: `CHAIN_MIGRATIONS_ENABLED` (`CFG:320`, `false`). -/
  enabled : Bool

/-- The configuration premise: chain id 0 is not a whitelisted settlement layer. `L1BH:94-100`
whitelists only a chain whose `settlementLayer` entry is L1, which only a registered chain has,
and no chain with id 0 is registered (`BH:491-494`). -/
def ValWorld.Ok (W : ValWorld) : Prop := W.wl 0 = false

/-- The environment guarantees, as switches (see the module docstring). -/
structure ValEnv where
  /-- L1 executes a settlement layer's batch only once it is sealed. -/
  sealedOnly : Bool
  /-- L1 finalizes the return message only once the layer batch containing its burn has been
  executed on L1. -/
  finalizedAfterExec : Bool

/-- Both guarantees. -/
def ValEnv.real : ValEnv := ⟨true, true⟩

/-- Chain `c` as registered on a settlement layer: its diamond there and that layer's message-root
entry. -/
structure SLCopy where
  /-- The diamond's `totalBatchesExecuted`. -/
  exec : ℕ
  /-- The layer's `MessageRoot.currentChainBatchNumber[c]`. -/
  mr : ℕ
  /-- The diamond's `s.settlementLayer == address(0)`: `c` settles there now. -/
  active : Bool
  deriving DecidableEq

/-- The L1 → layer migration message: the mint data of `CAH:289-295` and the commitment's
`totalBatchesExecuted`, sent as a priority transaction. -/
structure ToSLMsg where
  /-- The destination layer, `_settlementChainId`. -/
  sl : ℕ
  /-- `batchNumber` (`CAH:281`, `:346`). -/
  batchNumber : ℕ
  /-- The commitment's `totalBatchesExecuted` (`MIG:342`). -/
  exec : ℕ
  /-- `migrationNumber` (`CAH:349`). -/
  num : ℕ
  /-- The transaction failed on the layer. -/
  failed : Bool
  deriving DecidableEq

/-- The layer → L1 return message. -/
structure ToL1Msg where
  /-- The layer that burned. -/
  src : ℕ
  /-- `batchNumber`: the layer message root's `currentChainBatchNumber(c)` (`CAH:281`). -/
  batchNumber : ℕ
  /-- The commitment's `totalBatchesExecuted`. -/
  exec : ℕ
  /-- `migrationNumber`. -/
  num : ℕ
  /-- The layer batch that contains the burn: the layer's open batch at that time. -/
  slBatch : ℕ
  deriving DecidableEq

/-- Ghost: where one executed batch of `c` was executed. -/
structure Settled where
  /-- The chain id of the layer whose diamond executed it (`l1` for L1). -/
  layer : ℕ
  /-- On a settlement layer, its batch open at the time; `0` on L1. -/
  slBatch : ℕ
  deriving DecidableEq

/-- The joint state. -/
structure ValState where
  /-- L1 handler: `migrationNumber[c]` (`CAH:110`). -/
  mn : ℕ
  /-- L1 handler: `_migrationInterval[c][i]` (`L1CAH:58`). -/
  ivs : ℕ → MigInterval
  /-- L1 message root: `currentChainBatchNumber[x]` (`MRB:84`), for `c` and for every layer. -/
  mrL1 : ℕ → ℕ
  /-- `c`'s L1 diamond: `totalBatchesExecuted`. -/
  execL1 : ℕ
  /-- `c`'s L1 diamond: `s.settlementLayer != address(0)` (the bridgehub's
  `settlementLayer[c] != L1` moves with it: `BH:414`, `:445`, `:466`). -/
  awayL1 : Bool
  /-- Each settlement layer's batch currently being built. -/
  slOpen : ℕ → ℕ
  /-- `c` on each settlement layer; `none` when not registered there. -/
  gcopy : ℕ → Option SLCopy
  /-- Each layer's handler: `migrationNumber[c]`. -/
  mnG : ℕ → ℕ
  /-- The L1 → layer message in flight. -/
  toSL : Option ToSLMsg
  /-- The layer → L1 message in flight. -/
  toL1 : Option ToL1Msg
  /-- Ghost: batch `b` of `c` was executed, and where. -/
  hist : ℕ → Option Settled
  /-- Ghost: the number of batches of `c` executed so far. -/
  total : ℕ

/-- `isValidSettlementLayer(c, b, X, k)` on the state's L1 handler. -/
def isValidAt (W : ValWorld) (s : ValState) (b X k : ℕ) : Option Bool :=
  isValidSettlementLayer W.l1 s.mn s.ivs b X k

/-- What happens. -/
inductive ValLabel
  /-- `c`'s L1 diamond executes batch `b`. -/
  | execL1 (b : ℕ)
  /-- `c`'s diamond on layer `t` executes batch `b`. -/
  | execSL (t b : ℕ)
  /-- Layer `t` seals its open batch and opens the next. -/
  | slSeal (t : ℕ)
  /-- L1 executes layer `t`'s next batch. -/
  | slExecL1 (t : ℕ)
  /-- L1's `bridgeBurn` of `c` to layer `t` (`CAH:188-254`). -/
  | burnL1 (t : ℕ)
  /-- The pending L1 → layer transaction runs the layer's `bridgeMint` (`CAH:361-420`). -/
  | mintSL
  /-- The pending L1 → layer transaction fails on the layer. -/
  | failSL
  /-- L1's `bridgeConfirmTransferResult` with `TxStatus.Failure` (`L1CAH:122-172`). -/
  | confirmFailure
  /-- Layer `t`'s `bridgeBurn` of `c` back to L1 (`CAH:188-254`, `CAH:239-241`). -/
  | burnSL (t : ℕ)
  /-- L1's `bridgeMint` of the return message (`CAH:361-420`). -/
  | mintL1

/-- One step; `none` is a revert (or an environment step that cannot happen).

* `execL1 b`: `onlySettlementLayer` (`ZKB:141-146`), `b = currentChainBatchNumber[c] + 1`
  (`MRB:192-193`) and `b = totalBatchesExecuted + 1` (`EXE:66-68`); both counters become `b`
  (`MRB:196`, `EXE:201-202`).
* `execSL t b`: the same on `c`'s diamond on `t` and `t`'s message root.
* `slExecL1 t`: `t` is not `c` (whose execution is `execL1`) or L1; L1's counter of `t` advances
  by one (`MRB:192-196`); under `sealedOnly` the batch is sealed.
* `burnL1 t`: `whenMigrationsEnabled` (`CAH:201`), `t` whitelisted (`BH:407-409`), `c` settles on
  L1 (`BH:411-413`, `MIG:162-164`), `c` not whitelisted (`BH:416-418`),
  `migrationNumber < 2` (`CAH:277`), `t != L1` (`L1CAH:283-285`), new number `== 1`
  (`L1CAH:286-289`). Effects: `s.settlementLayer` set (`MIG:207`), number incremented
  (`CAH:278-279`), interval written (`L1CAH:290-298`), message sent with `batchNumber`
  (`CAH:281`) and the commitment (`MIG:208`).
* `mintSL`: `whenMigrationsEnabled` (`CAH:365`); the number is set (`CAH:384`; no check off L1);
  on a layer where `c` is not registered `addNewChain(c, batchNumber)` (`CAH:398-409`), else
  `setMigratingChainBatchNumber`'s `<=` (`MRB:155`) and the diamond's `NotMigrated` check
  (`MIG:284-287`); the diamond takes the commitment's counter and settles there (`MIG:238-240`,
  `:299`).
* `confirmFailure`: the pending message failed; `migrationNumber == 1` (`L1CAH:153-156`), set to
  0 (`:157`), interval 1 deleted (`:160`); the diamond is away (`MIG:324-326`) and settles on L1
  again (`MIG:332`, `BH:465-467`). Not gated by `whenMigrationsEnabled`.
* `burnSL t`: `whenMigrationsEnabled`, the diamond on `t` settles there (`MIG:162-164`),
  `migrationNumber < 2` on `t` (`CAH:277`); the destination is L1 (`CAH:239-241`); no interval is
  recorded (`L2CAH:136-143`); the message carries `t`'s counter (`CAH:281`) and is in `t`'s open
  batch.
* `mintL1`: `whenMigrationsEnabled`; `migrationNumber == 1` and message number `== 2`
  (`CAH:374-383`); interval 1 active (`L1CAH:313-314`); `c` away (`BH:441-443`,
  `MIG:280-282`); `currentChainBatchNumber[c] <= batchNumber` (`MRB:155`); under
  `finalizedAfterExec` the message's layer batch was executed on L1. Effects: number set
  (`CAH:384`), interval closed with the upper bound read from L1's counter of the interval's layer
  (`L1CAH:315-319`), L1's counter of `c` set (`MRB:156`), the diamond's counter set and `c`
  settles on L1 (`MIG:238-240`, `:299`). -/
def valStep (K : ValEnv) (W : ValWorld) (s : ValState) : ValLabel → Option ValState
  | .execL1 b =>
    if s.awayL1 = false ∧ b = s.mrL1 W.c + 1 ∧ b = s.execL1 + 1 then
      some { s with mrL1 := upd s.mrL1 W.c b, execL1 := b,
                    hist := upd s.hist b (some ⟨W.l1, 0⟩), total := s.total + 1 }
    else none
  | .execSL t b =>
    match s.gcopy t with
    | some g =>
      if g.active = true ∧ b = g.mr + 1 ∧ b = g.exec + 1 then
        some { s with gcopy := upd s.gcopy t (some ⟨b, b, true⟩),
                      hist := upd s.hist b (some ⟨t, s.slOpen t⟩), total := s.total + 1 }
      else none
    | none => none
  | .slSeal t => some { s with slOpen := upd s.slOpen t (s.slOpen t + 1) }
  | .slExecL1 t =>
    if t ≠ W.c ∧ t ≠ W.l1 ∧ (K.sealedOnly = true → s.mrL1 t + 1 < s.slOpen t) then
      some { s with mrL1 := upd s.mrL1 t (s.mrL1 t + 1) }
    else none
  | .burnL1 t =>
    if W.enabled = true ∧ W.wl t = true ∧ s.awayL1 = false ∧ W.wl W.c = false ∧
        s.mn < maxMigrations ∧ t ≠ W.l1 ∧ s.mn + 1 = numToSL then
      some { s with awayL1 := true, mn := s.mn + 1,
                    ivs := upd s.ivs (s.mn + 1) ⟨s.mrL1 W.c, 0, s.mrL1 t, 0, t, true⟩,
                    toSL := some ⟨t, s.mrL1 W.c, s.execL1, s.mn + 1, false⟩ }
    else none
  | .mintSL =>
    match s.toSL with
    | some m =>
      if W.enabled = true ∧ m.failed = false then
        match s.gcopy m.sl with
        | none =>
          some { s with mnG := upd s.mnG m.sl m.num,
                        gcopy := upd s.gcopy m.sl (some ⟨m.exec, m.batchNumber, true⟩),
                        toSL := none }
        | some g =>
          if g.mr ≤ m.batchNumber ∧ g.active = false then
            some { s with mnG := upd s.mnG m.sl m.num,
                          gcopy := upd s.gcopy m.sl (some ⟨m.exec, m.batchNumber, true⟩),
                          toSL := none }
          else none
      else none
    | none => none
  | .failSL =>
    match s.toSL with
    | some m =>
      if m.failed = false then some { s with toSL := some { m with failed := true } } else none
    | none => none
  | .confirmFailure =>
    match s.toSL with
    | some m =>
      if m.failed = true ∧ s.mn = numToSL ∧ s.awayL1 = true then
        some { s with mn := s.mn - 1, ivs := upd s.ivs s.mn MigInterval.empty,
                      awayL1 := false, toSL := none }
      else none
    | none => none
  | .burnSL t =>
    match s.gcopy t with
    | some g =>
      if W.enabled = true ∧ g.active = true ∧ s.mnG t < maxMigrations then
        some { s with mnG := upd s.mnG t (s.mnG t + 1),
                      gcopy := upd s.gcopy t (some { g with active := false }),
                      toL1 := some ⟨t, g.mr, g.exec, s.mnG t + 1, s.slOpen t⟩ }
      else none
    | none => none
  | .mintL1 =>
    match s.toL1 with
    | some r =>
      if W.enabled = true ∧ s.mn = numToSL ∧ r.num = numToL1 ∧ (s.ivs numToSL).active = true ∧
          s.awayL1 = true ∧ s.mrL1 W.c ≤ r.batchNumber ∧
          (K.finalizedAfterExec = true → r.slBatch ≤ s.mrL1 r.src) then
        some { s with
          mn := r.num
          ivs := upd s.ivs numToSL
            { (s.ivs numToSL) with
              fromGW := r.batchNumber
              upper := s.mrL1 (s.ivs numToSL).sl
              active := false }
          mrL1 := upd s.mrL1 W.c r.batchNumber
          execL1 := r.exec
          awayL1 := false
          toL1 := none }
      else none
    | none => none

/-- A list of steps run in order; `none` if one of them is `none`. -/
def valRun (K : ValEnv) (W : ValWorld) : ValState → List ValLabel → Option ValState
  | s, [] => some s
  | s, l :: ls => (valStep K W s l).bind (fun s' => valRun K W s' ls)

/-- A start state: `c` is registered on L1 and has never left it. It settles on L1 with both L1
counters at `total` (as `L1BH:134` and `L1BH:316` leave them), it has never migrated
(`migrationNumber` 0) and interval 2 is uninitialized, no message is in flight and no diamond of
`c` on a settlement layer settles there; every batch executed so far was executed on L1; and every
other chain's open batch is past the batches of it L1 has executed. Interval 1 and the layers'
handler numbers are arbitrary (each is written before it is read). -/
def ValInit (W : ValWorld) (s : ValState) : Prop :=
  s.mn = 0 ∧ (s.ivs 2).sl = 0 ∧ s.awayL1 = false ∧ s.toSL = none ∧ s.toL1 = none ∧
  s.execL1 = s.total ∧ s.mrL1 W.c = s.total ∧
  (∀ t g, s.gcopy t = some g → g.active = false) ∧
  (∀ t, t ≠ W.c → t ≠ W.l1 → s.mrL1 t < s.slOpen t) ∧
  (∀ b, (s.hist b).isSome = true ↔ 1 ≤ b ∧ b ≤ s.total) ∧
  (∀ b r, s.hist b = some r → r.layer = W.l1)

/-! ## Witness data -/

/-- The witness world: L1 is chain 1, the migrating chain is 7, chain 5 is the only whitelisted
settlement layer, migrations enabled. -/
def wWorld : ValWorld := ⟨1, 7, fun t => decide (t = 5), true⟩

/-- The same world with migrations disabled, as at this commit (`CFG:320`). -/
def wWorldBanned : ValWorld := ⟨1, 7, fun t => decide (t = 5), false⟩

/-- A world in which chain 0 is whitelisted, violating `ValWorld.Ok`. -/
def wWorldZero : ValWorld := ⟨1, 7, fun t => decide (t = 0), true⟩

/-- A freshly created chain (`createNewChain`, `L1BH:134`): nothing executed, every layer's
open batch is 1, every L1 counter 0. -/
def wFresh : ValState where
  mn := 0
  ivs := fun _ => MigInterval.empty
  mrL1 := fun _ => 0
  execL1 := 0
  awayL1 := false
  slOpen := fun _ => 1
  gcopy := fun _ => none
  mnG := fun _ => 0
  toSL := none
  toL1 := none
  hist := fun _ => none
  total := 0

/-- The round trip of the witnesses: batches 1 and 2 on L1; layer 5 seals a batch and L1
executes it; `c` moves to layer 5 (lower bound 1); batch 3 runs in layer batch 2 and batch 4 in
layer batch 3; `c` burns back in layer batch 3; L1 executes layer batches 2 and 3; `c` returns
(upper bound 3); batch 5 runs on L1. -/
def wRoundTrip : List ValLabel :=
  [.execL1 1, .execL1 2, .slSeal 5, .slExecL1 5, .burnL1 5, .mintSL, .execSL 5 3, .slSeal 5,
    .execSL 5 4, .burnSL 5, .slSeal 5, .slExecL1 5, .slExecL1 5, .mintL1, .execL1 5]

end Contracts.L1ChainAssetHandler.SettlementLayerValidation
