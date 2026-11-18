import Mathlib.Tactic

/-!
# Model: one settlement layer's batch counters — each diamond's `totalBatchesExecuted` and the `MessageRoot`'s `currentChainBatchNumber`

Source: era-contracts `draft/v0.35.0` at `b17415d20` (the v35 head). Paths are relative to
`l1-contracts/contracts/`; every `file:line` is at that commit unless it names another one.
Abbreviations:

* `MRB` = `core/message-root/MessageRootBase.sol`, `L1MR` = `core/message-root/L1MessageRoot.sol`
* `Ex` = `state-transition/chain-deps/facets/Executor.sol`
* `Co` = `state-transition/chain-deps/facets/Committer.sol`
* `Base` = `state-transition/chain-deps/facets/ZKChainBase.sol`
* `Mig` = `state-transition/chain-deps/facets/Migrator.sol`
* `CAH` = `core/chain-asset-handler/ChainAssetHandlerBase.sol`,
  `L1CAH` = `core/chain-asset-handler/L1ChainAssetHandler.sol`
* `L1BH` = `core/bridgehub/L1Bridgehub.sol`, `BHB` = `core/bridgehub/BridgehubBase.sol`

**This file is definitions only.** The statements are in
`EraSpec.Protocol.BatchCounters.Properties.MessageRootSync` and are proved in
`EraSpec.Protocol.BatchCounters.Proofs.MessageRootSync`.

## Why the two counters must agree

`executeBatchesSharedBridge` (`Ex:170-212`) first appends every batch's L2 logs root to the
settlement layer's `MessageRoot` (`Ex:192-194`, through `_appendMessageRoot`, `Ex:163-166`):

    messageRootContract.addChainBatchRootV32(s.chainId, _batchNumber, _messageRoot);   // Ex:165

and `_recordChainBatchRoot` (`MRB:183-197`) accepts a batch only as the next one of its own
counter:

    require(_chainBatchRoot != bytes32(0), ChainBatchRootZero());                    // MRB:187
    require(chainBatchRoots[_chainId][_batchNumber] == bytes32(0), ...);           // MRB:188-191
    uint256 expectedNewChainBatchNumber = currentChainBatchNumber[_chainId] + 1;   // MRB:192
    require(_batchNumber == expectedNewChainBatchNumber, NonConsecutiveBatchNumber(...)); // MRB:193

Then the executor checks the same batch numbers against its own counter
(`Ex:66`: `currentBatchNumber != s.totalBatchesExecuted + _executedBatchIdx + 1` reverts). The
call succeeds only if both checks pass, so it can succeed only while
`currentChainBatchNumber[c] = totalBatchesExecuted`.

## State

`Hub` is one settlement layer: its `MessageRoot` (`MsgRoot`) and, per chain id, the diamond the
layer's bridgehub registers (`BHB.getZKChain`) with that diamond's batch-pipeline storage
(`Diamond`). `none` is "no diamond registered".

* `MsgRoot.reg c` is `chainRegistered(c)` (`MRB:159-161`) for chains other than the layer's
  own id; `cur` is `currentChainBatchNumber` (`MRB:84`), `roots` is `chainBatchRoots`
  (`MRB:90`).
* `Diamond` keeps `totalBatchesCommitted/Verified/Executed`, `storedBatchHashes`,
  `l2LogsRootHashes`, the two upgrade-transaction fields, and `away`, which is
  `s.settlementLayer != address(0)` (`state-transition/chain-deps/ZKChainStorage.sol:93-106,
  159-163, 218`).

## Steps: every writer of these fields at `b17415d20`

| step | source |
|---|---|
| `createChain` | `L1BH.createNewChain` (`L1BH:108-139`): `DiamondInit` (`chain-deps/DiamondInit.sol:122-126, 138`) and the genesis upgrade, then `addNewChain(c, 0)` (`L1BH:134`, `MRB:145-150`, `_addNewChain` `MRB:275-293`) and `seedGenesisRoot(c)` (`L1BH:135`, `MRB:296-314`) |
| `registerDeployed` | `L1BH.registerAlreadyDeployedZKChain` (`L1BH:285-319`): `addNewChain(c, getTotalBatchesExecuted())` (`L1BH:302, 316`) |
| `commit` | `commitBatchesSharedBridge` (`Co:72-111`), `_commitBatches` (`Co:113-157`), the batch-number check of `_commitOneBatch` (`Co:165-167`) |
| `prove` | `proveBatchesSharedBridge` (`Ex:215-251`) |
| `execute` | `executeBatchesSharedBridge` (`Ex:170-212`), `_executeOneBatch` (`Ex:86-114`), `_checkBatchData` (`Ex:59-79`), and per batch `addChainBatchRootV32` (`MRB:173-180`) |
| `revert` | `_revertBatches` (`Base:317-337`), reached by `revertBatchesSharedBridge` (`Ex:264-269`) and `activatePriorityMode` (`Admin.sol:550`) |
| `upgrade` | `BaseZkSyncUpgrade._upgrade` (`upgrades/BaseZkSyncUpgrade.sol:72-107`): the upgrade transaction hash is written only on a diamond that settles here (`:86, :102-104, :199`) |
| `burn` | `CAH.bridgeBurn` (`CAH:188-254`) → `Migrator.forwardedBridgeBurn` (`Mig:154-209`) and `prepareChainCommitment` (`Mig:339-375`); the mint data's batch number is `currentChainBatchNumber(c)` (`CAH:281`) |
| `mintExisting` | `CAH.bridgeMint` (`CAH:361-420`) for a registered chain: `setMigratingChainBatchNumber` (`CAH:414`, `MRB:153-157`), then `Migrator.forwardedBridgeMint(data, true)` (`Mig:213-305`) |
| `mintNew` | `CAH.bridgeMint` for an unregistered chain: the CTM deploys a fresh diamond (`ChainTypeManager.sol:746-758`, `_deployNewChain` `:674-692`), `addNewChain(c, batchNumber)` (`CAH:409`), then `forwardedBridgeMint(data, false)`; on L1 this reverts (`Mig:277-279`) |
| `confirmFailure` | `L1CAH.bridgeConfirmTransferResult` with `Failure` (`L1CAH:122-172`) → `Migrator.forwardedBridgeConfirmTransferResult` (`Mig:309-333`) |

`burn` and both mints carry `whenMigrationsEnabled` (`CAH:151-156, 201, 365`), which reads the
constant `CHAIN_MIGRATIONS_ENABLED = false` (`common/Config.sol:320`; `CAH:165-167`). That is
`HubConfig.migrationsEnabled`. `confirmFailure` is not gated (`L1CAH:119-120`).

`grep` at `b17415d20` finds no other writer: `chainBatchRoots` is written at `MRB:195, 311`,
`currentChainBatchNumber` at `MRB:156, 196, 282`, `totalBatchesExecuted` at `Ex:202` and
`Mig:240`, `l2LogsRootHashes` at `Ex:103` and `DiamondInit.sol:138`, `storedBatchHashes` at
`Co:136`, `Mig:265` and `DiamondInit.sol:126`, `settlementLayer` at `Mig:207, 299, 332`.
The only caller of `addChainBatchRoot*` is `Ex:165`; the only callers of `addNewChain` are
`L1BH:134, 316` and `CAH:409`; the only caller of `setMigratingChainBatchNumber` is `CAH:414`.

## Modelling choices

* **A revert is no step.** Each step is atomic: every entry point is `nonReentrant` or an
  owner/handler call, and the `MessageRoot` calls are external calls whose revert propagates.
* **Reject-only checks are omitted**, so the model has more runs than the source: callers and
  roles, pause flags, protocol versions, priority-queue and priority-tree checks, the
  dependency-root and priority-operation hashes, DA checks, timestamps, deposit pausing,
  migration numbers and the CTM checks of a migration, the interop-fee charge
  (`Ex:106-113`), proof verification, the chain-id/bridgehub checks of
  `registerAlreadyDeployedZKChain`, and the upgrade's version and "all batches executed"
  checks. Safety statements therefore hold for the source's runs too; enabledness statements
  (`ExecuteNeverRevertsInMessageRoot`) are relative to the kept checks.
* **`_pushChainBatchRoot`** (`MRB:201-220`: the chain tree, shared tree, timestamps and
  historical roots) is not modelled; it is taken not to revert for a registered chain, whose
  chain tree `_addNewChain` set up (`MRB:285`).
* **Hashes are uninterpreted.** `HubConfig.hash` is `StoredBatchHashing.hashStoredBatchInfo`;
  no property assumes anything about it.
* **Chain ids** are other than the layer's own (`BHB:501-503` refuses it), and the
  `MessageRoot` is initialized (`MRB:138-142`), so a chain added later gets a nonzero index
  and `chainRegistered` is `chainIndex[c] != 0`.
* **Counters are `ℕ`.** The checked additions `currentChainBatchNumber + 1` (`MRB:192`) and
  `totalBatchesExecuted + nBatches` (`Ex:201`) could only add reverts at `2^256`;
  `StoredBatchInfo.batchNumber` is a `uint64` (`chain-interfaces/IExecutor.sol:30`), which
  only adds reverts beyond `2^64` batches.
* **Fixed configuration.** A diamond cut or an upgrade that runs other code, or a
  `MessageRoot` implementation upgrade, can write any storage (`OPS-CONFIG`); neither is a
  step. `upgrade` is the in-tree engine's write.
* **Legacy chains.** At `b17415d20` nothing writes `v31UpgradeChainBatchNumber` or calls the
  old `saveV31UpgradeChainBatchNumber` (removed; `L1MR:35-46`). At `main` `70096e2ea` that
  function (`L1MessageRoot.sol:89-107` there) set `currentChainBatchNumber[c]` to the calling
  diamond's `getTotalBatchesExecuted()`, once, for a chain registered before v31; until then
  the counter of such a chain is `0`. `protocol-docs/chain-lifecycle.md:218-223` makes every
  chain's per-chain v31 upgrade a precondition of this release. The model starts from any
  state, so such a chain is a state in which `cur c = 0` and `executed > 0`.
-/

namespace Contracts.BatchCounters

/-- Chain ids (`uint256`). -/
abbrev ChainId := ℕ

/-- A `bytes32` value; `0` is `bytes32(0)`. -/
abbrev Word := ℕ

/-- Point update of a map. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (v : β) : α → β :=
  fun x => if x = a then v else f x

/-- `IExecutor.StoredBatchInfo` (`chain-interfaces/IExecutor.sol:29-39`), as far as this model
reads it: `batchNumber` and `l2LogsTreeRoot`. `rest` stands for the other seven fields, which
enter only through the hash. -/
structure BatchInfo where
  batchNumber : ℕ
  logsRoot : Word
  rest : ℕ

/-- One diamond's batch-pipeline storage (`ZKChainStorage.sol:93-106, 159-163, 218`). -/
structure Diamond where
  /-- `totalBatchesCommitted`. -/
  committed : ℕ
  /-- `totalBatchesVerified`. -/
  verified : ℕ
  /-- `totalBatchesExecuted`. -/
  executed : ℕ
  /-- `storedBatchHashes`. -/
  batchHash : ℕ → Word
  /-- `l2LogsRootHashes`. -/
  logsRoot : ℕ → Word
  /-- `settlementLayer != address(0)`: the chain settles elsewhere. -/
  away : Bool
  /-- `l2SystemContractsUpgradeTxHash`. -/
  upgradeTxHash : Word
  /-- `l2SystemContractsUpgradeBatchNumber`. -/
  upgradeBatch : ℕ

/-- `ZKChainCommitment` (`common/Config.sol:234-260`) without the priority-tree commitment, the
permanent-rollup flag and the deprecated precommitment. -/
structure Commitment where
  executed : ℕ
  verified : ℕ
  committed : ℕ
  upgradeTxHash : Word
  upgradeBatch : ℕ
  batchHashes : List Word

/-- The `MessageRootBase` storage this model keeps (`MRB:84, 90`, `chainRegistered` `MRB:159-161`). -/
structure MsgRoot where
  /-- `chainRegistered(c)`. -/
  reg : ChainId → Bool
  /-- `currentChainBatchNumber`. -/
  cur : ChainId → ℕ
  /-- `chainBatchRoots`. -/
  roots : ChainId → ℕ → Word

/-- One settlement layer: its message root, and per chain id the registered diamond. -/
structure Hub where
  mr : MsgRoot
  chains : ChainId → Option Diamond

/-- Per-layer configuration. -/
structure HubConfig where
  /-- `block.chainid == L1_CHAIN_ID`. -/
  isL1 : Bool
  /-- `_getChainMigrationsEnabled()` (`CAH:165-167`): `false` at `b17415d20`. -/
  migrationsEnabled : Bool
  /-- `StoredBatchHashing.hashStoredBatchInfo`. -/
  hash : BatchInfo → Word

/-! ## Diamond-side effects -/

/-- The storage `DiamondInit` writes (`DiamondInit.sol:122-126, 138`) on fresh storage, with the
upgrade transaction hash `g` the genesis upgrade installs (`0` for a migration deploy). -/
def initDiamond (genesisHash genesisRoot g : Word) : Diamond where
  committed := 0
  verified := 0
  executed := 0
  batchHash := upd (fun _ => 0) 0 genesisHash
  logsRoot := upd (fun _ => 0) 0 genesisRoot
  away := false
  upgradeTxHash := g
  upgradeBatch := 0

/-- `_commitBatches` for one batch (`Co:113-157`): store the new batch's hash at its number,
record the upgrade batch if an upgrade transaction is pending (`Co:105-108, 119-129`), and
count it (`Co:110`). -/
def commitEffect (H : BatchInfo → Word) (d : Diamond) (new : BatchInfo) : Diamond :=
  { d with
    batchHash := upd d.batchHash new.batchNumber (H new)
    committed := d.committed + 1
    upgradeBatch := if d.upgradeTxHash ≠ 0 ∧ d.upgradeBatch = 0 then new.batchNumber
      else d.upgradeBatch }

/-- `_revertBatches(n)` (`Base:317-337`). -/
def revertEffect (d : Diamond) (n : ℕ) : Diamond :=
  { d with
    committed := n
    verified := if n < d.verified then n else d.verified
    upgradeBatch := if n < d.upgradeBatch then 0 else d.upgradeBatch }

/-- The upgrade transaction write of `BaseZkSyncUpgrade` (`upgrades/BaseZkSyncUpgrade.sol:86,
102-104, 199`): only on a diamond that settles here. -/
def upgradeEffect (d : Diamond) (t : Word) : Diamond :=
  if d.away = true then d else { d with upgradeTxHash := t }

/-- `writeRoots f infos`: `f` with each batch's logs root written at its number, in order
(`Ex:103`, once per batch). -/
def writeRoots (f : ℕ → Word) : List BatchInfo → ℕ → Word
  | [] => f
  | b :: bs => writeRoots (upd f b.batchNumber b.logsRoot) bs

/-- What the executor's own checks require of a call (`Ex:170-212`): a nonempty list
(`BatchDecoder.sol:204-206`), a diamond settling here (`onlySettlementLayer`, `Base:141-146`),
consecutive batch numbers after `totalBatchesExecuted` (`Ex:66`), each info hashing to the
stored hash at its number (`Ex:69`, `Base:238-255`), and no more batches than are verified
(`Ex:201-205`). -/
def ExecGuard (H : BatchInfo → Word) (d : Diamond) (infos : List BatchInfo) : Prop :=
  infos ≠ [] ∧ d.away = false ∧
  infos.map BatchInfo.batchNumber = List.range' (d.executed + 1) infos.length ∧
  (∀ b ∈ infos, H b = d.batchHash b.batchNumber) ∧
  d.executed + infos.length ≤ d.verified

/-- The executor's writes (`Ex:103, 201-211`): the logs roots, the counter, and clearing a
finished upgrade. -/
def executeEffect (d : Diamond) (infos : List BatchInfo) : Diamond :=
  { d with
    executed := d.executed + infos.length
    logsRoot := writeRoots d.logsRoot infos
    upgradeTxHash := if d.upgradeBatch ≠ 0 ∧ d.upgradeBatch ≤ d.executed + infos.length then 0
      else d.upgradeTxHash
    upgradeBatch := if d.upgradeBatch ≠ 0 ∧ d.upgradeBatch ≤ d.executed + infos.length then 0
      else d.upgradeBatch }

/-- `prepareChainCommitment()` (`Mig:339-375`): the counters, the upgrade fields, and the
stored hashes of batches `executed .. committed`. -/
def prepare (d : Diamond) : Commitment where
  executed := d.executed
  verified := d.verified
  committed := d.committed
  upgradeTxHash := d.upgradeTxHash
  upgradeBatch := d.upgradeBatch
  batchHashes := (List.range (d.committed - d.executed + 1)).map fun i => d.batchHash (d.executed + i)

/-- `writeHashes f base l`: `f` with `l[i]` written at `base + i` (`Mig:263-266`). -/
def writeHashes (f : ℕ → Word) (base : ℕ) : List Word → ℕ → Word
  | [] => f
  | x :: xs => upd (writeHashes f (base + 1) xs) base x

/-- The consistency checks of `forwardedBridgeMint` on the commitment (`Mig:247-259`). -/
def MintShape (com : Commitment) : Prop :=
  com.executed ≤ com.verified ∧ com.verified ≤ com.committed ∧
  com.batchHashes.length = com.committed - com.executed + 1

/-- `forwardedBridgeMint`'s writes (`Mig:238-240, 263-266, 295-296, 299`): the counters and the
upgrade fields are copied from the commitment, the batch hashes are written from
`totalBatchesExecuted` on, and the diamond settles here again. Nothing is compared with the
diamond's previous values. -/
def mintApply (d : Diamond) (com : Commitment) : Diamond :=
  { d with
    committed := com.committed
    verified := com.verified
    executed := com.executed
    batchHash := writeHashes d.batchHash com.executed com.batchHashes
    upgradeTxHash := com.upgradeTxHash
    upgradeBatch := com.upgradeBatch
    away := false }

/-! ## `MessageRoot` side -/

/-- `_recordChainBatchRoot(c, n, r)` (`MRB:183-197`). -/
def recordRoot (m : MsgRoot) (c : ChainId) (n : ℕ) (r : Word) : Option MsgRoot :=
  if m.reg c = true ∧ r ≠ 0 ∧ m.roots c n = 0 ∧ n = m.cur c + 1 then
    some { m with roots := upd m.roots c (upd (m.roots c) n r), cur := upd m.cur c n }
  else none

/-- The executor's append loop (`Ex:192-194`): one `addChainBatchRootV32` per batch, in order. -/
def appendAll (m : MsgRoot) (c : ChainId) : List BatchInfo → Option MsgRoot
  | [] => some m
  | b :: bs =>
    match recordRoot m c b.batchNumber b.logsRoot with
    | none => none
    | some m' => appendAll m' c bs

/-! ## Steps -/

/-- What happens on one layer. Each label names its chain. -/
inductive HubLabel
  /-- `createNewChain(c)` with the release's genesis batch hash, genesis logs root and genesis
  upgrade transaction hash. -/
  | createChain (c : ChainId) (genesisHash genesisRoot genesisTx : Word)
  /-- `registerAlreadyDeployedZKChain(c, d)`. -/
  | registerDeployed (c : ChainId) (d : Diamond)
  /-- `commitBatchesSharedBridge` of one batch: the last committed batch's info and the new
  batch's stored info. -/
  | commit (c : ChainId) (prev new : BatchInfo)
  /-- `proveBatchesSharedBridge`, verifying up to `v`. -/
  | prove (c : ChainId) (v : ℕ)
  /-- `executeBatchesSharedBridge` of these stored infos. -/
  | execute (c : ChainId) (infos : List BatchInfo)
  /-- `_revertBatches(n)`. -/
  | revert (c : ChainId) (n : ℕ)
  /-- An in-tree upgrade with upgrade transaction hash `t`. -/
  | upgrade (c : ChainId) (t : Word)
  /-- `bridgeBurn`: the mint data's batch number and commitment. -/
  | burn (c : ChainId) (bn : ℕ) (com : Commitment)
  /-- `bridgeMint` of a chain registered here. -/
  | mintExisting (c : ChainId) (bn : ℕ) (com : Commitment)
  /-- `bridgeMint` of a chain not registered here, with the deployed diamond's genesis hash and
  logs root. -/
  | mintNew (c : ChainId) (bn : ℕ) (com : Commitment) (genesisHash genesisRoot : Word)
  /-- `bridgeConfirmTransferResult(Failure)`. -/
  | confirmFailure (c : ChainId)

/-- The chain a label acts on. -/
def HubLabel.chain : HubLabel → ChainId
  | .createChain c .. => c
  | .registerDeployed c _ => c
  | .commit c .. => c
  | .prove c _ => c
  | .execute c _ => c
  | .revert c _ => c
  | .upgrade c _ => c
  | .burn c .. => c
  | .mintExisting c .. => c
  | .mintNew c .. => c
  | .confirmFailure c => c

/-- The migration labels. -/
def HubLabel.isMigration : HubLabel → Bool
  | .burn .. => true
  | .mintExisting .. => true
  | .mintNew .. => true
  | .confirmFailure _ => true
  | _ => false

/-- The mint data is consistent: its batch number equals the commitment's
`totalBatchesExecuted`. Data produced by `burn` on a synced chain is (`BurnDataConsistent`). -/
def HubLabel.MintConsistent : HubLabel → Prop
  | .mintExisting _ bn com => bn = com.executed
  | .mintNew _ bn com _ _ => bn = com.executed
  | _ => True

/-- One step on a layer. -/
inductive HubStep (cfg : HubConfig) : Hub → HubLabel → Hub → Prop
  /-- `L1BH:108-139`: only on L1 (`L2Bridgehub` has no `createNewChain`); the chain has no
  CTM entry (`BHB:534-536`) and is not in the message root (`MRB:146-148`); `DiamondInit`
  refuses a zero genesis hash (`DiamondInit.sol:122-125`); `seedGenesisRoot` refuses a zero
  logs root (`MRB:302-303`) and a batch-0 slot already written (`MRB:309`; its counter check
  `MRB:308` holds after `addNewChain(c, 0)`). -/
  | createChain {h : Hub} {c : ChainId} {gh gr g : Word} :
      cfg.isL1 = true → h.chains c = none → h.mr.reg c = false → gh ≠ 0 → gr ≠ 0 →
      h.mr.roots c 0 = 0 →
      HubStep cfg h (.createChain c gh gr g)
        { mr := { reg := upd h.mr.reg c true, cur := upd h.mr.cur c 0,
                  roots := upd h.mr.roots c (upd (h.mr.roots c) 0 gr) },
          chains := upd h.chains c (some (initDiamond gh gr g)) }
  /-- `L1BH:285-319`: only on L1; not registered (`L1BH:290-293`, `MRB:146-148`). The
  diamond's storage is whatever it is. -/
  | registerDeployed {h : Hub} {c : ChainId} {d : Diamond} :
      cfg.isL1 = true → h.chains c = none → h.mr.reg c = false →
      HubStep cfg h (.registerDeployed c d)
        { mr := { h.mr with reg := upd h.mr.reg c true, cur := upd h.mr.cur c d.executed },
          chains := upd h.chains c (some d) }
  /-- `Co:72-111`: settling here (`Co:77`), the previous info hashes to the stored hash at
  `totalBatchesCommitted` (`Co:103`), and the new batch number follows it (`Co:165-167`). -/
  | commit {h : Hub} {c : ChainId} {d : Diamond} {prev new : BatchInfo} :
      h.chains c = some d → d.away = false → cfg.hash prev = d.batchHash d.committed →
      new.batchNumber = prev.batchNumber + 1 →
      HubStep cfg h (.commit c prev new)
        { h with chains := upd h.chains c (some (commitEffect cfg.hash d new)) }
  /-- `Ex:215-251`: settling here (`Ex:220`), at least one batch (`BatchDecoder.sol:147-148`),
  not beyond the committed ones (`Ex:243-245`). -/
  | prove {h : Hub} {c : ChainId} {d : Diamond} {v : ℕ} :
      h.chains c = some d → d.away = false → d.verified < v → v ≤ d.committed →
      HubStep cfg h (.prove c v) { h with chains := upd h.chains c (some { d with verified := v }) }
  /-- `Ex:170-212` with the message root's checks on every appended batch. -/
  | execute {h : Hub} {c : ChainId} {d : Diamond} {infos : List BatchInfo} {m' : MsgRoot} :
      h.chains c = some d → ExecGuard cfg.hash d infos → appendAll h.mr c infos = some m' →
      HubStep cfg h (.execute c infos)
        { mr := m', chains := upd h.chains c (some (executeEffect d infos)) }
  /-- `Base:317-337`: settling here (`Ex:267`, `Admin.sol:524`), not before the executed
  batches and not after the committed ones (`Base:318-323`). -/
  | revert {h : Hub} {c : ChainId} {d : Diamond} {n : ℕ} :
      h.chains c = some d → d.away = false → d.executed ≤ n → n ≤ d.committed →
      HubStep cfg h (.revert c n) { h with chains := upd h.chains c (some (revertEffect d n)) }
  /-- An in-tree upgrade of a registered diamond. -/
  | upgrade {h : Hub} {c : ChainId} {d : Diamond} {t : Word} :
      h.chains c = some d →
      HubStep cfg h (.upgrade c t) { h with chains := upd h.chains c (some (upgradeEffect d t)) }
  /-- `CAH:188-300`: migrations enabled (`CAH:201`); the diamond settles here (`Mig:162-164`)
  and has executed every committed batch (`Mig:203-205`); `prepareChainCommitment`'s checks
  (`Mig:351-362`). The data carries the message root's counter (`CAH:281`) and the commitment
  (`Mig:208`). -/
  | burn {h : Hub} {c : ChainId} {d : Diamond} :
      cfg.migrationsEnabled = true → h.chains c = some d → d.away = false →
      d.committed = d.executed → d.executed ≤ d.verified → d.verified ≤ d.committed →
      HubStep cfg h (.burn c (h.mr.cur c) (prepare d))
        { h with chains := upd h.chains c (some { d with away := true }) }
  /-- `CAH:361-420` for a registered chain: migrations enabled (`CAH:365`); the counter may not
  move back (`MRB:155`); the commitment's shape (`Mig:247-259`); the diamond is away
  (`Mig:280-282` on L1, `:285-287` elsewhere). -/
  | mintExisting {h : Hub} {c : ChainId} {d : Diamond} {bn : ℕ} {com : Commitment} :
      cfg.migrationsEnabled = true → h.chains c = some d → h.mr.cur c ≤ bn → MintShape com →
      d.away = true →
      HubStep cfg h (.mintExisting c bn com)
        { mr := { h.mr with cur := upd h.mr.cur c bn },
          chains := upd h.chains c (some (mintApply d com)) }
  /-- `CAH:361-420` for an unregistered chain: migrations enabled; not on L1 (`Mig:277-279`);
  no diamond (`CAH:397`) and not in the message root (`MRB:146-148`); `DiamondInit`'s check;
  the commitment's shape. -/
  | mintNew {h : Hub} {c : ChainId} {bn : ℕ} {com : Commitment} {gh gr : Word} :
      cfg.migrationsEnabled = true → cfg.isL1 = false → h.chains c = none → h.mr.reg c = false →
      gh ≠ 0 → MintShape com →
      HubStep cfg h (.mintNew c bn com gh gr)
        { mr := { h.mr with reg := upd h.mr.reg c true, cur := upd h.mr.cur c bn },
          chains := upd h.chains c (some (mintApply (initDiamond gh gr 0) com)) }
  /-- `L1CAH:122-172` with `Failure`: only on L1, not gated by `whenMigrationsEnabled`; the
  diamond is away (`Mig:324-326`). -/
  | confirmFailure {h : Hub} {c : ChainId} {d : Diamond} :
      cfg.isL1 = true → h.chains c = some d → d.away = true →
      HubStep cfg h (.confirmFailure c)
        { h with chains := upd h.chains c (some { d with away := false }) }

/-- A sequence of steps. -/
inductive HubRun (cfg : HubConfig) : Hub → List HubLabel → Hub → Prop
  | nil {h : Hub} : HubRun cfg h [] h
  | cons {h h' h'' : Hub} {l : HubLabel} {ls : List HubLabel} :
      HubStep cfg h l h' → HubRun cfg h' ls h'' → HubRun cfg h (l :: ls) h''

/-! ## The invariant and the agreement -/

/-- The layer's chain-independent invariant.

* `regIff`: the message root registers exactly the chains the bridgehub does.
* `unregZero`: an unregistered chain has no batch root.
* `frontier`: no batch after `currentChainBatchNumber` has a root — the "expected invariant"
  of the NatSpec at `MRB:89`.
* `rootsAgree`: every nonzero batch root of a registered chain is the diamond's
  `l2LogsRootHashes` entry for that batch. -/
structure HubInv (h : Hub) : Prop where
  regIff : ∀ c, h.mr.reg c = true ↔ h.chains c ≠ none
  unregZero : ∀ c n, h.mr.reg c = false → h.mr.roots c n = 0
  frontier : ∀ c n, h.mr.cur c < n → h.mr.roots c n = 0
  rootsAgree : ∀ c d n, h.chains c = some d → h.mr.roots c n ≠ 0 → h.mr.roots c n = d.logsRoot n

/-- Chain `c`'s two counters agree: `currentChainBatchNumber[c] = totalBatchesExecuted` of its
diamond (vacuous while no diamond is registered). -/
def Synced (h : Hub) (c : ChainId) : Prop :=
  ∀ d, h.chains c = some d → h.mr.cur c = d.executed

/-- The layer before any chain: nothing registered. -/
def emptyHub : Hub where
  mr := { reg := fun _ => false, cur := fun _ => 0, roots := fun _ _ => 0 }
  chains := fun _ => none

/-- The batch numbers a run executes for chain `c`, in order. -/
def execNumbers (c : ChainId) : List HubLabel → List ℕ
  | [] => []
  | .execute c' infos :: ls =>
    (if c' = c then infos.map BatchInfo.batchNumber else []) ++ execNumbers c ls
  | _ :: ls => execNumbers c ls

/-! ## Witness data -/

/-- A concrete stand-in for the stored-batch hash, used only by the witnesses. -/
def wHash (b : BatchInfo) : Word := 1000 * b.batchNumber + b.logsRoot + b.rest + 1

/-- The configuration at `b17415d20` on L1: migrations disabled. -/
def headL1 : HubConfig := { isL1 := true, migrationsEnabled := false, hash := wHash }

/-- The genesis batch's info of the witness chains: batch 0, logs root `12`. -/
def wInfo0 : BatchInfo := { batchNumber := 0, logsRoot := 12, rest := 0 }

/-- The stored infos of the witness batches: batch `n` has logs root `20 + n`. -/
def wInfo (n : ℕ) : BatchInfo := { batchNumber := n, logsRoot := 20 + n, rest := 0 }

/-- The stored info of a batch 1 that a witness commits and then reverts: logs root `31`. -/
def wInfoReverted : BatchInfo := { batchNumber := 1, logsRoot := 31, rest := 0 }

/-- A diamond registered before v31 that never saved its v31 batch number: it has executed
five batches, committed and verified a sixth, and settles here. -/
def wLegacyDiamond : Diamond where
  committed := 6
  verified := 6
  executed := 5
  batchHash := upd (fun _ => 0) 6 (wHash (wInfo 6))
  logsRoot := fun _ => 0
  away := false
  upgradeTxHash := 0
  upgradeBatch := 0

/-- The already-deployed diamond of the witness: seven batches executed, an eighth committed
and verified. -/
def wDeployed : Diamond where
  committed := 8
  verified := 8
  executed := 7
  batchHash := upd (fun _ => 0) 8 (wHash (wInfo 8))
  logsRoot := fun _ => 0
  away := false
  upgradeTxHash := 0
  upgradeBatch := 0

/-- A layer whose only chain, `7`, is that legacy diamond: registered, counter `0`, no roots. -/
def wLegacyHub : Hub where
  mr := { reg := upd (fun _ => false) 7 true, cur := fun _ => 0, roots := fun _ _ => 0 }
  chains := upd (fun _ => none) 7 (some wLegacyDiamond)

end Contracts.BatchCounters
