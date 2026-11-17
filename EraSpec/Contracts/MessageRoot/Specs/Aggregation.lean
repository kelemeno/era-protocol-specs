import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `MessageRootBase` — chain trees, the shared tree, and the historical roots

Source: `l1-contracts/contracts/core/message-root/MessageRootBase.sol` in the pinned era-contracts
tree (`c67894b970a0dac6fe9144d8ebf4b0806e15a9af`), with `L1MessageRoot.sol`,
`common/libraries/MessageHashing.sol`, `core/bridgehub/L1Bridgehub.sol` and
`core/chain-asset-handler/ChainAssetHandlerBase.sol` from the same tree. A bare `:N` is a line of
`MessageRootBase.sol`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.MessageRoot.Properties.Aggregation` and are proved in
`EraSpec.Contracts.MessageRoot.Proofs.Aggregation`.

## Why this contract matters to the timeout protocol

`Contracts.Timeout.Aggregates` — "a batch that had settled by the time a settlement-layer root
was created is inside that root" — is the last load-bearing premise behind the timeout and
refund headlines (`Protocol/InteropAtomicity/Specs/Timeout.lean`, which says it "is not derived
here"). The settlement layer that supplies it is this contract: every settled batch root is pushed
into its chain's tree with `l1Timestamp = block.timestamp`, the chain's root is written into the
shared tree, and the shared root is recorded per block together with `block.timestamp`. The
timeout path reads that `(root, timestamp)` pair, imported into `L2InteropRootStorage` and
double-checked by the Executor. This file models the settlement-layer half.

## The code

    // _pushChainBatchRoot (:247-271), the interop half of the v32 flow
    uint256 l1Timestamp = block.timestamp;                                          // :251
    chainBatchRootTimestamp[_chainId][_batchNumber] = l1Timestamp;                  // :252
    (, chainRoot) = chainTree[_chainId].push(
        MessageHashing.batchLeafHash(_chainBatchRoot, _batchNumber, l1Timestamp));  // :257-259
    bytes32 cachedChainIdLeafHash =
        MessageHashing.chainIdLeafHash(chainRoot, _chainId);                         // :264
    bytes32 sharedTreeRoot =
        sharedTree.updateLeaf(chainIndex[_chainId], cachedChainIdLeafHash);          // :265
    _emitRoot(sharedTreeRoot);
    _recordHistoricalRoot(sharedTreeRoot);                                          // :270

    // _recordHistoricalRoot (:275-277)
    historicalRoots[block.number] =
        StoredInteropRoot({root: _sharedTreeRoot, timestamp: block.timestamp});      // :276

    // _recordChainBatchRoot (:228-243), shared by both add-chain-batch-root flows
    if (!chainRegistered(_chainId)) revert MessageRootNotRegistered();              // :230-232
    require(_chainBatchRoot != bytes32(0), ChainBatchRootZero());                   // :233
    require(chainBatchRoots[_chainId][_batchNumber] == bytes32(0), ...);            // :234-237
    uint256 expectedNewChainBatchNumber = currentChainBatchNumber[_chainId] + 1;    // :238
    require(_batchNumber == expectedNewChainBatchNumber, NonConsecutiveBatchNumber(...)); // :239
    chainBatchRoots[_chainId][_batchNumber] = _chainBatchRoot;                      // :241
    currentChainBatchNumber[_chainId] = expectedNewChainBatchNumber;                // :242

    // addChainBatchRoot (:199-205): record ONLY (the v31 flow)
    // addChainBatchRootV32 (:217-224): record, then _pushChainBatchRoot

    // _addNewChain (:339-358)
    ++chainCount; chainIndex[_chainId] = cachedChainCount;                          // :344-345
    chainIndexToId[cachedChainCount] = _chainId;                                    // :346
    currentChainBatchNumber[_chainId] = _startingBatchNumber;                       // :347
    chainTree[_chainId].setup(CHAIN_TREE_EMPTY_ENTRY_HASH);                         // :350
    sharedTree.pushNewLeaf(MessageHashing.chainIdLeafHash(bytes32(0), _chainId));   // :352
    _emitRoot(sharedTreeRoot); _recordHistoricalRoot(sharedTreeRoot);               // :356-357

    // seedGenesisRoot (:364-387): genesis root r = zkChain.l2LogsRootHash(0) of a ZKsync OS chain
    require(r != 0); registered; require(currentChainBatchNumber[_chainId] == 0);   // :374-380
    require(chainBatchRoots[_chainId][0] == bytes32(0));                            // :381
    chainBatchRoots[_chainId][0] = r; _pushChainBatchRoot(_chainId, 0, r);          // :383-386

    // setMigratingChainBatchNumber (:178-183), onlyChainAssetHandler, no registration check
    require(currentChainBatchNumber[_chainId] <= _batchNumber, ...);                // :181
    currentChainBatchNumber[_chainId] = _batchNumber;                               // :182

`chainRegistered(c)` is `c == block.chainid || chainIndex[c] != 0` (:185-187), and `_initialize`
(:162-166) sets the shared tree up and registers `block.chainid` at index 0.

## The inventory the model rests on (checked against the pinned tree)

* `historicalRoots` (:86) has one writer, `_recordHistoricalRoot` (:276), called from
  `_pushChainBatchRoot` (:270) and `_addNewChain` (:357). It is keyed by `block.number`, so a later
  write in the same block overwrites an earlier one.
* `chainTree[c]` (:69) is written by `_addNewChain` (`setup`, :350) and `_pushChainBatchRoot`
  (`push`, :257); `sharedTree` (:64) by `_initialize` (`setup`, :164), `_addNewChain`
  (`pushNewLeaf`, :352) and `_pushChainBatchRoot` (`updateLeaf`, :265).
* `chainBatchRoots` (:101) is written at :241 and :383, both guarded by "still zero";
  `chainBatchRootTimestamp` (:108) only at :252.
* `currentChainBatchNumber` (:95) is written at :182, :242, :347, and by
  `L1MessageRoot.saveV31UpgradeChainBatchNumber` (`L1MessageRoot.sol:99-117`: it writes
  `totalBatchesExecuted` under `require(currentChainBatchNumber[_chainId] == 0)`, :113-115). On the
  modelled state that last writer is a `setMigratingChainBatchNumber` step (its guard implies
  `current ≤ n`), so it is covered by that constructor.
* Callers: `addNewChain` is `onlyBridgehubOrChainAssetHandler` (:170); the Bridgehub registers a
  fresh chain at start 0 and seeds it (`L1Bridgehub.sol:141-142`), and onboards an existing chain
  at `getTotalBatchesExecuted()` (`L1Bridgehub.sol:309, 323`); the chain asset handler registers a
  migrating chain at its batch number or moves a returning chain's number with
  `setMigratingChainBatchNumber` (`ChainAssetHandlerBase.sol:380, 386`).

## Modelling choices

* **One MessageRoot contract**, deployed on chain `Params.self` (`block.chainid`).
* **Hashes are abstract functions** (`Hashes`), with no premise. `chainRoot` is the root
  `DynamicIncrementalMerkle.push` returns over the leaf hashes pushed so far and `sharedRoot` the
  root `FullMerkle` returns over its leaf list; that the libraries compute these folds is the
  separate correspondence `MODEL-DIM` (backlog W-MER-2) and A1's `FullMerkle` results.
* **A chain tree is the list of its pushed leaves, with their preimages** (`Leaf`): batch number,
  batch root, `l1Timestamp`, and a ghost field `blk`, the `block.number` of the push. Positions in
  that list are the tree's leaf indices.
* **A historical root carries a ghost count** (`HistEntry.count`): how many leaves each chain tree
  had when it was written. That is what the root aggregates; inclusion proofs against the root
  value are a separate binding question (W-MER-5).
* **The block is environment.** `nextBlock` advances `block.number` by one with a new
  `block.timestamp`, under one of two premises (`TsRule`): non-decreasing (`mono`) or strictly
  increasing (`strict`). Several transactions may run in one block.
* **A revert is the absence of a step**, and **caller checks are omitted** (they only reject, so
  omitting them adds runs and every safety result holds a fortiori). Also omitted: events and
  `interopRootLogId` (:288-303), message verification (:393-452), `v31UpgradeChainBatchNumber`
  (`L1MessageRoot.sol:54`), and `seedGenesisRoot`'s no-op branch for non-ZKsync-OS chains
  (:369-371).
* **Runs start at `_initialize`** (`init`), at any block and timestamp. A MessageRoot upgraded in
  place without `_initialize` (`L1MessageRoot.initializeL1V31Upgrade`, :86-89) starts elsewhere and
  is not covered.

## Pushed positions, not batch numbers

A chain's `n`-th leaf is not its batch `n`. A chain onboarded at a nonzero start (no genesis
leaf) pushes batch `start + 1` as leaf 0; `setMigratingChainBatchNumber` jumps the batch number
forward with no leaf; and a record-only batch (`addChainBatchRoot`, the v31 entry point) advances
the batch number without a leaf. So the clock the timeout protocol needs is indexed by **pushed
position**: `State.leafTime c i` is the `l1Timestamp` of chain `c`'s `i`-th leaf.
-/

namespace Contracts.MessageRoot

/-- `bytes32` and `uint256` words. -/
abbrev Word := UInt256

/-- Chain ids, as `uint256` (the same type as `Contracts.Atomicity.Chain`). -/
abbrev ChainId := UInt256

/-! ## Hashes and deployment -/

/-- The four hashes `MessageRootBase` composes. Abstract: no injectivity or other premise. -/
structure Hashes where
  /-- `MessageHashing.batchLeafHash(batchRoot, batchNumber, l1Timestamp)`
  (`MessageHashing.sol:78-84`). -/
  batchLeaf : Word → ℕ → ℕ → Word
  /-- `MessageHashing.chainIdLeafHash(chainRoot, chainId)` (`MessageHashing.sol:89-91`). -/
  chainIdLeaf : Word → ChainId → Word
  /-- The root `chainTree[c].push` returns (:257), over all leaf hashes pushed so far. -/
  chainRoot : List Word → Word
  /-- The root `sharedTree.pushNewLeaf` / `updateLeaf` return (:265, :352), over the leaf list. -/
  sharedRoot : List Word → Word

/-- The deployment constants. -/
structure Params where
  /-- `block.chainid` of the chain the contract is deployed on; registered at index 0 (:165). -/
  self : ChainId
  /-- The hashes. -/
  H : Hashes

/-! ## State -/

/-- One leaf of a chain tree, with its preimage: what `_pushChainBatchRoot` hashed (:257-259). -/
structure Leaf where
  /-- `_batchNumber`. -/
  batch : ℕ
  /-- `_chainBatchRoot`. -/
  root : Word
  /-- `l1Timestamp = block.timestamp` at the push (:251). -/
  ts : ℕ
  /-- Ghost: `block.number` at the push. The contract does not store it. -/
  blk : ℕ
deriving DecidableEq

/-- The leaf hash the chain tree stores (:258). -/
def Leaf.hash (H : Hashes) (l : Leaf) : Word := H.batchLeaf l.root l.batch l.ts

/-- One `historicalRoots[blockNumber]` entry (:86, `StoredInteropRoot`, `Messaging.sol:170-173`),
plus the ghost count of what it aggregated. -/
structure HistEntry where
  /-- `root`: the shared tree root when it was written. -/
  root : Word
  /-- `timestamp`: `block.timestamp` when it was written (:276). -/
  ts : ℕ
  /-- Ghost: the number of leaves of each chain tree when it was written. -/
  count : ChainId → ℕ

/-- The contract's state, the block it runs in, and the ghost fields. -/
structure State where
  /-- `block.number`. -/
  block : ℕ
  /-- `block.timestamp`. -/
  time : ℕ
  /-- `chainCount` (:54). -/
  chainCount : ℕ
  /-- `chainIndex` (:57). -/
  chainIndex : ChainId → ℕ
  /-- `chainIndexToId` (:60). -/
  chainIndexToId : ℕ → ChainId
  /-- `currentChainBatchNumber` (:95). -/
  current : ChainId → ℕ
  /-- `chainBatchRoots` (:101); `0` is "none". -/
  batchRoot : ChainId → ℕ → Word
  /-- `chainBatchRootTimestamp` (:108); `0` is "none". -/
  batchTs : ChainId → ℕ → ℕ
  /-- `chainTree[c]` (:69), as its pushed leaves, oldest first. -/
  leaves : ChainId → List Leaf
  /-- `sharedTree` (:64), as its leaf list in index order. -/
  shared : List Word
  /-- `historicalRoots` (:86); `none` is the default `(0, 0)`. -/
  hist : ℕ → Option HistEntry

/-- `chainRegistered(c)` (:185-187). -/
def State.Registered (P : Params) (st : State) (c : ChainId) : Prop :=
  c = P.self ∨ st.chainIndex c ≠ 0

/-- The `(root, timestamp)` pair `historicalRoot(b)` returns (:281-283). -/
def State.historicalRoot (st : State) (b : ℕ) : Word × ℕ :=
  match st.hist b with
  | some e => (e.root, e.ts)
  | none => (0, 0)

/-- The chain root a chain's shared-tree leaf commits to: `bytes32(0)` while the tree is empty
(:352), else the root `push` returned for its leaves (:257, :264). -/
def chainRootVal (H : Hashes) : List Leaf → Word
  | [] => 0
  | ls => H.chainRoot (ls.map (Leaf.hash H))

/-! ## Effects -/

/-- `_recordHistoricalRoot` after a tree update (:275-277): the current shared root, the current
timestamp, and (ghost) the current chain-tree sizes. -/
def State.writeHist (P : Params) (st : State) : State :=
  let e : HistEntry := ⟨P.H.sharedRoot st.shared, st.time, fun c => (st.leaves c).length⟩
  { st with hist := Function.update st.hist st.block (some e) }

/-- `_addNewChain(c, start)` (:339-358). -/
def State.addChain (P : Params) (st : State) (c : ChainId) (start : ℕ) : State :=
  State.writeHist P
    { st with
      chainCount := st.chainCount + 1
      chainIndex := Function.update st.chainIndex c st.chainCount
      chainIndexToId := Function.update st.chainIndexToId st.chainCount c
      current := Function.update st.current c start
      leaves := Function.update st.leaves c []
      shared := st.shared ++ [P.H.chainIdLeaf 0 c] }

/-- `chainBatchRoots[c][b] = r` (:241, :383). -/
def State.setBatchRoot (st : State) (c : ChainId) (b : ℕ) (r : Word) : State :=
  { st with batchRoot := Function.update st.batchRoot c (Function.update (st.batchRoot c) b r) }

/-- The effect of `_recordChainBatchRoot(c, b, r)` once its checks pass (:241-242). -/
def State.record (st : State) (c : ChainId) (b : ℕ) (r : Word) : State :=
  { st.setBatchRoot c b r with current := Function.update st.current c b }

/-- The leaf `_pushChainBatchRoot(c, b, r)` pushes in state `st` (:251, :257-259). -/
def State.newLeaf (st : State) (b : ℕ) (r : Word) : Leaf := ⟨b, r, st.time, st.block⟩

/-- `_pushChainBatchRoot(c, b, r)` (:247-271). -/
def State.push (P : Params) (st : State) (c : ChainId) (b : ℕ) (r : Word) : State :=
  let ls := st.leaves c ++ [st.newLeaf b r]
  State.writeHist P
    { st with
      batchTs := Function.update st.batchTs c (Function.update (st.batchTs c) b st.time)
      leaves := Function.update st.leaves c ls
      shared := st.shared.set (st.chainIndex c) (P.H.chainIdLeaf (chainRootVal P.H ls) c) }

/-- `seedGenesisRoot(c)` with genesis root `r` once its checks pass (:383-386). -/
def State.seed (P : Params) (st : State) (c : ChainId) (r : Word) : State :=
  (st.setBatchRoot c 0 r).push P c 0 r

/-- `setMigratingChainBatchNumber(c, b)` once its check passes (:182). -/
def State.migrate (st : State) (c : ChainId) (b : ℕ) : State :=
  { st with current := Function.update st.current c b }

/-- A new block with timestamp `τ`. -/
def State.advance (st : State) (τ : ℕ) : State :=
  { st with block := st.block + 1, time := τ }

/-! ## Guards -/

/-- The checks of `_recordChainBatchRoot(c, b, r)` (:230-239). -/
structure RecordGuard (P : Params) (st : State) (c : ChainId) (b : ℕ) (r : Word) : Prop where
  /-- `MessageRootNotRegistered` (:230-232). -/
  registered : st.Registered P c
  /-- `ChainBatchRootZero` (:233). -/
  nonzero : r ≠ 0
  /-- `ChainBatchRootAlreadyExists` (:234-237). -/
  fresh : st.batchRoot c b = 0
  /-- `NonConsecutiveBatchNumber` (:238-239). -/
  consecutive : b = st.current c + 1

/-- The checks of `seedGenesisRoot(c)` with genesis root `r` (:374-381). -/
structure SeedGuard (P : Params) (st : State) (c : ChainId) (r : Word) : Prop where
  /-- `ChainBatchRootZero` (:374). -/
  nonzero : r ≠ 0
  /-- `MessageRootNotRegistered` (:375-377). -/
  registered : st.Registered P c
  /-- `NonConsecutiveBatchNumber(_chainId, 0)` (:380). -/
  atGenesis : st.current c = 0
  /-- `ChainBatchRootAlreadyExists(_chainId, 0)` (:381). -/
  unseeded : st.batchRoot c 0 = 0

/-- How `block.timestamp` moves from one block to the next. -/
inductive TsRule
  /-- Non-decreasing (`MonoTs`): equal timestamps across blocks are allowed. -/
  | mono
  /-- Strictly increasing (`StrictTs`). -/
  | strict
deriving DecidableEq

/-- The timestamps a new block may have, after a block with timestamp `τ`. -/
def TsRule.Allows : TsRule → ℕ → ℕ → Prop
  | .mono, τ, τ' => τ ≤ τ'
  | .strict, τ, τ' => τ < τ'

/-! ## Runs -/

/-- One transaction that changes the modelled state, or a new block. -/
inductive Step (P : Params) (r : TsRule) : State → State → Prop
  /-- `addNewChain(c, start)` (:170-175): `ChainExists` unless unregistered. -/
  | addNewChain {st : State} (c : ChainId) (start : ℕ) :
      ¬ st.Registered P c → Step P r st (st.addChain P c start)
  /-- `seedGenesisRoot(c)` of a ZKsync OS chain whose genesis root is `g` (:364-387). -/
  | seedGenesisRoot {st : State} (c : ChainId) (g : Word) :
      SeedGuard P st c g → Step P r st (st.seed P c g)
  /-- `addChainBatchRoot(c, b, root)` (:199-205): record only, no push. -/
  | addChainBatchRoot {st : State} (c : ChainId) (b : ℕ) (root : Word) :
      RecordGuard P st c b root → Step P r st (st.record c b root)
  /-- `addChainBatchRootV32(c, b, root)` (:217-224): record, then push. -/
  | addChainBatchRootV32 {st : State} (c : ChainId) (b : ℕ) (root : Word) :
      RecordGuard P st c b root → Step P r st ((st.record c b root).push P c b root)
  /-- `setMigratingChainBatchNumber(c, b)` (:178-183); also `saveV31UpgradeChainBatchNumber`. -/
  | setMigratingChainBatchNumber {st : State} (c : ChainId) (b : ℕ) :
      st.current c ≤ b → Step P r st (st.migrate c b)
  /-- A new block, with a timestamp the rule allows. -/
  | nextBlock {st : State} (τ : ℕ) : r.Allows st.time τ → Step P r st (st.advance τ)

/-- Reachability. -/
inductive Reach (P : Params) (r : TsRule) : State → State → Prop
  | refl {st : State} : Reach P r st st
  | tail {st st' st'' : State} : Reach P r st st' → Step P r st' st'' → Reach P r st st''

/-- Storage before `_initialize`, in block `b0` at timestamp `τ0`. -/
def blank (b0 τ0 : ℕ) : State where
  block := b0
  time := τ0
  chainCount := 0
  chainIndex := fun _ => 0
  chainIndexToId := fun _ => 0
  current := fun _ => 0
  batchRoot := fun _ _ => 0
  batchTs := fun _ _ => 0
  leaves := fun _ => []
  shared := []
  hist := fun _ => none

/-- `_initialize()` (:162-166): the shared tree is set up empty, and `block.chainid` is added at
index 0 with starting batch 0. -/
def init (P : Params) (b0 τ0 : ℕ) : State := (blank b0 τ0).addChain P P.self 0

/-- A state some run from `_initialize` reaches. -/
def Reachable (P : Params) (r : TsRule) (st : State) : Prop :=
  ∃ b0 τ0, Reach P r (init P b0 τ0) st

/-! ## The settlement clock and the aggregation properties -/

/-- **THE SETTLEMENT CLOCK, BY PUSHED POSITION.** The `l1Timestamp` of chain `c`'s `i`-th leaf
(:251, bound into the leaf at :258). A position not yet pushed has not settled; it gets
`time + 1`, later than every timestamp so far. -/
def State.leafTime (st : State) (c : ChainId) (i : ℕ) : ℕ :=
  match (st.leaves c)[i]? with
  | some l => l.ts
  | none => st.time + 1

/-- **STRICT AGGREGATION.** Every leaf of `st` that settled strictly before the historical root
`e` was written is inside `e`. -/
def AggregatesStrictAt (st : State) (e : HistEntry) : Prop :=
  ∀ c i, st.leafTime c i < e.ts → i < e.count c

/-- **NON-STRICT AGGREGATION** (the shape of `Contracts.Timeout.Aggregates`). Every leaf of `st`
that settled at or before the historical root `e` was written is inside `e`. -/
def AggregatesAt (st : State) (e : HistEntry) : Prop :=
  ∀ c i, st.leafTime c i ≤ e.ts → i < e.count c

/-- The batch numbers chain `c`'s first `n` leaves carry: what a reader indexing by batch number
takes "inside the root" to mean, for a root that holds `n` of `c`'s leaves. -/
def State.BatchInFirst (st : State) (c : ChainId) (n : ℕ) (b : ℕ) : Prop :=
  ∃ l ∈ (st.leaves c).take n, l.batch = b

end Contracts.MessageRoot
