import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `MessageRootBase` — chain trees, the shared tree, and the historical roots

Source: `l1-contracts/contracts/core/message-root/MessageRootBase.sol` at era-contracts
`draft/v0.35.0` head `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, with `L1MessageRoot.sol`,
`common/libraries/MessageHashing.sol`, `core/bridgehub/L1Bridgehub.sol` and
`core/chain-asset-handler/ChainAssetHandlerBase.sol` from the same tree. A bare `:N` is a line of
`MessageRootBase.sol`. This is the same code as the canonical model `Specs/Model.lean`, seen with
ghost state (which leaf each historical root counts); see "Relation to the canonical model"
below.

**This file is definitions only.** The results are in
`EraSpec.Contracts.MessageRoot.Properties.Aggregation` and are proved in
`EraSpec.Contracts.MessageRoot.Proofs.Aggregation`. Everything is in the namespace
`Contracts.MessageRoot.Aggregation`.

## Why this contract matters to the timeout protocol

`Contracts.Timeout.Aggregates` — "a batch that had settled by the time a settlement-layer root
was created is inside that root" — is a premise of the timeout and refund headlines
(`PROTO-AGGREGATES` in ASSUMPTIONS.md; `Protocol/InteropAtomicity/Specs/Timeout.lean` says it
"is not derived here"). The settlement layer that supplies it is this contract: every settled batch
root it pushes goes into its chain's tree with `l1Timestamp = block.timestamp`, the chain's root is
written into the shared tree, and the shared root is recorded per block together with
`block.timestamp`. The timeout path reads that `(root, timestamp)` pair after it has been imported
into `L2InteropRootStorage`, and the Executor double-checks the import against this contract
(`Protocol/InteropAtomicity`, topic `SettlementRoots`). This file models the settlement-layer
half.

## The code

    // _pushChainBatchRoot (:201-220), the interop half of the v32 flow
    uint256 l1Timestamp = block.timestamp;                                          // :202
    chainBatchRootTimestamp[_chainId][_batchNumber] = l1Timestamp;                  // :203
    (, chainRoot) = chainTree[_chainId].push(
        MessageHashing.batchLeafHash(_chainBatchRoot, _batchNumber, l1Timestamp));  // :207-209
    bytes32 cachedChainIdLeafHash =
        MessageHashing.chainIdLeafHash(chainRoot, _chainId);                         // :213
    bytes32 sharedTreeRoot =
        sharedTree.updateLeaf(chainIndex[_chainId], cachedChainIdLeafHash);          // :214
    _emitRoot(sharedTreeRoot);
    _recordHistoricalRoot(sharedTreeRoot);                                          // :219

    // _recordHistoricalRoot (:223-225)
    historicalRoots[block.number] =
        StoredInteropRoot({root: _sharedTreeRoot, timestamp: block.timestamp});      // :224

    // _recordChainBatchRoot (:183-197), shared by both add-chain-batch-root flows
    if (!chainRegistered(_chainId)) revert MessageRootNotRegistered();              // :184-186
    require(_chainBatchRoot != bytes32(0), ChainBatchRootZero());                   // :187
    require(chainBatchRoots[_chainId][_batchNumber] == bytes32(0), ...);            // :188-191
    uint256 expectedNewChainBatchNumber = currentChainBatchNumber[_chainId] + 1;    // :192
    require(_batchNumber == expectedNewChainBatchNumber, NonConsecutiveBatchNumber(...)); // :193
    chainBatchRoots[_chainId][_batchNumber] = _chainBatchRoot;                      // :195
    currentChainBatchNumber[_chainId] = expectedNewChainBatchNumber;                // :196

    // addChainBatchRoot (:164-170): record ONLY (the v31 flow)
    // addChainBatchRootV32 (:173-180): record, then _pushChainBatchRoot

    // _addNewChain (:275-293)
    ++chainCount; chainIndex[_chainId] = cachedChainCount;                          // :279-280
    chainIndexToId[cachedChainCount] = _chainId;                                    // :281
    currentChainBatchNumber[_chainId] = _startingBatchNumber;                       // :282
    chainTree[_chainId].setup(CHAIN_TREE_EMPTY_ENTRY_HASH);                         // :285
    sharedTree.pushNewLeaf(MessageHashing.chainIdLeafHash(bytes32(0), _chainId));   // :287
    _emitRoot(sharedTreeRoot); _recordHistoricalRoot(sharedTreeRoot);               // :291-292

    // seedGenesisRoot (:296-314): genesis root r = zkChain.l2LogsRootHash(0) of a ZKsync OS chain
    require(r != 0); registered; require(currentChainBatchNumber[_chainId] == 0);   // :303-308
    require(chainBatchRoots[_chainId][0] == bytes32(0));                            // :309
    chainBatchRoots[_chainId][0] = r; _pushChainBatchRoot(_chainId, 0, r);          // :311-313

    // setMigratingChainBatchNumber (:153-157), onlyChainAssetHandler, no registration check
    require(currentChainBatchNumber[_chainId] <= _batchNumber, ...);                // :155
    currentChainBatchNumber[_chainId] = _batchNumber;                               // :156

`chainRegistered(c)` is `c == block.chainid || chainIndex[c] != 0` (:159-161), and `_initialize`
(:138-142) sets the shared tree up and registers `block.chainid` at index 0.

## The inventory the model rests on (checked against `b17415d20`)

* `historicalRoots` (:75) has one writer, `_recordHistoricalRoot` (:224), called from
  `_pushChainBatchRoot` (:219) and `_addNewChain` (:292). It is keyed by `block.number`, so a later
  write in the same block overwrites an earlier one.
* `chainTree[c]` (:69) is written by `_addNewChain` (`setup`, :285) and `_pushChainBatchRoot`
  (`push`, :207); `sharedTree` (:64) by `_initialize` (`setup`, :140), `_addNewChain`
  (`pushNewLeaf`, :287) and `_pushChainBatchRoot` (`updateLeaf`, :214).
* `chainBatchRoots` (:90) is written at :195 and :311, both guarded by "still zero";
  `chainBatchRootTimestamp` (:104) only at :203.
* `currentChainBatchNumber` (:84) is written at :156, :196 and :282, and nowhere else under
  `l1-contracts/contracts`.
* Callers: `addNewChain` is `onlyBridgehubOrChainAssetHandler` (:145); the Bridgehub registers a
  fresh chain at start 0 and seeds it (`L1Bridgehub.sol:134-135`), and onboards an existing chain
  at `getTotalBatchesExecuted()` (`L1Bridgehub.sol:302, 316`); the chain asset handler registers a
  migrating chain at its batch number, with no genesis leaf, or moves a returning chain's number
  with `setMigratingChainBatchNumber` (`ChainAssetHandlerBase.sol:409, 414`).

## Modelling choices

* **One MessageRoot contract**, deployed on chain `Params.self` (`block.chainid`).
* **Hashes are abstract functions** (`Hashes`), with no premise. `chainRoot` stands for the root
  `DynamicIncrementalMerkle.push` returns over the leaf hashes pushed so far and `sharedRoot` for
  the root `FullMerkle` returns over its leaf list. That the libraries compute one function of
  those lists is not proved here. `DynamicIncrementalMerkle` is modelled separately in
  `Contracts/DynamicIncrementalMerkle` (`Model`: along a run from `setup`, `root()` is the fold at
  the minimal height for a nonempty leaf list and `0` for the empty tree, `RunRootIsFold`, and each
  `push` returns that stored root, `PushReturnsStoredRoot`), but `chainRoot` is not instantiated
  with it here. `FullMerkle`'s cached storage is the separate topic `Contracts/FullMerkle`
  `CachedNodes`.
* **A chain tree is the list of its pushed leaves, with their preimages** (`Leaf`): batch number,
  batch root, `l1Timestamp`, and a ghost field `blk`, the `block.number` of the push. Positions in
  that list are the tree's leaf indices.
* **A historical root carries a ghost count** (`HistEntry.count`): how many leaves each chain tree
  had when it was written. That count is what the results say the root aggregates. Nothing here
  relates it to what a Merkle proof against the stored root VALUE (`HistEntry.root`) can show:
  that binding is not modelled.
* **The block is environment.** `nextBlock` advances `block.number` by one with a new
  `block.timestamp`, under one of two premises (`TsRule`): non-decreasing (`mono`) or strictly
  increasing (`strict`). Several transactions may run in one block.
* **A revert is the absence of a step**, and **caller checks are omitted** (`onlyChain`-style
  restrictions, `onlyBridgehubOrChainAssetHandler`, `onlyChainAssetHandler`, the Bridgehub check of
  `seedGenesisRoot`). They only reject, so omitting them adds runs, and every result that holds of
  all runs holds a fortiori of the runs the callers allow. The existential statements of the
  Properties module are the exception: a run they exhibit is a run of the model, and where its
  steps need a caller the code does not have, its docstring says so. Arithmetic is on `ℕ`, so
  the checked increments that revert at `2^256 - 1` never do here (more runs again). Also omitted:
  events and `interopRootLogId` (:233-246), message verification (:316-375),
  `v31UpgradeChainBatchNumber` (`L1MessageRoot.sol:46`), and the external read of
  `seedGenesisRoot` (the genesis root is a parameter of the step).
* **Runs start at `_initialize`** (`init`), at any block and timestamp. A MessageRoot upgraded in
  place from an earlier release starts from storage the model does not construct and is not
  covered.

## Relation to the canonical model

This topic was first written at the interop pin `c67894b9` and re-pinned to `b17415d20`: the
modelled functions differ there only in line numbers, the internal getters' names, the storage
order of three variables, a non-ZKsync-OS no-op branch of `seedGenesisRoot` and the writer
`L1MessageRoot.saveV31UpgradeChainBatchNumber`, neither of which this model took or needs.

`Specs/Model.lean` is the canonical model of the same code: every entry point, the `FullMerkle`
shared tree, callers, the checked increments and per-call environments. This topic keeps a coarser
view with ghost state (leaf preimages, push blocks, the leaf counts of each historical root) and a
block clock with a timestamp rule, because its statements are about that ghost state. Its steps
omit the caller checks and the overflow reverts, which only adds runs. No simulation between the
two models is proved (`handoff/2026-11-19/consolidation/roots.md`).

## Pushed positions, not batch numbers

A chain's `n`-th leaf is not its batch `n`. A chain onboarded at a nonzero start (no genesis
leaf) pushes batch `start + 1` as leaf 0; `setMigratingChainBatchNumber` jumps the batch number
forward with no leaf; and a record-only batch (`addChainBatchRoot`, the v31 entry point) advances
the batch number without a leaf. So the clock the timeout protocol needs is indexed by **pushed
position**: `State.leafTime c i` is the `l1Timestamp` of chain `c`'s `i`-th leaf.
-/

namespace Contracts.MessageRoot.Aggregation

/-- `bytes32` and `uint256` words. -/
abbrev Word := UInt256

/-- Chain ids, as `uint256` (the same type as `Contracts.Atomicity.Chain`). -/
abbrev ChainId := UInt256

/-! ## Hashes and deployment -/

/-- The four hashes `MessageRootBase` composes. Abstract: no injectivity or other premise. -/
structure Hashes where
  /-- `MessageHashing.batchLeafHash(batchRoot, batchNumber, l1Timestamp)`
  (`MessageHashing.sol:76-82`). -/
  batchLeaf : Word → ℕ → ℕ → Word
  /-- `MessageHashing.chainIdLeafHash(chainRoot, chainId)` (`MessageHashing.sol:87-89`). -/
  chainIdLeaf : Word → ChainId → Word
  /-- The root `chainTree[c].push` returns (:207), over all leaf hashes pushed so far. -/
  chainRoot : List Word → Word
  /-- The root `sharedTree.pushNewLeaf` / `updateLeaf` return (:214, :287), over the leaf list. -/
  sharedRoot : List Word → Word

/-- The deployment constants. -/
structure Params where
  /-- `block.chainid` of the chain the contract is deployed on; registered at index 0 (:141). -/
  self : ChainId
  /-- The hashes. -/
  H : Hashes

/-! ## State -/

/-- One leaf of a chain tree, with its preimage: what `_pushChainBatchRoot` hashed (:207-209). -/
structure Leaf where
  /-- `_batchNumber`. -/
  batch : ℕ
  /-- `_chainBatchRoot`. -/
  root : Word
  /-- `l1Timestamp = block.timestamp` at the push (:202). -/
  ts : ℕ
  /-- Ghost: `block.number` at the push. The contract does not store it. -/
  blk : ℕ
deriving DecidableEq

/-- The leaf hash the chain tree stores (:208). -/
def Leaf.hash (H : Hashes) (l : Leaf) : Word := H.batchLeaf l.root l.batch l.ts

/-- One `historicalRoots[blockNumber]` entry (:75, `StoredInteropRoot`, `Messaging.sol:161-164`),
plus the ghost count of what it aggregated. -/
structure HistEntry where
  /-- `root`: the shared tree root when it was written. -/
  root : Word
  /-- `timestamp`: `block.timestamp` when it was written (:224). -/
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
  /-- `currentChainBatchNumber` (:84). -/
  current : ChainId → ℕ
  /-- `chainBatchRoots` (:90); `0` is "none". -/
  batchRoot : ChainId → ℕ → Word
  /-- `chainBatchRootTimestamp` (:104); `0` is "none". -/
  batchTs : ChainId → ℕ → ℕ
  /-- `chainTree[c]` (:69), as its pushed leaves, oldest first. -/
  leaves : ChainId → List Leaf
  /-- `sharedTree` (:64), as its leaf list in index order. -/
  shared : List Word
  /-- `historicalRoots` (:75); `none` is the default `(0, 0)`. -/
  hist : ℕ → Option HistEntry

/-- `chainRegistered(c)` (:159-161). -/
def State.Registered (P : Params) (st : State) (c : ChainId) : Prop :=
  c = P.self ∨ st.chainIndex c ≠ 0

/-- The `(root, timestamp)` pair `historicalRoot(b)` returns (:228-230). -/
def State.historicalRoot (st : State) (b : ℕ) : Word × ℕ :=
  match st.hist b with
  | some e => (e.root, e.ts)
  | none => (0, 0)

/-- The chain root a chain's shared-tree leaf commits to: `bytes32(0)` while the tree is empty
(:287), else the root `push` returned for its leaves (:207, :213). -/
def chainRootVal (H : Hashes) : List Leaf → Word
  | [] => 0
  | ls => H.chainRoot (ls.map (Leaf.hash H))

/-! ## Effects -/

/-- `_recordHistoricalRoot` after a tree update (:223-225): the current shared root, the current
timestamp, and (ghost) the current chain-tree sizes. -/
def State.writeHist (P : Params) (st : State) : State :=
  let e : HistEntry := ⟨P.H.sharedRoot st.shared, st.time, fun c => (st.leaves c).length⟩
  { st with hist := Function.update st.hist st.block (some e) }

/-- `_addNewChain(c, start)` (:275-293). -/
def State.addChain (P : Params) (st : State) (c : ChainId) (start : ℕ) : State :=
  State.writeHist P
    { st with
      chainCount := st.chainCount + 1
      chainIndex := Function.update st.chainIndex c st.chainCount
      chainIndexToId := Function.update st.chainIndexToId st.chainCount c
      current := Function.update st.current c start
      leaves := Function.update st.leaves c []
      shared := st.shared ++ [P.H.chainIdLeaf 0 c] }

/-- `chainBatchRoots[c][b] = r` (:195, :311). -/
def State.setBatchRoot (st : State) (c : ChainId) (b : ℕ) (r : Word) : State :=
  { st with batchRoot := Function.update st.batchRoot c (Function.update (st.batchRoot c) b r) }

/-- The effect of `_recordChainBatchRoot(c, b, r)` once its checks pass (:195-196). -/
def State.record (st : State) (c : ChainId) (b : ℕ) (r : Word) : State :=
  { st.setBatchRoot c b r with current := Function.update st.current c b }

/-- The leaf `_pushChainBatchRoot(c, b, r)` pushes in state `st` (:202, :207-209). -/
def State.newLeaf (st : State) (b : ℕ) (r : Word) : Leaf := ⟨b, r, st.time, st.block⟩

/-- `_pushChainBatchRoot(c, b, r)` (:201-220). -/
def State.push (P : Params) (st : State) (c : ChainId) (b : ℕ) (r : Word) : State :=
  let ls := st.leaves c ++ [st.newLeaf b r]
  State.writeHist P
    { st with
      batchTs := Function.update st.batchTs c (Function.update (st.batchTs c) b st.time)
      leaves := Function.update st.leaves c ls
      shared := st.shared.set (st.chainIndex c) (P.H.chainIdLeaf (chainRootVal P.H ls) c) }

/-- `seedGenesisRoot(c)` with genesis root `r` once its checks pass (:311-313). -/
def State.seed (P : Params) (st : State) (c : ChainId) (r : Word) : State :=
  (st.setBatchRoot c 0 r).push P c 0 r

/-- `setMigratingChainBatchNumber(c, b)` once its check passes (:156). -/
def State.migrate (st : State) (c : ChainId) (b : ℕ) : State :=
  { st with current := Function.update st.current c b }

/-- A new block with timestamp `τ`. -/
def State.advance (st : State) (τ : ℕ) : State :=
  { st with block := st.block + 1, time := τ }

/-! ## Guards -/

/-- The checks of `_recordChainBatchRoot(c, b, r)` (:184-193). -/
structure RecordGuard (P : Params) (st : State) (c : ChainId) (b : ℕ) (r : Word) : Prop where
  /-- `MessageRootNotRegistered` (:184-186). -/
  registered : st.Registered P c
  /-- `ChainBatchRootZero` (:187). -/
  nonzero : r ≠ 0
  /-- `ChainBatchRootAlreadyExists` (:188-191). -/
  fresh : st.batchRoot c b = 0
  /-- `NonConsecutiveBatchNumber` (:192-193). -/
  consecutive : b = st.current c + 1

/-- The checks of `seedGenesisRoot(c)` with genesis root `r` (:303-309). -/
structure SeedGuard (P : Params) (st : State) (c : ChainId) (r : Word) : Prop where
  /-- `ChainBatchRootZero` (:303). -/
  nonzero : r ≠ 0
  /-- `MessageRootNotRegistered` (:304-306). -/
  registered : st.Registered P c
  /-- `NonConsecutiveBatchNumber(_chainId, 0)` (:308). -/
  atGenesis : st.current c = 0
  /-- `ChainBatchRootAlreadyExists(_chainId, 0)` (:309). -/
  unseeded : st.batchRoot c 0 = 0

/-- How `block.timestamp` moves from one block to the next: a premise about the chain the
contract runs on, not something the contract checks. -/
inductive TsRule
  /-- Non-decreasing: equal timestamps across blocks are allowed. -/
  | mono
  /-- Strictly increasing. -/
  | strict
deriving DecidableEq

/-- The timestamps a new block may have, after a block with timestamp `τ`. -/
def TsRule.Allows : TsRule → ℕ → ℕ → Prop
  | .mono, τ, τ' => τ ≤ τ'
  | .strict, τ, τ' => τ < τ'

/-! ## Runs -/

/-- One transaction that changes the modelled state, or a new block. -/
inductive Step (P : Params) (r : TsRule) : State → State → Prop
  /-- `addNewChain(c, start)` (:145-150): `ChainExists` unless unregistered. -/
  | addNewChain {st : State} (c : ChainId) (start : ℕ) :
      ¬ st.Registered P c → Step P r st (st.addChain P c start)
  /-- `seedGenesisRoot(c)` of a ZKsync OS chain whose genesis root is `g` (:296-314). -/
  | seedGenesisRoot {st : State} (c : ChainId) (g : Word) :
      SeedGuard P st c g → Step P r st (st.seed P c g)
  /-- `addChainBatchRoot(c, b, root)` (:164-170): record only, no push. -/
  | addChainBatchRoot {st : State} (c : ChainId) (b : ℕ) (root : Word) :
      RecordGuard P st c b root → Step P r st (st.record c b root)
  /-- `addChainBatchRootV32(c, b, root)` (:173-180): record, then push. -/
  | addChainBatchRootV32 {st : State} (c : ChainId) (b : ℕ) (root : Word) :
      RecordGuard P st c b root → Step P r st ((st.record c b root).push P c b root)
  /-- `setMigratingChainBatchNumber(c, b)` (:153-157). -/
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

/-- `_initialize()` (:138-142): the shared tree is set up empty, and `block.chainid` is added at
index 0 with starting batch 0. -/
def init (P : Params) (b0 τ0 : ℕ) : State := (blank b0 τ0).addChain P P.self 0

/-- A state some run from `_initialize` reaches. -/
def Reachable (P : Params) (r : TsRule) (st : State) : Prop :=
  ∃ b0 τ0, Reach P r (init P b0 τ0) st

/-! ## The settlement clock and the aggregation properties -/

/-- **THE SETTLEMENT CLOCK, BY PUSHED POSITION.** The `l1Timestamp` of chain `c`'s `i`-th leaf
(:202, bound into the leaf at :208). A position not yet pushed has not settled; it gets
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

end Contracts.MessageRoot.Aggregation
