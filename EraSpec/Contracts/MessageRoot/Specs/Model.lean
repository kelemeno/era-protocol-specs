import EraSpec.Contracts.FullMerkle.Specs.CachedNodes

/-!
# Model: `MessageRootBase` and `L1MessageRoot`, every state-changing entry point

Source: era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`,
`l1-contracts/contracts/core/message-root/MessageRootBase.sol` (cited `MRB`) and
`L1MessageRoot.sol` (cited `L1MR`).  A revert is `none`; a successful call is `some` of the new
storage.  Guards are listed in source order.

## Storage (`MRB:53-104`, `L1MR:46-49`)

`State` has one field per storage variable that some entry point writes, plus the
OpenZeppelin `_initialized` counter.  Two are abstracted:

* `sharedTree` is the library's own storage, `FullMerkle.FullTree` as transcribed in
  `../FullMerkle/Specs/CachedNodes.lean`.  `pushNewLeaf`, `updateLeaf`, `setup` and `root` are
  the transcribed functions, so the shared tree is **not** abstracted.
* `chainTree[c]` (a `DynamicIncrementalMerkle.Bytes32PushTree`) is abstracted to two things:
  `chainTreeSetups c`, how many times `setup` ran on it, and `chainLeaves c`, the leaves pushed
  into it since.  The library is cited `DIM` (`common/libraries/DynamicIncrementalMerkle.sol`).
  - `setup` (`DIM:53-58`) has no guard: it zeroes `_nextLeafIndex` and pushes one more entry
    onto `_zeros` and `_sides`.  On a tree that was never set up this gives the empty tree.  On
    one that was, it corrupts it.  The model counts the calls and empties `chainLeaves`; the
    abstraction below is claimed only for a count of `1`, and `Inv.setups` shows the count is
    `1` for every registered chain and `0` for every other, on every reachable storage.
  - `push` (`DIM:93-137`) on a never-set-up tree reverts: `self._zeros.length - 1` (`DIM:95`)
    underflows.  The model reverts there too.
  - The root of a tree set up once is `chainRootOf H (chainLeaves c)`: `bytes32(0)` for no
    leaves (`setup` stores side `0`, `root()` reads the last side, `DIM:56`, `DIM:161-163`),
    and the parameter `H.chainTreeRoot` of the pushed leaves otherwise.
  `MODEL-MR-DIM` in `ASSUMPTIONS.md`: that on a tree set up once `push` does not revert and
  returns, and `root()` reads, one function of the pushed leaves, is not proved here (the
  library is not transcribed).

`DEPRECATED_l1ChainId` and `__gap` are never written and are omitted.  Events are omitted
except where they write storage (`_emitRoot` writes `interopRootLogId`/`lastEmitBlock`).

## Hashes and environment

`Hashes` collects the hash functions as uninterpreted parameters: `node` is
`Merkle.efficientHash` inside `FullMerkle`, `batchLeaf` is `MessageHashing.batchLeafHash`,
`chainIdLeaf` is `MessageHashing.chainIdLeafHash`.  No property assumes anything about them.

`Config` is fixed per deployment: `block.chainid`, the two immutables, the empty-leaf constant
and `v31UpgradeChainBatchNumber`.  The last is storage, but this release has no writer for it
(`L1MR:35-46`: "nothing writes it any more"), so it is a constant of every run.

`Env` is what one call sees: `msg.sender`, `block.number`, `block.timestamp`, and the answers
of the external calls it makes (`Bridgehub.getZKChain`, `Bridgehub.owner`,
`getAllZKChainChainIDs().length`, the vault's `chainBalanceBackfillPending`, the chain's
getters).  Each call gets its own `Env`, so the Bridgehub's registry may change arbitrarily
between calls.  `MODEL-MR-ENV` in `ASSUMPTIONS.md`.

## Arithmetic

Numbers are `ℕ`.  The three checked increments revert at `2^256 - 1`: `++chainCount`
(`MRB:279`), `currentChainBatchNumber[c] + 1` (`MRB:192`) and `++currentCount` (`MRB:239`).
-/

namespace Contracts.MessageRoot

open MerkleSpec (Hash)

abbrev Address := UInt256
abbrev Bytes32 := UInt256
abbrev FullTree := Contracts.FullMerkle.FullTree

/-- `ZKSYNC_OS_MULTI_PROOF_VERIFICATION_TYPE` (`common/Config.sol:108`). -/
def multiProofType : ℕ := 5

/-- The hash functions, uninterpreted. -/
structure Hashes where
  /-- `Merkle.efficientHash`, the node hash of `FullMerkle` (the shared tree). -/
  node : Hash
  /-- `MessageHashing.batchLeafHash(batchRoot, batchNumber, l1Timestamp)`. -/
  batchLeaf : Bytes32 → ℕ → ℕ → Bytes32
  /-- `MessageHashing.chainIdLeafHash(chainRoot, chainId)`. -/
  chainIdLeaf : Bytes32 → ℕ → Bytes32
  /-- The root `DynamicIncrementalMerkle.push` returns after a nonempty list of pushes. -/
  chainTreeRoot : List Bytes32 → Bytes32

/-- Per-deployment constants. -/
structure Config where
  /-- `block.chainid`. -/
  selfChainId : ℕ
  /-- `BRIDGE_HUB` (`L1MR:30`). -/
  bridgehub : Address
  /-- `CHAIN_ASSET_HANDLER` (`L1MR:33`). -/
  chainAssetHandler : Address
  /-- `SHARED_ROOT_TREE_EMPTY_HASH` (`IMessageRoot.sol:14-16`). -/
  emptyHash : Bytes32
  /-- `v31UpgradeChainBatchNumber` (`L1MR:46`): no writer in this release. -/
  v31Upgrade : ℕ → ℕ

/-- What one call sees. -/
structure Env where
  sender : Address
  blockNumber : ℕ
  timestamp : ℕ
  /-- `IBridgehubBase(BRIDGE_HUB).getZKChain(c)`. -/
  zkChain : ℕ → Address
  /-- `IOwnable(BRIDGE_HUB).owner()`. -/
  bridgehubOwner : Address
  /-- `IBridgehubBase(BRIDGE_HUB).getAllZKChainChainIDs().length`. -/
  allZKChainsLength : ℕ
  /-- `nativeTokenVault.chainBalanceBackfillPending(c)`. -/
  backfillPending : ℕ → Bool
  /-- `IGetters(zkChain).isSecondProofSystemRequired()`. -/
  secondProofRequired : ℕ → Bool
  /-- `IGetters(zkChain).getProofMode()`. -/
  proofMode : ℕ → ℕ
  /-- `IGetters(getZKChain(c)).l2LogsRootHash(n)`. -/
  l2LogsRootHash : ℕ → ℕ → Bytes32

/-- The contract's storage. -/
structure State where
  /-- OpenZeppelin `Initializable._initialized`. -/
  initialized : ℕ
  /-- `chainCount` (`MRB:54`). -/
  chainCount : ℕ
  /-- `chainIndex` (`MRB:57`). -/
  chainIndex : ℕ → ℕ
  /-- `chainIndexToId` (`MRB:60`). -/
  chainIndexToId : ℕ → ℕ
  /-- `sharedTree` (`MRB:64`). -/
  sharedTree : FullTree
  /-- `chainTree` (`MRB:69`), as the leaves pushed since `setup`. -/
  chainLeaves : ℕ → List Bytes32
  /-- How many times `setup` ran on `chainTree[c]`. -/
  chainTreeSetups : ℕ → ℕ
  /-- `historicalRoots` (`MRB:75`): `(root, timestamp)`. -/
  historicalRoots : ℕ → Bytes32 × ℕ
  /-- `currentChainBatchNumber` (`MRB:84`). -/
  currentChainBatchNumber : ℕ → ℕ
  /-- `chainBatchRoots` (`MRB:90`). -/
  chainBatchRoots : ℕ → ℕ → Bytes32
  /-- `interopRootLogId` (`MRB:94`). -/
  interopRootLogId : ℕ
  /-- `lastEmitBlock` (`MRB:98`). -/
  lastEmitBlock : ℕ
  /-- `chainBatchRootTimestamp` (`MRB:104`). -/
  chainBatchRootTimestamp : ℕ → ℕ → ℕ
  /-- `interopEnabled` (`L1MR:49`). -/
  interopEnabled : ℕ → Bool

/-- Fresh proxy storage: everything zero or empty. -/
def fresh : State where
  initialized := 0
  chainCount := 0
  chainIndex := fun _ => 0
  chainIndexToId := fun _ => 0
  sharedTree := Contracts.FullMerkle.FullTree.empty
  chainLeaves := fun _ => []
  chainTreeSetups := fun _ => 0
  historicalRoots := fun _ => (0, 0)
  currentChainBatchNumber := fun _ => 0
  chainBatchRoots := fun _ _ => 0
  interopRootLogId := 0
  lastEmitBlock := 0
  chainBatchRootTimestamp := fun _ _ => 0
  interopEnabled := fun _ => false

/-- Write one entry of a nested mapping. -/
def upd2 {β : Type} (f : ℕ → ℕ → β) (a b : ℕ) (v : β) : ℕ → ℕ → β :=
  Function.update f a (Function.update (f a) b v)

/-! ## Views -/

/-- `chainRegistered(c)` (`MRB:159-161`). -/
def chainRegistered (cfg : Config) (s : State) (c : ℕ) : Bool :=
  decide (c = cfg.selfChainId) || decide (s.chainIndex c ≠ 0)

/-- The root of a chain tree holding `leaves`: `bytes32(0)` when empty (`setup` stores side 0),
`H.chainTreeRoot leaves` otherwise. -/
def chainRootOf (H : Hashes) (leaves : List Bytes32) : Bytes32 :=
  if leaves = [] then 0 else H.chainTreeRoot leaves

/-- `getAggregatedRoot()` (`MRB:249-254`). -/
def getAggregatedRoot (cfg : Config) (s : State) : Option Bytes32 :=
  if s.chainCount = 0 then some cfg.emptyHash else Contracts.FullMerkle.root s.sharedTree

/-- `getChainRoot(c)` (`MRB:263-268`). -/
def getChainRoot (H : Hashes) (cfg : Config) (s : State) (c : ℕ) : Option Bytes32 :=
  if chainRegistered cfg s c then some (chainRootOf H (s.chainLeaves c)) else none

/-- `chainTreeLeafCount(c)` (`MRB:257-259`). -/
def chainTreeLeafCount (s : State) (c : ℕ) : ℕ := (s.chainLeaves c).length

/-- `_getChainBatchRoot(c, n)` (`MRB:364-373`) with L1's `_noBatchFallback` (`L1MR:123-128`). -/
def getChainBatchRoot (cfg : Config) (env : Env) (s : State) (c n : ℕ) : Option Bytes32 :=
  -- `require(_batchNumber > 0, BatchZeroNotAllowed())` (:366)
  if n = 0 then none
  else if s.chainBatchRoots c n ≠ 0 then some (s.chainBatchRoots c n)
  -- pre-v31 batches are read from the chain itself (`L1MR:124-125`)
  else if n < cfg.v31Upgrade c then some (env.l2LogsRootHash c n)
  else some 0

/-- The final-proof-node branch of `_proveL2LeafInclusionRecursive` (`MRB:343-348`): the proven
batch root must equal the expected one, which must be nonzero.  `none` is a revert. -/
def finalNodeAccepts (cfg : Config) (env : Env) (s : State) (c n : ℕ) (proven : Bytes32) :
    Option Bool :=
  (getChainBatchRoot cfg env s c n).map fun r => decide (r = proven) && decide (r ≠ 0)

/-! ## Internal functions -/

/-- `_emitRoot` (`MRB:233-246`): advance `interopRootLogId` once per block. -/
def emitRoot (env : Env) (s : State) : Option State :=
  if env.blockNumber ≠ s.lastEmitBlock then
    if s.interopRootLogId + 1 < UInt256.size then
      some { s with interopRootLogId := s.interopRootLogId + 1, lastEmitBlock := env.blockNumber }
    else none
  else some s

/-- `_recordHistoricalRoot` (`MRB:223-225`). -/
def recordHistoricalRoot (env : Env) (r : Bytes32) (s : State) : State :=
  { s with historicalRoots := Function.update s.historicalRoots env.blockNumber (r, env.timestamp) }

/-- `_addNewChain(c, start)` (`MRB:275-293`). -/
def addNewChainInternal (H : Hashes) (env : Env) (c start : ℕ) (s : State) : Option State :=
  -- `++chainCount` (:279), checked
  if s.chainCount + 1 < UInt256.size then do
    let s₁ : State := { s with
      chainCount := s.chainCount + 1
      chainIndex := Function.update s.chainIndex c s.chainCount               -- :280
      chainIndexToId := Function.update s.chainIndexToId s.chainCount c       -- :281
      currentChainBatchNumber := Function.update s.currentChainBatchNumber c start  -- :282
      -- :285 `chainTree[c].setup(CHAIN_TREE_EMPTY_ENTRY_HASH)`
      chainLeaves := Function.update s.chainLeaves c []
      chainTreeSetups := Function.update s.chainTreeSetups c (s.chainTreeSetups c + 1) }
    -- :287 `sharedTree.pushNewLeaf(chainIdLeafHash(bytes32(0), c))`
    let p ← Contracts.FullMerkle.pushNewLeaf H.node s₁.sharedTree (H.chainIdLeaf 0 c)
    let s₂ ← emitRoot env { s₁ with sharedTree := p.1 }             -- :291
    pure (recordHistoricalRoot env p.2 s₂)                           -- :292
  else none

/-- `_recordChainBatchRoot(c, n, r)` (`MRB:183-197`). -/
def recordChainBatchRoot (cfg : Config) (c n : ℕ) (r : Bytes32) (s : State) : Option State :=
  if chainRegistered cfg s c = false then none                      -- :184-186
  else if r = 0 then none                                           -- :187
  else if s.chainBatchRoots c n ≠ 0 then none                       -- :188-191
  else if UInt256.size ≤ s.currentChainBatchNumber c + 1 then none  -- :192, checked `+ 1`
  else if n ≠ s.currentChainBatchNumber c + 1 then none             -- :193
  else some { s with
    chainBatchRoots := upd2 s.chainBatchRoots c n r                 -- :195
    currentChainBatchNumber :=
      Function.update s.currentChainBatchNumber c (s.currentChainBatchNumber c + 1) }  -- :196

/-- `_pushChainBatchRoot(c, n, r)` (`MRB:201-220`).  `push` on a tree that was never set up
reverts (`DIM:95`, `self._zeros.length - 1` underflows). -/
def pushChainBatchRoot (H : Hashes) (env : Env) (c n : ℕ) (r : Bytes32) (s : State) :
    Option State :=
  if s.chainTreeSetups c = 0 then none else do
  -- :202-203
  let s₁ : State := { s with
    chainBatchRootTimestamp := upd2 s.chainBatchRootTimestamp c n env.timestamp }
  -- :207-209 `chainTree[c].push(batchLeafHash(r, n, l1Timestamp))`
  let leaves' := s₁.chainLeaves c ++ [H.batchLeaf r n env.timestamp]
  let s₂ : State := { s₁ with chainLeaves := Function.update s₁.chainLeaves c leaves' }
  -- :213-214
  let p ← Contracts.FullMerkle.updateLeaf H.node s₂.sharedTree (s₂.chainIndex c)
    (H.chainIdLeaf (chainRootOf H leaves') c)
  let s₃ ← emitRoot env { s₂ with sharedTree := p.1 }              -- :218
  pure (recordHistoricalRoot env p.2 s₃)                            -- :219

/-! ## Entry points -/

/-- The state-changing external functions. -/
inductive Call where
  /-- `L1MessageRoot.initialize()` (`L1MR:63-69`), `reinitializer(2)`. -/
  | initialize
  /-- `addNewChain(c, start)` (`MRB:145-150`). -/
  | addNewChain (c start : ℕ)
  /-- `setMigratingChainBatchNumber(c, n)` (`MRB:153-157`). -/
  | setMigratingChainBatchNumber (c n : ℕ)
  /-- `addChainBatchRoot(c, n, r)` (`MRB:164-170`): the v31 record-only flow. -/
  | addChainBatchRoot (c n : ℕ) (r : Bytes32)
  /-- `addChainBatchRootV32(c, n, r)` (`MRB:173-180`): record and push. -/
  | addChainBatchRootV32 (c n : ℕ) (r : Bytes32)
  /-- `seedGenesisRoot(c)` (`MRB:296-314`). -/
  | seedGenesisRoot (c : ℕ)
  /-- `L1MessageRoot.enableInterop(c, requireSecondProofSystem)` (`L1MR:72-89`). -/
  | enableInterop (c : ℕ) (requireSecond : Bool)

/-- One external call. -/
def exec (H : Hashes) (cfg : Config) (env : Env) (s : State) : Call → Option State
  | .initialize =>
      -- `reinitializer(2)`: `_initialized < 2`, then `_initialized = 2`
      if s.initialized < 2 then do
        let s₁ : State := { s with
          initialized := 2
          sharedTree := (Contracts.FullMerkle.setup s.sharedTree cfg.emptyHash).1 }  -- MRB:140
        let s₂ ← addNewChainInternal H env cfg.selfChainId 0 s₁                     -- MRB:141
        -- `require(allZKChainsLength == 0, LocallyNoChainsAtGenesis())` (L1MR:65-68)
        if env.allZKChainsLength = 0 then some s₂ else none
      else none
  | .addNewChain c start =>
      -- `onlyBridgehubOrChainAssetHandler` (MRB:114-119)
      if env.sender ≠ cfg.bridgehub ∧ env.sender ≠ cfg.chainAssetHandler then none
      -- `if (chainRegistered(_chainId)) revert ChainExists()` (MRB:146-148)
      else if chainRegistered cfg s c then none
      else addNewChainInternal H env c start s
  | .setMigratingChainBatchNumber c n =>
      -- `onlyChainAssetHandler` (MRB:122-127)
      if env.sender ≠ cfg.chainAssetHandler then none
      -- `require(currentChainBatchNumber[c] <= n)` (MRB:155)
      else if s.currentChainBatchNumber c ≤ n then
        some { s with currentChainBatchNumber := Function.update s.currentChainBatchNumber c n }
      else none
  | .addChainBatchRoot c n r =>
      -- `addChainBatchRootRestriction` (MRB:131-136)
      if env.sender ≠ env.zkChain c then none
      else recordChainBatchRoot cfg c n r s
  | .addChainBatchRootV32 c n r =>
      if env.sender ≠ env.zkChain c then none
      else (recordChainBatchRoot cfg c n r s).bind (pushChainBatchRoot H env c n r)
  | .seedGenesisRoot c =>
      -- MRB:297-299
      if env.sender ≠ cfg.bridgehub then none
      else
        -- :302 `zkChain.l2LogsRootHash(0)`
        if env.l2LogsRootHash c 0 = 0 then none                                 -- :303
        else if chainRegistered cfg s c = false then none                       -- :304-306
        else if s.currentChainBatchNumber c ≠ 0 then none                       -- :308
        else if s.chainBatchRoots c 0 ≠ 0 then none                             -- :309
        else pushChainBatchRoot H env c 0 (env.l2LogsRootHash c 0)              -- :311, :313
          { s with chainBatchRoots := upd2 s.chainBatchRoots c 0 (env.l2LogsRootHash c 0) }
  | .enableInterop c req =>
      if env.sender ≠ env.bridgehubOwner then none                         -- L1MR:73
      else if env.zkChain c = 0 then none                                  -- :75
      else if s.interopEnabled c = true then none                          -- :76
      else if env.backfillPending c = true then none                       -- :80
      else if req = true ∧ env.secondProofRequired c = false then none     -- :82
      else if req = true ∧ env.proofMode c ≠ multiProofType then none      -- :83-84
      else some { s with interopEnabled := Function.update s.interopEnabled c true }  -- :87

/-! ## Runs -/

/-- A run: calls applied in order, each to the storage the previous one left, each successful.
The trace records each call with the environment it saw. -/
inductive Run (H : Hashes) (cfg : Config) : State → List (Env × Call) → State → Prop
  | nil (s : State) : Run H cfg s [] s
  | snoc {s t u : State} {tr : List (Env × Call)} {e : Env} {c : Call} :
      Run H cfg s tr t → exec H cfg e t c = some u → Run H cfg s (tr ++ [(e, c)]) u

/-- Storage reachable from fresh proxy storage: a successful `initialize`, then any successful
calls from any callers in any order. -/
inductive Reachable (H : Hashes) (cfg : Config) : State → Prop
  | init {e : Env} {s : State} : exec H cfg e fresh .initialize = some s → Reachable H cfg s
  | step {s t : State} {e : Env} {c : Call} :
      Reachable H cfg s → exec H cfg e s c = some t → Reachable H cfg t

/-! ## The invariant -/

/-- The shared tree's leaves as a function of the per-chain trees: slot `i` holds
`chainIdLeafHash(root of chain chainIndexToId[i]'s tree, chainIndexToId[i])`. -/
def sharedLeaves (H : Hashes) (s : State) : List Bytes32 :=
  (List.range s.chainCount).map fun i =>
    H.chainIdLeaf (chainRootOf H (s.chainLeaves (s.chainIndexToId i))) (s.chainIndexToId i)

/-- The leaf a chain tree holds for batch `n`. -/
def batchLeafOf (H : Hashes) (s : State) (c n : ℕ) : Bytes32 :=
  H.batchLeaf (s.chainBatchRoots c n) n (s.chainBatchRootTimestamp c n)

/-- A chain tree is a log of recorded batches: its leaves are the batch leaves of a strictly
increasing list of batch numbers, each at most the chain's current batch number and each with a
recorded (nonzero) root. -/
def ChainLog (H : Hashes) (s : State) (c : ℕ) : Prop :=
  ∃ ns : List ℕ, ns.Pairwise (· < ·)
    ∧ (∀ n ∈ ns, n ≤ s.currentChainBatchNumber c ∧ s.chainBatchRoots c n ≠ 0)
    ∧ s.chainLeaves c = ns.map (batchLeafOf H s c)

/-- The storage invariant of an initialized message root: the index bijection
(`self_at_zero` … `slot_of_index`), the shared tree holding `sharedLeaves` (`tree_reach`,
`tree_rep`), the batch-root bookkeeping (`unreg_empty`, `beyond_zero`), each chain tree as a
log of recorded batches (`log`), the last recorded historical root being the current one
(`hist`), and each chain tree set up once exactly when its chain is registered (`setups`). -/
structure Inv (H : Hashes) (cfg : Config) (s : State) : Prop where
  initialized : 2 ≤ s.initialized
  count_pos : 1 ≤ s.chainCount
  self_at_zero : s.chainIndexToId 0 = cfg.selfChainId
  self_index : s.chainIndex cfg.selfChainId = 0
  index_of_slot : ∀ i, i < s.chainCount → s.chainIndex (s.chainIndexToId i) = i
  slot_of_index : ∀ c, s.chainIndex c ≠ 0 →
    s.chainIndex c < s.chainCount ∧ s.chainIndexToId (s.chainIndex c) = c
  tree_reach : Contracts.FullMerkle.Reachable H.node cfg.emptyHash s.sharedTree
  tree_rep : Contracts.FullMerkle.Represents H.node cfg.emptyHash (sharedLeaves H s) s.sharedTree
  unreg_empty : ∀ c, chainRegistered cfg s c = false →
    s.chainLeaves c = [] ∧ ∀ n, s.chainBatchRoots c n = 0
  beyond_zero : ∀ c n, s.currentChainBatchNumber c < n → s.chainBatchRoots c n = 0
  log : ∀ c, ChainLog H s c
  hist : Contracts.FullMerkle.root s.sharedTree = some (s.historicalRoots s.lastEmitBlock).1
  setups : ∀ c, s.chainTreeSetups c = if chainRegistered cfg s c then 1 else 0

end Contracts.MessageRoot
