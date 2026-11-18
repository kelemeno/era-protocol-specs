import EraSpec.Contracts.MessageRoot.Specs.Model

/-!
# Check-deleted variants, and concrete instances for the witnesses

Source as in `Model.lean` (`MessageRootBase.sol`, cited `MRB`, at
`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`).

* Five variants of the model, each with one source check deleted:
  `execNoRegisteredCheck` drops `if (chainRegistered(_chainId)) revert ChainExists()`
  (`MRB:146-148`) from `addNewChain`; `execNoConsecutiveCheck` drops
  `require(_batchNumber == expectedNewChainBatchNumber)` (`MRB:193`) from
  `_recordChainBatchRoot`; `recordNoExistsCheck` drops
  `require(chainBatchRoots[c][n] == bytes32(0))` (`MRB:188-191`); `execNoMigratingCheck` drops
  `require(currentChainBatchNumber[_chainId] <= _batchNumber)` (`MRB:155`) from
  `setMigratingChainBatchNumber`; `execNoRecordRegisteredCheck` drops
  `if (!chainRegistered(_chainId)) revert MessageRootNotRegistered()` (`MRB:184-186`) from
  `_recordChainBatchRoot`, in both append flows.  Everything else is the model.
* `execCalls` applies a list of calls in order (`none` if one reverts).
* `mrHashes`, `mrConfig`, `mrConfigPreV31` and the environments `mrEnv` are concrete
  instances, and `mrCalls`, `mrMigrationCalls`, `mrCollisionCalls`, `mrWritersOnlyFirst`,
  `mrWritersOnlySecond` and `mrReregistrationCalls` concrete call lists.
  The hashes are arbitrary arithmetic, not keccak: a witness only shows that the premises of
  the properties can hold together, and a countermodel only needs one instance.
-/

namespace Contracts.MessageRoot

/-- `_recordChainBatchRoot` without the consecutive-number check (`MRB:193`). -/
def recordNoConsecutiveCheck (cfg : Config) (c n : ℕ) (r : Bytes32) (s : State) : Option State :=
  if chainRegistered cfg s c = false then none
  else if r = 0 then none
  else if s.chainBatchRoots c n ≠ 0 then none
  else if UInt256.size ≤ s.currentChainBatchNumber c + 1 then none
  else some { s with
    chainBatchRoots := upd2 s.chainBatchRoots c n r
    currentChainBatchNumber :=
      Function.update s.currentChainBatchNumber c (s.currentChainBatchNumber c + 1) }

/-- `_recordChainBatchRoot` without the already-exists check (`MRB:188-191`). -/
def recordNoExistsCheck (cfg : Config) (c n : ℕ) (r : Bytes32) (s : State) : Option State :=
  if chainRegistered cfg s c = false then none
  else if r = 0 then none
  else if UInt256.size ≤ s.currentChainBatchNumber c + 1 then none
  else if n ≠ s.currentChainBatchNumber c + 1 then none
  else some { s with
    chainBatchRoots := upd2 s.chainBatchRoots c n r
    currentChainBatchNumber :=
      Function.update s.currentChainBatchNumber c (s.currentChainBatchNumber c + 1) }

/-- The model with `addNewChain`'s `ChainExists` check (`MRB:146-148`) deleted. -/
def execNoRegisteredCheck (H : Hashes) (cfg : Config) (env : Env) (s : State) :
    Call → Option State
  | .addNewChain c start =>
      if env.sender ≠ cfg.bridgehub ∧ env.sender ≠ cfg.chainAssetHandler then none
      else addNewChainInternal H env c start s
  | call => exec H cfg env s call

/-- The model with `_recordChainBatchRoot`'s consecutive check (`MRB:193`) deleted, in the
`addChainBatchRootV32` flow. -/
def execNoConsecutiveCheck (H : Hashes) (cfg : Config) (env : Env) (s : State) :
    Call → Option State
  | .addChainBatchRootV32 c n r =>
      if env.sender ≠ env.zkChain c then none
      else (recordNoConsecutiveCheck cfg c n r s).bind (pushChainBatchRoot H env c n r)
  | call => exec H cfg env s call

/-- The model with `setMigratingChainBatchNumber`'s `<=` check (`MRB:155`) deleted. -/
def execNoMigratingCheck (H : Hashes) (cfg : Config) (env : Env) (s : State) :
    Call → Option State
  | .setMigratingChainBatchNumber c n =>
      if env.sender ≠ cfg.chainAssetHandler then none
      else some { s with currentChainBatchNumber := Function.update s.currentChainBatchNumber c n }
  | call => exec H cfg env s call

/-- `_recordChainBatchRoot` without the registration check (`MRB:184-186`). -/
def recordNoRegisteredCheck (c n : ℕ) (r : Bytes32) (s : State) : Option State :=
  if r = 0 then none
  else if s.chainBatchRoots c n ≠ 0 then none
  else if UInt256.size ≤ s.currentChainBatchNumber c + 1 then none
  else if n ≠ s.currentChainBatchNumber c + 1 then none
  else some { s with
    chainBatchRoots := upd2 s.chainBatchRoots c n r
    currentChainBatchNumber :=
      Function.update s.currentChainBatchNumber c (s.currentChainBatchNumber c + 1) }

/-- The model with `_recordChainBatchRoot`'s registration check (`MRB:184-186`) deleted, in both
append flows. -/
def execNoRecordRegisteredCheck (H : Hashes) (cfg : Config) (env : Env) (s : State) :
    Call → Option State
  | .addChainBatchRoot c n r =>
      if env.sender ≠ env.zkChain c then none
      else recordNoRegisteredCheck c n r s
  | .addChainBatchRootV32 c n r =>
      if env.sender ≠ env.zkChain c then none
      else (recordNoRegisteredCheck c n r s).bind (pushChainBatchRoot H env c n r)
  | call => exec H cfg env s call

/-- Apply calls in order; `none` if any reverts. -/
def execCalls (H : Hashes) (cfg : Config) (s : State) : List (Env × Call) → Option State
  | [] => some s
  | (e, c) :: rest => (exec H cfg e s c).bind fun t => execCalls H cfg t rest

/-! ## Concrete instances -/

/-- Arbitrary arithmetic "hashes". -/
def mrHashes : Hashes where
  node a b := a + 2 * b + 1
  batchLeaf r n ts := r + 3 * (n : UInt256) + 5 * (ts : UInt256) + 1
  chainIdLeaf r c := r + 7 * (c : UInt256) + 2
  chainTreeRoot L := L.sum + 11

/-- A deployment on chain `1`: Bridgehub `10`, chain asset handler `11`, empty-tree constant
`9`, no pre-v31 batches. -/
def mrConfig : Config where
  selfChainId := 1
  bridgehub := 10
  chainAssetHandler := 11
  emptyHash := 9
  v31Upgrade := fun _ => 0

/-- `mrConfig`, except that chain `5`'s `v31UpgradeChainBatchNumber` is `4`. -/
def mrConfigPreV31 : Config := { mrConfig with v31Upgrade := fun c => if c = 5 then 4 else 0 }

/-- The environment of a call from `sender` in block `b`, at timestamp `1000 + b`: chain `5`'s
diamond is `55` and chain `6`'s is `66`; the Bridgehub owner is `12`; chain `5`'s diamond
answers `l2LogsRootHash(0) = 77` and `l2LogsRootHash(n) = 300 + n` for `n > 0`; no backfill is
pending; no chain requires a second proof system. -/
def mrEnv (sender : Address) (b : ℕ) : Env where
  sender := sender
  blockNumber := b
  timestamp := 1000 + b
  zkChain := fun c => if c = 5 then 55 else if c = 6 then 66 else 0
  bridgehubOwner := 12
  allZKChainsLength := 0
  backfillPending := fun _ => false
  secondProofRequired := fun _ => false
  proofMode := fun _ => 0
  l2LogsRootHash := fun c n => if c = 5 then (if n = 0 then 77 else 300 + (n : Bytes32)) else 0

/-- The main witness run: initialize (block 1); the Bridgehub adds chain `5` at batch `0` and
seeds its genesis root (block 2); the chain appends batch `1` (record and push) and records
batch `2` (record only) (block 3); the chain asset handler moves its counter to `5`, as on a
return from another settlement layer (block 4); the chain appends batch `6` (block 5); the
Bridgehub owner enables interop for it (block 6); the chain asset handler registers chain `6`
at batch `0`, and chain `6` appends batch `1` (block 7). -/
def mrCalls : List (Env × Call) :=
  [ (mrEnv 10 1, .initialize),
    (mrEnv 10 2, .addNewChain 5 0),
    (mrEnv 10 2, .seedGenesisRoot 5),
    (mrEnv 55 3, .addChainBatchRootV32 5 1 101),
    (mrEnv 55 3, .addChainBatchRoot 5 2 102),
    (mrEnv 11 4, .setMigratingChainBatchNumber 5 5),
    (mrEnv 55 5, .addChainBatchRootV32 5 6 106),
    (mrEnv 12 6, .enableInterop 5 false),
    (mrEnv 11 7, .addNewChain 6 0),
    (mrEnv 66 7, .addChainBatchRootV32 6 1 201) ]

/-- A migration round trip with every batch pushed: initialize; add chain `5` at batch `0`
and seed its genesis root; append batch `1`; the chain asset handler moves the counter to `5`;
append batch `6`. -/
def mrMigrationCalls : List (Env × Call) :=
  [ (mrEnv 10 1, .initialize),
    (mrEnv 10 2, .addNewChain 5 0),
    (mrEnv 10 2, .seedGenesisRoot 5),
    (mrEnv 55 3, .addChainBatchRootV32 5 1 101),
    (mrEnv 11 4, .setMigratingChainBatchNumber 5 5),
    (mrEnv 55 5, .addChainBatchRootV32 5 6 106) ]

/-- From the storage of the first five calls of `mrCalls` (chain `5` at counter `2`): the chain
asset handler adds chain `6` at batch `0` and moves chain `5`'s counter to `5` (block 4). -/
def mrWritersOnlyFirst : List (Env × Call) :=
  [(mrEnv 11 4, .addNewChain 6 0), (mrEnv 11 4, .setMigratingChainBatchNumber 5 5)]

/-- Then chain `6` appends batch `1` (block 5) and the Bridgehub owner enables interop for chain
`5` (block 6). -/
def mrWritersOnlySecond : List (Env × Call) :=
  [(mrEnv 66 5, .addChainBatchRootV32 6 1 201), (mrEnv 12 6, .enableInterop 5 false)]

/-- After a counter move on an unregistered chain `5`: the Bridgehub adds chain `5` at batch `0`
and seeds its genesis root (block 3), and the chain appends batch `1` (block 4). -/
def mrReregistrationCalls : List (Env × Call) :=
  [(mrEnv 10 3, .addNewChain 5 0), (mrEnv 10 3, .seedGenesisRoot 5),
    (mrEnv 55 4, .addChainBatchRootV32 5 1 101)]

/-- Initialize; add chains `5` (by the Bridgehub) and `6` (by the chain asset handler) at batch
`0`; chain `5` appends batch `1` with root `r₅` and chain `6` appends batch `1` with root `r₆`,
in the same block. -/
def mrCollisionCalls (r₅ r₆ : Bytes32) : List (Env × Call) :=
  [ (mrEnv 10 1, .initialize),
    (mrEnv 10 2, .addNewChain 5 0),
    (mrEnv 11 2, .addNewChain 6 0),
    (mrEnv 55 3, .addChainBatchRootV32 5 1 r₅),
    (mrEnv 66 3, .addChainBatchRootV32 6 1 r₆) ]

end Contracts.MessageRoot
