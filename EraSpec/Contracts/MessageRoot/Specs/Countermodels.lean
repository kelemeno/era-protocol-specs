import EraSpec.Contracts.MessageRoot.Specs.Model

/-!
# Countermodels and a concrete run

Source as in `Model.lean` (`MessageRootBase.sol`, cited `MRB`, at
`d9f678900e1bc8286412b78f56d4a9f443983c29`).

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
* `runFrom` applies a list of calls in order (`none` if one reverts).
* `wH`, `wCfg` and the environments `wEnv` are concrete instances for witnesses.  The hashes
  are arbitrary arithmetic, not keccak: a witness only shows that the premises of the
  properties can hold together, and a countermodel only needs one instance.
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
def runFrom (H : Hashes) (cfg : Config) (s : State) : List (Env × Call) → Option State
  | [] => some s
  | (e, c) :: rest => (exec H cfg e s c).bind fun t => runFrom H cfg t rest

/-! ## Concrete instances -/

/-- Arbitrary arithmetic "hashes". -/
def wH : Hashes where
  node a b := a + 2 * b + 1
  batchLeaf r n ts := r + 3 * (n : UInt256) + 5 * (ts : UInt256) + 1
  chainIdLeaf r c := r + 7 * (c : UInt256) + 2
  chainTreeRoot L := L.sum + 11

/-- A deployment on chain `1`, Bridgehub `10`, chain asset handler `11`, Bridgehub owner `12`,
chain `5`'s diamond at `55`, no pre-v31 batches. -/
def wCfg : Config where
  selfChainId := 1
  bridgehub := 10
  chainAssetHandler := 11
  emptyHash := 9
  v31Upgrade := fun _ => 0

/-- The environment of a call from `sender` in block `b`: chain `5`'s diamond is `55`, its
genesis batch root is `77`, no backfill is pending, the chain needs no second proof system. -/
def wEnv (sender : Address) (b : ℕ) : Env where
  sender := sender
  blockNumber := b
  timestamp := 1000 + b
  zkChain := fun c => if c = 5 then 55 else 0
  bridgehubOwner := 12
  allZKChainsLength := 0
  backfillPending := fun _ => false
  secondProofRequired := fun _ => false
  proofMode := fun _ => 0
  l2LogsRootHash := fun c n => if c = 5 ∧ n = 0 then 77 else 0

/-- The witness run: initialize; the Bridgehub adds chain `5` at batch `0` and seeds its
genesis root; the chain appends batch `1` (v32 flow) and batch `2` (v31 record-only flow); the
chain asset handler moves its counter to `5` (a round trip through another settlement layer);
the chain appends batch `6` (v32); the Bridgehub owner enables interop for it. -/
def witnessCalls : List (Env × Call) :=
  [ (wEnv 10 1, .initialize),
    (wEnv 10 2, .addNewChain 5 0),
    (wEnv 10 2, .seedGenesisRoot 5),
    (wEnv 55 3, .addChainBatchRootV32 5 1 101),
    (wEnv 55 3, .addChainBatchRoot 5 2 102),
    (wEnv 11 4, .setMigratingChainBatchNumber 5 5),
    (wEnv 55 5, .addChainBatchRootV32 5 6 106),
    (wEnv 12 6, .enableInterop 5 false) ]

end Contracts.MessageRoot
