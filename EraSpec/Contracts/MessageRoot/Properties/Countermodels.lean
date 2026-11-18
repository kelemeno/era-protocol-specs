import EraSpec.Contracts.MessageRoot.Specs.Countermodels
import EraSpec.Contracts.FullMerkle.Specs.CapacityInvariant
import EraSpec.Contracts.Merkle.Specs.RootForgeryPinned

/-!
# Properties: witnesses for every premise, the premises that are needed, and the checks that
carry the guarantees

Statements about `Specs/Countermodels.lean`.  Proofs are in `Proofs/Countermodels.lean`.  The
instances are `mrHashes` (toy arithmetic hashes), `mrConfig`, `mrEnv` and the call lists of
that file.

## Witnesses: the premises of `Properties/Model.lean` hold together

| Witness | Premises it instantiates |
|---|---|
| `EveryEntryPointRun` | `Reachable` alone (`ReachableInv`, `ChainIndexBijection`, `AggregatedRootFormula`, `HistoricalRootIsAggregated`, `BatchRootsBeyondCurrentAreZero`, `ChainTreeIsOrderedLog`, `ChainTreeSetUpOnce`, `NoReinitialization`, `ExistsCheckRedundant`); `ProofRootIsRecordedRoot`; the first case of `FinalNodeAcceptsIff` |
| `RegistrationPremisesHold` | `ChainAddedOnce` (both parts), `AddNewChainLiveness` (both senders) |
| `AppendPremisesHold` | `GenesisSeedIsFirstLeaf`, `AppendExact` (both flows), `AppendLiveness`, `InvKeptByEveryCall` |
| `MigrationPremisesHold` | `MigrationSkippedBatchesNeverRecorded` |
| `RunPremisesHold` | `BatchRootsWriteOnce`, `SettledBatchRootsFrozen`, `ChainTreeAppendOnly`, `CurrentBatchMonotone`, `RegistrationStable`, `ChainWriteProvenance`, `GenesisSeedOnce` |
| `WritersOnlyPremisesHold` | `ChainWritersOnly`, both premises; its counter clause needs the second |
| `LogIdPremisesHold` | `LogIdOncePerBlock`, with the bound attained and with the last emission in the block |
| `InteropPremisesHold` | `InteropEnabledOnce`, every antecedent |
| `SameTreesPremisesHold` | `AggregatedRootDeterminedByChainTrees`, `AggregatedRootPinsChainRootOrCollision` (its first disjunct holds) |
| `AggregatedRootCollisionFires` | `AggregatedRootPinsChainRootOrCollision`, with only its last disjunct true |
| `FinalNodeFallbackFollowsTheChain` | the second case of `FinalNodeAcceptsIff`; the premises of `MigrationSkippedBatchesNeverRecorded` and `SettledBatchRootsFrozen` except `v31UpgradeChainBatchNumber ≤ n`, whose verdict parts then fail |

## Countermodels

* `MigrationBeforeRegistrationIsOverwritten`: the registration premise of
  `MigrationSkippedBatchesNeverRecorded` is needed.
* `ChainTreePositionIsNotBatchNumber`: a chain tree's leaf position need not be its batch
  number, on reachable storage where every batch with a root here is in the tree
  (`PROTO-CONTIGUOUS-PUSH` in `ASSUMPTIONS.md`).
* Four source checks are load-bearing, each shown on the storage a variant without it reaches
  in one call from reachable storage: without `ChainExists` (`MRB:146-148`) a chain gets two
  slots (the injectivity part of `ChainIndexBijection` fails); without the consecutive-number
  check (`MRB:193`) a batch root lands beyond the counter (`BatchRootsBeyondCurrentAreZero`
  fails); without the `<=` check of `setMigratingChainBatchNumber` (`MRB:155`) the counter drops
  below a recorded batch, and one more model call leaves the chain tree out of batch order;
  without `MessageRootNotRegistered` in the record-only flow (`MRB:184-186`) an unregistered
  chain gets a batch root.
* On reachable storage the already-exists check (`MRB:188-191`) never decides the outcome
  (`ExistsCheckRedundant`), and in the record-and-push flow neither does
  `MessageRootNotRegistered`: the push into a never-set-up tree reverts by itself
  (`RecordRegisteredCheckLoadBearing`, second part).
-/

namespace Contracts.MessageRoot

open AttackVectors.CapacityInvariant (TreeDims)

/-! ## Witnesses -/

/-- **A RUN THROUGH EVERY ENTRY POINT.**  `mrCalls` (initialize; the Bridgehub adds chain `5`
and seeds its genesis root; append of batch `1`; record-only batch `2`; the chain asset
handler moves the counter to `5`; append of batch `6`; interop enabled; the chain asset handler
adds chain `6`, which appends batch `1`) succeeds from fresh storage.  At the end: three
chains, `5` at index `1` and `6` at index `2`; chain `5`'s counter is `6` and its tree holds
exactly the leaves of batches `0`, `1`, `6` (batch `2` is recorded but not in the tree); chain
`6`'s tree holds batch `1` only; interop is enabled for `5`.  The final proof node accepts the
recorded roots of batches `6` and `2` of chain `5`, rejects batch `3` (never recorded) for every
candidate root and every environment, and reverts on batch `0`; and the latest historical root
is the aggregated root. -/
def Properties.EveryEntryPointRun : Prop :=
  ∃ s : State, execCalls mrHashes mrConfig fresh mrCalls = some s ∧ Reachable mrHashes mrConfig s
    ∧ s.chainCount = 3 ∧ s.chainIndex 5 = 1 ∧ s.chainIndex 6 = 2
    ∧ s.currentChainBatchNumber 5 = 6
    ∧ s.chainLeaves 5 = [0, 1, 6].map (batchLeafOf mrHashes s 5)
    ∧ s.chainLeaves 6 = [1].map (batchLeafOf mrHashes s 6)
    ∧ s.chainBatchRoots 5 2 = 102 ∧ s.interopEnabled 5 = true
    ∧ finalNodeAccepts mrConfig (mrEnv 0 8) s 5 6 106 = some true
    ∧ finalNodeAccepts mrConfig (mrEnv 0 8) s 5 2 102 = some true
    ∧ (∀ (env : Env) (proven : Bytes32), finalNodeAccepts mrConfig env s 5 3 proven = some false)
    ∧ (∀ (env : Env) (proven : Bytes32), finalNodeAccepts mrConfig env s 5 0 proven = none)
    ∧ getAggregatedRoot mrConfig s = some (s.historicalRoots s.lastEmitBlock).1

/-- **THE REGISTRATION PREMISES HOLD.**  On reachable storage where chains `5` and `6` are
unregistered and neither `chainCount` nor `interopRootLogId` is about to overflow, the
Bridgehub's `addNewChain(5, 0)` succeeds, and so does the chain asset handler's
`addNewChain(6, 0)` (a different address from the Bridgehub).  On the reachable storage the
first call leaves, `5` is registered. -/
def Properties.RegistrationPremisesHold : Prop :=
  ∃ s t t' : State, Reachable mrHashes mrConfig s
    ∧ chainRegistered mrConfig s 5 = false ∧ chainRegistered mrConfig s 6 = false
    ∧ s.chainCount + 1 < UInt256.size ∧ s.interopRootLogId + 1 < UInt256.size
    ∧ (mrEnv 10 2).sender = mrConfig.bridgehub
    ∧ exec mrHashes mrConfig (mrEnv 10 2) s (.addNewChain 5 0) = some t
    ∧ (mrEnv 11 2).sender = mrConfig.chainAssetHandler
    ∧ mrConfig.chainAssetHandler ≠ mrConfig.bridgehub
    ∧ exec mrHashes mrConfig (mrEnv 11 2) s (.addNewChain 6 0) = some t'
    ∧ Reachable mrHashes mrConfig t ∧ chainRegistered mrConfig t 5 = true

/-- **THE APPEND PREMISES HOLD.**  On reachable storage the Bridgehub's `seedGenesisRoot(5)`
succeeds (the diamond answers a nonzero genesis root).  The storage it leaves satisfies `Inv`;
there the chain's diamond sends `addChainBatchRootV32(5, 1, 101)` with every premise of
`AppendLiveness` (counter `0`, root nonzero, no overflow) and succeeds; then
`addChainBatchRoot(5, 2, 102)` (record only) succeeds, records `102` at batch `2` and leaves the
tree, which holds batches `0` and `1`, unchanged. -/
def Properties.AppendPremisesHold : Prop :=
  ∃ s₂ s₃ s₄ s₅ : State, Reachable mrHashes mrConfig s₂
    ∧ exec mrHashes mrConfig (mrEnv 10 2) s₂ (.seedGenesisRoot 5) = some s₃
    ∧ (mrEnv 10 2).l2LogsRootHash 5 0 ≠ 0
    ∧ Reachable mrHashes mrConfig s₃ ∧ Inv mrHashes mrConfig s₃
    ∧ (mrEnv 55 3).sender = (mrEnv 55 3).zkChain 5 ∧ chainRegistered mrConfig s₃ 5 = true
    ∧ (101 : Bytes32) ≠ 0 ∧ s₃.currentChainBatchNumber 5 = 0
    ∧ s₃.currentChainBatchNumber 5 + 1 < UInt256.size ∧ s₃.interopRootLogId + 1 < UInt256.size
    ∧ exec mrHashes mrConfig (mrEnv 55 3) s₃ (.addChainBatchRootV32 5 1 101) = some s₄
    ∧ s₄.currentChainBatchNumber 5 = 1
    ∧ exec mrHashes mrConfig (mrEnv 55 3) s₄ (.addChainBatchRoot 5 2 102) = some s₅
    ∧ s₅.chainBatchRoots 5 2 = 102 ∧ s₅.chainLeaves 5 = s₄.chainLeaves 5
    ∧ s₄.chainLeaves 5 = [0, 1].map (batchLeafOf mrHashes s₄ 5)

/-- **THE MIGRATION PREMISES HOLD.**  On reachable storage where chain `5` is registered with
counter `2`, the chain asset handler's `setMigratingChainBatchNumber(5, 5)` succeeds (it skips
batch numbers `3`, `4`, `5`), and a nonempty run follows after which the counter is `6` and
batch `6` has a root. -/
def Properties.MigrationPremisesHold : Prop :=
  ∃ (s t u : State) (tr : List (Env × Call)), Reachable mrHashes mrConfig s
    ∧ chainRegistered mrConfig s 5 = true ∧ s.currentChainBatchNumber 5 = 2
    ∧ exec mrHashes mrConfig (mrEnv 11 4) s (.setMigratingChainBatchNumber 5 5) = some t
    ∧ Run mrHashes mrConfig t tr u ∧ tr ≠ []
    ∧ u.currentChainBatchNumber 5 = 6 ∧ u.chainBatchRoots 5 6 ≠ 0

/-- **THE RUN PREMISES HOLD.**  A five-call run from reachable storage on which chain `5` is
registered with counter `2` and nonzero roots at batches `0`, `1`, `2`.  Along it chain `5`'s
counter goes to `6`, its tree grows, a root is written at batch `6`, and `chainCount` goes from
`2` to `3`. -/
def Properties.RunPremisesHold : Prop :=
  ∃ (s t : State) (tr : List (Env × Call)), Reachable mrHashes mrConfig s
    ∧ Run mrHashes mrConfig s tr t ∧ tr.length = 5
    ∧ chainRegistered mrConfig s 5 = true ∧ s.currentChainBatchNumber 5 = 2
    ∧ s.chainBatchRoots 5 0 ≠ 0 ∧ s.chainBatchRoots 5 1 ≠ 0 ∧ s.chainBatchRoots 5 2 ≠ 0
    ∧ t.chainBatchRoots 5 6 ≠ s.chainBatchRoots 5 6 ∧ t.chainLeaves 5 ≠ s.chainLeaves 5
    ∧ t.currentChainBatchNumber 5 = 6 ∧ s.chainCount = 2 ∧ t.chainCount = 3

/-- **`ChainWritersOnly`'S PREMISES HOLD, AND ITS SECOND ONE IS NEEDED.**  From reachable
storage, the run `mrWritersOnlyFirst ++ mrWritersOnlySecond`: none of its calls is sent by
chain `5`'s diamond or the Bridgehub, and none of `mrWritersOnlySecond` (nonempty) by the chain
asset handler.  Along the first part chain `5`'s counter changes; along the second the
aggregated root changes. -/
def Properties.WritersOnlyPremisesHold : Prop :=
  ∃ s s' t : State, Reachable mrHashes mrConfig s
    ∧ Run mrHashes mrConfig s mrWritersOnlyFirst s'
    ∧ Run mrHashes mrConfig s' mrWritersOnlySecond t
    ∧ Run mrHashes mrConfig s (mrWritersOnlyFirst ++ mrWritersOnlySecond) t
    ∧ (∀ p ∈ mrWritersOnlyFirst ++ mrWritersOnlySecond,
        p.1.sender ≠ p.1.zkChain 5 ∧ p.1.sender ≠ mrConfig.bridgehub)
    ∧ (∀ p ∈ mrWritersOnlySecond, p.1.sender ≠ mrConfig.chainAssetHandler)
    ∧ mrWritersOnlySecond ≠ []
    ∧ s'.currentChainBatchNumber 5 ≠ s.currentChainBatchNumber 5
    ∧ getAggregatedRoot mrConfig t ≠ getAggregatedRoot mrConfig s'

/-- **`LogIdOncePerBlock`'S PREMISES HOLD.**  From reachable storage whose last emission was not
in block `2`, the two calls `addNewChain(5, 0)` and `seedGenesisRoot(5)`, both in block `2`,
each change the aggregated root, and `interopRootLogId` grows by exactly one.  The second call
alone, from the storage `s₂` the first leaves (last emission in block `2`), changes the
aggregated root and leaves `interopRootLogId` unchanged. -/
def Properties.LogIdPremisesHold : Prop :=
  ∃ s₁ s₂ s₃ : State, Reachable mrHashes mrConfig s₁
    ∧ Run mrHashes mrConfig s₁
        [(mrEnv 10 2, .addNewChain 5 0), (mrEnv 10 2, .seedGenesisRoot 5)] s₃
    ∧ exec mrHashes mrConfig (mrEnv 10 2) s₁ (.addNewChain 5 0) = some s₂
    ∧ Run mrHashes mrConfig s₂ [(mrEnv 10 2, .seedGenesisRoot 5)] s₃
    ∧ s₁.lastEmitBlock ≠ 2 ∧ s₃.interopRootLogId = s₁.interopRootLogId + 1
    ∧ s₂.lastEmitBlock = 2 ∧ s₃.interopRootLogId = s₂.interopRootLogId
    ∧ getAggregatedRoot mrConfig s₁ ≠ getAggregatedRoot mrConfig s₂
    ∧ getAggregatedRoot mrConfig s₂ ≠ getAggregatedRoot mrConfig s₃

/-- **`InteropEnabledOnce`'S ANTECEDENTS HOLD.**  A run of one call, the Bridgehub owner's
`enableInterop(5, false)`, enables interop for chain `5`, which was not enabled; on the storage
it leaves a second `enableInterop(5, false)` from the owner reverts, and a further two-call run
keeps chain `5` enabled. -/
def Properties.InteropPremisesHold : Prop :=
  ∃ s t u : State, Run mrHashes mrConfig s [(mrEnv 12 6, .enableInterop 5 false)] t
    ∧ s.interopEnabled 5 = false ∧ t.interopEnabled 5 = true
    ∧ exec mrHashes mrConfig (mrEnv 12 8) t (.enableInterop 5 false) = none
    ∧ Run mrHashes mrConfig t
        [(mrEnv 11 7, .addNewChain 6 0), (mrEnv 66 7, .addChainBatchRootV32 6 1 201)] u
    ∧ u.interopEnabled 5 = true

/-- **THE SAME-TREES PREMISES HOLD ON DIFFERENT STORAGES.**  Two reachable storages with the
same chains in the same slots and the same chain trees, but different counters for chain `5`
and different recorded roots at its batch `2`.  Chain `5` is registered, in the same slot in
both, and the aggregated roots are equal. -/
def Properties.SameTreesPremisesHold : Prop :=
  ∃ s s' : State, Reachable mrHashes mrConfig s ∧ Reachable mrHashes mrConfig s'
    ∧ s.chainCount = s'.chainCount
    ∧ (∀ i, i < s.chainCount → s.chainIndexToId i = s'.chainIndexToId i)
    ∧ (∀ c, chainRegistered mrConfig s c = true → s.chainLeaves c = s'.chainLeaves c)
    ∧ chainRegistered mrConfig s 5 = true ∧ s'.chainIndexToId (s.chainIndex 5) = 5
    ∧ getAggregatedRoot mrConfig s = getAggregatedRoot mrConfig s'
    ∧ s.currentChainBatchNumber 5 ≠ s'.currentChainBatchNumber 5
    ∧ s.chainBatchRoots 5 2 ≠ s'.chainBatchRoots 5 2

/-- **THE COLLISION DISJUNCT OF `AggregatedRootPinsChainRootOrCollision` FIRES.**  With the toy
hashes, the storages `s` and `s'` that `mrCollisionCalls 101 201` and `mrCollisionCalls 102 200`
reach have the same `chainCount`, chain `5` registered in the same slot, and equal aggregated
roots, yet chain `5`'s tree roots differ, and so do their chain-id leaves.  The located
`TreeCollision` holds on `5`'s slot. -/
def Properties.AggregatedRootCollisionFires : Prop :=
  ∃ s s' : State, execCalls mrHashes mrConfig fresh (mrCollisionCalls 101 201) = some s
    ∧ execCalls mrHashes mrConfig fresh (mrCollisionCalls 102 200) = some s'
    ∧ Reachable mrHashes mrConfig s ∧ Reachable mrHashes mrConfig s'
    ∧ s.chainCount = s'.chainCount ∧ chainRegistered mrConfig s 5 = true
    ∧ s'.chainIndexToId (s.chainIndex 5) = 5
    ∧ getAggregatedRoot mrConfig s = getAggregatedRoot mrConfig s'
    ∧ chainRootOf mrHashes (s.chainLeaves 5) ≠ chainRootOf mrHashes (s'.chainLeaves 5)
    ∧ mrHashes.chainIdLeaf (chainRootOf mrHashes (s.chainLeaves 5)) 5
        ≠ mrHashes.chainIdLeaf (chainRootOf mrHashes (s'.chainLeaves 5)) 5
    ∧ MerkleSpec.Pinned.TreeCollision mrHashes.node mrConfig.emptyHash (sharedLeaves mrHashes s)
        (sharedLeaves mrHashes s')
        (AttackVectors.CapacityInvariant.push^[s.chainCount] (⟨0, 0⟩ : TreeDims)).height
        (s.chainIndex 5)

/-- **BELOW `v31UpgradeChainBatchNumber` THE FINAL NODE FOLLOWS THE CHAIN'S GETTER.**  Under
`mrConfigPreV31` (chain `5`'s `v31UpgradeChainBatchNumber` is `4`): on reachable storage where
chain `5` is registered with counter `1`, the chain asset handler's
`setMigratingChainBatchNumber(5, 5)` succeeds, and the chain then appends batch `6`.  On the
reachable storage this leaves, batch `3` (skipped by the migration) has no root, and the final
proof node accepts for it the nonzero root the chain's diamond answers for `l2LogsRootHash(3)`;
with an environment whose diamond answers `0` it rejects the same candidate.  So the second case
of `FinalNodeAcceptsIff` occurs, and without `cfg.v31Upgrade c ≤ n` the verdict parts of
`SettledBatchRootsFrozen` (here with the empty run) and `MigrationSkippedBatchesNeverRecorded`
fail. -/
def Properties.FinalNodeFallbackFollowsTheChain : Prop :=
  ∃ s t u : State, Reachable mrHashes mrConfigPreV31 s
    ∧ chainRegistered mrConfigPreV31 s 5 = true ∧ s.currentChainBatchNumber 5 = 1
    ∧ exec mrHashes mrConfigPreV31 (mrEnv 11 4) s (.setMigratingChainBatchNumber 5 5) = some t
    ∧ Run mrHashes mrConfigPreV31 t [(mrEnv 55 5, .addChainBatchRootV32 5 6 106)] u
    ∧ Reachable mrHashes mrConfigPreV31 u ∧ chainRegistered mrConfigPreV31 u 5 = true
    ∧ u.currentChainBatchNumber 5 = 6 ∧ u.chainBatchRoots 5 3 = 0
    ∧ 3 < mrConfigPreV31.v31Upgrade 5 ∧ (mrEnv 0 8).l2LogsRootHash 5 3 ≠ 0
    ∧ finalNodeAccepts mrConfigPreV31 (mrEnv 0 8) u 5 3 ((mrEnv 0 8).l2LogsRootHash 5 3)
        = some true
    ∧ finalNodeAccepts mrConfigPreV31 { mrEnv 0 8 with l2LogsRootHash := fun _ _ => 0 } u 5 3
        ((mrEnv 0 8).l2LogsRootHash 5 3) = some false

/-! ## Countermodels for dropped premises -/

/-- **THE REGISTRATION PREMISE OF `MigrationSkippedBatchesNeverRecorded` IS NEEDED.**
`setMigratingChainBatchNumber` has no registration check (`MRB:153-157`).  On reachable storage
where chain `5` is unregistered with counter `0`, the chain asset handler's
`setMigratingChainBatchNumber(5, 5)` succeeds; then `mrReregistrationCalls` runs: the
Bridgehub's `addNewChain(5, 0)`, which sets the counter back to `0` (`MRB:282`), the genesis
seed, and the chain's append of batch `1`.  At the end the counter is below `5`, batch `1`
(between the old counter and `5`) has a nonzero root, and the final proof node accepts it. -/
def Properties.MigrationBeforeRegistrationIsOverwritten : Prop :=
  ∃ s t u : State, Reachable mrHashes mrConfig s
    ∧ chainRegistered mrConfig s 5 = false ∧ s.currentChainBatchNumber 5 = 0
    ∧ exec mrHashes mrConfig (mrEnv 11 2) s (.setMigratingChainBatchNumber 5 5) = some t
    ∧ Run mrHashes mrConfig t mrReregistrationCalls u
    ∧ u.currentChainBatchNumber 5 < 5 ∧ mrConfig.v31Upgrade 5 ≤ 1
    ∧ u.chainBatchRoots 5 1 ≠ 0
    ∧ finalNodeAccepts mrConfig (mrEnv 0 8) u 5 1 (u.chainBatchRoots 5 1) = some true

/-- **A CHAIN TREE'S LEAF POSITION NEED NOT BE ITS BATCH NUMBER.**  After `mrMigrationCalls`
(genesis seed, batch `1`, the chain asset handler moves the counter from `1` to `5`, batch `6`:
every batch of chain `5` with a root here is pushed into its tree, and the first pushed batch is
`0`), chain `5`'s tree holds the leaves of batches `0`, `1`, `6`, in that order: position `2`
holds batch `6`.  Batches `2` to `5` have no root here. -/
def Properties.ChainTreePositionIsNotBatchNumber : Prop :=
  ∃ s : State, execCalls mrHashes mrConfig fresh mrMigrationCalls = some s
    ∧ Reachable mrHashes mrConfig s ∧ chainRegistered mrConfig s 5 = true
    ∧ s.currentChainBatchNumber 5 = 6
    ∧ s.chainLeaves 5 = [0, 1, 6].map (batchLeafOf mrHashes s 5)
    ∧ ∀ n, 2 ≤ n → n ≤ 5 → s.chainBatchRoots 5 n = 0

/-! ## The source checks the guarantees rest on -/

/-- **`ChainExists` IS LOAD-BEARING.**  There is reachable storage on which the model's
`addNewChain(c, start)` reverts but the variant without the `chainRegistered` check succeeds
and leaves two distinct slots below `chainCount` holding the same chain id. -/
def Properties.RegisteredCheckLoadBearing : Prop :=
  ∃ (H : Hashes) (cfg : Config) (s t : State) (env : Env) (c start : ℕ), Reachable H cfg s
    ∧ exec H cfg env s (.addNewChain c start) = none
    ∧ execNoRegisteredCheck H cfg env s (.addNewChain c start) = some t
    ∧ ∃ i j, i < t.chainCount ∧ j < t.chainCount ∧ i ≠ j
      ∧ t.chainIndexToId i = c ∧ t.chainIndexToId j = c

/-- **THE CONSECUTIVE CHECK IS LOAD-BEARING.**  There is reachable storage on which the model's
`addChainBatchRootV32(c, n, r)` from the chain's diamond reverts but the variant without
`_batchNumber == currentChainBatchNumber + 1` succeeds and records a nonzero root at a batch
number above the chain's new counter. -/
def Properties.ConsecutiveCheckLoadBearing : Prop :=
  ∃ (H : Hashes) (cfg : Config) (s t : State) (env : Env) (c n : ℕ) (r : Bytes32),
    Reachable H cfg s
    ∧ exec H cfg env s (.addChainBatchRootV32 c n r) = none
    ∧ execNoConsecutiveCheck H cfg env s (.addChainBatchRootV32 c n r) = some t
    ∧ t.currentChainBatchNumber c < n ∧ t.chainBatchRoots c n ≠ 0

/-- **THE `<=` CHECK OF `setMigratingChainBatchNumber` IS LOAD-BEARING.**  There is reachable
storage on which the model's `setMigratingChainBatchNumber(c, k)` from the chain asset handler
reverts, but the variant without `currentChainBatchNumber[c] <= k` (`MRB:155`) succeeds and
leaves a nonzero batch root above the chain's counter.  From there the unmodified model accepts
an append of batch `k + 1` by the chain, and the chain's tree then holds batches `0, 1, 6, 3`
in that order: not increasing. -/
def Properties.MigratingCheckLoadBearing : Prop :=
  ∃ (H : Hashes) (cfg : Config) (s t u : State) (env env' : Env) (c k : ℕ) (r : Bytes32),
    Reachable H cfg s
    ∧ exec H cfg env s (.setMigratingChainBatchNumber c k) = none
    ∧ execNoMigratingCheck H cfg env s (.setMigratingChainBatchNumber c k) = some t
    ∧ (∃ n, t.currentChainBatchNumber c < n ∧ t.chainBatchRoots c n ≠ 0)
    ∧ exec H cfg env' t (.addChainBatchRootV32 c (k + 1) r) = some u
    ∧ u.chainLeaves c = [0, 1, 6, 3].map (batchLeafOf H u c)

/-- **`MessageRootNotRegistered` IS LOAD-BEARING IN THE RECORD-ONLY FLOW, NOT IN THE
RECORD-AND-PUSH FLOW.**  (1) There is reachable storage and an unregistered chain `c` for which
the model's `addChainBatchRoot(c, n, r)` from `getZKChain(c)` reverts, but the variant without
the registration check of `_recordChainBatchRoot` (`MRB:184-186`) succeeds: `c` is still
unregistered and has a nonzero batch root.  (2) On every reachable storage, the same variant's
`addChainBatchRootV32(c, n, r)` for an unregistered `c` reverts anyway: the push into the
never-set-up chain tree underflows (`DIM:95`). -/
def Properties.RecordRegisteredCheckLoadBearing : Prop :=
  (∃ (H : Hashes) (cfg : Config) (s t : State) (env : Env) (c n : ℕ) (r : Bytes32),
    Reachable H cfg s ∧ chainRegistered cfg s c = false
    ∧ exec H cfg env s (.addChainBatchRoot c n r) = none
    ∧ execNoRecordRegisteredCheck H cfg env s (.addChainBatchRoot c n r) = some t
    ∧ chainRegistered cfg t c = false ∧ t.chainBatchRoots c n ≠ 0)
  ∧ ∀ (H : Hashes) (cfg : Config) (s : State) (env : Env) (c n : ℕ) (r : Bytes32),
      Reachable H cfg s → chainRegistered cfg s c = false →
        execNoRecordRegisteredCheck H cfg env s (.addChainBatchRootV32 c n r) = none

/-- **THE ALREADY-EXISTS CHECK NEVER DECIDES ON REACHABLE STORAGE.**  `_recordChainBatchRoot`
with and without `require(chainBatchRoots[c][n] == bytes32(0))` (`MRB:188-191`) are the same
function on every reachable storage: the consecutive check alone rejects every `n` with a
recorded root. -/
def Properties.ExistsCheckRedundant : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State) (c n : ℕ) (r : Bytes32), Reachable H cfg s →
    recordChainBatchRoot cfg c n r s = recordNoExistsCheck cfg c n r s

end Contracts.MessageRoot
