import EraSpec.Protocol.BatchCounters.Specs.MessageRootSync

/-!
# Properties: the message root's counter tracks each diamond's executed count

Statements about `EraSpec.Protocol.BatchCounters.Specs.MessageRootSync` (source `b17415d20`).
Proofs are in `EraSpec.Protocol.BatchCounters.Proofs.MessageRootSync`.

* **The layer invariant.** Every step preserves `HubInv`: the message root and the bridgehub
  register the same chains, an unregistered chain has no batch root, no batch after
  `currentChainBatchNumber` has a root (the NatSpec at `MessageRootBase.sol:89`), and every
  nonzero batch root is the diamond's `l2LogsRootHashes` entry (`HubStepPreservesInv`,
  `ReachableHubsSatisfyInv`). Batch roots are write-once (`BatchRootsWriteOnce`), and every
  batch an executor executes has its logs root recorded in both places for good
  (`ExecutedRootsRecorded`).
* **Sync.** Once a chain's two counters agree they agree after every step whose mint data, if
  any, is consistent (`SyncedStaysSynced`, `SyncedAlongRuns`); every way of registering a
  chain starts it synced (the same statements: `Synced` is vacuous for an unregistered
  chain). With migrations disabled, as at `b17415d20`, no premise on mint data is needed
  (`HeadRunsKeepSync`), and every chain of a layer reachable from the empty one is synced
  (`ReachableHeadHubsSynced`).
* **Liveness.** On a layer satisfying the invariant, an execute that passes the executor's own
  modelled checks passes the message root's checks iff the counters agree, provided no logs root
  is zero (`ExecuteNeverRevertsInMessageRoot`, `ExecuteEnabledIffSynced`); a zero logs root is
  always refused (`ZeroLogsRootRefused`), also on a synced chain for a call that passes the
  executor's own modelled checks (`ZeroLogsRootRefusedOnSyncedChain`).
* **Drift wedges the chain.** A chain whose counters disagree can never execute
  (`DriftBlocksExecute`), and with migrations disabled nothing changes either counter, so it
  never executes again (`DriftPersistsAtHead`). A legacy chain whose v31 counter was never
  saved is such a chain, on a layer that satisfies `HubInv` (`LegacyUnsavedChainIsWedged`); the
  same chain with the counter set to its executed count executes (`LegacySavedChainExecutes`).

## Witnesses

| Witness | Premises it meets |
|---|---|
| `HubSyncWitness` | a run from the empty layer through `createNewChain`, commits, a proof, executes of two chains and `registerAlreadyDeployedZKChain` of a chain with seven batches executed (`HubStepPreservesInv`, `ReachableHubsSatisfyInv`, `BatchRootsWriteOnce` with the genesis root and executed roots in place, `ExecutedRootsRecorded`, `SyncedStaysSynced`, `SyncedAlongRuns`, `HeadRunsKeepSync`, `ReachableHeadHubsSynced`) |
| `LegacySavedChainExecutes` | an invariant layer, a synced chain and a call passing the executor's modelled checks with nonzero roots (`ExecuteNeverRevertsInMessageRoot`, the `←` direction of `ExecuteEnabledIffSynced`) |
| `LegacyUnsavedChainIsWedged` | a chain whose counters disagree on an invariant layer, and runs with migrations disabled from it (`DriftBlocksExecute`, `DriftPersistsAtHead`, the `→` direction of `ExecuteEnabledIffSynced`) |
| `ZeroLogsRootRefusedOnSyncedChain` | `ZeroLogsRootRefused` on a synced chain of an invariant layer, for a call passing the executor's modelled checks |
| `HubUpgradeRevertWitness` | a run from the empty layer with a nonzero genesis upgrade transaction, a commit that records the upgrade batch, a revert that resets it, a re-commit, an execution that clears both upgrade fields and an in-tree upgrade that sets a new transaction hash (`HubStepPreservesInv`, `SyncedStaysSynced`, `SyncedAlongRuns`, `HeadRunsKeepSync`, `ReachableHubsSatisfyInv`, `ReachableHeadHubsSynced` and `BatchRootsWriteOnce` through revert and upgrade steps; `ExecutedRootsRecorded` for a batch number whose first committed batch was reverted) |

Mint steps with consistent data are instantiated in `MigrationContinuity` (`RoundTripWitness`,
`PendingUpgradeMigratesWitness`).
-/

namespace Contracts.BatchCounters

/-! ## The layer invariant -/

/-- **EVERY STEP PRESERVES THE LAYER INVARIANT**, for every configuration, mint data
included. -/
def Properties.HubStepPreservesInv : Prop :=
  ∀ (cfg : HubConfig) (h h' : Hub) (l : HubLabel), HubInv h → HubStep cfg h l h' → HubInv h'

/-- **THE EMPTY LAYER SATISFIES THE INVARIANT.** -/
def Properties.EmptyHubInv : Prop := HubInv emptyHub

/-- **EVERY LAYER REACHABLE FROM THE EMPTY ONE SATISFIES THE INVARIANT**; in particular no batch
after `currentChainBatchNumber` has a root (`MessageRootBase.sol:89`). -/
def Properties.ReachableHubsSatisfyInv : Prop :=
  ∀ (cfg : HubConfig) (ls : List HubLabel) (h : Hub), HubRun cfg emptyHub ls h →
    HubInv h ∧ ∀ c n, h.mr.cur c < n → h.mr.roots c n = 0

/-- **BATCH ROOTS ARE WRITE-ONCE.** No step changes a nonzero `chainBatchRoots[c][n]`. -/
def Properties.BatchRootsWriteOnce : Prop :=
  ∀ (cfg : HubConfig) (h h' : Hub) (l : HubLabel) (c n : ℕ), HubStep cfg h l h' →
    h.mr.roots c n ≠ 0 → h'.mr.roots c n = h.mr.roots c n

/-- **EXECUTED BATCHES ARE RECORDED FOR GOOD.** Along any run from a layer satisfying the
invariant, for every batch info `b` of an `execute c infos` step of the run, at the end of the
run the message root holds `b`'s logs root as chain `c`'s root of batch `b.batchNumber`, and
so does `c`'s diamond as its `l2LogsRootHashes` entry. -/
def Properties.ExecutedRootsRecorded : Prop :=
  ∀ (cfg : HubConfig) (h h' : Hub) (ls : List HubLabel) (c : ChainId) (infos : List BatchInfo)
    (b : BatchInfo),
    HubInv h → HubRun cfg h ls h' → HubLabel.execute c infos ∈ ls → b ∈ infos →
    h'.mr.roots c b.batchNumber = b.logsRoot ∧ b.logsRoot ≠ 0 ∧
      ∃ d', h'.chains c = some d' ∧ d'.logsRoot b.batchNumber = b.logsRoot

/-! ## Sync -/

/-- **SYNC IS PRESERVED.** If chain `c`'s counters agree (or `c` has no diamond), they agree
after any step whose mint data, if it is a mint, is consistent. Registration steps start a
chain synced: `createNewChain` at `0`, `registerAlreadyDeployedZKChain` at the diamond's
executed count, and a mint at the data's batch number. -/
def Properties.SyncedStaysSynced : Prop :=
  ∀ (cfg : HubConfig) (h h' : Hub) (l : HubLabel) (c : ChainId),
    HubStep cfg h l h' → l.MintConsistent → Synced h c → Synced h' c

/-- **SYNC ALONG RUNS**, given consistent mint data in the run. -/
def Properties.SyncedAlongRuns : Prop :=
  ∀ (cfg : HubConfig) (h h' : Hub) (ls : List HubLabel) (c : ChainId),
    HubRun cfg h ls h' → (∀ l ∈ ls, HubLabel.MintConsistent l) → Synced h c → Synced h' c

/-- **SYNC AT `b17415d20`.** With migrations disabled every run keeps a synced chain synced;
no premise on mint data is needed, because no mint step can occur. -/
def Properties.HeadRunsKeepSync : Prop :=
  ∀ (cfg : HubConfig) (h h' : Hub) (ls : List HubLabel) (c : ChainId),
    cfg.migrationsEnabled = false → HubRun cfg h ls h' → Synced h c → Synced h' c

/-- **EVERY CHAIN OF A LAYER REACHABLE AT `b17415d20` IS SYNCED.** With migrations disabled,
every layer reachable from the empty one satisfies the invariant and has every chain's two
counters equal. -/
def Properties.ReachableHeadHubsSynced : Prop :=
  ∀ (cfg : HubConfig) (ls : List HubLabel) (h : Hub), cfg.migrationsEnabled = false →
    HubRun cfg emptyHub ls h → HubInv h ∧ ∀ c, Synced h c

/-! ## Liveness of execution -/

/-- **EXECUTION NEVER REVERTS IN THE MESSAGE ROOT.** On a layer satisfying the invariant, if
chain `c`'s counters agree and an execute call passes the executor's own modelled checks with
no zero logs root, every `addChainBatchRootV32` call of it succeeds, the counter ends at the
diamond's new executed count, and the step exists. -/
def Properties.ExecuteNeverRevertsInMessageRoot : Prop :=
  ∀ (cfg : HubConfig) (h : Hub) (c : ChainId) (d : Diamond) (infos : List BatchInfo),
    HubInv h → Synced h c → h.chains c = some d → ExecGuard cfg.hash d infos →
    (∀ b ∈ infos, b.logsRoot ≠ 0) →
    (∃ m', appendAll h.mr c infos = some m' ∧ m'.cur c = (executeEffect d infos).executed) ∧
      ∃ h', HubStep cfg h (.execute c infos) h'

/-- **A ZERO LOGS ROOT IS REFUSED.** Whatever the state, the message root refuses an append
list containing a zero logs root (`MessageRootBase.sol:187`), so no execute of it exists. -/
def Properties.ZeroLogsRootRefused : Prop :=
  ∀ (cfg : HubConfig) (h : Hub) (c : ChainId) (infos : List BatchInfo),
    (∃ b ∈ infos, b.logsRoot = 0) →
    appendAll h.mr c infos = none ∧ ∀ h', ¬ HubStep cfg h (.execute c infos) h'

/-- **EXECUTION IS ENABLED IFF THE COUNTERS AGREE.** On a layer satisfying the invariant, for an
execute call that passes the executor's own modelled checks with no zero logs root, the step
exists exactly when `currentChainBatchNumber[c]` equals the diamond's `totalBatchesExecuted`. -/
def Properties.ExecuteEnabledIffSynced : Prop :=
  ∀ (cfg : HubConfig) (h : Hub) (c : ChainId) (d : Diamond) (infos : List BatchInfo),
    HubInv h → h.chains c = some d → ExecGuard cfg.hash d infos →
    (∀ b ∈ infos, b.logsRoot ≠ 0) →
    ((∃ h', HubStep cfg h (.execute c infos) h') ↔ h.mr.cur c = d.executed)

/-! ## Drift -/

/-- **DRIFT BLOCKS EXECUTION.** If chain `c`'s counters disagree, no execute of `c` exists,
whatever the batches. -/
def Properties.DriftBlocksExecute : Prop :=
  ∀ (cfg : HubConfig) (h : Hub) (c : ChainId) (d : Diamond),
    h.chains c = some d → h.mr.cur c ≠ d.executed →
    ∀ (infos : List BatchInfo) (h' : Hub), ¬ HubStep cfg h (.execute c infos) h'

/-- **DRIFT IS PERMANENT AT `b17415d20`.** With migrations disabled, along any run from a layer
where chain `c`'s counters disagree, both counters keep their values and the run executes no
batch of `c`. -/
def Properties.DriftPersistsAtHead : Prop :=
  ∀ (cfg : HubConfig) (h h' : Hub) (ls : List HubLabel) (c : ChainId) (d : Diamond),
    cfg.migrationsEnabled = false → HubRun cfg h ls h' → h.chains c = some d →
    h.mr.cur c ≠ d.executed →
    (∃ d', h'.chains c = some d' ∧ d'.executed = d.executed ∧ h'.mr.cur c = h.mr.cur c) ∧
      execNumbers c ls = []

/-- **A LEGACY CHAIN WHOSE V31 COUNTER WAS NEVER SAVED IS WEDGED AT `b17415d20`.** Chain `7` of
`wLegacyHub` has executed five batches, its message-root counter is `0`, and it has no batch
root. The layer satisfies the invariant; the call executing batch 6 passes the executor's own
checks and has a nonzero logs root, yet no execute step exists; and along every run with the
`b17415d20` configuration chain `7` executes nothing. -/
def Properties.LegacyUnsavedChainIsWedged : Prop :=
  HubInv wLegacyHub ∧ ExecGuard headL1.hash wLegacyDiamond [wInfo 6] ∧ (wInfo 6).logsRoot ≠ 0 ∧
    (∀ h', ¬ HubStep headL1 wLegacyHub (.execute 7 [wInfo 6]) h') ∧
    ∀ (ls : List HubLabel) (h' : Hub), HubRun headL1 wLegacyHub ls h' → execNumbers 7 ls = []

/-- **THE SAME CHAIN EXECUTES ONCE ITS COUNTER IS SAVED.** With `currentChainBatchNumber[7]`
set to `5` (what `saveV31UpgradeChainBatchNumber` at `main` `70096e2ea` writes for this
diamond), the layer satisfies the invariant, chain `7` is synced, and executing batch 6
succeeds, leaving both counters at `6` and batch 6's root recorded in both places. -/
def Properties.LegacySavedChainExecutes : Prop :=
  let h : Hub := { wLegacyHub with mr := { wLegacyHub.mr with cur := upd (fun _ => 0) 7 5 } }
  HubInv h ∧ Synced h 7 ∧
    ∃ h', HubStep headL1 h (.execute 7 [wInfo 6]) h' ∧ h'.mr.cur 7 = 6 ∧
      h'.mr.roots 7 6 = 26 ∧ ∃ d', h'.chains 7 = some d' ∧ d'.executed = 6 ∧ d'.logsRoot 6 = 26

/-- **A ZERO LOGS ROOT IS REFUSED ON A SYNCED CHAIN.** Take the layer of
`LegacySavedChainExecutes` (chain `7` synced at five executed batches), with batch 6 stored under
the stand-in hash of the info `b` whose logs root is `0`. The layer satisfies the invariant,
chain `7` is synced, and the call executing `b` passes the executor's own modelled checks, yet no
execute step exists: the `logsRoot ≠ 0` premise of `ExecuteNeverRevertsInMessageRoot` cannot be
dropped. -/
def Properties.ZeroLogsRootRefusedOnSyncedChain : Prop :=
  let b : BatchInfo := { batchNumber := 6, logsRoot := 0, rest := 0 }
  let d : Diamond := { wLegacyDiamond with batchHash := upd (fun _ => 0) 6 (wHash b) }
  let h : Hub := { mr := { wLegacyHub.mr with cur := upd (fun _ => 0) 7 5 },
                   chains := upd (fun _ => none) 7 (some d) }
  HubInv h ∧ Synced h 7 ∧ ExecGuard headL1.hash d [b] ∧ ∀ h', ¬ HubStep headL1 h (.execute 7 [b]) h'

/-! ## Witness -/

/-- **A RUN THROUGH `createNewChain`, `registerAlreadyDeployedZKChain`, COMMIT, PROVE AND
EXECUTE.** From the empty layer with the `b17415d20` L1 configuration: create chain `1`; commit
batches 1 and 2; prove both; execute both in one call; register an already-deployed chain `2`
that has executed seven batches and committed and verified an eighth; execute that eighth batch.
At the end both chains are synced, chain `1`'s counter is `2` and chain `2`'s is `8`, batch roots
`21`, `22` (chain `1`) and `28` (chain `2`) are recorded in the message root and in the diamonds,
and the run's executed batch numbers of chain `1` are `[1, 2]`. Registration by a mint is in
`RoundTripWitness` (`MigrationContinuity`); a revert and an upgrade are in
`HubUpgradeRevertWitness`. -/
def Properties.HubSyncWitness : Prop :=
  ∃ (ls : List HubLabel) (h : Hub), HubRun headL1 emptyHub ls h ∧
    execNumbers 1 ls = [1, 2] ∧ execNumbers 2 ls = [8] ∧
    HubInv h ∧ Synced h 1 ∧ Synced h 2 ∧ h.mr.cur 1 = 2 ∧ h.mr.cur 2 = 8 ∧
    h.mr.roots 1 1 = 21 ∧ h.mr.roots 1 2 = 22 ∧ h.mr.roots 2 8 = 28 ∧
    (∃ d, h.chains 1 = some d ∧ d.executed = 2 ∧ d.logsRoot 1 = 21 ∧ d.logsRoot 2 = 22) ∧
    ∃ d, h.chains 2 = some d ∧ d.executed = 8 ∧ d.logsRoot 8 = 28

/-- **A RUN WITH THE GENESIS UPGRADE TRANSACTION, A REVERT AND AN IN-TREE UPGRADE.** From the empty
layer with the `b17415d20` L1 configuration: create chain `1` with genesis upgrade transaction
hash `77`, and commit the batch 1 `wInfoReverted` (logs root `31`); afterwards one batch is
committed and the upgrade fields are `77` and `1` (batch 1 is the upgrade batch). Revert to `0`
batches: none is committed and the upgrade fields are `77` and `0`. Commit batch 1 again, now
`wInfo 1` (logs root `21`), prove it and execute it: one batch is executed and both upgrade fields
are `0`. Then an in-tree upgrade with transaction hash `88`. At the end the layer satisfies the
invariant, chain `1` is synced with counter `1`, its diamond has one batch executed, its batch
root of batch 1 is `21` in the message root and in the diamond, its stored hash of batch 1 is
that of `wInfo 1` and not that of `wInfoReverted` (under the witness hash `wHash`), and its upgrade
fields are `88` and `0`. -/
def Properties.HubUpgradeRevertWitness : Prop :=
  ∃ h₁ h₂ h₃ h : Hub,
    HubRun headL1 emptyHub [.createChain 1 13 12 77, .commit 1 wInfo0 wInfoReverted] h₁ ∧
    (∃ d, h₁.chains 1 = some d ∧ d.committed = 1 ∧ d.upgradeTxHash = 77 ∧ d.upgradeBatch = 1) ∧
    HubStep headL1 h₁ (.revert 1 0) h₂ ∧
    (∃ d, h₂.chains 1 = some d ∧ d.committed = 0 ∧ d.upgradeTxHash = 77 ∧ d.upgradeBatch = 0) ∧
    HubRun headL1 h₂ [.commit 1 wInfo0 (wInfo 1), .prove 1 1, .execute 1 [wInfo 1]] h₃ ∧
    (∃ d, h₃.chains 1 = some d ∧ d.executed = 1 ∧ d.upgradeTxHash = 0 ∧ d.upgradeBatch = 0) ∧
    HubStep headL1 h₃ (.upgrade 1 88) h ∧
    HubInv h ∧ Synced h 1 ∧ h.mr.cur 1 = 1 ∧ h.mr.roots 1 1 = 21 ∧
    ∃ d, h.chains 1 = some d ∧ d.executed = 1 ∧ d.logsRoot 1 = 21 ∧
      d.batchHash 1 = headL1.hash (wInfo 1) ∧ d.batchHash 1 ≠ headL1.hash wInfoReverted ∧
      d.upgradeTxHash = 88 ∧ d.upgradeBatch = 0

end Contracts.BatchCounters
