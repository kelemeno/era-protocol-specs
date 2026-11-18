import EraSpec.Contracts.MessageRoot.Specs.Countermodels

/-!
# Properties: which source checks carry the guarantees, and a run that exercises them

Statements about `Specs/Countermodels.lean`.  Proofs are in `Proofs/Countermodels.lean`.

* Four checks are load-bearing: without `ChainExists` (`MRB:146-148`) a chain gets two slots,
  breaking `ChainIndexBijection`; without the consecutive-number check (`MRB:193`) a batch
  root lands beyond the counter, breaking `BatchRootsBeyondCurrentAreZero` (and with it
  `AppendLiveness` for that batch number); without the `<=` check of
  `setMigratingChainBatchNumber` (`MRB:155`) the counter drops below a recorded batch and the
  chain tree stops being in batch order; without `MessageRootNotRegistered` in the v31
  record-only flow (`MRB:184-186`) an unregistered chain gets a batch root.
* One check is redundant: on reachable storage `ChainBatchRootAlreadyExists` (`MRB:188-191`)
  never decides the outcome.  This is informational, not a defect.  (It is what stops a
  re-append in the variant without `MRB:155`, so it is defence in depth for that check.)
  Likewise `MessageRootNotRegistered` in the v32 flow: the push into a never-set-up tree
  reverts by itself.
* Two source comments are false, each refuted by a reachable instance (documentation only):
  `MRB:278` calls the Bridgehub "the only registrar", but the chain asset handler registers
  chains too (`MRB:114-119`, `MRB:145`); `MRB:66-68` says a chain tree is "pushed to on every
  `addChainBatchRoot`", but the v31 `addChainBatchRoot` only records (`MRB:164-170`; the
  interface comment, `IMessageRoot.sol:74-75`, is the accurate one).
* The witness run reaches storage where every premise of `Properties/Model.lean` that a reader
  might suspect of being vacuous holds at once.
-/

namespace Contracts.MessageRoot

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

/-- **`MessageRootNotRegistered` IS LOAD-BEARING IN THE V31 FLOW, REDUNDANT IN THE V32 FLOW.**
(1) There is reachable storage and an unregistered chain `c` for which the model's
`addChainBatchRoot(c, n, r)` from `getZKChain(c)` reverts, but the variant without the
registration check of `_recordChainBatchRoot` (`MRB:184-186`) succeeds: `c` is still
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

/-- **THE ALREADY-EXISTS CHECK IS REDUNDANT ON REACHABLE STORAGE.**  `_recordChainBatchRoot`
with and without `require(chainBatchRoots[c][n] == bytes32(0))` (`MRB:188-191`) are the same
function on every reachable storage: the consecutive check alone rejects every `n` with a
recorded root. -/
def Properties.ExistsCheckRedundant : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State) (c n : ℕ) (r : Bytes32), Reachable H cfg s →
    recordChainBatchRoot cfg c n r s = recordNoExistsCheck cfg c n r s

/-- **A RUN THROUGH EVERY ENTRY POINT.**  `witnessCalls` (initialize; add chain 5; seed its
genesis; v32 append of batch 1; v31 record of batch 2; migration counter to 5; v32 append of
batch 6; enable interop) succeeds from fresh storage.  At the end: two chains, chain 5 at
index 1; its counter is 6; its tree holds exactly batches 0, 1, 6 (a gap, and the v31 batch 2
recorded but not in the tree); interop is enabled; the final proof node accepts batch 6's and
batch 2's recorded roots and rejects batch 3 (never recorded) and batch 0; and the latest
historical root is the aggregated root. -/
def Properties.WitnessRun : Prop :=
  ∃ s : State, runFrom wH wCfg fresh witnessCalls = some s ∧ Reachable wH wCfg s
    ∧ s.chainCount = 2 ∧ s.chainIndex 5 = 1 ∧ s.currentChainBatchNumber 5 = 6
    ∧ s.chainLeaves 5 = [0, 1, 6].map (batchLeafOf wH s 5)
    ∧ s.chainBatchRoots 5 2 = 102 ∧ s.interopEnabled 5 = true
    ∧ finalNodeAccepts wCfg (wEnv 0 7) s 5 6 106 = some true
    ∧ finalNodeAccepts wCfg (wEnv 0 7) s 5 2 102 = some true
    ∧ finalNodeAccepts wCfg (wEnv 0 7) s 5 3 0 = some false
    ∧ finalNodeAccepts wCfg (wEnv 0 7) s 5 0 77 = none
    ∧ getAggregatedRoot wCfg s = some (s.historicalRoots s.lastEmitBlock).1

/-- **SOURCE COMMENT REFUTED: "The bridgehub (the only registrar)" (`MRB:278`).**  On reachable
storage, with the chain asset handler a different address from the Bridgehub, a call from the
chain asset handler registers a new chain. -/
def Properties.BridgehubNotOnlyRegistrar : Prop :=
  ∃ (H : Hashes) (cfg : Config) (s t : State) (env : Env) (c start : ℕ), Reachable H cfg s
    ∧ cfg.chainAssetHandler ≠ cfg.bridgehub ∧ env.sender = cfg.chainAssetHandler
    ∧ chainRegistered cfg s c = false
    ∧ exec H cfg env s (.addNewChain c start) = some t ∧ chainRegistered cfg t c = true

/-- **SOURCE COMMENT REFUTED: chain trees are "pushed to on every `addChainBatchRoot`"
(`MRB:66-68`).**  On reachable storage, a successful `addChainBatchRoot` records a nonzero batch
root and leaves the chain's tree unchanged.  The same instance contradicts `MRB:87`
(`chainBatchRoots` "are the same values as the leaves of the chainTree"): a recorded root with
no leaf. -/
def Properties.RecordOnlyDoesNotPush : Prop :=
  ∃ (H : Hashes) (cfg : Config) (s t : State) (env : Env) (c n : ℕ) (r : Bytes32),
    Reachable H cfg s ∧ exec H cfg env s (.addChainBatchRoot c n r) = some t
    ∧ r ≠ 0 ∧ t.chainBatchRoots c n = r ∧ t.chainLeaves c = s.chainLeaves c

end Contracts.MessageRoot
