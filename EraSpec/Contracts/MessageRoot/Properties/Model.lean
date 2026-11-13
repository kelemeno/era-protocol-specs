import EraSpec.Contracts.MessageRoot.Specs.Model
import EraSpec.Contracts.FullMerkle.Specs.CapacityInvariant
import EraSpec.Contracts.Merkle.Specs.RootForgeryPinned

/-!
# Properties: what the message root guarantees on every run

Statements about `Specs/Model.lean`.  Proofs are in `Proofs/Model.lean`.

`Reachable H cfg s`: `s` is reached from fresh proxy storage by a successful `initialize`
followed by any successful calls to any entry point (`addNewChain`,
`setMigratingChainBatchNumber`, `addChainBatchRoot`, `addChainBatchRootV32`, `seedGenesisRoot`,
`enableInterop`, `initialize` again), from any callers, in any order, each call with its own
environment (so the Bridgehub's `getZKChain` may change between calls).  `Run H cfg s tr t`:
the calls of `tr` take `s` to `t`.  No hash premise is used anywhere: every statement holds for
all hash functions `H`.

A proxy upgraded from an earlier release does not start from `initialize` (`L1MR:62`: "used in
local deployments").  `InvKeptByEveryCall` is the statement for it: storage that satisfies
`Inv` keeps satisfying it.  That an upgraded proxy's storage satisfies `Inv` at the upgrade is
not proved here (`MODEL-MR-GENESIS` in `ASSUMPTIONS.md`).

Groups:
* **Registration**: chains have unique indices, are added once, keep their index forever.
* **The aggregated root**: it is the `FullMerkle` root over one leaf per registered chain, each
  a function of that chain's tree; the last recorded historical root is the current one.
* **Batch roots**: written once, consecutively, never beyond the chain's counter, final once
  the counter has passed them; each chain tree is set up once, is an increasing log of
  recorded batches and only grows; the genesis seed happens at most once.
* **Who writes**: only the chain's own diamond (via `getZKChain`) and the Bridgehub write a
  chain's batch roots and tree; the counter additionally only by the chain asset handler.
* **Liveness**: a registration by the Bridgehub or the chain asset handler, and a correctly
  ordered append by the registered chain, do not revert in the shared-tree update.
* **Migration**: batch numbers skipped by `setMigratingChainBatchNumber` never get a root here.
* **Proofs**: the final proof node's verdict, exactly; from `v31UpgradeChainBatchNumber` on it
  only accepts a recorded batch root.
* **Bookkeeping**: `interopRootLogId` advances at most once per block; interop enablement is
  owner-only and permanent; `initialize` cannot run twice.
-/

namespace Contracts.MessageRoot

open AttackVectors.CapacityInvariant (TreeDims)

/-! ## The invariant -/

/-- **EVERY REACHABLE STORAGE SATISFIES `Inv`.**  `Inv` (`Specs/Model.lean`) collects the
index bijection, the shared tree representing `sharedLeaves`, the batch-root bookkeeping, the
chain-tree log and the historical-root equation.  The properties below restate its parts. -/
def Properties.ReachableInv : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State), Reachable H cfg s → Inv H cfg s

/-- **EVERY CALL KEEPS `Inv`, FROM ANY STORAGE.**  If storage satisfies `Inv` (reachable from
`initialize` or not, e.g. a proxy upgraded from an earlier release whose storage satisfies it),
every successful call leaves storage that satisfies `Inv`. -/
def Properties.InvKeptByEveryCall : Prop :=
  ∀ (H : Hashes) (cfg : Config) (env : Env) (s t : State) (call : Call),
    Inv H cfg s → exec H cfg env s call = some t → Inv H cfg t

/-! ## Registration -/

/-- **UNIQUE INDICES.**  On every reachable storage: this chain sits at index 0
(`MRB:56`); there is at least one chain; `chainIndexToId` is injective on
`[0, chainCount)`; a chain is registered exactly when it occupies a slot below `chainCount`;
and a registered chain's `chainIndex` is that slot. -/
def Properties.ChainIndexBijection : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State), Reachable H cfg s →
    s.chainIndexToId 0 = cfg.selfChainId ∧ s.chainIndex cfg.selfChainId = 0 ∧ 1 ≤ s.chainCount
      ∧ (∀ i j, i < s.chainCount → j < s.chainCount →
          s.chainIndexToId i = s.chainIndexToId j → i = j)
      ∧ (∀ c, chainRegistered cfg s c = true ↔ ∃ i, i < s.chainCount ∧ s.chainIndexToId i = c)
      ∧ (∀ c, chainRegistered cfg s c = true →
          s.chainIndex c < s.chainCount ∧ s.chainIndexToId (s.chainIndex c) = c)

/-- **A CHAIN IS ADDED ONCE, AT THE NEXT INDEX.**  On reachable storage, `addNewChain` for a
registered chain reverts, whoever calls.  A successful `addNewChain(c, start)` was called by
the Bridgehub or the chain asset handler for an unregistered `c`; it gives `c` the index
`chainCount`, increments `chainCount`, sets `c`'s counter to `start` with an empty tree, and
appends exactly `chainIdLeafHash(0, c)` to the shared tree's leaves. -/
def Properties.ChainAddedOnce : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State) (env : Env) (c start : ℕ), Reachable H cfg s →
    (chainRegistered cfg s c = true → exec H cfg env s (.addNewChain c start) = none)
      ∧ ∀ t, exec H cfg env s (.addNewChain c start) = some t →
        (env.sender = cfg.bridgehub ∨ env.sender = cfg.chainAssetHandler)
          ∧ chainRegistered cfg s c = false ∧ chainRegistered cfg t c = true
          ∧ t.chainIndex c = s.chainCount ∧ t.chainCount = s.chainCount + 1
          ∧ t.currentChainBatchNumber c = start ∧ t.chainLeaves c = []
          ∧ sharedLeaves H t = sharedLeaves H s ++ [H.chainIdLeaf 0 c]

/-- **A CORRECT REGISTRATION DOES NOT REVERT.**  On reachable storage, `addNewChain(c, start)`
from the Bridgehub or the chain asset handler for an unregistered `c`, with no `uint256`
overflow of `chainCount` or `interopRootLogId`, succeeds: the shared tree's `pushNewLeaf`
(growth, padding and the path update, as transcribed) does not revert.  The shared tree's own
limit of `2^255` leaves is outside the `FullMerkle` transcription (`MODEL-FULLMERKLE`). -/
def Properties.AddNewChainLiveness : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State) (env : Env) (c start : ℕ), Reachable H cfg s →
    (env.sender = cfg.bridgehub ∨ env.sender = cfg.chainAssetHandler) →
    chainRegistered cfg s c = false → s.chainCount + 1 < UInt256.size →
    s.interopRootLogId + 1 < UInt256.size →
    ∃ t, exec H cfg env s (.addNewChain c start) = some t

/-- **REGISTRATION IS PERMANENT.**  Along any run from reachable storage, a registered chain
stays registered with the same index, `chainCount` never decreases, and slots below the old
count keep their chain. -/
def Properties.RegistrationStable : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t : State) (tr : List (Env × Call)),
    Reachable H cfg s → Run H cfg s tr t →
      s.chainCount ≤ t.chainCount
      ∧ (∀ i, i < s.chainCount → t.chainIndexToId i = s.chainIndexToId i)
      ∧ ∀ c, chainRegistered cfg s c = true →
        chainRegistered cfg t c = true ∧ t.chainIndex c = s.chainIndex c

/-! ## The aggregated root -/

/-- **THE AGGREGATED ROOT IS A FUNCTION OF THE CHAIN TREES.**  On every reachable storage,
`getAggregatedRoot()` does not revert and returns the `FullMerkle` fold over `sharedLeaves`
(slot `i` holds `chainIdLeafHash(root of chain chainIndexToId[i]'s tree, chainIndexToId[i])`)
at the height that `chainCount` pushes from an empty tree produce. -/
def Properties.AggregatedRootFormula : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State), Reachable H cfg s →
    getAggregatedRoot cfg s = some (MerkleSpec.rootOf H.node cfg.emptyHash (sharedLeaves H s)
      (AttackVectors.CapacityInvariant.push^[s.chainCount] (⟨0, 0⟩ : TreeDims)).height)

/-- **SAME CHAINS, SAME TREES, SAME ROOT.**  Two reachable storages (same deployment, same
hashes) with the same chains in the same slots and the same per-chain tree leaves have the
same aggregated root, whatever else differs (counters, record-only batch roots, timestamps,
interop flags, history, how the trees were reached). -/
def Properties.AggregatedRootDeterminedByChainTrees : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s s' : State), Reachable H cfg s → Reachable H cfg s' →
    s.chainCount = s'.chainCount →
    (∀ i, i < s.chainCount → s.chainIndexToId i = s'.chainIndexToId i) →
    (∀ c, chainRegistered cfg s c = true → s.chainLeaves c = s'.chainLeaves c) →
    getAggregatedRoot cfg s = getAggregatedRoot cfg s'

/-- **EQUAL AGGREGATED ROOTS PIN EACH CHAIN'S TREE ROOT, OR A LOCATED COLLISION.**  Take two
reachable storages with the same `chainCount` and a chain `c` registered in the first whose
slot holds `c` in the second too.  If their aggregated roots are equal, then `c`'s chain-tree
roots are equal, or `chainIdLeafHash` maps the two different roots (with the same chain id) to
one value, or the two shared trees hash different pairs to one value on the path of `c`'s
slot (`MerkleSpec.Pinned.TreeCollision`).  Every collision named is at specific inputs taken
from the two storages; no hash is assumed injective. -/
def Properties.AggregatedRootPinsChainRootOrCollision : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s s' : State) (c : ℕ), Reachable H cfg s → Reachable H cfg s' →
    s.chainCount = s'.chainCount → chainRegistered cfg s c = true →
    s'.chainIndexToId (s.chainIndex c) = c →
    getAggregatedRoot cfg s = getAggregatedRoot cfg s' →
      chainRootOf H (s.chainLeaves c) = chainRootOf H (s'.chainLeaves c)
      ∨ (chainRootOf H (s.chainLeaves c) ≠ chainRootOf H (s'.chainLeaves c)
          ∧ H.chainIdLeaf (chainRootOf H (s.chainLeaves c)) c
            = H.chainIdLeaf (chainRootOf H (s'.chainLeaves c)) c)
      ∨ MerkleSpec.Pinned.TreeCollision H.node cfg.emptyHash (sharedLeaves H s) (sharedLeaves H s')
          (AttackVectors.CapacityInvariant.push^[s.chainCount] (⟨0, 0⟩ : TreeDims)).height
          (s.chainIndex c)

/-- **THE LATEST HISTORICAL ROOT IS THE CURRENT ROOT.**  On every reachable storage, the root
recorded in `historicalRoots[lastEmitBlock]` is `getAggregatedRoot()`: every shared-tree
change is followed, in the same call, by `_emitRoot` and `_recordHistoricalRoot` at the same
block. -/
def Properties.HistoricalRootIsAggregated : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State), Reachable H cfg s →
    getAggregatedRoot cfg s = some (s.historicalRoots s.lastEmitBlock).1

/-! ## Batch roots and chain trees -/

/-- **NO BATCH ROOT BEYOND THE COUNTER (`MRB:89`, "an expected invariant").**  On every
reachable storage, `chainBatchRoots[c][n] = 0` for every `n > currentChainBatchNumber[c]`;
an unregistered chain has no batch roots and an empty tree. -/
def Properties.BatchRootsBeyondCurrentAreZero : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State), Reachable H cfg s →
    (∀ c n, s.currentChainBatchNumber c < n → s.chainBatchRoots c n = 0)
      ∧ ∀ c, chainRegistered cfg s c = false →
        s.chainLeaves c = [] ∧ ∀ n, s.chainBatchRoots c n = 0

/-- **EACH CHAIN TREE IS AN INCREASING LOG OF RECORDED BATCHES.**  On every reachable storage
and for every chain, there are strictly increasing batch numbers `ns`, each at most the
chain's counter and each with a nonzero recorded root, such that the chain tree's leaves are
`batchLeafHash(chainBatchRoots[c][n], n, chainBatchRootTimestamp[c][n])` for `n ∈ ns`, in
order.  Batches recorded by the v31 flow are in `chainBatchRoots` but not in the tree; that
is why `ns` may skip numbers. -/
def Properties.ChainTreeIsOrderedLog : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State), Reachable H cfg s → ∀ c, ∃ ns : List ℕ,
    ns.Pairwise (· < ·)
      ∧ (∀ n ∈ ns, n ≤ s.currentChainBatchNumber c ∧ s.chainBatchRoots c n ≠ 0)
      ∧ s.chainLeaves c = ns.map fun n =>
          H.batchLeaf (s.chainBatchRoots c n) n (s.chainBatchRootTimestamp c n)

/-- **EACH CHAIN TREE IS SET UP EXACTLY ONCE.**  On every reachable storage,
`DynamicIncrementalMerkle.setup` has run once on the tree of every registered chain and never
on the tree of any other chain.  The library's `setup` has no guard and a second call corrupts
the tree (`DIM:53-58`); a `push` into a never-set-up tree reverts (`DIM:95`).  Neither
happens. -/
def Properties.ChainTreeSetUpOnce : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State), Reachable H cfg s → ∀ c,
    s.chainTreeSetups c = if chainRegistered cfg s c then 1 else 0

/-- **BATCH ROOTS ARE WRITTEN ONCE.**  Along any run from reachable storage, a nonzero
`chainBatchRoots[c][n]` and its `chainBatchRootTimestamp[c][n]` never change. -/
def Properties.BatchRootsWriteOnce : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t : State) (tr : List (Env × Call)) (c n : ℕ),
    Reachable H cfg s → Run H cfg s tr t → s.chainBatchRoots c n ≠ 0 →
      t.chainBatchRoots c n = s.chainBatchRoots c n
        ∧ t.chainBatchRootTimestamp c n = s.chainBatchRootTimestamp c n

/-- **A BATCH ROOT IS FINAL ONCE THE COUNTER HAS PASSED IT.**  Take a registered chain `c` on
reachable storage and a batch number `n ≤ currentChainBatchNumber[c]`, with the counter
positive or the genesis root (batch `0`) recorded.  Along any run, `chainBatchRoots[c][n]`
never changes, whether it is zero or not.  So a batch number skipped by
`setMigratingChainBatchNumber` (settled on another layer) never gets a root here.  And for
`n` at or above `v31UpgradeChainBatchNumber[c]` the final proof node's verdict on `(c, n)` is
the same before and after the run, for every candidate root and whatever the chain's getters
answer. -/
def Properties.SettledBatchRootsFrozen : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t : State) (tr : List (Env × Call)) (c n : ℕ),
    Reachable H cfg s → Run H cfg s tr t → chainRegistered cfg s c = true →
    n ≤ s.currentChainBatchNumber c →
    (0 < s.currentChainBatchNumber c ∨ s.chainBatchRoots c 0 ≠ 0) →
      t.chainBatchRoots c n = s.chainBatchRoots c n
        ∧ (cfg.v31Upgrade c ≤ n → ∀ (env env' : Env) (proven : Bytes32),
            finalNodeAccepts cfg env t c n proven = finalNodeAccepts cfg env' s c n proven)

/-- **CHAIN TREES ONLY GROW.**  Along any run from reachable storage, every chain tree's old
leaves are a prefix of its new leaves. -/
def Properties.ChainTreeAppendOnly : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t : State) (tr : List (Env × Call)) (c : ℕ),
    Reachable H cfg s → Run H cfg s tr t → s.chainLeaves c <+: t.chainLeaves c

/-- **A REGISTERED CHAIN'S COUNTER NEVER DECREASES.**  Along any run from reachable storage. -/
def Properties.CurrentBatchMonotone : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t : State) (tr : List (Env × Call)) (c : ℕ),
    Reachable H cfg s → Run H cfg s tr t → chainRegistered cfg s c = true →
      s.currentChainBatchNumber c ≤ t.currentChainBatchNumber c

/-- **BATCHES SKIPPED BY A MIGRATION ARE NEVER RECORDED HERE.**  Take a registered chain `c`
on reachable storage and a successful `setMigratingChainBatchNumber(c, m)`.  It was sent by the
chain asset handler with `currentChainBatchNumber[c] ≤ m` and sets the counter to `m`.  After
any further run the counter is still at least `m`, and every batch number `n` the call skipped
(old counter `< n ≤ m`: the batches settled on another layer) has `chainBatchRoots[c][n] = 0`.
For such `n` at or above `v31UpgradeChainBatchNumber[c]` the final proof node never accepts
`(c, n)`, for any candidate root and whatever the chain's getters answer: these batches can
only be proven through the settlement layer they settled on
(`_proveL2LeafInclusionOnSettlementLayer`, not modelled).  The registration premise is needed:
`MigrationBeforeRegistrationIsOverwritten` in `Properties/Countermodels.lean`. -/
def Properties.MigrationSkippedBatchesNeverRecorded : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t u : State) (env : Env) (tr : List (Env × Call)) (c m : ℕ),
    Reachable H cfg s → chainRegistered cfg s c = true →
    exec H cfg env s (.setMigratingChainBatchNumber c m) = some t → Run H cfg t tr u →
      env.sender = cfg.chainAssetHandler ∧ s.currentChainBatchNumber c ≤ m
        ∧ t.currentChainBatchNumber c = m ∧ m ≤ u.currentChainBatchNumber c
        ∧ ∀ n, s.currentChainBatchNumber c < n → n ≤ m →
            u.chainBatchRoots c n = 0
              ∧ (cfg.v31Upgrade c ≤ n → ∀ (env' : Env) (proven : Bytes32),
                  finalNodeAccepts cfg env' u c n proven ≠ some true)

/-- **AN APPEND IS BY THE CHAIN, CONSECUTIVE, AND EXACT.**  On reachable storage, a successful
`addChainBatchRootV32(c, n, r)` was sent by `getZKChain(c)` for a registered `c`, with
`r ≠ 0` and `n = currentChainBatchNumber[c] + 1`.  It records `r` at `n`, advances the
counter to `n`, stamps `n` with `block.timestamp`, appends exactly
`batchLeafHash(r, n, block.timestamp)` to `c`'s tree, and changes no other chain's roots,
counter or tree.  A successful `addChainBatchRoot(c, n, r)` (v31 flow) has the same guards and
record, and leaves every tree, the shared tree and the history unchanged. -/
def Properties.AppendExact : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State) (env : Env) (c n : ℕ) (r : Bytes32),
    Reachable H cfg s →
    (∀ t, exec H cfg env s (.addChainBatchRootV32 c n r) = some t →
      env.sender = env.zkChain c ∧ chainRegistered cfg s c = true ∧ r ≠ 0
        ∧ n = s.currentChainBatchNumber c + 1
        ∧ t.chainBatchRoots c n = r ∧ t.currentChainBatchNumber c = n
        ∧ t.chainBatchRootTimestamp c n = env.timestamp
        ∧ t.chainLeaves c = s.chainLeaves c ++ [H.batchLeaf r n env.timestamp]
        ∧ ∀ c', c' ≠ c → t.chainLeaves c' = s.chainLeaves c'
          ∧ t.chainBatchRoots c' = s.chainBatchRoots c'
          ∧ t.currentChainBatchNumber c' = s.currentChainBatchNumber c')
    ∧ (∀ t, exec H cfg env s (.addChainBatchRoot c n r) = some t →
      env.sender = env.zkChain c ∧ chainRegistered cfg s c = true ∧ r ≠ 0
        ∧ n = s.currentChainBatchNumber c + 1
        ∧ t.chainBatchRoots c n = r ∧ t.currentChainBatchNumber c = n
        ∧ t.chainLeaves = s.chainLeaves ∧ t.sharedTree = s.sharedTree
        ∧ t.historicalRoots = s.historicalRoots)

/-- **A CORRECT APPEND DOES NOT REVERT.**  On reachable storage, `addChainBatchRootV32(c, n, r)`
from `getZKChain(c)` for a registered `c` with `r ≠ 0`, `n = currentChainBatchNumber[c] + 1`
and no `uint256` overflow succeeds: the already-exists check passes and the shared tree's
`updateLeaf` finds the chain's slot. -/
def Properties.AppendLiveness : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State) (env : Env) (c n : ℕ) (r : Bytes32),
    Reachable H cfg s → env.sender = env.zkChain c → chainRegistered cfg s c = true → r ≠ 0 →
    n = s.currentChainBatchNumber c + 1 → s.currentChainBatchNumber c + 1 < UInt256.size →
    s.interopRootLogId + 1 < UInt256.size →
    ∃ t, exec H cfg env s (.addChainBatchRootV32 c n r) = some t

/-- **THE GENESIS LEAF IS ALWAYS FIRST.**  On reachable storage, a successful
`seedGenesisRoot(c)` was sent by the Bridgehub, found `c`'s tree empty and its counter at `0`,
records the chain's `l2LogsRootHash(0)` at batch `0`, leaves the counter at `0`, and makes it
the tree's only leaf. -/
def Properties.GenesisSeedIsFirstLeaf : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State) (env : Env) (c : ℕ), Reachable H cfg s →
    ∀ t, exec H cfg env s (.seedGenesisRoot c) = some t →
      env.sender = cfg.bridgehub ∧ s.chainLeaves c = [] ∧ s.currentChainBatchNumber c = 0
        ∧ t.currentChainBatchNumber c = 0 ∧ t.chainBatchRoots c 0 = env.l2LogsRootHash c 0
        ∧ t.chainLeaves c = [H.batchLeaf (env.l2LogsRootHash c 0) 0 env.timestamp]

/-- **THE GENESIS ROOT IS SEEDED AT MOST ONCE (`IMessageRoot.sol:88`, "One-time").**  On
reachable storage where chain `c`'s batch-`0` root is recorded, or `c` is registered with a
positive counter, `seedGenesisRoot(c)` reverts after any run, whoever calls and whatever the
chain's `l2LogsRootHash(0)` answers. -/
def Properties.GenesisSeedOnce : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t : State) (tr : List (Env × Call)) (env : Env) (c : ℕ),
    Reachable H cfg s → Run H cfg s tr t →
    (s.chainBatchRoots c 0 ≠ 0
      ∨ (chainRegistered cfg s c = true ∧ 0 < s.currentChainBatchNumber c)) →
      exec H cfg env t (.seedGenesisRoot c) = none

/-! ## Who writes -/

/-- **ONLY THE CHAIN AND THE BRIDGEHUB WRITE A CHAIN'S ROOTS AND TREE.**  Along any run from
reachable storage in which no call is sent by `getZKChain(c)` (as that call saw it) or by the
Bridgehub, chain `c`'s batch roots, timestamps and tree are unchanged.  If in addition no call
is from the chain asset handler, `c`'s counter is unchanged. -/
def Properties.ChainWritersOnly : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t : State) (tr : List (Env × Call)) (c : ℕ),
    Reachable H cfg s → Run H cfg s tr t →
    (∀ p ∈ tr, p.1.sender ≠ p.1.zkChain c ∧ p.1.sender ≠ cfg.bridgehub) →
      t.chainBatchRoots c = s.chainBatchRoots c
        ∧ t.chainBatchRootTimestamp c = s.chainBatchRootTimestamp c
        ∧ t.chainLeaves c = s.chainLeaves c
        ∧ ((∀ p ∈ tr, p.1.sender ≠ cfg.chainAssetHandler) →
            t.currentChainBatchNumber c = s.currentChainBatchNumber c)

/-- **EVERY WRITE TO A CHAIN'S ROOTS OR TREE IS AN APPEND BY THAT CHAIN, OR ITS GENESIS SEED.**
Along any run from reachable storage, if chain `c`'s batch roots or tree differ at the end,
then the run contains `addChainBatchRoot(c, ·, ·)` or `addChainBatchRootV32(c, ·, ·)` sent by
the address the Bridgehub returned for `getZKChain(c)` in that call, or `seedGenesisRoot(c)`
sent by the Bridgehub.  (`ChainWritersOnly` only says some call came from one of the two
senders; this names the call.) -/
def Properties.ChainWriteProvenance : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t : State) (tr : List (Env × Call)) (c : ℕ),
    Reachable H cfg s → Run H cfg s tr t →
    (t.chainBatchRoots c ≠ s.chainBatchRoots c ∨ t.chainLeaves c ≠ s.chainLeaves c) →
      ∃ e call, (e, call) ∈ tr
        ∧ ((e.sender = e.zkChain c
              ∧ ∃ n r, call = .addChainBatchRoot c n r ∨ call = .addChainBatchRootV32 c n r)
            ∨ (e.sender = cfg.bridgehub ∧ call = .seedGenesisRoot c))

/-! ## Proofs read recorded roots -/

/-- **THE FINAL PROOF NODE'S VERDICT, EXACTLY.**  On any storage, the final-node check of
`_proveL2LeafInclusionRecursive` (`MRB:343-348`, with L1's `_noBatchFallback`, `L1MR:123-128`)
accepts `proven` for `(c, n)` exactly when `n > 0`, `proven ≠ 0`, and either `proven` is the
recorded `chainBatchRoots[c][n]`, or no root is recorded, `n` is below
`v31UpgradeChainBatchNumber[c]`, and `proven` is what the chain's diamond answers for
`l2LogsRootHash(n)` in that call.  The second case is the trust the source documents at
`L1MR:42-44`: for an unrecorded pre-v31 batch the contract accepts whatever nonzero root the
chain's own diamond reports.  Where `v31UpgradeChainBatchNumber[c] = 0` (every chain added
under this release, `L1MR:37`) only recorded roots are accepted. -/
def Properties.FinalNodeAcceptsIff : Prop :=
  ∀ (cfg : Config) (env : Env) (s : State) (c n : ℕ) (proven : Bytes32),
    finalNodeAccepts cfg env s c n proven = some true ↔
      0 < n ∧ proven ≠ 0
        ∧ (s.chainBatchRoots c n = proven
          ∨ (s.chainBatchRoots c n = 0 ∧ n < cfg.v31Upgrade c
              ∧ env.l2LogsRootHash c n = proven))

/-- **THE FINAL PROOF NODE ONLY ACCEPTS A SETTLED, RECORDED BATCH.**  On reachable storage,
for a batch number at or above the chain's `v31UpgradeChainBatchNumber`, if the final-node
check of `_proveL2LeafInclusionRecursive` (`MRB:343-348`) accepts `proven` for `(c, n)`, then
`n > 0`, `n` is at most the chain's counter, and `proven` is the nonzero recorded
`chainBatchRoots[c][n]`.  Batch `0`, the seeded genesis root included, is never accepted
(`BatchZeroNotAllowed`). -/
def Properties.ProofRootIsRecordedRoot : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State) (env : Env) (c n : ℕ) (proven : Bytes32),
    Reachable H cfg s →
    finalNodeAccepts cfg env s c 0 proven = none
      ∧ (cfg.v31Upgrade c ≤ n → finalNodeAccepts cfg env s c n proven = some true →
          0 < n ∧ n ≤ s.currentChainBatchNumber c ∧ s.chainBatchRoots c n = proven ∧ proven ≠ 0)

/-! ## Bookkeeping -/

/-- **`interopRootLogId` ADVANCES AT MOST ONCE PER BLOCK (`MRB:92`).**  Along any run (from any
storage) whose calls all run in block `b`, `interopRootLogId` grows by at most one, and not at
all if the last emission was already in block `b`. -/
def Properties.LogIdOncePerBlock : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t : State) (tr : List (Env × Call)) (b : ℕ),
    Run H cfg s tr t → (∀ p ∈ tr, p.1.blockNumber = b) →
      s.interopRootLogId ≤ t.interopRootLogId ∧ t.interopRootLogId ≤ s.interopRootLogId + 1
        ∧ (s.lastEmitBlock = b → t.interopRootLogId = s.interopRootLogId)

/-- **INTEROP IS ENABLED ONCE, BY THE OWNER, AND STAYS ENABLED.**  Along any run (from any
storage), an enabled chain stays enabled; a chain that becomes enabled was the subject of an
`enableInterop` call from the Bridgehub's owner, for a chain the Bridgehub knew, with no
balance backfill pending; and `enableInterop` on an enabled chain reverts. -/
def Properties.InteropEnabledOnce : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s t : State) (tr : List (Env × Call)) (c : ℕ),
    Run H cfg s tr t →
      (s.interopEnabled c = true → t.interopEnabled c = true)
      ∧ (s.interopEnabled c = false → t.interopEnabled c = true →
          ∃ e req, (e, Call.enableInterop c req) ∈ tr ∧ e.sender = e.bridgehubOwner
            ∧ e.zkChain c ≠ 0 ∧ e.backfillPending c = false)
      ∧ ∀ env req, s.interopEnabled c = true →
          exec H cfg env s (.enableInterop c req) = none

/-- **NO SECOND `initialize`.**  On reachable storage `initialize` reverts. -/
def Properties.NoReinitialization : Prop :=
  ∀ (H : Hashes) (cfg : Config) (s : State) (env : Env), Reachable H cfg s →
    exec H cfg env s .initialize = none

end Contracts.MessageRoot
