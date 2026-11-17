import EraSpec.Contracts.L2InteropCommitmentTree.Specs.InitOnce
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.CachedRoot

/-!
# Model at `draft/v0.35.0`: the commitment tree's walk, entry points and padding

**Commit.** era-contracts `draft/v0.35.0` at `d9f678900e1bc8286412b78f56d4a9f443983c29`
("build(l1-contracts): drop CBOR metadata from the default build (v35) (#2653)").  Paths are
relative to `l1-contracts/contracts/` at that commit unless they start with another top-level
directory.  The pin models of this folder (`c67894b9`) are not changed: this file adds the v35
machine beside them, and the properties relate the two.

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.L2InteropCommitmentTree.Properties.CommitmentTreeAtV35`, proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CommitmentTreeAtV35`.

## Source identity (git blob ids, first ten hex digits)

| file | pin `c67894b9` | `main` `3605e82` | v35 `d9f6789` |
|---|---|---|---|
| `common/libraries/IndexedMerkleTree.sol` | `572566ad9b` | `90c8418ff0` | `90c8418ff0` |
| `common/libraries/FullMerkle.sol` | `325ac0baea` | `325ac0baea` | `325ac0baea` |
| `common/libraries/Merkle.sol` | `1c1b8a0944` | `1c1b8a0944` | `1c1b8a0944` |
| `l2-upgrades/SystemContractProxy.sol` | `c7845b7382` | `c7845b7382` | `c7845b7382` |
| `l2-system/zksync-os/L1MessageGasLib.sol` | `5aa0a41ec8` | `7694d3ba38` | `7694d3ba38` |
| `atomic-interop/L2InteropCommitmentTree.sol` | `c63711593d` | `d2e582a2d6` | `8b892427a9` |

The v35 tree contract differs from `main`'s only in two import lines (`Unauthorized` now comes
from `common/L1ContractErrors.sol:498`, `NotSelfCall` / `NotEnoughGasSupplied` from
`l2-system/zksync-os/errors/SystemContractErrors.sol`; the selectors are unchanged), so its line
numbers sit one below `main`'s.  So everything modelled here is also `main`'s code.  The `main`
models being written concurrently (`…AtHead`) describe the same functions.  This file restates
only what this folder's headlines need, under `V35` names, so that it does not depend on them.

## What changed since the pin

1. **The low-leaf walk is unbounded** (`b8cc61203`, #2349).  `IndexedMerkleTree.insert`
   (`IndexedMerkleTree.sol:65-107`) keeps the pin's checks (`:70-88`) and writes (`:95-106`), but
   its loop is now

       while (lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value) {          // :90-93
           lowLeafIndex = lowLeaf.nextIndex;
           lowLeaf = self.leaves[lowLeafIndex];
       }

   and `MAX_LOW_INDEX_SEARCH_ATTEMPTS` is removed from `common/Config.sol` (pin `:66`).  The exit
   test and the hop are the pin's.  `WalkExitsAtV35` reads the loop as "some number of hops of
   `lowSearch` exits at `low`": a successful transaction ran the loop finitely often, and a loop
   that never exits runs out of gas, which reverts, which is no step.

2. **The padding is domain-separated** (`78e14b3bc`, audit item F-04).  `IndexedMerkleTree.setup`
   (`IndexedMerkleTree.sol:46-54`):

       if (self.tree._leafNumber != 0) { revert IMTAlreadyInitialized(); }               // :47-49
       self.tree.setup(IMT_EMPTY_LEAF_HASH);                                               // :51
       self.tree.pushNewLeaf(hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0})));  // :52
       self.leaves[0] = IMTLeaf({value: 0, nextIndex: 0, nextValue: 0});                  // :53

   with `IMT_EMPTY_LEAF_HASH = keccak256("zkSync:IndexedMerkleTree:emptyLeaf")`
   (`common/Config.sol:138-141`).  The pin passed one value, `hashLeaf({0,0,0})`, to both calls
   (pin `IndexedMerkleTree.sol:47-49`).  `cSetupAtV35 h hl zE` passes `zE` to `FullMerkle.setup`
   and `hl ⟨0,0,0⟩` to `pushNewLeaf`.  The list state (`Tree`) does not see the change:
   `setupWrites` and `setupLevel` still describe `:51-53` (`setupLevel` records index 0's stored
   hash, `hashLeaf({0,0,0})`, which `:52` still writes).

3. **`L2InteropCommitmentTree.insert` reports the leaf** (`L2InteropCommitmentTree.sol:51-64`).
   After the engine's insert (`:57`) it calls `_reportLeaf(_value)` (`:62`, body `:71-76`).  That
   burns the log gas (`_burnLogGas`, `:80-91`) and calls `INTEROP_COMMITMENT_LEAF_HOOK`
   (`common/l2-helpers/L2ContractAddresses.sol:27`, `0x7004`) under
   `require(ok, InteropCommitmentLeafHookFailed())` (`:75`).  A new `fallback` (`:121-126`)
   requires `msg.sender == address(this)` and executes `invalid()`.  Every new path can only
   revert, and none writes `_imt`.  `TxStepAtV35` records successful transactions, so it does not
   see them.  The refinement is the topic `InsertRevertOnlyAtV35`.

## What did not change

* `onlyUpgrader` (`L2InteropCommitmentTree.sol:35-40`; `L2_COMPLEX_UPGRADER_ADDR =
  SYSTEM_CONTRACTS_OFFSET + 0x0f = 0x800f`, `L2ContractAddresses.sol:6, 65`), `initL2`
  (`:45-48`), the appender check (`:52-54`) and `appender()` (`:114-116`;
  `L2_ATOMIC_FLOW_MANAGER_ADDR = BUILT_IN_CONTRACTS_OFFSET + 0x14 = 0x10014`,
  `L2ContractAddresses.sol:12, 142`).  So `Roles`, `deployedRoles`, `Call` and the `initL2` case
  of `InitOnce.TxStep` describe v35.  The one appender call site is `AtomicFlowManager.append`
  (`atomic-interop/AtomicFlowManager.sol:104`, tree call `:170`).
* `root`, `merklePath`, `hashLeaf` (`IndexedMerkleTree.sol:110-112, 116-118, 124-126`) and the two
  verifiers (`verifyInclusion` `:134-146`, `verifyNonInclusion` `:154-172`).  So `TreeRoot`'s
  `PathAccepts`, `InclusionAccepted` and `NonInclusionAccepted` describe v35.  In particular
  `Merkle.calculateRootMemory` (`common/libraries/Merkle.sol:53-70`) still bounds the index only
  by `2 ^ pathLength` (`_validatePathLengthForSingleProof`, `:133-140`), not by the leaf count.
* `FullMerkle` is byte-identical, so `FullMerkle/Specs/CachedNodes.lean` and `CachedRoot.cInsert`
  describe v35.  The padding enters `cInsert` only through the stored `_zeros`, which
  `FullMerkle.setup` (`FullMerkle.sol:29-35`) seeds with whatever constant it is passed.

## Model boundary

As in `InitOnce` and `CachedRoot`.  In addition:
* `InsertChecksAtV35.lowInBounds` is `FullMerkle.updateLeaf`'s own range check
  (`FullMerkle.sol:74-77`, reached from `IndexedMerkleTree.sol:101`), so a successful insert has
  it.  The pin's `InsertChecks` omits it.  That is a faithfulness minor recorded against the pin
  (from a non-valid start it lets the model take an insert step the source reverts).  On valid
  trees the field follows from the others.
* `zE` is a parameter standing for `IMT_EMPTY_LEAF_HASH`, and nothing is assumed about it.  A
  statement that needs `zE` to differ from a leaf hash concludes the located equation
  `hl ℓ = zE` instead of assuming it away.  At v35 that equation is a keccak collision between
  the 96-byte `abi.encode(ℓ.value, ℓ.nextIndex, ℓ.nextValue)` (`IndexedMerkleTree.sol:125`) and
  the 34-byte string of `Config.sol:141`.  The byte-level reading is `main`'s topic, because the
  two files are byte-identical there.
* The genesis seeding call site changed at v35 and is the topic `GenesisSeedingAtV35`.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## The walk -/

/-- **THE v35 LOOP EXITS AT `low`** (`IndexedMerkleTree.sol:90-93`): some number of hops of the
walk from `hint` ends on `low`.  `lowSearch T v hops hint` (`Specs/Model.lean`) runs the same exit
test and hop with at most `hops` hops, and returns `none` only if it needs more. -/
def WalkExitsAtV35 (T : Tree) (v : UInt256) (hint low : ℕ) : Prop :=
  ∃ hops : ℕ, lowSearch T v hops hint = some low

/-- What a successful v35 `insert(v, hint)` has checked before it writes, at the index `low` the
walk exits on (`IndexedMerkleTree.sol:65-107`).  The first five fields are the pin's
`InitOnce.InsertChecks` fields at their v35 lines.  `walk` replaces the pin's five-hop search, and
`lowInBounds` is the `FullMerkle` check the pin's model omits. -/
structure InsertChecksAtV35 (T : Tree) (v : UInt256) (hint low : ℕ) : Prop where
  /-- `leafNumber == 0` reverts with `IMTNotInitialized` (`:70-73`). -/
  initialized : Initialized T
  /-- `_value == 0` reverts with `IMTValueZero` (`:74-76`). -/
  nonzero : v ≠ 0
  /-- `valueToIndex[_value] != 0` reverts with `IMTValueAlreadyExists` (`:77-79`). -/
  unregistered : T.valueToIndex v = 0
  /-- `_lowLeafIndex >= leafNumber` reverts with `IMTLowLeafIndexOutOfBounds` (`:80-82`). -/
  hintInBounds : hint < T.leafCount
  /-- `leaves[_lowLeafIndex].value >= _value` reverts with `IMTLowLeafValueTooLarge` (`:84-88`). -/
  hintBelow : (T.leaf hint).value < v
  /-- The unbounded walk (`:90-93`) exits at `low`. -/
  walk : WalkExitsAtV35 T v hint low
  /-- `tree.updateLeaf(lowLeafIndex, …)` (`:101`) reverts with `MerkleWrongIndex` unless
  `lowLeafIndex ≤ _leafNumber - 1` (`FullMerkle.sol:74-77`). -/
  lowInBounds : low < T.leafCount

/-! ## Transactions -/

/-- One successful transaction of the v35 tree contract, sent by `c`.

* `initL2()` (`L2InteropCommitmentTree.sol:45-48`): `onlyUpgrader` (`:35-40`), then
  `IMT.setup`, which reverts with `IMTAlreadyInitialized` unless `_leafNumber == 0`
  (`IndexedMerkleTree.sol:47-49`).  Its list-state writes are `setupWrites` (`:52-53`).
* `insert(v, hint)` (`:51-64`): the appender check (`:52-54`), the engine's checks and walk
  (`InsertChecksAtV35`), and the three writes of `insert` at the exit index
  (`IndexedMerkleTree.sol:95-106`).  The leaf report (`:62`) only adds reverts
  (`InsertRevertOnlyAtV35`). -/
inductive TxStepAtV35 (K : Roles) : Tree → Caller → Call → Tree → Prop
  /-- `initL2()` by the upgrader on an uninitialized tree. -/
  | initL2 {T : Tree} {c : Caller} :
      c = K.upgrader → T.leafCount = 0 → TxStepAtV35 K T c .initL2 (setupWrites T)
  /-- `insert(v, hint)` by the appender, written at the walk's exit index. -/
  | insert {T : Tree} {c : Caller} {v : UInt256} {hint low : ℕ} :
      c = K.appender → InsertChecksAtV35 T v hint low →
      TxStepAtV35 K T c (.insert v hint) (insert T v low)

/-- A run of the v35 tree contract (`RunOf`, from `InitOnce`). -/
abbrev TxRunAtV35 (K : Roles) : (ℕ → Tree) → Trace → Prop :=
  RunOf (TxStepAtV35 K)

/-! ## Where the walk lands, and a v35 run read as a pin run -/

/-- Where the v35 walk from `hint` lands: `lowSearch` with `leafCount` hops, which suffice from
an occupied hint of a valid tree (`LowSearchTerminates`).  If that search fails (it never does on
the states of a run from deployment), the hint itself. -/
def landingV35 (T : Tree) (v : UInt256) (hint : ℕ) : ℕ :=
  (lowSearch T v T.leafCount hint).getD hint

/-- A call with an insert's hint replaced by its landing index on `T`.  `initL2()` is unchanged. -/
def relabelCallV35 (T : Tree) : Call → Call
  | .initL2 => .initL2
  | .insert v hint => .insert v (landingV35 T v hint)

/-- The trace `tx` with every insert's hint replaced by its landing index at the state the insert
runs in.  Senders, idle steps and `initL2()` calls are unchanged. -/
def relabelV35 (R : ℕ → Tree) (tx : Trace) : Trace :=
  fun n => (tx n).map (fun p => (p.1, relabelCallV35 (R n) p.2))

/-! ## `_nodes[0]` along a v35 run -/

/-- The `_nodes[0]` writes of a successful v35 transaction.  `initL2()` writes as at the pin
(`pushNewLeaf(hashLeaf({0,0,0}))`, `IndexedMerkleTree.sol:52`, so `setupLevel`).  `insert` writes
`updateLeaf(lowLeafIndex, …)` and `pushNewLeaf(…)` (`:101, :106`) at the index the walk lands on. -/
def levelWritesV35 (hl : LeafHash) (T : Tree) (H : LeafLevel) : Call → LeafLevel
  | .initL2 => setupLevel hl T H
  | .insert v hint => insertLevel hl T H v (landingV35 T v hint)

/-- `L n` is `_nodes[0]` at step `n` of the v35 run `(R, tx)`: unchanged by an idle step, moved by
each successful transaction's writes.  `L 0` is arbitrary. -/
def LevelRunAtV35 (hl : LeafHash) (R : ℕ → Tree) (tx : Trace) (L : ℕ → LeafLevel) : Prop :=
  ∀ n, L (n + 1) = match tx n with
    | none => L n
    | some (_, call) => levelWritesV35 hl (R n) (L n) call

/-! ## The whole storage, padded with `IMT_EMPTY_LEAF_HASH` -/

/-- **`IndexedMerkleTree.setup` at v35, on fresh storage** (`IndexedMerkleTree.sol:46-54`):
`tree.setup(zE)` (`:51`), then `tree.pushNewLeaf(hashLeaf({0,0,0}))` (`:52`), with the sentinel
list state (`:53`).  At v35, `zE` is `IMT_EMPTY_LEAF_HASH` (`Config.sol:141`).  The pin's
`CachedRoot.cSetup` is the instance `zE = hashLeaf({0,0,0})`. -/
def cSetupAtV35 (h : MerkleSpec.Hash) (hl : LeafHash) (zE : UInt256) : Option CState :=
  (FullMerkle.pushNewLeaf h (FullMerkle.setup FullMerkle.FullTree.empty zE).1 (hl ⟨0, 0, 0⟩)).map
    fun r => ⟨setup, r.1⟩

/-- States reached from `cSetupAtV35 h hl zE` by guarded inserts that do not revert inside
`FullMerkle`.  This is `CachedRoot.CReaches` with the v35 setup; the insert step is the same
`cInsert`, since `IndexedMerkleTree.insert`'s two `FullMerkle` calls are unchanged
(`IndexedMerkleTree.sol:101, 106`). -/
inductive CReachesAtV35 (h : MerkleSpec.Hash) (hl : LeafHash) (zE : UInt256) : CState → Prop
  | init {S : CState} : cSetupAtV35 h hl zE = some S → CReachesAtV35 h hl zE S
  | insert {S S' : CState} {v : UInt256} {low : ℕ} {r : UInt256} :
      CReachesAtV35 h hl zE S → InsertGuard S.tree v low → cInsert h hl S v low = some (S', r) →
      CReachesAtV35 h hl zE S'

/-! ## A v35 run the pin does not have -/

/-- The states of a run from deployment: the predeploy, then `chainTree k` after `initL2()` and
`k` inserts, for `k ≤ 7`, and `chainTree 7` from then on. -/
def staleHintRunV35 (n : ℕ) : Tree :=
  if n = 0 then predeploy else chainTree (min (n - 1) 7)

/-- The trace of `staleHintRunV35`: the upgrader's `initL2()`; the appender's honest
`insert(k, k - 1)` for `k = 1, …, 6`; then `insert(7, 0)` from the sentinel, six hops below the
landing index `6` (the pin's five-hop search reverts on it, `HonestInsertRevertsAtDeployedFuel`);
then nothing. -/
def staleHintTxV35 (K : Roles) : Trace := fun n =>
  if n = 0 then some (K.upgrader, .initL2)
  else if n ≤ 6 then some (K.appender, .insert ((n : ℕ) : UInt256) (n - 1))
  else if n = 7 then some (K.appender, .insert 7 0)
  else none

end Contracts.InteropCommitmentTree
