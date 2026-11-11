import EraSpec.Contracts.L2InteropCommitmentTree.Specs.HintSearch
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight
import EraSpec.Contracts.IndexedMerkleTree.Specs.ResetAndZero

/-!
# Model: the contract's two entry points, from deployment storage

`Run`, `Reaches` and `HRun` start at `setup` and step only by guarded inserts. The
deployed contract starts earlier, at the zero storage of a genesis predeploy, and has
a second state-changing entry point, `initL2`, which runs `IndexedMerkleTree.setup`.
This file adds both, so that "the tree is seeded once and its history cannot be reset"
is a statement about the contract's own transactions rather than a property of where
the model chose to start.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.L2InteropCommitmentTree.Properties.InitOnce`, proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.InitOnce`.

## What the source does (era-contracts `c67894b9`)

`L2InteropCommitmentTree.sol` has exactly two non-`view` functions:

    function initL2() external onlyUpgrader {                         // :47-50
        _imt.setup();
        emit RootUpdated(0, _imt.root());
    }
    function insert(uint256 _value, uint256 _lowNullifierIndex)       // :53-59
        external returns (uint256 newIndex, bytes32 newRoot) {
        if (msg.sender != appender()) revert CommitmentTreeNotAppender(msg.sender);
        (newIndex, newRoot) = _imt.insert(_value, _lowNullifierIndex);
        …

`onlyUpgrader` (:36-41) requires `msg.sender == L2_COMPLEX_UPGRADER_ADDR`, and
`appender()` (:82-84) is the constant `L2_ATOMIC_FLOW_MANAGER_ADDR`. Every other
function (:62-84) is `view`. `IndexedMerkleTree.setup` (`IndexedMerkleTree.sol:42-51`):

    if (self.tree._leafNumber != 0) { revert IMTAlreadyInitialized(); }   // :43-45
    bytes32 zeroLeafHash = hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0}));
    self.tree.setup(zeroLeafHash);                                         // :48
    self.tree.pushNewLeaf(zeroLeafHash);                                   // :49
    self.leaves[0] = IMTLeaf({value: 0, nextIndex: 0, nextValue: 0});      // :50

On the list state (`Tree`), past its guard, that is: `_leafNumber` goes up by one
(`FullMerkle.pushNewLeaf`, `FullMerkle.sol:43`; `FullMerkle.setup`, `:29-35`, only pushes
onto `_zeros` and `_nodes`), and `leaves[0]` is overwritten with `{0,0,0}`. Nothing
else is written: no other `leaves[i]`, and no `valueToIndex` entry. `setupWrites` below
is exactly that. On the zero storage of the predeploy it yields the model's `setup`.

## Deployment

The tree is a ZKsync OS genesis predeploy with no constructor (`L2InteropCommitmentTree.sol:26`):
the genesis tool places a `SystemContractProxy` at its address with the implementation
elsewhere (`tools/zksync-os-genesis-gen/src/consts.rs:248-251`, `genesis.rs:69-79`), and
the proxy's only initial storage is the EIP-1967 implementation and admin slots
(`genesis.rs:85-86, 330-338`). So `_imt` starts as all-zero storage, which is `predeploy`.
The genesis upgrade calls `initL2()` once, on ZKsync OS genesis only
(`L2GenesisForceDeploymentsHelper.sol:448-461`). The proxy forwards `initL2` and `insert`
to the implementation for every caller (`SystemContractProxy.sol:39-67`).

## The countermodel's machine

`TxStepNoGuard` is `TxStep` with the `_leafNumber != 0` check of `IMT.setup` deleted and
nothing else changed. Run on a tree that already holds a value, `setupWrites` does not
erase it: `leaves[i]` for `i ≥ 1` and `valueToIndex` are untouched. What it does is
reset the sentinel's links (`leaves[0] := {0,0,0}`, so its window is `(0, ∞)`) and occupy
index `_leafNumber`, whose `leaves` entry no transaction has written (so it reads
`{0,0,0}`) and whose hash `pushNewLeaf(zeroLeafHash)` writes into the hash tree. Either
leaf straddles every delivered value. (The stored hash at index 0 is not rewritten by
`:50`, so after such a call the list state and the hash tree also disagree at index 0;
the zero leaf at the old `_leafNumber` is in both.)

## Model boundary

* The model is the implementation's own code. The complex upgrader also owns the
  `SystemContractProxyAdmin` that administers the tree's proxy (`genesis.rs:320-328`), and
  through it can `upgradeTo`/`upgradeToAndCall` (`SystemContractProxy.sol:42-49`), which
  can rewrite `_imt` arbitrarily. Such an upgrade is outside this transition system
  (`OPS-CONFIG`, and the governance caveat in `ResetAndZero`).
* A reverted transaction, or a transaction to another contract, is an idle step: it
  leaves the tree unchanged (`VM-REVERT`, `MODEL-COMMIT`).
* `insert`'s label is the calldata `(_value, _lowNullifierIndex)`; the index written is
  the one the bounded search returns, with the deployed fuel
  `MAX_LOW_INDEX_SEARCH_ATTEMPTS` (`HintSearch`).
* Counts and indices are `ℕ`. `_leafNumber++` is checked arithmetic and cannot reach
  `2^256` in practice, so `_leafNumber` never returns to `0`.
* Callers are compared with the two role addresses by equality only.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## Callers and roles -/

/-- A `msg.sender`, as a word. Only equality with the role addresses is used. -/
abbrev Caller := UInt256

/-- The two addresses the contract compares `msg.sender` against. -/
structure Roles where
  /-- `L2_COMPLEX_UPGRADER_ADDR`, checked by `onlyUpgrader`
  (`L2InteropCommitmentTree.sol:36-41`). -/
  upgrader : Caller
  /-- `appender()`, the constant `L2_ATOMIC_FLOW_MANAGER_ADDR`
  (`L2InteropCommitmentTree.sol:82-84`), checked first thing in `insert` (`:54`). -/
  appender : Caller

/-- The deployed role addresses: `L2_COMPLEX_UPGRADER_ADDR = SYSTEM_CONTRACTS_OFFSET + 0x0f`
(`L2ContractAddresses.sol:75`, `system-contracts/contracts/Constants.sol:10`) and
`L2_ATOMIC_FLOW_MANAGER_ADDR = BUILT_IN_CONTRACTS_OFFSET + 0x14`
(`L2ContractAddresses.sol:12,150`). -/
def deployedRoles : Roles := ⟨0x800f, 0x10014⟩

/-! ## Entry points -/

/-- The contract's state-changing entry points (`L2InteropCommitmentTree.sol:47-59`); every
other function of the contract is `view`. -/
inductive Call where
  /-- `initL2()`. -/
  | initL2
  /-- `insert(_value, _lowNullifierIndex)`: the value and the caller's low-leaf hint. -/
  | insert (value : UInt256) (hint : ℕ)
deriving DecidableEq

/-- The only caller each entry point accepts. -/
def Roles.roleFor (K : Roles) : Call → Caller
  | .initL2 => K.upgrader
  | .insert _ _ => K.appender

/-! ## States -/

/-- The predeploy's storage before `initL2`: `_leafNumber = 0`, every `leaves[i]` and every
`valueToIndex[v]` zero. -/
def predeploy : Tree where
  leafCount := 0
  leaf := fun _ => ⟨0, 0, 0⟩
  valueToIndex := fun _ => 0

/-- The list-state writes of `IndexedMerkleTree.setup` past its guard
(`IndexedMerkleTree.sol:47-50`): `pushNewLeaf` increments `_leafNumber`, and
`leaves[0] := {0,0,0}`. Every other leaf and all of `valueToIndex` are left as they were. -/
def setupWrites (T : Tree) : Tree where
  leafCount := T.leafCount + 1
  leaf := fun i => if i = 0 then ⟨0, 0, 0⟩ else T.leaf i
  valueToIndex := T.valueToIndex

/-! ## Transactions -/

/-- What a successful `insert(v, hint)` has checked before it writes, at the index `low`
the search returns (`IndexedMerkleTree.sol:65-92`). -/
structure InsertChecks (T : Tree) (v : UInt256) (hint low : ℕ) : Prop where
  /-- `leafNumber == 0` reverts with `IMTNotInitialized` (:65-68). -/
  initialized : Initialized T
  /-- `_value == 0` reverts with `IMTValueZero` (:69-71). -/
  nonzero : v ≠ 0
  /-- `valueToIndex[_value] != 0` reverts with `IMTValueAlreadyExists` (:72-74). -/
  unregistered : T.valueToIndex v = 0
  /-- `_lowLeafIndex >= leafNumber` reverts with `IMTLowLeafIndexOutOfBounds` (:75-77). -/
  hintInBounds : hint < T.leafCount
  /-- `lowLeaf.value >= _value` reverts with `IMTLowLeafValueTooLarge` (:79-83). -/
  hintBelow : (T.leaf hint).value < v
  /-- The bounded walk (:85-92) ends at `low`; running out of hops reverts with
  `IMTLowLeafNextTooSmall`. -/
  search : lowSearch T v maxLowIndexSearchAttempts hint = some low

/-- One successful transaction of the deployed contract, sent by `c`. -/
inductive TxStep (K : Roles) : Tree → Caller → Call → Tree → Prop
  /-- `initL2()`: `onlyUpgrader`, then `IMT.setup`, which reverts with
  `IMTAlreadyInitialized` unless `_leafNumber == 0`. -/
  | initL2 {T : Tree} {c : Caller} :
      c = K.upgrader → T.leafCount = 0 → TxStep K T c .initL2 (setupWrites T)
  /-- `insert(v, hint)`: the appender check, the engine's checks, the search, then the
  three writes of `insert` at the searched index. -/
  | insert {T : Tree} {c : Caller} {v : UInt256} {hint low : ℕ} :
      c = K.appender → InsertChecks T v hint low →
      TxStep K T c (.insert v hint) (insert T v low)

/-- The countermodel's machine: `TxStep` with `IMT.setup`'s `_leafNumber != 0` check
deleted. Nothing else differs. -/
inductive TxStepNoGuard (K : Roles) : Tree → Caller → Call → Tree → Prop
  /-- `initL2()` with `onlyUpgrader` but without `IMTAlreadyInitialized`. -/
  | initL2 {T : Tree} {c : Caller} :
      c = K.upgrader → TxStepNoGuard K T c .initL2 (setupWrites T)
  /-- `insert(v, hint)`, exactly as in `TxStep`. -/
  | insert {T : Tree} {c : Caller} {v : UInt256} {hint low : ℕ} :
      c = K.appender → InsertChecks T v hint low →
      TxStepNoGuard K T c (.insert v hint) (insert T v low)

/-! ## Runs -/

/-- A trace: at each step, the transaction that succeeded and its sender, or `none` if
nothing succeeded. Reverted transactions are not recorded. -/
abbrev Trace := ℕ → Option (Caller × Call)

/-- A run of a transaction relation `step`: states `R n`, and at each step `n` either no
transaction succeeded (`tx n = none`; the state is unchanged) or `tx n = some (c, call)`
and that transaction took `R n` to `R (n + 1)`. -/
def RunOf (step : Tree → Caller → Call → Tree → Prop) (R : ℕ → Tree) (tx : Trace) : Prop :=
  ∀ n, (tx n = none ∧ R (n + 1) = R n)
    ∨ ∃ (c : Caller) (call : Call), tx n = some (c, call) ∧ step (R n) c call (R (n + 1))

/-- A run of the deployed contract. -/
abbrev TxRun (K : Roles) : (ℕ → Tree) → Trace → Prop :=
  RunOf (TxStep K)

/-- A run of the countermodel's machine. -/
abbrev TxRunNoGuard (K : Roles) : (ℕ → Tree) → Trace → Prop :=
  RunOf (TxStepNoGuard K)

/-! ## Concrete runs, for the witnesses -/

/-- Deployment, `initL2()` by the upgrader, then `insert(a, 0)` and `insert(b, 1)` by the
appender, then nothing: the states. For `0 < a < b` the last is `threeLeafTree a b`. -/
def genesisRun (a b : UInt256) : ℕ → Tree :=
  fun n => if n = 0 then predeploy else if n = 1 then setup
    else if n = 2 then insert setup a 0 else threeLeafTree a b

/-- The trace of `genesisRun`. -/
def genesisTx (K : Roles) (a b : UInt256) : Trace :=
  fun n => if n = 0 then some (K.upgrader, .initL2)
    else if n = 1 then some (K.appender, .insert a 0)
    else if n = 2 then some (K.appender, .insert b 1) else none

/-- Deployment, `initL2()` by the upgrader, `insert(a, 0)` by the appender, then a second
`initL2()` by the upgrader, which only the guardless machine accepts, then nothing: the
states. -/
def reinitRun (a : UInt256) : ℕ → Tree :=
  fun n => if n = 0 then predeploy else if n = 1 then setup
    else if n = 2 then insert setup a 0 else setupWrites (insert setup a 0)

/-- The trace of `reinitRun`. -/
def reinitTx (K : Roles) (a : UInt256) : Trace :=
  fun n => if n = 0 then some (K.upgrader, .initL2)
    else if n = 1 then some (K.appender, .insert a 0)
    else if n = 2 then some (K.upgrader, .initL2) else none

/-! ## The hash tree's leaf level, as a ghost over runs

`TreeRoot` publishes the root over `leafHashes hl T`, the hashes of the list state's
leaves. The contract does not compute it from `leaves`: `FullMerkle` keeps its own copy
of the leaf hashes in `_nodes[0]`. The first `FullMerkle.setup` creates that array with
one slot (`FullMerkle.sol:32`); `updateLeaf(i, x)` sets entry `i` to `x` (`:78`);
`pushNewLeaf(x)` appends a placeholder unless the index is 0 (`:53-64`) and then calls
`updateLeaf` at index `_leafNumber` (`:43, 65`). So, net, `pushNewLeaf(x)` sets entry
`_leafNumber` to `x`, and nothing else writes the array. `IMT.setup` and `IMT.insert` write `leaves` and `_nodes[0]` separately. This layer
tracks `_nodes[0]` along a run, so that whether the two copies agree is a statement rather
than a modelling choice.

That the stored root `_nodes[_height][0]` is `rootOf` over `_nodes[0]` at `_height` stays
the open obligation O7 (the cached-nodes half), as in `TreeRoot` and `RunHeight`. -/

/-- `FullMerkle._nodes[0]`, the stored leaf hashes, as a total function of the index. -/
abbrev LeafLevel := ℕ → UInt256

/-- `IMT.setup`'s write to `_nodes[0]` past its guard: `pushNewLeaf(zeroLeafHash)` stores the
zero leaf's hash at index `_leafNumber` (`IndexedMerkleTree.sol:47-49`). The write
`leaves[0] := {0,0,0}` (`:50`) does not touch `_nodes`. -/
def setupLevel (hl : LeafHash) (T : Tree) (H : LeafLevel) : LeafLevel :=
  Function.update H T.leafCount (hl ⟨0, 0, 0⟩)

/-- `IMT.insert`'s writes to `_nodes[0]` at the searched index `low`:
`updateLeaf(low, hashLeaf(updatedLowLeaf))`, then `pushNewLeaf(hashLeaf(newLeaf))` at index
`_leafNumber` (`IndexedMerkleTree.sol:98-105`). -/
def insertLevel (hl : LeafHash) (T : Tree) (H : LeafLevel) (v : UInt256) (low : ℕ) :
    LeafLevel :=
  Function.update
    (Function.update H low (hl { T.leaf low with nextIndex := T.leafCount, nextValue := v }))
    T.leafCount (hl ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩)

/-- The `_nodes[0]` writes of a successful transaction `call` on the list state `T`. For
`insert`, the index is the one the search returns, which a successful insert has
(`InsertChecks.search`); the `none` branch is never taken by a successful transaction. -/
def levelWrites (hl : LeafHash) (T : Tree) (H : LeafLevel) : Call → LeafLevel
  | .initL2 => setupLevel hl T H
  | .insert v hint =>
      match lowSearch T v maxLowIndexSearchAttempts hint with
      | some low => insertLevel hl T H v low
      | none => H

/-- `L n` is `_nodes[0]` at step `n` of the run `(R, tx)`: unchanged by an idle step, and
moved by each successful transaction's writes. `L 0` is arbitrary. -/
def LevelRun (hl : LeafHash) (R : ℕ → Tree) (tx : Trace) (L : ℕ → LeafLevel) : Prop :=
  ∀ n, L (n + 1) = match tx n with
    | none => L n
    | some (_, call) => levelWrites hl (R n) (L n) call

/-- The stored leaf hashes of the first `n` indices, in order: the list `rootOf` folds. -/
def storedLeaves (H : LeafLevel) (n : ℕ) : List UInt256 :=
  (List.range n).map H

/-- `_nodes[0]` along `genesisRun a b`, from the predeploy's empty array (read as zeros). -/
def genesisLevel (hl : LeafHash) (a b : UInt256) : ℕ → LeafLevel :=
  fun n => if n = 0 then fun _ => 0
    else if n = 1 then setupLevel hl predeploy (fun _ => 0)
    else if n = 2 then insertLevel hl setup (setupLevel hl predeploy (fun _ => 0)) a 0
    else insertLevel hl (insert setup a 0)
      (insertLevel hl setup (setupLevel hl predeploy (fun _ => 0)) a 0) b 1

/-- `_nodes[0]` along `reinitRun a`, from the predeploy's empty array (read as zeros). -/
def reinitLevel (hl : LeafHash) (a : UInt256) : ℕ → LeafLevel :=
  fun n => if n = 0 then fun _ => 0
    else if n = 1 then setupLevel hl predeploy (fun _ => 0)
    else if n = 2 then insertLevel hl setup (setupLevel hl predeploy (fun _ => 0)) a 0
    else setupLevel hl (insert setup a 0)
      (insertLevel hl setup (setupLevel hl predeploy (fun _ => 0)) a 0)

end Contracts.InteropCommitmentTree
