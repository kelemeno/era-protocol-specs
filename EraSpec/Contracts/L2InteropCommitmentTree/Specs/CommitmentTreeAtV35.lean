import EraSpec.Contracts.L2InteropCommitmentTree.Specs.InitOnce
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.CachedRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.HintSearchAtHead

/-!
# Model at `draft/v0.35.0`: the tree contract's transactions on its whole storage

**Commit.** era-contracts `draft/v0.35.0` at `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`.  Paths are
relative to `l1-contracts/contracts/`.  This model was first drafted against `d9f6789`
(`d9f678900e1bc8286412b78f56d4a9f443983c29`); none of the files cited below changed between the
two commits.

**`main`.**  At `main` `70096e2ea6eeb5373992e178064c4b26dcf6436a`,
`common/libraries/IndexedMerkleTree.sol`, `common/libraries/FullMerkle.sol` and
`common/libraries/Merkle.sol` are byte-identical to the files here.  `atomic-interop/L2InteropCommitmentTree.sol` differs only in where it imports its three error
types from: `main` has one import line (12) where this branch has two (12-13), so line `n ≥ 14`
here is line `n - 1` on `main`.  `IMT_EMPTY_LEAF_HASH` is `common/Config.sol:90` on `main` and
`:141` here.  So the machine below describes the tree code of `main` as well.  The other files
cited below (`common/l2-helpers/L2ContractAddresses.sol`, the genesis helper,
`AtomicFlowManager.sol`) have different line numbers on `main`: for example
`L2_COMPLEX_UPGRADER_ADDR` is at `L2ContractAddresses.sol:80` and `L2_ATOMIC_FLOW_MANAGER_ADDR` at
`:157`.  The address values are the same (`0x800f`, `0x10014`, `0x7004`); every citation below is
`b17415d20`'s.

**The canonical model.**  `CTxStepAtV35` / `CTxRunAtV35` is the one v35 model of the tree
contract.  Its walk and checks are `WalkExitsAtV35` and `InsertChecksAtV35`
(`Specs/HintSearch.lean`), its `initL2()` makes the same `FullMerkle` calls as
`CachedRoot.cSetupPad`, and its list state projects onto
`HintSearchAtHead.TxStepAtHead` (`Properties.CTxRunAtV35ProjectsToTxRunAtHead`).

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.L2InteropCommitmentTree.Properties.CommitmentTreeAtV35`, proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CommitmentTreeAtV35`.

## Why a new machine

At the pin, `InitOnce` models the tree contract's two entry points with their callers, from the
predeploy's all-zero storage, but on the list state only: `FullMerkle`'s leaf level `_nodes[0]` is
a ghost, and the stored root `_nodes[_height][0]` is not part of its statements.  `CachedRoot`
carries `FullMerkle`'s whole storage, but starts at `setup` and steps by guarded inserts, with no
caller, no hint and no `initL2`.  So neither describes the root that the contract's own
transactions write, from genesis storage.  `CTxStepAtV35` does, for the v35 code: it is one
successful transaction (`initL2()` or `insert(v, hint)`, with its sender), acting on the list
state and the whole `FullMerkle` storage (`CState`) through the transcribed library calls
(`FullMerkle/Specs/CachedNodes.lean`), at the points where `IndexedMerkleTree.setup` and `insert`
make them.  Runs start from the predeploy's storage, `cPredeployAtV35`.

## What changed since the pin

1. **The low-leaf walk is unbounded** (`b8cc61203`, #2349).  `IndexedMerkleTree.insert`
   (`IndexedMerkleTree.sol:65-107`) keeps the pin's checks (`:70-88`) and writes (`:95-106`), but
   its loop is now

       while (lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value) {          // :90-93
           lowLeafIndex = lowLeaf.nextIndex;
           lowLeaf = self.leaves[lowLeafIndex];
       }

   and `MAX_LOW_INDEX_SEARCH_ATTEMPTS` is gone from `common/Config.sol` (pin `:66`).  The exit test
   and the hop are the pin's.  `WalkExitsAtV35` reads the loop as "some number of hops of
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
   (pin `IndexedMerkleTree.sol:47-49`).  `cInitL2AtV35 h hl zE` passes `zE` to `FullMerkle.setup`
   and `hl ⟨0,0,0⟩` to `pushNewLeaf`.  The list state it writes is the pin's (`setupWrites`).

3. **`L2InteropCommitmentTree.insert` reports the leaf** (`L2InteropCommitmentTree.sol:51-64`).
   After the engine's insert (`:57`) it calls `_reportLeaf(_value)` (`:62`, body `:71-76`).  That
   burns the log gas (`_burnLogGas`, `:80-91`: a self-call into `fallback`, whose result is
   ignored) and calls `INTEROP_COMMITMENT_LEAF_HOOK`
   (`common/l2-helpers/L2ContractAddresses.sol:27`, `SYSTEM_HOOKS_OFFSET + 0x04 = 0x7004`) under `require(ok, InteropCommitmentLeafHookFailed())`
   (`:75`).  A new `fallback` (`:121-126`) requires `msg.sender == address(this)` and executes
   `invalid()`, so every call to it reverts.  None of these paths writes `_imt` (for the hook, see
   the model boundary); each can only make the insert revert.  `CTxStepAtV35` records successful
   transactions and does not model them.

## What did not change

* `onlyUpgrader` (`L2InteropCommitmentTree.sol:35-40`; `L2_COMPLEX_UPGRADER_ADDR =
  SYSTEM_CONTRACTS_OFFSET + 0x0f = 0x800f`, `L2ContractAddresses.sol:6, 65`), `initL2`
  (`:45-48`), the appender check (`:52-54`) and `appender()` (`:114-116`;
  `L2_ATOMIC_FLOW_MANAGER_ADDR = BUILT_IN_CONTRACTS_OFFSET + 0x14 = 0x10014`,
  `L2ContractAddresses.sol:12, 142`).  So `Roles`, `deployedRoles` and `Call` (`InitOnce`) describe
  v35.  The one appender call site is `AtomicFlowManager.append`
  (`atomic-interop/AtomicFlowManager.sol:104`, tree call `:170`).
* `root`, `merklePath`, `hashLeaf` (`IndexedMerkleTree.sol:110-112, 116-118, 124-126`) and the two
  verifiers (`verifyInclusion` `:134-146`, `verifyNonInclusion` `:154-172`).  So `CState.root`,
  `CState.merklePath` (`CachedRoot`) and `TreeRoot`'s `PathAccepts`, `InclusionAccepted` and
  `NonInclusionAccepted` describe v35.  In particular `Merkle.calculateRootMemory`
  (`common/libraries/Merkle.sol:53-70`) still bounds the index only by `2 ^ pathLength`
  (`_validatePathLengthForSingleProof`, `:133-140`), not by the leaf count.
* `FullMerkle.sol`, `Merkle.sol` and `l2-upgrades/SystemContractProxy.sol` are byte-identical to the
  pin.  So `FullMerkle/Specs/CachedNodes.lean` and `CachedRoot.cInsert` describe v35.  The padding
  enters `cInsert` only through the storage that `FullMerkle.setup` (`FullMerkle.sol:29-35`) seeds
  with whatever constant it is passed: `_zeros`, and the `_nodes` entries made from it.
* The genesis upgrade is the caller of `initL2()`:
  `L2GenesisForceDeploymentsHelper._initContractsAfterWiring`
  (`l2-upgrades/L2GenesisForceDeploymentsHelper.sol:352-375`, the call at `:373`) runs only when
  `_isGenesisUpgrade` (`:230-232`).  That is not modelled: the machine lets the upgrader send
  `initL2()` at any step, and its guard decides.

## Model boundary

* As in `InitOnce`: a reverted transaction, or a transaction to another contract, is an idle step
  (`tx n = none`).  Callers are compared with the two role addresses by equality only.  Proxy
  upgrades through the tree's `SystemContractProxy` are outside the machine (`OPS-CONFIG`).  Runs
  start from all-zero storage; how the genesis tool leaves the tree's storage is not re-checked at
  v35.
* As in `CachedRoot` (`MODEL-FULLMERKLE`): a revert inside a `FullMerkle` call is `none`, counters
  and indices are `ℕ`, and `Merkle.efficientHash` is the abstract node hash `h`.
* `zE` is a parameter standing for `IMT_EMPTY_LEAF_HASH`, and nothing is assumed about it.  A
  statement that needs `zE` to differ from a leaf hash concludes the located equation `hl ℓ = zE`
  instead of assuming it away.  At v35 that equation says that keccak takes the same value on the
  96-byte `abi.encode(ℓ.value, ℓ.nextIndex, ℓ.nextValue)` (`IndexedMerkleTree.sol:125`) and on the
  34-byte string of `Config.sol:141`; keccak at the byte level is not modelled here.
* `CState` holds `_leafNumber` twice: `tree.leafCount` (the list state's copy, which `InitOnce`'s
  checks read) and `fm.leafNumber` (the one the `FullMerkle` calls read).  The source has one slot.
  The checks below read `tree.leafCount`, and `cInsert` puts the new leaf at `tree.leafCount`.
  Along every run from `cPredeployAtV35` the two copies are equal at every state
  (`Properties.CTxRunAtV35StoredRootIsPublished`), so there it does not matter which one is read.
* `FullMerkle.updateLeaf`'s range check (`FullMerkle.sol:74-77`, reached from
  `IndexedMerkleTree.sol:101`) is part of the transcription: `cInsert` returns `none` when the walk
  lands at or beyond `fm.leafNumber`.  So the insert checks below have no field for it.
* Gas is not modelled.  The walk's hops, `_burnLogGas` and the hook call cost gas, and a transaction
  that runs out of it reverts.  `CTxStepAtV35` admits such a transaction as a step: it
  over-approximates the successful transactions, the safe direction for statements about all runs.
  The run of the witnesses is a run of this machine; that gas suffices for it and that the hook
  accepts each report is not shown.
* `INTEROP_COMMITMENT_LEAF_HOOK` is a ZKsync OS system hook, not in this source tree.  That it does
  not write the tree's storage is taken from its description (`L2InteropCommitmentTree.sol:58-61,
  66-70`), not proved.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## Storage and the setup call -/

/-- **THE PREDEPLOY'S STORAGE.**  The list state `predeploy` (`_leafNumber = 0`, every `leaves[i]`
and `valueToIndex[v]` zero) and fresh `FullMerkle` storage (both counters zero, `_nodes` and
`_zeros` empty). -/
def cPredeployAtV35 : CState := ⟨predeploy, FullMerkle.FullTree.empty⟩

/-- **`IndexedMerkleTree.setup` AT v35, PAST ITS GUARD** (`IndexedMerkleTree.sol:51-53`), on the
storage `S`: `tree.setup(zE)`, then `tree.pushNewLeaf(hashLeaf({0,0,0}))`, then
`leaves[0] := {0,0,0}`; on the list state this is `setupWrites` (which also counts the pushed
leaf).  At v35, `zE` is `IMT_EMPTY_LEAF_HASH`.  `none` is a revert inside `FullMerkle`.  On
`cPredeployAtV35` with `zE = hashLeaf({0,0,0})` this is the pin's `CachedRoot.cSetup`
(`Properties.CInitL2AtV35AtPinPaddingIsCSetup`). -/
def cInitL2AtV35 (h : MerkleSpec.Hash) (hl : LeafHash) (zE : UInt256) (S : CState) :
    Option CState :=
  (FullMerkle.pushNewLeaf h (FullMerkle.setup S.fm zE).1 (hl ⟨0, 0, 0⟩)).map
    fun r => ⟨setupWrites S.tree, r.1⟩

/-! ## Transactions and runs -/

/-- **ONE SUCCESSFUL TRANSACTION OF THE v35 TREE CONTRACT ON ITS WHOLE STORAGE**, sent by `c`,
for node hash `h`, leaf hash `hl` and padding constant `zE`.

* `initL2()` (`L2InteropCommitmentTree.sol:45-48`): `onlyUpgrader` (`:35-40`), then
  `IndexedMerkleTree.setup`, which reverts with `IMTAlreadyInitialized` unless `_leafNumber == 0`
  (`IndexedMerkleTree.sol:47-49`), then its calls (`cInitL2AtV35`).
* `insert(v, hint)` (`:51-64`): the appender check (`:52-54`), the engine's checks and walk
  (`InsertChecksAtV35`), then `updateLeaf(low, …)` and `pushNewLeaf(…)` with the list update at
  the exit index `low` (`CachedRoot.cInsert`, `IndexedMerkleTree.sol:95-106`), which must not
  revert.  The leaf report (`:62`) is not modelled (module header, item 3). -/
inductive CTxStepAtV35 (h : MerkleSpec.Hash) (hl : LeafHash) (zE : UInt256) (K : Roles) :
    CState → Caller → Call → CState → Prop
  /-- `initL2()` by the upgrader on storage whose `_leafNumber` is zero. -/
  | initL2 {S S' : CState} {c : Caller} :
      c = K.upgrader → S.tree.leafCount = 0 → cInitL2AtV35 h hl zE S = some S' →
      CTxStepAtV35 h hl zE K S c .initL2 S'
  /-- `insert(v, hint)` by the appender, written at the walk's exit index `low`; `r` is the
  `newRoot` it returns. -/
  | insert {S S' : CState} {c : Caller} {v : UInt256} {hint low : ℕ} {r : UInt256} :
      c = K.appender → InsertChecksAtV35 S.tree v hint low → cInsert h hl S v low = some (S', r) →
      CTxStepAtV35 h hl zE K S c (.insert v hint) S'

/-- **A RUN OF THE v35 TREE CONTRACT ON ITS WHOLE STORAGE**: states `R n`, and at each step `n`
either no transaction succeeded (`tx n = none`; the storage is unchanged) or `tx n = some (c, call)`
and that transaction took `R n` to `R (n + 1)`.  `InitOnce.RunOf` with `CState` for `Tree`. -/
def CTxRunAtV35 (h : MerkleSpec.Hash) (hl : LeafHash) (zE : UInt256) (K : Roles)
    (R : ℕ → CState) (tx : Trace) : Prop :=
  ∀ n, (tx n = none ∧ R (n + 1) = R n)
    ∨ ∃ (c : Caller) (call : Call),
        tx n = some (c, call) ∧ CTxStepAtV35 h hl zE K (R n) c call (R (n + 1))

/-! ## A concrete run, for the witnesses -/

/-- The list states of a run from deployment: the predeploy, then `chainTree k` after `initL2()`
and `k` inserts, for `k ≤ 7`, and `chainTree 7` from then on. -/
def staleHintRunV35 (n : ℕ) : Tree :=
  if n = 0 then predeploy else chainTree (min (n - 1) 7)

/-- The trace of `staleHintRunV35`: the upgrader's `initL2()`; the appender's honest
`insert(k, k - 1)` for `k = 1, …, 6`; then `insert(7, 0)` from the sentinel, whose walk makes six
hops to the exit index `6` (the pin's five-hop search reverts on it,
`HonestInsertRevertsAtDeployedFuel`); then nothing. -/
def staleHintTxV35 (K : Roles) : Trace := fun n =>
  if n = 0 then some (K.upgrader, .initL2)
  else if n ≤ 6 then some (K.appender, .insert ((n : ℕ) : UInt256) (n - 1))
  else if n = 7 then some (K.appender, .insert 7 0)
  else none

/-- The whole storage after `initL2()` on the predeploy and then `insert(j + 1)` at the exit index
`j` for `j = 0, …, k - 1`: the storage of `chainTree k`.  Each call is evaluated with the
transcribed library; the fallback value (the previous storage) is used only if a call reverts,
which for `k ≤ 7` none does (the steps of `Properties.StaleHintCRunWitnessAtV35` are these
calls). -/
def chainCStateAtV35 (h : MerkleSpec.Hash) (hl : LeafHash) (zE : UInt256) : ℕ → CState
  | 0 => (cInitL2AtV35 h hl zE cPredeployAtV35).getD cPredeployAtV35
  | k + 1 =>
      ((cInsert h hl (chainCStateAtV35 h hl zE k) ((k + 1 : ℕ) : UInt256) k).map Prod.fst).getD
        (chainCStateAtV35 h hl zE k)

/-- The states of the run `staleHintTxV35` on the whole storage: `cPredeployAtV35`, then
`chainCStateAtV35 h hl zE k` after `initL2()` and `k` inserts, for `k ≤ 7`, and
`chainCStateAtV35 h hl zE 7` from then on. -/
def staleHintCRunAtV35 (h : MerkleSpec.Hash) (hl : LeafHash) (zE : UInt256) (n : ℕ) : CState :=
  if n = 0 then cPredeployAtV35 else chainCStateAtV35 h hl zE (min (n - 1) 7)

end Contracts.InteropCommitmentTree
