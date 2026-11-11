import EraSpec.Contracts.L2InteropCommitmentTree.Specs.InitOnce

/-!
# Model at head: `insert`'s low-leaf walk has no hop bound

**Commit.** era-contracts `main` at `3605e82dbdca5b60bd7bc6bde14ebb52a6b09b73`.  The two
files cited below, `common/libraries/IndexedMerkleTree.sol` and
`atomic-interop/L2InteropCommitmentTree.sol`, are the same on `draft/v0.35.0` at
`d9f678900e1bc8286412b78f56d4a9f443983c29` (the tree differs only in two import lines).
Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.L2InteropCommitmentTree.Properties.HintSearchAtHead`, proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearchAtHead`.

## What changed since the pin

At the pin (`c67894b9`) the search loop of `IndexedMerkleTree.insert` was

    for (uint256 attempts = 0; lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value; ++attempts) {
        if (attempts == MAX_LOW_INDEX_SEARCH_ATTEMPTS) revert IMTLowLeafNextTooSmall(..);
        lowLeafIndex = lowLeaf.nextIndex;
        lowLeaf = self.leaves[lowLeafIndex];
    }

with `MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5`.  That is `lowSearch` with fuel
`maxLowIndexSearchAttempts` (`Specs/HintSearch.lean`), and `InitOnce.InsertChecks.search` and
`AppendPath.InsertSucceeds.search` use exactly that fuel.  Commit `b8cc61203` (#2349, "IMT
insert: remove low-leaf search bound so stale hints cannot trigger hint-validity reverts")
replaced the loop by (`IndexedMerkleTree.sol:90-93`)

    while (lowLeaf.nextValue != 0 && lowLeaf.nextValue < _value) {
        lowLeafIndex = lowLeaf.nextIndex;
        lowLeaf = self.leaves[lowLeafIndex];
    }

and removed the constant from `common/Config.sol`.  The NatSpec says the walk is
"deliberately unbounded", because a bound "would make inserts grievable" (`:59-62`).  The exit
condition and the hop are the pin's.  So are the checks before the loop and the writes after
it, at shifted lines:

    leafNumber == 0                → IMTNotInitialized         :71-73
    _value == 0                    → IMTValueZero              :74-76
    valueToIndex[_value] != 0      → IMTValueAlreadyExists     :77-79
    _lowLeafIndex >= leafNumber    → IMTLowLeafIndexOutOfBounds :80-82
    leaves[_lowLeafIndex].value >= _value → IMTLowLeafValueTooLarge :84-88
    writes: low leaf retargeted, new leaf at leafNumber, valueToIndex  :95-106

## How the model reads the unbounded loop

`lowSearch T v n i` (`Specs/Model.lean`) runs the loop from `i` with at most `n` hops.  It
returns `none` only when the loop would need more hops.  A successful transaction ran the
`while` loop finitely often.  A loop that never exits runs out of gas, and the transaction
reverts, which is no step.  So `WalkSucceedsAtHead T v hint low`, "some number of hops `n`
makes `lowSearch T v n hint` return `low`", is exactly "the loop exits, at `low`".  Which `n`
does not matter: once the walk exits, more hops do not change its result
(`Contracts.InteropCommitmentTree.Properties.WalkAtHeadIsLeafCountSearch`).  Gas is outside
the model.

## The tree contract at head

`L2InteropCommitmentTree` still has the two state-changing entry points of `InitOnce`:
`initL2` (`L2InteropCommitmentTree.sol:44-47`, `onlyUpgrader` at `:34-39`) and `insert`
(`:50-63`, appender check at `:51-53`, then the engine's `insert` at `:56`).  Two additions do
not write the list state:

* after the engine's insert, `insert` reports the value to `INTEROP_COMMITMENT_LEAF_HOOK`
  (`_reportLeaf`, `:61`, `:70-75`).  The report first burns gas through a self-call
  (`_burnLogGas`, `:79-90`), and it reverts the insert if the hook call fails.  Both only
  reject calls;
* a `fallback` (`:120-125`) requires `msg.sender == address(this)` and then executes
  `invalid()`, so every call to it reverts.

`IndexedMerkleTree.setup` (`IndexedMerkleTree.sol:46-54`) writes the same list state as at
the pin: `pushNewLeaf` raises `_leafNumber` by one, and `leaves[0] := {0,0,0}`.  Its hash
writes changed: `FullMerkle.setup` now pads with `IMT_EMPTY_LEAF_HASH`, and index 0's stored
hash is still `hashLeaf({0,0,0})`.  `Tree` has no hash side, and the `_nodes[0]` ghost
(`setupLevel`) records only index 0's stored hash, so neither changes here.  The padding
change is a separate topic.  So `TxStepAtHead` is `InitOnce.TxStep` with the insert's
five-hop search replaced by the head's walk, and nothing else differs.

## Relabelling a head run

`landingAtHead T v hint` is where the walk from `hint` lands, computed with `leafCount` hops,
which suffice on a valid tree (`LowSearchTerminates`).  `relabelAtHead R tx` is the trace `tx`
with every insert's hint replaced by its landing index at the state it runs in.  Initial
calls and idle steps stay as they are.  From its landing index the walk makes no hop, so the
pin's five hops suffice.  That is why a head run, relabelled, is a pin run with the same
states (`Contracts.InteropCommitmentTree.Properties.TxRunAtHeadIsRelabelledTxRun`).
`LevelRunAtHead` is the `_nodes[0]` ghost of a head run: `LevelRun` over the relabelled trace,
so that each insert writes its leaf hashes at the index the walk lands on, as
`IndexedMerkleTree.sol:100-106` does.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## The walk and the insert checks at head -/

/-- **THE HEAD'S `while` LOOP EXITS AT `low`** (`IndexedMerkleTree.sol:90-93`): some finite
number of hops from `hint` ends on `low`.  See the module header for why this is the loop. -/
def WalkSucceedsAtHead (T : Tree) (v : UInt256) (hint low : ℕ) : Prop :=
  ∃ hops : ℕ, lowSearch T v hops hint = some low

/-- What a successful `insert(v, hint)` has checked at head before it writes, at the index
`low` the walk lands on (`IndexedMerkleTree.sol:65-93`).  The first five fields are
`InitOnce.InsertChecks`'s, and only `walk` differs from it. -/
structure InsertChecksAtHead (T : Tree) (v : UInt256) (hint low : ℕ) : Prop where
  /-- `leafNumber == 0` reverts with `IMTNotInitialized` (`:71-73`). -/
  initialized : Initialized T
  /-- `_value == 0` reverts with `IMTValueZero` (`:74-76`). -/
  nonzero : v ≠ 0
  /-- `valueToIndex[_value] != 0` reverts with `IMTValueAlreadyExists` (`:77-79`). -/
  unregistered : T.valueToIndex v = 0
  /-- `_lowLeafIndex >= leafNumber` reverts with `IMTLowLeafIndexOutOfBounds` (`:80-82`). -/
  hintInBounds : hint < T.leafCount
  /-- `lowLeaf.value >= _value` reverts with `IMTLowLeafValueTooLarge` (`:84-88`). -/
  hintBelow : (T.leaf hint).value < v
  /-- The unbounded walk (`:90-93`) exits at `low`. -/
  walk : WalkSucceedsAtHead T v hint low

/-! ## Transactions at head -/

/-- One successful transaction of the tree contract at head, sent by `c`.  `initL2` is
`InitOnce.TxStep.initL2` verbatim (`L2InteropCommitmentTree.sol:44-47`,
`IndexedMerkleTree.sol:46-54`).  `insert` is the appender check (`:51-53`), the head's
checks and walk, and the same three writes at the landing index (`IndexedMerkleTree.sol:95-106`).
The leaf hook report (`:61`) only rejects calls and is not modelled. -/
inductive TxStepAtHead (K : Roles) : Tree → Caller → Call → Tree → Prop
  /-- `initL2()`: `onlyUpgrader`, then `IMT.setup`, which reverts with
  `IMTAlreadyInitialized` unless `_leafNumber == 0` (`IndexedMerkleTree.sol:47-49`). -/
  | initL2 {T : Tree} {c : Caller} :
      c = K.upgrader → T.leafCount = 0 → TxStepAtHead K T c .initL2 (setupWrites T)
  /-- `insert(v, hint)`: the appender check, the head's checks and walk, then the writes at
  the landing index. -/
  | insert {T : Tree} {c : Caller} {v : UInt256} {hint low : ℕ} :
      c = K.appender → InsertChecksAtHead T v hint low →
      TxStepAtHead K T c (.insert v hint) (insert T v low)

/-- A run of the tree contract at head (`RunOf`, from `InitOnce`). -/
abbrev TxRunAtHead (K : Roles) : (ℕ → Tree) → Trace → Prop :=
  RunOf (TxStepAtHead K)

/-! ## Relabelling a head run as a pin run -/

/-- Where the head's walk from `hint` lands: the search with `leafCount` hops, defaulting to
the hint itself if that search fails (it never does from an occupied hint of a valid tree). -/
def landingAtHead (T : Tree) (v : UInt256) (hint : ℕ) : ℕ :=
  (lowSearch T v T.leafCount hint).getD hint

/-- A call with an insert's hint replaced by the landing index of its walk on `T`.  An
`initL2()` call is unchanged. -/
def relabelCallAtHead (T : Tree) : Call → Call
  | .initL2 => .initL2
  | .insert v hint => .insert v (landingAtHead T v hint)

/-- The trace `tx` with each insert's hint replaced by its landing index at the state it runs
in.  Senders, idle steps and `initL2()` calls are unchanged. -/
def relabelAtHead (R : ℕ → Tree) (tx : Trace) : Trace :=
  fun n => (tx n).map (fun p => (p.1, relabelCallAtHead (R n) p.2))

/-- **`_nodes[0]` ALONG A HEAD RUN.**  `L n` is the stored leaf hashes at step `n` of the head
run `(R, tx)`.  It is `LevelRun` over the relabelled trace, so each insert writes
`insertLevel` at the index its walk lands on.  That is where the head's `updateLeaf` and
`pushNewLeaf` write (`IndexedMerkleTree.sol:101, 106`).  `initL2()`'s write
(`pushNewLeaf(hashLeaf({0,0,0}))`, `:52`) is the pin's `setupLevel`. -/
def LevelRunAtHead (hl : LeafHash) (R : ℕ → Tree) (tx : Trace) (L : ℕ → LeafLevel) : Prop :=
  LevelRun hl R (relabelAtHead R tx) L

/-! ## A concrete head run, for the witness -/

/-- The states of a run from deployment: the predeploy, then `chainTree k` after `initL2()`
and `k` inserts, for `k ≤ 7`, and `chainTree 7` from then on. -/
def staleHintRunAtHead (n : ℕ) : Tree :=
  if n = 0 then predeploy else chainTree (min (n - 1) 7)

/-- The trace of `staleHintRunAtHead`: the upgrader's `initL2()`; the appender's honest
`insert(k, k - 1)` for `k = 1, …, 6`, each from its own low leaf; then `insert(7, 0)`, from the
sentinel, six hops below the landing index `6`; then nothing. -/
def staleHintTxAtHead (K : Roles) : Trace := fun n =>
  if n = 0 then some (K.upgrader, .initL2)
  else if n ≤ 6 then some (K.appender, .insert ((n : ℕ) : UInt256) (n - 1))
  else if n = 7 then some (K.appender, .insert 7 0)
  else none

end Contracts.InteropCommitmentTree
