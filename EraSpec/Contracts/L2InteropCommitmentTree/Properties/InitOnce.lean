import EraSpec.Contracts.L2InteropCommitmentTree.Specs.InitOnce

/-!
# Properties: the tree is seeded once, and its history cannot be reset

Statements about `EraSpec.Contracts.L2InteropCommitmentTree.Specs.InitOnce`; proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.InitOnce`. No hash premise anywhere.

## What holds, for the deployed contract

* **One transaction at a time.** On the predeploy's zero storage, `initL2()` succeeds
  exactly when the upgrader sends it, and then writes exactly the model's `setup`
  (`InitL2OnPredeploy`). On an initialized tree it reverts whoever sends it, the
  complex upgrader included (`InitL2RevertsOnceInitialized`): `onlyUpgrader` decides who
  may call, `IMTAlreadyInitialized` makes the second call revert. `insert` reverts before
  initialization (`InsertRevertsBeforeInit`), and each entry point accepts only its role
  (`TxStepCallerIsRole`).
* **Seeded at most once.** In every run, from any start, at most one transaction is a
  successful `initL2()` (`InitL2AtMostOnce`), and none follows a state where the tree is
  initialized (`NoInitL2OnceInitialized`); in particular no run from `setup` contains one
  (`NoRunFromSetupReinitializes`).
* **Append-only, so nothing is forgotten.** Along every run, from any start and with no
  validity premise, the leaf count never decreases and an occupied index never changes
  its value (`TxRunAppendOnly`). So the key set never shrinks (`TxRunKeysMono`, which extends
  `ReachesKeysMono` to runs containing `initL2` and drops its `Valid` premise), and no
  stretch of any run projects to `ResetAndZero.resetHistory` (`ResetHistoryUnreachable`).
  "Append-only" is about values: `insert` does rewrite the low leaf's links.
* **The existing models are the runs from deployment.** A run from a valid state is a
  `Run` (`TxRunFromValidIsRun`), and every `Run` from `setup` is the tail of a run from
  the predeploy (`RunLiftsToTxRun`). A run from the predeploy stays on the predeploy
  until its one `initL2()`, which yields `setup`, and is a `Run` from there
  (`PredeployRunShape`). So each of its states is the predeploy or is reached from `setup`,
  valid, and reached from `hSetup` with the source's own `(_leafNumber, _height)`
  (`PredeployRunStates`): every `RunHeight` headline, which takes `HReaches hSetup S` as
  its only state premise, applies at every initialized state of a run from deployment.
  The security corollary holds there too (`PredeployRunReclaimableIffAbsent`).
  `GenesisRunWitness` shows the premises are met by a run with an `initL2` and two inserts.
* **The hash tree's own copy agrees.** `FullMerkle` folds its stored leaf hashes
  (`_nodes[0]`), not `leaves`. Tracking them as a ghost along the run (`LevelRun`): along
  every run from the predeploy they are exactly `leafHashes hl` of the list state
  (`StoredLeavesAreLeafHashes`), so `TreeRoot`'s `root` is the fold of the contract's own
  leaf level, and against that fold an inclusion and a non-inclusion proof of one value
  force a located break, with no hash premise (`PredeployStoredRootExclusiveOrBreak`;
  `StoredRootWitness` meets its premises at the published root). The fold being the stored
  root `_nodes[_height][0]` stays O7.

## What deleting the guard does, and does not, do

`ResetAndZero` motivates the one-time guard by a reset that erases every delivered key
(`resetHistory`). With the source's own `setup` writes, deleting the guard does something
else:

* **The exclusivity countermodel fires.** With `IMTAlreadyInitialized` deleted, a run from
  the predeploy has a second successful `initL2()` after a delivery, which leaves the
  delivered value both a key and straddled by a leaf, so it is reclaimable while present:
  `InitL2AtMostOnce` and `PredeployRunReclaimableIffAbsent` both fail, the state is not
  `Valid`, and the history projected from `setup` on is neither an `Evolution` nor a
  `GuardedEvolution` (`GuardlessReinitBreaksExclusivity`). The deployed machine has no step
  for that second call. At the hash level the second call leaves index 0's stored hash
  stale, and the fold of the stored leaf hashes accepts an honest inclusion proof and an
  honest non-inclusion proof of the delivered value, under every hash function and padding
  (`GuardlessReinitForgesAbsenceAtStoredRoot`): the delivered value is also provably absent.
* **The reset countermodel does not.** `setup` never erases a key: even without the
  guard, every run from a state whose index-0 value is zero keeps every key
  (`GuardlessRunsKeepKeys`) and never projects to `resetHistory`
  (`GuardlessResetHistoryUnreachable`). What the guard protects is the sentinel's link,
  not the key set.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract AttackVectors.ResetAndZero

/-! ## Single transactions -/

/-- **`initL2()` ON THE PREDEPLOY WRITES EXACTLY `setup`.** On the zero storage of the
genesis predeploy, a transaction `initL2()` from `c` succeeds exactly when `c` is the
upgrader, and the state it leaves is the model's `setup`. So `setup`, where `Run`,
`Reaches` and `HRun` start, is what the contract's own initialization writes. -/
def Properties.InitL2OnPredeploy : Prop :=
  ∀ (K : Roles) (c : Caller) (U : Tree),
    TxStep K predeploy c .initL2 U ↔ c = K.upgrader ∧ U = setup

/-- **THE GUARD BINDS EVERY CALLER.** On an initialized tree (`_leafNumber ≠ 0`), no
`initL2()` succeeds, whoever sends it, including the complex upgrader, the only caller
`onlyUpgrader` lets through. -/
def Properties.InitL2RevertsOnceInitialized : Prop :=
  ∀ (K : Roles) (T : Tree) (c : Caller) (U : Tree), Initialized T → ¬ TxStep K T c .initL2 U

/-- **NO INSERT BEFORE `initL2()`.** On a tree that is not initialized, no `insert(v, hint)`
succeeds, whoever sends it (`IMTNotInitialized`). -/
def Properties.InsertRevertsBeforeInit : Prop :=
  ∀ (K : Roles) (T : Tree) (c : Caller) (v : UInt256) (hint : ℕ) (U : Tree),
    ¬ Initialized T → ¬ TxStep K T c (.insert v hint) U

/-- **EACH ENTRY POINT ACCEPTS ONLY ITS ROLE.** A successful `initL2()` was sent by the
upgrader and a successful `insert` by the appender. -/
def Properties.TxStepCallerIsRole : Prop :=
  ∀ (K : Roles) (T : Tree) (c : Caller) (call : Call) (U : Tree),
    TxStep K T c call U → c = K.roleFor call

/-! ## Runs: seeded at most once -/

/-- **AT MOST ONE SUCCESSFUL `initL2()` PER RUN.** In any run, from any start state, if the
transactions at steps `m` and `n` are both successful `initL2()` calls, then `m = n`. -/
def Properties.InitL2AtMostOnce : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRun K R tx →
    ∀ (m n : ℕ) (cm cn : Caller), tx m = some (cm, .initL2) → tx n = some (cn, .initL2) →
      m = n

/-- **ONCE SEEDED, NEVER RE-SEEDED.** In any run, if the tree is initialized at step `m`,
then no transaction at any step `n ≥ m` is a successful `initL2()`, whoever its sender. -/
def Properties.NoInitL2OnceInitialized : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRun K R tx →
    ∀ m n : ℕ, m ≤ n → Initialized (R m) → ∀ c : Caller, tx n ≠ some (c, .initL2)

/-- **NO RUN FROM `setup` CONTAINS A SUCCESSFUL `initL2()`.** The call that seeded the tree
was the only one: in a run whose first state is `setup`, no step's transaction is a
successful `initL2()`. -/
def Properties.NoRunFromSetupReinitializes : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRun K R tx →
    R 0 = setup → ∀ (n : ℕ) (c : Caller), tx n ≠ some (c, .initL2)

/-! ## Runs: append-only, so nothing is forgotten -/

/-- **THE TREE IS APPEND-ONLY.** In any run, from any start state and with no validity
premise: for `m ≤ n`, the leaf count at `n` is at least that at `m`, and every index
occupied at `m` holds the same value at `n`. (Values, not leaves: `insert` rewrites the
low leaf's `nextIndex` and `nextValue`.) This is the "append-only indexed tree" of
`L2InteropCommitmentTree.sol:30`. -/
def Properties.TxRunAppendOnly : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRun K R tx →
    ∀ m n : ℕ, m ≤ n → (R m).leafCount ≤ (R n).leafCount
      ∧ ∀ i < (R m).leafCount, ((R n).leaf i).value = ((R m).leaf i).value

/-- **THE KEY SET NEVER SHRINKS.** In any run, from any start state and with no validity
premise, a value that is a key at step `m` is a key at every step `n ≥ m`. The
transactions include `initL2()`, which `ReachesKeysMono` does not cover. -/
def Properties.TxRunKeysMono : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRun K R tx →
    ∀ m n : ℕ, m ≤ n → keys (toAbs (R m)) ⊆ keys (toAbs (R n))

/-- **THE RESET HISTORY IS UNREACHABLE.** For a nonzero `a`, no stretch of any run, from
any start state, projects to `resetHistory a` (genesis, then `a` delivered, then genesis
again). Its delivery step holds `a` as a key and its reset step does not, which
`TxRunKeysMono` forbids. -/
def Properties.ResetHistoryUnreachable : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace) (a : UInt256), a ≠ 0 →
    TxRun K R tx → ∀ k : ℕ, ¬ ∀ n : ℕ, toAbs (R (k + n)) = resetHistory a n

/-! ## Runs: the existing models are the runs from deployment -/

/-- **A RUN FROM A VALID STATE IS A `Run`.** If the first state is `Valid`, every step of a
run is idle or a guarded `insert` at the searched index (`SearchYieldsGuard`); no
`initL2()` succeeds, since a valid tree is initialized. So `run_valid`,
`run_isGuardedEvolution` and the rest of `Properties/Model.lean` apply to it. -/
def Properties.TxRunFromValidIsRun : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRun K R tx →
    Valid (R 0) → Run R

/-- **NO `Run` IS LOST.** Every `Run` from `setup` is the tail of a run of the deployed
contract from the predeploy, whose first transaction is the upgrader's `initL2()` (each
insert is sent with its own low leaf as the hint). So adding `initL2()` and the callers
removes no behaviour of the existing model. -/
def Properties.RunLiftsToTxRun : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree), Run R → R 0 = setup →
    ∃ (R' : ℕ → Tree) (tx : Trace), TxRun K R' tx ∧ R' 0 = predeploy
      ∧ tx 0 = some (K.upgrader, .initL2) ∧ ∀ n : ℕ, R' (n + 1) = R n

/-- **THE SHAPE OF A RUN FROM DEPLOYMENT.** A run from the predeploy either never has a
successful transaction and stays on the predeploy, or there is a step `k` such that the
state is the predeploy up to `k`, no transaction succeeds before `k`, the transaction at
`k` is the upgrader's `initL2()`, the state after it is `setup`, and the run from `k + 1`
on is a `Run`. -/
def Properties.PredeployRunShape : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRun K R tx →
    R 0 = predeploy →
    (∀ n : ℕ, R n = predeploy ∧ tx n = none)
    ∨ ∃ k : ℕ, (∀ n ≤ k, R n = predeploy) ∧ (∀ n < k, tx n = none)
        ∧ tx k = some (K.upgrader, .initL2) ∧ R (k + 1) = setup
        ∧ Run (fun n => R (k + 1 + n))

/-- **EVERY STATE OF A RUN FROM DEPLOYMENT IS THE PREDEPLOY OR A REACHED, VALID TREE.**
Each state of a run from the predeploy is the predeploy, or it is reached from `setup` by
guarded inserts, `Valid`, and, paired with the source's own `(_leafNumber, _height)`,
reached from `hSetup`. So `ProofsExclusiveOrBreakAtOwnHeight` and the other `RunHeight`
results apply at each initialized state. -/
def Properties.PredeployRunStates : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRun K R tx →
    R 0 = predeploy →
    ∀ n : ℕ, R n = predeploy
      ∨ (Reaches setup (R n) ∧ Valid (R n)
          ∧ HReaches hSetup ⟨R n, ⟨(R n).leafCount, fmHeight (R n).leafCount⟩⟩)

/-- **THE SECURITY COROLLARY, FROM DEPLOYMENT.** At every initialized state of every run
from the predeploy, `initL2()` included, a nonzero value has a straddling leaf (is
reclaimable) exactly when it is not a key. (`Initialized` is needed: the predeploy holds
no leaf at all.) -/
def Properties.PredeployRunReclaimableIffAbsent : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRun K R tx →
    R 0 = predeploy →
    ∀ (n : ℕ) (v : UInt256), Initialized (R n) → v ≠ 0 →
      ((∃ W ∈ toAbs (R n), W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ↔ v ∉ keys (toAbs (R n)))

/-! ## Anti-vacuity -/

/-- **THE PREMISES ARE MET BY A RUN WITH AN `initL2()` AND INSERTS.** The two deployed role
addresses differ. For any roles and `0 < a < b`, `genesisRun a b` with trace
`genesisTx K a b` is a run from the predeploy whose transactions are the upgrader's
`initL2()` (step 0) and the appender's `insert(a, 0)` and `insert(b, 1)` (steps 1, 2); its
state at step 0 is not initialized, those from step 1 on are, step 1 is `setup`, step 3 is
`threeLeafTree a b`, and `a` and `b` are keys at step 3. Its tail from step 1 is a run from
a valid state and a `Run` from `setup`. And the upgrader's second `initL2()`, at step 1,
has no step: `InitL2RevertsOnceInitialized` fires. -/
def Properties.GenesisRunWitness : Prop :=
  deployedRoles.upgrader ≠ deployedRoles.appender ∧
  ∀ (K : Roles) (a b : UInt256), 0 < a → a < b →
    TxRun K (genesisRun a b) (genesisTx K a b) ∧ genesisRun a b 0 = predeploy
      ∧ genesisTx K a b 0 = some (K.upgrader, .initL2)
      ∧ genesisTx K a b 1 = some (K.appender, .insert a 0)
      ∧ genesisTx K a b 2 = some (K.appender, .insert b 1)
      ∧ ¬ Initialized (genesisRun a b 0)
      ∧ genesisRun a b 1 = setup ∧ Initialized (genesisRun a b 1)
      ∧ genesisRun a b 3 = threeLeafTree a b ∧ Initialized (genesisRun a b 3)
      ∧ a ∈ keys (toAbs (genesisRun a b 3)) ∧ b ∈ keys (toAbs (genesisRun a b 3))
      ∧ TxRun K (fun n => genesisRun a b (n + 1)) (fun n => genesisTx K a b (n + 1))
      ∧ Valid (genesisRun a b 1) ∧ Run (fun n => genesisRun a b (n + 1))
      ∧ ¬ (∃ U : Tree, TxStep K (genesisRun a b 1) K.upgrader .initL2 U)

/-! ## The guard deleted -/

/-- **WITHOUT `IMTAlreadyInitialized`, A SECOND `initL2()` SUCCEEDS AND MAKES A DELIVERED
VALUE RECLAIMABLE.** For any roles and nonzero `a`, on the guardless machine, from the
predeploy: the upgrader's `initL2()` yields `setup`, the appender's `insert(a, 0)` delivers
`a`, and then the upgrader's `initL2()` succeeds again, so the run has two successful
`initL2()` calls (steps 0 and 2; `InitL2AtMostOnce` fails). The deployed machine has no
step for that second call. After it the tree is initialized with three leaves: the sentinel
reset to `{0,0,0}`, the delivered leaf `{a,0,0}` unchanged, and a new zero leaf at index 2
(the one `pushNewLeaf(zeroLeafHash)` commits). `a` is still a key and still registered, so
the dedup gate still refuses it, but the zero leaves straddle it: `a` is reclaimable while
present, so the conclusion of `PredeployRunReclaimableIffAbsent` fails at step 3, whose
premises this run meets apart from the guard. The state is not `Valid`, and the history
projected from `setup` on is neither an `Evolution` nor a `GuardedEvolution`. The run's
first state has index-0 value zero, so it also meets the premises of
`GuardlessRunsKeepKeys`. -/
def Properties.GuardlessReinitBreaksExclusivity : Prop :=
  ∀ (K : Roles) (a : UInt256), a ≠ 0 →
    TxRunNoGuard K (reinitRun a) (reinitTx K a) ∧ reinitRun a 0 = predeploy
      ∧ ((reinitRun a 0).leaf 0).value = 0
      ∧ reinitTx K a 0 = some (K.upgrader, .initL2)
      ∧ reinitTx K a 1 = some (K.appender, .insert a 0)
      ∧ reinitTx K a 2 = some (K.upgrader, .initL2)
      ∧ reinitRun a 1 = setup ∧ reinitRun a 2 = insert setup a 0
      ∧ ¬ (∃ U : Tree, TxStep K (reinitRun a 2) K.upgrader .initL2 U)
      ∧ Initialized (reinitRun a 3) ∧ (reinitRun a 3).leafCount = 3
      ∧ (reinitRun a 3).leaf 0 = ⟨0, 0, 0⟩ ∧ (reinitRun a 3).leaf 1 = ⟨a, 0, 0⟩
      ∧ (reinitRun a 3).leaf 2 = ⟨0, 0, 0⟩
      ∧ (reinitRun a 3).valueToIndex a = 1
      ∧ a ∈ keys (toAbs (reinitRun a 3))
      ∧ (∃ W ∈ toAbs (reinitRun a 3), W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey))
      ∧ ¬ ((∃ W ∈ toAbs (reinitRun a 3), W.key < a ∧ (W.nextKey = 0 ∨ a < W.nextKey))
            ↔ a ∉ keys (toAbs (reinitRun a 3)))
      ∧ ¬ Valid (reinitRun a 3)
      ∧ ¬ Evolution (fun n => toAbs (reinitRun a (n + 1)))
      ∧ ¬ GuardedEvolution (fun n => toAbs (reinitRun a (n + 1)))

/-- **BUT EVEN WITHOUT THE GUARD, NO KEY IS EVER ERASED.** On the guardless machine, in any
run whose first state has value zero at index 0 (the predeploy, `setup`, and every valid
tree do), the key set never shrinks. `setup` overwrites only `leaves[0]`, whose value stays
zero, and never touches another leaf. -/
def Properties.GuardlessRunsKeepKeys : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRunNoGuard K R tx →
    ((R 0).leaf 0).value = 0 →
    ∀ m n : ℕ, m ≤ n → keys (toAbs (R m)) ⊆ keys (toAbs (R n))

/-- **SO THE RESET HISTORY IS UNREACHABLE WITH OR WITHOUT THE GUARD.** On the guardless
machine, for nonzero `a`, no stretch of any run whose first state has value zero at index
0 projects to `resetHistory a`. The `ResetAndZero` reset (keys erased) is not what a
second `setup` would do; `GuardlessReinitBreaksExclusivity` is. -/
def Properties.GuardlessResetHistoryUnreachable : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace) (a : UInt256), a ≠ 0 →
    TxRunNoGuard K R tx → ((R 0).leaf 0).value = 0 →
    ∀ k : ℕ, ¬ ∀ n : ℕ, toAbs (R (k + n)) = resetHistory a n

/-! ## The hash tree's leaf level

`TreeRoot`'s `root` folds `leafHashes hl T`, the hashes of the list state's leaves; the
contract folds its own stored copy, `_nodes[0]`. These results track that copy along a
run (`LevelRun`). The fold of `_nodes[0]` being the stored root is O7, as elsewhere. -/

/-- **ALONG A RUN FROM DEPLOYMENT, THE STORED LEAF HASHES ARE THE LIST STATE'S.** For any
leaf hash `hl`, at every step of every run from the predeploy, whatever `_nodes[0]` held
before `initL2()`, the stored hashes of the occupied indices are `leafHashes hl` of the list
state. So `TreeRoot`'s `root h z0 hl (R n) height` is the fold of the contract's own leaf
level, and every `TreeRoot` and `RunHeight` statement about it is about that fold. -/
def Properties.StoredLeavesAreLeafHashes : Prop :=
  ∀ (K : Roles) (hl : LeafHash) (R : ℕ → Tree) (tx : Trace) (L : ℕ → LeafLevel),
    TxRun K R tx → LevelRun hl R tx L → R 0 = predeploy →
    ∀ n : ℕ, storedLeaves (L n) (R n).leafCount = leafHashes hl (R n)

/-- **EXCLUSIVITY OR A LOCATED BREAK, AT THE STORED ROOT, FROM DEPLOYMENT.** For any node
hash `h`, padding `z0` and leaf hash `hl`, at every initialized step of every run from the
predeploy, and against the fold of the stored leaf hashes at any height: if a value has
both an accepted inclusion proof and an accepted non-inclusion proof, one of the two
submitted paths carries a located `TreeRootBreak` (on the list state). No hash premise. -/
def Properties.PredeployStoredRootExclusiveOrBreak : Prop :=
  ∀ (K : Roles) (h : MerkleSpec.Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree)
    (tx : Trace) (L : ℕ → LeafLevel),
    TxRun K R tx → LevelRun hl R tx L → R 0 = predeploy →
    ∀ (n height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256)
      (k₁ k₂ : ℕ), Initialized (R n) →
      InclusionAccepted h hl
        (MerkleSpec.rootOf h z0 (storedLeaves (L n) (R n).leafCount) height) v ℓ₁ i₁ s₁ k₁ →
      NonInclusionAccepted h hl
        (MerkleSpec.rootOf h z0 (storedLeaves (L n) (R n).leafCount) height) v ℓ₂ i₂ s₂ k₂ →
      TreeRootBreak h z0 hl (R n) height s₁ k₁ i₁ ℓ₁
        ∨ TreeRootBreak h z0 hl (R n) height s₂ k₂ i₂ ℓ₂

/-- **THE PREMISES ARE MET, AT THE PUBLISHED ROOT.** For any roles, node hash, leaf hash and
`0 < a < b`, `genesisLevel hl a b` is `_nodes[0]` along `genesisRun a b`; at step 3 it holds
the hashes of `threeLeafTree a b`'s leaves `{0,1,a}`, `{a,2,b}`, `{b,0,0}`, and the source's
`_height` is 2. Against its fold at that height with the pinned padding `hl {0,0,0}`, `a`
has an accepted honest inclusion proof (index 1) and an accepted non-inclusion proof (the
empty slot 3: the existing padding forgery, `PaddingForgeryAtOwnHeight`). So the premises of
`PredeployStoredRootExclusiveOrBreak` hold at step 3 of a run from the predeploy, at the
root the source publishes. Its conclusion is met by the second disjunct only: the honest
inclusion path carries no located break, the forged absence path carries the padding hit. -/
def Properties.StoredRootWitness : Prop :=
  ∀ (K : Roles) (h : MerkleSpec.Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    LevelRun hl (genesisRun a b) (genesisTx K a b) (genesisLevel hl a b)
      ∧ storedLeaves (genesisLevel hl a b 3) (genesisRun a b 3).leafCount
          = [hl ⟨0, 1, a⟩, hl ⟨a, 2, b⟩, hl ⟨b, 0, 0⟩]
      ∧ fmHeight (genesisRun a b 3).leafCount = 2
      ∧ InclusionAccepted h hl
          (MerkleSpec.rootOf h (hl ⟨0, 0, 0⟩) (storedLeaves (genesisLevel hl a b 3) 3) 2) a
          ⟨a, 2, b⟩ 1
          (MerkleSpec.Verifier.honestSibs h (hl ⟨0, 0, 0⟩)
            (storedLeaves (genesisLevel hl a b 3) 3) 1) 2
      ∧ NonInclusionAccepted h hl
          (MerkleSpec.rootOf h (hl ⟨0, 0, 0⟩) (storedLeaves (genesisLevel hl a b 3) 3) 2) a
          ⟨0, 0, 0⟩ 3
          (MerkleSpec.Verifier.honestSibs h (hl ⟨0, 0, 0⟩)
            (storedLeaves (genesisLevel hl a b 3) 3) 3) 2
      ∧ ¬ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (genesisRun a b 3) 2
          (MerkleSpec.Verifier.honestSibs h (hl ⟨0, 0, 0⟩)
            (storedLeaves (genesisLevel hl a b 3) 3) 1) 2 1 ⟨a, 2, b⟩
      ∧ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (genesisRun a b 3) 2
          (MerkleSpec.Verifier.honestSibs h (hl ⟨0, 0, 0⟩)
            (storedLeaves (genesisLevel hl a b 3) 3) 3) 2 3 ⟨0, 0, 0⟩

/-- **WITHOUT THE GUARD, THE STORED ROOT ACCEPTS BOTH PROOFS FOR A DELIVERED VALUE, UNDER
EVERY HASH.** For any roles, node hash `h`, padding `z0`, leaf hash `hl` and nonzero `a`:
`reinitLevel hl a` is `_nodes[0]` along the guardless run `reinitRun a`. After the second
`initL2()` the stored leaf hashes are those of `{0,1,a}` (index 0 keeps the sentinel's
pre-reset hash), `{a,0,0}` and `{0,0,0}`, while the list state's are those of `{0,0,0}`,
`{a,0,0}`, `{0,0,0}`: the two copies disagree at index 0 unless `hl` collides there. The
source's `_height` is 2. Against the fold of the stored leaf hashes at height 2, `a` has an
accepted inclusion proof (index 1) and an accepted non-inclusion proof (the occupied zero
leaf at index 2), both on the honest paths of the stored tree: no forged sibling and no
collision, for every `h`, `z0` and `hl`. On the deployed machine the same pair forces a
located break (`PredeployStoredRootExclusiveOrBreak`).

(Re-running `FullMerkle.setup` also pushes a stray entry onto `_zeros` and `_nodes`
(`FullMerkle.sol:31-32`), which this fold does not see; it is read only once `_height`
reaches 3.) -/
def Properties.GuardlessReinitForgesAbsenceAtStoredRoot : Prop :=
  ∀ (K : Roles) (h : MerkleSpec.Hash) (z0 : UInt256) (hl : LeafHash) (a : UInt256), a ≠ 0 →
    LevelRun hl (reinitRun a) (reinitTx K a) (reinitLevel hl a)
      ∧ storedLeaves (reinitLevel hl a 3) (reinitRun a 3).leafCount
          = [hl ⟨0, 1, a⟩, hl ⟨a, 0, 0⟩, hl ⟨0, 0, 0⟩]
      ∧ leafHashes hl (reinitRun a 3) = [hl ⟨0, 0, 0⟩, hl ⟨a, 0, 0⟩, hl ⟨0, 0, 0⟩]
      ∧ fmHeight (reinitRun a 3).leafCount = 2
      ∧ InclusionAccepted h hl
          (MerkleSpec.rootOf h z0 (storedLeaves (reinitLevel hl a 3) 3) 2) a ⟨a, 0, 0⟩ 1
          (MerkleSpec.Verifier.honestSibs h z0 (storedLeaves (reinitLevel hl a 3) 3) 1) 2
      ∧ NonInclusionAccepted h hl
          (MerkleSpec.rootOf h z0 (storedLeaves (reinitLevel hl a 3) 3) 2) a ⟨0, 0, 0⟩ 2
          (MerkleSpec.Verifier.honestSibs h z0 (storedLeaves (reinitLevel hl a 3) 3) 2) 2

end Contracts.InteropCommitmentTree
