import EraSpec.Contracts.L2InteropCommitmentTree.Specs.HintSearchAtHead
import EraSpec.Core.Headline

/-!
# Properties: the head's unbounded walk, against the pin's five-hop search

Statements about `EraSpec.Contracts.L2InteropCommitmentTree.Specs.HintSearchAtHead`
(`main` `70096e2` and `draft/v0.35.0` `b17415d`; the cited files are unchanged since `3605e82`
and `d9f6789`).  Proofs in `EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearchAtHead`.
No hash premise anywhere.  Gas is not modelled (see the spec): "passes the checks" below
means the code's checks, and a walk that exits can still run out of gas.

## What removing the bound changes, and what it does not

* **Where a value goes is unchanged.**  On a valid tree the walk lands where the guarded
  insert of the rest of the theory puts the value (`InsertChecksAtHeadYieldGuard`).  That
  index does not depend on the hint (`InsertAtHeadLandingHintIndependent`), and the walk is
  the search with `leafCount` hops (`WalkAtHeadIsLeafCountSearch`).  So on a valid tree every
  head insert passes the pin's checks when sent with its own landing index as the hint, and
  every pin insert is a head insert (`InsertChecksAtHeadVsPin`).
* **Which hints pass changes.**  At head an insert passes every check of the engine from every
  hint that its two hint checks admit, an occupied index whose value is below `v`
  (`InsertAtHeadEnabledIff`).  At the pin the hint also had to be within five hops of the
  landing index.  The pin's liveness caveat `HonestInsertRevertsAtDeployedFuel` has no
  counterpart in the head's checks: the same honest insert passes them
  (`HonestInsertSucceedsAtHead`).
* **The pin's results about runs from the predeploy apply to relabelled head runs.**  A head
  run from the predeploy, with each insert's hint replaced by its landing index, is a pin run
  with the same states (`TxRunAtHeadIsRelabelledTxRun`).  Relabelling keeps idle steps,
  senders, `initL2()` calls and inserted values (`RelabelAtHeadKeepsShape`).  So
  `PredeployRunStates`, `PredeployRunReclaimableIffAbsent`, `StoredLeavesAreLeafHashes` and
  `PredeployStoredRootExclusiveOrBreak` hold for head runs (the `…AtHead` forms below, whose
  statements are about states and the head run's own ghost `LevelRunAtHead`).
* **Results about runs from any start are re-proved directly** (`InitL2AtMostOnceAtHead`,
  `TxRunAtHeadAppendOnly`, `TxRunAtHeadKeysMono`, `TxRunAtHeadFromValidIsRun`), since
  relabelling needs every state to be the predeploy or valid.
* **The head admits strictly more runs.**  Every pin run is a head run
  (`PinTxRunIsTxRunAtHead`).  `StaleHintRunWitnessAtHead` is a head run from the predeploy
  with an insert six hops from its landing index.  It is not a pin run, and its relabelling
  is.

## Witnesses

`HonestInsertSucceedsAtHead` and `InsertAtHeadWitness` meet the premises of the walk and
insert results on the reached tree `chainTree 6`, with two different hints landing at one
index and a head step that is no pin step.  `StaleHintRunWitnessAtHead` meets the premises
of the results about runs from the predeploy, and `StaleHintRunFromValidWitnessAtHead` those
about runs from a valid state, each on a run with the stale-hint insert.
`StaleHintStoredRootWitnessAtHead` meets the premises of the two `_nodes[0]` results on that
run (`LevelRunAtHeadExists` gives every head run its ghost).
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## The walk -/

/-- **THE WALK IS THE SEARCH WITH `leafCount` HOPS.**  On a valid tree, from an occupied
hint, the head's walk lands at `low` exactly when `lowSearch` with `leafCount` hops returns
`low`.  So the walk's result is that of any number of hops that lets it exit. -/
def Properties.WalkAtHeadIsLeafCountSearch : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint low : ℕ), hint < T.leafCount →
    (WalkExitsAtV35 T v hint low ↔ lowSearch T v T.leafCount hint = some low)

/-- **THE WALK ALWAYS EXITS.**  On a valid tree, from every occupied hint and for every value,
the head's loop exits after finitely many hops (`LowSearchTerminates`). -/
def Properties.WalkAtHeadTerminates : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint : ℕ), hint < T.leafCount →
    ∃ low, WalkExitsAtV35 T v hint low

/-- **THE WALK IS DETERMINISTIC.**  On any tree, two exits of the walk from one hint are at
one index. -/
def Properties.WalkAtHeadDeterministic : Prop :=
  ∀ (T : Tree) (v : UInt256) (hint low low' : ℕ),
    WalkExitsAtV35 T v hint low → WalkExitsAtV35 T v hint low' → low = low'

/-! ## The insert -/

/-- **A SUCCESSFUL HEAD INSERT IS THE GUARDED INSERT AT ITS LANDING INDEX.**  On a valid tree,
the head's checks and walk establish `InsertGuard` at the landing index, so the head's insert
is the guarded `insert` of `Specs/Model.lean` (`SearchYieldsGuard`, for the walk). -/
def Properties.InsertChecksAtHeadYieldGuard : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint low : ℕ),
    InsertChecksAtV35 T v hint low → InsertGuard T v low

/-- **THE HINT DOES NOT CHOOSE WHERE THE VALUE GOES.**  On a valid tree, two successful head
inserts of one value, from any two hints, land at one index: the leaf whose window straddles
the value.  So the state after an insert does not depend on its hint. -/
def Properties.InsertAtHeadLandingHintIndependent : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint hint' low low' : ℕ),
    InsertChecksAtV35 T v hint low → InsertChecksAtV35 T v hint' low' → low = low'

/-- **AT HEAD, AN INSERT PASSES THE ENGINE'S CHECKS FROM EVERY ADMISSIBLE HINT.**  On a valid
tree, some landing index makes `insert(v, hint)` pass every check of `InsertChecksAtV35`
exactly when the tree is initialized, `v` is nonzero and unregistered, and the hint is an
occupied index whose value is below `v`.  These are the checks of
`IndexedMerkleTree.sol:71-88`: the walk adds no check that can fail.  Gas, the tree's appender
check and its leaf report are not part of `InsertChecksAtV35`. -/
@[headline] def Properties.InsertAtHeadEnabledIff : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint : ℕ),
    (∃ low, InsertChecksAtV35 T v hint low)
      ↔ Initialized T ∧ v ≠ 0 ∧ T.valueToIndex v = 0 ∧ hint < T.leafCount
        ∧ (T.leaf hint).value < v

/-- **PIN INSERTS ARE HEAD INSERTS, AND HEAD INSERTS ARE PIN INSERTS FROM THEIR LANDING
INDEX.**  On a valid tree: every insert the pin's five-hop search accepts, the head accepts,
at the same index; and every head insert passes the pin's checks when its landing index is
sent as the hint, since the walk then makes no hop. -/
def Properties.InsertChecksAtHeadVsPin : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint low : ℕ),
    (InsertChecks T v hint low → InsertChecksAtV35 T v hint low)
      ∧ (InsertChecksAtV35 T v hint low → InsertChecks T v low low)

/-- **THE PIN'S HONEST REVERT PASSES THE HEAD'S CHECKS.**  The instance of
`HonestInsertRevertsAtDeployedFuel`: on the honest seven-leaf tree `chainTree 6`, reached from
`setup`, inserting `7` from hint `0` passes the pin's checks for no landing index (the
five-hop search runs out), and passes the head's checks, landing at index `6` after six hops. -/
def Properties.HonestInsertSucceedsAtHead : Prop :=
  Reaches setup (chainTree 6)
    ∧ (∀ low, ¬ InsertChecks (chainTree 6) 7 0 low)
    ∧ InsertChecksAtV35 (chainTree 6) 7 0 6

/-- **THE INSERT RESULTS' PREMISES, WITH TWO HINTS.**  On the valid tree `chainTree 6`, for any
roles: inserting `7` passes the head's checks from hint `0` (six hops) and from hint `3`
(three hops), both landing at index `6`; it passes the pin's checks from hint `3`; and the
appender's `insert(7, 0)` is a head transaction to `chainTree 7` that is no pin transaction.
So the premises of `InsertAtHeadLandingHintIndependent` hold with two different hints, those
of both halves of `InsertChecksAtHeadVsPin` hold, and so do those of
`TxStepAtHeadIsRelabelledTxStep` on a step outside the pin's model. -/
@[witness] def Properties.InsertAtHeadWitness : Prop :=
  ∀ K : Roles,
    Valid (chainTree 6)
      ∧ InsertChecksAtV35 (chainTree 6) 7 0 6 ∧ InsertChecksAtV35 (chainTree 6) 7 3 6
      ∧ InsertChecks (chainTree 6) 7 3 6
      ∧ TxStepAtHead K (chainTree 6) K.appender (.insert 7 0) (chainTree 7)
      ∧ ¬ TxStep K (chainTree 6) K.appender (.insert 7 0) (chainTree 7)

/-! ## Transactions and runs -/

/-- **EVERY PIN TRANSACTION IS A HEAD TRANSACTION.** -/
def Properties.PinTxStepIsTxStepAtHead : Prop :=
  ∀ (K : Roles) (T : Tree) (c : Caller) (call : Call) (U : Tree),
    TxStep K T c call U → TxStepAtHead K T c call U

/-- **EVERY PIN RUN IS A HEAD RUN**, with the same states and trace.  So the head results
below about all runs cover every pin run. -/
def Properties.PinTxRunIsTxRunAtHead : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRun K R tx → TxRunAtHead K R tx

/-- **ON A VALID TREE, A HEAD TRANSACTION IS A PIN TRANSACTION WITH ITS HINT RELABELLED.**
Same sender, same state after; the insert's hint becomes its landing index. -/
def Properties.TxStepAtHeadIsRelabelledTxStep : Prop :=
  ∀ (K : Roles) (T : Tree) (c : Caller) (call : Call) (U : Tree), Valid T →
    TxStepAtHead K T c call U → TxStep K T c (relabelCallAtHead T call) U

/-- **RELABELLING CHANGES ONLY INSERT HINTS.**  At every step, the relabelled trace is idle
exactly when the original is.  It has an `initL2()` call by `c` exactly when the original
does.  For an insert of `v` by `c`, it has an insert of `v` by `c` with the landing index as
the hint. -/
def Properties.RelabelAtHeadKeepsShape : Prop :=
  ∀ (R : ℕ → Tree) (tx : Trace) (n : ℕ),
    (relabelAtHead R tx n = none ↔ tx n = none)
      ∧ (∀ c : Caller, relabelAtHead R tx n = some (c, .initL2) ↔ tx n = some (c, .initL2))
      ∧ ∀ (c : Caller) (v : UInt256) (hint : ℕ), tx n = some (c, .insert v hint) →
          relabelAtHead R tx n = some (c, .insert v (landingAtHead (R n) v hint))

/-- **A HEAD RUN FROM THE PREDEPLOY IS A PIN RUN, RELABELLED.**  For every head run from the
all-zero storage `predeploy`, the same states with the relabelled trace form a run of the
pin's `TxStep`.  So every `InitOnce` result about runs from the predeploy applies to the
head run's states, with the relabelled trace in place of the head's. -/
def Properties.TxRunAtHeadIsRelabelledTxRun : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRunAtHead K R tx → R 0 = predeploy →
    TxRun K R (relabelAtHead R tx)

/-! ## `InitOnce`, restated at head: runs from any start -/

/-- **AT MOST ONE SUCCESSFUL `initL2()` PER HEAD RUN.**  `InitL2AtMostOnce`, for head runs
from any start state. -/
def Properties.InitL2AtMostOnceAtHead : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRunAtHead K R tx →
    ∀ (m n : ℕ) (cm cn : Caller), tx m = some (cm, .initL2) → tx n = some (cn, .initL2) →
      m = n

/-- **THE TREE IS APPEND-ONLY AT HEAD.**  `TxRunAppendOnly`, for head runs from any start
state and with no validity premise. -/
def Properties.TxRunAtHeadAppendOnly : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRunAtHead K R tx →
    ∀ m n : ℕ, m ≤ n → (R m).leafCount ≤ (R n).leafCount
      ∧ ∀ i < (R m).leafCount, ((R n).leaf i).value = ((R m).leaf i).value

/-- **THE KEY SET NEVER SHRINKS AT HEAD.**  `TxRunKeysMono`, for head runs from any start. -/
def Properties.TxRunAtHeadKeysMono : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRunAtHead K R tx →
    ∀ m n : ℕ, m ≤ n → keys (toAbs (R m)) ⊆ keys (toAbs (R n))

/-- **A HEAD RUN FROM A VALID STATE IS A `Run`.**  `TxRunFromValidIsRun` at head: each step is
idle or a guarded insert at the landing index. -/
def Properties.TxRunAtHeadFromValidIsRun : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRunAtHead K R tx → Valid (R 0) → Run R

/-! ## `InitOnce`, restated at head: runs from the predeploy -/

/-- **EVERY STATE OF A HEAD RUN FROM DEPLOYMENT IS THE PREDEPLOY OR A REACHED, VALID TREE.**
`PredeployRunStates` at head, so the `RunHeight` results apply at each initialized state. -/
def Properties.PredeployRunStatesAtHead : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRunAtHead K R tx →
    R 0 = predeploy →
    ∀ n : ℕ, R n = predeploy
      ∨ (Reaches setup (R n) ∧ Valid (R n)
          ∧ HReaches hSetup ⟨R n, ⟨(R n).leafCount, fmHeight (R n).leafCount⟩⟩)

/-- **THE SECURITY COROLLARY AT HEAD.**  `PredeployRunReclaimableIffAbsent`: at every
initialized state of a head run from the predeploy, a nonzero value is straddled by a leaf
exactly when it is not a key.  As at the pin, the straddling leaf is a genuine leaf of
`toAbs (R n)`; what the deployed `verifyNonInclusion` accepts is not part of this
statement. -/
def Properties.PredeployRunReclaimableIffAbsentAtHead : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRunAtHead K R tx →
    R 0 = predeploy →
    ∀ (n : ℕ) (v : UInt256), Initialized (R n) → v ≠ 0 →
      ((∃ W ∈ toAbs (R n), W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ↔ v ∉ keys (toAbs (R n)))

/-- **THE STORED LEAF HASHES ARE THE LIST STATE'S, AT HEAD.**  `StoredLeavesAreLeafHashes`,
with `_nodes[0]` written at each insert's landing index (`LevelRunAtHead`): for any leaf hash
`hl`, at every step of every head run from the predeploy, whatever `_nodes[0]` held before
`initL2()`, the stored hashes of the occupied indices are `leafHashes hl` of the list
state. -/
def Properties.StoredLeavesAreLeafHashesAtHead : Prop :=
  ∀ (K : Roles) (hl : LeafHash) (R : ℕ → Tree) (tx : Trace) (L : ℕ → LeafLevel),
    TxRunAtHead K R tx → LevelRunAtHead hl R tx L → R 0 = predeploy →
    ∀ n : ℕ, storedLeaves (L n) (R n).leafCount = leafHashes hl (R n)

/-- **EXCLUSIVITY OR A LOCATED BREAK AT THE STORED LEAF FOLD, AT HEAD.**
`PredeployStoredRootExclusiveOrBreak` for head runs.  For any node hash `h`, padding `z0` (so
in particular the head's `IMT_EMPTY_LEAF_HASH`) and leaf hash `hl`, at every initialized step
of every head run from the predeploy, and against the fold of the stored leaf hashes at any
height: if a value has both an accepted inclusion proof and an accepted non-inclusion proof,
one of the two submitted paths carries a located `TreeRootBreak` (on the list state).  No
hash premise.  As at the pin, that this fold is the stored root `_nodes[_height][0]` is not
part of the statement: `CachedRoot` shows it for the pin's runs of the transcribed
`FullMerkle.sol` (unchanged since the pin), and compiled code stays O7. -/
def Properties.PredeployStoredRootExclusiveOrBreakAtHead : Prop :=
  ∀ (K : Roles) (h : MerkleSpec.Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree)
    (tx : Trace) (L : ℕ → LeafLevel),
    TxRunAtHead K R tx → LevelRunAtHead hl R tx L → R 0 = predeploy →
    ∀ (n height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256)
      (k₁ k₂ : ℕ), Initialized (R n) →
      InclusionAccepted h hl
        (MerkleSpec.rootOf h z0 (storedLeaves (L n) (R n).leafCount) height) v ℓ₁ i₁ s₁ k₁ →
      NonInclusionAccepted h hl
        (MerkleSpec.rootOf h z0 (storedLeaves (L n) (R n).leafCount) height) v ℓ₂ i₂ s₂ k₂ →
      TreeRootBreak h z0 hl (R n) height s₁ k₁ i₁ ℓ₁
        ∨ TreeRootBreak h z0 hl (R n) height s₂ k₂ i₂ ℓ₂

/-! ## Anti-vacuity: a head run the pin does not have -/

/-- **A HEAD RUN FROM DEPLOYMENT WITH A STALE HINT.**  For any roles, `staleHintRunAtHead`
with trace `staleHintTxAtHead K` is a head run from the predeploy: the upgrader's `initL2()`,
six honest inserts, then `insert(7, 0)`, whose walk makes six hops.  It reaches
`chainTree 7`.  It is not a pin run, since the pin reverts that last insert.  Its relabelling
is a pin run: the stale hint becomes the landing index `6`.  So the run premises of the
results above about head runs from the predeploy (for the `_nodes[0]` ghost see
`StaleHintStoredRootWitnessAtHead`) are met by a run outside the pin's model, and its state
at step 7 is initialized (`StaleHintStoredRootWitnessAtHead`). -/
@[witness] def Properties.StaleHintRunWitnessAtHead : Prop :=
  ∀ K : Roles,
    TxRunAtHead K staleHintRunAtHead (staleHintTxAtHead K)
      ∧ staleHintRunAtHead 0 = predeploy
      ∧ staleHintRunAtHead 8 = chainTree 7
      ∧ staleHintTxAtHead K 7 = some (K.appender, .insert 7 0)
      ∧ ¬ TxRun K staleHintRunAtHead (staleHintTxAtHead K)
      ∧ TxRun K staleHintRunAtHead (relabelAtHead staleHintRunAtHead (staleHintTxAtHead K))
      ∧ relabelAtHead staleHintRunAtHead (staleHintTxAtHead K) 7
          = some (K.appender, .insert 7 6)

/-- **THE SAME, FROM A VALID STATE.**  For any roles, the stale-hint run from step 1 on is a
head run whose first state, `setup`, is valid, and it still contains the stale insert
`insert(7, 0)` (at its step 6).  It is not a pin run.  So the premises of
`TxRunAtHeadFromValidIsRun` (and of the results about runs from any start) are met by a run
outside the pin's model. -/
def Properties.StaleHintRunFromValidWitnessAtHead : Prop :=
  ∀ K : Roles,
    TxRunAtHead K (fun n => staleHintRunAtHead (n + 1)) (fun n => staleHintTxAtHead K (n + 1))
      ∧ Valid (staleHintRunAtHead 1)
      ∧ staleHintTxAtHead K (6 + 1) = some (K.appender, .insert 7 0)
      ∧ ¬ TxRun K (fun n => staleHintRunAtHead (n + 1)) (fun n => staleHintTxAtHead K (n + 1))

/-- **EVERY HEAD RUN HAS ITS `_nodes[0]` GHOST.**  For any leaf hash, run and initial array,
`levelAlongAtHead` is a `LevelRunAtHead` ghost of the run that starts from that array.  So
the `LevelRunAtHead` premise of the two results above never restricts the run. -/
def Properties.LevelRunAtHeadExists : Prop :=
  ∀ (hl : LeafHash) (R : ℕ → Tree) (tx : Trace) (L0 : LeafLevel),
    LevelRunAtHead hl R tx (levelAlongAtHead hl R tx L0) ∧ levelAlongAtHead hl R tx L0 0 = L0

/-- **THE `_nodes[0]` RESULTS' PREMISES, ON THE STALE-HINT RUN.**  For any roles, node hash `h`
and leaf hash `hl`: `staleHintLevelAtHead hl K` is a `_nodes[0]` ghost of the stale-hint run.
At step 7 the state is `chainTree 6`, initialized, with seven leaves at the source's
`_height` 3, and the stored leaf hashes are its leaf hashes.  Against their fold at height 3
with the padding `hl {0,0,0}` (the pin's padding; at head `setup` pads with
`IMT_EMPTY_LEAF_HASH`), the key `1` has an accepted honest inclusion proof (index 1) and an
accepted non-inclusion proof (the sentinel `{0,0,0}` at the empty slot 7).  So the premises
of `StoredLeavesAreLeafHashesAtHead` and `PredeployStoredRootExclusiveOrBreakAtHead` hold on a
run that is not a pin run.  The conclusion of the latter is met by the second disjunct only:
the honest inclusion path carries no located break, and the forged absence path carries the
padding hit.

Step 7 is chosen because `chainTree 6` has an empty slot at height 3 for the absence proof. It
is the state before the stale-hint insert (trace index 7), so it is one the pin also reaches;
the ghost after that insert, where the relabelled write lands at the landing index, is
`StaleHintStoredLeavesAfterInsertAtHead` in the Proofs file. The padding is the pin's
`hl {0,0,0}`, not a head-like `z0`; `PredeployStoredRootExclusiveOrBreakAtHead` holds for every `z0`. -/
def Properties.StaleHintStoredRootWitnessAtHead : Prop :=
  ∀ (K : Roles) (h : MerkleSpec.Hash) (hl : LeafHash),
    LevelRunAtHead hl staleHintRunAtHead (staleHintTxAtHead K) (staleHintLevelAtHead hl K)
      ∧ staleHintRunAtHead 7 = chainTree 6 ∧ Initialized (staleHintRunAtHead 7)
      ∧ (staleHintRunAtHead 7).leafCount = 7
      ∧ fmHeight (staleHintRunAtHead 7).leafCount = 3
      ∧ storedLeaves (staleHintLevelAtHead hl K 7) 7 = leafHashes hl (chainTree 6)
      ∧ InclusionAccepted h hl
          (MerkleSpec.rootOf h (hl ⟨0, 0, 0⟩) (storedLeaves (staleHintLevelAtHead hl K 7) 7) 3)
          1 ⟨1, 2, 2⟩ 1
          (MerkleSpec.Verifier.honestSibs h (hl ⟨0, 0, 0⟩)
            (storedLeaves (staleHintLevelAtHead hl K 7) 7) 1) 3
      ∧ NonInclusionAccepted h hl
          (MerkleSpec.rootOf h (hl ⟨0, 0, 0⟩) (storedLeaves (staleHintLevelAtHead hl K 7) 7) 3)
          1 ⟨0, 0, 0⟩ 7
          (MerkleSpec.Verifier.honestSibs h (hl ⟨0, 0, 0⟩)
            (storedLeaves (staleHintLevelAtHead hl K 7) 7) 7) 3
      ∧ ¬ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3
          (MerkleSpec.Verifier.honestSibs h (hl ⟨0, 0, 0⟩)
            (storedLeaves (staleHintLevelAtHead hl K 7) 7) 1) 3 1 ⟨1, 2, 2⟩
      ∧ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (chainTree 6) 3
          (MerkleSpec.Verifier.honestSibs h (hl ⟨0, 0, 0⟩)
            (storedLeaves (staleHintLevelAtHead hl K 7) 7) 7) 3 7 ⟨0, 0, 0⟩

end Contracts.InteropCommitmentTree
