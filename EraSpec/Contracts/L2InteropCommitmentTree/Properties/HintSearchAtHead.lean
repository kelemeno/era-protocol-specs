import EraSpec.Contracts.L2InteropCommitmentTree.Specs.HintSearchAtHead

/-!
# Properties: the head's unbounded walk, against the pin's five-hop search

Statements about `EraSpec.Contracts.L2InteropCommitmentTree.Specs.HintSearchAtHead`
(`main` `3605e82`; the same on `draft/v0.35.0` `d9f6789`).  Proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.HintSearchAtHead`.  No hash premise
anywhere.

## What removing the bound changes, and what it does not

* **Where a value goes is unchanged.**  On a valid tree the walk lands where the guarded
  insert of the rest of the theory puts the value (`InsertChecksAtHeadYieldGuard`).  That
  index does not depend on the hint (`InsertAtHeadLandingHintIndependent`), and the walk is
  the search with `leafCount` hops (`WalkAtHeadIsLeafCountSearch`).  So every head insert is
  a pin insert sent with its own landing index as the hint, and every pin insert is a head
  insert (`InsertChecksAtHeadVsPin`).
* **Which hints work changes.**  At head an insert succeeds from every hint the two
  up-front checks admit, an occupied index whose value is below `v`
  (`InsertAtHeadEnabledIff`).  At the pin the hint also had to be within five hops of the
  landing index.  The pin's liveness caveat `HonestInsertRevertsAtDeployedFuel` therefore
  no longer applies: the same honest insert succeeds at head (`HonestInsertSucceedsAtHead`).
* **Every result about pin runs from the predeploy transfers.**  A head run from the
  predeploy, with each insert's hint replaced by its landing index, is a pin run with the
  same states (`TxRunAtHeadIsRelabelledTxRun`).  Relabelling keeps idle steps, senders,
  `initL2()` calls and inserted values (`RelabelAtHeadKeepsShape`).  So
  `PredeployRunStates`, `PredeployRunReclaimableIffAbsent`, `StoredLeavesAreLeafHashes` and
  `PredeployStoredRootExclusiveOrBreak` hold for head runs (the `…AtHead` forms below).
* **Results about runs from any start are re-proved directly** (`InitL2AtMostOnceAtHead`,
  `TxRunAtHeadAppendOnly`, `TxRunAtHeadKeysMono`, `TxRunAtHeadFromValidIsRun`), since
  relabelling needs a valid tree.
* **The head admits strictly more runs.**  `StaleHintRunWitnessAtHead` is a head run from
  the predeploy with an insert six hops from its landing index.  It is not a pin run, and its
  relabelling is.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## The walk -/

/-- **THE WALK IS THE SEARCH WITH `leafCount` HOPS.**  On a valid tree, from an occupied
hint, the head's walk lands at `low` exactly when `lowSearch` with `leafCount` hops returns
`low`.  So the walk's result is that of any number of hops that lets it exit. -/
def Properties.WalkAtHeadIsLeafCountSearch : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint low : ℕ), hint < T.leafCount →
    (WalkSucceedsAtHead T v hint low ↔ lowSearch T v T.leafCount hint = some low)

/-- **THE WALK ALWAYS EXITS.**  On a valid tree, from every occupied hint and for every value,
the head's loop terminates (`LowSearchTerminates`). -/
def Properties.WalkAtHeadTerminates : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint : ℕ), hint < T.leafCount →
    ∃ low, WalkSucceedsAtHead T v hint low

/-- **THE WALK IS DETERMINISTIC.**  On any tree, two exits of the walk from one hint are at
one index. -/
def Properties.WalkAtHeadDeterministic : Prop :=
  ∀ (T : Tree) (v : UInt256) (hint low low' : ℕ),
    WalkSucceedsAtHead T v hint low → WalkSucceedsAtHead T v hint low' → low = low'

/-! ## The insert -/

/-- **A SUCCESSFUL HEAD INSERT IS THE GUARDED INSERT AT ITS LANDING INDEX.**  On a valid tree,
the head's checks and walk establish `InsertGuard` at the landing index, so the head's insert
is the guarded `insert` of `Specs/Model.lean` (`SearchYieldsGuard`, for the walk). -/
def Properties.InsertChecksAtHeadYieldGuard : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint low : ℕ),
    InsertChecksAtHead T v hint low → InsertGuard T v low

/-- **THE HINT DOES NOT CHOOSE WHERE THE VALUE GOES.**  On a valid tree, two successful head
inserts of one value, from any two hints, land at one index: the leaf whose window straddles
the value.  So the state after an insert does not depend on its hint. -/
def Properties.InsertAtHeadLandingHintIndependent : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint hint' low low' : ℕ),
    InsertChecksAtHead T v hint low → InsertChecksAtHead T v hint' low' → low = low'

/-- **AT HEAD, AN INSERT SUCCEEDS FROM EVERY ADMISSIBLE HINT.**  On a valid tree, some landing
index makes `insert(v, hint)` pass every check exactly when the tree is initialized, `v` is
nonzero and unregistered, and the hint is an occupied index whose value is below `v`.  These
are the checks of `IndexedMerkleTree.sol:71-88`; the walk itself never makes the call revert. -/
def Properties.InsertAtHeadEnabledIff : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint : ℕ),
    (∃ low, InsertChecksAtHead T v hint low)
      ↔ Initialized T ∧ v ≠ 0 ∧ T.valueToIndex v = 0 ∧ hint < T.leafCount
        ∧ (T.leaf hint).value < v

/-- **PIN INSERTS ARE HEAD INSERTS, AND HEAD INSERTS ARE PIN INSERTS FROM THEIR LANDING
INDEX.**  On a valid tree: every insert the pin's five-hop search accepts, the head accepts,
at the same index; and every head insert passes the pin's checks when its landing index is
sent as the hint, since the walk then makes no hop. -/
def Properties.InsertChecksAtHeadVsPin : Prop :=
  ∀ (T : Tree), Valid T → ∀ (v : UInt256) (hint low : ℕ),
    (InsertChecks T v hint low → InsertChecksAtHead T v hint low)
      ∧ (InsertChecksAtHead T v hint low → InsertChecks T v low low)

/-- **THE PIN'S HONEST REVERT SUCCEEDS AT HEAD.**  The instance of
`HonestInsertRevertsAtDeployedFuel`: on the honest seven-leaf tree `chainTree 6`, inserting
`7` from hint `0` passes no pin check for any landing index (the five-hop search runs out),
and passes the head's checks, landing at index `6` after six hops. -/
def Properties.HonestInsertSucceedsAtHead : Prop :=
  Reaches setup (chainTree 6)
    ∧ (∀ low, ¬ InsertChecks (chainTree 6) 7 0 low)
    ∧ InsertChecksAtHead (chainTree 6) 7 0 6

/-! ## Transactions and runs -/

/-- **EVERY PIN TRANSACTION IS A HEAD TRANSACTION.**  So every pin run is a head run, and
the head's results below cover every pin run. -/
def Properties.PinTxStepIsTxStepAtHead : Prop :=
  ∀ (K : Roles) (T : Tree) (c : Caller) (call : Call) (U : Tree),
    TxStep K T c call U → TxStepAtHead K T c call U

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
genesis predeploy's zero storage, the same states with the relabelled trace form a run of the
pin's `TxStep`.  So every `InitOnce` result about runs from the predeploy applies to the
head run's states. -/
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
exactly when it is not a key. -/
def Properties.PredeployRunReclaimableIffAbsentAtHead : Prop :=
  ∀ (K : Roles) (R : ℕ → Tree) (tx : Trace), TxRunAtHead K R tx →
    R 0 = predeploy →
    ∀ (n : ℕ) (v : UInt256), Initialized (R n) → v ≠ 0 →
      ((∃ W ∈ toAbs (R n), W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
        ↔ v ∉ keys (toAbs (R n)))

/-- **THE STORED LEAF HASHES ARE THE LIST STATE'S, AT HEAD.**  `StoredLeavesAreLeafHashes`,
with `_nodes[0]` written at each insert's landing index (`LevelRunAtHead`). -/
def Properties.StoredLeavesAreLeafHashesAtHead : Prop :=
  ∀ (K : Roles) (hl : LeafHash) (R : ℕ → Tree) (tx : Trace) (L : ℕ → LeafLevel),
    TxRunAtHead K R tx → LevelRunAtHead hl R tx L → R 0 = predeploy →
    ∀ n : ℕ, storedLeaves (L n) (R n).leafCount = leafHashes hl (R n)

/-- **EXCLUSIVITY OR A LOCATED BREAK AT THE STORED ROOT, AT HEAD.**
`PredeployStoredRootExclusiveOrBreak` for head runs, for every node hash, padding and leaf
hash (so in particular for the head's `IMT_EMPTY_LEAF_HASH` padding). -/
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
is a pin run: the stale hint becomes the landing index `6`.  So every premise of the
`…AtHead` run results above is met by a run outside the pin's model. -/
def Properties.StaleHintRunWitnessAtHead : Prop :=
  ∀ K : Roles,
    TxRunAtHead K staleHintRunAtHead (staleHintTxAtHead K)
      ∧ staleHintRunAtHead 0 = predeploy
      ∧ staleHintRunAtHead 8 = chainTree 7
      ∧ staleHintTxAtHead K 7 = some (K.appender, .insert 7 0)
      ∧ ¬ TxRun K staleHintRunAtHead (staleHintTxAtHead K)
      ∧ TxRun K staleHintRunAtHead (relabelAtHead staleHintRunAtHead (staleHintTxAtHead K))
      ∧ relabelAtHead staleHintRunAtHead (staleHintTxAtHead K) 7
          = some (K.appender, .insert 7 6)

end Contracts.InteropCommitmentTree
