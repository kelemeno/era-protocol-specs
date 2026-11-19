import EraSpec.Contracts.L2InteropCommitmentTree.Specs.UnboundedSearchAtV35

/-!
# Properties: the v35 `insert` on the indexed list state

Statements about `../Specs/UnboundedSearchAtV35.lean` (era-contracts `b17415d20`,
`IndexedMerkleTree.sol:65-107`); proofs in `../Proofs/UnboundedSearchAtV35.lean`.  No hash
appears.  Gas is not modelled, so "succeeds" means that the checks pass and the loop exits.

* **The lift.**  The loop has one exit (`SearchExitsDeterministicV35`).  On a `Valid` tree, from an
  occupied index, every exiting run of the fuelled loop is a v35 walk of the projection
  (`SearchIsWalkV35`), and every v35 walk of the projection is a run of the loop with exactly that
  many hops of fuel (`WalkIsSearchV35`).  The fuel the loop needs is the number of values strictly
  between the hint's value and `v` (`SearchFuelIsGapV35`): the pin's five hops sufficed exactly
  when that gap held at most five values.
* **The call.**  A successful v35 call is a v35 insert of the projection and keeps the tree
  `Valid` (`InsertCallProjectsV35`), and on a `Valid` tree every call that passes the five checks
  succeeds (`InsertCallSucceedsV35`).  So a v35 history of the indexed state from a `Valid` state
  projects to a v35 history (`RunCallProjectsV35`), to which the history results of
  `../../IndexedMerkleTree/Properties/UnboundedSearchAtV35.lean` apply under their own premises
  (from `setup`, the projection starts at the genesis `{⟨0, 0⟩}`: `toAbs_setup`).
* **Hint indices.**  Along such a history from `setup`, the hint index `0` always works
  (`SentinelIndexAlwaysWorksV35`), and along one from any `Valid` state a hint index that passed
  the hint checks once still passes them, with the same value, so the call succeeds while `v` is
  fresh (`OnceValidHintIndexStaysValidV35`).  This is the claim of `protocol-docs/message-root.md:95`
  at `b17415d20`, at the level of indices.
* **Witnesses**: `ChainTreeProjectsV35` (the pin's `chainTree` projects to `chainSetV35`) and
  `ChainTreeRunCallsV35` (a v35 history from `setup` whose seventh call, from the stale hint `0`,
  is the one the pin's five-hop loop reverts), which together instantiate every premise above.
-/

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false

namespace Contracts.InteropCommitmentTree

open IMTAbstract

/-! ## The lift of the loop -/

/-- **THE LOOP HAS ONE EXIT.**  If two fuels make the fuelled loop return, they return the same
index: the loop is deterministic, and more fuel never changes where it stops.  No premise. -/
def Properties.SearchExitsDeterministicV35 : Prop :=
  ∀ (T : Tree) (v : UInt256) (i j j' : ℕ),
    WalkExitsAtV35 T v i j → WalkExitsAtV35 T v i j' → j = j'

/-- **EVERY EXITING SEARCH IS A v35 WALK OF THE PROJECTION.**  On a `Valid` tree, from an occupied
index `i`, if the fuelled loop returns `j`, then the abstract v35 walk from `lowAbs T i` exits at
`lowAbs T j` after at most `fuel` hops.  Each hop to `nextIndex` lands on the leaf whose value is
`nextValue` (`Valid.linkAgree`). -/
def Properties.SearchIsWalkV35 : Prop :=
  ∀ (T : Tree) (v : UInt256) (fuel i j : ℕ), Valid T → i < T.leafCount →
    lowSearch T v fuel i = some j →
      ∃ n, n ≤ fuel ∧ WalkV35 (toAbs T) v n (lowAbs T i) (lowAbs T j)

/-- **EVERY v35 WALK OF THE PROJECTION IS A RUN OF THE LOOP.**  On a `Valid` tree, from an occupied
index `i`, an abstract v35 walk of `n` hops from `lowAbs T i` to `W` is the loop: with fuel `n` it
returns an occupied index `j` whose leaf projects to `W`.  The abstract hop target is the leaf at
`nextIndex` because keys are unique in a `Valid` tree. -/
def Properties.WalkIsSearchV35 : Prop :=
  ∀ (T : Tree) (v : UInt256) (n i : ℕ) (W : AbsLeaf), Valid T → i < T.leafCount →
    WalkV35 (toAbs T) v n (lowAbs T i) W →
      ∃ j, j < T.leafCount ∧ lowSearch T v n i = some j ∧ lowAbs T j = W

/-- **THE FUEL THE LOOP NEEDS IS THE GAP.**  On a `Valid` tree, from an occupied index `i`, the
fuelled loop returns an index iff the fuel is at least the number of values of the tree strictly
between the hint's value and `v`.  With the pin's `maxLowIndexSearchAttempts = 5` this is the exact
revert condition of the pin's search; at v35 the loop has no bound, so it exits from every
occupied index. -/
def Properties.SearchFuelIsGapV35 : Prop :=
  ∀ (T : Tree) (v : UInt256) (fuel i : ℕ), Valid T → i < T.leafCount →
    ((∃ j, lowSearch T v fuel i = some j)
      ↔ (gapKeysV35 (toAbs T) (T.leaf i).value v).card ≤ fuel)

/-! ## The call -/

/-- **A v35 CALL IS A v35 INSERT OF THE PROJECTION.**  On a `Valid` tree, a successful v35 call
`insert(v, hint)` leaving `T'` projects to a successful abstract v35 insert of `v` with hint leaf
`lowAbs T hint`, and `T'` is `Valid`. -/
def Properties.InsertCallProjectsV35 : Prop :=
  ∀ (T T' : Tree) (v : UInt256) (hint : ℕ), Valid T → InsertCallV35 T v hint T' →
    InsertV35 (toAbs T) v (lowAbs T hint) (toAbs T') ∧ Valid T'

/-- **A CALL THAT PASSES THE CHECKS SUCCEEDS.**  On a `Valid` tree, if `v` is nonzero and fresh in
`valueToIndex`, and the hint index is occupied with a value below `v`, the loop returns with
exactly the gap's number of hops of fuel and the call succeeds.  Gas is not modelled. -/
def Properties.InsertCallSucceedsV35 : Prop :=
  ∀ (T : Tree) (v : UInt256) (hint : ℕ), Valid T → v ≠ 0 → T.valueToIndex v = 0 →
    hint < T.leafCount → (T.leaf hint).value < v →
      ∃ j, lowSearch T v (gapKeysV35 (toAbs T) (T.leaf hint).value v).card hint = some j
        ∧ InsertCallV35 T v hint (insert T v j)

/-- **AN INDEXED v35 HISTORY PROJECTS TO A v35 HISTORY.**  From a `Valid` state, every state of a
v35 history of the indexed state is `Valid`, and the projections form a `RunV35`. -/
def Properties.RunCallProjectsV35 : Prop :=
  ∀ R : ℕ → Tree, RunCallV35 R → Valid (R 0) →
    (∀ n, Valid (R n)) ∧ RunV35 (fun n => toAbs (R n))

/-- **AN INDEXED v35 HISTORY IS A GUARDED RUN.**  From a `Valid` state, a v35 history of the
indexed state is a `Run` of `Specs/Model.lean` (each step idle or an `InsertGuard` insert at the
index the loop exits at), so the `Run`-based results (`run_valid`, `run_isGuardedEvolution`,
`genesis_run_reclaimable_iff_absent`) apply to it. -/
def Properties.RunCallIsRunV35 : Prop :=
  ∀ R : ℕ → Tree, RunCallV35 R → Valid (R 0) → Run R

/-! ## Hint indices -/

/-- **HINT INDEX 0 ALWAYS WORKS.**  Along a v35 history of the indexed state from `setup`, at every
snapshot, a call `insert(v, 0)` of a nonzero `v` that is fresh in `valueToIndex` succeeds: index
`0` is occupied and holds value `0` (`Valid.sentinel`), however many values lie below `v`. -/
def Properties.SentinelIndexAlwaysWorksV35 : Prop :=
  ∀ R : ℕ → Tree, RunCallV35 R → R 0 = setup →
    ∀ (n : ℕ) (v : UInt256), v ≠ 0 → (R n).valueToIndex v = 0 →
      ∃ T' : Tree, InsertCallV35 (R n) v 0 T'

/-- **A ONCE-VALID HINT INDEX STAYS VALID.**  Along a v35 history of the indexed state from a
`Valid` state, if the hint index `h` passed the two hint checks for `v` at snapshot `i` (occupied,
value below `v`), then at every later snapshot `j` it is still occupied with the same value, and
while `v` is nonzero and fresh in `valueToIndex` the call `insert(v, h)` succeeds.  This is the
claim of `protocol-docs/message-root.md:95` at `b17415d20` that a once-valid hint stays a valid
starting point; gas is not modelled. -/
def Properties.OnceValidHintIndexStaysValidV35 : Prop :=
  ∀ R : ℕ → Tree, RunCallV35 R → Valid (R 0) →
    ∀ (i j h : ℕ) (v : UInt256), i ≤ j → h < (R i).leafCount → ((R i).leaf h).value < v →
      v ≠ 0 → (R j).valueToIndex v = 0 →
        h < (R j).leafCount ∧ ((R j).leaf h).value = ((R i).leaf h).value
          ∧ ∃ T' : Tree, InsertCallV35 (R j) v h T'

/-! ## Witnesses -/

/-- **THE PIN'S HONEST RUN PROJECTS TO THE CHAIN.**  For `k ≤ 7`, the projection of the pin's
`chainTree k` (`Specs/HintSearch.lean`) is `chainSetV35 k`, the chain of the abstract v35
witnesses. -/
def Properties.ChainTreeProjectsV35 : Prop :=
  ∀ k : ℕ, k ≤ 7 → toAbs (chainTree k) = chainSetV35 k

/-- **AN INDEXED v35 HISTORY FROM `setup` THE PIN COULD NOT HAVE RUN.**  `chainTreeRunV35` is a v35
history of the indexed state from `setup` whose step `n < 7` is the call `insert(n + 1, 0)`,
from the hint index `0` (stale from the second call on), and which is idle afterwards.  At
snapshot `6`, from hint `0`, the loop returns index `6` with
six or seven hops of fuel, while with the pin's `maxLowIndexSearchAttempts` it reverts; the
projection there has the six-hop v35 walk from `lowAbs _ 0 = ⟨0, 1⟩`.  The hint index `5`
passed the hint checks for `7` at snapshot `5`, and its leaf has changed by snapshot `6`, where
`7` is fresh.

This instantiates every premise of the statements above: a `Valid` state (snapshot `6`, reached
from `setup`) with the occupied hint `0` below `v = 7` and `7` fresh, two exits of one search, a
walk of the projection, a v35 call, the history premises (`R 0 = setup`, and `setup` is `Valid`
by `setup_valid`), and those of `OnceValidHintIndexStaysValidV35` with `i = 5`, `j = 6`, `h = 5`,
`v = 7`. -/
def Properties.ChainTreeRunCallsV35 : Prop :=
  RunCallV35 chainTreeRunV35 ∧ chainTreeRunV35 0 = setup
    ∧ (∀ n, n < 7 →
        InsertCallV35 (chainTreeRunV35 n) ((n + 1 : ℕ) : UInt256) 0 (chainTreeRunV35 (n + 1)))
    ∧ (∀ n, 7 ≤ n → chainTreeRunV35 (n + 1) = chainTreeRunV35 n)
    ∧ Reaches setup (chainTreeRunV35 6) ∧ Valid (chainTreeRunV35 6)
    ∧ lowSearch (chainTreeRunV35 6) 7 6 0 = some 6 ∧ lowSearch (chainTreeRunV35 6) 7 7 0 = some 6
    ∧ lowSearch (chainTreeRunV35 6) 7 maxLowIndexSearchAttempts 0 = none
    ∧ lowAbs (chainTreeRunV35 6) 0 = ⟨0, 1⟩
    ∧ WalkV35 (toAbs (chainTreeRunV35 6)) 7 6 (lowAbs (chainTreeRunV35 6) 0) ⟨6, 0⟩
    ∧ (chainTreeRunV35 6).valueToIndex 7 = 0
    ∧ 5 < (chainTreeRunV35 5).leafCount ∧ ((chainTreeRunV35 5).leaf 5).value < 7
    ∧ (chainTreeRunV35 5).leaf 5 ≠ (chainTreeRunV35 6).leaf 5

/-- **`InsertCallV35` IS THE CANONICAL CHECKS PLUS THE RANGE CHECK AND THE WRITES.**  A successful
v35 `insert(v, hint)` on the list state, as this topic states it, is exactly: the canonical v35
checks `InsertChecksAtV35` (`Specs/HintSearch.lean`) at some exit index `low`,
`FullMerkle.updateLeaf`'s range check `low < leafCount`, and the writes `insert T v low`.  So this
topic's call and the canonical machine's insert (`CommitmentTreeAtV35.CTxStepAtV35.insert`) read
the same checks. -/
def Properties.InsertCallV35IffChecksAtV35 : Prop :=
  ∀ (T : Tree) (v : UInt256) (hint : ℕ) (T' : Tree),
    InsertCallV35 T v hint T'
      ↔ ∃ low, InsertChecksAtV35 T v hint low ∧ low < T.leafCount ∧ T' = insert T v low

end Contracts.InteropCommitmentTree
