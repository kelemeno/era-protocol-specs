import EraSpec.Contracts.IndexedMerkleTree.Specs.UnboundedSearchAtV35

/-!
# Properties: the unbounded low-leaf walk at draft/v0.35.0

Statements about `../Specs/UnboundedSearchAtV35.lean` (era-contracts `d9f6789`,
`IndexedMerkleTree.sol:65-107`, walk at `:90-93`).  Proofs:
`../Proofs/UnboundedSearchAtV35.lean`.  No hash appears: the walk reads only the leaf list.

* **The walk** exits at a leaf of the tree below `v` in the weak loop-exit window, with no
  soundness premise (`WalkSoundV35`).  On a sound set it always exits (`WalkTerminatesV35`), it is
  a function of its start (`WalkDeterministicV35`), and it takes exactly as many hops as there are
  keys strictly between the hint's key and `v` (`WalkLengthIsGapV35`).  For an absent `v` it ends
  at the unique leaf whose window straddles `v`, whatever the hint (`WalkFindsLowLeafV35`,
  `StraddlingLeafUniqueV35`, `WalkHintIndependentV35`).
* **The insert** is a `GuardedEvolution` step (`InsertV35IsGuardedStep`), keeps `SoundState` and
  adds exactly `v` (`InsertV35SoundStep`), flips `v` from reclaimable to not
  (`InsertV35TogglesReclaimable`), and its result does not depend on the hint
  (`InsertV35HintIndependent`).
* **The headlines over v35 histories** — the `IMTAbstract` capstones restated for `RunV35`:
  `RunV35IsGuardedEvolution`, `RunV35IsEvolution`, `RunV35Sound`, `ReclaimableIffAbsentV35`,
  `DeliveredAvailableForeverV35`, `DeliveryExactlyOnceV35`.
* **Liveness**, which the pin did not have: an honest insert's search never reverts from any member
  hint below `v` (`HonestInsertNeverSearchRevertsV35`); the sentinel is always such a hint
  (`SentinelHintAlwaysWorksV35`); a hint that was valid once stays valid
  (`OnceValidHintStaysValidV35`, the claim of `protocol-docs/message-root.md:95`).
* **Data availability**: a sound leaf set is determined by its keys
  (`SoundLeafSetDeterminedByKeysV35`), and the sequence of inserted values (what `_reportLeaf`
  logs) determines the whole history (`ValuesDetermineTreeV35`).
* **The pin, for contrast**: the pin's counted loop is the v35 walk cut off after the bound
  (`BoundedWalkIsTruncatedWalkV35`), so it reverts exactly when the gap holds more keys than the
  bound (`BoundedWalkRevertsIffGapExceedsV35`).  `PinBoundRevertsWhereV35InsertsV35` is the
  instance of the pin's `HonestInsertRevertsAtDeployedFuel`: six hops, bound five, reverted at the
  pin and performed at v35.
* **Witnesses**: `WalkPremisesSatisfiableV35` (two hints, two different walk lengths, one result)
  and `RunV35Satisfiable` (a genesis-rooted v35 history whose last insert walks six hops).
-/

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false

namespace IMTAbstract

open Clear

/-! ## The walk -/

/-- **WHERE THE WALK EXITS.**  Entered at a leaf of the tree below `v` (the two hint checks,
`IndexedMerkleTree.sol:80-88`), the walk exits at a leaf of the tree below `v` whose `nextKey` is `0`
or at least `v`: the weak loop-exit window of `GuardedEvolution`.  No invariant of the set is
needed: each hop lands on a leaf of the set whose key is below `v` by the loop test. -/
def Properties.WalkSoundV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (n : ℕ) (W₀ W : AbsLeaf),
    WalkV35 s v n W₀ W → W₀ ∈ s → W₀.key < v →
      W ∈ s ∧ W.key < v ∧ (W.nextKey = 0 ∨ v ≤ W.nextKey)

/-- **THE WALK ALWAYS EXITS.**  If every nonzero `nextKey` is a key (`NextClosed`) and windows
open upward (`WindowPos`), the walk from any leaf exits, after fewer hops than the tree has
leaves: each hop moves to a strictly larger key. -/
def Properties.WalkTerminatesV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (W₀ : AbsLeaf),
    NextClosed s → WindowPos s → W₀ ∈ s →
      ∃ (n : ℕ) (W : AbsLeaf), WalkV35 s v n W₀ W ∧ n < s.card

/-- **THE WALK IS A FUNCTION.**  With unique keys the hop target is unique, so two walks from the
same leaf take the same number of hops to the same leaf. -/
def Properties.WalkDeterministicV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (n n' : ℕ) (W₀ W W' : AbsLeaf),
    KeyInj s → WalkV35 s v n W₀ W → WalkV35 s v n' W₀ W' → n = n' ∧ W = W'

/-- **THE WALK'S LENGTH IS THE GAP.**  From a leaf of a `GapSound`, `WindowPos` tree, the walk
takes exactly as many hops as there are keys strictly between the starting key and `v`.  So every
hop of a stale hint's walk is a key that some earlier insert put into the gap, and the hint that
is already the low leaf walks zero hops. -/
def Properties.WalkLengthIsGapV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (n : ℕ) (W₀ W : AbsLeaf),
    GapSound s → WindowPos s → W₀ ∈ s → WalkV35 s v n W₀ W →
      n = (gapKeysV35 s W₀.key v).card

/-- **AT MOST ONE LEAF STRADDLES A VALUE.**  In a `GapSound`, `KeyInj` set, two leaves below `v`
whose windows both straddle `v` are the same leaf. -/
def Properties.StraddlingLeafUniqueV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (W₁ W₂ : AbsLeaf),
    GapSound s → KeyInj s → W₁ ∈ s → W₂ ∈ s →
    W₁.key < v → (W₁.nextKey = 0 ∨ v < W₁.nextKey) →
    W₂.key < v → (W₂.nextKey = 0 ∨ v < W₂.nextKey) → W₁ = W₂

/-- **THE WALK FINDS THE LOW LEAF.**  On a sound set, for an absent `v` and a hint that passes the
two hint checks, the walk exits at a leaf whose window straddles `v` STRICTLY, and it is the only
such leaf. -/
def Properties.WalkFindsLowLeafV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (n : ℕ) (W₀ W : AbsLeaf),
    SoundState s → v ∉ keys s → W₀ ∈ s → W₀.key < v → WalkV35 s v n W₀ W →
      W ∈ s ∧ W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)
        ∧ ∀ W' ∈ s, W'.key < v → (W'.nextKey = 0 ∨ v < W'.nextKey) → W' = W

/-- **THE HINT DOES NOT MATTER.**  On a sound set, for an absent `v`, walks from any two hints that
pass the hint checks exit at the same leaf. -/
def Properties.WalkHintIndependentV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (n₁ n₂ : ℕ) (W₁ W₂ R₁ R₂ : AbsLeaf),
    SoundState s → v ∉ keys s → W₁ ∈ s → W₁.key < v → W₂ ∈ s → W₂.key < v →
    WalkV35 s v n₁ W₁ R₁ → WalkV35 s v n₂ W₂ R₂ → R₁ = R₂

/-! ## The insert -/

/-- **A SUCCESSFUL v35 INSERT IS A `GuardedEvolution` STEP.**  Its exit leaf is a leaf of the tree
below `v` in the weak window, `v` is absent, and the new set is `imtInsert` through that leaf:
exactly the step `GuardedEvolution` allows.  No invariant of the set is needed. -/
def Properties.InsertV35IsGuardedStep : Prop :=
  ∀ (s s' : Finset AbsLeaf) (v : UInt256) (W₀ : AbsLeaf), InsertV35 s v W₀ s' →
    ∃ W : AbsLeaf, W ∈ s ∧ W.key < v ∧ (W.nextKey = 0 ∨ v ≤ W.nextKey) ∧ v ∉ keys s
      ∧ s' = imtInsert s W v

/-- **THE v35 INSERT IS SOUND.**  From a sound set, a successful v35 insert leaves a sound set and
adds exactly `v` to the keys (`guarded_insert_sound_step`). -/
def Properties.InsertV35SoundStep : Prop :=
  ∀ (s s' : Finset AbsLeaf) (v : UInt256) (W₀ : AbsLeaf), SoundState s → InsertV35 s v W₀ s' →
    SoundState s' ∧ keys s' = insert v (keys s)

/-- **THE v35 INSERT TOGGLES RECLAIMABILITY.**  Before a successful v35 insert of `v` some leaf
straddles `v` (a reclaim witness exists); after it none does
(`guarded_insert_toggles_reclaimable`). -/
def Properties.InsertV35TogglesReclaimable : Prop :=
  ∀ (s s' : Finset AbsLeaf) (v : UInt256) (W₀ : AbsLeaf), SoundState s → InsertV35 s v W₀ s' →
    (∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
      ∧ ¬ ∃ W ∈ s', W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **THE INSERT'S RESULT DOES NOT DEPEND ON THE HINT.**  On a sound set, two successful v35
inserts of the same value, through any two hints, leave the same set. -/
def Properties.InsertV35HintIndependent : Prop :=
  ∀ (s s₁ s₂ : Finset AbsLeaf) (v : UInt256) (W₁ W₂ : AbsLeaf),
    SoundState s → InsertV35 s v W₁ s₁ → InsertV35 s v W₂ s₂ → s₁ = s₂

/-- **AN HONEST INSERT'S SEARCH NEVER REVERTS.**  On a sound set, for a nonzero absent `v` and ANY
leaf below `v` as the hint, the walk exits, after exactly the gap's number of hops, and the insert
succeeds.  At the pin the same call reverted once the gap held more than five keys
(`BoundedWalkRevertsIffGapExceedsV35`). -/
def Properties.HonestInsertNeverSearchRevertsV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (W₀ : AbsLeaf),
    SoundState s → v ≠ 0 → v ∉ keys s → W₀ ∈ s → W₀.key < v →
      ∃ (n : ℕ) (W : AbsLeaf), WalkV35 s v n W₀ W ∧ n = (gapKeysV35 s W₀.key v).card
        ∧ InsertV35 s v W₀ (imtInsert s W v)

/-! ## The headlines over v35 histories -/

/-- **A v35 HISTORY IS A `GuardedEvolution`.**  No premise: every successful v35 insert is a
guarded step (`InsertV35IsGuardedStep`). -/
def Properties.RunV35IsGuardedEvolution : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → GuardedEvolution S

/-- **A v35 HISTORY FROM A SOUND GENESIS IS AN `Evolution`**, so the whole analytic corpus of
`Properties/Model.lean` applies to it (`guardedEvolution_isEvolution`). -/
def Properties.RunV35IsEvolution : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → SoundState (S 0) → Evolution S

/-- **A v35 HISTORY FROM A SOUND GENESIS STAYS SOUND.** -/
def Properties.RunV35Sound : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → SoundState (S 0) → ∀ n, SoundState (S n)

/-- **RECLAIM DICHOTOMY AT v35.**  Along a v35 history from the genesis `{⟨0, 0⟩}`, a nonzero value
has a reclaim witness at snapshot `j` iff it is absent from `S j`
(`guardedEvolution_reclaimable_iff_absent`). -/
def Properties.ReclaimableIffAbsentV35 : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → S 0 = {⟨0, 0⟩} →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 →
      ((∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)) ↔ v ∉ keys (S j))

/-- **DELIVERY IS FINAL AT v35.**  Along a v35 history from genesis with monotone settlement
timestamps, a value present at an on-time snapshot stays present and has no reclaim witness at
any deadline-pinned snapshot (`guardedEvolution_delivered_available_forever`). -/
def Properties.DeliveredAvailableForeverV35 : Prop :=
  ∀ (S : ℕ → Finset AbsLeaf) (t : ℕ → UInt256) (D v : UInt256), RunV35 S → S 0 = {⟨0, 0⟩} →
    Monotone t → ∀ i, t i ≤ D → v ∈ keys (S i) →
      (∀ j, i ≤ j → v ∈ keys (S j))
        ∧ ∀ (j : ℕ) (W : AbsLeaf), D < t (j + 1) → W ∈ S j → W.key < v →
            ¬ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **DELIVERY IS EXACTLY ONCE AT v35.**  Along a v35 history from genesis, a nonzero value present
at step `n` entered the tree at exactly one earlier step
(`guardedEvolution_delivery_exactly_once`). -/
def Properties.DeliveryExactlyOnceV35 : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → S 0 = {⟨0, 0⟩} →
    ∀ (v : UInt256), v ≠ 0 → ∀ n, v ∈ keys (S n) →
      ∃! m, m < n ∧ v ∉ keys (S m) ∧ keys (S (m + 1)) = insert v (keys (S m))

/-! ## Liveness along v35 histories -/

/-- **THE SENTINEL IS ALWAYS A WORKING HINT.**  Along a v35 history from genesis, at every snapshot
there is a leaf with key `0` (index 0's leaf; its key never changes), and an insert of any nonzero
absent value through it succeeds, however many keys now lie below the value. -/
def Properties.SentinelHintAlwaysWorksV35 : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → S 0 = {⟨0, 0⟩} →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 → v ∉ keys (S j) →
      ∃ W₀ ∈ S j, W₀.key = 0 ∧ ∃ s' : Finset AbsLeaf, InsertV35 (S j) v W₀ s'

/-- **A ONCE-VALID HINT STAYS VALID.**  Along a v35 history from a sound genesis, if `W₀` passed the
hint checks for `v` at snapshot `i`, then at every later snapshot `j` at which `v` is still absent
there is a leaf with the same key (the same index: an insert retargets the low leaf's `nextKey` and
never its key), and an insert of `v` through it succeeds.  This is the claim of
`protocol-docs/message-root.md:95` at `d9f6789`: "a once-valid hint stays a valid starting point
forever, so an insert with a once-valid hint can no longer hit a hint-validity revert". -/
def Properties.OnceValidHintStaysValidV35 : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → SoundState (S 0) →
    ∀ (i j : ℕ) (W₀ : AbsLeaf) (v : UInt256), i ≤ j → W₀ ∈ S i → W₀.key < v → v ≠ 0 →
      v ∉ keys (S j) →
        ∃ W₀' ∈ S j, W₀'.key = W₀.key ∧ ∃ s' : Finset AbsLeaf, InsertV35 (S j) v W₀' s'

/-! ## Data availability: the inserted values determine the tree -/

/-- **A SOUND LEAF SET IS DETERMINED BY ITS KEYS.**  In a sound set each leaf's `nextKey` is the
next larger key, or `0` on the largest, so two sound sets with the same keys are equal. -/
def Properties.SoundLeafSetDeterminedByKeysV35 : Prop :=
  ∀ s s' : Finset AbsLeaf, SoundState s → SoundState s' → keys s = keys s' → s = s'

/-- **THE INSERTED VALUES DETERMINE THE HISTORY.**  Two v35 histories from the same sound genesis
that insert the same values at the same steps (each through hints of its own) are equal at every
step.  At `d9f6789`, `L2InteropCommitmentTree.insert` reports each inserted value through
`_reportLeaf` (`L2InteropCommitmentTree.sol:58-62`), so the logged values determine the leaf set. -/
def Properties.ValuesDetermineTreeV35 : Prop :=
  ∀ (S S' : ℕ → Finset AbsLeaf) (vals : ℕ → Option UInt256),
    (∀ n, StepV35 (vals n) (S n) (S (n + 1))) → (∀ n, StepV35 (vals n) (S' n) (S' (n + 1))) →
    S 0 = S' 0 → SoundState (S 0) → ∀ n, S n = S' n

/-! ## The pin's bound, for contrast -/

/-- **THE PIN'S LOOP IS THE v35 WALK CUT OFF AFTER THE BOUND.**  A v35 walk of `n` hops is a
successful run of the pin's counted loop when `n ≤ bound`, and a reverting one when `bound < n`. -/
def Properties.BoundedWalkIsTruncatedWalkV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (bound n : ℕ) (W₀ W : AbsLeaf), WalkV35 s v n W₀ W →
    (n ≤ bound → BoundedWalkV35 s v bound 0 W₀ (some W))
      ∧ (bound < n → BoundedWalkV35 s v bound 0 W₀ none)

/-- **THE PIN REVERTED EXACTLY WHEN THE GAP EXCEEDED THE BOUND.**  On a sound set, from a leaf of
the tree, the pin's counted loop reverts iff more than `bound` keys lie strictly between the hint's
key and `v`, and exits at `W` iff the gap is within the bound and the v35 walk exits at `W`. -/
def Properties.BoundedWalkRevertsIffGapExceedsV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (bound : ℕ) (W₀ : AbsLeaf), SoundState s → W₀ ∈ s →
    (BoundedWalkV35 s v bound 0 W₀ none ↔ bound < (gapKeysV35 s W₀.key v).card)
      ∧ ∀ W : AbsLeaf, BoundedWalkV35 s v bound 0 W₀ (some W)
          ↔ ((gapKeysV35 s W₀.key v).card ≤ bound ∧ ∃ n, WalkV35 s v n W₀ W)

/-- **THE PIN'S DEPLOYED BOUND REVERTS AN HONEST INSERT THAT v35 PERFORMS.**  On the sound chain
`chainSetV35 6` (the leaf set of the pin's `chainTree 6`), inserting the absent `7` through the
sentinel `⟨0, 1⟩`: the gap holds six keys, the v35 walk takes six hops to the tail `⟨6, 0⟩` and the
insert succeeds, while the pin's loop with `MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5` reverts and has no
successful run.  The abstract counterpart of the pin's `HonestInsertRevertsAtDeployedFuel`. -/
def Properties.PinBoundRevertsWhereV35InsertsV35 : Prop :=
  SoundState (chainSetV35 6) ∧ (⟨0, 1⟩ : AbsLeaf) ∈ chainSetV35 6
    ∧ (7 : UInt256) ∉ keys (chainSetV35 6)
    ∧ (gapKeysV35 (chainSetV35 6) 0 7).card = 6
    ∧ WalkV35 (chainSetV35 6) 7 6 ⟨0, 1⟩ ⟨6, 0⟩
    ∧ InsertV35 (chainSetV35 6) 7 ⟨0, 1⟩ (chainSetV35 7)
    ∧ BoundedWalkV35 (chainSetV35 6) 7 pinSearchAttemptsV35 0 ⟨0, 1⟩ none
    ∧ ∀ W : AbsLeaf, ¬ BoundedWalkV35 (chainSetV35 6) 7 pinSearchAttemptsV35 0 ⟨0, 1⟩ (some W)

/-! ## Witnesses -/

/-- **THE WALK PREMISES ARE SATISFIABLE, WITH A STALE HINT.**  On the sound chain `chainSetV35 2`
(`{⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 0⟩}`), inserting the absent `3`: the stale sentinel hint walks two hops and
the hint `⟨1, 2⟩` one, both to `⟨2, 0⟩`; both inserts succeed, with the same result. -/
def Properties.WalkPremisesSatisfiableV35 : Prop :=
  SoundState (chainSetV35 2) ∧ (3 : UInt256) ∉ keys (chainSetV35 2)
    ∧ (⟨0, 1⟩ : AbsLeaf) ∈ chainSetV35 2 ∧ (⟨1, 2⟩ : AbsLeaf) ∈ chainSetV35 2
    ∧ WalkV35 (chainSetV35 2) 3 2 ⟨0, 1⟩ ⟨2, 0⟩ ∧ WalkV35 (chainSetV35 2) 3 1 ⟨1, 2⟩ ⟨2, 0⟩
    ∧ InsertV35 (chainSetV35 2) 3 ⟨0, 1⟩ (chainSetV35 3)
    ∧ InsertV35 (chainSetV35 2) 3 ⟨1, 2⟩ (chainSetV35 3)

/-- **A v35 HISTORY THE PIN COULD NOT HAVE RUN.**  `chainRunV35` is a v35 history from the genesis
`{⟨0, 0⟩}` (so it meets the premises of every run headline above) whose seven inserts all use the
sentinel as the hint; its last insert walks six hops, which the pin's loop rejects, and puts `7`
in the tree. -/
def Properties.RunV35Satisfiable : Prop :=
  RunV35 chainRunV35 ∧ chainRunV35 0 = {⟨0, 0⟩}
    ∧ InsertV35 (chainRunV35 6) 7 ⟨0, 1⟩ (chainRunV35 7)
    ∧ WalkV35 (chainRunV35 6) 7 6 ⟨0, 1⟩ ⟨6, 0⟩
    ∧ BoundedWalkV35 (chainRunV35 6) 7 pinSearchAttemptsV35 0 ⟨0, 1⟩ none
    ∧ (7 : UInt256) ∈ keys (chainRunV35 7)

end IMTAbstract
