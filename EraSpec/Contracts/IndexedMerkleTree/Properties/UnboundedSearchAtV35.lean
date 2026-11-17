import EraSpec.Contracts.IndexedMerkleTree.Specs.UnboundedSearchAtV35

/-!
# Properties: the unbounded low-leaf walk at draft/v0.35.0

Statements about `../Specs/UnboundedSearchAtV35.lean` (era-contracts `b17415d20`, identical to
`d9f6789` here; `IndexedMerkleTree.sol:65-107`, walk at `:90-93`).  Proofs:
`../Proofs/UnboundedSearchAtV35.lean`.  No hash appears: the walk reads only the leaf list.  Gas is
not modelled, so "succeeds" below means that the checks pass and the loop exits.

* **The walk** exits at a leaf of the set below `v` in the weak loop-exit window, with no
  invariant of the set needed (`WalkSoundV35`).  If links resolve and windows open upward, some
  walk from every leaf exits (`WalkTerminatesV35`); with unique keys there is only one
  (`WalkDeterministicV35`); on a `GapSound`, `WindowPos` set it takes exactly as many hops as there
  are keys strictly between the hint's key and `v` (`WalkLengthIsGapV35`).  On a sound set, for an absent
  `v`, it ends at the one leaf whose window straddles `v`, whatever the hint
  (`WalkFindsLowLeafV35`, `StraddlingLeafUniqueV35`, `WalkHintIndependentV35`).
* **The insert** is a `GuardedEvolution` step (`InsertV35IsGuardedStep`), keeps `SoundState` and
  adds exactly `v` (`InsertV35SoundStep`), flips `v` from having a straddling leaf to having none
  (`InsertV35TogglesReclaimable`), and its result does not depend on the hint
  (`InsertV35HintIndependent`).
* **The headlines over v35 histories**, the `IMTAbstract` capstones restated for `RunV35`:
  `RunV35IsGuardedEvolution`, `RunV35IsEvolution`, `RunV35Sound`, `ReclaimableIffAbsentV35`,
  `DeliveredAvailableForeverV35`, `DeliveryExactlyOnceV35`.
* **Liveness from every member hint below `v`**: on a sound set an insert of a nonzero absent
  value succeeds from any such hint (`HonestInsertNeverSearchRevertsV35`); along a history from
  genesis the leaf with key `0` is always such a hint (`SentinelHintAlwaysWorksV35`), and a hint
  key that passed the checks once still does (`OnceValidHintStaysValidV35`, the claim of
  `protocol-docs/message-root.md:95`).  The pin's bound broke this once the gap held more than
  five keys.
* **Data availability**: a sound leaf set is determined by its keys
  (`SoundLeafSetDeterminedByKeysV35`), so the sequence of inserted values determines every leaf
  set of a history (`ValuesDetermineTreeV35`).  Indices are not covered.
* **The pin, for contrast**: the pin's counted loop is the v35 walk cut off after the bound
  (`BoundedWalkIsTruncatedWalkV35`), so it reverts exactly when the gap holds more keys than the
  bound (`BoundedWalkRevertsIffGapExceedsV35`).  `PinBoundRevertsWhereV35InsertsV35` is the
  abstract counterpart of the pin's `HonestInsertRevertsAtDeployedFuel`: six hops, bound five,
  reverted at the pin and performed at v35.
* **Witnesses**, which together instantiate every premise of every statement above:
  `WalkPremisesSatisfiableV35` (one set, two hints, walks of two and one hops),
  `InsertOrderForgottenV35` (two insertion orders, one set), `RunV35Satisfiable` (a history from
  genesis whose last insert walks six hops) and `RunV35PremisesMetV35` (its clock, a stale hint
  whose leaf has changed, and a second hint for the same step).
-/

-- Named propositions are transparent abbreviations; proofs reference these statements.
-- Preconditions remain parameters even when absent from the conclusion.
set_option linter.unusedVariables false

namespace IMTAbstract

open Clear

/-! ## The walk -/

/-- **WHERE THE WALK EXITS.**  Entered at a leaf of the set below `v` (the two hint checks,
`IndexedMerkleTree.sol:80-88`), a walk exits at a leaf of the set below `v` whose `nextKey` is `0`
or at least `v`: the weak loop-exit window of `GuardedEvolution`.  No invariant of the set is
needed: each hop lands on a leaf of the set, and its key is below `v` by the loop test. -/
def Properties.WalkSoundV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (n : ℕ) (W₀ W : AbsLeaf),
    WalkV35 s v n W₀ W → W₀ ∈ s → W₀.key < v →
      W ∈ s ∧ W.key < v ∧ (W.nextKey = 0 ∨ v ≤ W.nextKey)

/-- **THE WALK EXITS.**  If every nonzero `nextKey` is a key (`NextClosed`) and windows open
upward (`WindowPos`), then from every leaf of the set some walk exits, after fewer hops than the
set has leaves: each hop moves to a strictly larger key.  With unique keys it is the only walk
(`WalkDeterministicV35`). -/
def Properties.WalkTerminatesV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (W₀ : AbsLeaf),
    NextClosed s → WindowPos s → W₀ ∈ s →
      ∃ (n : ℕ) (W : AbsLeaf), WalkV35 s v n W₀ W ∧ n < s.card

/-- **THE WALK IS A FUNCTION.**  With unique keys the hop target is unique, so two walks from the
same leaf take the same number of hops to the same leaf. -/
def Properties.WalkDeterministicV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (n n' : ℕ) (W₀ W W' : AbsLeaf),
    KeyInj s → WalkV35 s v n W₀ W → WalkV35 s v n' W₀ W' → n = n' ∧ W = W'

/-- **THE WALK'S LENGTH IS THE GAP.**  From a leaf of a `GapSound`, `WindowPos` set, a walk takes
exactly as many hops as there are keys strictly between the starting key and `v`: each hop
crosses one key of that gap.  A hint that is already the low leaf walks zero hops. -/
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
two hint checks, a walk exits at a leaf whose window straddles `v` STRICTLY, and it is the only
leaf of the set below `v` that does. -/
def Properties.WalkFindsLowLeafV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (n : ℕ) (W₀ W : AbsLeaf),
    SoundState s → v ∉ keys s → W₀ ∈ s → W₀.key < v → WalkV35 s v n W₀ W →
      W ∈ s ∧ W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)
        ∧ ∀ W' ∈ s, W'.key < v → (W'.nextKey = 0 ∨ v < W'.nextKey) → W' = W

/-- **THE HINT DOES NOT CHANGE WHERE THE WALK ENDS.**  On a sound set, for an absent `v`, walks
from any two hints that pass the hint checks exit at the same leaf. -/
def Properties.WalkHintIndependentV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (n₁ n₂ : ℕ) (W₁ W₂ R₁ R₂ : AbsLeaf),
    SoundState s → v ∉ keys s → W₁ ∈ s → W₁.key < v → W₂ ∈ s → W₂.key < v →
    WalkV35 s v n₁ W₁ R₁ → WalkV35 s v n₂ W₂ R₂ → R₁ = R₂

/-! ## The insert -/

/-- **A SUCCESSFUL v35 INSERT IS A `GuardedEvolution` STEP.**  Its exit leaf is a leaf of the set
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

/-- **THE v35 INSERT FLIPS THE STRADDLING LEAF.**  On a sound set, before a successful v35 insert
of `v` some leaf of the set straddles `v`, and after it no leaf of the new set does
(`guarded_insert_toggles_reclaimable`).  Only leaves of the set are considered. -/
def Properties.InsertV35TogglesReclaimable : Prop :=
  ∀ (s s' : Finset AbsLeaf) (v : UInt256) (W₀ : AbsLeaf), SoundState s → InsertV35 s v W₀ s' →
    (∃ W ∈ s, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey))
      ∧ ¬ ∃ W ∈ s', W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **THE INSERT'S RESULT DOES NOT DEPEND ON THE HINT.**  On a sound set, two successful v35
inserts of the same value, through any two hints, leave the same set. -/
def Properties.InsertV35HintIndependent : Prop :=
  ∀ (s s₁ s₂ : Finset AbsLeaf) (v : UInt256) (W₁ W₂ : AbsLeaf),
    SoundState s → InsertV35 s v W₁ s₁ → InsertV35 s v W₂ s₂ → s₁ = s₂

/-- **AN HONEST INSERT SUCCEEDS FROM ANY HINT BELOW THE VALUE.**  On a sound set, for a nonzero
absent `v` and ANY leaf of the set below `v` as the hint, a walk exits after exactly the gap's
number of hops, and the insert through it succeeds.  Gas is not modelled.  At the pin the same
call reverted once the gap held more than five keys (`BoundedWalkRevertsIffGapExceedsV35` with
`pinSearchAttemptsV35`). -/
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

/-- **A v35 HISTORY FROM A SOUND START IS AN `Evolution`**, so the analytic results of
`Properties/Model.lean` stated for `Evolution` apply to it (`guardedEvolution_isEvolution`). -/
def Properties.RunV35IsEvolution : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → SoundState (S 0) → Evolution S

/-- **A v35 HISTORY FROM A SOUND START STAYS SOUND.** -/
def Properties.RunV35Sound : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → SoundState (S 0) → ∀ n, SoundState (S n)

/-- **STRADDLING DICHOTOMY AT v35.**  Along a v35 history from the genesis `{⟨0, 0⟩}`, a nonzero
value has a leaf of `S j` straddling it iff it is absent from `S j`
(`guardedEvolution_reclaimable_iff_absent`).  The witness ranges over leaves of `S j` only. -/
def Properties.ReclaimableIffAbsentV35 : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → S 0 = {⟨0, 0⟩} →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 →
      ((∃ W ∈ S j, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)) ↔ v ∉ keys (S j))

/-- **A PRESENT VALUE STAYS PRESENT AND UNSTRADDLED AT v35.**  Along a v35 history from genesis
with monotone settlement timestamps `t`, a value present at a snapshot `i` with `t i ≤ D` is
present at every later snapshot, and at every snapshot `j` with `D < t (j + 1)` no leaf of `S j`
below it straddles it (`guardedEvolution_delivered_available_forever`). -/
def Properties.DeliveredAvailableForeverV35 : Prop :=
  ∀ (S : ℕ → Finset AbsLeaf) (t : ℕ → UInt256) (D v : UInt256), RunV35 S → S 0 = {⟨0, 0⟩} →
    Monotone t → ∀ i, t i ≤ D → v ∈ keys (S i) →
      (∀ j, i ≤ j → v ∈ keys (S j))
        ∧ ∀ (j : ℕ) (W : AbsLeaf), D < t (j + 1) → W ∈ S j → W.key < v →
            ¬ (W.nextKey = 0 ∨ v < W.nextKey)

/-- **EACH VALUE ENTERS ONCE AT v35.**  Along a v35 history from genesis, a nonzero value present
at step `n` entered the key set at exactly one earlier step
(`guardedEvolution_delivery_exactly_once`). -/
def Properties.DeliveryExactlyOnceV35 : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → S 0 = {⟨0, 0⟩} →
    ∀ (v : UInt256), v ≠ 0 → ∀ n, v ∈ keys (S n) →
      ∃! m, m < n ∧ v ∉ keys (S m) ∧ keys (S (m + 1)) = insert v (keys (S m))

/-! ## Liveness along v35 histories -/

/-- **THE KEY-0 LEAF IS ALWAYS A WORKING HINT.**  Along a v35 history from genesis, every snapshot
has a leaf with key `0`, and an insert of any nonzero absent value through it succeeds, however
many keys lie below the value.  (In the source this is index 0's sentinel: `insert` never
rewrites a leaf's `value`, `IndexedMerkleTree.sol:99-100`.  Indices are not modelled here; the
index-level statement is `Contracts.InteropCommitmentTree.Properties.SentinelIndexAlwaysWorksV35`.) -/
def Properties.SentinelHintAlwaysWorksV35 : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → S 0 = {⟨0, 0⟩} →
    ∀ (j : ℕ) (v : UInt256), v ≠ 0 → v ∉ keys (S j) →
      ∃ W₀ ∈ S j, W₀.key = 0 ∧ ∃ s' : Finset AbsLeaf, InsertV35 (S j) v W₀ s'

/-- **A ONCE-VALID HINT STAYS VALID.**  Along a v35 history from a sound start, if `W₀` passed the
hint checks for `v` at snapshot `i`, then at every later snapshot `j` at which `v` is still absent
some leaf has `W₀`'s key, and an insert of `v` through it succeeds.  The leaf itself may have
changed: an insert retargets the low leaf's `nextKey`.  This is the claim of
`protocol-docs/message-root.md:95` at `b17415d20`, read through keys (indices are not modelled;
in the source an index's `value` never changes, `IndexedMerkleTree.sol:99-100`).  The
index-level statement is `Contracts.InteropCommitmentTree.Properties.OnceValidHintIndexStaysValidV35`. -/
def Properties.OnceValidHintStaysValidV35 : Prop :=
  ∀ S : ℕ → Finset AbsLeaf, RunV35 S → SoundState (S 0) →
    ∀ (i j : ℕ) (W₀ : AbsLeaf) (v : UInt256), i ≤ j → W₀ ∈ S i → W₀.key < v → v ≠ 0 →
      v ∉ keys (S j) →
        ∃ W₀' ∈ S j, W₀'.key = W₀.key ∧ ∃ s' : Finset AbsLeaf, InsertV35 (S j) v W₀' s'

/-! ## Data availability: the inserted values determine the leaf sets -/

/-- **A SOUND LEAF SET IS DETERMINED BY ITS KEYS.**  In a sound set each leaf's `nextKey` is the
next larger key, or `0` on the largest, so two sound sets with the same keys are equal. -/
def Properties.SoundLeafSetDeterminedByKeysV35 : Prop :=
  ∀ s s' : Finset AbsLeaf, SoundState s → SoundState s' → keys s = keys s' → s = s'

/-- **THE INSERTED VALUES DETERMINE THE LEAF SETS.**  Two v35 histories from the same sound start
whose steps insert the same values in the same order (each through hints of its own) have the
same leaf set at every step.  In the source, `L2InteropCommitmentTree.insert` passes each inserted
value to `_reportLeaf` (`L2InteropCommitmentTree.sol:58-62` at `b17415d20`); the report is not
modelled.  The statement is about abstract leaf sets: leaf positions and `nextIndex` are not
covered. -/
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
the set, the pin's counted loop reverts iff more than `bound` keys lie strictly between the hint's
key and `v`, and exits at `W` iff the gap is within the bound and a v35 walk exits at `W`. -/
def Properties.BoundedWalkRevertsIffGapExceedsV35 : Prop :=
  ∀ (s : Finset AbsLeaf) (v : UInt256) (bound : ℕ) (W₀ : AbsLeaf), SoundState s → W₀ ∈ s →
    (BoundedWalkV35 s v bound 0 W₀ none ↔ bound < (gapKeysV35 s W₀.key v).card)
      ∧ ∀ W : AbsLeaf, BoundedWalkV35 s v bound 0 W₀ (some W)
          ↔ ((gapKeysV35 s W₀.key v).card ≤ bound ∧ ∃ n, WalkV35 s v n W₀ W)

/-- **THE PIN'S DEPLOYED BOUND REVERTS AN HONEST INSERT THAT v35 PERFORMS.**  On the sound chain
`chainSetV35 6`, inserting the absent `7` through the key-0 leaf `⟨0, 1⟩`: the gap holds six
keys, the v35 walk takes six hops to the tail `⟨6, 0⟩` and the insert succeeds, while the pin's
loop with `MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5` reverts and has no successful run.  The abstract
counterpart of the pin's `HonestInsertRevertsAtDeployedFuel` (`chainSetV35 6` is the projection
of its `chainTree 6`: `Contracts.InteropCommitmentTree.Properties.ChainTreeProjectsV35`). -/
def Properties.PinBoundRevertsWhereV35InsertsV35 : Prop :=
  SoundState (chainSetV35 6) ∧ (⟨0, 1⟩ : AbsLeaf) ∈ chainSetV35 6
    ∧ (7 : UInt256) ∉ keys (chainSetV35 6)
    ∧ (gapKeysV35 (chainSetV35 6) 0 7).card = 6
    ∧ WalkV35 (chainSetV35 6) 7 6 ⟨0, 1⟩ ⟨6, 0⟩
    ∧ InsertV35 (chainSetV35 6) 7 ⟨0, 1⟩ (chainSetV35 7)
    ∧ BoundedWalkV35 (chainSetV35 6) 7 pinSearchAttemptsV35 0 ⟨0, 1⟩ none
    ∧ ∀ W : AbsLeaf, ¬ BoundedWalkV35 (chainSetV35 6) 7 pinSearchAttemptsV35 0 ⟨0, 1⟩ (some W)

/-! ## Witnesses -/

/-- **THE WALK AND INSERT PREMISES ARE SATISFIABLE, WITH A STALE HINT.**  On the sound chain
`chainSetV35 2` (`{⟨0, 1⟩, ⟨1, 2⟩, ⟨2, 0⟩}`), inserting the nonzero absent `3`: the stale key-0
hint `⟨0, 1⟩` walks two hops (the gap `{1, 2}`) and the hint `⟨1, 2⟩` one, both to the leaf
`⟨2, 0⟩`, which straddles `3`; both inserts succeed, with the same result `chainSetV35 3`.

This instantiates every premise of the walk and insert statements, the pin-contrast statements,
`WalkTerminatesV35` (`NextClosed`, `WindowPos`, `KeyInj` and `GapSound` are parts of
`SoundState`), `StraddlingLeafUniqueV35` (with `W₁ = W₂ = ⟨2, 0⟩`, which its conclusion forces),
`WalkHintIndependentV35` and `InsertV35HintIndependent` (two different hints), and
`HonestInsertNeverSearchRevertsV35`. -/
def Properties.WalkPremisesSatisfiableV35 : Prop :=
  SoundState (chainSetV35 2) ∧ (3 : UInt256) ≠ 0 ∧ (3 : UInt256) ∉ keys (chainSetV35 2)
    ∧ (⟨0, 1⟩ : AbsLeaf) ∈ chainSetV35 2 ∧ (⟨0, 1⟩ : AbsLeaf).key < 3
    ∧ (⟨1, 2⟩ : AbsLeaf) ∈ chainSetV35 2 ∧ (⟨1, 2⟩ : AbsLeaf).key < 3
    ∧ (⟨2, 0⟩ : AbsLeaf) ∈ chainSetV35 2 ∧ (⟨2, 0⟩ : AbsLeaf).key < 3
    ∧ (⟨2, 0⟩ : AbsLeaf).nextKey = 0
    ∧ (gapKeysV35 (chainSetV35 2) 0 3).card = 2
    ∧ WalkV35 (chainSetV35 2) 3 2 ⟨0, 1⟩ ⟨2, 0⟩ ∧ WalkV35 (chainSetV35 2) 3 1 ⟨1, 2⟩ ⟨2, 0⟩
    ∧ InsertV35 (chainSetV35 2) 3 ⟨0, 1⟩ (chainSetV35 3)
    ∧ InsertV35 (chainSetV35 2) 3 ⟨1, 2⟩ (chainSetV35 3)

/-- **TWO INSERTION ORDERS, ONE SET.**  Inserting `2` and then `1` into the genesis (each through
the key-0 leaf; the second walk takes zero hops) passes through `{⟨0, 2⟩, ⟨2, 0⟩}`, which is not
`chainSetV35 1`, and reaches `swappedSetV35`: a sound set with the keys of `chainSetV35 2`.  So the
premises of `SoundLeafSetDeterminedByKeysV35` hold for `chainSetV35 2` and `swappedSetV35`,
which are built by different histories. -/
def Properties.InsertOrderForgottenV35 : Prop :=
  SoundState (chainSetV35 2) ∧ SoundState swappedSetV35
    ∧ keys swappedSetV35 = keys (chainSetV35 2)
    ∧ InsertV35 {⟨0, 0⟩} 2 ⟨0, 0⟩ (imtInsert {⟨0, 0⟩} ⟨0, 0⟩ 2)
    ∧ InsertV35 (imtInsert {⟨0, 0⟩} ⟨0, 0⟩ 2) 1 ⟨0, 2⟩ swappedSetV35
    ∧ imtInsert {⟨0, 0⟩} ⟨0, 0⟩ 2 ≠ chainSetV35 1

/-- **A v35 HISTORY THE PIN COULD NOT HAVE RUN.**  `chainRunV35` is a v35 history from the genesis
`{⟨0, 0⟩}`.  Each of its seven inserts (of `n + 1` at step `n < 7`) can be made through the leaf of
the current set with key `0`, and it is idle from step `7` on; its steps insert the values
`chainValsV35`.  Its last insert walks six hops from `⟨0, 1⟩`, which the pin's loop rejects, and
puts `7` in the tree.

This instantiates the premises `RunV35 S` and `S 0 = {⟨0, 0⟩}` (hence `SoundState (S 0)`) of
every history statement, and the step premises of `ValuesDetermineTreeV35` with
`S = S' = chainRunV35` and `vals = chainValsV35`. -/
def Properties.RunV35Satisfiable : Prop :=
  RunV35 chainRunV35 ∧ chainRunV35 0 = {⟨0, 0⟩}
    ∧ (∀ n, n < 7 → ∃ W₀ ∈ chainRunV35 n, W₀.key = 0
          ∧ InsertV35 (chainRunV35 n) ((n + 1 : ℕ) : UInt256) W₀ (chainRunV35 (n + 1)))
    ∧ (∀ n, 7 ≤ n → chainRunV35 (n + 1) = chainRunV35 n)
    ∧ (∀ n, StepV35 (chainValsV35 n) (chainRunV35 n) (chainRunV35 (n + 1)))
    ∧ WalkV35 (chainRunV35 6) 7 6 ⟨0, 1⟩ ⟨6, 0⟩
    ∧ BoundedWalkV35 (chainRunV35 6) 7 pinSearchAttemptsV35 0 ⟨0, 1⟩ none
    ∧ (7 : UInt256) ∈ keys (chainRunV35 7)

/-- **THE REMAINING HISTORY PREMISES, ON `chainRunV35`.**

* `DeliveredAvailableForeverV35`, with `t = chainClockV35`, `D = 7`, `i = 7`, `v = 7`: the clock is
  monotone, `t 7 ≤ 7`, `7` is a key of snapshot `7`, and snapshot `7` has `D < t (7 + 1)`, so the
  second conclusion is exercised there.
* `DeliveryExactlyOnceV35` with `v = 7`, `n = 7`; `SentinelHintAlwaysWorksV35` and
  `ReclaimableIffAbsentV35` with `j = 6`, `v = 7` (absent there).
* `OnceValidHintStaysValidV35` with `i = 5`, `j = 6`, `W₀ = ⟨5, 0⟩`, `v = 7`: the hint leaf
  `⟨5, 0⟩` passed the checks at snapshot `5` and is gone at snapshot `6`, where the leaf with its
  key is `⟨5, 6⟩`, and the insert through `⟨5, 6⟩` succeeds.
* For `ValuesDetermineTreeV35`, a second hint for step `6`: the insert of `7` through `⟨5, 6⟩`
  reaches the same snapshot `7` as the one through `⟨0, 1⟩` in `RunV35Satisfiable`. -/
def Properties.RunV35PremisesMetV35 : Prop :=
  Monotone chainClockV35 ∧ chainClockV35 7 ≤ 7 ∧ (7 : UInt256) < chainClockV35 (7 + 1)
    ∧ (7 : UInt256) ∈ keys (chainRunV35 7) ∧ (7 : UInt256) ∉ keys (chainRunV35 6)
    ∧ (⟨5, 0⟩ : AbsLeaf) ∈ chainRunV35 5 ∧ (⟨5, 0⟩ : AbsLeaf).key < 7
    ∧ (⟨5, 0⟩ : AbsLeaf) ∉ chainRunV35 6 ∧ (⟨5, 6⟩ : AbsLeaf) ∈ chainRunV35 6
    ∧ InsertV35 (chainRunV35 6) 7 ⟨5, 6⟩ (chainRunV35 7)

end IMTAbstract
