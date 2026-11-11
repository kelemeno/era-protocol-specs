import EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight

/-!
# Properties: the capacity premise, discharged by the run

Statements about `EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight`; proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.RunHeight`.

`TreeRoot`'s completeness and fold-correspondence results take
`T.leafCount ≤ 2 ^ height` (or `<`) for an external `height`.  Here the height is
the run's own `FullMerkle._height`, and the premise is a theorem:

* **Dimensions** — along every run from `setup`, `(_leafNumber, _height)` is
  `(leafCount, fmHeight leafCount)`: the height is a function of the leaf count, and
  `leafCount ≤ 2 ^ _height` (`HReachesCapacity`, `HRunCapacity`).  `fmHeight` is also
  not larger than needed (`FmHeightTight`).
* **The model adds nothing to `Run`** — the tree component of an `HRun` is a `Run`,
  and every `Run` from `setup` carries dimensions making it an `HRun`.
* **Fold correspondence at the source's heights** — `updateLeaf` at the old
  `_height`, then `pushNewLeaf` at the (possibly grown) new one, with the capacity
  premises of `RootAfterUpdateLeaf` / `RootAfterInsert` discharged.
* **The headlines at the run's own height** — `ProofsExclusiveOrBreak` and
  `RunRootsExclusiveOrBreak` restated at the published root: validity and capacity
  come from the run, and two completeness clauses (which need capacity) are added.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier AttackVectors.CapacityInvariant

/-! ## Dimensions along runs -/

/-- **THE HEIGHT IS A FUNCTION OF THE LEAF COUNT.**  Any state reached from `hSetup` by
guarded inserts has `_leafNumber = leafCount` and `_height = fmHeight leafCount`. -/
def Properties.HReachesDims : Prop :=
  ∀ S : HState, HReaches hSetup S →
    S.dims = ⟨S.tree.leafCount, fmHeight S.tree.leafCount⟩

/-- `n` leaves fit the height `pushNewLeaf` has grown to after `n` pushes. -/
def Properties.FmHeightCapacity : Prop :=
  ∀ n : ℕ, n ≤ 2 ^ fmHeight n

/-- **`fmHeight` IS NOT LARGER THAN NEEDED.**  For a nonempty tree, `2 ^ fmHeight n < 2n`.
Together with `FmHeightCapacity`, `fmHeight n` is the least `k` with `n ≤ 2 ^ k`, so the
capacity bound is not met by an oversized height. -/
def Properties.FmHeightTight : Prop :=
  ∀ n : ℕ, 0 < n → 2 ^ fmHeight n < 2 * n

/-- **THE CAPACITY PREMISE, DISCHARGED.**  Every state reached from `hSetup` by guarded
inserts fits its own `_height`. -/
def Properties.HReachesCapacity : Prop :=
  ∀ S : HState, HReaches hSetup S → S.tree.leafCount ≤ 2 ^ S.height

/-- The same along every run from `hSetup`, at every step. -/
def Properties.HRunDims : Prop :=
  ∀ R : ℕ → HState, HRun R → R 0 = hSetup →
    ∀ n, (R n).dims = ⟨(R n).tree.leafCount, fmHeight (R n).tree.leafCount⟩

/-- **THE CAPACITY PREMISE, DISCHARGED ALONG RUNS.** -/
def Properties.HRunCapacity : Prop :=
  ∀ R : ℕ → HState, HRun R → R 0 = hSetup → ∀ n, (R n).tree.leafCount ≤ 2 ^ (R n).height

/-- A run from `hSetup` reaches each of its states. -/
def Properties.HRunReaches : Prop :=
  ∀ R : ℕ → HState, HRun R → R 0 = hSetup → ∀ n, HReaches hSetup (R n)

/-! ## The model adds no constraint on the list state -/

/-- The list component of an `HRun` is a `Run`. -/
def Properties.HRunProjects : Prop :=
  ∀ R : ℕ → HState, HRun R → Run (fun n => (R n).tree)

/-- Every `Run` from `setup` is the list component of an `HRun` from `hSetup`. -/
def Properties.RunLiftsToHRun : Prop :=
  ∀ R : ℕ → Tree, Run R → R 0 = setup →
    ∃ D : ℕ → TreeDims, HRun (fun n => ⟨R n, D n⟩) ∧ D 0 = setupDims

/-- The list component of an `HReaches` step is a `Reaches` step. -/
def Properties.HReachesProjects : Prop :=
  ∀ S U : HState, HReaches S U → Reaches S.tree U.tree

/-- A `Reaches` step between list states lifts to an `HReaches` step between those
states paired with their source dimensions `(leafCount, fmHeight leafCount)`. -/
def Properties.ReachesLifts : Prop :=
  ∀ T U : Tree, Reaches T U →
    HReaches ⟨T, ⟨T.leafCount, fmHeight T.leafCount⟩⟩ ⟨U, ⟨U.leafCount, fmHeight U.leafCount⟩⟩

/-! ## Fold correspondence at the source's heights -/

/-- **`pushNewLeaf`'s INDEX IS BELOW THE GROWN CAPACITY.**  On a reached state, the new
leaf's index `leafCount` is below `2 ^ _height` after `pushNewLeaf` has grown it. -/
def Properties.InsertBelowOwnCapacity : Prop :=
  ∀ (S : HState) (v : UInt256) (low : ℕ), HReaches hSetup S →
    S.tree.leafCount < 2 ^ (hInsert S v low).height

/-- `RootAfterUpdateLeaf` at the run's own height (the `updateLeaf` of the low leaf runs
before `pushNewLeaf`, so at the OLD `_height`), with its capacity premise discharged. -/
def Properties.RootAfterUpdateLeafOwnHeight : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState) (low : ℕ) (x : UInt256),
    HReaches hSetup S → low < S.tree.leafCount →
    rootOf h z0 ((leafHashes hl S.tree).set low x) S.height
      = walkPure h (honestSibs h z0 (leafHashes hl S.tree) low) 0 S.height low x

/-- `RootAfterInsert` at the run's own height: the root of the state after a guarded
insert, at its own (possibly grown) `_height`, is the `pushNewLeaf` walk at that height.
Both capacity premises are discharged. -/
def Properties.RootAfterInsertOwnHeight : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState) (v : UInt256) (low : ℕ),
    HReaches hSetup S → InsertGuard S.tree v low →
    (hInsert S v low).root h z0 hl
      = walkPure h
          (honestSibs h z0
            ((leafHashes hl S.tree).set low
              (hl { S.tree.leaf low with nextIndex := S.tree.leafCount, nextValue := v }))
            S.tree.leafCount)
          0 (hInsert S v low).height S.tree.leafCount
          (hl ⟨v, (S.tree.leaf low).nextIndex, (S.tree.leaf low).nextValue⟩)

/-! ## The headlines at the run's own height -/

/-- **`ProofsExclusiveOrBreak` AT THE PUBLISHED ROOT, WITH COMPLETENESS.**  On any state
reached from `hSetup`, against its root at its own `_height`, for every node hash, leaf
hash and padding constant:

1. every value the tree holds has the honest inclusion proof (`merklePath` of an occupied
   index carrying it), accepted, with no located break;
2. every nonzero value the tree does not hold has an honest non-inclusion proof (the
   `merklePath` of an occupied low leaf), accepted, with no located break;
3. if a value has both an accepted inclusion proof and an accepted non-inclusion proof,
   one of the two submitted paths carries a located `TreeRootBreak`.

`Valid` (a premise of `ProofsExclusiveOrBreak`) and capacity (needed by 1 and 2) come
from the run. -/
def Properties.ProofsExclusiveOrBreakAtOwnHeight : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : HState), HReaches hSetup S →
    (∀ v : UInt256, v ∈ keys (toAbs S.tree) →
      ∃ i < S.tree.leafCount, (S.tree.leaf i).value = v
        ∧ InclusionAccepted h hl (S.root h z0 hl) v (S.tree.leaf i) i
            (honestSibs h z0 (leafHashes hl S.tree) i) S.height
        ∧ ¬ TreeRootBreak h z0 hl S.tree S.height (honestSibs h z0 (leafHashes hl S.tree) i)
            S.height i (S.tree.leaf i))
    ∧ (∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs S.tree) →
      ∃ i < S.tree.leafCount,
        NonInclusionAccepted h hl (S.root h z0 hl) v (S.tree.leaf i) i
            (honestSibs h z0 (leafHashes hl S.tree) i) S.height
        ∧ ¬ TreeRootBreak h z0 hl S.tree S.height (honestSibs h z0 (leafHashes hl S.tree) i)
            S.height i (S.tree.leaf i))
    ∧ (∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      InclusionAccepted h hl (S.root h z0 hl) v ℓ₁ i₁ s₁ k₁ →
      NonInclusionAccepted h hl (S.root h z0 hl) v ℓ₂ i₂ s₂ k₂ →
        TreeRootBreak h z0 hl S.tree S.height s₁ k₁ i₁ ℓ₁
          ∨ TreeRootBreak h z0 hl S.tree S.height s₂ k₂ i₂ ℓ₂)

/-- **`RunRootsExclusiveOrBreak` AT EACH STEP'S PUBLISHED ROOT, WITH COMPLETENESS.**  The
three clauses of `ProofsExclusiveOrBreakAtOwnHeight`, at every step `n` of every run from
`hSetup`, against the root at that step's own `_height`. -/
def Properties.RunRootsExclusiveOrBreakAtOwnHeight : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∀ n : ℕ,
    (∀ v : UInt256, v ∈ keys (toAbs (R n).tree) →
      ∃ i < (R n).tree.leafCount, ((R n).tree.leaf i).value = v
        ∧ InclusionAccepted h hl ((R n).root h z0 hl) v ((R n).tree.leaf i) i
            (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height
        ∧ ¬ TreeRootBreak h z0 hl (R n).tree (R n).height
            (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height i ((R n).tree.leaf i))
    ∧ (∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs (R n).tree) →
      ∃ i < (R n).tree.leafCount,
        NonInclusionAccepted h hl ((R n).root h z0 hl) v ((R n).tree.leaf i) i
            (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height
        ∧ ¬ TreeRootBreak h z0 hl (R n).tree (R n).height
            (honestSibs h z0 (leafHashes hl (R n).tree) i) (R n).height i ((R n).tree.leaf i))
    ∧ (∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      InclusionAccepted h hl ((R n).root h z0 hl) v ℓ₁ i₁ s₁ k₁ →
      NonInclusionAccepted h hl ((R n).root h z0 hl) v ℓ₂ i₂ s₂ k₂ →
        TreeRootBreak h z0 hl (R n).tree (R n).height s₁ k₁ i₁ ℓ₁
          ∨ TreeRootBreak h z0 hl (R n).tree (R n).height s₂ k₂ i₂ ℓ₂)

/-! ## Anti-vacuity -/

/-- **THE PREMISES ARE SATISFIABLE, WITH THE HEIGHT GROWING.**  For `0 < a < b`,
`hThreeRun a b` is an `HRun` from `hSetup`; its `_height` is `0, 1, 2` at steps
`0, 1, 2` (both inserts take the growing branch of `pushNewLeaf`, the `setup` push the
non-growing one); every step is reached; and step 2 is `threeLeafTree a b` with three
leaves at height 2, one slot below capacity. -/
def Properties.HThreeRunWitness : Prop :=
  ∀ a b : UInt256, 0 < a → a < b →
    HRun (hThreeRun a b) ∧ hThreeRun a b 0 = hSetup
      ∧ (∀ n, HReaches hSetup (hThreeRun a b n))
      ∧ setupDims = ⟨1, 0⟩
      ∧ (hThreeRun a b 0).height = 0 ∧ (hThreeRun a b 1).height = 1
      ∧ (hThreeRun a b 2).height = 2
      ∧ (hThreeRun a b 2).tree = threeLeafTree a b
      ∧ (hThreeRun a b 2).tree.leafCount = 3
      ∧ (hThreeRun a b 2).tree.leafCount < 2 ^ (hThreeRun a b 2).height

/-- **THE PADDING FORGERY IS LIVE AT THE SOURCE'S OWN HEIGHT.**  `threeLeafTree a b` is
published at height 2 by the source's own growth rule, not by a choice of the
statement.  With the extraction-pin padding `hl ⟨0,0,0⟩`, against `hThree a b`'s root at
its own height, `a` has an accepted honest inclusion proof (leaf 1) with no located break
AND an accepted non-inclusion proof (slot 3), whose located break is exactly
`paddingHit`.  So clause 3 of `ProofsExclusiveOrBreakAtOwnHeight` has its premises met on
a reached state, and its first break disjunct is false there.  `hThree a b` is step 2
of `hThreeRun a b`, so the same holds for `RunRootsExclusiveOrBreakAtOwnHeight`. -/
def Properties.PaddingForgeryAtOwnHeight : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    HReaches hSetup (hThree a b) ∧ hThreeRun a b 2 = hThree a b ∧ (hThree a b).height = 2
      ∧ InclusionAccepted h hl ((hThree a b).root h (hl ⟨0, 0, 0⟩) hl) a
          ((hThree a b).tree.leaf 1) 1
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 1) (hThree a b).height
      ∧ NonInclusionAccepted h hl ((hThree a b).root h (hl ⟨0, 0, 0⟩) hl) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 3) (hThree a b).height
      ∧ ¬ TreeRootBreak h (hl ⟨0, 0, 0⟩) hl (hThree a b).tree (hThree a b).height
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 1) (hThree a b).height 1
          ((hThree a b).tree.leaf 1)
      ∧ TreeRootBreakExactly h (hl ⟨0, 0, 0⟩) hl (hThree a b).tree (hThree a b).height
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (hThree a b).tree) 3) (hThree a b).height 3
          ⟨0, 0, 0⟩ .paddingHit

end Contracts.InteropCommitmentTree
