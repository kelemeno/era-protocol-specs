import EraSpec.Contracts.L2InteropCommitmentTree.Specs.CachedRoot

/-!
# Properties: the stored root is the published root

Statements about `EraSpec.Contracts.L2InteropCommitmentTree.Specs.CachedRoot`; proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.CachedRoot`.

`RunHeight` publishes `HState.root`, the fold over the leaf hashes at `_height`, and
records as an assumption (O7) that this is what `IndexedMerkleTree.root()` returns.
Here the whole `FullMerkle` storage is carried and moved by the transcribed library
calls.  So the assumption becomes a theorem about the transcription:

* **The calls.**  `setup` caches the sentinel tree.  A guarded `insert` never reverts
  inside `FullMerkle`, keeps the storage caching the leaf hashes, moves the counters as
  `hInsert` does, and returns the fold.
* **Along runs.**  On every reached state, and at every step of every run,
  `IndexedMerkleTree.root()` is `HState.root` at the state's own `_height`.  The value
  `insert` returns is that root too, and it is the `pushNewLeaf` walk that
  `RootAfterInsertOwnHeight` describes.  Every state and every run of `RunHeight` is the
  view of one with whole storage, so the model gives up nothing.
* **The headline against the contract's own root and paths.**  The three clauses of
  `ProofsExclusiveOrBreakAtOwnHeight` hold against the root the storage holds, with the
  honest proofs being the contract's own `merklePath` outputs.
* **Anti-vacuity.**  On the three-leaf run with whole storage, both later inserts
  grow the height.  The padding forgery for a delivered value is accepted against the
  contract's own stored root, while the contract's `merklePath` refuses to produce that
  path.

The padding constant is the pin's `hashLeaf({0,0,0})` (`zeroLeafHash`) throughout, as the
source sets it.  No hash premise is used.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier

/-! ## The calls -/

/-- **`setup` CACHES THE SENTINEL TREE.**  `IndexedMerkleTree.setup` on fresh storage does
not revert, gives the sentinel list state with the dimensions `hSetup` carries, and leaves
`FullMerkle`'s storage caching the one leaf hash `hashLeaf({0,0,0})`, padded with that
same constant. -/
def Properties.CSetupCaches : Prop :=
  ∀ (h : Hash) (hl : LeafHash), ∃ S : CState, cSetup h hl = some S ∧ S.tree = setup
    ∧ S.toH = hSetup ∧ FullMerkle.Represents h (zeroLeafHash hl) (leafHashes hl S.tree) S.fm

/-- **AN `insert` AT AN OCCUPIED LOW LEAF NEVER REVERTS IN `FullMerkle`, AND RETURNS THE
FOLD.**  If the storage caches the leaf hashes of the list state (for any padding `z0`)
and `low` is occupied (`InsertGuard.inBounds`), then `updateLeaf(low, …)` followed by
`pushNewLeaf(…)` does not revert.  The list state becomes `insert`, the counters move as
`hInsert` moves them, the storage caches the new leaf hashes, and `newRoot` is the fold
over them at the new `_height`. -/
def Properties.CInsertCaches : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (S : CState) (v : UInt256) (low : ℕ),
    FullMerkle.Represents h z0 (leafHashes hl S.tree) S.fm → low < S.tree.leafCount →
    ∃ (S' : CState) (r : UInt256), cInsert h hl S v low = some (S', r)
      ∧ S'.tree = insert S.tree v low ∧ S'.toH = hInsert S.toH v low
      ∧ FullMerkle.Represents h z0 (leafHashes hl S'.tree) S'.fm
      ∧ r = root h z0 hl S'.tree S'.fm.height

/-! ## Along runs -/

/-- **ON EVERY REACHED STATE, `root()` IS THE PUBLISHED ROOT.**  A state reached from
`setup` by guarded inserts has a `RunHeight` view reached from `hSetup`, its storage
caches its leaf hashes, and `IndexedMerkleTree.root()` returns `HState.root` of the view,
at its own `_height`, with the pin's padding.  This discharges, for the transcription,
the assumption `RunHeight` records under O7. -/
def Properties.CReachesRootIsPublished : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (S : CState), CReaches h hl S →
    HReaches hSetup S.toH
      ∧ FullMerkle.Represents h (zeroLeafHash hl) (leafHashes hl S.tree) S.fm
      ∧ S.root = some (S.toH.root h (zeroLeafHash hl) hl)

/-- **THE SAME AT EVERY STEP OF EVERY RUN.** -/
def Properties.CRunRootIsPublished : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (R : ℕ → CState), CRun h hl R → cSetup h hl = some (R 0) →
    ∀ n, CReaches h hl (R n) ∧ HReaches hSetup (R n).toH
      ∧ (R n).root = some ((R n).toH.root h (zeroLeafHash hl) hl)

/-- **`insert` RETURNS THE STORED ROOT, WHICH IS THE PUBLISHED ONE.**  From a reached
state, a guarded insert does not revert.  Its `newRoot` is what `root()` reads afterwards,
and it is `HState.root` of `hInsert`: the left-hand side of `RootAfterInsertOwnHeight`. -/
def Properties.CInsertReturnsPublishedRoot : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (S : CState) (v : UInt256) (low : ℕ),
    CReaches h hl S → InsertGuard S.tree v low →
    ∃ (S' : CState) (r : UInt256), cInsert h hl S v low = some (S', r) ∧ CReaches h hl S'
      ∧ S'.toH = hInsert S.toH v low ∧ S'.root = some r
      ∧ r = (hInsert S.toH v low).root h (zeroLeafHash hl) hl

/-- **`insert` RETURNS THE `pushNewLeaf` WALK.**  Combined with `RootAfterInsertOwnHeight`:
the `newRoot` a guarded insert returns from a reached state is the walk from the frontier
index `leafCount`, over the post-`updateLeaf` tree's honest siblings, at the new `_height`.
This is the statement O7 had narrowed the source side to (`RootAfterInsert`), now about
the transcribed library's return value. -/
def Properties.CInsertReturnsTheWalk : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (S S' : CState) (v : UInt256) (low : ℕ) (r : UInt256),
    CReaches h hl S → InsertGuard S.tree v low → cInsert h hl S v low = some (S', r) →
    r = walkPure h
          (honestSibs h (zeroLeafHash hl)
            ((leafHashes hl S.tree).set low
              (hl { S.tree.leaf low with nextIndex := S.tree.leafCount, nextValue := v }))
            S.tree.leafCount)
          0 S'.fm.height S.tree.leafCount
          (hl ⟨v, (S.tree.leaf low).nextIndex, (S.tree.leaf low).nextValue⟩)

/-- **THE MODEL LOSES NO STATE.**  Every state `RunHeight` reaches from `hSetup` is the view
of a state reached with whole storage. -/
def Properties.HReachesLifts : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (S : HState), HReaches hSetup S →
    ∃ C : CState, CReaches h hl C ∧ C.toH = S

/-- **THE MODEL LOSES NO RUN.**  Every run `RunHeight` makes from `hSetup` is, step by
step, the view of a run with whole storage from `setup`.  So `RunRootsExclusiveOrBreakAtOwnHeight`
and the results here talk about the same runs. -/
def Properties.HRunLiftsToCRun : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (R : ℕ → HState), HRun R → R 0 = hSetup →
    ∃ C : ℕ → CState, CRun h hl C ∧ cSetup h hl = some (C 0) ∧ ∀ n, (C n).toH = R n

/-! ## The headline against the contract's own root and paths -/

/-- **`ProofsExclusiveOrBreakAtOwnHeight` AGAINST THE STORED ROOT, WITH THE CONTRACT'S OWN
PATHS.**  On any reached state, `root()` returns some `R`, and for every node hash and
leaf hash:

1. every value the tree holds sits at an occupied index `i` whose `merklePath(i)` is a
   path of length `_height` that is accepted as an inclusion proof against `R`, with no
   located break;
2. every nonzero value the tree does not hold has an occupied low leaf `i` whose
   `merklePath(i)` is accepted as a non-inclusion proof against `R`, with no located
   break;
3. if a value has both an accepted inclusion proof and an accepted non-inclusion proof
   against `R`, one of the two submitted paths carries a located `TreeRootBreak`. -/
def Properties.ContractProofsAtStoredRoot : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (S : CState), CReaches h hl S →
    ∃ R : UInt256, S.root = some R
      ∧ (∀ v : UInt256, v ∈ keys (toAbs S.tree) →
          ∃ i < S.tree.leafCount, (S.tree.leaf i).value = v
            ∧ ∃ p : List UInt256, S.merklePath i = some p ∧ p.length = S.fm.height
              ∧ InclusionAccepted h hl R v (S.tree.leaf i) i (FullMerkle.pathSibs p) p.length
              ∧ ¬ TreeRootBreak h (zeroLeafHash hl) hl S.tree S.fm.height (FullMerkle.pathSibs p)
                  p.length i (S.tree.leaf i))
      ∧ (∀ v : UInt256, v ≠ 0 → v ∉ keys (toAbs S.tree) →
          ∃ i < S.tree.leafCount,
            ∃ p : List UInt256, S.merklePath i = some p ∧ p.length = S.fm.height
              ∧ NonInclusionAccepted h hl R v (S.tree.leaf i) i (FullMerkle.pathSibs p) p.length
              ∧ ¬ TreeRootBreak h (zeroLeafHash hl) hl S.tree S.fm.height (FullMerkle.pathSibs p)
                  p.length i (S.tree.leaf i))
      ∧ (∀ (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
          InclusionAccepted h hl R v ℓ₁ i₁ s₁ k₁ → NonInclusionAccepted h hl R v ℓ₂ i₂ s₂ k₂ →
            TreeRootBreak h (zeroLeafHash hl) hl S.tree S.fm.height s₁ k₁ i₁ ℓ₁
              ∨ TreeRootBreak h (zeroLeafHash hl) hl S.tree S.fm.height s₂ k₂ i₂ ℓ₂)

/-! ## Anti-vacuity -/

end Contracts.InteropCommitmentTree
