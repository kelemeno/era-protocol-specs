import EraSpec.Contracts.TreeRoot
import EraSpec.Contracts.Protocol

/-!
# Properties: the root and the two proof gates

Statements about `EraSpec.Contracts.TreeRoot` — the root `FullMerkle` publishes
and the verifiers `verifyInclusion` / `verifyNonInclusion`.  Proofs are in
`EraSpec.Proofs.TreeRoot`.

Three groups:

* **Fold correspondence** — what "the root after `insert`" means in terms of the
  list state: `insert`'s two hash-tree writes are a `List.set` followed by an
  append, and the resulting root is the `pushNewLeaf` walk.  This is the
  protocol half of root-binding piece (2) in `AttackVectors.RootBinding`; the
  compiled half stays in the sibling repo (obligation O7).
* **Soundness and completeness** — an accepted proof, for ANY index and path
  length the prover chose, names an occupied index holding the presented leaf;
  and every honest proof is accepted.  This closes root-binding piece (3): the
  leaves a verified proof talks about are the leaves `toAbs` talks about, so the
  `W ∈ s` hypothesis that `IMTAbstract.forged_padding_witness_breaks_exclusivity`
  proves indispensable is DISCHARGED from the Merkle check rather than assumed.
* **The padding countermodel** — `HashAssumptions.padNotLeaf` is false at the
  extraction pin (`setup` pads with `hashLeaf({0,0,0})`), and the consequence is
  a forged absence proof for a delivered leg, on a real contract run, with no
  hash assumption at all.  Later era-contracts revisions pad with a dedicated
  `IMT_EMPTY_LEAF_HASH`; `PaddingCollisionRefundsDeliveredLeg` is what that
  constant buys.
-/

namespace Properties.TreeRoot

open IMTAbstract MerkleSpec MerkleSpec.Verifier
open Contracts.InteropCommitmentTree Contracts.Protocol

/-! ## Fold correspondence -/

/-- `insert` is `updateLeaf` then `pushNewLeaf` on the leaf-hash list: a
`List.set` at the low index followed by an append — the two operations
`MerkleSpec` analyses as M-A and M-B. -/
def LeafHashesInsert : Prop :=
  ∀ (hl : LeafHash) (T : Tree) (v : UInt256) (low : ℕ), low < T.leafCount →
    leafHashes hl (insert T v low)
      = (leafHashes hl T).set low (hl { T.leaf low with nextIndex := T.leafCount, nextValue := v })
          ++ [hl ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩]

/-- The intermediate root `updateLeaf(low, x)` returns is the update walk from
`low` over the OLD tree's siblings (what the contract reads from storage). -/
def RootAfterUpdateLeaf : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (low : ℕ) (x : UInt256) (height : ℕ),
    low < T.leafCount → T.leafCount ≤ 2 ^ height →
    rootOf h z0 ((leafHashes hl T).set low x) height
      = walkPure h (honestSibs h z0 (leafHashes hl T) low) 0 height low x

/-- The root after `insert` is the `pushNewLeaf` walk from the frontier index
`leafCount` over the post-`updateLeaf` tree, with the new leaf's hash as the
accumulator — exactly the walk the contract performs. -/
def RootAfterInsert : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (v : UInt256) (low height : ℕ),
    low < T.leafCount → T.leafCount < 2 ^ height →
    root h z0 hl (insert T v low) height
      = walkPure h
          (honestSibs h z0
            ((leafHashes hl T).set low (hl { T.leaf low with nextIndex := T.leafCount, nextValue := v }))
            T.leafCount)
          0 height T.leafCount (hl ⟨v, (T.leaf low).nextIndex, (T.leaf low).nextValue⟩)

/-! ## Soundness -/

/-- An accepted path names an occupied index holding the presented leaf.
Whatever index and path length the prover chose: the length is the tree's
height, the index is below `leafCount`, and the leaf stored there IS the
presented preimage. -/
def AcceptedPathPinsLeaf : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Tree) (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf),
      PathAccepts h (root h z0 hl T height) sibs k idx (hl ℓ) →
      k = height ∧ idx < T.leafCount ∧ T.leaf idx = ℓ

/-- A verified inclusion proof means delivered: the value is a key of the tree's
projection. -/
def InclusionSound : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      InclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k → v ∈ keys (toAbs T)

/-- A verified non-inclusion proof is a reclaim witness IN the tree: the low leaf
is a member of `toAbs T` with a window straddling `v`. -/
def NonInclusionSound : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Tree) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k →
      ∃ W ∈ toAbs T, W.key < v ∧ (W.nextKey = 0 ∨ v < W.nextKey)

/-- A delivered value has no verified absence proof against a valid tree's root. -/
def VerifiedAbsenceExcludesDelivered : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Tree), Valid T →
    ∀ (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx sibs k → v ∉ keys (toAbs T)

/-- **The headline for the hash side.**  No value has both an accepted inclusion
proof and an accepted non-inclusion proof against a valid tree's root, whatever
leaves, indices, paths and path lengths the two provers present. -/
def ProofsExclusive : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Tree), Valid T →
    ∀ (height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      ¬ (InclusionAccepted h hl (root h z0 hl T height) v ℓ₁ i₁ s₁ k₁
          ∧ NonInclusionAccepted h hl (root h z0 hl T height) v ℓ₂ i₂ s₂ k₂)

/-- The same at every step of every run from `setup`: validity is not assumed,
it is inherited from the run. -/
def RunRootsExclusive : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (R : ℕ → Tree), Run R → R 0 = setup →
    ∀ (n height : ℕ) (v : UInt256) (ℓ₁ ℓ₂ : Leaf) (i₁ i₂ : ℕ) (s₁ s₂ : ℕ → UInt256) (k₁ k₂ : ℕ),
      ¬ (InclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₁ i₁ s₁ k₁
          ∧ NonInclusionAccepted h hl (root h z0 hl (R n) height) v ℓ₂ i₂ s₂ k₂)

/-- The multi-chain hook: a non-inclusion proof verified against chain `c`'s root
is an `AbsenceWitnessAt` for `c`, so the `Protocol` results apply to
root-verified proofs verbatim. -/
def VerifiedAbsenceIsWitness : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash), HashAssumptions h z0 hl →
    ∀ (T : Chain → Tree) (c : Chain) (height : ℕ) (v : UInt256) (ℓ : Leaf) (idx : ℕ)
      (sibs : ℕ → UInt256) (k : ℕ),
      NonInclusionAccepted h hl (root h z0 hl (T c) height) v ℓ idx sibs k →
      AbsenceWitnessAt (ofChains T) c v

/-! ## Completeness

Soundness alone would be satisfied by a verifier that rejects everything.  These
need the capacity invariant `leafCount ≤ 2^height`, which `pushNewLeaf`
maintains by growing the height; soundness did not. -/

/-- Every occupied leaf has an accepted inclusion proof for its value: the
honest path (`FullMerkle.merklePath`) at the tree's height. -/
def InclusionComplete : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ), T.leafCount ≤ 2 ^ height →
    ∀ i : ℕ, i < T.leafCount →
      InclusionAccepted h hl (root h z0 hl T height) (T.leaf i).value (T.leaf i) i
        (honestSibs h z0 (leafHashes hl T) i) height

/-- Every absent nonzero value has an accepted non-inclusion proof: the leaf with
the maximal key below it is a valid low leaf, and its honest path verifies. -/
def NonInclusionComplete : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree), Valid T →
    ∀ (height : ℕ), T.leafCount ≤ 2 ^ height → ∀ (v : UInt256), v ≠ 0 → v ∉ keys (toAbs T) →
      ∃ (ℓ : Leaf) (idx : ℕ),
        NonInclusionAccepted h hl (root h z0 hl T height) v ℓ idx
          (honestSibs h z0 (leafHashes hl T) idx) height

/-! ## The padding countermodel -/

/-- Without padding separation, every empty slot is a universal low leaf: in any
tree with an empty slot below capacity, the honest sibling path for that slot is
accepted by `verifyNonInclusion` with `{0,0,0}` as the low leaf, for EVERY
nonzero value.  No hash assumption is used — the proof is honest. -/
def PaddingCollisionForgesAbsence : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (T : Tree) (height : ℕ), T.leafCount < 2 ^ height →
    ∀ v : UInt256, 0 < v →
      NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl T height) v ⟨0, 0, 0⟩ T.leafCount
        (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl T) T.leafCount) height

/-- The padding collision refunds a delivered leg.  A real run from `setup` (two
guarded inserts, so the tree is `Valid`) has `a` delivered, and yet — with
`hashLeaf({0,0,0})` as the padding constant — `verifyNonInclusion` accepts an
absence proof for `a` against the tree's own root at its own height.  This is
the double spend the `IMT_EMPTY_LEAF_HASH` fix removes. -/
def PaddingCollisionRefundsDeliveredLeg : Prop :=
  ∀ (h : Hash) (hl : LeafHash) (a b : UInt256), 0 < a → a < b →
    Valid (threeLeafTree a b)
      ∧ a ∈ keys (toAbs (threeLeafTree a b))
      ∧ NonInclusionAccepted h hl (root h (hl ⟨0, 0, 0⟩) hl (threeLeafTree a b) 2) a ⟨0, 0, 0⟩ 3
          (honestSibs h (hl ⟨0, 0, 0⟩) (leafHashes hl (threeLeafTree a b)) 3) 2

end Properties.TreeRoot
