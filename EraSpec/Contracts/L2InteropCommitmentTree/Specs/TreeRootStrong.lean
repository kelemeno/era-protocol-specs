import EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRoot
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight

/-!
# Spec: the query log of one verification, and a hash premise pinned to it

## Why this topic exists

`Properties/TreeRoot.lean` states seven soundness results under `HashAssumptions`:
`AcceptedPathPinsLeaf`, `InclusionSound`, `NonInclusionSound`,
`VerifiedAbsenceExcludesDelivered`, `ProofsExclusive`, `RunRootsExclusive` and
`VerifiedAbsenceIsWitness`. `HashAssumptions.nodeInj` asks a map
`UInt256 → UInt256 → UInt256` to be injective on all `2^512` pairs, so no hash meets the
bundle (`HashAssumptionsUnsatisfiable`) and all seven are vacuously true. Their
`…OrBreak` restatements take no hash premise and conclude "the property, or a located
`TreeRootBreak`".

This topic restates the seven with their ORIGINAL conclusions, under a premise that a
hash can meet. `TreeRootStrongLogSafe` keeps each field of `HashAssumptions`, but only
on the finitely many values that one verification touches:

* **The query log.** `treeRootStrongWalkLog` holds the `k` pairs the verifier
  (`Merkle.calculateRootMemory`) hashes along the submitted path.
  `treeRootStrongTreeLog` holds the pairs `FullMerkle` hashes to build the root that
  path is checked against: at each level `l < height`, the pair under each of the
  `2 ^ (height - l - 1)` parents. So the log has at most `k + 2 ^ height` pairs
  (`Properties.TreeRootStrongLogBounded`).
* **The pinned premise** `TreeRootStrongLogSafe`, field by field against the
  `HashAssumptions` field it replaces:
  - `nodeInjOn` (for `nodeInj`): the node hash has no collision among the logged pairs;
  - `shortSeparated` (for `leafNotNode`): if the submitted path is shorter than the
    height, the presented leaf hash is not the node hash of a pair in the tree log;
  - `longSeparated` (for `leafNotNode`, `padNotNode`): if the submitted path is longer
    than the height, no level-0 entry (a stored leaf hash or the padding constant) is
    the node hash of a pair in the walk log;
  - `openedLeafInj` (for `leafInj`): if the opened index is occupied, the stored leaf
    and the presented leaf do not collide under the leaf hash;
  - `padNotPresented` (for `padNotLeaf`): if the opened index is empty, the presented
    leaf does not hash to the padding constant.

Every compared value is a function of the instance (the tree, the height, the
submitted siblings, length, index and leaf), so the premise can hold. It holds on every
honest proof as soon as the tree's own log has no node-hash collision
(`Properties.TreeRootStrongHonestLogSafeIff`), whatever the padding constant, and the
concrete instance `Properties.TreeRootStrongWitness` meets it at the extraction pin's
padding. It fails on the pin's forged absence proof, for every hash
(`Properties.TreeRootStrongPinForgeryFailsLogSafe`); when the tree's own log has no
node-hash collision, the padding clause `padNotPresented` (the clause the
`IMT_EMPTY_LEAF_HASH` fix is about) is the only one it fails
(`Properties.TreeRootStrongPinForgeryFailsOnlyPadding`). With a dedicated padding
constant 7 and the witness hash pair, the same forgery on `threeLeafTree 1 2` meets it,
and is rejected (`Properties.TreeRootStrongDedicatedPaddingWitness`).

## What this does not assume or prove

* Nothing about `keccak`. `TreeRootStrongLogSafe` is a hypothesis of each result, as
  `HashAssumptions` was; the difference is that it can be true. Whether `keccak` meets it
  on a given instance is a question about named inputs only: no collision among at most
  `k + 2 ^ height` pairs, and no equality between a few named values (the presented leaf
  hash, the stored leaf hashes, the padding constant) and node hashes of logged pairs.
  That question is outside this package.
* The stored-root correspondence (O7) is as in `TreeRoot`: the root is the fold
  `root h z0 hl T height`.

## The witness hash pair

`treeRootStrongWitnessNodeHash` and `treeRootStrongWitnessLeafHash` are small affine
maps, not models of `keccak`. They are here only to show that `TreeRootStrongLogSafe`
is satisfiable on a real run state, by honest proofs and by an attack: on
`threeLeafTree 1 2` at height 2 the relevant logs have no collision, which `decide`
checks pair by pair.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier

/-! ## The query log -/

/-- **The verifier's log.** The pairs `Merkle.calculateRootMemory` hashes on a submitted
path of length `k` from index `idx` with item hash `x`: the pair `walkPair` at each step
`i < k`. -/
def treeRootStrongWalkLog (h : Hash) (sibs : ℕ → UInt256) (k idx : ℕ) (x : UInt256) :
    Finset (UInt256 × UInt256) :=
  (Finset.range k).image (walkPair h sibs 0 idx x)

/-- **The tree's log.** The pairs `FullMerkle` hashes to build the root at `height` over
the level-0 list `L`: at each level `l < height`, the pair `treePair` under each parent
`m < 2 ^ (height - l - 1)` (padding read as the level's zero). A parent above only empty
slots contributes the zero pair `(zeros l, zeros l)`, which `setup` hashes into
`_zeros`. -/
def treeRootStrongTreeLog (h : Hash) (z0 : UInt256) (L : List UInt256) (height : ℕ) :
    Finset (UInt256 × UInt256) :=
  (Finset.range height).biUnion fun l =>
    (Finset.range (2 ^ (height - l - 1))).image fun m => treePair h z0 L l (2 * m)

/-- **No node-hash collision on the finite set `S` of pairs.** -/
def TreeRootStrongPairInjOn (h : Hash) (S : Finset (UInt256 × UInt256)) : Prop :=
  ∀ p ∈ S, ∀ q ∈ S, h p.1 p.2 = h q.1 q.2 → p = q

/-! ## The pinned premise -/

/-- **The hash premise, pinned to one verification.** For the proof
`(sibs, k, idx, ℓ)` checked against `root h z0 hl T height`: each field of
`HashAssumptions`, restricted to the values this verification touches. See the module
docstring for the field-by-field correspondence. -/
structure TreeRootStrongLogSafe (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree)
    (height : ℕ) (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) : Prop where
  /-- No node-hash collision among the pairs the verifier and the tree hash. -/
  nodeInjOn : TreeRootStrongPairInjOn h
    (treeRootStrongWalkLog h sibs k idx (hl ℓ)
      ∪ treeRootStrongTreeLog h z0 (leafHashes hl T) height)
  /-- A short path does not present the node hash of a tree pair as its leaf hash. -/
  shortSeparated : k < height →
    ∀ p ∈ treeRootStrongTreeLog h z0 (leafHashes hl T) height, hl ℓ ≠ h p.1 p.2
  /-- On a long path, no level-0 entry (the padding constant or a stored leaf hash) is
  the node hash of a pair the verifier hashes. -/
  longSeparated : height < k →
    ∀ p ∈ treeRootStrongWalkLog h sibs k idx (hl ℓ),
      ∀ y ∈ z0 :: leafHashes hl T, y ≠ h p.1 p.2
  /-- The leaf stored at an occupied opened index and the presented leaf do not collide
  under the leaf hash. -/
  openedLeafInj : idx < T.leafCount → hl (T.leaf idx) = hl ℓ → T.leaf idx = ℓ
  /-- At an empty opened index, the presented leaf does not hash to the padding
  constant. -/
  padNotPresented : T.leafCount ≤ idx → hl ℓ ≠ z0

/-! ## The witness hash pair -/

/-- Witness node hash: `3a + 7b + 1` modulo `2^256`. Not a model of `keccak`. -/
def treeRootStrongWitnessNodeHash : Hash := fun a b => 3 * a + 7 * b + 1

/-- Witness leaf hash: `1000·value + 100·nextIndex + 10·nextValue + 5` modulo `2^256`.
Not a model of `keccak`. Its value on the sentinel `{0,0,0}` is `5`, the padding
constant at the extraction pin. -/
def treeRootStrongWitnessLeafHash : LeafHash := fun ℓ =>
  1000 * ℓ.value + 100 * (ℓ.nextIndex : UInt256) + 10 * ℓ.nextValue + 5

end Contracts.InteropCommitmentTree
