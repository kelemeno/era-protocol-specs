import EraSpec.Contracts.Merkle.Specs.Verifier
import EraSpec.Contracts.Merkle.Specs.PathCollision
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.Model

/-!
# Model: the root, and the two proof gates over it

`Contracts.InteropCommitmentTree` carries the LIST state of the indexed Merkle
tree.  This file adds the hash side: the root `FullMerkle` publishes over that
state, and the two verifiers `IndexedMerkleTree.verifyInclusion` /
`verifyNonInclusion` exactly as they consume an attacker-supplied proof.

**This file is definitions only.**  Soundness, completeness and the padding
countermodel are stated in `EraSpec.Contracts.L2InteropCommitmentTree.Properties.TreeRoot` and proved in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.TreeRoot`.

## What the verifier does and does not check

`Merkle.calculateRootMemory(path, index, itemHash)` is a pure function of a
32-byte root.  It checks `index < 2^path.length` and `path.length < 256`, folds
the path, and compares.  It does NOT know how many leaves the tree has or how
high it is, so it checks neither that `index` is occupied nor that `path.length`
is the tree's height.  `PathAccepts` records exactly this — the path length `k`
and the index are the prover's — so that whatever is proved about it is proved
about the verifier as deployed.

## The hash assumptions

`HashAssumptions` isolates every cryptographic idealization the soundness
argument needs.  Two of them are domain-separation facts the source relies on
but does not state as code:

* `leafNotNode` — a leaf hash is never a node hash.  The content of the
  `hashLeaf` comment that the preimage must not be 64 bytes long (it is 96).
* `padNotLeaf` — the `FullMerkle` padding constant is never a leaf hash.  **This
  is false at the extraction pin**, whose `setup` pads with `hashLeaf({0,0,0})`;
  later era-contracts revisions pad with a dedicated `IMT_EMPTY_LEAF_HASH`.
  `threeLeafTree` below is the concrete run on which the properties file exhibits
  the resulting forged absence proof.
-/

namespace Contracts.InteropCommitmentTree

open IMTAbstract MerkleSpec MerkleSpec.Verifier

/-! ## The leaf-hash list and the root -/

/-- `hashLeaf`, abstractly: `keccak256(abi.encode(value, nextIndex, nextValue))`. -/
abbrev LeafHash := Leaf → UInt256

/-- Level 0 of the `FullMerkle` tree: the occupied leaves' hashes, in index order. -/
def leafHashes (hl : LeafHash) (T : Tree) : List UInt256 :=
  (List.range T.leafCount).map (fun i => hl (T.leaf i))

/-- The root `FullMerkle` publishes: the Merkle fold over the leaf hashes at the
tree's current height. -/
def root (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ) : UInt256 :=
  rootOf h z0 (leafHashes hl T) height

/-! ## The verifiers -/

/-- `Merkle.calculateRootMemory(path, index, itemHash) == root`, together with its
`MerkleIndexOutOfBounds` check.  The path length `k` and the index are the
prover's; nothing here says `k` is the tree's height or that `idx` is occupied. -/
structure PathAccepts (h : Hash) (R : UInt256) (sibs : ℕ → UInt256) (k idx : ℕ) (x : UInt256) :
    Prop where
  inBounds : idx < 2 ^ k
  recompute : walkPure h sibs 0 k idx x = R

/-- `IndexedMerkleTree.verifyInclusion` returning `true`: the presented leaf
carries the value, and its path recomputes the root. -/
structure InclusionAccepted (h : Hash) (hl : LeafHash) (R v : UInt256) (ℓ : Leaf) (idx : ℕ)
    (sibs : ℕ → UInt256) (k : ℕ) : Prop where
  valueMatch : ℓ.value = v
  path : PathAccepts h R sibs k idx (hl ℓ)

/-- `IndexedMerkleTree.verifyNonInclusion` returning `true`: the three reverts
(`IMTValueZero`, `IMTLowLeafValueTooLarge`, `IMTLowLeafNextTooSmall`) did not
fire, and the low leaf's path recomputes the root.  Note the window is STRICT
here — `nextValue != 0 && nextValue <= value` reverts — unlike the insert loop's
weak exit. -/
structure NonInclusionAccepted (h : Hash) (hl : LeafHash) (R v : UInt256) (ℓ : Leaf) (idx : ℕ)
    (sibs : ℕ → UInt256) (k : ℕ) : Prop where
  nonzero : v ≠ 0
  lowBelow : ℓ.value < v
  window : ℓ.nextValue = 0 ∨ v < ℓ.nextValue
  path : PathAccepts h R sibs k idx (hl ℓ)

/-! ## The cryptographic idealizations -/

/-- Every hash assumption the soundness argument needs, as one bundle.  Each is a
statement about `keccak256`; none is proved anywhere in this package. -/
structure HashAssumptions (h : Hash) (z0 : UInt256) (hl : LeafHash) : Prop where
  /-- Node-hash pair-injectivity (collision resistance on 64-byte inputs). -/
  nodeInj : ∀ a b c d : UInt256, h a b = h c d → a = c ∧ b = d
  /-- Leaf-hash injectivity (collision resistance on the 96-byte encoding). -/
  leafInj : Function.Injective hl
  /-- A leaf hash is never a node hash — the `hashLeaf` 64-byte-preimage comment. -/
  leafNotNode : ∀ (ℓ : Leaf) (a b : UInt256), hl ℓ ≠ h a b
  /-- The padding constant is never a leaf hash — what `IMT_EMPTY_LEAF_HASH` buys. -/
  padNotLeaf : ∀ ℓ : Leaf, hl ℓ ≠ z0
  /-- The padding constant is never a node hash. -/
  padNotNode : ∀ a b : UInt256, z0 ≠ h a b

/-! ## The located break, replacing `HashAssumptions`

`HashAssumptions` is unsatisfiable (`HashAssumptionsUnsatisfiable`), so everything
stated under it is vacuous.  What the soundness argument actually extracts from an
accepted path that does NOT name an occupied index holding the presented leaf is one
of the following, each about values determined by the instance (the tree, the
submitted siblings, length, index and leaf). -/

/-- **A located break of the root check.**  `PathAccepts h (root h z0 hl T height) sibs k
idx (hl ℓ)` holds, yet the path does not open `T.leaf idx = ℓ` at the tree's height,
only because of one of:

* `wrongLength` — the submitted length is not the height, located by `HeightBreak`
  on the leaf-hash list (the claimed leaf hash is the node hash of a specific tree
  pair, or a level-0 entry — a leaf hash or the padding constant — is the node hash of
  the verifier's own pair, or a positional collision on the re-anchored / split walk);
* `pathCollision` — the right length, and a `PathCollision` on the submitted path;
* `leafCollision` — the opened index is occupied by a DIFFERENT leaf with the same
  leaf hash as the presented one (a `hashLeaf` collision between these two leaves);
* `paddingHit` — the opened index is empty and the presented leaf's hash IS the
  padding constant.  At the extraction pin `z0 = hl ⟨0,0,0⟩`, so this disjunct holds
  for `ℓ = ⟨0,0,0⟩` with no cryptographic work: it is the forged-absence bug
  (`PaddingCollisionRefundsDeliveredLeg`), which `IMT_EMPTY_LEAF_HASH` turns into a
  preimage problem.

Every case is reachable and attributed alone: `Properties.TreeRootBreakEveryCaseFires`
exhibits, for each case, a forged inclusion proof whose located break is exactly that
case (`TreeRootBreakExactly` below). -/
inductive TreeRootBreak (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ)
    (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) : Prop
  | wrongLength :
      HeightBreak h z0 (leafHashes hl T) sibs k height idx (hl ℓ) →
      TreeRootBreak h z0 hl T height sibs k idx ℓ
  | pathCollision : k = height →
      PathCollision h z0 (leafHashes hl T) sibs 0 k idx (hl ℓ) →
      TreeRootBreak h z0 hl T height sibs k idx ℓ
  | leafCollision : idx < T.leafCount → T.leaf idx ≠ ℓ → hl (T.leaf idx) = hl ℓ →
      TreeRootBreak h z0 hl T height sibs k idx ℓ
  | paddingHit : T.leafCount ≤ idx → hl ℓ = z0 →
      TreeRootBreak h z0 hl T height sibs k idx ℓ

/-! ## Which case of the break fires

`TreeRootBreak` is an inductive with four constructors, and a proof term of it names
one; but the statement `TreeRootBreak …` does not say WHICH case holds on an
instance, nor that only one does.  `TreeRootBreakAt c` is the premise of
constructor `c` as a proposition, and `TreeRootBreakExactly … c` says that case
`c`, and no other, holds.  `Contracts.InteropCommitmentTree.Properties.TreeRootBreakIffSomeCase`
checks the two views agree. -/

/-- The four cases of `TreeRootBreak`. -/
inductive TreeRootBreakCase
  | wrongLength
  | pathCollision
  | leafCollision
  | paddingHit
deriving DecidableEq

/-- The premise of the `TreeRootBreak` constructor named by the case. -/
def TreeRootBreakAt (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ)
    (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) : TreeRootBreakCase → Prop
  | .wrongLength => HeightBreak h z0 (leafHashes hl T) sibs k height idx (hl ℓ)
  | .pathCollision => k = height ∧ PathCollision h z0 (leafHashes hl T) sibs 0 k idx (hl ℓ)
  | .leafCollision => idx < T.leafCount ∧ T.leaf idx ≠ ℓ ∧ hl (T.leaf idx) = hl ℓ
  | .paddingHit => T.leafCount ≤ idx ∧ hl ℓ = z0

/-- **Exactly case `c` fires**: the break of case `c` holds on this instance, and
the break of every other case does not.  So the located break is unambiguous. -/
def TreeRootBreakExactly (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ)
    (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) (c : TreeRootBreakCase) : Prop :=
  ∀ c' : TreeRootBreakCase, TreeRootBreakAt h z0 hl T height sibs k idx ℓ c' ↔ c' = c

/-! ## A toy hash pair, for the firing witnesses

Not a model of `keccak`: a deliberately weak node hash and leaf hash whose
collisions can be written down, so that each case of `TreeRootBreak` can be shown
to fire on a concrete forged proof.  With these and padding constant `1`, each of
the four cases is the unique located break of some accepted inclusion proof, on the
`setup` tree at height 1, for a value that tree does not hold
(`Contracts.InteropCommitmentTree.Properties.TreeRootBreakEveryCaseFires`). -/

/-- Toy node hash: addition modulo `2^256`.  `toyNodeHash 1 0 = toyNodeHash 0 1`. -/
def toyNodeHash : Hash := fun a b => a + b

/-- Toy leaf hash: `value - nextValue` modulo `2^256`.  Collides on any two leaves
with the same difference, e.g. `⟨1, 0, 1⟩` and the sentinel `⟨0, 0, 0⟩`. -/
def toyLeafHash : LeafHash := fun ℓ => ℓ.value - ℓ.nextValue

/-! ## A concrete run, for the countermodel -/

/-- The contract run `setup; insert a; insert b` with `0 < a < b`: three leaves,
so `FullMerkle` sits at height 2 with slot 3 empty. -/
def threeLeafTree (a b : UInt256) : Tree := insert (insert setup a 0) b 1

end Contracts.InteropCommitmentTree
