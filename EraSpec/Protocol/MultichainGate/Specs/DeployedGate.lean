import EraSpec.Protocol.MultichainGate.Specs.Model
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight

/-!
# Multi-chain refund gate over the deployed verifier: definitions

`EraSpec.Protocol.MultichainGate.Specs.Model` states the source-bound refund gate over
abstract leaf-set witnesses: `AbsenceWitnessAt P c v` asks for a leaf `W ∈ P.trees c`
whose window straddles `v`.  `authorizeRefund` does not check membership of a leaf.  It
compares `_absence.sourceChainId` with the missing leg's declared chain and then runs
`IndexedMerkleTree.verifyNonInclusion` against that chain's root, with the low leaf, its
index, its sibling path and the path length all chosen by the prover
(`AtomicInteropProof.verifyTimeoutAbsence`, `libraries/AtomicInteropProof.sol:198-204`,
passes `_absence.imtLeafIndex` through with no bound against the tree's leaf count).

## Where the two differ at the extraction pin

At era-contracts `c67894b9`:

* `IndexedMerkleTree.setup` (`common/libraries/IndexedMerkleTree.sol:47-48`) passes
  `hashLeaf({0,0,0})` to `FullMerkle.setup` as the zero value, so every empty slot below
  the tree's capacity carries the sentinel leaf's own hash (`FullMerkle.sol:29-35`,
  `:84`, `:118`);
* `Merkle.calculateRootMemory` (`common/libraries/Merkle.sol:53-70`) checks only
  `pathLength < 256` and `index < 2 ^ pathLength` (`_validatePathLengthForSingleProof`,
  `:132-139`), so an index past the leaf count is accepted;
* `verifyNonInclusion` (`IndexedMerkleTree.sol:153-171`) checks only
  `lowLeaf.value < v` and `nextValue == 0 || v < nextValue`, which the sentinel
  `{0,0,0}` meets for every nonzero `v`.

So the sentinel, opened at an empty slot with the honest siblings, recomputes the
stored root and passes, for any nonzero value, delivered or not.  The leaf it presents
is not a member of the tree at that index.  At the upgrade pin `e561b9cc2` the padding
is `IMT_EMPTY_LEAF_HASH = keccak256("zkSync:IndexedMerkleTree:emptyLeaf")`
(`common/Config.sol:134`, `IndexedMerkleTree.sol:44-51`), whose NatSpec says it is there
to block exactly this forgery.

This file states the gate the contract runs, over contract states that carry their own
`FullMerkle._height` (`Contracts.InteropCommitmentTree.HState`), so the root the gate is
checked against is the one the source publishes, at the source's own height.  The root
is the model's fold over the leaf hashes at that height; that the stored
`_nodes[_height][0]` equals it is obligation O7 in `EraSpec.Refinement`, as for every
other root in this package.

**Definitions only.**  Statements: `EraSpec.Protocol.MultichainGate.Properties.DeployedGate`;
proofs: `EraSpec.Protocol.MultichainGate.Proofs.DeployedGate`.
-/

namespace Contracts.Protocol

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-- `FullMerkle`'s level-0 padding at the extraction pin: `IndexedMerkleTree.setup`
passes `hashLeaf({0,0,0})` as the zero value (`IndexedMerkleTree.sol:47-48`). -/
def pinPadding (hl : LeafHash) : UInt256 := hl ⟨0, 0, 0⟩

/-- Every chain's commitment-tree contract state, with its `FullMerkle` dimensions
`(_leafNumber, _height)`. -/
abbrev ChainStates := Chain → HState

/-- The abstract `Protocol` view of a family of chain states: each chain's list state,
projected by `toAbs`.  This is what `BoundGate` and `Delivered` read. -/
def ofStates (St : ChainStates) : Protocol := ofChains (fun c => (St c).tree)

/-- Every chain's state is reached from `IndexedMerkleTree.setup` by guarded inserts,
with the dimensions `pushNewLeaf` gives it. -/
def StatesFromSetup (St : ChainStates) : Prop := ∀ c, HReaches hSetup (St c)

/-- **THE DEPLOYED SOURCE-BOUND GATE, ON ONE SUBMITTED PROOF.**  The source-chain check
has selected chain `src`; `verifyNonInclusion` accepts the low leaf `ℓ` at index `idx`
with siblings `sibs` and path length `k` against `src`'s root at its own `_height`.
Every one of `ℓ, idx, sibs, k` is the prover's. -/
def DeployedBoundGateBy (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates)
    (src : Chain) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ) : Prop :=
  NonInclusionAccepted h hl ((St src).root h z0 hl) v ℓ idx sibs k

/-- **THE DEPLOYED SOURCE-BOUND GATE.**  Some proof passes it.  Compare `BoundGate`,
which asks for a leaf of the abstract leaf set instead. -/
def DeployedBoundGate (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates)
    (src : Chain) (v : UInt256) : Prop :=
  ∃ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k

/-- The tree has no empty slot below its capacity: `_leafNumber = 2 ^ _height`.  On a
state reached from `setup` this holds exactly when the leaf count is a power of two. -/
def FullAtOwnHeight (S : HState) : Prop := S.tree.leafCount = 2 ^ S.height

/-- **A COLLISION BREAK.**  The located breaks of `TreeRootBreak` other than
`paddingHit`: a wrong-length path carrying a `HeightBreak`, a right-length path carrying
a `PathCollision`, or a `hashLeaf` collision between the presented leaf and the leaf
stored at the opened index.  Each is a hash collision or a leaf/node domain-separation
failure on values the instance determines.  `paddingHit` is left out because at the
extraction pin it needs no hash work at all. -/
def CollisionBreak (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ)
    (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) : Prop :=
  TreeRootBreakAt h z0 hl T height sibs k idx ℓ .wrongLength
    ∨ TreeRootBreakAt h z0 hl T height sibs k idx ℓ .pathCollision
    ∨ TreeRootBreakAt h z0 hl T height sibs k idx ℓ .leafCollision

/-! ## Concrete configurations -/

/-- The attack states at the pin: chain `0` ran `setup; insert a; insert b` (three
leaves, `_height = 2`, slot 3 empty); every other chain ran only `setup`. -/
def paddingStates (a b : UInt256) : ChainStates :=
  fun c => if c = 0 then hThree a b else hSetup

/-- The siblings of the forged absence proof: `FullMerkle.merklePath`'s honest stream for
the empty slot 3 of `hThree a b`, under the pinned padding. -/
def paddingSlotSibs (h : Hash) (hl : LeafHash) (a b : UInt256) : ℕ → UInt256 :=
  honestSibs h (pinPadding hl) (leafHashes hl (hThree a b).tree) 3

/-- `setup; insert a`: two leaves at `_height = 1`, so the tree is full. -/
def twoLeafState (a : UInt256) : HState := hInsert hSetup a 0

/-- A low leaf that collides with the sentinel's post-insert form `⟨0, 1, 2⟩` under the
toy leaf hash `value - nextValue` (both hash to `-2`), and straddles `2`. -/
def toyCollidingLowLeaf : Leaf := ⟨1, 0, 3⟩

end Contracts.Protocol
