import EraSpec.Protocol.MultichainGate.Specs.Model
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.RunHeight

/-!
# Multi-chain refund gate over the deployed absence verifier: definitions

`EraSpec.Protocol.MultichainGate.Specs.Model` states the source-bound refund gate over
abstract leaf sets: `AbsenceWitnessAt P c v` asks for a leaf `W ∈ P.trees c` whose window
straddles `v`.  `authorizeRefund` does not check that a leaf is in a set.  It compares
`_absence.sourceChainId` with the missing leg's declared chain and then runs
`IndexedMerkleTree.verifyNonInclusion` against that chain's IMT root, with the low leaf,
its index, its sibling path and the path length all supplied by the prover
(`AtomicInteropProof.verifyTimeoutAbsence`,
`atomic-interop/libraries/AtomicInteropProof.sol:198-204`, passes `_absence.imtLeafIndex`
with no bound against the tree's leaf count).

Sources: era-contracts `c67894b9`, under `l1-contracts/contracts/`.

## Where the two differ at `c67894b9`

* `IndexedMerkleTree.setup` (`common/libraries/IndexedMerkleTree.sol:47-48`) passes
  `hashLeaf({0,0,0})` to `FullMerkle.setup` as the zero value, so every empty slot below
  the tree's capacity carries the sentinel leaf's own hash (`FullMerkle.sol:29-35`, `:84`);
* `Merkle.calculateRootMemory` (`common/libraries/Merkle.sol:53-70`) checks only
  `pathLength < 256` and `index < 2 ^ pathLength` (`_validatePathLengthForSingleProof`,
  `:133-140`), so an index at or past the leaf count is accepted;
* `verifyNonInclusion` (`IndexedMerkleTree.sol:153-171`) checks only `v ≠ 0`,
  `lowLeaf.value < v` and `nextValue == 0 || v < nextValue`, which the sentinel `{0,0,0}`
  meets for every nonzero `v`.

So the sentinel, opened at an empty slot below capacity with the siblings the tree's own
nodes give that slot, recomputes the root and passes for every nonzero value, delivered or
not.  (`FullMerkle.merklePath` reverts for that index, `FullMerkle.sol:111-114`, but the
siblings are the tree's stored nodes.)  An empty slot below capacity needs at least three
leaves, and once the tree has had an insert the presented `{0,0,0}` is not one of its leaves
(the sentinel's links have moved).

At the current heads, `main` `70096e2ea` and `draft/v0.35.0` `b17415d20`, the padding is
`IMT_EMPTY_LEAF_HASH = keccak256("zkSync:IndexedMerkleTree:emptyLeaf")`
(`common/Config.sol:90`, resp. `:141`; `IndexedMerkleTree.sol:43-51` at both), introduced
by `78e14b3bc` ("F-04").

## What is modelled

The gate the contract runs, over chain states that carry their own `FullMerkle._height`
(`Contracts.InteropCommitmentTree.HState`), so the root is checked at the height the source
itself computes.  The root is `HState.root`, the fold over the leaf hashes at that height.
That the stored root equals it along every run is `CReachesRootIsPublished`
(`L2InteropCommitmentTree` topic `CachedRoot`), for the transcribed `FullMerkle` storage;
that compiled code executes the transcription is O7 in `EraSpec.Refinement`.

Model boundary: one state per chain, as in `MultichainGate`.  Which batch's BEGIN or END
root the proof is checked against, the deadline and the timeout branches are not modelled
here (`Contracts.Timeout`); nor is `_authenticateRoot`, so the root is the source chain's
true root.

**Definitions only.**  Statements: `EraSpec.Protocol.MultichainGate.Properties.DeployedGate`;
proofs: `EraSpec.Protocol.MultichainGate.Proofs.DeployedGate`.
-/

namespace Contracts.Protocol.DeployedGate

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-- `FullMerkle`'s level-0 padding at `c67894b9`: `IndexedMerkleTree.setup` passes
`hashLeaf({0,0,0})` as the zero value (`IndexedMerkleTree.sol:47-48`). -/
def pinPadding (hl : LeafHash) : UInt256 := hl ⟨0, 0, 0⟩

/-- Every chain's commitment-tree state, with its `FullMerkle` dimensions
`(_leafNumber, _height)`. -/
abbrev ChainStates := Chain → HState

/-- The abstract `Protocol` view of a family of chain states: each chain's list state,
projected by `toAbs`.  This is what `BoundGate` and `Delivered` read. -/
def ofStates (St : ChainStates) : Protocol := ofChains (fun c => (St c).tree)

/-- Every chain's state is reached from `IndexedMerkleTree.setup` by guarded inserts, with
the dimensions `pushNewLeaf` gives it. -/
def StatesFromSetup (St : ChainStates) : Prop := ∀ c, HReaches hSetup (St c)

/-- **THE DEPLOYED SOURCE-BOUND GATE, ON ONE SUBMITTED PROOF.**  The source-chain check has
selected chain `src`, and `verifyNonInclusion` accepts the low leaf `ℓ` at index `idx` with
siblings `sibs` and path length `k` against `src`'s root at its own `_height`.  Every one of
`ℓ, idx, sibs, k` is the prover's. -/
def DeployedBoundGateBy (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates)
    (src : Chain) (v : UInt256) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ) : Prop :=
  NonInclusionAccepted h hl ((St src).root h z0 hl) v ℓ idx sibs k

/-- **THE DEPLOYED SOURCE-BOUND GATE.**  Some submitted proof passes it.  Compare `BoundGate`,
which asks for a leaf of the abstract leaf set instead. -/
def DeployedBoundGate (h : Hash) (z0 : UInt256) (hl : LeafHash) (St : ChainStates)
    (src : Chain) (v : UInt256) : Prop :=
  ∃ (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    DeployedBoundGateBy h z0 hl St src v ℓ idx sibs k

/-- The tree has no empty slot below its capacity: `_leafNumber = 2 ^ _height`. -/
def FullAtOwnHeight (S : HState) : Prop := S.tree.leafCount = 2 ^ S.height

/-- **A COLLISION BREAK.**  The located cases of `TreeRootBreak` other than `paddingHit`: a
wrong-length path carrying a `HeightBreak`, a right-length path carrying a
`PathCollision`, or a `hashLeaf` collision between the presented leaf and a different leaf
stored at the opened index.  Each compares hashes of values the instance determines.
`paddingHit` is left out because at `c67894b9` the sentinel meets it with no collision. -/
def CollisionBreak (h : Hash) (z0 : UInt256) (hl : LeafHash) (T : Tree) (height : ℕ)
    (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) : Prop :=
  TreeRootBreakAt h z0 hl T height sibs k idx ℓ .wrongLength
    ∨ TreeRootBreakAt h z0 hl T height sibs k idx ℓ .pathCollision
    ∨ TreeRootBreakAt h z0 hl T height sibs k idx ℓ .leafCollision

/-! ## Concrete configurations -/

/-- The attack states at `c67894b9`: chain `0` ran `setup; insert a; insert b` (three leaves,
`_height = 2`, slot 3 empty); every other chain ran only `setup`. -/
def paddingStates (a b : UInt256) : ChainStates :=
  fun c => if c = 0 then hThree a b else hSetup

/-- The siblings of the forged absence proof: the honest sibling stream for the empty slot 3
of `hThree a b` under the pinned padding (the tree's own nodes at that slot's path;
`merklePath(3)` itself reverts). -/
def paddingSlotSibs (h : Hash) (hl : LeafHash) (a b : UInt256) : ℕ → UInt256 :=
  honestSibs h (pinPadding hl) (leafHashes hl (hThree a b).tree) 3

/-- `setup; insert a`: two leaves at `_height = 1`, so the tree is full. -/
def twoLeafState (a : UInt256) : HState := hInsert hSetup a 0

/-- A low leaf that collides with the sentinel's post-insert form `⟨0, 1, 2⟩` under the toy
leaf hash `value - nextValue` (both hash to `-2`), and straddles `2`. -/
def toyCollidingLowLeaf : Leaf := ⟨1, 0, 3⟩

end Contracts.Protocol.DeployedGate
