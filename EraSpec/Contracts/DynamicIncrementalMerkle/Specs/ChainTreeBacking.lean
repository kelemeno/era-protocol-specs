import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.Model
import EraSpec.Protocol.InteropAtomicity.Specs.Timeout
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.CachedRoot

/-!
# Model: the `MessageRoot` chain trees as the backing of a settlement-layer root

`Contracts.Timeout.RootBacking` (Protocol/InteropAtomicity/Specs/Timeout.lean) is the per-chain
batch tree an aggregation root is built from.  It takes the tree's leaves, its height, and two
facts as fields: `upToLast` (the root holds batches `0 … upTo c`, so the last leaf index is
`upTo c`) and `capacity` (the leaves fit the height).  `LastBatchAccepted` then asks for a batch
path whose walk recomputes `rootOf ze leaves height` and whose right siblings are the zero
cascade wherever it turns left (`_verifyLastBatchInRoot`, AtomicInteropProof.sol:217-230).

Those chain trees are `DynamicIncrementalMerkle` trees (`chainTree[chainId]`,
MessageRootBase.sol:69), set up with `CHAIN_TREE_EMPTY_ENTRY_HASH` (:350) and pushed one batch
leaf per settled batch (:257-259).  Here the backing is built from DIM runs, so its height is the
library's own minimal height, its root is the root the library stores, and `upToLast` and
`capacity` are discharged instead of assumed.  The batch path is the honest sibling stream of the
tree (`MerkleSpec.Verifier.honestSibs`), the path an off-chain prover reads from the DIM's
levels; the DIM library itself has no `merklePath` function.

## Model boundary

* `ChainTrees` records, per chain, the leaves pushed so far and the storage they produced by a
  run from `setup(CHAIN_TREE_EMPTY_ENTRY_HASH)`.  Which batches are pushed, and the mapping from
  tree position to batch number, is the `MessageRoot`'s business (backlog item W-X-1); here leaf
  `i` is "the chain's `i`-th pushed batch leaf", as `RootBacking`'s docstring reads it.
* Every chain is required to have at least one leaf, as `RootBacking.upToLast` requires; an empty
  chain tree has root `bytes32(0)` (`Properties.DimEmptyRootIsZero`), which is not the fold, so
  it cannot back `RootBacking` at all.

## The empty-entry constants

`CHAIN_TREE_EMPTY_ENTRY_HASH`, `SHARED_ROOT_TREE_EMPTY_HASH` (IMessageRoot.sol:9-16) and
`ChainBatchRootTree.EMPTY_IMT_ROOT` (ChainBatchRootTree.sol:55) are the same 32-byte literal.
The source documents it as the keccak of 96 zero bytes, which is also
`hashLeaf({value: 0, nextIndex: 0, nextValue: 0})`, the leaf hash of the IMT's sentinel that
`IndexedMerkleTree.setup` pads its tree with (ChainBatchRootTree.sol:50-54).  Lean cannot
evaluate keccak, so that last identity stays a premise (`zeroLeafHash hl = emptyImtRoot`).
-/

namespace Contracts.DynamicIncrementalMerkle

open MerkleSpec MerkleSpec.Verifier Contracts.Timeout

/-! ## The chain trees -/

/-- **The `MessageRoot`'s chain trees as DIM storage**: per chain, the batch leaves pushed so far
and the storage a run from `setup(ze)` left; every chain has at least one leaf. -/
structure ChainTrees (h : Hash) (ze : UInt256) where
  /-- Chain `c`'s pushed batch leaves, in push order. -/
  leaves : Contracts.Atomicity.Chain → List UInt256
  /-- Chain `c`'s `chainTree[c]` storage. -/
  state : Contracts.Atomicity.Chain → PushTree
  /-- The storage is what pushing those leaves from `setup(ze)` produced. -/
  run : ∀ c, Run h ze (leaves c) (state c)
  /-- Every chain has at least one batch leaf. -/
  nonempty : ∀ c, leaves c ≠ []

/-- The settlement-layer root the chain trees back, created at `created`: chain `c`'s last batch
in it is its last leaf, index `|leaves c| - 1`. -/
def ChainTrees.slRoot {h : Hash} {ze : UInt256} (T : ChainTrees h ze) (created : ℕ) : SlRoot where
  created := created
  upTo := fun c => (T.leaves c).length - 1

/-- **The chain trees as a `Timeout.RootBacking`**: the leaves, and the height the DIM run
reached (`dimHeight |leaves c|`).  `upToLast` holds because every chain has a leaf, and
`capacity` because `|L| ≤ 2^⌈log₂ |L|⌉`. -/
def ChainTrees.backing {h : Hash} {ze : UInt256} (T : ChainTrees h ze) (created : ℕ) :
    RootBacking h ze (T.slRoot created) where
  leaves := T.leaves
  height := fun c => dimHeight (T.leaves c).length
  upToLast := fun c =>
    (Nat.sub_add_cancel (List.length_pos_iff.mpr (T.nonempty c))).symm
  capacity := fun c => Nat.le_pow_clog (by norm_num) _

/-- The right side of the path the contract checks for leaf `i`: at every level below the
height where the path turns left, the honest sibling is that level's zero. -/
def ZeroRightSide (h : Hash) (ze : UInt256) (L : List UInt256) (H i : ℕ) : Prop :=
  ∀ l, l < H → (i / 2 ^ l) % 2 = 0 → honestSibs h ze L i l = zeros h ze l

/-! ## The empty-entry constants -/

/-- `SHARED_ROOT_TREE_EMPTY_HASH` (IMessageRoot.sol:14-16), the zero of the shared tree
(MessageRootBase.sol:164). -/
def sharedRootTreeEmptyHash : UInt256 :=
  0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21

/-- `ChainBatchRootTree.EMPTY_IMT_ROOT` (ChainBatchRootTree.sol:55), documented as the root of a
freshly set-up interop commitment tree, `hashLeaf({0, 0, 0})`. -/
def emptyImtRoot : UInt256 :=
  0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21

/-! ## A concrete instance for the witnesses -/

/-- Two batch leaves `[5, 7]` under the toy hash `MerkleSpec.LastLeaf.demoHash` with zero `0`:
the DIM storage after pushing them, `⟨2, [5, h 5 7], [0, h 0 0]⟩`. -/
def demoChainState : PushTree :=
  ⟨2, [5, MerkleSpec.LastLeaf.demoHash 5 7],
    [0, MerkleSpec.LastLeaf.demoHash 0 0]⟩

end Contracts.DynamicIncrementalMerkle
