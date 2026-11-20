import EraSpec.Contracts.DynamicIncrementalMerkle.Specs.Model
import EraSpec.Protocol.InteropAtomicity.Specs.Timeout
import EraSpec.Contracts.AtomicInteropProof.Specs.LastLeafFaithful

/-!
# Model: `MessageRoot` chain trees as DIM storage, backing a settlement-layer root

`Contracts.Timeout.RootBacking` (Protocol/InteropAtomicity/Specs/Timeout.lean) is the per-chain
batch tree an aggregation root is built from.  It takes the tree's leaves and its height as
data, and two facts as fields: `upToLast` (the root holds leaves `0 … upTo c`, so the last leaf
index is `upTo c`) and `capacity` (the leaves fit the height).  `LastBatchAccepted` then asks for
a batch-leaf path whose walk recomputes `rootOf ze leaves height` and whose right siblings are the
zero cascade wherever the path turns left (`_verifyLastBatchInRoot`, AtomicInteropProof.sol:130-143
at era-contracts `draft/v0.35.0` `b17415d20`, the commit every line below refers to).

The chain trees are `DynamicIncrementalMerkle` trees (`chainTree[chainId]`,
MessageRootBase.sol:69).  The source writes them in two places only: `_addNewChain` (:275-292)
runs `setup(CHAIN_TREE_EMPTY_ENTRY_HASH)` (:285), and `_pushChainBatchRoot` (:201-221) pushes one
batch leaf (:207-209).  `_addNewChain` is reached from `_initialize` (:138-142) and from
`addNewChain` (:145-150), which reverts on a registered chain; `_pushChainBatchRoot` from
`addChainBatchRootV32` (:173-180) and `seedGenesisRoot` (:296-314).  (The interop pin `c67894b9`,
where this topic was first written, has the same writes at other lines.)

`ChainTrees` below takes each chain's storage to be a DIM run (`Specs/Model.lean`, `Run`):
`setup(ze)` on fresh storage, then pushes.  That those two writes produce such runs is read from
the source, not proved.  Given it, the backing's height is the library's own minimal height, the
fold it authenticates against is the value `root()` returns for the chain's storage, and
`capacity` is proved rather than given; `upToLast` holds by the choice of `upTo`
(`ChainTrees.slRoot`).

Two acceptance forms are used.  `LastBatchAccepted` (Timeout) fixes the walk's length to the
tree's height and the index to an occupied leaf, and leaves the siblings free.  The deployed check
also leaves the length and the mask free: `batchLeafProofLen` is a metadata byte
(MessageHashing.sol:129), the mask is read from the proof (:198), `Merkle.sol` checks only
`_pathLength < 256` and `_index < 1 << _pathLength` (:133-140), and `_verifyLastBatchInRoot` runs
its zero check over the submitted siblings (`levels = _path.batchLeafSiblings.length`,
AtomicInteropProof.sol:133), starting from `CHAIN_TREE_EMPTY_ENTRY_HASH` (:132), the value the
`MessageRoot` sets each chain tree up with (MessageRootBase.sol:285).
`MerkleSpec.LastLeafFaithful` models that acceptance; `Properties.DimAcceptedLastLeafAnyLengthOrBreak`
reads it against the `root()` of DIM storage.  Where a statement needs a concrete path it uses the
honest sibling stream of the tree (`MerkleSpec.Verifier.honestSibs`), read from the tree's levels;
the DIM library itself has no `merklePath` function.

## Model boundary

* `ChainTrees` records, for every chain id, the leaves pushed so far and the storage they
  produced by a run from `setup(ze)` on fresh storage.  Which batch leaves are pushed, and the
  mapping from tree position to batch number, belong to the `MessageRoot` and are not modelled
  here: leaf `i` is "the chain's `i`-th pushed batch leaf", as `RootBacking` reads it (its
  LastBatchInRootOffset correction and `PROTO-CONTIGUOUS-PUSH` apply unchanged).
* Every chain id has at least one leaf.  `RootBacking` quantifies over all chains
  (`Chain = UInt256`) and its `upToLast` forces a leaf for each, so a chain that is not
  registered, or has nothing pushed, has no place in a `ChainTrees`.  The DIM root of an empty
  tree is `bytes32(0)`, not the fold (`Properties.DimEmptyRootIsZero`,
  `Properties.EmptyRootIsNotTheFold`), so the backing could not cover it anyway.
  `seedGenesisRoot` (:296-314) pushes a batch-0 leaf only for a registered chain with nothing
  recorded yet (`currentChainBatchNumber == 0`, no batch-0 root); every other chain's tree starts
  empty after `_addNewChain`.
* The leaf values are arbitrary words: the batch-leaf encoding (`MessageHashing.batchLeafHash`) is
  not modelled.
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

/-- The settlement-layer root the chain trees back, created at `created`: chain `c`'s last leaf
in it has index `|leaves c| - 1`. -/
def ChainTrees.slRoot {h : Hash} {ze : UInt256} (T : ChainTrees h ze) (created : ℕ) : SlRoot where
  created := created
  upTo := fun c => (T.leaves c).length - 1

/-- **The chain trees as a `Timeout.RootBacking`**: the leaves, and the height the DIM run
reached (`dimHeight |leaves c|`).  `upToLast` holds because every chain has a leaf, and
`capacity` because `n ≤ 2^⌈log₂ n⌉` (`Nat.le_pow_clog`). -/
def ChainTrees.backing {h : Hash} {ze : UInt256} (T : ChainTrees h ze) (created : ℕ) :
    RootBacking h ze (T.slRoot created) where
  leaves := T.leaves
  height := fun c => dimHeight (T.leaves c).length
  upToLast := fun c =>
    (Nat.sub_add_cancel (List.length_pos_iff.mpr (T.nonempty c))).symm
  capacity := fun c => Nat.le_pow_clog (by norm_num) _

/-- The check `_verifyLastBatchInRoot` makes, on the honest path of leaf `i` of the tree over `L`
at height `H`: at every level below `H` where the path turns left, the sibling is that level's
zero. -/
def ZeroRightSide (h : Hash) (ze : UInt256) (L : List UInt256) (H i : ℕ) : Prop :=
  ∀ l, l < H → (i / 2 ^ l) % 2 = 0 → honestSibs h ze L i l = zeros h ze l

/-! ## A concrete instance for the witnesses -/

/-- The DIM storage after `setup(0)` and pushes of `[5, 7, 9]` under the toy hash
`MerkleSpec.LastLeaf.demoHash` (`a + 2b + 1`): `_nextLeafIndex = 3`, `_sides = [9, h 5 7,
h (h 5 7) (h 9 0)] = [9, 20, 41]`, `_zeros = [0, h 0 0, h 1 1] = [0, 1, 4]`.  Three leaves at
height 2 is a shape a deployed chain tree has. -/
def demoChainState : PushTree := ⟨3, [9, 20, 41], [0, 1, 4]⟩

end Contracts.DynamicIncrementalMerkle
