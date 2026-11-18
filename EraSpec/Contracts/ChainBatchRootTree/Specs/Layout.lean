import EraSpec.Contracts.Merkle.Specs.PathCollision
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned
import EraSpec.Contracts.L2InteropCommitmentTree.Specs.TreeRoot

/-!
# Spec: `ChainBatchRootTree`, the height-3 chain batch root of a ZKsync OS batch

Source: era-contracts `draft/v0.35.0` head `b17415d20`, `l1-contracts/contracts/`
(cited without that prefix). The library's code is the same at the earlier v35 draft
`d9f678900`, at `c67894b9` and at main `70096e2ea`; only comments differ.

    common/libraries/ChainBatchRootTree.sol
      :11      TREE_DEPTH = 3
      :15-25   LOGS_ROOT_LEAF_INDEX = 0, MULTICHAIN_ROOT_LEAF_INDEX = 1,
               IMT_BEGIN_ROOT_LEAF_INDEX = 2, IMT_END_ROOT_LEAF_INDEX = 3
      :29-30   RESERVED_SUBTREE_NODE = 0xb4c1…0d30   (documented: z2, z1 = keccak(0 ‖ 0),
                                                       z2 = keccak(z1 ‖ z1))
      :35      EMPTY_IMT_ROOT = 0x4670…8c21          (documented: keccak of 96 zero bytes)
      :40-42   genesisChainBatchRoot() = compute(0, 0, EMPTY_IMT_ROOT, EMPTY_IMT_ROOT)
      :49-62   compute(l, m, b, e) =
                 keccak(keccak(keccak(l ‖ m) ‖ keccak(b ‖ e)) ‖ RESERVED_SUBTREE_NODE)

Every internal node, here and in `Merkle.calculateRootMemory` (`common/libraries/Merkle.sol:53-70`,
`efficientHash` at `:125-131`), is keccak of the same 64 bytes `l ‖ r`. The tree's leaves are used
directly: it has no leaf-hashing step (`protocol-docs/message-root.md:70`).

The two documented values are pinned by unit tests at `b17415d20`
(`l1-contracts/test/foundry/l1/unit/concrete/common/libraries/ChainBatchRootTree.t.sol:15-21` and
`:58-61`). Off-chain recomputation (`cast keccak`) agrees with both, and gives
`genesisChainBatchRoot() = 0x1d57c24629c4445766683a9843cae545c6fe1f8f35159aca41f2a38b7b227885`.
Lean does not evaluate keccak, so every use of these values here is a named premise
(`ReservedSubtreeDocumented`, `EmptyImtRootDocumented`) on two specific keccak inputs, never an
injectivity assumption.

## Model

* `keccak : List UInt8 → UInt256` is an arbitrary function. Nothing is assumed about it.
* `node keccak a b = keccak (w32 a ++ w32 b)`: the 64-byte node preimage of `Merkle.efficientHash`
  and of `compute`'s `bytes.concat`. `w32` is the 32-byte big-endian word (`word`,
  `InteropDataEncoding/Specs/BundleHashEncoding.lean`), the ABI meaning of a `bytes32` (`SOL-ABI`).
* `Merkle.calculateRootMemory(path, index, item)` is `walkPure (node keccak) sibs 0 k index item`
  with the check `index < 2^k` (`Merkle.sol:133-140`), as everywhere in `Merkle`.
* `cbrPair` names, for each of the three levels, the pair the tree hashes above an index. The two
  lower levels are the `FullMerkle` pairs over `[a, b, c, d]` padded with `0`
  (`MerkleSpec.Verifier.treePair`); the top level is `(liveSubtreeNode, RESERVED_SUBTREE_NODE)`.
  A located break is a keccak collision on two NAMED 64-byte strings: the pair the verifier hashed
  at a step and the tree's pair at the same position (`OpeningCollision`).

**This file is definitions only.** Results: `../Properties/Layout.lean`.
-/

namespace Contracts.ChainBatchRootTree

open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision word toBytesBE)

/-- `keccak256` over byte strings: an arbitrary function. -/
abbrev Keccak := List UInt8 → UInt256

/-- The 32-byte big-endian word of a `bytes32` / `uint256`. -/
abbrev w32 (x : UInt256) : List UInt8 := word x.val

/-- **THE 64-BYTE NODE PREIMAGE.** `bytes.concat(l, r)` in `compute` (`ChainBatchRootTree.sol:55-61`)
and `mstore(0x00, l) mstore(0x20, r) keccak256(0x00, 0x40)` in `Merkle.efficientHash`
(`Merkle.sol:125-131`). -/
def nodePre (a b : UInt256) : List UInt8 := w32 a ++ w32 b

/-- The node preimage of an ordered pair. -/
def pairPre (p : UInt256 × UInt256) : List UInt8 := nodePre p.1 p.2

/-- The node hash of the chain batch root tree and of `Merkle.calculateRootMemory`. -/
def node (keccak : Keccak) : Hash := fun a b => keccak (nodePre a b)

/-! ## The constants (`ChainBatchRootTree.sol:11-35`) -/

/-- `TREE_DEPTH` (`:11`). -/
def TREE_DEPTH : ℕ := 3

/-- `LOGS_ROOT_LEAF_INDEX` (`:15`). -/
def LOGS_ROOT_LEAF_INDEX : ℕ := 0

/-- `MULTICHAIN_ROOT_LEAF_INDEX` (`:19`). No contract reads it at `b17415d20`. -/
def MULTICHAIN_ROOT_LEAF_INDEX : ℕ := 1

/-- `IMT_BEGIN_ROOT_LEAF_INDEX` (`:22`), read by `AtomicInteropProof.sol:86`. -/
def IMT_BEGIN_ROOT_LEAF_INDEX : ℕ := 2

/-- `IMT_END_ROOT_LEAF_INDEX` (`:25`), read by `AtomicInteropProof.sol:52, 87`. -/
def IMT_END_ROOT_LEAF_INDEX : ℕ := 3

/-- `RESERVED_SUBTREE_NODE` (`:29-30`), the hex literal as written. -/
def RESERVED_SUBTREE_NODE : UInt256 :=
  0xb4c11951957c6f8f642c4af61cd6b24640fec6dc7fc607ee8206a99e92410d30

/-- `EMPTY_IMT_ROOT` (`:35`), the hex literal as written. -/
def EMPTY_IMT_ROOT : UInt256 :=
  0x46700b4d40ac5c35af2c22dda2787a91eb567b06c924a8fb8ae9a05b20c08c21

/-! ## `compute` and `genesisChainBatchRoot` (`:40-62`) -/

/-- `liveSubtreeNode` (`:55-60`): the node over the four live leaves. -/
def liveSubtreeNode (keccak : Keccak) (a b c d : UInt256) : UInt256 :=
  node keccak (node keccak a b) (node keccak c d)

/-- **`ChainBatchRootTree.compute(_logsRoot, _multichainRoot, _imtRootBegin, _imtRootEnd)`**
(`:49-62`). -/
def compute (keccak : Keccak) (a b c d : UInt256) : UInt256 :=
  node keccak (liveSubtreeNode keccak a b c d) RESERVED_SUBTREE_NODE

/-- **`ChainBatchRootTree.genesisChainBatchRoot()`** (`:40-42`). -/
def genesisChainBatchRoot (keccak : Keccak) : UInt256 :=
  compute keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT

/-- The four live leaves, at indices `0 … 3`: logs root, multichain root, IMT root at batch
begin, IMT root at batch end (`:13-25`). Indices `4 … 7` are the reserved zero leaves. -/
def liveLeaves (a b c d : UInt256) : List UInt256 := [a, b, c, d]

/-! ## The documented values, as premises on two keccak inputs -/

/-- **THE DOCUMENTED VALUE OF `RESERVED_SUBTREE_NODE`** (`:27-28`): `z2` with `z1 = keccak(0 ‖ 0)`,
`z2 = keccak(z1 ‖ z1)`. A premise on two keccak inputs (64 zero bytes, and `z1 ‖ z1`). -/
def ReservedSubtreeDocumented (keccak : Keccak) : Prop :=
  RESERVED_SUBTREE_NODE = node keccak (node keccak 0 0) (node keccak 0 0)

/-- The 96 zero bytes: `abi.encode(uint256(0), uint256(0), uint256(0))`, the preimage of the
`{0,0,0}` sentinel leaf hash (`IndexedMerkleTree.sol:124-126`). -/
def sentinelLeafPre : List UInt8 := List.replicate 96 0

/-- **THE DOCUMENTED VALUE OF `EMPTY_IMT_ROOT`** (`:32-34`): keccak of 96 zero bytes. A premise on
one keccak input. -/
def EmptyImtRootDocumented (keccak : Keccak) : Prop :=
  EMPTY_IMT_ROOT = keccak sentinelLeafPre

/-! ## The interop commitment tree's leaves (`IndexedMerkleTree.sol`, `b17415d20`) -/

/-- **THE IMT LEAF PREIMAGE, 96 BYTES.** `IndexedMerkleTree.hashLeaf` (`IndexedMerkleTree.sol:124-126`):
`keccak256(abi.encode(_leaf.value, _leaf.nextIndex, _leaf.nextValue))`. The model's `nextIndex` is a
natural number (`Contracts.InteropCommitmentTree.Leaf`); `word` keeps its low 32 bytes, which is
`abi.encode` of the `uint256` the contract stores. -/
def imtLeafPre (ℓ : Contracts.InteropCommitmentTree.Leaf) : List UInt8 :=
  w32 ℓ.value ++ word ℓ.nextIndex ++ w32 ℓ.nextValue

/-- `IndexedMerkleTree.hashLeaf`, with keccak. -/
def imtHashLeaf (keccak : Keccak) : Contracts.InteropCommitmentTree.LeafHash :=
  fun ℓ => keccak (imtLeafPre ℓ)

/-- **THE IMT PADDING PREIMAGE AT `b17415d20`, 34 BYTES.** `IMT_EMPTY_LEAF_HASH =
keccak256("zkSync:IndexedMerkleTree:emptyLeaf")` (`common/Config.sol:141`), the zero value
`IndexedMerkleTree.setup` gives its `FullMerkle` tree (`IndexedMerkleTree.sol:51`). These are the 34
ASCII bytes of that string, written out. -/
def imtPaddingPre : List UInt8 :=
  [0x7a, 0x6b, 0x53, 0x79, 0x6e, 0x63, 0x3a, 0x49, 0x6e, 0x64, 0x65, 0x78, 0x65, 0x64, 0x4d, 0x65,
    0x72, 0x6b, 0x6c, 0x65, 0x54, 0x72, 0x65, 0x65, 0x3a, 0x65, 0x6d, 0x70, 0x74, 0x79, 0x4c, 0x65,
    0x61, 0x66]

/-! ## Opening a leaf: the pairs the tree hashes, and the located collision -/

/-- **THE TREE'S PAIR AT LEVEL `i` ABOVE INDEX `j`** (`i < 3`). Levels 0 and 1: the `FullMerkle`
pair over `[a, b, c, d]` with padding `0` (`(a, b)`, `(c, d)`, `(0, 0)`; then
`(node a b, node c d)`, `(node 0 0, node 0 0)`). Level 2: `(liveSubtreeNode, RESERVED_SUBTREE_NODE)`,
the pair `compute` hashes last. For `j ≥ 4` the lower two levels are the pairs below the reserved
node when `ReservedSubtreeDocumented` holds. -/
def cbrPair (keccak : Keccak) (a b c d : UInt256) (i j : ℕ) : UInt256 × UInt256 :=
  if i < 2 then treePair (node keccak) 0 (liveLeaves a b c d) i (j / 2 ^ i)
  else (liveSubtreeNode keccak a b c d, RESERVED_SUBTREE_NODE)

/-- **A COLLISION LOCATED ON A DEPTH-3 OPENING.** At some level `i < 3` the pair the verifier hashed
(`walkPair`, from the submitted siblings, index and claimed leaf) differs from the tree's pair at
that position (`cbrPair`), and keccak maps their two 64-byte node preimages to the same word. Both
strings are functions of the instance. -/
def OpeningCollision (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (j : ℕ)
    (x : UInt256) : Prop :=
  ∃ i < 3, HashCollision keccak (pairPre (walkPair (node keccak) sibs 0 j x i))
    (pairPre (cbrPair keccak a b c d i j))

/-- The tree's own siblings for index `j`: the `FullMerkle` siblings over `[a, b, c, d]` at the two
lower levels, then `RESERVED_SUBTREE_NODE` (live half, `j < 4`) or `liveSubtreeNode` (reserved
half). This is the proof an honest prover submits. -/
def openingSibs (keccak : Keccak) (a b c d : UInt256) (j : ℕ) : ℕ → UInt256 :=
  fun l => if l < 2 then honestSibs (node keccak) 0 (liveLeaves a b c d) j l
    else if j < 4 then RESERVED_SUBTREE_NODE else liveSubtreeNode keccak a b c d

/-! ## The atomic-interop IMT-root hop -/

/-- **`_authenticateRoot`'s FIRST HOP, UP TO THE CHAIN BATCH ROOT** (`AtomicInteropProof.sol:155-173`).
The metadata's `logLeafProofLen` must equal `TREE_DEPTH` (`:160-162`); the leaf is the claimed IMT
root `x` and the mask the fixed leaf index `m` (`:164-170`, `m` is `IMT_BEGIN_ROOT_LEAF_INDEX` or
`IMT_END_ROOT_LEAF_INDEX` by `:52`, `:85-87`); `MessageHashing._getProofData` walks
`calculateRootMemory(slice, mask, leaf)` (`MessageHashing.sol:174-178`, `Merkle.sol:53-70`). That
the walk's result is the batch's recorded chain batch root `compute a b c d` is the conclusion of the
outer hops, which are not modelled here. -/
structure ImtRootHopAccepted (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256)
    (len m : ℕ) (x : UInt256) : Prop where
  /-- `metadata.logLeafProofLen == ChainBatchRootTree.TREE_DEPTH` (`AtomicInteropProof.sol:160-162`). -/
  depthPinned : len = TREE_DEPTH
  /-- `Merkle.sol:137-139`, `MerkleIndexOutOfBounds`. -/
  inBounds : m < 2 ^ len
  /-- The walk reaches the batch's chain batch root. -/
  reachesBatchRoot : walkPure (node keccak) sibs 0 len m x = compute keccak a b c d

/-! ## The L2 `MessageRoot`'s genesis aggregated root (for the leaf-1 remark) -/

/-- **`chainIdLeafHash`'s 96-BYTE PREIMAGE** (`MessageHashing.sol:87-89`):
`abi.encodePacked(CHAIN_ID_LEAF_PADDING, chainIdRoot, chainId)`. `padC` stands for
`CHAIN_ID_LEAF_PADDING = keccak256("zkSync:ChainIdLeaf")` (`:16`). -/
def chainIdLeafPre (padC chainIdRoot chainId : UInt256) : List UInt8 :=
  w32 padC ++ w32 chainIdRoot ++ w32 chainId

/-- **A `MessageRoot`'s aggregated root right after `_initialize`.** `_initialize` sets up the
shared tree and adds `block.chainid` with an empty chain root (`MessageRootBase.sol:138-142`,
`:275-293`): its one leaf is `chainIdLeafHash(bytes32(0), block.chainid)` (`:287`). A one-leaf
`FullMerkle` tree has height 0 and its root is that leaf (`FullMerkle.sol:41-66, 73-94, 99-101`),
which `getAggregatedRoot` returns while `chainCount != 0` (`MessageRootBase.sol:249-254`). -/
def initialAggregatedRoot (keccak : Keccak) (padC chainId : UInt256) : UInt256 :=
  keccak (chainIdLeafPre padC 0 chainId)

end Contracts.ChainBatchRootTree
