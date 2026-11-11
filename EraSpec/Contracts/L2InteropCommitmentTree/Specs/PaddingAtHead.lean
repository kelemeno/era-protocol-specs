import EraSpec.Contracts.L2InteropCommitmentTree.Specs.CachedRoot
import EraSpec.Contracts.InteropDataEncoding.Specs.BundleHashPinned

/-!
# Model: the commitment tree at `main`, with a domain-separated padding constant

Source: era-contracts `main` at `3605e82` (`MAIN/` below is `l1-contracts/contracts/` of that
tree).  The change modelled is commit `78e14b3bc` ("F-04 domain-separate the IMT empty-leaf
padding value"), merged through #2315.  `CachedRoot` models the pin `c67894b9`, where the
padding constant was the hash of a valid leaf; its `CThreeLeafWitness` is the forged absence
proof that this allowed against the stored root.

**This file is definitions only.**  Statements are in
`EraSpec.Contracts.L2InteropCommitmentTree.Properties.PaddingAtHead`, proofs in
`EraSpec.Contracts.L2InteropCommitmentTree.Proofs.PaddingAtHead`.

## What changed

    MAIN/common/Config.sol:86-90
        /// @dev Padding value for empty/unused leaves in an {IndexedMerkleTree}. Deliberately NOT a
        /// valid `hashLeaf(IMTLeaf)` output, so an unused padded index can't be presented as a
        /// `{0,0,0}` low leaf to forge a non-inclusion proof. ...
        bytes32 constant IMT_EMPTY_LEAF_HASH = keccak256("zkSync:IndexedMerkleTree:emptyLeaf");

    MAIN/common/libraries/IndexedMerkleTree.sol:46-54
        function setup(IMT storage self) internal {
            if (self.tree._leafNumber != 0) { revert IMTAlreadyInitialized(); }
            self.tree.setup(IMT_EMPTY_LEAF_HASH);
            self.tree.pushNewLeaf(hashLeaf(IMTLeaf({value: 0, nextIndex: 0, nextValue: 0})));
            self.leaves[0] = IMTLeaf({value: 0, nextIndex: 0, nextValue: 0});
        }

At the pin (`IndexedMerkleTree.sol:42-51` at `c67894b9`) the same function computed
`zeroLeafHash = hashLeaf({0,0,0})` and passed it to both calls: `tree.setup(zeroLeafHash)` and
`tree.pushNewLeaf(zeroLeafHash)`.  So the padding constant and leaf 0's hash were one value.  At
`main` they are two values with different keccak preimages: the 34-byte string, and the 96-byte
`abi.encode(0, 0, 0)`.

## What did not change

* `hashLeaf` is `keccak256(abi.encode(_leaf.value, _leaf.nextIndex, _leaf.nextValue))`
  (`MAIN/common/libraries/IndexedMerkleTree.sol:124-126`).
* `verifyInclusion` (`:134-146`) and `verifyNonInclusion` (`:154-172`) are unchanged.  The
  latter checks `_value != 0`, `_lowLeaf.value < _value` and
  `_lowLeaf.nextValue == 0 || _lowLeaf.nextValue > _value`, then compares
  `Merkle.calculateRootMemory(_lowLeafProof, _lowLeafIndex, hashLeaf(_lowLeaf))` with `_root`.
  `TreeRoot`'s `PathAccepts`, `InclusionAccepted` and `NonInclusionAccepted` model these.
* `MAIN/common/libraries/Merkle.sol` and `FullMerkle.sol` are byte-identical to the pin.  In
  particular `calculateRootMemory` (`Merkle.sol:53-70`) still bounds the index only by
  `2 ^ pathLength` (`_validatePathLengthForSingleProof`, `:133-140`), not by the leaf count.
  `efficientHash(a, b)` (`:124-131`) is keccak of the 64 bytes `a ‖ b`.  So `FullMerkle`'s cached
  storage (`FullMerkle/Specs/CachedNodes.lean`) and `CachedRoot`'s `cInsert` describe `main`.
* The insert guards and writes are unchanged (`IndexedMerkleTree.sol:70-106`).  The low-leaf
  search is now unbounded (`:90-93`, #2349).  `cInsert` takes the low leaf the search ends on,
  with `InsertGuard`, and `InsertGuard` does not mention the bound: a search that ends, from any
  hint and with any number of hops, ends on a guarded leaf (`SearchYieldsGuard` is stated for
  every fuel), and from the hint `low` itself the loop runs zero times.  So the bounded search of
  the pin and the unbounded one of `main` give the same reached states.
* `L2InteropCommitmentTree.insert` (`MAIN/atomic-interop/L2InteropCommitmentTree.sol:50-63`) now
  also calls `_reportLeaf` (`:70-75`).  That call writes no tree storage and can only revert, so
  the reached states over-approximate the wrapper's, and statements over all of them cover it.
  `root()` (`:93-95`) and `merklePath(i)` (`:108-110`) read the `IMT` as before.

## Two layers

* **Any padding constant.**  `cSetupPad h hl ze` is `setup` with `FullMerkle.setup(ze)` and
  `pushNewLeaf(hl ⟨0,0,0⟩)`.  The node hash `h`, leaf hash `hl` and `ze` are arbitrary.  The pin
  is the instance `ze = hl ⟨0,0,0⟩`, and `main` is `ze = IMT_EMPTY_LEAF_HASH`.
* **keccak.**  `imtHashLeaf`, `imtNodeHash` and `imtEmptyLeafHash` are one arbitrary function
  `keccak : List UInt8 → UInt256` applied to the three byte strings the source hashes:
  `abi.encode` of a leaf (96 bytes), a node pair (64 bytes) and the tag (34 bytes).  Nothing about
  `keccak` is assumed.  The located breaks of `TreeRoot` then become keccak collisions on two
  byte strings that the instance names (`KeccakBreakAtHead`).

## Model boundaries

* `keccak` is any function.  Collisions are conclusions, never excluded by a premise, and each is
  pinned: `HashCollision keccak x y` names `x` and `y`.
* `word` is the 32-byte big-endian word of `InteropDataEncoding/Specs/BundleHashEncoding.lean`.
  `Leaf.nextIndex` is `ℕ`, and `word` reduces it modulo `2^256` as a `uint256` field would.
* As in `CachedRoot`: `IMTAlreadyInitialized` is replaced by starting from fresh storage, a
  revert inside `FullMerkle` is `none`, and compiled-code correspondence is obligation O7.
-/

namespace Contracts.InteropCommitmentTree

open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (word HashCollision)

/-! ## `setup` with an independent padding constant -/

/-- `IndexedMerkleTree.setup` on fresh storage, padding with `ze`
(`MAIN/common/libraries/IndexedMerkleTree.sol:46-54`): `tree.setup(ze)`, then
`tree.pushNewLeaf(hashLeaf({0,0,0}))`, with the sentinel list state.  At `main`, `ze` is
`IMT_EMPTY_LEAF_HASH` (`imtEmptyLeafHash`).  With `ze = hashLeaf({0,0,0})` this is the pin's
`cSetup` (`Properties.PinSetupIsPadAtZeroLeafHash`). -/
def cSetupPad (h : Hash) (hl : LeafHash) (ze : UInt256) : Option CState :=
  (FullMerkle.pushNewLeaf h (FullMerkle.setup FullMerkle.FullTree.empty ze).1 (hl ⟨0, 0, 0⟩)).map
    fun r => ⟨setup, r.1⟩

/-- States reached from `cSetupPad h hl ze` by guarded inserts that do not revert.  This is
`CachedRoot`'s `CReaches` with the padding constant as a parameter; the insert step is the same
`cInsert`. -/
inductive CReachesPad (h : Hash) (hl : LeafHash) (ze : UInt256) : CState → Prop
  | init {S : CState} : cSetupPad h hl ze = some S → CReachesPad h hl ze S
  | insert {S S' : CState} {v : UInt256} {low : ℕ} {r : UInt256} :
      CReachesPad h hl ze S → InsertGuard S.tree v low → cInsert h hl S v low = some (S', r) →
      CReachesPad h hl ze S'

/-! ## keccak, at the byte level -/

/-- `abi.encode(_leaf.value, _leaf.nextIndex, _leaf.nextValue)`, the preimage `hashLeaf` hashes
(`IndexedMerkleTree.sol:124-126`): three 32-byte big-endian words, 96 bytes. -/
def imtLeafPreimage (ℓ : Leaf) : List UInt8 :=
  word ℓ.value.val ++ (word ℓ.nextIndex ++ word ℓ.nextValue.val)

/-- The 64 bytes `Merkle.efficientHash(a, b)` hashes (`Merkle.sol:124-131`: `mstore(0x00, a)`,
`mstore(0x20, b)`, `keccak256(0x00, 0x40)`). -/
def imtNodePreimage (a b : UInt256) : List UInt8 := word a.val ++ word b.val

/-- The node preimage of an ordered pair, as `walkPair` and `treePair` return them. -/
def imtPairPreimage (p : UInt256 × UInt256) : List UInt8 := imtNodePreimage p.1 p.2

/-- The bytes `keccak256` hashes in `IMT_EMPTY_LEAF_HASH` (`Config.sol:90`): the string literal
`"zkSync:IndexedMerkleTree:emptyLeaf"`, 34 ASCII bytes, which are also its UTF-8 encoding
(`Properties.ImtEmptyLeafTagIsTheLiteral`). -/
def imtEmptyLeafTag : List UInt8 :=
  [122, 107, 83, 121, 110, 99, 58, 73, 110, 100, 101, 120, 101, 100, 77, 101, 114, 107, 108, 101,
   84, 114, 101, 101, 58, 101, 109, 112, 116, 121, 76, 101, 97, 102]

/-- `IndexedMerkleTree.hashLeaf`, from keccak. -/
def imtHashLeaf (keccak : List UInt8 → UInt256) : LeafHash := fun ℓ => keccak (imtLeafPreimage ℓ)

/-- `Merkle.efficientHash`, from keccak. -/
def imtNodeHash (keccak : List UInt8 → UInt256) : Hash := fun a b => keccak (imtNodePreimage a b)

/-- `IMT_EMPTY_LEAF_HASH`, from keccak. -/
def imtEmptyLeafHash (keccak : List UInt8 → UInt256) : UInt256 := keccak imtEmptyLeafTag

/-- Level 0 of the tree at `main`: the occupied leaves' `hashLeaf`s, in index order. -/
abbrev imtLevel0 (keccak : List UInt8 → UInt256) (T : Tree) : List UInt256 :=
  leafHashes (imtHashLeaf keccak) T

/-- **States reached at `main`.**  `CReachesPad` with keccak's node hash and leaf hash, and the
padding constant `IMT_EMPTY_LEAF_HASH`. -/
abbrev CReachesAtHead (keccak : List UInt8 → UInt256) (S : CState) : Prop :=
  CReachesPad (imtNodeHash keccak) (imtHashLeaf keccak) (imtEmptyLeafHash keccak) S

/-! ## The located break at `main`, as keccak collisions on named byte strings

`TreeRoot`'s `TreeRootBreak` is stated for arbitrary `h`, `z0` and `hl`.  At `main`'s hashes each
of its cases is a keccak collision: two different byte strings, both determined by the instance,
with the same keccak.  The definitions below state those collisions directly.  The proofs relate
them to `PathCollision`, `HeightBreak` and `TreeRootBreak` (`Properties.PathCollisionAtHeadIffKeccak`,
`HeightBreakAtHeadIffKeccak`, `KeccakBreakAtHeadIsTreeRootBreak`). -/

/-- **A node-hash collision on a path, as a keccak collision.**  At some step `i < k` of the walk
from level `lvl`, index `j`, accumulator `x`, keccak takes the same value on the 64-byte preimage
of the pair the verifier hashed and on that of the tree's pair at the same position, and the two
preimages differ.  This is `PathCollision` for the node hash `imtNodeHash keccak`. -/
def PathKeccakCollision (keccak : List UInt8 → UInt256) (z0 : UInt256) (L : List UInt256)
    (sibs : ℕ → UInt256) (lvl k j : ℕ) (x : UInt256) : Prop :=
  ∃ i < k, HashCollision keccak
    (imtPairPreimage (walkPair (imtNodeHash keccak) sibs lvl j x i))
    (imtPairPreimage (treePair (imtNodeHash keccak) z0 L (lvl + i) (j / 2 ^ i)))

/-- **A wrong path length, as a keccak collision.**  `HeightBreak` at `main`'s hashes, one
constructor per case.  The `longEntryIsNode` case is split by what the level-0 entry is: the hash
of an occupied slot's leaf, or the padding constant.  Arguments as for `HeightBreak`: tree `T` at
`height`, submitted siblings `sibs`, length `k`, index `j`, presented leaf `ℓ`. -/
inductive LengthKeccakBreak (keccak : List UInt8 → UInt256) (T : Tree) (height : ℕ)
    (sibs : ℕ → UInt256) (k j : ℕ) (ℓ : Leaf) : Prop
  /-- Too short: the presented leaf's 96-byte preimage and the 64-byte preimage of the tree's
  level-`height - k - 1` pair below `j` collide. -/
  | shortLeafIsNode : k < height →
      HashCollision keccak (imtLeafPreimage ℓ)
        (imtPairPreimage (treePair (imtNodeHash keccak) (imtEmptyLeafHash keccak) (imtLevel0 keccak T)
          (height - k - 1) (2 * j))) →
      LengthKeccakBreak keccak T height sibs k j ℓ
  /-- Too short: the walk, re-anchored at level `height - k`, collides on the path. -/
  | shortCollision : k < height →
      PathKeccakCollision keccak (imtEmptyLeafHash keccak) (imtLevel0 keccak T)
        (fun l => sibs (l - (height - k))) (height - k) k j (imtHashLeaf keccak ℓ) →
      LengthKeccakBreak keccak T height sibs k j ℓ
  /-- Too long, through an occupied slot `m = j / 2 ^ (k - height)`: that stored leaf's 96-byte
  preimage and the 64-byte preimage of the pair the verifier hashed at its last step below the
  split collide. -/
  | longLeafIsNode : height < k → j / 2 ^ (k - height) < T.leafCount →
      HashCollision keccak (imtLeafPreimage (T.leaf (j / 2 ^ (k - height))))
        (imtPairPreimage
          (walkPair (imtNodeHash keccak) sibs 0 j (imtHashLeaf keccak ℓ) (k - height - 1))) →
      LengthKeccakBreak keccak T height sibs k j ℓ
  /-- Too long, through a padding slot: the 34-byte tag and the 64-byte preimage of the pair the
  verifier hashed at its last step below the split collide. -/
  | longEmptyLeafIsNode : height < k → T.leafCount ≤ j / 2 ^ (k - height) →
      HashCollision keccak imtEmptyLeafTag
        (imtPairPreimage
          (walkPair (imtNodeHash keccak) sibs 0 j (imtHashLeaf keccak ℓ) (k - height - 1))) →
      LengthKeccakBreak keccak T height sibs k j ℓ
  /-- Too long: the top `height` steps, read from the shifted siblings, collide on the path. -/
  | longCollision : height < k →
      PathKeccakCollision keccak (imtEmptyLeafHash keccak) (imtLevel0 keccak T)
        (fun l => sibs (l + (k - height))) 0 height (j / 2 ^ (k - height))
        (walkPure (imtNodeHash keccak) sibs 0 (k - height) j (imtHashLeaf keccak ℓ)) →
      LengthKeccakBreak keccak T height sibs k j ℓ

/-- **A KECCAK COLLISION LOCATED ON A SUBMITTED PROOF, AT `main`.**  An accepted path presenting
`hashLeaf(ℓ)` at index `idx`, with `k` siblings `sibs`, against the root of `T` at `height`, that
does not open a stored leaf with `ℓ`'s value and `nextValue`, yields one of:

* `emptyLeaf`: the right length, and `idx` is a padding slot.  keccak takes the same value on the
  presented leaf's `abi.encode` and on the tag, i.e. `hashLeaf(ℓ) = IMT_EMPTY_LEAF_HASH`.  At the
  pin this case cost nothing for `ℓ = {0,0,0}`, because the padding was `hashLeaf({0,0,0})`;
  at `main` it is a collision between a 96-byte and a 34-byte string.
* `leaf`: the right length, and `idx` is occupied by a leaf whose `abi.encode` differs from the
  presented one's but has the same keccak.
* `node`: the right length, and a node-hash collision at a named step of the submitted path.
* `length`: a wrong length, located as in `LengthKeccakBreak`.

Every case names its two byte strings.  So this is not "keccak has a collision", which is
always true; `Properties.HonestProofNoKeccakBreakAtHead` shows it is false on every honest
proof, for every `keccak`. -/
inductive KeccakBreakAtHead (keccak : List UInt8 → UInt256) (T : Tree) (height : ℕ)
    (sibs : ℕ → UInt256) (k idx : ℕ) (ℓ : Leaf) : Prop
  | emptyLeaf : k = height → T.leafCount ≤ idx →
      HashCollision keccak (imtLeafPreimage ℓ) imtEmptyLeafTag →
      KeccakBreakAtHead keccak T height sibs k idx ℓ
  | leaf : k = height → idx < T.leafCount →
      HashCollision keccak (imtLeafPreimage (T.leaf idx)) (imtLeafPreimage ℓ) →
      KeccakBreakAtHead keccak T height sibs k idx ℓ
  | node : k = height →
      PathKeccakCollision keccak (imtEmptyLeafHash keccak) (imtLevel0 keccak T) sibs 0 k idx
        (imtHashLeaf keccak ℓ) →
      KeccakBreakAtHead keccak T height sibs k idx ℓ
  | length : LengthKeccakBreak keccak T height sibs k idx ℓ →
      KeccakBreakAtHead keccak T height sibs k idx ℓ

end Contracts.InteropCommitmentTree
