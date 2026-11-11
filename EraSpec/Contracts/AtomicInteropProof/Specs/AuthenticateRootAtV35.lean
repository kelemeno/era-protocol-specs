import EraSpec.Contracts.AtomicInteropProof.Specs.LastLeaf
import EraSpec.Contracts.Merkle.Specs.PathCollision

/-!
# `_authenticateRoot` at draft/v0.35.0: the settlement-layer words, read by position

era-contracts `draft/v0.35.0` at commit `d9f678900e1bc8286412b78f56d4a9f443983c29` (`d9f6789`).
Every `file:line` here is at `d9f6789` and relative to `l1-contracts/contracts/`, unless it is
marked `@c67894b9` (the extraction pin the older models in this folder describe).

## What changed between the pin and v35

`AtomicInteropProof._authenticateRoot` (`atomic-interop/libraries/AtomicInteropProof.sol:155-189`)
authenticates a claimed IMT root as leaf 2 or 3 of a source chain's batch root, then returns the
settlement-layer metadata `(slBlock, slChainId, l1BatchTimestamp)`.

* At the pin it got that metadata by running `MessageHashing._getProofData` a second time on the
  already-verified proof, with the same leaf and mask (`AtomicInteropProof.sol:276-289@c67894b9`).
* At v35 it reads the same words by position, through the new accessor
  `MessageHashing.readSettlementLayerReference` (`common/libraries/MessageHashing.sol:285-299`).
  The final-node rejection moved from the parse result to the metadata parsed at the start
  (`AtomicInteropProof.sol:177-179`).
* `MessageHashing.readAggregationHopPath` (`MessageHashing.sol:252-262`) now reverts on a final-node
  proof (`:254-256`). `verifyTimeoutAbsence`'s end branch hands its result to
  `_verifyLastBatchInRoot` (`AtomicInteropProof.sol:111-113`).

`AtomicInteropProof.sol` is the same blob (`40a6c702`) on main `3605e82` and on `d9f6789`, so none of
this is specific to v35. `_getProofData` (`MessageHashing.sol:152-236`), the L2 verifier
(`interop/L2MessageVerification.sol:18-56`, `common/MessageVerification.sol:35-73`) and
`Merkle.calculateRootMemory` (`common/libraries/Merkle.sol:53-70`, `:133-140`) changed only in
comments between the pin and v35.

## What is modelled

The word layout, transcribed:

* `Proof` is the `bytes32[] calldata` word list. `word w i` is `_proof[i]`, and it reverts
  (`none`) when `i` is out of range. `slice w l r` is `extractSlice` (`MessageHashing.sol:306-315`).
* `getProofData` is `_getProofData` (`MessageHashing.sol:152-236`), one hop, every revert included.
* `readSL` and `readHop` are the two positional accessors (`MessageHashing.sol:285-299` and
  `:252-262`).
* `proveShared` is `proveL2LeafInclusionShared` on an L2: depth 0, then at most one recursive hop
  (`L2MessageVerification.sol:26-55`).
* `authenticateRootV35` and `authenticateRootPin` are the two versions of `_authenticateRoot`.
* `LastBatchCheck` is the loop of `_verifyLastBatchInRoot` (`AtomicInteropProof.sol:130-143`).

`parseProofMetadata` (`MessageHashing.sol:101-143`) is left uninterpreted as `Env.parse`. Every
consumer calls that same function on the same bytes, and the results below hold for every parser.
The hash functions are uninterpreted too. No property about any of them is assumed.

Results: `../Properties/AuthenticateRootAtV35.lean`.
-/

namespace AttackVectors.AuthenticateRootAtV35

open MerkleSpec MerkleSpec.Verifier

/-- The `bytes32[] calldata` proof, as a list of words. -/
abbrev Proof := List UInt256

/-- `_proof[i]`. Out of range is a revert, written `none`. -/
def word (w : Proof) (i : ℕ) : Option UInt256 := w[i]?

/-- `MessageHashing.extractSlice(_proof, l, r)` (`MessageHashing.sol:306-315`).
`new bytes32[](r - l)` panics on underflow under checked arithmetic, and each read `_proof[i]` for
`l ≤ i < r` panics when out of range. So the call succeeds exactly when `l ≤ r`, and either the
range is empty or `r ≤ length`. -/
def slice (w : Proof) (l r : ℕ) : Option (List UInt256) :=
  if l ≤ r ∧ (l = r ∨ r ≤ w.length) then some ((w.drop l).take (r - l)) else none

/-- `MessageHashing.ProofMetadata` (`MessageHashing.sol:91-96`). -/
structure Metadata where
  proofStartIndex : ℕ
  logLeafProofLen : ℕ
  batchLeafProofLen : ℕ
  finalProofNode : Bool
deriving DecidableEq

/-- The uninterpreted functions the proof code calls. -/
structure Env where
  /-- `Merkle.efficientHash` (`Merkle.sol:125-131`). -/
  node : Hash
  /-- `MessageHashing.batchLeafHash(batchRoot, batchNumber, l1Timestamp)` (`MessageHashing.sol:76-82`). -/
  batchLeaf : UInt256 → UInt256 → UInt256 → UInt256
  /-- `MessageHashing.chainIdLeafHash(chainIdRoot, chainId)` (`MessageHashing.sol:87-89`). -/
  chainIdLeaf : UInt256 → UInt256 → UInt256
  /-- `L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH`, the leaf `_getProofData` rejects (`MessageHashing.sol:165-167`). -/
  defaultLeaf : UInt256
  /-- `MessageHashing.parseProofMetadata` (`MessageHashing.sol:101-143`). `none` is a revert. -/
  parse : Proof → Option Metadata

/-- `Merkle.calculateRootMemory(path, index, item)` (`Merkle.sol:53-70`), together with
`_validatePathLengthForSingleProof` (`Merkle.sol:133-140`). -/
def calcRoot (h : Hash) (path : List UInt256) (index : ℕ) (item : UInt256) : Option UInt256 :=
  if path.length < 256 ∧ index < 2 ^ path.length then
    some (walkPure h (fun l => path.getD l 0) 0 path.length index item)
  else none

/-- `uint256(x >> 128)`. -/
def hi128 (x : UInt256) : UInt256 := ((x.val / 2 ^ 128 : ℕ) : UInt256)

/-- `x & ((1 << 128) - 1)`. -/
def lo128 (x : UInt256) : UInt256 := ((x.val % 2 ^ 128 : ℕ) : UInt256)

/-- `ProofData` (`common/Messaging.sol`), as `_getProofData` fills it. -/
structure ProofData where
  slChainId : UInt256
  slBatchNumber : UInt256
  slBatchRootMask : UInt256
  batchLeafProofLen : ℕ
  batchSettlementRoot : UInt256
  chainIdLeaf : UInt256
  l1BatchTimestamp : UInt256
  ptr : ℕ
  finalProofNode : Bool
deriving DecidableEq

/-- `MessageHashing._getProofData(chainId, batchNumber, mask, leaf, _proof)`
(`MessageHashing.sol:152-236`). With `p = proofStartIndex + logLeafProofLen`, the words after the
log-leaf path are `[p] = l1Timestamp`, `[p+1] = batchLeafProofMask`,
`[p+2, p+2+bLen) = batch-leaf siblings`, `[p+2+bLen] = packed SL batch info` and
`[p+3+bLen] = slChainId`. The returned `ptr` is `p + 4 + bLen`. A final-node proof returns early
at `:183-185` with only `ptr`, `batchSettlementRoot` and `finalProofNode` set. -/
def getProofData (E : Env) (chainId batchNumber mask leaf : UInt256) (w : Proof) :
    Option ProofData :=
  if w = [] then none else
  if leaf = E.defaultLeaf then none else
  (E.parse w).bind fun md =>
  (slice w md.proofStartIndex (md.proofStartIndex + md.logLeafProofLen)).bind fun logPath =>
  (calcRoot E.node logPath mask.val leaf).bind fun bsr =>
  if md.finalProofNode then
    some ⟨0, 0, 0, 0, bsr, 0, 0, md.proofStartIndex + md.logLeafProofLen, true⟩
  else
  (word w (md.proofStartIndex + md.logLeafProofLen)).bind fun t =>
  (word w (md.proofStartIndex + md.logLeafProofLen + 1)).bind fun bmask =>
  (slice w (md.proofStartIndex + md.logLeafProofLen + 2)
      (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen)).bind fun bPath =>
  (calcRoot E.node bPath bmask.val (E.batchLeaf bsr batchNumber t)).bind fun chainIdRoot =>
  (word w (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen)).bind fun packed =>
  (word w (md.proofStartIndex + md.logLeafProofLen + 3 + md.batchLeafProofLen)).bind fun slChain =>
  some ⟨slChain, hi128 packed, lo128 packed, md.batchLeafProofLen, bsr,
    E.chainIdLeaf chainIdRoot chainId, t,
    md.proofStartIndex + md.logLeafProofLen + 4 + md.batchLeafProofLen, false⟩

/-- `MessageHashing.SettlementLayerReference` (`MessageHashing.sol:268-275`), in the order
`_authenticateRoot` returns it: `(slBlock, slChainId, l1BatchTimestamp)`. -/
structure SLRef where
  slBatchNumber : UInt256
  slChainId : UInt256
  l1BatchTimestamp : UInt256
deriving DecidableEq

/-- `MessageHashing.readSettlementLayerReference` (`MessageHashing.sol:285-299`), new at main and
v35. It reads `[p]`, `[p+2+bLen] >> 128` and `[p+3+bLen]`. -/
def readSL (E : Env) (w : Proof) : Option SLRef :=
  (E.parse w).bind fun md =>
  if md.finalProofNode then none else
  (word w (md.proofStartIndex + md.logLeafProofLen)).bind fun t =>
  (word w (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen)).bind fun packed =>
  (word w (md.proofStartIndex + md.logLeafProofLen + 3 + md.batchLeafProofLen)).bind fun slChain =>
  some ⟨hi128 packed, slChain, t⟩

/-- `MessageHashing.AggregationHopPath` (`MessageHashing.sol:240-245`). -/
structure HopPath where
  mask : UInt256
  sibs : List UInt256
deriving DecidableEq

/-- `MessageHashing.readAggregationHopPath` (`MessageHashing.sol:252-262`). It reads
`[p+1]` and `[p+2, p+2+bLen)`. The final-node revert at `:254-256` is new at main and v35. -/
def readHop (E : Env) (w : Proof) : Option HopPath :=
  (E.parse w).bind fun md =>
  if md.finalProofNode then none else
  (word w (md.proofStartIndex + md.logLeafProofLen + 1)).bind fun mask =>
  (slice w (md.proofStartIndex + md.logLeafProofLen + 2)
      (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen)).bind fun sibs =>
  some ⟨mask, sibs⟩

/-- `L2_MESSAGE_VERIFICATION.proveL2LeafInclusionShared` as it runs on an L2
(`common/MessageVerification.sol:35-73`, `interop/L2MessageVerification.sol:18-56`).
`_getProofData` runs at depth 0. A final node anchors to `interopRoots(chainId, batch).root`
(`:33-39`). Otherwise one recursive hop runs on the suffix from `ptr`
(`extractSliceUntilEnd`, `:53`). That hop must itself be a final node anchored at
`interopRoots(slChainId, slBatchNumber)`, and a second non-final hop reverts (`:40-42`).
`roots c b` is `L2_INTEROP_ROOT_STORAGE.interopRoots(c, b).root`. -/
def proveShared (E : Env) (roots : UInt256 → UInt256 → UInt256)
    (chainId batchNumber mask leaf : UInt256) (w : Proof) : Option Bool :=
  (getProofData E chainId batchNumber mask leaf w).bind fun pd =>
  if pd.finalProofNode then
    some (decide (roots chainId batchNumber = pd.batchSettlementRoot ∧ roots chainId batchNumber ≠ 0))
  else
  (slice w pd.ptr w.length).bind fun rest =>
  (getProofData E pd.slChainId pd.slBatchNumber pd.slBatchRootMask pd.chainIdLeaf rest).bind fun pd' =>
  if pd'.finalProofNode then
    some (decide (roots pd.slChainId pd.slBatchNumber = pd'.batchSettlementRoot
      ∧ roots pd.slChainId pd.slBatchNumber ≠ 0))
  else none

/-- `ChainBatchRootTree.TREE_DEPTH` (`common/libraries/ChainBatchRootTree.sol:11`; `:28@c67894b9`). -/
def treeDepth : ℕ := 3

/-- **`_authenticateRoot` at v35** (`AtomicInteropProof.sol:155-189`): metadata (`:159`), the
exact-depth check (`:160-162`), the verifier (`:164-173`), the final-node rejection on the parsed
metadata (`:177-179`), then the positional read (`:183-188`). -/
def authenticateRootV35 (E : Env) (roots : UInt256 → UInt256 → UInt256)
    (src batch leafIndex imtRoot : UInt256) (w : Proof) : Option SLRef :=
  (E.parse w).bind fun md =>
  if md.logLeafProofLen ≠ treeDepth then none else
  (proveShared E roots src batch leafIndex imtRoot w).bind fun ok =>
  if ok = false then none else
  if md.finalProofNode then none else
  readSL E w

/-- **`_authenticateRoot` at the pin** (`AtomicInteropProof.sol:256-290@c67894b9`). It is the same
up to the verifier, then re-runs `_getProofData` with the same arguments (`:276-282@c67894b9`) and
rejects a final node on the result (`:285@c67894b9`). -/
def authenticateRootPin (E : Env) (roots : UInt256 → UInt256 → UInt256)
    (src batch leafIndex imtRoot : UInt256) (w : Proof) : Option SLRef :=
  (E.parse w).bind fun md =>
  if md.logLeafProofLen ≠ treeDepth then none else
  (proveShared E roots src batch leafIndex imtRoot w).bind fun ok =>
  if ok = false then none else
  (getProofData E src batch leafIndex imtRoot w).bind fun pd =>
  if pd.finalProofNode then none else
  some ⟨pd.slBatchNumber, pd.slChainId, pd.l1BatchTimestamp⟩

/-- The loop of `_verifyLastBatchInRoot` (`AtomicInteropProof.sol:130-143`). At every level
`i < sibs.length` where bit `i` of the mask is 0, the sibling equals `zeros h z0 i`. That is the
cascade from `z0 = CHAIN_TREE_EMPTY_ENTRY_HASH` (`core/message-root/IMessageRoot.sol:9`) through
`Merkle.efficientHash`. It is the same loop as `:217-230@c67894b9`. -/
def LastBatchCheck (h : Hash) (z0 : UInt256) (hop : HopPath) : Prop :=
  ∀ i < hop.sibs.length, (hop.mask.val / 2 ^ i) % 2 = 0 → hop.sibs.getD i 0 = zeros h z0 i

/-- `ChainBatchRootTree.IMT_END_ROOT_LEAF_INDEX` (`ChainBatchRootTree.sol:25`). -/
def imtEndLeafIndex : UInt256 := 3

/-- **The end branch of `verifyTimeoutAbsence` at v35, up to the last-batch check**
(`AtomicInteropProof.sol:77-114`). `_authenticateRoot` runs against leaf 3 (`:85-89`), the hop path
is read from the same words (`:113`), and the zero cascade passes (`:113`, `:130-143`). The SL,
`T` and `t` comparisons (`:90-110`) do not touch the path and are not repeated here. -/
structure EndBranchPassesV35 (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 : UInt256)
    (src batch imtRoot : UInt256) (w : Proof) (sl : SLRef) (hop : HopPath) : Prop where
  auth : authenticateRootV35 E roots src batch imtEndLeafIndex imtRoot w = some sl
  hop_eq : readHop E w = some hop
  last : LastBatchCheck E.node z0 hop

/-! ## A concrete instance, for the anti-vacuity witness

It is not a model of `keccak`. The node hash is `MerkleSpec.LastLeaf.demoHash`, which collides
freely, and the leaf encodings are small sums. The proof below is a two-hop proof with a
three-word log-leaf path, a one-word batch-leaf path with a left turn, and a final hop with an
empty path. -/

/-- The demo environment. The full proof starts with the word `1`, which the demo parser reads as
a non-final metadata word (`logLen = 3`, `bLen = 1`). Any other first word reads as a final
node with an empty log path. -/
def demoEnv : Env where
  node := MerkleSpec.LastLeaf.demoHash
  batchLeaf := fun r b t => r + b + t
  chainIdLeaf := fun r c => r + c
  defaultLeaf := 0
  parse := fun w => if w.head? = some 1 then some ⟨1, 3, 1, false⟩ else some ⟨1, 0, 0, true⟩

/-- The demo `CHAIN_TREE_EMPTY_ENTRY_HASH`. -/
def demoZ0 : UInt256 := 5

/-- The demo proof. The words are: the metadata, three log-leaf siblings, `t = 4`, batch mask `0`,
the batch sibling `zeros 0 = 5`, packed SL info `0` (SL block 0, mask 0), SL chain `7`, and the
second-hop metadata `2`. -/
def demoProof : Proof := [1, 10, 20, 30, 4, 0, 5, 0, 7, 2]

end AttackVectors.AuthenticateRootAtV35
