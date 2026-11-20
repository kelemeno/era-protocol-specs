import EraSpec.Contracts.AtomicInteropProof.Specs.LastLeafFaithful

/-!
# `_authenticateRoot` at draft/v0.35.0: the settlement-layer words, read by position

era-contracts `draft/v0.35.0` at commit `b17415d2068065a4a3e3f0e7a14a2e96f54212e5`
(`b17415d20`). Every `file:line` here is at `b17415d20` and relative to `l1-contracts/contracts/`,
unless it is marked `@c67894b9` (the extraction pin; such lines are as earlier rounds recorded
them, since `c67894b9` is not in the local clone). The files cited here are the same blobs at the earlier `draft/v0.35.0` head `d9f6789`, so every
citation holds there too. `AtomicInteropProof.sol` is also the same blob (`40a6c702`) on main
`3605e82` and `70096e2ea`. There `MessageHashing.sol` differs from `b17415d20` only in comments
and one `solhint` line (`:66`), which moves its later lines down by one.

## What the v35 code does (and what changed from the pin)

`AtomicInteropProof._authenticateRoot` (`atomic-interop/libraries/AtomicInteropProof.sol:155-189`)
authenticates a claimed IMT root as leaf 2 or 3 of a source chain's batch root, then returns the
settlement-layer metadata `(slBlock, slChainId, l1BatchTimestamp)`.

* At the pin it got that metadata by running `MessageHashing._getProofData` a second time on the
  already-verified proof, with the same leaf and mask, and rejected a final node on that result
  (`AtomicInteropProof.sol:274-289@c67894b9`).
* At v35 it rejects a final node on the metadata parsed at the start (`AtomicInteropProof.sol:175-179`)
  and reads the three words by position, through the new accessor
  `MessageHashing.readSettlementLayerReference` (`common/libraries/MessageHashing.sol:285-299`,
  called at `AtomicInteropProof.sol:181-188`).
* `MessageHashing.readAggregationHopPath` (`MessageHashing.sol:252-262`) now reverts on a final-node
  proof (`:254-256`). At the pin it had no such check (`MessageHashing.sol:258-265@c67894b9`).

`verifyTimeoutAbsence`'s end branch passes `readAggregationHopPath`'s result to
`_verifyLastBatchInRoot` in both versions (`AtomicInteropProof.sol:111-113`, `:193-195@c67894b9`).
`_getProofData` (`MessageHashing.sol:152-236`), the L2 verifier (`interop/L2MessageVerification.sol:18-56`,
`common/MessageVerification.sol:35-73`), `Merkle.calculateRootMemory` (`common/libraries/Merkle.sol:53-70`,
`:133-140`) and `_verifyLastBatchInRoot` (`AtomicInteropProof.sol:130-143`) changed only in comments
between the pin and v35.

## What is modelled

The word layout, transcribed:

* `Proof` is the `bytes32[] calldata` word list. `word w i` is `_proof[i]`, and it reverts
  (`none`) when `i` is out of range. `slice w l r` is `extractSlice` (`MessageHashing.sol:306-315`).
* `getProofData` is `_getProofData` (`MessageHashing.sol:152-236`), one hop, every revert included.
* `readSL` and `readHop` are the two positional accessors (`MessageHashing.sol:285-299` and
  `:252-262`). The pin's `readAggregationHopPath` (`readHopPin`) is in
  `../History/Specs/AuthenticateRootAtV35.lean`.
* `proveShared` is `proveL2LeafInclusionShared` on an L2: depth 0, then at most one recursive hop
  (`L2MessageVerification.sol:26-55`).
* `authenticateRootV35` is `_authenticateRoot`. The pin's version (`authenticateRootPin`) and the
  comparison with it are History (`../History/`).
* `LastBatchCheck` is the loop of `_verifyLastBatchInRoot` (`AtomicInteropProof.sol:130-143`).
* `slHopPath` is the Merkle path of the recursive (settlement-layer) hop, `SharedTreeBacking`
  describes the settlement layer's shared tree behind an imported root
  (`core/message-root/MessageRootBase.sol`), and `SLHopBreak` is what an accepted outer hop can
  exhibit instead of opening the source chain's slot.
* `logHopPath` is the first hop's log-leaf path, `ChainTreeEntries` describes the source chain's
  tree entry by entry (batch leaves of height-3 chain batch roots), and `AuthBreak` is what the
  first hop and the batch-leaf hop can exhibit instead of authenticating the claimed root.

`parseProofMetadata` (`MessageHashing.sol:101-143`) is the parameter `Env.parse`. Every consumer
calls that same function on the same words, and the results hold for every parser.
`parseMeta` is its transcription, and the witnesses use it. Offsets are natural numbers. With
`parseMeta` the start index is 0 or 1 and each length is a metadata byte or the proof's own length,
so none of the contract's checked `uint256` offset additions can overflow and the offsets agree.

The hash functions (`Env.node`, `Env.batchLeaf`, `Env.chainIdLeaf`) are parameters too. No
property of any of them is assumed. The witnesses instantiate them with small additive
functions, not with `keccak`.

Results: `../Properties/AuthenticateRootAtV35.lean`.
-/

namespace AttackVectors.AuthenticateRootAtV35

open MerkleSpec MerkleSpec.Verifier

/-! ## The proof words -/

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

/-- The functions the proof code calls, as parameters. -/
structure Env where
  /-- `Merkle.efficientHash` (`Merkle.sol:125-131`). -/
  node : Hash
  /-- `MessageHashing.batchLeafHash(batchRoot, batchNumber, l1Timestamp)` (`MessageHashing.sol:76-82`). -/
  batchLeaf : UInt256 → UInt256 → UInt256 → UInt256
  /-- `MessageHashing.chainIdLeafHash(chainIdRoot, chainId)` (`MessageHashing.sol:87-89`). -/
  chainIdLeaf : UInt256 → UInt256 → UInt256
  /-- `L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH`, the leaf `_getProofData` rejects (`MessageHashing.sol:165-167`,
  `common/Config.sol:27`). -/
  defaultLeaf : UInt256
  /-- `MessageHashing.parseProofMetadata` (`MessageHashing.sol:101-143`). `none` is a revert. Its
  transcription is `parseMeta`. -/
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

/-- `ProofData` (`common/Messaging.sol:332-345`), as `_getProofData` fills it. -/
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

/-! ## One hop, and the two positional readers -/

/-- `MessageHashing._getProofData(chainId, batchNumber, mask, leaf, _proof)`
(`MessageHashing.sol:152-236`). With `p = proofStartIndex + logLeafProofLen`, the words after the
log-leaf path are `[p] = l1Timestamp`, `[p+1] = batchLeafProofMask`,
`[p+2, p+2+bLen) = batch-leaf siblings`, `[p+2+bLen] = packed SL batch info` and
`[p+3+bLen] = slChainId`. The returned `ptr` is `p + 4 + bLen`. A final-node proof returns early
at `:183-185` with only `ptr`, `batchSettlementRoot` and `finalProofNode` set; the other fields
keep the zero of the fresh `memory` struct. -/
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

/-- `MessageHashing.readSettlementLayerReference` (`MessageHashing.sol:285-299`), new at v35. It
rejects a final node (`:289-291`), then reads `[p]`, `[p+2+bLen] >> 128` and `[p+3+bLen]`. -/
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

/-- `MessageHashing.readAggregationHopPath` (`MessageHashing.sol:252-262`). It rejects a final node
(`:254-256`, new at v35), then reads `[p+1]` and `[p+2, p+2+bLen)`. -/
def readHop (E : Env) (w : Proof) : Option HopPath :=
  (E.parse w).bind fun md =>
  if md.finalProofNode then none else
  (word w (md.proofStartIndex + md.logLeafProofLen + 1)).bind fun mask =>
  (slice w (md.proofStartIndex + md.logLeafProofLen + 2)
      (md.proofStartIndex + md.logLeafProofLen + 2 + md.batchLeafProofLen)).bind fun sibs =>
  some ⟨mask, sibs⟩

/-! ## The verifier and `_authenticateRoot` at b17415d20 -/

/-- `L2_MESSAGE_VERIFICATION.proveL2LeafInclusionShared` as it runs on an L2
(`common/MessageVerification.sol:35-73`, `interop/L2MessageVerification.sol:18-56`).
`_getProofData` runs at depth 0. A final node anchors to `interopRoots(chainId, batch).root`
(`:33-39`). Otherwise one recursive hop runs on the suffix from `ptr`
(`extractSliceUntilEnd`, `:53`, `MessageHashing.sol:319-324`). That hop must itself be a final
node anchored at `interopRoots(slChainId, slBatchNumber)`, and a second non-final hop reverts
(`:40-42`). `roots c b` is `L2_INTEROP_ROOT_STORAGE.interopRoots(c, b).root`
(`interop/L2InteropRootStorage.sol:39-44`). A revert of the external call reverts the caller,
so every revert is `none`. -/
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
metadata (`:177-179`), then the positional read (`:183-188`). The returned triple is
`(slBlock, slChainId, l1BatchTimestamp)`. -/
def authenticateRootV35 (E : Env) (roots : UInt256 → UInt256 → UInt256)
    (src batch leafIndex imtRoot : UInt256) (w : Proof) : Option SLRef :=
  (E.parse w).bind fun md =>
  if md.logLeafProofLen ≠ treeDepth then none else
  (proveShared E roots src batch leafIndex imtRoot w).bind fun ok =>
  if ok = false then none else
  if md.finalProofNode then none else
  readSL E w

/-! ## The end branch, up to the last-batch check -/

/-- The loop of `_verifyLastBatchInRoot` (`AtomicInteropProof.sol:130-143`) does not revert. At
every level `i < sibs.length` where bit `i` of the mask is 0 (`(mask >> i) & 1 == 0`), the
sibling equals `zeros h z0 i`, the cascade from `z0 = CHAIN_TREE_EMPTY_ENTRY_HASH`
(`core/message-root/IMessageRoot.sol:9-11`) through `Merkle.efficientHash`. It is the same loop
as `:217-230@c67894b9`. -/
def LastBatchCheck (h : Hash) (z0 : UInt256) (hop : HopPath) : Prop :=
  ∀ i < hop.sibs.length, (hop.mask.val / 2 ^ i) % 2 = 0 → hop.sibs.getD i 0 = zeros h z0 i

/-- `ChainBatchRootTree.IMT_END_ROOT_LEAF_INDEX` (`ChainBatchRootTree.sol:25`). -/
def imtEndLeafIndex : UInt256 := 3

/-- **The end branch of `verifyTimeoutAbsence` at v35, up to the last-batch check**
(`AtomicInteropProof.sol:77-114`). `_authenticateRoot` runs against leaf 3 (`:85-89`), the hop path
is read from the same words (`:113`), and the zero cascade passes (`:113`, `:130-143`). An end branch
that does not revert runs all three without reverting, so it meets this structure. Its other checks
(`:90-110`: the settlement-layer chain, the imported root's timestamp, `t ≤ deadline`; `:116-123`:
the absence proof) are not part of it. -/
structure EndBranchPassesV35 (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 : UInt256)
    (src batch imtRoot : UInt256) (w : Proof) (sl : SLRef) (hop : HopPath) : Prop where
  auth : authenticateRootV35 E roots src batch imtEndLeafIndex imtRoot w = some sl
  hop_eq : readHop E w = some hop
  last : LastBatchCheck E.node z0 hop

/-! ## The outer hop

The recursive call of `proveShared` opens the chain-id leaf the first hop built
(`chainIdLeafHash(chainIdRoot, sourceChainId)`) inside the imported settlement-layer root, at the
prover's mask `settlementLayerBatchRootMask` (the low half of the packed word,
`MessageHashing.sol:219`). -/

/-- The Merkle path of the recursive hop: `proveShared` slices the words from the first hop's
`ptr` to the end (`L2MessageVerification.sol:53`), parses them again, and `_getProofData` folds
the log-leaf section of that suffix (`MessageHashing.sol:169-178`). -/
def slHopPath (E : Env) (w : Proof) (pd : ProofData) : Option (List UInt256) :=
  (slice w pd.ptr w.length).bind fun rest =>
  (E.parse rest).bind fun md' =>
  slice rest md'.proofStartIndex (md'.proofStartIndex + md'.logLeafProofLen)

/-- **THE SETTLEMENT LAYER'S SHARED TREE BEHIND AN IMPORTED ROOT `R`.** A world description, not
a check any contract performs on the importing chain. On the settlement layer, `MessageRootBase`
keeps `sharedTree`, a `FullMerkle` tree set up with padding `SHARED_ROOT_TREE_EMPTY_HASH`
(`core/message-root/MessageRootBase.sol:140`, `IMessageRoot.sol:14-16`). Slot `chainIndex[c]` holds
`chainIdLeafHash(root, c)`: `root` is `bytes32(0)` when chain `c` is added (`:287`), and the chain
tree's root after each push (`:207-214`). Every update records the tree's root for the block
(`:223-224`). A chain's bootloader imports such `(root, timestamp)` pairs into `interopRoots`, and
the executor compares each with the settlement layer's `historicalRoot` when the importing batch
executes (`state-transition/chain-deps/facets/Executor.sol:96-97`, `:117-158`).

The fields say that `R` is the `rootOf` of `slots` at `height` with padding `zS`, and that each
occupied slot `i` holds `chainIdLeaf (chainRoot i) (chainAt i)`. Which chain sits in which slot,
and with which root, is left free. That an imported root is such a root is the premise
`PROTO-SHARED-ROOT` (`ASSUMPTIONS.md`); that `FullMerkle`'s stored root is `rootOf` is
`FullMerkle` `CachedNodes`. The structure does not ask `slots.length ≤ 2 ^ height`, which
`FullMerkle` always meets on chain; the results quantify over every backing and do not need it,
so the world it describes is only looser than `FullMerkle`'s. -/
structure SharedTreeBacking (node : Hash) (chainIdLeaf : UInt256 → UInt256 → UInt256)
    (zS R : UInt256) where
  /-- The shared tree's occupied slots, in slot order. -/
  slots : List UInt256
  /-- The shared tree's height. -/
  height : ℕ
  /-- The chain registered at slot `i` (`chainIndexToId`). -/
  chainAt : ℕ → UInt256
  /-- The chain root slot `i` was last written with. -/
  chainRoot : ℕ → UInt256
  /-- `R` is the tree's root. -/
  root : R = rootOf node zS slots height
  /-- Each occupied slot is a chain-id leaf. -/
  slot : ∀ i < slots.length, slots.getD i zS = chainIdLeaf (chainRoot i) (chainAt i)

/-- **WHAT AN ACCEPTED OUTER HOP CAN EXHIBIT INSTEAD OF OPENING THE SOURCE CHAIN'S SLOT.**
`m` is the prover's slot mask, `sp` the outer hop's siblings, and `walk` the root the inner
(batch-leaf) walk computed, so `E.chainIdLeaf walk src` is the chain-id leaf the first hop built.
Every compared value is a function of the instance.

* `chainIdLeafCollision`: slot `m` is occupied and `chainIdLeafHash` maps the verifier's pair
  `(walk, src)` and the slot's pair to the same value, though the pairs differ (both are 96-byte
  `keccak` preimages, `MessageHashing.sol:87-89`);
* `paddedSlot`: slot `m` is beyond the occupied slots and the built chain-id leaf IS the padding
  constant (on chain, a 96-byte `keccak` preimage of `keccak(new bytes(96))` that starts with
  `CHAIN_ID_LEAF_PADDING`);
* `pathCollision`: the outer path has the tree's height and a `PathCollision` on it;
* `wrongLength`: the outer path's length is not the tree's height, located by `HeightBreak`. -/
inductive SLHopBreak (E : Env) (zS : UInt256) {R : UInt256}
    (B : SharedTreeBacking E.node E.chainIdLeaf zS R) (sp : List UInt256) (m : ℕ)
    (walk src : UInt256) : Prop
  | chainIdLeafCollision : m < B.slots.length → (walk, src) ≠ (B.chainRoot m, B.chainAt m) →
      E.chainIdLeaf walk src = E.chainIdLeaf (B.chainRoot m) (B.chainAt m) →
      SLHopBreak E zS B sp m walk src
  | paddedSlot : B.slots.length ≤ m → E.chainIdLeaf walk src = zS →
      SLHopBreak E zS B sp m walk src
  | pathCollision : sp.length = B.height →
      PathCollision E.node zS B.slots (fun l => sp.getD l 0) 0 B.height m (E.chainIdLeaf walk src) →
      SLHopBreak E zS B sp m walk src
  | wrongLength :
      HeightBreak E.node zS B.slots (fun l => sp.getD l 0) sp.length B.height m
        (E.chainIdLeaf walk src) →
      SLHopBreak E zS B sp m walk src

/-! ## The first hop, and the source chain's tree

`_authenticateRoot`'s NatSpec (`AtomicInteropProof.sol:145-148`) says it authenticates
`_proof.chainImtRoot` as leaf `_imtRootLeafIndex` of the chain batch root of
`(_proof.sourceChainId, _proof.batchNumber)` against the imported root. Stating that needs the first
hop's path and a description of the source chain's tree entries. -/

/-- The first hop's log-leaf path: the words `[proofStartIndex, proofStartIndex + logLeafProofLen)`
that `_getProofData` folds from the claimed leaf into `batchSettlementRoot`
(`MessageHashing.sol:174-178`). -/
def logHopPath (E : Env) (w : Proof) : Option (List UInt256) :=
  (E.parse w).bind fun md => slice w md.proofStartIndex (md.proofStartIndex + md.logLeafProofLen)

/-- **THE SOURCE CHAIN'S TREE, ENTRY BY ENTRY.** A world description, like `SharedTreeBacking`.
`MessageRootBase._pushChainBatchRoot` pushes `batchLeafHash(chainBatchRoot, batchNumber,
block.timestamp)` (`MessageRootBase.sol:201-209`), so entry `i` of the list `L` is the batch leaf of
a chain batch root, a batch number and a timestamp. A ZKsync OS chain's chain batch root is
`ChainBatchRootTree`'s height-3 tree over four live leaves (logs root, multichain root, IMT root at
batch begin, IMT root at batch end), the reserved leaves 4 to 7 zero (`ChainBatchRootTree.sol:6-11`,
`:21-25`, `:48-61`); the zksync-os bootloader computes it, and `rootOf` with padding `0` is that
tree. That the pushed roots have this shape is part of the premise `PROTO-SHARED-ROOT`. -/
structure ChainTreeEntries (E : Env) (z0 : UInt256) (L : List UInt256) where
  /-- The chain batch root pushed as entry `i`. -/
  batchRoot : ℕ → UInt256
  /-- Its batch number. -/
  number : ℕ → UInt256
  /-- The settlement-layer timestamp of the push. -/
  timestamp : ℕ → UInt256
  /-- The chain batch root tree's live leaves. -/
  rootLeaves : ℕ → List UInt256
  /-- Each entry is a batch leaf (`MessageRootBase.sol:207-209`). -/
  entry : ∀ i < L.length, L.getD i z0 = E.batchLeaf (batchRoot i) (number i) (timestamp i)
  /-- Each chain batch root is the height-3 tree over its leaves, padded with zero. -/
  batchRootTree : ∀ i < L.length, batchRoot i = rootOf E.node 0 (rootLeaves i) treeDepth

/-- **WHAT AN ACCEPTED FIRST HOP AND BATCH-LEAF HOP CAN EXHIBIT INSTEAD OF AUTHENTICATING THE
CLAIMED ROOT.** `hop` is the batch-leaf path (`readAggregationHopPath`), `j = hop.mask` its index
in the source chain's tree `L`, `(bsr, batch, t)` the triple the verifier hashed into the batch
leaf, and `lp` the first hop's log-leaf path. Every compared value is a function of the instance.

* `batchPathCollision`: the batch-leaf path has the tree's height and a `PathCollision` on it;
* `batchPathLength`: its length is not the tree's height, located by `HeightBreak`;
* `paddedEntry`: the tree's height, a padded index, and the batch leaf IS the empty-entry constant
  (on chain, a 128-byte `keccak` preimage of `keccak(new bytes(96))`);
* `batchLeafCollision`: entry `j` is occupied and `batchLeafHash` maps the verifier's triple and the
  entry's triple to the same value, though the triples differ;
* `logPathCollision`: entry `j` is occupied and the log-leaf path collides against entry `j`'s chain
  batch root tree (`PathCollision` at the pinned depth 3). -/
inductive AuthBreak (E : Env) (z0 : UInt256) {L : List UInt256} (height : ℕ)
    (C : ChainTreeEntries E z0 L) (lp : List UInt256) (leafIndex : ℕ) (imtRoot : UInt256)
    (hop : HopPath) (bsr batch t : UInt256) : Prop
  | batchPathCollision : hop.sibs.length = height →
      PathCollision E.node z0 L (fun l => hop.sibs.getD l 0) 0 height hop.mask.val
        (E.batchLeaf bsr batch t) →
      AuthBreak E z0 height C lp leafIndex imtRoot hop bsr batch t
  | batchPathLength :
      HeightBreak E.node z0 L (fun l => hop.sibs.getD l 0) hop.sibs.length height hop.mask.val
        (E.batchLeaf bsr batch t) →
      AuthBreak E z0 height C lp leafIndex imtRoot hop bsr batch t
  | paddedEntry : hop.sibs.length = height → L.length ≤ hop.mask.val → E.batchLeaf bsr batch t = z0 →
      AuthBreak E z0 height C lp leafIndex imtRoot hop bsr batch t
  | batchLeafCollision : hop.mask.val < L.length →
      (bsr, batch, t) ≠ (C.batchRoot hop.mask.val, C.number hop.mask.val, C.timestamp hop.mask.val) →
      E.batchLeaf bsr batch t
        = E.batchLeaf (C.batchRoot hop.mask.val) (C.number hop.mask.val) (C.timestamp hop.mask.val) →
      AuthBreak E z0 height C lp leafIndex imtRoot hop bsr batch t
  | logPathCollision : hop.mask.val < L.length →
      PathCollision E.node 0 (C.rootLeaves hop.mask.val) (fun l => lp.getD l 0) 0 treeDepth leafIndex
        imtRoot →
      AuthBreak E z0 height C lp leafIndex imtRoot hop bsr batch t

/-! ## `parseProofMetadata`, transcribed -/

/-- `SUPPORTED_PROOF_METADATA_VERSION` (`common/Config.sol:30`). -/
def supportedProofMetadataVersion : ℕ := 1

/-- `MessageHashing.parseProofMetadata` (`MessageHashing.sol:101-143`). `_proof[0]` is the
metadata word `m` (an empty proof reverts). If `uint256(m) << 32` is zero, `m` is in the new
format: its first byte must be the supported version (`:122-125`), and bytes 1, 2 and 3 are the
log-leaf path length, the batch-leaf path length and the final-node flag (`:127-130`). Otherwise
the whole proof is a plain Merkle path (`:135-138`). A final node with a nonzero batch-leaf
length reverts (`:140-142`). Byte `i` of a `bytes32` is `(m / 2^(8·(31-i))) % 256`. -/
def parseMeta (w : Proof) : Option Metadata :=
  (word w 0).bind fun m =>
  (if (m.val * 2 ^ 32) % 2 ^ 256 = 0 then
      if m.val / 2 ^ 248 ≠ supportedProofMetadataVersion then none
      else some ⟨1, (m.val / 2 ^ 240) % 2 ^ 8, (m.val / 2 ^ 232) % 2 ^ 8,
        decide ((m.val / 2 ^ 224) % 2 ^ 8 ≠ 0)⟩
    else some ⟨0, w.length, 0, true⟩).bind fun md =>
  if md.finalProofNode = true ∧ md.batchLeafProofLen ≠ 0 then none else some md

/-! ## A concrete instance, for the witnesses

It is not a model of `keccak`. The node hash is `MerkleSpec.LastLeaf.demoHash`, which collides
freely, and the leaf encodings are small sums. The parser is `parseMeta`, and the rejected default
leaf is the deployed constant.

The source chain `300` has pushed batches `0`, `1` and `2`, at timestamps `90`, `95` and `100`.
Batch `i`'s chain batch root is the height-3 tree over `[0, 0, 40 + i, 41 + i]` (zero logs and
multichain roots; the IMT root at batch begin is the one at the previous batch's end). Its three
batch leaves sit at height 2, the shape `DynamicIncrementalMerkle.push` gives three leaves. The
proof authenticates the IMT end root `43` of the last batch, so the batch-leaf path has a left turn
at level 0 (the zero check compares its sibling with `zeros 0`) and a right turn at level 1. The
settlement layer is chain `7`, its imported root is at block `9`, and its shared tree has two slots
at height 1: the settlement layer's own chain at slot 0 (with chain root `0`) and chain `300` at
slot 1. -/

/-- A `parseProofMetadata` word in the new format: version 1, then the three bytes. -/
def authDemoMetaWord (logLen bLen final : ℕ) : UInt256 :=
  ((supportedProofMetadataVersion * 2 ^ 248 + logLen * 2 ^ 240 + bLen * 2 ^ 232
    + final * 2 ^ 224 : ℕ) : UInt256)

/-- The demo environment, with `parseMeta` and the deployed `L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH`. -/
def authDemoEnv : Env where
  node := MerkleSpec.LastLeaf.demoHash
  batchLeaf := fun r b t => r + b + t
  chainIdLeaf := fun r c => r + c
  defaultLeaf := 0x72abee45b59e344af8a6e520241c4744aff26ed411f4c4b00f8af09adada43ba
  parse := parseMeta

/-- The demo `CHAIN_TREE_EMPTY_ENTRY_HASH`, used also as the shared tree's padding (the deployed
`SHARED_ROOT_TREE_EMPTY_HASH` is the same constant, `IMessageRoot.sol:9-16`). -/
def authDemoZ0 : UInt256 := 5

/-- The live leaves of batch `i`'s chain batch root: logs root, multichain root, IMT root at batch
begin, IMT root at batch end. -/
def authDemoRootLeaves (i : ℕ) : List UInt256 := [0, 0, 40 + (i : UInt256), 41 + (i : UInt256)]

/-- Batch `i`'s settlement-layer timestamp. -/
def authDemoTimestamp (i : ℕ) : UInt256 := 90 + 5 * (i : UInt256)

/-- Batch `i`'s chain batch root. -/
def authDemoBatchRootOf (i : ℕ) : UInt256 := rootOf authDemoEnv.node 0 (authDemoRootLeaves i) 3

/-- Batch `i`'s leaf in the source chain's tree. -/
def authDemoEntryLeaf (i : ℕ) : UInt256 :=
  authDemoEnv.batchLeaf (authDemoBatchRootOf i) (i : UInt256) (authDemoTimestamp i)

/-- The proven batch's chain batch root. -/
def authDemoBatchRoot : UInt256 := authDemoBatchRootOf 2

/-- The source chain's tree: three batch leaves, the last of them the proven one. -/
def authDemoChainLeaves : List UInt256 := [authDemoEntryLeaf 0, authDemoEntryLeaf 1, authDemoEntryLeaf 2]

/-- The source chain's tree root at height 2. -/
def authDemoChainRoot : UInt256 := rootOf authDemoEnv.node authDemoZ0 authDemoChainLeaves 2

/-- The source chain's tree, entry by entry. -/
def authDemoEntries : ChainTreeEntries authDemoEnv authDemoZ0 authDemoChainLeaves where
  batchRoot := authDemoBatchRootOf
  number := fun i => (i : UInt256)
  timestamp := authDemoTimestamp
  rootLeaves := authDemoRootLeaves
  entry := by
    intro i hi
    have hi' : i < 3 := by simpa [authDemoChainLeaves] using hi
    interval_cases i <;> rfl
  batchRootTree := fun _ _ => rfl

/-- The shared tree's slots: the settlement layer `7` with chain root `0`, then chain `300`. -/
def authDemoSlots : List UInt256 :=
  [authDemoEnv.chainIdLeaf 0 7, authDemoEnv.chainIdLeaf authDemoChainRoot 300]

/-- The imported roots: the shared tree's root at `(7, 9)`, nothing elsewhere. -/
def authDemoRoots (c b : UInt256) : UInt256 :=
  if c = 7 ∧ b = 9 then rootOf authDemoEnv.node authDemoZ0 authDemoSlots 1 else 0

/-- The demo proof. The first hop: the metadata (log length 3, batch length 2, not final), the
log-leaf siblings of leaf 3 (leaf 2, the node over leaves 0 and 1, and the zero subtree over
leaves 4 to 7), `t = 100`, batch mask `2`, the batch siblings `zeros 0` and the node over the first
two batch leaves, the packed word (SL block `9`, slot mask `1`) and SL chain `7`. The second hop: its
metadata (log length 1, final) and the sibling slot 0. -/
def authDemoProof : Proof :=
  [authDemoMetaWord 3 2 0, 42, authDemoEnv.node 0 0, zeros authDemoEnv.node 0 2, 100, 2, authDemoZ0,
    authDemoEnv.node (authDemoEntryLeaf 0) (authDemoEntryLeaf 1),
    ((9 * 2 ^ 128 + 1 : ℕ) : UInt256), 7,
    authDemoMetaWord 1 0 1, authDemoEnv.chainIdLeaf 0 7]

/-- The shared tree behind `authDemoRoots 7 9`. -/
def authDemoShared :
    SharedTreeBacking authDemoEnv.node authDemoEnv.chainIdLeaf authDemoZ0 (authDemoRoots 7 9) where
  slots := authDemoSlots
  height := 1
  chainAt := fun i => if i = 0 then 7 else 300
  chainRoot := fun i => if i = 0 then 0 else authDemoChainRoot
  root := by simp [authDemoRoots]
  slot := by
    intro i hi
    have hi' : i < 2 := by simpa [authDemoSlots] using hi
    interval_cases i <;> rfl

end AttackVectors.AuthenticateRootAtV35
