import EraSpec.Contracts.AtomicInteropProof.Specs.AuthenticateRootAtV35

/-!
# Properties: `_authenticateRoot` at v35, its readers, and what it authenticates

era-contracts `draft/v0.35.0` at `b17415d20` (the cited files are the same blobs at `d9f6789`).
Definitions and citations are in `../Specs/AuthenticateRootAtV35.lean`, and proofs are in
`../Proofs/AuthenticateRootAtV35.lean`. Every universally quantified statement here holds for every
parser `E.parse` and every hash function in `E`, and none takes a hash premise.

The readers (the comparison with the pin's `_authenticateRoot` is History,
`../History/Properties/AuthenticateRootAtV35.lean`):

* `ReadSLEqParsedV35` and `ReadHopIsFoldedPathV35`: the two positional readers return exactly the
  words `_getProofData` consumed, on every proof on which `_getProofData` succeeds with a non-final
  first hop.
* `HopReadTotalAfterAuthV35`: once `_authenticateRoot` has accepted, `readAggregationHopPath` does
  not revert. Its new final-node revert, and its out-of-range reads, cannot be reached from
  `verifyTimeoutAbsence`.

The walks the end branch relies on:

* `LastBatchCheckOnVerifiedWalkV35`: the mask and siblings `_verifyLastBatchInRoot` inspects are the
  batch-leaf walk the verifier folded into the chain-id leaf, from the batch leaf carrying the
  timestamp `_authenticateRoot` returned, with the mask in range for the walk's length. So the
  path `LastLeafFaithful.LastBatchPathAccepted` describes is the verifier's own: its `inBounds` and
  `zeroCheck` fields hold, and its `authenticated` field is what the chain-id leaf must bind.
* `SLHopIsVerifiedWalkV35`: the outer hop's path walks that chain-id leaf, at the prover's slot
  mask, to the nonzero imported root at the settlement-layer coordinates `_authenticateRoot`
  returned.

The last leaf:

* `EndBranchLastLeafOrBreakV35`: if the chain-id leaf binds the source chain's tree root (the
  outer hop taken as a premise), the batch-leaf path of an accepted end branch opens the tree's last
  leaf, or the instance exhibits a located break.
* `EndBranchTwoHopLastLeafOrBreakV35`: the outer hop is not a premise. If the imported root is
  the settlement layer's shared tree (`SharedTreeBacking`, `PROTO-SHARED-ROOT`) and the source
  chain's slot commits its tree, the batch leaf of an accepted end branch is the tree's last leaf,
  at the tree's height, or the instance exhibits a `LastLeafAnyLengthBreak` on the batch-leaf path
  or an `SLHopBreak` on the outer hop.

What `_authenticateRoot` authenticates:

* `AuthenticateRootSoundV35`: its NatSpec claim (`AtomicInteropProof.sol:145-148`), for every leaf
  index. Under the same world description plus the source chain's tree entries (`ChainTreeEntries`),
  the claimed root is the given leaf of the chain batch root of an entry of the source chain's tree
  whose batch number is the proof's and whose timestamp is the returned one, or the instance exhibits
  an `AuthBreak` (first hop or batch-leaf hop) or an `SLHopBreak` (outer hop).
* `EndBranchSoundV35`: the same for the end branch, with the entry the tree's last: the claimed root
  is the IMT end root of the source chain's last batch inside the imported root, or a located break.

* `EndBranchV35Satisfiable`: every premise above is met at once, on a concrete two-hop proof read
  by the transcribed parser, with a deployed tree shape and the zero check exercised; on it no
  `SLHopBreak` and no `AuthBreak` holds.
-/

namespace AttackVectors.AuthenticateRootAtV35

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf MerkleSpec.LastLeafFaithful

/-- **THE POSITIONAL SL READ IS THE PARSE.** On every proof where `_getProofData` succeeds with a
non-final first hop, `readSettlementLayerReference` returns that hop's `(slBatchNumber, slChainId,
l1BatchTimestamp)`. This holds for every leaf, mask, chain and batch, since none of those words
depend on them. -/
def Properties.ReadSLEqParsedV35 : Prop :=
  ∀ (E : Env) (chainId batchNumber mask leaf : UInt256) (w : Proof) (pd : ProofData),
    getProofData E chainId batchNumber mask leaf w = some pd → pd.finalProofNode = false →
      readSL E w = some ⟨pd.slBatchNumber, pd.slChainId, pd.l1BatchTimestamp⟩

/-- **THE POSITIONAL HOP READ IS THE FOLDED PATH.** On the same proofs, `readAggregationHopPath`
returns a mask and siblings that the verifier itself folded, through `Merkle.calculateRootMemory`
(length below 256, mask in range), from the batch leaf `batchLeafHash(batchSettlementRoot,
batchNumber, l1BatchTimestamp)` into the root inside `pd.chainIdLeaf`. -/
def Properties.ReadHopIsFoldedPathV35 : Prop :=
  ∀ (E : Env) (chainId batchNumber mask leaf : UInt256) (w : Proof) (pd : ProofData),
    getProofData E chainId batchNumber mask leaf w = some pd → pd.finalProofNode = false →
      ∃ hop, readHop E w = some hop ∧ ∃ chainIdRoot,
        calcRoot E.node hop.sibs hop.mask.val
            (E.batchLeaf pd.batchSettlementRoot batchNumber pd.l1BatchTimestamp) = some chainIdRoot
          ∧ pd.chainIdLeaf = E.chainIdLeaf chainIdRoot chainId

/-- **THE HOP READ CANNOT REVERT AFTER AUTHENTICATION.** If `_authenticateRoot` accepted a proof,
`readAggregationHopPath` returns on it. So its final-node revert (`MessageHashing.sol:254-256`) is
unreachable from `verifyTimeoutAbsence`, because `_authenticateRoot` already rejected final nodes
(`AtomicInteropProof.sol:177-179`). -/
def Properties.HopReadTotalAfterAuthV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (src batch leafIndex imtRoot : UInt256)
    (w : Proof) (sl : SLRef),
    authenticateRootV35 E roots src batch leafIndex imtRoot w = some sl →
      ∃ hop, readHop E w = some hop

/-- **THE LAST-BATCH CHECK RUNS ON THE VERIFIED WALK.** If the v35 end branch passes, then the
first hop `pd` of the authenticated proof satisfies all of the following:

* it is not a final node, and the returned triple is `pd`'s;
* the mask the check inspects is in range for the sibling count;
* `pd.chainIdLeaf` is `chainIdLeafHash` of the walk of those siblings from the batch leaf
  `batchLeafHash(batchSettlementRoot, batch, t)`, where `t` is the timestamp `_authenticateRoot`
  returned, and the source chain id;
* every left-child sibling of that walk is the zero cascade. -/
def Properties.LastBatchCheckOnVerifiedWalkV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 src batch imtRoot : UInt256) (w : Proof)
    (sl : SLRef) (hop : HopPath),
    EndBranchPassesV35 E roots z0 src batch imtRoot w sl hop →
      ∃ pd : ProofData,
        getProofData E src batch imtEndLeafIndex imtRoot w = some pd
          ∧ pd.finalProofNode = false
          ∧ sl = ⟨pd.slBatchNumber, pd.slChainId, pd.l1BatchTimestamp⟩
          ∧ hop.mask.val < 2 ^ hop.sibs.length
          ∧ pd.chainIdLeaf = E.chainIdLeaf
              (walkPure E.node (fun l => hop.sibs.getD l 0) 0 hop.sibs.length hop.mask.val
                (E.batchLeaf pd.batchSettlementRoot batch sl.l1BatchTimestamp)) src
          ∧ ∀ l < hop.sibs.length, (hop.mask.val / 2 ^ l) % 2 = 0 →
              (fun l => hop.sibs.getD l 0) l = zeros E.node z0 l

/-- **THE OUTER HOP IS A VERIFIED WALK AT THE RETURNED COORDINATES.** If `_authenticateRoot`
accepted a proof, its first hop `pd` is not final and gave the returned triple, and the outer
hop's path `sp` (`slHopPath`) walks `pd.chainIdLeaf`, at the prover's slot mask
`settlementLayerBatchRootMask` (in range for the path), to `interopRoots(slChainId, slBlock).root`
at exactly the `(slChainId, slBlock)` `_authenticateRoot` returned, and that root is nonzero.
`verifyTimeoutAbsence` reads the imported root's timestamp at those same coordinates
(`AtomicInteropProof.sol:94`). -/
def Properties.SLHopIsVerifiedWalkV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (src batch leafIndex imtRoot : UInt256)
    (w : Proof) (sl : SLRef),
    authenticateRootV35 E roots src batch leafIndex imtRoot w = some sl →
      ∃ (pd : ProofData) (sp : List UInt256),
        getProofData E src batch leafIndex imtRoot w = some pd
          ∧ pd.finalProofNode = false
          ∧ sl = ⟨pd.slBatchNumber, pd.slChainId, pd.l1BatchTimestamp⟩
          ∧ slHopPath E w pd = some sp
          ∧ pd.slBatchRootMask.val < 2 ^ sp.length
          ∧ walkPure E.node (fun l => sp.getD l 0) 0 sp.length pd.slBatchRootMask.val
              pd.chainIdLeaf = roots sl.slChainId sl.slBatchNumber
          ∧ roots sl.slChainId sl.slBatchNumber ≠ 0

/-- **AN ACCEPTED v35 END BRANCH, OUTER HOP AS A PREMISE: THE LAST LEAF, OR A LOCATED BREAK.** Let
`L` be the source chain's tree leaves at height `height` (`L.length ≤ 2 ^ height`), and assume the
chain-id leaf the first hop built is `chainIdLeafHash` of that tree's root and the source chain.
`EndBranchTwoHopLastLeafOrBreakV35` replaces this premise by a description of the imported root.
Then, with `x` the batch leaf the verifier built, `j` the mask and `k` the sibling count, one of
these holds:

* `chainIdLeafHash` maps the verifier's pair and the tree's pair to the same value, and the walk is
  not the tree's root;
* `k` is the height, `j` is occupied, and `j` is the last leaf, or there is a `PinnedBreak` at `j`,
  or a `PathCollision` on the submitted path;
* `k` is the height, `j` is a padded index, and `x` IS the empty-entry constant `z0`, or there is
  a `PathCollision`;
* `k` is not the height, located by `HeightBreak`.

The path length and the index are the prover's. Neither is assumed. -/
def Properties.EndBranchLastLeafOrBreakV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 src batch imtRoot : UInt256) (w : Proof)
    (sl : SLRef) (hop : HopPath) (L : List UInt256) (height : ℕ),
    EndBranchPassesV35 E roots z0 src batch imtRoot w sl hop →
    L.length ≤ 2 ^ height →
    (∀ pd, getProofData E src batch imtEndLeafIndex imtRoot w = some pd →
      pd.chainIdLeaf = E.chainIdLeaf (rootOf E.node z0 L height) src) →
    ∃ pd : ProofData, getProofData E src batch imtEndLeafIndex imtRoot w = some pd ∧
      let x := E.batchLeaf pd.batchSettlementRoot batch sl.l1BatchTimestamp
      let sibs := fun l => hop.sibs.getD l 0
      let walk := walkPure E.node sibs 0 hop.sibs.length hop.mask.val x
      (walk ≠ rootOf E.node z0 L height
          ∧ E.chainIdLeaf walk src = E.chainIdLeaf (rootOf E.node z0 L height) src)
      ∨ (hop.sibs.length = height ∧ hop.mask.val < L.length
          ∧ (hop.mask.val + 1 = L.length ∨ PinnedBreak E.node z0 L hop.mask.val
              ∨ PathCollision E.node z0 L sibs 0 height hop.mask.val x))
      ∨ (hop.sibs.length = height ∧ L.length ≤ hop.mask.val
          ∧ (x = z0 ∨ PathCollision E.node z0 L sibs 0 height hop.mask.val x))
      ∨ HeightBreak E.node z0 L sibs hop.sibs.length height hop.mask.val x

/-- **AN ACCEPTED v35 END BRANCH, BOTH HOPS: THE LAST LEAF, OR A LOCATED BREAK.** Let `B` describe
the settlement layer's shared tree behind the imported root at the coordinates `_authenticateRoot`
returned (`SharedTreeBacking`, premise `PROTO-SHARED-ROOT`), let `L` be the source chain's tree
leaves at height `height` (`L.length ≤ 2 ^ height`), and assume every slot of `B` registered to the
source chain was last written with that tree's root. No premise is made on the outer hop's path.
Then, with `x` the batch leaf the verifier built, `j` the mask, `k` the sibling count, `walk` the
inner walk's root and `sp` the outer hop's path (`slHopPath`), one of these holds:

* `k` is the tree's height, `j` is its last leaf, and `x` is that leaf's entry;
* a `LastLeafAnyLengthBreak` on the batch-leaf path (`LastLeafFaithful`: a `HeightBreak`, a padded
  index whose leaf hash is `z0`, a `PinnedBreak`, or a `PathCollision`);
* an `SLHopBreak` on the outer hop at the prover's slot mask: a `chainIdLeafHash` collision with
  the opened slot's pair, a padded slot equal to the built chain-id leaf, or a `PathCollision` or
  `HeightBreak` on `sp` against the shared tree.

Every break is located on the instance. -/
def Properties.EndBranchTwoHopLastLeafOrBreakV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 zS src batch imtRoot : UInt256)
    (w : Proof) (sl : SLRef) (hop : HopPath)
    (B : SharedTreeBacking E.node E.chainIdLeaf zS (roots sl.slChainId sl.slBatchNumber))
    (L : List UInt256) (height : ℕ),
    EndBranchPassesV35 E roots z0 src batch imtRoot w sl hop →
    L.length ≤ 2 ^ height →
    (∀ i < B.slots.length, B.chainAt i = src → B.chainRoot i = rootOf E.node z0 L height) →
    ∃ (pd : ProofData) (sp : List UInt256),
      getProofData E src batch imtEndLeafIndex imtRoot w = some pd ∧ slHopPath E w pd = some sp ∧
      let x := E.batchLeaf pd.batchSettlementRoot batch sl.l1BatchTimestamp
      let sibs := fun l => hop.sibs.getD l 0
      let walk := walkPure E.node sibs 0 hop.sibs.length hop.mask.val x
      (hop.sibs.length = height ∧ hop.mask.val + 1 = L.length ∧ L.getD hop.mask.val z0 = x)
        ∨ LastLeafAnyLengthBreak E.node z0 L sibs hop.sibs.length height hop.mask.val x
        ∨ SLHopBreak E zS B sp pd.slBatchRootMask.val walk src

/-- **WHAT `_authenticateRoot` AUTHENTICATES, ANY LEAF INDEX: ITS NATSPEC CLAIM, OR A LOCATED
BREAK.** Let `B` describe the settlement layer's shared tree behind the imported root at the
coordinates `_authenticateRoot` returned (`SharedTreeBacking`), let `L` be the source chain's tree at
height `height`, described entry by entry by `C` (`ChainTreeEntries`: each entry a batch leaf of a
height-3 chain batch root), and assume every slot of `B` registered to the source chain was last
written with that tree's root (premises `PROTO-SHARED-ROOT`). No premise is made on any of the
three paths in the proof. If `_authenticateRoot` accepts the claimed root `imtRoot` at leaf index
`leafIndex` for `(src, batch)`, then, with `j` the batch-leaf path's index, one of these holds:

* the batch-leaf path has the tree's height, entry `j` is occupied, its batch number is `batch`,
  its timestamp is the `l1BatchTimestamp` `_authenticateRoot` returned, and leaf `leafIndex` of its
  chain batch root is `imtRoot`;
* an `AuthBreak` on the first hop or the batch-leaf hop;
* an `SLHopBreak` on the outer hop.

Every break is located on the instance. -/
def Properties.AuthenticateRootSoundV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 zS src batch leafIndex imtRoot : UInt256)
    (w : Proof) (sl : SLRef)
    (B : SharedTreeBacking E.node E.chainIdLeaf zS (roots sl.slChainId sl.slBatchNumber))
    (L : List UInt256) (height : ℕ) (C : ChainTreeEntries E z0 L),
    authenticateRootV35 E roots src batch leafIndex imtRoot w = some sl →
    (∀ i < B.slots.length, B.chainAt i = src → B.chainRoot i = rootOf E.node z0 L height) →
    ∃ (pd : ProofData) (lp sp : List UInt256) (hop : HopPath),
      getProofData E src batch leafIndex imtRoot w = some pd ∧ logHopPath E w = some lp
        ∧ readHop E w = some hop ∧ slHopPath E w pd = some sp ∧
      ((hop.sibs.length = height ∧ hop.mask.val < L.length ∧ C.number hop.mask.val = batch
          ∧ C.timestamp hop.mask.val = sl.l1BatchTimestamp
          ∧ (C.rootLeaves hop.mask.val).getD leafIndex.val 0 = imtRoot)
        ∨ AuthBreak E z0 height C lp leafIndex.val imtRoot hop pd.batchSettlementRoot batch
            sl.l1BatchTimestamp
        ∨ SLHopBreak E zS B sp pd.slBatchRootMask.val
            (walkPure E.node (fun l => hop.sibs.getD l 0) 0 hop.sibs.length hop.mask.val
              (E.batchLeaf pd.batchSettlementRoot batch sl.l1BatchTimestamp)) src)

/-- **THE END BRANCH, ALL THREE HOPS: THE IMT END ROOT OF THE SOURCE CHAIN'S LAST BATCH, OR A LOCATED
BREAK.** Under the premises of `AuthenticateRootSoundV35` and `L.length ≤ 2 ^ height`, an end branch
that passes up to the last-batch check (`EndBranchPassesV35`, leaf index 3) has one of these:

* the batch-leaf path has the tree's height, `j` is the tree's LAST entry, its batch number is
  `batch`, its timestamp is the returned `l1BatchTimestamp`, and leaf 3 (the IMT root at batch end)
  of its chain batch root is `imtRoot`;
* a `LastLeafAnyLengthBreak` on the batch-leaf path;
* an `AuthBreak` on the first hop or the batch-leaf hop;
* an `SLHopBreak` on the outer hop. -/
def Properties.EndBranchSoundV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 zS src batch imtRoot : UInt256)
    (w : Proof) (sl : SLRef) (hop : HopPath)
    (B : SharedTreeBacking E.node E.chainIdLeaf zS (roots sl.slChainId sl.slBatchNumber))
    (L : List UInt256) (height : ℕ) (C : ChainTreeEntries E z0 L),
    EndBranchPassesV35 E roots z0 src batch imtRoot w sl hop →
    L.length ≤ 2 ^ height →
    (∀ i < B.slots.length, B.chainAt i = src → B.chainRoot i = rootOf E.node z0 L height) →
    ∃ (pd : ProofData) (lp sp : List UInt256),
      getProofData E src batch imtEndLeafIndex imtRoot w = some pd ∧ logHopPath E w = some lp
        ∧ slHopPath E w pd = some sp ∧
      let x := E.batchLeaf pd.batchSettlementRoot batch sl.l1BatchTimestamp
      let sibs := fun l => hop.sibs.getD l 0
      ((hop.sibs.length = height ∧ hop.mask.val + 1 = L.length ∧ C.number hop.mask.val = batch
          ∧ C.timestamp hop.mask.val = sl.l1BatchTimestamp
          ∧ (C.rootLeaves hop.mask.val).getD 3 0 = imtRoot)
        ∨ LastLeafAnyLengthBreak E.node z0 L sibs hop.sibs.length height hop.mask.val x
        ∨ AuthBreak E z0 height C lp 3 imtRoot hop pd.batchSettlementRoot batch sl.l1BatchTimestamp
        ∨ SLHopBreak E zS B sp pd.slBatchRootMask.val
            (walkPure E.node sibs 0 hop.sibs.length hop.mask.val x) src)

/-- **THE PREMISES ARE SATISFIABLE TOGETHER, ON A DEPLOYED SHAPE.** On `authDemoEnv` (the
transcribed parser `parseMeta`, the deployed default-leaf constant, toy hashes) and the two-hop
`authDemoProof`, all of the following hold at once:

* the end branch passes (`EndBranchPassesV35`) against leaf 3, with a first hop that is not final
  (the premise of `ReadSLEqParsedV35` and `ReadHopIsFoldedPathV35`), a log-leaf path `lp` and an
  outer-hop path `sp`;
* the zero check fires: the batch-leaf path has a left turn (at level 0);
* the source chain's tree is three batch leaves at height 2, the shape
  `DynamicIncrementalMerkle.push` gives three leaves, described entry by entry by `C`, and the proven
  batch is its last entry;
* the chain-id leaf binds that tree's root (the premise of `EndBranchLastLeafOrBreakV35`);
* the shared tree `B` (two slots at height 1) commits the source chain's tree in its slot (with `C`,
  the premises of `EndBranchTwoHopLastLeafOrBreakV35`, `AuthenticateRootSoundV35` and
  `EndBranchSoundV35`);
* no `SLHopBreak` and no `AuthBreak` holds, so neither break predicate is always true. -/
def Properties.EndBranchV35Satisfiable : Prop :=
  ∃ (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 zS src batch imtRoot : UInt256)
    (w : Proof) (sl : SLRef) (hop : HopPath)
    (B : SharedTreeBacking E.node E.chainIdLeaf zS (roots sl.slChainId sl.slBatchNumber))
    (L : List UInt256) (height : ℕ) (C : ChainTreeEntries E z0 L) (pd : ProofData)
    (lp sp : List UInt256),
    E.parse = parseMeta
      ∧ EndBranchPassesV35 E roots z0 src batch imtRoot w sl hop
      ∧ getProofData E src batch imtEndLeafIndex imtRoot w = some pd ∧ pd.finalProofNode = false
      ∧ logHopPath E w = some lp ∧ slHopPath E w pd = some sp
      ∧ (∃ l < hop.sibs.length, (hop.mask.val / 2 ^ l) % 2 = 0)
      ∧ L.length = 3 ∧ height = 2 ∧ hop.mask.val + 1 = L.length
      ∧ L.length ≤ 2 ^ height
      ∧ (∀ pd', getProofData E src batch imtEndLeafIndex imtRoot w = some pd' →
          pd'.chainIdLeaf = E.chainIdLeaf (rootOf E.node z0 L height) src)
      ∧ (∀ i < B.slots.length, B.chainAt i = src → B.chainRoot i = rootOf E.node z0 L height)
      ∧ ¬ SLHopBreak E zS B sp pd.slBatchRootMask.val
          (walkPure E.node (fun l => hop.sibs.getD l 0) 0 hop.sibs.length hop.mask.val
            (E.batchLeaf pd.batchSettlementRoot batch sl.l1BatchTimestamp)) src
      ∧ ¬ AuthBreak E z0 height C lp 3 imtRoot hop pd.batchSettlementRoot batch sl.l1BatchTimestamp

end AttackVectors.AuthenticateRootAtV35
