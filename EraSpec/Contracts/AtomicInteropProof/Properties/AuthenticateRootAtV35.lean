import EraSpec.Contracts.AtomicInteropProof.Specs.AuthenticateRootAtV35

/-!
# Properties: the v35 `_authenticateRoot` refactor is exact, and the last-batch check runs on the verified walk

era-contracts `draft/v0.35.0` at `d9f6789`. Definitions and citations are in
`../Specs/AuthenticateRootAtV35.lean`, and proofs are in `../Proofs/AuthenticateRootAtV35.lean`.

* `ReadSLEqParsedV35` and `ReadHopIsFoldedPathV35`: the two positional accessors return exactly the
  words `_getProofData` consumed, for every proof on which `_getProofData` succeeds with a non-final
  first hop.
* `AuthenticateRootRefactorExactV35`: the v35 `_authenticateRoot` and the pin's are the same function
  of their inputs. The refactor changes no accepted input and no returned value.
* `HopReadTotalAfterAuthV35`: once `_authenticateRoot` has accepted, `readAggregationHopPath` cannot
  revert. Its new final-node revert, and its out-of-range reads, cannot be reached from
  `verifyTimeoutAbsence`.
* `LastBatchCheckOnVerifiedWalkV35`: the mask and siblings `_verifyLastBatchInRoot` inspects are the
  walk whose result the verifier bound into the chain-id leaf. That walk is in range for its own
  length, and it starts from the batch leaf carrying the same `t` the deadline is compared with.
  This discharges, at v35, the "walk = verified path" half of `LastLeaf`'s accepted-path premises.
* `EndBranchLastLeafOrBreakV35`: an accepted v35 end branch whose chain-id leaf binds the chain tree's
  real root has one of these outcomes:
  - the proven leaf is the tree's last leaf;
  - a `PinnedBreak`;
  - a `PathCollision`;
  - a `HeightBreak` (the path length is not the tree height);
  - the presented batch leaf hash is the empty-entry constant (a padded index);
  - a collision of `chainIdLeafHash` on the two named pairs.
  There is no length or index-range premise, so this covers faithfulness major #4 (prover-chosen
  length and index), and every alternative is a break located on the instance.
* `EndBranchPassesV35Satisfiable`: the premises are met by a concrete two-hop proof whose zero
  cascade runs and passes.
-/

namespace AttackVectors.AuthenticateRootAtV35

open MerkleSpec MerkleSpec.Verifier MerkleSpec.LastLeaf

/-- **THE POSITIONAL SL READ IS THE PARSE.** On every proof where `_getProofData` succeeds with a
non-final first hop, `readSettlementLayerReference` returns that hop's `(slBatchNumber, slChainId,
l1BatchTimestamp)`. This holds for every leaf, mask, chain and batch, since none of those words
depend on them. -/
def Properties.ReadSLEqParsedV35 : Prop :=
  ∀ (E : Env) (chainId batchNumber mask leaf : UInt256) (w : Proof) (pd : ProofData),
    getProofData E chainId batchNumber mask leaf w = some pd → pd.finalProofNode = false →
      readSL E w = some ⟨pd.slBatchNumber, pd.slChainId, pd.l1BatchTimestamp⟩

/-- **THE POSITIONAL HOP READ IS THE FOLDED PATH.** On the same proofs, `readAggregationHopPath`
returns a mask and siblings that the verifier itself folded, through `Merkle.calculateRootMemory`,
into the root inside `pd.chainIdLeaf`. -/
def Properties.ReadHopIsFoldedPathV35 : Prop :=
  ∀ (E : Env) (chainId batchNumber mask leaf : UInt256) (w : Proof) (pd : ProofData),
    getProofData E chainId batchNumber mask leaf w = some pd → pd.finalProofNode = false →
      ∃ hop, readHop E w = some hop ∧ ∃ chainIdRoot,
        calcRoot E.node hop.sibs hop.mask.val
            (E.batchLeaf pd.batchSettlementRoot batchNumber pd.l1BatchTimestamp) = some chainIdRoot
          ∧ pd.chainIdLeaf = E.chainIdLeaf chainIdRoot chainId

/-- **THE REFACTOR IS EXACT.** The v35 `_authenticateRoot` (positional read,
`AtomicInteropProof.sol:155-189`) and the pin's (re-parse, `:256-290@c67894b9`) agree on every input:
same reverts, same returned triple. -/
def Properties.AuthenticateRootRefactorExactV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (src batch leafIndex imtRoot : UInt256)
    (w : Proof),
    authenticateRootV35 E roots src batch leafIndex imtRoot w
      = authenticateRootPin E roots src batch leafIndex imtRoot w

/-- **THE HOP READ CANNOT REVERT AFTER AUTHENTICATION.** If `_authenticateRoot` accepted a proof,
`readAggregationHopPath` returns on it. So its final-node revert (`MessageHashing.sol:254-256`) is
unreachable from `verifyTimeoutAbsence`, because `_authenticateRoot` already rejected final nodes
(`AtomicInteropProof.sol:177-179`). -/
def Properties.HopReadTotalAfterAuthV35 : Prop :=
  ∀ (E : Env) (roots : UInt256 → UInt256 → UInt256) (src batch leafIndex imtRoot : UInt256)
    (w : Proof) (sl : SLRef),
    authenticateRootV35 E roots src batch leafIndex imtRoot w = some sl →
      ∃ hop, readHop E w = some hop

/-- **THE LAST-BATCH CHECK RUNS ON THE VERIFIED WALK.** If the v35 end branch passes, then the first
hop `pd` of the authenticated proof satisfies all of the following:

* the returned triple is `pd`'s;
* the mask the check inspects is in range for the sibling count;
* `pd.chainIdLeaf` binds exactly the walk of those siblings from the batch leaf
  `batchLeafHash(batchSettlementRoot, batch, t)`, where `t` is the timestamp `_authenticateRoot`
  returned;
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

/-- **AN ACCEPTED v35 END BRANCH: THE LAST LEAF, OR A LOCATED BREAK.** Let `L` be the source chain's
L1 chain-tree leaves inside the cited root, at the tree's height `height` (so
`L.length ≤ 2 ^ height`). Assume the shared-tree hop binds this proof's chain-id leaf to that
tree's real root. That is the remaining outer-hop premise, which this file does not discharge.
Then, with `x` the presented batch leaf, `j` the mask and `k` the sibling count, one of these
holds:

* `chainIdLeafHash` collides on the pair the verifier built and the tree's pair;
* `k` is the height, `j` is occupied, and `j` is the last leaf, or there is a `PinnedBreak` at
  `j`, or a `PathCollision` on the submitted path;
* `k` is the height, `j` is a padded index, and the batch leaf hash `x` IS the empty-entry
  constant `z0`, or there is a `PathCollision`;
* `k` is not the height, located by `HeightBreak`.

The path length and the index are the prover's (faithfulness major #4). Both are quantified, and
neither is assumed. -/
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

/-- **THE PREMISES ARE SATISFIABLE, WITH THE ZERO CASCADE EXERCISED.** The demo two-hop proof is
authenticated against leaf 3, its hop path is read, and `_verifyLastBatchInRoot` passes on a
one-level path whose node is a left child. So the check really compares a sibling with `zeros 0`.
The demo chain tree `[x]` at height 1 also meets the outer-hop binding premise of
`EndBranchLastLeafOrBreakV35`, with `x` the demo batch leaf. -/
def Properties.EndBranchPassesV35Satisfiable : Prop :=
  ∃ (E : Env) (roots : UInt256 → UInt256 → UInt256) (z0 src batch imtRoot : UInt256) (w : Proof)
    (sl : SLRef) (hop : HopPath) (L : List UInt256) (height : ℕ),
    EndBranchPassesV35 E roots z0 src batch imtRoot w sl hop
      ∧ hop.sibs ≠ [] ∧ (hop.mask.val / 2 ^ 0) % 2 = 0
      ∧ L.length ≤ 2 ^ height
      ∧ (∀ pd, getProofData E src batch imtEndLeafIndex imtRoot w = some pd →
          pd.chainIdLeaf = E.chainIdLeaf (rootOf E.node z0 L height) src)

end AttackVectors.AuthenticateRootAtV35
