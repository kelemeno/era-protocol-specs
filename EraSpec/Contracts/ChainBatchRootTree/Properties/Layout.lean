import EraSpec.Contracts.ChainBatchRootTree.Specs.Layout

/-!
# Properties: the chain batch root is the height-3 tree over its four leaves, and a depth-3 path
opens one of them or locates a collision

No property assumes anything about `keccak` beyond the two documented values where named
(`ReservedSubtreeDocumented`, `EmptyImtRootDocumented`), each a premise on specific keccak inputs.
Proofs: `../Proofs/Layout.lean`.

* `ComputeIsRootOfHeightThree`: under the documented reserved value, `compute` is
  `rootOf (node keccak) 0 [a, b, c, d] 3`, the `FullMerkle` fold at height 3 with padding `0`.
  `ComputeRootNeedsDocumentedValue` shows the premise is satisfiable and load-bearing.
* `LiveLeafOpeningPinsLeafOrCollision` (no premise), `ReservedLeafOpeningPinsZeroOrCollision`
  and `OpeningPinsLeafOrCollision` (documented reserved value): a length-3 walk at index `j` that
  reaches `compute a b c d` has claimed leaf `[a, b, c, d][j]` (`j < 4`) or `0` (`4 ≤ j < 8`), or
  exhibits an `OpeningCollision`: a keccak collision on two named 64-byte node preimages.
* `ImtRootHopPinsLeafOrCollision`: the atomic-interop IMT-root hop (`TREE_DEPTH` pinned, mask 2 or
  3) opens exactly `c` or `d`, or locates a collision. `ImtRootHopDepthPinNeeded`: without the
  depth pin, a length-2 path with the same mask is accepted for the claimed root `node 0 0`.
* `HonestOpeningAccepted`, `HonestOpeningNoCollision`, `ReservedOpeningWitness`,
  `ImtRootHopWitness`, `OpeningCollisionFires`: the honest proof satisfies the premises (with the
  documented value where needed) and locates no collision; on a degenerate keccak a wrong leaf is
  accepted and the collision is located.
* `GenesisLeafOneOpensZeroOrCollision`, `GenesisLeafOneNotInitialAggregatedRoot`,
  `GenesisLeafOneRejectsInitialAggregatedRootWitness`: leaf 1 of the genesis root opens only to
  `0`; opening it at a `MessageRoot`'s initial aggregated root needs that root to be `0` or a
  located collision, and on a concrete keccak neither happens.
-/

namespace Contracts.ChainBatchRootTree

open MerkleSpec MerkleSpec.Verifier
open AttackVectors.BundleHashEncoding (HashCollision word toBytesBE)

/-! ## (a) The layout -/

/-- **`compute` IS THE HEIGHT-3 TREE OVER `[a, b, c, d]` WITH PADDING `0`.** Under the documented
value of `RESERVED_SUBTREE_NODE` (`z2` over zero leaves), `ChainBatchRootTree.compute(a, b, c, d)`
equals `rootOf (node keccak) 0 [a, b, c, d] TREE_DEPTH`: leaves `4 … 7` are the padding `0`. -/
def Properties.ComputeIsRootOfHeightThree : Prop :=
  ∀ (keccak : Keccak) (a b c d : UInt256),
    ReservedSubtreeDocumented keccak →
      compute keccak a b c d = rootOf (node keccak) 0 (liveLeaves a b c d) TREE_DEPTH

/-- **THE DOCUMENTED-VALUE PREMISE IS SATISFIABLE AND LOAD-BEARING.** Some keccak meets
`ReservedSubtreeDocumented`, and for some keccak `compute` differs from the height-3 fold. -/
def Properties.ComputeRootNeedsDocumentedValue : Prop :=
  (∃ keccak : Keccak, ReservedSubtreeDocumented keccak)
    ∧ ∃ (keccak : Keccak) (a b c d : UInt256),
        compute keccak a b c d ≠ rootOf (node keccak) 0 (liveLeaves a b c d) TREE_DEPTH

/-! ## (b) Opening a leaf with a depth-3 path -/

/-- **A DEPTH-3 PATH INTO THE LIVE HALF OPENS ITS LEAF, OR LOCATES A COLLISION.** No hash premise.
`calculateRootMemory` with a 3-sibling path at index `j < 4` that returns `compute a b c d` has
claimed leaf `x = [a, b, c, d][j]`, or at a named level the verifier hashed a pair different from
the tree's and keccak maps the two 64-byte node preimages to the same word. -/
def Properties.LiveLeafOpeningPinsLeafOrCollision : Prop :=
  ∀ (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256),
    j < 4 →
    walkPure (node keccak) sibs 0 TREE_DEPTH j x = compute keccak a b c d →
      x = (liveLeaves a b c d).getD j 0 ∨ OpeningCollision keccak a b c d sibs j x

/-- **A DEPTH-3 PATH INTO THE RESERVED HALF OPENS `0`, OR LOCATES A COLLISION.** Under the
documented reserved value, a 3-sibling path at index `4 ≤ j < 8` that returns `compute a b c d`
has claimed leaf `x = 0`, or an `OpeningCollision`. -/
def Properties.ReservedLeafOpeningPinsZeroOrCollision : Prop :=
  ∀ (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256),
    ReservedSubtreeDocumented keccak → 4 ≤ j → j < 2 ^ TREE_DEPTH →
    walkPure (node keccak) sibs 0 TREE_DEPTH j x = compute keccak a b c d →
      x = 0 ∨ OpeningCollision keccak a b c d sibs j x

/-- **EVERY DEPTH-3 OPENING, ONE STATEMENT.** Under the documented reserved value, a 3-sibling path
at any index `j < 8` (`Merkle.sol:137-139`) that returns `compute a b c d` has claimed leaf
`[a, b, c, d].getD j 0` (the live leaf, or the padding `0`), or an `OpeningCollision`. -/
def Properties.OpeningPinsLeafOrCollision : Prop :=
  ∀ (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256),
    ReservedSubtreeDocumented keccak → j < 2 ^ TREE_DEPTH →
    walkPure (node keccak) sibs 0 TREE_DEPTH j x = compute keccak a b c d →
      x = (liveLeaves a b c d).getD j 0 ∨ OpeningCollision keccak a b c d sibs j x

/-- **THE ATOMIC-INTEROP IMT-ROOT HOP OPENS LEAF 2 OR 3, OR LOCATES A COLLISION.** No hash premise.
With `logLeafProofLen = TREE_DEPTH` and mask `IMT_BEGIN_ROOT_LEAF_INDEX` (resp.
`IMT_END_ROOT_LEAF_INDEX`), a first hop that reaches `compute a b c d` has claimed IMT root `x = c`
(resp. `x = d`), or an `OpeningCollision`. -/
def Properties.ImtRootHopPinsLeafOrCollision : Prop :=
  ∀ (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (len : ℕ) (x : UInt256),
    (ImtRootHopAccepted keccak a b c d sibs len IMT_BEGIN_ROOT_LEAF_INDEX x →
        x = c ∨ OpeningCollision keccak a b c d sibs IMT_BEGIN_ROOT_LEAF_INDEX x)
      ∧ (ImtRootHopAccepted keccak a b c d sibs len IMT_END_ROOT_LEAF_INDEX x →
        x = d ∨ OpeningCollision keccak a b c d sibs IMT_END_ROOT_LEAF_INDEX x)

/-- **THE DEPTH PIN IS LOAD-BEARING.** Under the documented reserved value, for either fixed mask
(`2` or `3`), a path of length 2 with siblings `node 0 0` then `liveSubtreeNode` is in bounds and
reaches `compute a b c d` for the claimed root `x = node 0 0` (the reserved half's level-1 node),
for every `a b c d`. Only `ImtRootHopAccepted.depthPinned` (`AtomicInteropProof.sol:160-162`)
rejects it. -/
def Properties.ImtRootHopDepthPinNeeded : Prop :=
  ∀ (keccak : Keccak) (a b c d : UInt256), ReservedSubtreeDocumented keccak →
    ∀ m, (m = IMT_BEGIN_ROOT_LEAF_INDEX ∨ m = IMT_END_ROOT_LEAF_INDEX) →
      m < 2 ^ 2
        ∧ walkPure (node keccak)
            (fun l => if l = 0 then node keccak 0 0 else liveSubtreeNode keccak a b c d) 0 2 m
            (node keccak 0 0) = compute keccak a b c d

/-! ## Non-triviality -/

/-- **THE HONEST PROOF IS ACCEPTED.** For every keccak and every index `j < 4` (and every `j < 8`
under the documented reserved value), the tree's own siblings `openingSibs` with the leaf
`[a, b, c, d].getD j 0` reach `compute a b c d`. So the opening properties' premises hold on
honest proofs. -/
def Properties.HonestOpeningAccepted : Prop :=
  ∀ (keccak : Keccak) (a b c d : UInt256) (j : ℕ),
    (j < 4 ∨ (ReservedSubtreeDocumented keccak ∧ j < 2 ^ TREE_DEPTH)) →
      walkPure (node keccak) (openingSibs keccak a b c d j) 0 TREE_DEPTH j
        ((liveLeaves a b c d).getD j 0) = compute keccak a b c d

/-- **NO COLLISION IS LOCATED ON THE HONEST PROOF.** Under the same conditions, `OpeningCollision`
is false for the tree's own siblings and leaf: the verifier hashes exactly the tree's pairs. -/
def Properties.HonestOpeningNoCollision : Prop :=
  ∀ (keccak : Keccak) (a b c d : UInt256) (j : ℕ),
    (j < 4 ∨ (ReservedSubtreeDocumented keccak ∧ j < 2 ^ TREE_DEPTH)) →
      ¬ OpeningCollision keccak a b c d (openingSibs keccak a b c d j) j
        ((liveLeaves a b c d).getD j 0)

/-- **THE COLLISION DISJUNCT FIRES.** On the constant keccak `fun _ => 0`, a depth-3 path at index
0 with claimed leaf `1 ≠ a = 0` reaches `compute`, and the collision is located. -/
def Properties.OpeningCollisionFires : Prop :=
  ∃ (keccak : Keccak) (a b c d : UInt256) (sibs : ℕ → UInt256) (j : ℕ) (x : UInt256),
    j < 4 ∧ walkPure (node keccak) sibs 0 TREE_DEPTH j x = compute keccak a b c d
      ∧ x ≠ (liveLeaves a b c d).getD j 0 ∧ OpeningCollision keccak a b c d sibs j x

/-! ## (e) Leaf 1 of the genesis root -/

/-- **LEAF 1 OF THE GENESIS ROOT OPENS ONLY TO `0`.** No hash premise. A depth-3 path at
`MULTICHAIN_ROOT_LEAF_INDEX` that reaches `genesisChainBatchRoot` has claimed leaf `0`, or an
`OpeningCollision` against the genesis tree `[0, 0, EMPTY_IMT_ROOT, EMPTY_IMT_ROOT]`. -/
def Properties.GenesisLeafOneOpensZeroOrCollision : Prop :=
  ∀ (keccak : Keccak) (sibs : ℕ → UInt256) (x : UInt256),
    walkPure (node keccak) sibs 0 TREE_DEPTH MULTICHAIN_ROOT_LEAF_INDEX x
        = genesisChainBatchRoot keccak →
      x = 0 ∨ OpeningCollision keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT sibs
        MULTICHAIN_ROOT_LEAF_INDEX x

/-- **LEAF 1 OF THE GENESIS ROOT IS NOT A `MessageRoot`'S INITIAL AGGREGATED ROOT.** No hash
premise. A depth-3 opening of leaf 1 of the genesis root at the aggregated root a `MessageRoot`
reports right after `_initialize` (`initialAggregatedRoot`, keccak of a 96-byte chain-id leaf
preimage) needs keccak to map that 96-byte string to `0`, or an `OpeningCollision`. -/
def Properties.GenesisLeafOneNotInitialAggregatedRoot : Prop :=
  ∀ (keccak : Keccak) (padC chainId : UInt256) (sibs : ℕ → UInt256),
    walkPure (node keccak) sibs 0 TREE_DEPTH MULTICHAIN_ROOT_LEAF_INDEX
        (initialAggregatedRoot keccak padC chainId) = genesisChainBatchRoot keccak →
      keccak (chainIdLeafPre padC 0 chainId) = 0
        ∨ OpeningCollision keccak 0 0 EMPTY_IMT_ROOT EMPTY_IMT_ROOT sibs MULTICHAIN_ROOT_LEAF_INDEX
            (initialAggregatedRoot keccak padC chainId)

/-- **WITNESS: ON A CONCRETE KECCAK, NO PATH OPENS IT.** There is a keccak under which the initial
aggregated root is nonzero and no sibling stream makes a depth-3 path at leaf 1 reach the genesis
root with that claimed leaf. -/
def Properties.GenesisLeafOneRejectsInitialAggregatedRootWitness : Prop :=
  ∃ (keccak : Keccak) (padC chainId : UInt256),
    keccak (chainIdLeafPre padC 0 chainId) ≠ 0
      ∧ ∀ sibs : ℕ → UInt256,
          walkPure (node keccak) sibs 0 TREE_DEPTH MULTICHAIN_ROOT_LEAF_INDEX
            (initialAggregatedRoot keccak padC chainId) ≠ genesisChainBatchRoot keccak

/-- **WITNESS FOR THE RESERVED HALF.** Some keccak meets the documented reserved value, and under
it the honest proof at every index `j < 8`, reserved half included, is accepted and locates no
collision. So the premises of `ReservedLeafOpeningPinsZeroOrCollision` and
`OpeningPinsLeafOrCollision` hold together, for every `a b c d`. -/
def Properties.ReservedOpeningWitness : Prop :=
  ∃ keccak : Keccak, ReservedSubtreeDocumented keccak
    ∧ ∀ (a b c d : UInt256) (j : ℕ), j < 2 ^ TREE_DEPTH →
        walkPure (node keccak) (openingSibs keccak a b c d j) 0 TREE_DEPTH j
            ((liveLeaves a b c d).getD j 0) = compute keccak a b c d
          ∧ ¬ OpeningCollision keccak a b c d (openingSibs keccak a b c d j) j
              ((liveLeaves a b c d).getD j 0)

/-- **WITNESS FOR THE IMT-ROOT HOP.** For every keccak and every `a b c d`, the honest proofs of
leaves 2 and 3 meet `ImtRootHopAccepted` with `len = TREE_DEPTH` and claimed roots `c` and `d`. -/
def Properties.ImtRootHopWitness : Prop :=
  ∀ (keccak : Keccak) (a b c d : UInt256),
    ImtRootHopAccepted keccak a b c d (openingSibs keccak a b c d IMT_BEGIN_ROOT_LEAF_INDEX)
        TREE_DEPTH IMT_BEGIN_ROOT_LEAF_INDEX c
      ∧ ImtRootHopAccepted keccak a b c d (openingSibs keccak a b c d IMT_END_ROOT_LEAF_INDEX)
        TREE_DEPTH IMT_END_ROOT_LEAF_INDEX d

end Contracts.ChainBatchRootTree
