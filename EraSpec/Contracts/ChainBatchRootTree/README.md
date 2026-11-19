# ChainBatchRootTree

## Headline guarantees

All about `l1-contracts/contracts/common/libraries/ChainBatchRootTree.sol` and its consumers at
era-contracts `draft/v0.35.0` head `b17415d20`. keccak is an arbitrary function; the only premise
on it is the documented value of a named constant where stated.

- `Contracts.ChainBatchRootTree.Properties.OpeningPinsLeafOrCollision`: given the documented value
  of `RESERVED_SUBTREE_NODE`, a 3-sibling path at an index below 8 that returns
  `compute(a, b, c, d)` claims the leaf at that index (`0` for the reserved half), or a keccak
  collision on two named 64-byte node preimages is located.
- `Contracts.ChainBatchRootTree.Properties.ImtRootHopPinsLeafOrCollision`: with no premise, the
  atomic-interop IMT-root hop (depth pinned to 3, mask 2 or 3) that reaches `compute(a, b, c, d)`
  claims `c` (resp. `d`), or a collision is located.
- `Contracts.ChainBatchRootTree.Properties.ImtBatchRootLogProofConfinedOrKeccakEvent`: given the
  documented reserved value and a multichain subtree with no cut and no 64- or 88-byte leaf
  preimage, a log proof of any length and mask that returns a ZKsync OS batch root passes through
  leaf 0 at height 3, or keccak collides the walk's 88- or 64-byte input with a named string of
  another length, or maps it to `0` or a multichain constant.
- `Contracts.ChainBatchRootTree.Properties.GenesisRootStable`: on every successful run from fresh
  storage, once the chain exists both the diamond's `l2LogsRootHashes[0]` and the message root's
  `chainBatchRoots[c][0]` hold the nonzero genesis root, and the chain is registered.
- `Contracts.ChainBatchRootTree.Properties.SeedAtMostOnce` and
  `Contracts.ChainBatchRootTree.Properties.NoSeedAfterRealBatch`: on every successful run from any
  storage, `seedGenesisRoot` succeeds at most once and never after a batch root was recorded
  (message-root calls from any caller at any time). `MessageRootLink` shows the canonical
  `../MessageRoot/` model's calls move a chain's slice exactly by these `seedExec` calls.

## Topics

Source: `l1-contracts/contracts/common/libraries/ChainBatchRootTree.sol` at era-contracts
`draft/v0.35.0` head `b17415d20` (the library's code is identical at `d9f678900`, `c67894b9` and main
`70096e2ea`; only comments differ), with the consumers that read it: `DiamondInit.sol:138`,
`MessageRootBase.seedGenesisRoot` (`:296-314`), `L1Bridgehub.createNewChain` (`:108-139`),
`AtomicInteropProof._authenticateRoot` (`:155-189`) and `MessageVerification._proveL2LogInclusion`
(`:85-108`). Backlog item W-MER-3.

The chain batch root of a ZKsync OS batch is a fixed height-3 keccak Merkle tree over four live
leaves (logs root, multichain root, IMT root at batch begin and at batch end) and four zero leaves,
with no leaf-hashing step. Every hash is an arbitrary `keccak : List UInt8 → UInt256`; nothing is
assumed about it except the two documented constants where named (`ASSUMPTIONS.md`
`CRYPTO-CBR-DOCUMENTED`). Model boundaries: `MODEL-CBR-ROOT`, `MODEL-CBR-SEED`.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Layout | [Specs/Layout.lean](Specs/Layout.lean) | [Properties/Layout.lean](Properties/Layout.lean) | [Proofs/Layout.lean](Proofs/Layout.lean) |
| GenesisSeed | [Specs/GenesisSeed.lean](Specs/GenesisSeed.lean) | [Properties/GenesisSeed.lean](Properties/GenesisSeed.lean) | [Proofs/GenesisSeed.lean](Proofs/GenesisSeed.lean) |
| LogConfinement | [Specs/LogConfinement.lean](Specs/LogConfinement.lean) | [Properties/LogConfinement.lean](Properties/LogConfinement.lean) | [Proofs/LogConfinement.lean](Proofs/LogConfinement.lean) |
| MessageRootLink | [Specs/MessageRootLink.lean](Specs/MessageRootLink.lean) | [Properties/MessageRootLink.lean](Properties/MessageRootLink.lean) | [Proofs/MessageRootLink.lean](Proofs/MessageRootLink.lean) |

**Layout.** Under the documented value of `RESERVED_SUBTREE_NODE`, `compute(a, b, c, d)` is
`rootOf (node keccak) 0 [a, b, c, d] 3`, the `FullMerkle` fold at height 3 with padding `0`
(`ComputeIsRootOfHeightThree`; the premise is satisfiable and load-bearing,
`ComputeRootNeedsDocumentedValue`). A 3-sibling path at index `j` that returns `compute(a, b, c, d)`
has claimed leaf `[a, b, c, d][j]` for `j < 4` with no premise, and `0` for `4 ≤ j < 8` under the
documented value, or exhibits an `OpeningCollision`: keccak equal on two different named 64-byte
node preimages, the pair the verifier hashed and the tree's pair at the same level
(`LiveLeafOpeningPinsLeafOrCollision`, `ReservedLeafOpeningPinsZeroOrCollision`,
`OpeningPinsLeafOrCollision`). So the atomic-interop IMT-root hop, with its depth pinned to
`TREE_DEPTH` and mask 2 or 3, opens exactly leaf 2 or leaf 3 or locates a collision
(`ImtRootHopPinsLeafOrCollision`). The depth pin is load-bearing: a length-2 path with the same
mask is accepted for the claimed root `node 0 0` (`ImtRootHopDepthPinNeeded`). The honest proof is
accepted and locates no collision (`HonestOpeningAccepted`, `HonestOpeningNoCollision`,
`ReservedOpeningWitness`, `ImtRootHopWitness`), and on a degenerate keccak the collision disjunct
fires (`OpeningCollisionFires`). Leaf 1 of the genesis root opens only to `0`
(`GenesisLeafOneOpensZeroOrCollision`); opening it at a `MessageRoot`'s aggregated root right after
`_initialize` needs keccak of that 96-byte chain-id leaf preimage to be `0`, or a collision
(`GenesisLeafOneNotInitialAggregatedRoot`), and on a concrete keccak no path does
(`GenesisLeafOneRejectsInitialAggregatedRootWitness`). Source context, not modelled here: no
contract at `b17415d20` reads `MULTICHAIN_ROOT_LEAF_INDEX`; batch 0 is rejected on the settlement
layer's final-node path (`BatchZeroNotAllowed`, `MessageRootBase.sol:366`); on L2 consumers a proof
for batch 0 that is not a final-node proof goes through the chain tree, which holds the seeded leaf
(`L2MessageVerification.sol:18-56`), and that is how atomic interop reaches the genesis leaves 2
and 3. A final-node proof on L2 compares its root directly with `interopRoots(chainId, n)`
(`L2MessageVerification.sol:33-38`); atomic interop rejects final-node proofs
(`ProofMissingSettlementLayerBatch`, `AtomicInteropProof.sol:177-179`).

**GenesisSeed.** A successful `createNewChain` leaves `chainBatchRoots[c][0]` and the diamond's
`l2LogsRootHashes[0]` both equal to `compute(0, 0, EMPTY_IMT_ROOT, EMPTY_IMT_ROOT)` with
`currentChainBatchNumber[c] = 0` (`CreateNewChainSeedsGenesisRoot`); from uncreated, unregistered
storage it succeeds exactly when that root is nonzero (`CreateNewChainSucceedsIffGenesisNonzero`;
off chain the root is `0x1d57…7885`). On every run from fresh storage the two slots stay equal to the
genesis root once the chain exists (`GenesisRootStable`). On every successful run from any storage,
`seedGenesisRoot` succeeds at most once (`SeedAtMostOnce`) and never after a batch root was
recorded (`NoSeedAfterRealBatch`); the next recorded batch after creation is batch 1
(`FirstRealBatchIsOne`). Under the documented value of `EMPTY_IMT_ROOT`, the IMT-root hop at leaf 2
or 3 of the genesis root opens the root of the freshly set-up commitment tree, the batch-0 tree
`Contracts.InteropOperational.BatchLog.genesis` takes, or locates a collision
(`GenesisImtLeavesOpenSetupRoot`, premises met by `GenesisImtLeavesWitness`).
`GenesisSeedRunWitness` runs creation and one batch on a concrete keccak. The model lets every
message-root call come from any caller at any time, so these hold for the deployed callers too
(`MODEL-CBR-SEED`).

**MessageRootLink.** `GenesisSeed` models one chain's slice of `MessageRootBase` with its own
transition `seedExec`; the canonical model of the contract is `../MessageRoot/` topic `Model`. On
storage satisfying that model's invariant, every successful call leaves the slice of a chain other
than `block.chainid` unchanged or is one `seedExec` call on it (`MessageRootCallIsSeedCall`); right
after `initialize` such a slice is fresh (`InitializedSliceIsFresh`); so every reachable slice is a
`seedExec` run from the fresh slice (`ReachableSliceIsSeedRun`).

**LogConfinement.** `MessageVerification._proveL2LogInclusion` does not check the log proof's
length and uses the log index as the mask; its comment justifies this by the 88-byte log preimage
differing from 64-byte node preimages and by the logs root being on the left of the tree. Here the
honest tree below a batch root is a `PreTree` (64-byte nodes, leaves with named keccak inputs,
constants, and a `cut` for the logs tree at leaf 0), and `land` follows a walk down it while the
walk's pairs equal the tree's. For any tree, an accepted walk reaches a cut, or its keccak input
where it leaves the tree is the landing node's keccak input, or a `LandingBreak` is located there:
a keccak collision on two named strings, or the walk's keccak input hashing to a constant that has
no modelled preimage (`AcceptedWalkCutMatchOrBreak`). For the chain batch root, with leaves 1-3 and
the reserved half free of cuts and of 64- and 88-byte leaf preimages, a log proof of any length and
mask passes through leaf 0 at height 3 (top three mask bits zero, honest top siblings, value `a`
after `k - 3` steps), or a `LandingBreak` is located (`LogProofPassesLeafZeroOrBreak`); the two
outcomes exclude each other (`PassesLeafZeroExcludesBreak`). With the two IMT snapshots as
`imtPreTree`s (which evaluate to the existing `Contracts.InteropCommitmentTree.root` model,
`ImtPreTreeRoot`) and the reserved zero half (`ZeroPreTreeReserved`), the break is a keccak
collision between an 88- or 64-byte walk input and a different string 64, 96 or 34 bytes long or a
leaf of the multichain subtree, or keccak of the walk input equal to `0` or a constant of the
multichain subtree (`ImtBatchRootLogProofConfinedOrKeccakEvent`). Wrong path lengths are among these
cases: a walk that ends at an interior node pairs the 88-byte log with a 64-byte node preimage, and
one that runs past a leaf pairs a 64-byte walk node with a 96- or 34-byte IMT input, or hashes it to
a zero leaf's value `0`. `HonestLogProofPassesLeafZero` and `LogProofPassesLeafZeroWitness` give an
honest instance meeting every premise; `ImtLandingCollisionFires` gives a concrete keccak under which
a log hash equals the `{0,0,0}` IMT leaf hash and a proof through leaf 2 is accepted, with that
88-versus-96-byte collision located.

Not modelled here: the outer proof hops (batch leaf into the chain tree, chain-id leaf into the
shared root) and the L1 final-node comparison, which these results take by their conclusion; that
the recorded root is `compute` of the batch's actual subtrees (the bootloader's
`compute_chain_batch_root` and the batch proof); the logs tree below leaf 0; and the structure of the
multichain leaf, which `b17415d20` does not specify ("empty for now"), so it is a premise on `T1`.
At main `70096e2ea` the genesis seeding runs only for ZKsync OS chains (`DiamondInit` behind
`IS_ZKSYNC_OS`, `seedGenesisRoot` returns early otherwise); the model is the `b17415d20` code.
