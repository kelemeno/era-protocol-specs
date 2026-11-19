# MessageVerification

## Headline guarantees

All about `l1-contracts/contracts/common/MessageVerification.sol` on L1 (final-node branch) at
era-contracts `draft/v0.35.0` head `b17415d20`. keccak is an arbitrary function.

- `Contracts.MessageVerification.Properties.FailureProofForSucceededTxIsKeccakBreak`: if the
  recorded root is the chain batch root over the batch's logs tree (L2-side premise), every
  bootloader log of the batch is a genuine status log with its transaction's real status (L2-side
  premise), the logs fit their Solidity types and the transaction number is below `2^16`, then an
  accepted Failure proof for a transaction that succeeded gives a keccak collision between the
  batch's log at the proof's index and the Failure log, or a keccak collision on named byte strings
  of the walk, except when the walk reaches another leaf of the chain batch root (`otherLeaf`).
- `Contracts.MessageVerification.Properties.HeldLogIsProvable`: under the same root premise, every
  log the batch holds at an index below `2^H`, with `H + 3 < 256`, a nonzero root and a leaf hash
  other than the default leaf hash, has an honest proof that the check accepts.
- `Contracts.MessageVerification.Properties.StatusProofAtMessageRoot`: for a batch `n > 0` at or
  above `v31UpgradeChainBatchNumber[c]`, or with a recorded root, the status check against
  `R = chainBatchRoots[c][n]` is exactly the default-leaf and bounds checks followed by the
  canonical `../MessageRoot/` model's final-node verdict.
- `Contracts.MessageVerification.Properties.ChainBatchRootIsCompute`: given the documented value
  of `RESERVED_SUBTREE_NODE`, this folder's chain batch root is `ChainBatchRootTree.compute`.

## Topics

Source: `l1-contracts/contracts/common/MessageVerification.sol` at era-contracts
`draft/v0.35.0` head `b17415d20` (`proveL1ToL2TransactionStatusShared`, `_proveL2LogInclusion`,
`proveL2LogInclusionShared`), with the L1 leaf check it reaches
(`core/message-root/MessageRootBase.sol:328-373`, `common/libraries/MessageHashing.sol:152-236`,
`common/libraries/Merkle.sol:53-70, 125-140`) and the ZKsync OS chain batch root
(`common/libraries/ChainBatchRootTree.sol`). At `main` `70096e2ea` these functions are unchanged
in substance (`MessageRootBase.sol` line numbers differ); main still supports EraVM chains, whose
batch roots do not have the `ChainBatchRootTree` shape, and the composition here covers ZKsync OS
batch roots only.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| StatusProof | [Specs/StatusProof.lean](Specs/StatusProof.lean) | [Properties/StatusProof.lean](Properties/StatusProof.lean) | [Proofs/StatusProof.lean](Proofs/StatusProof.lean) |
| StatusProofKeccak | [Specs/StatusProofKeccak.lean](Specs/StatusProofKeccak.lean) | [Properties/StatusProofKeccak.lean](Properties/StatusProofKeccak.lean) | [Proofs/StatusProofKeccak.lean](Proofs/StatusProofKeccak.lean) |
| Refinement | [Specs/Refinement.lean](Specs/Refinement.lean) | [Properties/Refinement.lean](Properties/Refinement.lean) | [Proofs/Refinement.lean](Proofs/Refinement.lean) |

`L1Nullifier.bridgeRecoverFailedTransfer` refunds a deposit after
`proveL1ToL2TransactionStatusShared(…, TxStatus.Failure)` returns `true`
(`bridge/L1Nullifier.sol:180-248`). `StatusProof` models that call on L1, on the final-node
branch: the default-leaf check, the path-length and index bounds, the walk
(`Merkle.calculateRootMemory`) and the comparison with a nonzero stored batch root
(`LogProofAccepted`, `StatusProofAccepted`).

- Over an abstract node hash: `ChainBatchRootTree.compute` is the height-3 fold
  (`ChainBatchRootIsFold`), and a walk of any length and index accepted against a chain batch root
  opens the logs tree's entry at its index with the honest shape (`k = H + 3`, `j < 2^H`), or is a
  located `BatchWalkBreak`: a `PathCollision` or `HeightBreak` of the logs tree or of the height-3
  tree, or `otherLeaf`, a walk reaching the multichain root, an interop-tree root or a reserved
  zero leaf instead of the logs root (`BatchWalkOpensLogsEntryOrBreak`). The honest proof of every
  index below `2^H` is accepted with no break (`HonestBatchWalkNoBreak`).
- Over keccak, with two L2-side premises (`PROTO-L2-LOGS` in `ASSUMPTIONS.md`): the recorded root
  is the chain batch root over the batch's logs tree padded with `keccak(new bytes(88))`
  (`BatchRootCommitsLogs`), and every bootloader log of the batch is a genuine status log with
  its transaction's real status (`BootloaderLogsAreStatusLogs`; the L1 side cannot check this,
  since `proveL2LogInclusionShared` accepts a proof for any log the tree holds).
  - `LogProofOfAbsentLogLocatesBreak`: a log proof of a well-formed log the batch does not hold
    gives a keccak collision between the batch's log at the proof's index and the claimed log
    (two named 88-byte preimages), or a `BatchWalkBreak`. The default-leaf check
    (`MessageHashing.sol:163-167`) rules out padded positions.
  - `StatusProofOfUnrealStatusLocatesBreak` and the headline
    `FailureProofForSucceededTxLocatesBreak`: the same for a status proof whose status is not the
    transaction's real status, in particular a Failure proof for a transaction that succeeded.
  - `StatusProofWitness` meets every premise of the three (a stand-in keccak under which all
    88-byte logs collide), at index 1 of a two-log batch.
  - Completeness: every log the batch holds, whatever its sender, has an honest proof that passes
    the modelled check (`HeldLogIsProvable`, witness `HeldLogIsProvableWitness`); in particular a
    status the batch recorded is provable.
  - Countermodels: without `BootloaderLogsAreStatusLogs`, a Failure proof for a succeeded
    transaction is accepted with no collision and no break, for every keccak under which the root
    is nonzero and the Failure leaf is not the default leaf hash (`BootloaderPremiseLoadBearing`);
    with the default-leaf check removed, the all-zero log passes every remaining check at a padded
    position with no collision and no break (`DefaultLeafCheckLoadBearing`).
- `StatusProofKeccak` turns the breaks into keccak statements: a `PathCollision` of
  `efficientHash keccak` is exactly a collision on two named 64-byte node preimages
  (`PathCollisionIffKeccakCollision`), and for an 88-byte claimed preimage `BatchWalkBreak` is
  exactly `StatusWalkKeccakBreak` (`BatchWalkBreakIffKeccakBreak`), where every wrong-length case
  is a collision between an 88-byte and a 64-byte string: the argument of the comment at
  `MessageVerification.sol:94-96` for leaving the proof length unchecked. Headline:
  `FailureProofForSucceededTxIsKeccakBreak`, a named keccak collision in every case except
  `otherLeaf`. `HonestStatusWalkNoKeccakBreak` shows the predicate is not a tautology;
  `ShortStatusProofIsCrossLengthCollision` is an accepted zero-length Failure proof under a
  stand-in keccak, located as a cross-length collision.

`Refinement` links this folder to the canonical models: its `chainBatchRoot` is
`ChainBatchRootTree.compute` under the documented reserved value (`ChainBatchRootIsCompute`), and
its abstract stored root `R` is `MessageRoot`'s `chainBatchRoots[c][n]` with the final-node verdict
of `../MessageRoot/` topic `Model` (`StatusProofAtMessageRoot`).

Not covered: the multi-hop branch (`MessageRootBase.sol:349-360`, `L1MessageRoot.sol:96-120`), on
which the walk's result is authenticated through a settlement layer that
`L1ChainAssetHandler.isValidSettlementLayer` accepts for the batch (chain migrations are disabled in
this release, `common/Config.sol:320`); reading the stored root from `chainBatchRoots`; the
`otherLeaf` case below keccak, which needs the multichain and interop trees (their hashes have fixed
preimage lengths at `b17415d20`: IMT leaves 96 bytes, `common/libraries/IndexedMerkleTree.sol:125`;
`chainIdLeafHash` 96 and `batchLeafHash` 128 bytes, `MessageHashing.sol:76-89`; nodes 64, so the
case may reduce to cross-length or preimage-of-zero statements as for the logs tree; that is not
done here); the ZKsync OS side of `PROTO-L2-LOGS`. The hex constants
`L2_L1_LOGS_TREE_DEFAULT_LEAF_HASH` and `RESERVED_SUBTREE_NODE` are modelled by their documented
keccak definitions.
