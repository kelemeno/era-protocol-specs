# MessageRoot

Source: `contracts/core/message-root/MessageRootBase.sol` in the pinned era-contracts tree
(`c67894b9`), with `L1MessageRoot.sol` for the v31 batch-number writer and `MessageHashing.sol` for
the two leaf hashes. Only the state the timeout protocol reads is modelled: the registry
(`chainCount`, `chainIndex`, `chainIndexToId`), `currentChainBatchNumber`, `chainBatchRoots`,
`chainBatchRootTimestamp`, each chain tree as its list of pushed leaves, the shared tree as its leaf
list, and `historicalRoots`, plus the block number and timestamp.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Aggregation | [Specs/Aggregation.lean](Specs/Aggregation.lean) | [Properties/Aggregation.lean](Properties/Aggregation.lean) | [Proofs/Aggregation.lean](Proofs/Aggregation.lean) |

Namespace `Contracts.MessageRoot.Aggregation`. Statements are
`Contracts.MessageRoot.Aggregation.Properties.*`; each certificate has the same name without the
`Properties` segment.

Runs start at `_initialize` and interleave `addNewChain`, `seedGenesisRoot`, the record-only
`addChainBatchRoot`, `addChainBatchRootV32`, `setMigratingChainBatchNumber` and new blocks, under
non-decreasing or strictly increasing block timestamps. Hashes are abstract, with no premise.
Caller checks and arithmetic overflow are not modelled, so the run-universal results cover more
runs than the deployed contract allows (`MODEL-MESSAGE-ROOT` in `ASSUMPTIONS.md`).

- **The registry and the trees.** One chain per shared-tree position, whose leaf is
  `chainIdLeafHash` of the chain's current tree root (`ChainIndexInjective`,
  `ChainIndexIsAPosition`, `SharedLeafIsChainIdLeaf`, `FreshChainLeafIsZeroRoot`). A chain tree
  holds recorded batches in strictly increasing batch order with their recorded timestamps
  (`ChainLeavesArePushedBatches`); the source's invariant at `MessageRootBase.sol:100` holds
  (`UnrecordedAboveCurrent`); recorded batch roots are never rewritten (`BatchRootWriteOnce`).
- **The clock.** Leaves are pushed in timestamp order, so the clock indexed by pushed position is
  monotone (`LeavesOrdered`, `LeafTimeMonotone`, `LeafTimeMonotoneAsWord`).
- **Historical roots.** `historicalRoots[b]` counts exactly the leaves pushed in blocks up to `b`
  (`HistoricalRootIsSnapshot`, `LastWriteInBlockWins`). Every leaf that settled strictly before a
  root was written is counted by it, for the root as it stood at any point of the run and every
  later state (`AggregatesStrictFromMessageRoot`, `PushedAfterLastIsLate`); under strictly
  increasing timestamps the non-strict form holds for the roots as they stand
  (`AggregatesFromMessageRootStrictTs`). Equal timestamps across blocks, or a mid-block read, break
  the non-strict form (`EqualTimestampEscapesRoot`, `MidBlockReadEscapesRoot`).
- **Positions, not batch numbers.** A record-only batch is never pushed later
  (`RecordOnlyBatchNotCitable`); indexed by batch number with `chainBatchRootTimestamp` as the
  clock, `LastBatchInRoot.OutsideRootLate` fails (`RecordOnlyGap`, which takes the record-only step
  after pushes, as `PROTO-CONTIGUOUS-PUSH` describes); a chain registered at a nonzero start pushes
  batch numbers that are not its positions (`OnboardedChainPositionsAreNotBatchNumbers`).

Witnesses: `AggregationWitness`, `AggregationRegistryWitness`, `RecordOnlyBatchNotCitableWitness`;
the Properties module's table says which premises each meets.

How these roots reach a destination and what the timeout protocol gets from them is
`../../Protocol/InteropAtomicity/`, topic `SettlementRoots`. At `draft/v0.35.0` `b17415d20` the
modelled functions are unchanged apart from line numbers and the details listed in the Specs
module ("Later heads"); the model was not re-pinned.

Related model: `../ChainBatchRootTree/` topic `GenesisSeed` (`b17415d20`) models the per-chain
numbering slice of `MessageRootBase` (`chainRegistered`, `currentChainBatchNumber`,
`chainBatchRoots`); its `GenesisRootStable` and `NoSeedAfterRealBatch` sit next to this topic's
`BatchRootWriteOnce` and `UnrecordedAboveCurrent`.
