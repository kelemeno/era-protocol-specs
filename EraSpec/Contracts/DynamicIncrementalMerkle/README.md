# DynamicIncrementalMerkle

Source: `contracts/common/libraries/DynamicIncrementalMerkle.sol` and
`DynamicIncrementalMerkleMemory.sol` in the pinned era-contracts tree (`c67894b9`). Both files
are unchanged on `main` (`70096e2`). On `draft/v0.35.0` (`b17415d20`) `reset` returns `setup`'s
value explicitly, and the memory `push` is declared over four lines and names its index
`leafIndex`, as `pushLazy` does; the specification headers record the line shifts.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| ChainTreeBacking | [Specs/ChainTreeBacking.lean](Specs/ChainTreeBacking.lean) | [Properties/ChainTreeBacking.lean](Properties/ChainTreeBacking.lean) | [Proofs/ChainTreeBacking.lean](Proofs/ChainTreeBacking.lean) |
| MemoryLazy | [Specs/MemoryLazy.lean](Specs/MemoryLazy.lean) | [Properties/MemoryLazy.lean](Properties/MemoryLazy.lean) | [Proofs/MemoryLazy.lean](Proofs/MemoryLazy.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |

The `MessageRoot`'s chain trees and the priority tree are storage trees of this library. The
timeout path's last-batch check (`AtomicInteropProof._verifyLastBatchInRoot`) runs against
roots built from the chain trees, which `Contracts.Timeout.RootBacking` models as a fold at a
given height.

`Model` transcribes the storage library (`setup`, `reset`, `clear`, `push`, `extendUntilEnd`,
`root`, `height`) statement by statement as pure functions (a revert is `none`). For every
node hash and zero value:
- `setup` represents the empty tree, whose `root()` is `bytes32(0)`, not the fold
  (`SetupRepresentsEmpty`, `DimEmptyRootIsZero`, `EmptyRootIsNotTheFold`,
  `ChainTreeEmptyRootIsNotTheFold`).
- `push` returns the fold over the new leaves and grows the height exactly when the tree is
  full (`PushComputesRoot`); before `setup` and after `clear` it reverts
  (`PushBeforeSetupReverts`, `PushAfterClearReverts`).
- Every run sits at the minimal height `⌈log₂ n⌉`, and `root()` is the fold there
  (`ReachableHeightMinimal`, `DimHeightSucc`, `SidesInvariant`, `RootIsFold`, `RunRootIsFold`,
  `PushReturnsStoredRoot`, `PushAllSucceeds`).
- The fork's `updatedSides` write policy returns OpenZeppelin's index and root
  (`OzEquivalent`) but not its storage (`OzSidesDiffer`); a mutation of the guard without
  `isLeft` changes the root (`MisplacedGuardBreaksRoot`).
- `extendUntilEnd` leaves the fold at the target depth, also for the empty tree, and a later
  push returns the fold (`ExtendUntilEndRoot`, `ExtendUntilEndAgain`,
  `PushAfterExtendComputesRoot`, `RunExtendThenPush`); `reset` is `setup` on fresh storage
  (`ResetIsSetup`).
- Witnesses with the storage written out: `OnePushWitness`, `TwoPushWitness`,
  `ThreePushWitness`, `FourthPushWitness`, `ExtendEmptyWitness`, `ExtendThenPushWitness`.

`MemoryLazy` transcribes the memory library except `extendUntilEnd` and `index`, which no
contract calls. Eager and lazy pushes keep the invariant, and `root()` recomputes the fold when
the lazy flag is set (`MemSetupRepresentsEmpty`, `MemPushComputesRoot`, `MemRootIsFold`,
`LazyRootRecalculated`, `LazyFlagMeansNotFull`); over the same leaves the memory tree reports
what the storage tree reports (`MemoryMatchesStorage`). The empty chain tree
`L2MessageRoot.getEmptyMultichainBatchRoot` builds has root `0`, as a storage chain tree has
after `_addNewChain` (`EmptyChainTreeRootsAgree`). Witnesses: `LazyRunWitness`, `MemPushWitness`.

`ChainTreeBacking` builds a `Timeout.RootBacking` from DIM runs: its height is the library's
minimal height and the fold it authenticates against is the stored `root()`
(`ChainTreeBackingIsStored`); the honest path of each chain's last leaf is accepted
(`DimLastBatchAccepted`, `DimLastBatchAcceptedThreeLeaves`, `ChainTreesExist`); and
`Timeout.LastBatchProofIdentifiesLastBatchPinned` instantiates to
`DimLastBatchProofIdentifiesLastBatchPinned`, which keeps `LastBatchAccepted`'s fixed walk length
and occupied index. With the length and the mask free, as the deployed check leaves them, a
submission accepted against the `root()` of DIM storage has the DIM height and opens the last
pushed leaf, or exhibits a located break (`DimAcceptedLastLeafAnyLengthOrBreak`, from
`LastLeafFaithful.AcceptedLastLeafAnyLengthOrBreak`). Each of its five outcomes occurs on a DIM
run (`DimAcceptedLastLeafThreeLeaves`, `DimWrongLengthOccurs`, `DimPaddedEntryOccurs`,
`DimPinnedBreakOccurs`, `DimPathCollisionOccurs`); the last two are also the `PinnedBreak` and the
`PathCollision` disjunct of `DimLastBatchProofIdentifiesLastBatchPinned`, each holding alone. On
the honest path, the last leaf's path recomputes the stored root and passes the zero check
(`ContractPathLastHasZeroRightSide`). For every leaf list that fits the height, which every
represented one does, a leaf whose honest path passes the check is the last or exhibits a
`PinnedBreak`, and under a bounded no-collision premise it is exactly the last
(`ContractPathZeroRightSideIsLastOrPinnedBreak`, `ContractPathLastIff`,
`ContractPathLastIffSatisfiable`); these two are `LastLeaf`'s results on the honest siblings and
do not read storage.

No hash premise except the bounded one of `ContractPathLastIff`. Not covered: that compiled
code executes the transcriptions; the `uint256` wrap of `1 << levels` and `_nextLeafIndex++`
(more than 2^255 leaves); storage written directly (`PriorityTree.initFromCommitment`); that
the `MessageRoot`'s writes produce runs (read from the source); chains with an empty tree, or
none (`RootBacking` needs a leaf for every chain id); the batch-leaf encoding and which batches
are pushed (`PROTO-CONTIGUOUS-PUSH`). `MODEL-DIM` in [ASSUMPTIONS.md](../../../ASSUMPTIONS.md)
records the boundary.
