# Consolidation inventory: roots unit

Unit `roots`, branch `consol9/roots`, from `claude/proof-round-9` at `35d2eb9`. Contracts:
MessageRoot, L2InteropRootStorage, ChainBatchRootTree, L2MessageVerification, MessageVerification.
Target commit: era-contracts `draft/v0.35.0` head `b17415d20`. Citations were checked against an
extracted `b17415d20` tree. `c67894b9` and `e561b9cc2` were not available locally, so claims about
those commits were not re-checked here; they are kept only where they already were.

Property counts at the branch point: MessageRoot 71, L2InteropRootStorage 44, ChainBatchRootTree 33,
L2MessageVerification 17, MessageVerification 16.

## Topics

| Contract / topic | Commit it models (checked) | Model | Imported by (outside the topic) | Decision |
|---|---|---|---|---|
| MessageRoot / Model | `b17415d20` (`MessageRootBase.sol`, `L1MessageRoot.sol`; spot-checked) | `Contracts.MessageRoot.State`, `exec`, `Run`, `Reachable`, `Inv` | MessageRoot/Countermodels; `EraSpec.lean` | **canonical** |
| MessageRoot / Countermodels | `b17415d20` | the Model's types (Specs adds toy hashes and configs only) | `EraSpec.lean` | **canonical** (witnesses and countermodels of the Model) |
| MessageRoot / Aggregation | header says `c67894b9`; the modelled code is the same at `b17415d20` apart from line numbers (`seedGenesisRoot`'s non-ZKsync-OS branch and `saveV31UpgradeChainBatchNumber` are gone; the model took neither) | `Contracts.MessageRoot.Aggregation.State` (with ghost leaf preimages, push blocks and historical-root counts), `Step`, `Reach`, `Reachable` under a timestamp rule | `Protocol/InteropAtomicity/{Specs,Proofs}/SettlementRoots.lean` | **re-pin** to `b17415d20` (line numbers only) and keep as the ghost-instrumented aggregation view of the same code. Its statements need the ghost fields (which leaf is counted by which root), which the canonical Model does not have, so they cannot be restated on it without a simulation proof (see "Not done") |
| L2InteropRootStorage / Storage | `b17415d20` (checked `:20-103`) | `Contracts.InteropRootStorage.State`, `exec`, `Step`, `Reach`, `ReachLog` | L2MessageVerification/Verification; RootImportLink | **canonical**. Its `c67894b9` section (`RootsAtC67`, `execAtC67`, `ReachAtC67` and the five `…C67894b9…` statements) is a pin record: **History** |
| L2InteropRootStorage / RootImportLink | links the `c67894b9` storage to `Protocol/InteropAtomicity` `RootImport` | `importWorldAtC67` over `RootsAtC67` | `EraSpec.lean` | **restate-onto-canonical** (`StorageRunsGrowImports` over the canonical `Reach`), and the `c67894b9` statement goes to **History** |
| L2InteropRootStorage / Model | header says `c67894b9`; at `b17415d20` the four checks and the write are the same (`:77-93`), plus the `latestInteropRootTimestamp` update (`:98-100`), which no check reads | `Contracts.L2InteropRootStorage.State` (ℕ keys), `Step ok`, `Reach ok` with an admission predicate `ok` | `Protocol/InteropAtomicity/{Specs,Proofs}/SettlementRoots.lean` | **re-pin** to `b17415d20` and **refinement-lemma**: every successful call of the canonical Storage, projected to `storedInteropRoots` with ℕ keys, is a `Step ok` for any `ok` its imports meet, so the Model's run results apply to the canonical runs. Kept as the abstract `ok`-admitted view the Protocol topic instantiates |
| ChainBatchRootTree / Layout | `b17415d20` (checked `:11-62`) | `compute`, `cbrPair`, `OpeningCollision` over arbitrary keccak | AtomicInteropProof, Merkle/DomainSeparation, Protocol/InteropAtomicity (docstring mentions only) | **canonical** for the chain batch root |
| ChainBatchRootTree / GenesisSeed | `b17415d20` | `SeedChainState` (one chain's slice of `MessageRootBase`), `SeedDiamond`, `seedStep`, `seedRun` | `EraSpec.lean` | **refinement-lemma**: a call of the canonical MessageRoot Model on reachable storage projects, for a chain other than `block.chainid`, onto a `seedExec` call or a stutter. The slice model stays: it also models the diamond and `createNewChain`, which MessageRoot does not |
| ChainBatchRootTree / LogConfinement | `b17415d20` | `PreTree`, `land`, `LandingBreak` over Layout's `node`; its own `L2Log`/`logPre` (same bytes as `MessageHashing`'s) | `EraSpec.lean` | **canonical** (the `L2Log` duplicate with `Contracts/MessageHashing` is outside this unit's folders; noted below) |
| L2MessageVerification / Verification | `b17415d20` (checked `:18-56`) | `proveRecursive`, `anchorRec` over the canonical Storage `State` | `EraSpec.lean` | **canonical** (already on the canonical storage model) |
| MessageVerification / StatusProof | `b17415d20` (checked `MV:85-147`, `MH:152-167`, `MRB:343-373`) | `LogProofAccepted` against a stored root `R`; its own `chainBatchRoot` with the documented reserved node | `EraSpec.lean` | **refinement-lemma**: (1) `chainBatchRoot (efficientHash keccak)` is ChainBatchRootTree's `compute` under `ReservedSubtreeDocumented`; (2) against the canonical MessageRoot storage, `R` is `chainBatchRoots[c][n]` and the final-node verdict is `LogProofAccepted`'s last two conjuncts |
| MessageVerification / StatusProofKeccak | `b17415d20` | `StatusWalkKeccakBreak` over StatusProof | `EraSpec.lean` | **canonical** |

Namespaces: L2MessageVerification and MessageVerification both use `Contracts.MessageVerification`
(no clashes today). L2InteropRootStorage uses two namespaces, `Contracts.L2InteropRootStorage`
(Model) and `Contracts.InteropRootStorage` (Storage). Renaming them would rename every statement
for no gain in strength, so this unit leaves the namespaces as they are.

## Files outside the unit's folders that depend on it

- `Protocol/InteropAtomicity/{Specs,Proofs}/SettlementRoots.lean`: imports MessageRoot/Aggregation
  and L2InteropRootStorage/Model. Both topics stay (re-pinned), so no edit is needed.
- `Protocol/InteropAtomicity/Specs/RootImport.lean`: imported by RootImportLink.
- `EraSpec.lean`: the module list.

## Other models of these contracts outside the unit's folders

Found by grep; not consolidated here (other units' folders):
`AtomicFlowManager/Specs/RefundClosesAppend.lean` (its own model of `L2InteropRootStorage` with
`latestInteropRootTimestamp`), `DynamicIncrementalMerkle/Specs/ChainTreeBacking.lean` (MessageRoot
chain trees), `Protocol/BatchCounters/Specs/MessageRootSync.lean` (MessageRoot's
`currentChainBatchNumber`), and `Protocol/InteropAtomicity/Specs/{SystemAtV35,Atomicity,RootImport}.lean`.
Each could be linked to the canonical models here by a refinement lemma like the ones below.

## Done in this unit

- MessageRoot/Aggregation re-pinned to `b17415d20` (line numbers; the "Later heads" note replaced by
  the relation to the canonical model).
- L2InteropRootStorage/Model re-pinned to `b17415d20`, with `Refinement`: canonical calls and runs
  are `Model` steps and runs (`CanonicalCallIsModelStep`, `CanonicalRunIsModelRun`).
- L2InteropRootStorage `c67894b9` transcription and its five statements, and the `c67894b9`
  RootImportLink, moved to `History/`; RootImportLink restated on the canonical storage
  (`StorageRunsGrowImports`).
- ChainBatchRootTree/MessageRootLink: canonical MessageRoot calls project onto `seedExec`
  (`MessageRootCallIsSeedCall`, `InitializedSliceIsFresh`, `ReachableSliceIsSeedRun`).
- MessageVerification/Refinement: `ChainBatchRootIsCompute`, `StatusProofAtMessageRoot`.
- Renames: `handoff/2026-11-19/renames/roots.json` (7 entries, all History moves).

## Tag plan (not applied: `EraSpec/Core/Headline.lean` was not on `claude/proof-round-9` yet)

Apply with `import EraSpec.Core.Headline` and `attribute [tag] Properties.X` at the end of each
module. Untagged statements are supporting lemmas; History, Refinement, RootImportLink-at-c67894b9
and MessageRootLink statements stay untagged.

- `EraSpec/Contracts/MessageRoot/Properties/Model.lean`:
  - headline: `ChainIndexBijection`, `BatchRootsWriteOnce`, `SettledBatchRootsFrozen`, `ChainTreeIsOrderedLog`, `AppendExact`, `ChainWritersOnly`, `MigrationSkippedBatchesNeverRecorded`, `ProofRootIsRecordedRoot`, `AggregatedRootPinsChainRootOrCollision`, `GenesisSeedOnce`
- `EraSpec/Contracts/MessageRoot/Properties/Countermodels.lean`:
  - witness: `EveryEntryPointRun`, `RegistrationPremisesHold`, `AppendPremisesHold`, `MigrationPremisesHold`, `RunPremisesHold`, `WritersOnlyPremisesHold`, `LogIdPremisesHold`, `InteropPremisesHold`, `SameTreesPremisesHold`, `FinalNodeFallbackFollowsTheChain`
  - countermodel: `AggregatedRootCollisionFires`, `MigrationBeforeRegistrationIsOverwritten`, `ChainTreePositionIsNotBatchNumber`, `RegisteredCheckLoadBearing`, `ConsecutiveCheckLoadBearing`, `MigratingCheckLoadBearing`, `RecordRegisteredCheckLoadBearing`
- `EraSpec/Contracts/MessageRoot/Properties/Aggregation.lean`:
  - headline: `AggregatesStrictFromMessageRoot`
  - witness: `AggregationWitness`, `AggregationRegistryWitness`, `RecordOnlyBatchNotCitableWitness`
  - countermodel: `EqualTimestampEscapesRoot`, `MidBlockReadEscapesRoot`, `RecordOnlyGap`, `OnboardedChainPositionsAreNotBatchNumbers`
- `EraSpec/Contracts/L2InteropRootStorage/Properties/Storage.lean`:
  - headline: `OnlyBootloaderWrites`, `NoOverwrite`, `EachKeyImportedOnce`, `ZeroTimestampIffUnsetInvariant`, `LatestIsMaxInvariant`, `StoredTimestampStaysBelowLatest`
  - witness: `RootImportRunWitness`, `SingleImportEffectWitness`, `StoredRootSurvivesRunWitness`, `DuplicateKeyBatchWitness`, `LegacyRootStateWitness`
  - countermodel: `WithoutAuthAnyoneSquatsAKey`, `WithoutExistsCheckRootIsOverwritten`, `WithoutZeroRootCheckTimestampIsRewritten`, `WithoutZeroTimestampCheckRootLooksUnimported`, `LegacyRootBreaksZeroTimestampClaim`
- `EraSpec/Contracts/L2InteropRootStorage/Properties/RootImportLink.lean`:
  - headline: `StorageRunsGrowImports`
  - witness: `StorageRunsGrowImportsRunWitness`
- `EraSpec/Contracts/L2InteropRootStorage/Properties/Model.lean`:
  - witness: `RootStorageRunWitness`
  - countermodel: `LegacyEntryCountermodel`
- `EraSpec/Contracts/ChainBatchRootTree/Properties/Layout.lean`:
  - headline: `OpeningPinsLeafOrCollision`, `ImtRootHopPinsLeafOrCollision`
  - witness: `HonestOpeningAccepted`, `HonestOpeningNoCollision`, `ReservedOpeningWitness`, `ImtRootHopWitness`, `GenesisLeafOneRejectsInitialAggregatedRootWitness`
  - countermodel: `ComputeRootNeedsDocumentedValue`, `ImtRootHopDepthPinNeeded`, `OpeningCollisionFires`
- `EraSpec/Contracts/ChainBatchRootTree/Properties/GenesisSeed.lean`:
  - headline: `GenesisRootStable`, `SeedAtMostOnce`, `NoSeedAfterRealBatch`
  - witness: `GenesisSeedRunWitness`, `GenesisImtLeavesWitness`
- `EraSpec/Contracts/ChainBatchRootTree/Properties/LogConfinement.lean`:
  - headline: `ImtBatchRootLogProofConfinedOrKeccakEvent`
  - witness: `HonestLogProofPassesLeafZero`, `LogProofPassesLeafZeroWitness`
  - countermodel: `ImtLandingCollisionFires`
- `EraSpec/Contracts/L2MessageVerification/Properties/Verification.lean`:
  - headline: `AcceptedIffStoredRootAtAnchor`, `SharedEntryAcceptsIff`, `AcceptanceSurvivesRuns`, `AcceptedFromFreshStorageWasImported`, `AcceptedAnchorHasNonzeroTimestamp`
  - witness: `HonestOneHopProofAccepted`, `OneHopProofWitness`
  - countermodel: `WithoutNonzeroCheckUnimportedKeyAccepts`
- `EraSpec/Contracts/MessageVerification/Properties/StatusProof.lean`:
  - headline: `HeldLogIsProvable`
  - witness: `HonestBatchWalkNoBreak`, `HeldLogIsProvableWitness`, `StatusProofWitness`
  - countermodel: `BootloaderPremiseLoadBearing`, `DefaultLeafCheckLoadBearing`
- `EraSpec/Contracts/MessageVerification/Properties/StatusProofKeccak.lean`:
  - headline: `FailureProofForSucceededTxIsKeccakBreak`
  - witness: `HonestStatusWalkNoKeccakBreak`
  - countermodel: `ShortStatusProofIsCrossLengthCollision`

## Not done in this unit (and why)

- **Aggregation onto the canonical MessageRoot Model.** A simulation from the Model's runs to the
  Aggregation runs needs a premise on the per-call environments (blocks and timestamps of
  consecutive calls), the `FullMerkle` root as the Aggregation's abstract `sharedRoot`, and the
  ghost reconstruction for every entry point. The Aggregation statements are kept, re-pinned, and
  the README says they are about the same code.
- **One `L2Log`.** `ChainBatchRootTree.L2Log`/`logPre` and `MessageHashing.L2Log`/`logPre` encode
  the same 88 bytes. Merging them touches `Contracts/MessageHashing` (another unit).
- **`SettlementRoots` onto the canonical models.** It is a Protocol topic; it keeps using the two
  re-pinned abstract views.
- **Headline tags.** The infra unit's `EraSpec/Core/Headline.lean` had not reached
  `claude/proof-round-9` when this unit finished, so no tags are applied; the READMEs carry the
  headline lists and the tag plan above says which statement gets which tag.
