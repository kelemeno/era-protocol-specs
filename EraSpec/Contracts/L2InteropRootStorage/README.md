# L2InteropRootStorage

## Headline guarantees

All about `l1-contracts/contracts/interop/L2InteropRootStorage.sol` at era-contracts
`draft/v0.35.0` head `b17415d20`. The contract hashes nothing, so no statement has a hash premise.
A "run" is any sequence of successful calls, by any caller, with any arguments.

- `Contracts.InteropRootStorage.Properties.OnlyBootloaderWrites`: every successful call was made
  by the bootloader address.
- `Contracts.InteropRootStorage.Properties.NoOverwrite`: along any run from any storage, a key
  holding a nonzero root keeps its whole stored pair, root and timestamp.
- `Contracts.InteropRootStorage.Properties.EachKeyImportedOnce`: in any logged run, the imported
  keys are pairwise distinct and each was unset at the start.
- `Contracts.InteropRootStorage.Properties.ZeroTimestampIffUnsetInvariant`: on fresh storage, and
  along any run from storage where it holds, a stored timestamp is zero exactly when the stored
  root is. Premise: the storage started empty, as the source comment (`:29-31`) says it was at the
  v31 upgrade; `LegacyRootBreaksZeroTimestampClaim` shows a carried-over root breaks it.
- `Contracts.InteropRootStorage.Properties.LatestIsMaxInvariant`: on fresh storage, and along any
  run from storage where it holds, `latestInteropRootTimestamp[c]` bounds every timestamp stored
  for `c` and, if nonzero, is one of them.
- `Contracts.InteropRootStorage.Properties.StoredTimestampStaysBelowLatest`: for storage reached
  from fresh storage, every stored timestamp stays at or below the chain's
  `latestInteropRootTimestamp` in every later state.
- `Contracts.InteropRootStorage.Properties.StorageRunsGrowImports`: if each destination's storage
  moves by a run, the imports read off the storages only grow
  (`Contracts.RootImport.ImportsGrow`, the premise of
  `Contracts.RootImport.Properties.FinalizableAtPersistsAsImportsGrow`).

Nothing here makes a stored root authentic: which tuples the bootloader imports is checked on the
settlement layer (`ExecutorFacet._verifyDependencyInteropRoots`), outside this contract.

## Topics

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Storage (canonical) | [Specs/Storage.lean](Specs/Storage.lean) | [Properties/Storage.lean](Properties/Storage.lean) | [Proofs/Storage.lean](Proofs/Storage.lean) |
| RootImportLink | [Specs/RootImportLink.lean](Specs/RootImportLink.lean) | [Properties/RootImportLink.lean](Properties/RootImportLink.lean) | [Proofs/RootImportLink.lean](Proofs/RootImportLink.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| Refinement | [Specs/Refinement.lean](Specs/Refinement.lean) | [Properties/Refinement.lean](Properties/Refinement.lean) | [Proofs/Refinement.lean](Proofs/Refinement.lean) |
| History: `c67894b9` | [History/Specs/AtC67894b9.lean](History/Specs/AtC67894b9.lean) | [History/Properties/AtC67894b9.lean](History/Properties/AtC67894b9.lean) | [History/Proofs/AtC67894b9.lean](History/Proofs/AtC67894b9.lean) |

## Storage and RootImportLink (canonical)

Namespace `Contracts.InteropRootStorage`. The whole storage (both mappings) and both bootloader
entry points, every check of `_addInteropRoot` in source order. Further results:
`AddInteropRootIff`, `AddInteropRootEffect`, `BatchUnfoldsToSingles`, `BatchRejectsDuplicateKey`,
`StorageIsTheLog`, `StoredIffImported`, `LatestNeverDecreases`, `LatestBoundsEveryImport`,
`LatestZeroIffNothingImported`. Each check is load-bearing: `WithoutAuthAnyoneSquatsAKey`,
`WithoutExistsCheckRootIsOverwritten`, `WithoutZeroRootCheckTimestampIsRewritten`,
`WithoutZeroTimestampCheckRootLooksUnimported`. Witnesses: `RootImportRunWitness`,
`SingleImportEffectWitness`, `StoredRootSurvivesRunWitness`, `DuplicateKeyBatchWitness`,
`LegacyRootStateWitness`, `StorageRunsGrowImportsRunWitness`.

Model boundaries (`MODEL-ROOT-STORAGE-V35` in `ASSUMPTIONS.md`): events, calldata decoding, gas and
code replacement by upgrades are not modelled; the caller and the imported tuples are inputs.

## Model and Refinement

Namespace `Contracts.L2InteropRootStorage`. `Model` is a coarser view of the same code that
`../../Protocol/InteropAtomicity/` topic `SettlementRoots` instantiates: `storedInteropRoots` only,
`ℕ` keys and timestamps, no callers, and an admission predicate `ok` on each import. Its results:
`WriteOnce`, `TimestampNotRewritable`, `BatchImportWritesEach`, `BatchKeysDistinct`,
`ZeroTimestampIffAbsent`, `EntriesAreAdmittedImports`, `LegacyEntryBlocksTimeoutForever`,
`LegacyEntryCountermodel`; witness `RootStorageRunWitness` (`MODEL-ROOT-STORAGE`).

`Refinement` proves that the canonical model refines it: `toModel` reads the canonical storage
exactly at every addressable key (`ToModelReadsTheStorage`, `ToModelEmpty`), every successful
canonical call is a `Step ok` for any `ok` admitting its imports (`CanonicalCallIsModelStep`), and
every logged canonical run is a `Reach ok` run (`CanonicalRunIsModelRun`). So the `Model` results
hold of the canonical runs.

## History

`History/` is the record of the interop pin `c67894b9`, where the contract had no
`latestInteropRootTimestamp`; it is not a claim about `b17415d20`. Namespace
`Contracts.InteropRootStorage.History`: that version is the canonical model with the tracked
timestamps dropped (`C67894b9CallIsTheProjection`, `C67894b9RunsAreProjectedRuns`), so
`NoOverwriteAtC67894b9` and `ZeroTimestampIffUnsetAtC67894b9` hold there, and its runs grow
`RootImport` imports (`StorageRunsGrowImportsAtC67894b9`). Witnesses: `C67894b9RunWitness`,
`StorageRunsGrowImportsWitnessAtC67894b9`.

The verifier that reads these roots is [`../L2MessageVerification/`](../L2MessageVerification/README.md).
