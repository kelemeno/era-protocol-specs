# L2InteropRootStorage

Source: `contracts/interop/L2InteropRootStorage.sol` in the pinned era-contracts tree
(`c67894b9`), with `IL2InteropRootStorage.sol`, `common/Messaging.sol`, and the two readers the
interop gates use (`interop/L2MessageVerification.sol:29-33`,
`atomic-interop/libraries/AtomicInteropProof.sol:171-179`). The whole storage
(`storedInteropRoots`) and both bootloader entry points are modelled, with every check of
`_addInteropRoot` in source order.

Topics `Storage` and `RootImportLink` model the contract at era-contracts `draft/v0.35.0` head
`b17415d20` (byte-identical at `d9f6789` and `e561b9cc2`; the same code, with one more comment
line, at `main` `70096e2`). At `c67894b9`, the interop pin, the contract has no
`latestInteropRootTimestamp`; that version is transcribed separately (`execAtC67`).

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| Storage | [Specs/Storage.lean](Specs/Storage.lean) | [Properties/Storage.lean](Properties/Storage.lean) | [Proofs/Storage.lean](Proofs/Storage.lean) |
| RootImportLink | [Specs/RootImportLink.lean](Specs/RootImportLink.lean) | [Properties/RootImportLink.lean](Properties/RootImportLink.lean) | [Proofs/RootImportLink.lean](Proofs/RootImportLink.lean) |

## Model (`c67894b9`)

Namespace `Contracts.L2InteropRootStorage`. Statements are
`Contracts.L2InteropRootStorage.Properties.*`; each certificate has the same name without the
`Properties` segment.

- **Write-once.** In any run from any storage, an entry with a nonzero root never changes
  (`WriteOnce`); from fresh storage, neither does one with a nonzero timestamp
  (`TimestampNotRewritable`). A successful batch import stores every tuple as given and has
  pairwise distinct, previously unused keys (`BatchImportWritesEach`, `BatchKeysDistinct`).
- **A zero timestamp means nothing imported.** From fresh storage an entry's timestamp is zero
  iff its root is (`ZeroTimestampIffAbsent`, the `IL2InteropRootStorage.sol:18-19` invariant the
  timeout path relies on), and every nonzero entry is an admitted import, as imported
  (`EntriesAreAdmittedImports`).
- **A zero-timestamp entry from earlier storage** is kept forever: inclusion against it is
  accepted and the timeout read at its key fails for every deadline
  (`LegacyEntryBlocksTimeoutForever`, `LegacyEntryCountermodel`). It is not reachable from fresh
  storage, and the source's NatSpec says none was carried over (`:35-39`).

Witness: `RootStorageRunWitness`.

Model boundaries: imports are admitted by a predicate `ok` on the tuple, which the contract does
not check (anything, for the contract alone); `Protocol/InteropAtomicity` topic `SettlementRoots`
instantiates it with the settlement layer's Executor check. Callers, events and `uint256` bounds are
not modelled (`MODEL-ROOT-STORAGE` in `ASSUMPTIONS.md`). At `draft/v0.35.0` `b17415d20` the modelled
checks and write are unchanged; the new `latestInteropRootTimestamp` mapping is not modelled.
`../AtomicFlowManager/` topic `RefundClosesAppend` (`b17415d20`) has its own model of this
contract that includes `latestInteropRootTimestamp`.

## Storage and RootImportLink (`b17415d20`)

Namespace `Contracts.InteropRootStorage`. Statements are `Contracts.InteropRootStorage.Properties.*`;
each certificate has the same name without the `Properties` segment. No result takes a hash
premise: the contract hashes nothing.

- **Who writes, and what.** Every successful call is the bootloader's (`OnlyBootloaderWrites`,
  `LoggedCallersAreBootloader`). One import succeeds exactly when `sides` is one nonzero word, the
  timestamp is nonzero and the key holds a zero root (`AddInteropRootIff`, `AddInteropRootEffect`).
  A batch is its singles in order, all or nothing, and a batch naming a key twice reverts
  (`BatchUnfoldsToSingles`, `BatchRejectsDuplicateKey`).
- **Keys are written once.** A key holding a nonzero root keeps its whole pair, root and
  timestamp, in every later state of every run (`NoOverwrite`). In a logged run the imported keys
  are distinct and were unset at the start, and the storage is exactly the log
  (`EachKeyImportedOnce`, `StorageIsTheLog`; `StoredIffImported` from fresh storage).
- **Timestamps.** Along runs from fresh storage a zero stored timestamp means "nothing imported"
  (`ZeroTimestampIffUnsetInvariant`), and `latestInteropRootTimestamp` is the chain's maximum
  stored timestamp, zero exactly when the chain has no root (`LatestIsMaxInvariant`,
  `LatestZeroIffNothingImported`). Along every run it never decreases and bounds every import of
  the run (`LatestNeverDecreases`, `LatestBoundsEveryImport`). From fresh storage it bounds, in
  every later state, every timestamp stored earlier (`StoredTimestampStaysBelowLatest`), the
  ordering `AtomicFlowManager.append` relies on at `b17415d20`
  (`atomic-interop/AtomicFlowManager.sol:112-125`; the manager is not modelled here).
- **Each check is load-bearing.** With one check deleted: anyone squats a key, after which the
  bootloader's import of it reverts forever (`WithoutAuthAnyoneSquatsAKey`); a stored root is
  replaced (`WithoutExistsCheckRootIsOverwritten`); a stored timestamp is rewritten
  (`WithoutZeroRootCheckTimestampIsRewritten`); a root looks unimported forever
  (`WithoutZeroTimestampCheckRootLooksUnimported`). With no check deleted, any start state holding
  a nonzero root with timestamp zero, which is how a root stored under the earlier `bytes32` value
  type would read, falsifies the zero-timestamp claim in every reachable state
  (`LegacyRootBreaksZeroTimestampClaim`). The claim rests on the source comment that the mapping
  was empty at the v31 upgrade (`:29-31`), which the model takes as its start state and does not
  check.
- **At `c67894b9`.** The pin's calls and runs are this model's with the tracked timestamps dropped
  (`C67894b9CallIsTheProjection`, `C67894b9RunsAreProjectedRuns`), so a stored root is never
  overwritten there either, and from fresh storage a zero timestamp means "nothing imported"
  (`NoOverwriteAtC67894b9`, `ZeroTimestampIffUnsetAtC67894b9`).
- **`RootImportLink`.** `Contracts.RootImport` (`../../Protocol/InteropAtomicity/`, `c67894b9`)
  describes a destination's imports as an abstract predicate and relates snapshots by
  `ImportsGrow`. Reading that predicate off one `c67894b9` storage per destination,
  `ImportsGrow` follows from the storages' runs (`StorageRunsGrowImportsAtC67894b9`), so
  `FinalizableAtPersistsAsImportsGrow` applies to such runs.

Witnesses: `RootImportRunWitness` (a two-call run from fresh storage, with a batch out of
timestamp order), `SingleImportEffectWitness`, `StoredRootSurvivesRunWitness`,
`DuplicateKeyBatchWitness`, `LegacyRootStateWitness`, `C67894b9RunWitness`,
`StorageRunsGrowImportsWitness`.

Model boundaries (`MODEL-ROOT-STORAGE-V35` in `ASSUMPTIONS.md`): the `InteropRootAdded` event is not
modelled (the logged run carries the same data). The caller and the imported tuples are inputs:
that the bootloader imports only the settlement layer's `MessageRoot.historicalRoot` tuples,
checked when the importing batch executes (`ExecutorFacet._verifyDependencyInteropRoots`), is
outside this contract, so nothing here establishes that a stored root or timestamp is authentic.
Results that need a start state start from fresh storage. Code replacement by protocol upgrades
(`OPS-CONFIG`), calldata decoding (`SOL-ABI`) and gas are not modelled. The verifier that reads
these roots is [`../L2MessageVerification/`](../L2MessageVerification/README.md).
