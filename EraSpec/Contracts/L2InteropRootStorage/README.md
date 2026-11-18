# L2InteropRootStorage

Source: `contracts/interop/L2InteropRootStorage.sol` in the pinned era-contracts tree
(`c67894b9`), with `IL2InteropRootStorage.sol`, `common/Messaging.sol`, and the two readers the
interop gates use (`interop/L2MessageVerification.sol:29-33`,
`atomic-interop/libraries/AtomicInteropProof.sol:171-179`). The whole storage
(`storedInteropRoots`) and both bootloader entry points are modelled, with every check of
`_addInteropRoot` in source order.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |

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
