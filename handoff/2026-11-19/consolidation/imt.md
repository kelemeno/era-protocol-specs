# Consolidation inventory: IndexedMerkleTree and L2InteropCommitmentTree (unit `imt`)

Branch `consol9/imt`, from `claude/proof-round-9` at `35d2eb9`. Target commit: era-contracts
`draft/v0.35.0` head `b17415d20`.

## Source check

At `b17415d20` the cited source files are
`l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol` (173 lines),
`common/libraries/FullMerkle.sol`, `common/libraries/Merkle.sol` and
`atomic-interop/L2InteropCommitmentTree.sol` (127 lines). Compared with the other pins in the
local era-contracts clone:

| File | `d9f6789` | `3605e82` (`main`) | `70096e2ea` (`main`) | `c67894b9` (interop pin) |
|---|---|---|---|---|
| `IndexedMerkleTree.sol` | identical | identical | identical | not in the local clone |
| `FullMerkle.sol`, `Merkle.sol` | identical | identical | identical | not in the local clone |
| `L2InteropCommitmentTree.sol` | identical | error imports only | error imports only | not in the local clone |

`c67894b9` (and `e561b9cc2`) are not reachable from the local era-contracts clone, so pin line
numbers were not re-checked. They survive only in History and in the "what differs" notes, as
earlier rounds recorded them. Two logic differences between the pin and `b17415d20` matter for
these models. Both were already recorded in the headers and are re-checked against `b17415d20`:

1. **Padding.** `setup` passes `IMT_EMPTY_LEAF_HASH` (`common/Config.sol:141`) to
   `FullMerkle.setup` (`IndexedMerkleTree.sol:51`) and `hashLeaf({0,0,0})` to `pushNewLeaf`
   (`:52`). The pin passed `hashLeaf({0,0,0})` to both.
2. **Low-leaf walk.** `insert`'s loop (`IndexedMerkleTree.sol:90-93`) has no hop bound. The pin
   counted `MAX_LOW_INDEX_SEARCH_ATTEMPTS = 5` hops.

## Models

There are two state spaces, one per contract. All other models are layers on the second:

* **IndexedMerkleTree:** `IMTAbstract` over `Finset AbsLeaf` (`Specs/Model.lean`), the sorted
  list with its indices erased: `imtInsert`, `Evolution`, `GuardedEvolution`. It is pure order
  theory and tied to no pin. `UnboundedSearchAtV35` adds the v35 walk (`WalkV35`, `InsertV35`,
  `RunV35`) on the same state.
* **L2InteropCommitmentTree:** the indexed list state `Tree` (`Specs/Model.lean`: `leaf`,
  `nextIndex`, `valueToIndex`, `lowSearch`, `InsertGuard`, `insert`, `Run`), which `toAbs`
  projects to `IMTAbstract`. The other Specs modules are layers on it, not independent models:
  - `Reaches`: batch steps.
  - `TreeRoot`: the root fold, with a padding parameter `z0`.
  - `RunHeight`: `FullMerkle`'s two counters.
  - `CachedRoot`: `FullMerkle`'s whole storage, `CState`.
  - `InitOnce`: callers, `initL2` and the predeploy.
  - The v35 forms of these layers.

Several definitions were duplicated, with identical bodies under different names:

| Definition | Copies |
|---|---|
| the unbounded walk exits at `low` | `WalkSucceedsAtHead` (HintSearchAtHead), `WalkExitsAtV35` (CommitmentTreeAtV35), `SearchExitsV35` (UnboundedSearchAtV35) |
| the v35 insert checks | `InsertChecksAtHead` (HintSearchAtHead), `InsertChecksAtV35` (CommitmentTreeAtV35) |
| `setup` with a padding parameter | `cSetupPad` (PaddingAtHead), `cSetupAtPadding` (ReclaimGateFaithful) |
| states reached from it | `CReachesPad` (PaddingAtHead), `CReachesAtPadding` (ReclaimGateFaithful) |

**Canonical v35 model.**
- **IndexedMerkleTree:** `IMTAbstract`, with the v35 walk.
- **L2InteropCommitmentTree:** the machine `CTxStepAtV35` / `CTxRunAtV35` of
  `CommitmentTreeAtV35`. It has both entry points with their callers, starts from the predeploy's
  storage, acts on `CState`, walks without a bound, and takes the padding parameter
  `zE = IMT_EMPTY_LEAF_HASH`. It sits on the shared layers `Model` → `Reaches` → `TreeRoot` →
  `RunHeight` → `CachedRoot`.
- **Tree-level v35 machines** (`TxStepAtHead`, `InsertCallV35`/`RunCallV35`): these are
  projections of the canonical machine, related to it by proved lemmas.

## Topics

"Imported by" lists modules outside the topic's own Specs/Properties/Proofs triple, across the
whole `EraSpec` tree except `EraSpec.lean`.

### IndexedMerkleTree

| Topic | Commit (header) | Model | Imported by | Decision |
|---|---|---|---|---|
| Model | pure order theory (`c67894b9` only in a correction note) | `IMTAbstract`: `Finset AbsLeaf`, `imtInsert`, `Evolution`, `GuardedEvolution` | every IMT topic; L2ICT Model; AtomicFlowManager Model; AtomicInteropProof StaleSnapshot, StaleSnapshotBranches, StaleSnapshotFaithful, Timestamps; Protocol FlowAtomicity, FlowAtomicityPerChain, MultichainGate Model, NoTheft | **canonical**; re-cite to `b17415d20` |
| InsertGuard | none (order theory) | `IMTAbstract` | ModelStrong proofs | canonical layer; re-cite |
| ModelStrong | `c67894b9` in prose | `IMTAbstract` | ResetAndZeroStrong | canonical layer. Its padding-leaf statements are abstract countermodels showing the membership premise is needed. They hold at every revision and are not pin records |
| ResetAndZero | none | `IMTAbstract` | ResetAndZeroStrong; L2ICT InitOnce | canonical layer; re-cite |
| ResetAndZeroStrong | `c67894b9` in prose | `IMTAbstract` | none | canonical layer; re-cite |
| UnboundedSearchAtV35 | `b17415d20` | `IMTAbstract` + `WalkV35`, `InsertV35`, `RunV35` | L2ICT UnboundedSearchAtV35 | **canonical**: already v35, the v35 walk on the abstract state |
| ReclaimGateFaithful | `c67894b9` and `b17415d20` (padding parameter) | `HState`/`CState` runs at a padding `z0`; `cSetupAtPadding`, `CReachesAtPadding` | none | **restate onto canonical**: use `cSetupPad`/`CReachesPad`, now in CachedRoot. The five `Pinned*` results at the pin's padding go to **History** |

### L2InteropCommitmentTree

| Topic | Commit (header) | Model | Imported by | Decision |
|---|---|---|---|---|
| Model | none (list state) | `Tree`, `Valid`, `lowSearch`, `InsertGuard`, `insert`, `Run` | all L2ICT topics; AtomicInteropProof ProofPolarityStrong, StaleSnapshotFaithful; MultichainGate Model; Refinement | **canonical layer**; re-cite. The insert guard is v35's loop exit |
| Reaches | none | `Reaches` over `Tree` | InteropAtomicity Atomicity, OncePerLeg; MultichainGate DeployedGate | canonical layer |
| HintSearch | pin (`MAX_LOW_INDEX_SEARCH_ATTEMPTS`) | `maxLowIndexSearchAttempts = 5`, `chainTree` | InitOnce, TreeRoot proofs, UnboundedSearchAtV35; InteropAtomicity OncePerLeg; MultichainGate DeployedGate | **re-pin with the difference stated**. The fuel-generic results hold at v35. The five-hop bound is the pin's, kept as the bounded-loop comparison the v35 topics use |
| TreeRoot | `c67894b9` | root fold with padding parameter `z0`; verifiers; `TreeRootBreak` | RunHeight; AtomicInteropProof StaleSnapshotFaithful; ChainBatchRootTree Layout; Merkle DomainSeparation; InteropAtomicity Atomicity, SharedCommitment; MultichainGate DeployedGate; Refinement | canonical layer (the padding is a parameter). The four `PaddingCollision…`/`PaddingCountermodel…` results at the pin's padding go to **History** |
| TreeRootStrong | none | log-safety over `TreeRoot` | none | canonical layer; re-cite |
| RunHeight | `c67894b9` | `HState`: list state + `(_leafNumber, _height)` | CachedRoot, InitOnce, PublishedRootCommits, TreeRootStrong, ReclaimGateFaithful; InteropAtomicity SourceHeight; MultichainGate DeployedGate | canonical layer. `PaddingForgeryAtOwnHeight` goes to **History** |
| CachedRoot | `c67894b9` | `CState`: list state + whole `FullMerkle` storage; `cSetup` at the pin's padding | PaddingAtHead, CommitmentTreeAtV35, ReclaimGateFaithful | canonical storage layer. It gains `cSetupPad`/`CReachesPad` (the v35 setup, with a padding parameter). `cSetup` stays as the pin-padding instance, with the difference stated. `CThreeLeafWitness` goes to **History** |
| PublishedRootCommits | none (FullMerkle lines) | over `RunHeight` | none | canonical layer; re-cite |
| InitOnce | `c67894b9` | `TxStep` (the pin's five-hop search), `TxStepNoGuard`, `Roles`, `Call`, `predeploy`, `LevelRun` | HintSearchAtHead, CommitmentTreeAtV35 | **re-pin with the difference stated**. The shared definitions (roles, calls, predeploy, `setupWrites`, traces, `LeafLevel`) are v35's. `TxStep`'s search is the pin's five-hop search, and `TxRunAtHeadIsRelabelledTxRun` and `PinTxRunIsTxRunAtHead` relate it to the v35 machine. Moving it to History would strand the head results, which are proved through it |
| HintSearchAtHead | `70096e2` / `b17415d20` | `TxStepAtHead` over `Tree` | InteropAtomicity OncePerLegAtHead | **refinement lemma**. Its walk and checks become the canonical `WalkExitsAtV35`/`InsertChecksAtV35`, removing the duplicates. A projection lemma from the canonical machine makes it the list-state view of `CTxRunAtV35` |
| UnboundedSearchAtV35 | `b17415d20` | `InsertCallV35`, `RunCallV35` over `Tree` | none | **refinement lemma**. `SearchExitsV35` becomes `WalkExitsAtV35`, and a proved equivalence relates `InsertCallV35` to `InsertChecksAtV35` |
| PaddingAtHead | `3605e82` (library identical at `b17415d20`) | keccak at the byte level over `CState` | none | **re-pin** to `b17415d20`; only the wrapper's error imports differ. Its `cSetupPad`/`CReachesPad` move to CachedRoot |
| CommitmentTreeAtV35 | `b17415d20` | `CTxStepAtV35`/`CTxRunAtV35` over `CState` | none | **canonical** |

### DynamicIncrementalMerkle

Not in this unit. It models `DynamicIncrementalMerkle.sol`, an append-only Merkle accumulator
for message roots, and shares no definition with the IMT models. It is not touched here.

## History

These results are kept as the record of the H2 padding finding at `c67894b9`, where the tree
padded with `hashLeaf({0,0,0})`. They move under `EraSpec/Contracts/<C>/History/`, with a
`History` namespace segment:

* IndexedMerkleTree, from ReclaimGateFaithful: `PinnedGateAcceptsEveryValueBelowCapacity`,
  `PinnedGateAcceptsEveryValueOffPowersOfTwo`, `PinnedReclaimDichotomyReadingFails`,
  `PinnedDeliveryFinalityReadingFails`, `PinnedCounterexampleMeetsCapstoneHypotheses`.
* L2InteropCommitmentTree: from TreeRoot, `PaddingCollisionForgesAbsence`,
  `PaddingCollisionRefundsDeliveredLeg`, `PaddingCountermodelLocatesPaddingHit` and
  `PaddingCountermodelExactlyPaddingHit`; from RunHeight, `PaddingForgeryAtOwnHeight`; from
  CachedRoot, `CThreeLeafWitness`.

Each result keeps its statement and proof. Only its name gains the `History` segment (see
`../renames/imt.json`).

## Not done in this unit

* The `…AtHead` / `…AtV35` topic and property names are kept. External references depend on
  them, and one model per contract does not require renaming them.
* `InitOnce` and `HintSearch` keep the pin's five-hop search, with the difference stated in their
  headers. Restating `InitOnce`'s 23 results directly over `CTxStepAtV35` is left for a later
  step.
* The `HashAssumptions`-premised results of `TreeRoot` are unchanged. They are vacuous
  (`HashAssumptionsUnsatisfiable`).
