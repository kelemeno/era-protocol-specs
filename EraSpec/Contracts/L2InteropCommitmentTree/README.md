# L2InteropCommitmentTree

Source: `l1-contracts/contracts/atomic-interop/L2InteropCommitmentTree.sol` over
`common/libraries/IndexedMerkleTree.sol` and `FullMerkle.sol`, at era-contracts `draft/v0.35.0`
`b17415d20`.

**The model.** The canonical model is the machine `CTxStepAtV35` / `CTxRunAtV35`
(`Specs/CommitmentTreeAtV35.lean`). It covers both entry points, `initL2()` (upgrader only) and
`insert(v, hint)` (appender only), and acts on the list state and the whole `FullMerkle` storage
(`CState`). Runs start from the predeploy's all-zero storage. The walk is unbounded, and the
padding constant is a parameter `zE` (`IMT_EMPTY_LEAF_HASH` at `b17415d20`). It is built on
shared layers:
- `Model`: the list state.
- `TreeRoot`: the root fold and the two verifiers.
- `RunHeight`: `FullMerkle`'s counters.
- `CachedRoot`: the whole storage.

The list-state machines `TxStepAtHead` (`HintSearchAtHead`) and `InsertCallV35`
(`UnboundedSearchAtV35`) are its projections, related by proved lemmas.

## Headline guarantees

Unless a premise below says otherwise, each statement holds for every node hash, leaf hash,
padding constant `zE` and pair of role addresses. Its run is a run of the v35 machine: a
sequence of successful transactions, from the predeploy's all-zero storage. Gas, and the leaf
hook's report, are not modelled. A reverted transaction is an idle step.

- `Contracts.InteropCommitmentTree.Properties.CTxRunAtV35StoredRootIsPublished`: at every step
  the storage is the predeploy's or meets all of the following. The list state is reached from
  `setup` and valid, the two copies of `_leafNumber` agree, `_height` is the source's, the
  storage caches the leaf hashes padded with `zE`, and `root()` is their fold at `_height`.
  Premise: a run from the predeploy.
- `…Properties.CTxRunAtV35ContractProofsAtStoredRoot`: at every initialized step, `root()`
  accepts the contract's own `merklePath` proofs. They give inclusion for every key and
  non-inclusion for every absent nonzero value, with no located break. An accepted inclusion
  proof and an accepted non-inclusion proof of the same value together locate a `TreeRootBreak`.
  Premises: a run from the predeploy; the step is initialized.
- `…Properties.CTxRunAtV35EmptySlotLocatesPadding`: a path that `root()` accepts and that
  presents a leaf at an index at or beyond the leaf count has one of these: the leaf's hash
  equals `zE`, a node-hash collision on the path, or a wrong length. Premise: a run from the
  predeploy.
- `…Properties.CTxRunAtV35ReclaimableIffAbsent`: at every initialized step, a nonzero value is
  straddled by a leaf of the tree exactly when it is not a key. Premises: a run from the
  predeploy; the step is initialized; the value is nonzero.
- `…Properties.CTxRunAtV35KeysMono` and `CTxRunAtV35InitL2AtMostOnce`: keys are never removed,
  and at most one `initL2()` succeeds. Premise: a run, from any start.
- `…Properties.NonInclusionAtHeadIsAbsentOrKeccakCollision` and
  `ProofsExclusiveAtHeadOrKeccakCollision`: these use `b17415d20`'s actual hashing, keccak over
  the byte strings the source hashes. A `verifyNonInclusion` accepted against the stored root
  means the value is absent, or keccak collides on two different byte strings that the
  submitted proof names. The same holds for a pair of inclusion and non-inclusion proofs.
  Premises: keccak is any function; the state is reached from `setup` by guarded inserts, with
  `IMT_EMPTY_LEAF_HASH` padding.
- `…Properties.InsertAtHeadEnabledIff`: on a valid tree, an insert's checks pass exactly when
  the tree is initialized, the value is nonzero and unregistered, and the hint is an occupied
  index whose value is below the value. So no hint that passes the up-front checks makes the
  walk revert. Premise: the tree is valid.

**Witnesses:** `StaleHintCRunWitnessAtV35` (a run whose last insert is six hops from its hint,
which the pin's five-hop search refused), `NonInclusionAtHeadWitness`,
`ContractProofsAtStoredRootAtHead`, `PaddingAtHeadThreeLeafRun`, `InsertAtHeadWitness`,
`StaleHintRunWitnessAtHead`, `ChainTreeRunCallsV35`, `GenesisRunWitness`, `HThreeRunWitness`.

**Countermodels**, each showing that a premise or disjunct is needed:
- each case of the keccak break fires alone: `PinForgeryAtHeadFiresOnCollision`,
  `LeafCollisionAtHeadFires`, `NodeCollisionAtHeadFires`, `OutOfRangeIndexAtHeadWitness`,
  `TreeRootBreakEveryCaseFires`;
- `PaddingForgeryAtV35Witness`: with the pin's constant as `zE`, the machine accepts the forgery;
- `GuardlessReinitBreaksExclusivity`: without `IMTAlreadyInitialized`, a delivered value becomes
  reclaimable;
- `TreeRootBreakAtHeadNeedsNextIndexBound`;
- `HashAssumptionsUnsatisfiable`: the `HashAssumptions`-premised results of `TreeRoot` are
  vacuous, and their `…OrBreak` forms replace them.

## Topics

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| CommitmentTreeAtV35 (canonical) | [Specs/CommitmentTreeAtV35.lean](Specs/CommitmentTreeAtV35.lean) | [Properties/CommitmentTreeAtV35.lean](Properties/CommitmentTreeAtV35.lean) | [Proofs/CommitmentTreeAtV35.lean](Proofs/CommitmentTreeAtV35.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| Reaches | [Specs/Reaches.lean](Specs/Reaches.lean) | [Properties/Reaches.lean](Properties/Reaches.lean) | [Proofs/Reaches.lean](Proofs/Reaches.lean) |
| HintSearch | [Specs/HintSearch.lean](Specs/HintSearch.lean) | [Properties/HintSearch.lean](Properties/HintSearch.lean) | [Proofs/HintSearch.lean](Proofs/HintSearch.lean) |
| TreeRoot | [Specs/TreeRoot.lean](Specs/TreeRoot.lean) | [Properties/TreeRoot.lean](Properties/TreeRoot.lean) | [Proofs/TreeRoot.lean](Proofs/TreeRoot.lean) |
| TreeRootStrong | [Specs/TreeRootStrong.lean](Specs/TreeRootStrong.lean) | [Properties/TreeRootStrong.lean](Properties/TreeRootStrong.lean) | [Proofs/TreeRootStrong.lean](Proofs/TreeRootStrong.lean) |
| RunHeight | [Specs/RunHeight.lean](Specs/RunHeight.lean) | [Properties/RunHeight.lean](Properties/RunHeight.lean) | [Proofs/RunHeight.lean](Proofs/RunHeight.lean) |
| CachedRoot | [Specs/CachedRoot.lean](Specs/CachedRoot.lean) | [Properties/CachedRoot.lean](Properties/CachedRoot.lean) | [Proofs/CachedRoot.lean](Proofs/CachedRoot.lean) |
| PublishedRootCommits | [Specs/PublishedRootCommits.lean](Specs/PublishedRootCommits.lean) | [Properties/PublishedRootCommits.lean](Properties/PublishedRootCommits.lean) | [Proofs/PublishedRootCommits.lean](Proofs/PublishedRootCommits.lean) |
| InitOnce | [Specs/InitOnce.lean](Specs/InitOnce.lean) | [Properties/InitOnce.lean](Properties/InitOnce.lean) | [Proofs/InitOnce.lean](Proofs/InitOnce.lean) |
| HintSearchAtHead | [Specs/HintSearchAtHead.lean](Specs/HintSearchAtHead.lean) | [Properties/HintSearchAtHead.lean](Properties/HintSearchAtHead.lean) | [Proofs/HintSearchAtHead.lean](Proofs/HintSearchAtHead.lean) |
| UnboundedSearchAtV35 | [Specs/UnboundedSearchAtV35.lean](Specs/UnboundedSearchAtV35.lean) | [Properties/UnboundedSearchAtV35.lean](Properties/UnboundedSearchAtV35.lean) | [Proofs/UnboundedSearchAtV35.lean](Proofs/UnboundedSearchAtV35.lean) |
| PaddingAtHead | [Specs/PaddingAtHead.lean](Specs/PaddingAtHead.lean) | [Properties/PaddingAtHead.lean](Properties/PaddingAtHead.lean) | [Proofs/PaddingAtHead.lean](Proofs/PaddingAtHead.lean) |

- **Model, Reaches.** The list state (`Tree`, `Valid`, `InsertGuard`, `insert`) and its
  projection `toAbs` into `../IndexedMerkleTree/`. Guarded runs are `GuardedEvolution`s
  (`run_isGuardedEvolution`).
- **HintSearch.** The canonical v35 walk and checks (`WalkExitsAtV35`, `InsertChecksAtV35`),
  and the fuel-generic search lemmas. `maxLowIndexSearchAttempts` and
  `HonestInsertRevertsAtDeployedFuel` are the pin's five-hop bound, kept as the comparison.
- **TreeRoot, TreeRootStrong, PublishedRootCommits.** The root, the verifiers, and the located
  break `TreeRootBreak`, for every padding constant. The repaired `…OrBreak` forms take no hash
  premise.
- **RunHeight, CachedRoot.** `FullMerkle`'s counters and its whole storage, moved by the
  transcribed library calls. `root()` is the published fold at the run's own height.
  `cSetupPad`/`CReachesPad` is `setup` with the padding as a parameter. `cSetup` is its
  instance at the pin's `hashLeaf({0,0,0})`.
- **InitOnce.** Callers, `initL2()` and the predeploy, shared with the v35 machines. Its own
  `TxStep` uses the pin's five-hop search. `PinTxRunIsTxRunAtHead` and
  `TxRunAtHeadIsRelabelledTxRun` relate it to the v35 machine, and the `…AtHead` results are
  derived through them.
- **HintSearchAtHead, UnboundedSearchAtV35.** The v35 insert on the list state.
  `CTxRunAtV35ProjectsToTxRunAtHead` and `InsertCallV35IffChecksAtV35` tie them to the
  canonical machine.
- **PaddingAtHead.** `b17415d20`'s hashing at the byte level. Every `TreeRootBreak` is a named
  keccak collision (`KeccakBreakAtHeadIsTreeRootBreak`, `TreeRootBreakAtHeadIsKeccakCollision`).

**Not covered:**
- keccak collision resistance itself;
- gas;
- that the leaf hook (`INTEROP_COMMITMENT_LEAF_HOOK`) does not write the tree's storage;
- proxy upgrades by the complex upgrader (`OPS-CONFIG`);
- that compiled code executes the transcription (obligation O7, `../../Refinement.lean`).

`PathAccepts` omits the `_pathLength >= 256` revert, so the model accepts more proofs than the
source does.

## History

[History/](History/) is the record of the interop pin `c67894b9`, not a claim about `b17415d20`.
At that pin, `setup` padded empty slots with `hashLeaf({0,0,0})`. `verifyNonInclusion` bounds
the low-leaf index only by `2^pathLength` (`Merkle.sol:133-140`), not by the leaf count, so a
forged absence proof was accepted against the stored root (finding H2, high severity; fixed by
`78e14b3bc`). The record is in `History.Properties.CThreeLeafWitness`,
`PaddingCollisionRefundsDeliveredLeg`, `PaddingForgeryAtOwnHeight` and
`PaddingCountermodel…`. The index bound is unchanged at `b17415d20`. There, presenting a leaf at
an empty slot requires `hashLeaf(ℓ) = IMT_EMPTY_LEAF_HASH` (`CTxRunAtV35EmptySlotLocatesPadding`,
`PaddingHitAtHeadIffEmptyLeafCollision`).
