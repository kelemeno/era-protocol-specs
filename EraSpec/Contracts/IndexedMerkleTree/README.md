# IndexedMerkleTree

Source: `l1-contracts/contracts/common/libraries/IndexedMerkleTree.sol` at era-contracts
`draft/v0.35.0` `b17415d20`. The model is the abstract sorted leaf set `IMTAbstract`
(`Specs/Model.lean`: leaves `⟨key, nextKey⟩` with indices erased), with the v35 unbounded walk
(`Specs/UnboundedSearchAtV35.lean`). The indexed storage model of the deployed wrapper is
`../L2InteropCommitmentTree/`, which projects into this one.

## Headline guarantees

A *v35 history* (`RunV35`) is a sequence of leaf sets in which each step changes nothing or is a
successful v35 `insert`: the five checks, then the unbounded walk from the hint. The genesis set
is `{⟨0, 0⟩}`, the sentinel that `setup` writes. Gas is not modelled. No statement takes a hash
premise.

- `IMTAbstract.Properties.ReclaimableIffAbsentV35`: on every snapshot of a v35 history, a
  nonzero value is straddled by a leaf of the set exactly when it is not a key. Premises: the
  history is a v35 history; it starts at genesis; the value is nonzero.
- `IMTAbstract.Properties.DeliveredAvailableForeverV35`: a value that is a key at a snapshot
  settled by the deadline stays a key, and no leaf straddles it at any snapshot whose successor
  settles after the deadline. Premises: a v35 history from genesis; settlement times that never
  decrease; the first snapshot settled at or before the deadline.
- `IMTAbstract.Properties.DeliveryExactlyOnceV35`: a nonzero key entered the set at exactly one
  earlier step. Premises: a v35 history from genesis; the value is nonzero.
- `IMTAbstract.Properties.HonestInsertNeverSearchRevertsV35`: an insert of an absent value
  succeeds from every member hint below it. The walk takes exactly as many hops as there are
  keys strictly between the hint and the value. Premises: the leaf set is sound (sorted links,
  unique keys, no dangling link); the value is nonzero and not a key; the hint is a member whose
  key is below the value.
- `IMTAbstract.ReclaimGateFaithful.Properties.DeliveredRefundLocatesCollisionOrPaddingHit`: an
  absence proof that `verifyNonInclusion` accepts for a present value carries one of these:
  a wrong path length, a node-hash collision on the path, a leaf-hash collision with the stored
  leaf, or a presented leaf whose hash equals the padding constant at an empty index. Premises:
  the state is reached from `setup` by guarded inserts; the root is the fold over the leaf hashes
  at the state's own height (obligation O7). The statement holds for every node hash, leaf hash
  and padding constant.
- `IMTAbstract.ReclaimGateFaithful.Properties.BreakFreeGateDichotomy` and `DeployedGateLiveness`:
  along every run from `setup`, a nonzero value passes `verifyNonInclusion` with no located
  break exactly when it is absent, and every absent nonzero value passes. Premises: a run from
  `setup`; the value is nonzero. The statements hold for every node hash, leaf hash and padding
  constant.

**Witnesses:** `RunV35Satisfiable`, `RunV35PremisesMetV35`, `WalkPremisesSatisfiableV35`,
`BreakFreeGateRunWitness`, `FinalityPremisesWitness`, `DedicatedPaddingPremiseWitness`,
`ReachedSnapshotShapesWitness`, `StoredRootAtPaddingWitness`, `genesisInsertHistory_guarded`.

**Countermodels**, each showing that a premise or a stronger reading fails:
- the membership premise of the exclusivity theorems: `forged_padding_witness_breaks_exclusivity`,
  `ModelStrong.Properties.padding_leaf_forges_every_delivered`;
- the insert guard: `InsertGuard`'s `weak_window_without_dedup_breaks_keyInj` and
  `below_window_insert_breaks_windowPos`;
- reset: `ResetAndZero`'s `resetHistory_*`;
- the deployed gate: `DedicatedPaddingReadingsFailUnderToyHashes`, `ToyEmptyIndexRefundWitness`
  and `ToyFullSnapshotRefundWitness`;
- the pin's hop bound: `PinBoundRevertsWhereV35InsertsV35`.

## Topics

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| UnboundedSearchAtV35 | [Specs/UnboundedSearchAtV35.lean](Specs/UnboundedSearchAtV35.lean) | [Properties/UnboundedSearchAtV35.lean](Properties/UnboundedSearchAtV35.lean) | [Proofs/UnboundedSearchAtV35.lean](Proofs/UnboundedSearchAtV35.lean) |
| ReclaimGateFaithful | [Specs/ReclaimGateFaithful.lean](Specs/ReclaimGateFaithful.lean) | [Properties/ReclaimGateFaithful.lean](Properties/ReclaimGateFaithful.lean) | [Proofs/ReclaimGateFaithful.lean](Proofs/ReclaimGateFaithful.lean) |
| InsertGuard | [Specs/InsertGuard.lean](Specs/InsertGuard.lean) | [Properties/InsertGuard.lean](Properties/InsertGuard.lean) | [Proofs/InsertGuard.lean](Proofs/InsertGuard.lean) |
| ModelStrong | [Specs/ModelStrong.lean](Specs/ModelStrong.lean) | [Properties/ModelStrong.lean](Properties/ModelStrong.lean) | [Proofs/ModelStrong.lean](Proofs/ModelStrong.lean) |
| ResetAndZero | [Specs/ResetAndZero.lean](Specs/ResetAndZero.lean) | [Properties/ResetAndZero.lean](Properties/ResetAndZero.lean) | [Proofs/ResetAndZero.lean](Proofs/ResetAndZero.lean) |
| ResetAndZeroStrong | [Specs/ResetAndZeroStrong.lean](Specs/ResetAndZeroStrong.lean) | [Properties/ResetAndZeroStrong.lean](Properties/ResetAndZeroStrong.lean) | [Proofs/ResetAndZeroStrong.lean](Proofs/ResetAndZeroStrong.lean) |

- **Model** holds the order theory: `GapSound`, `SoundState`, `imtInsert`, `Evolution`,
  `GuardedEvolution`, and the capstones over histories (`guardedEvolution_*`). A v35 history
  is a `GuardedEvolution` (`RunV35IsGuardedEvolution`), so they apply to v35.
- **UnboundedSearchAtV35** adds the v35 walk (`WalkV35`) and insert (`InsertV35`) on the same
  state. It also models the pin's counted loop (`BoundedWalkV35`) for comparison.
- **ReclaimGateFaithful** reads the reclaim capstones with the deployed absence check
  (`DeployedGate`) in place of their member-leaf premise. It works over the canonical storage
  model with the padding constant as a parameter (`cSetupPad`/`CReachesPad` in
  `../L2InteropCommitmentTree/Specs/CachedRoot.lean`).
- **InsertGuard, ModelStrong, ResetAndZero(Strong)** show that each guard conjunct, the
  membership premise, the one-time setup and the zero sentinel are each needed.

## History

[History/](History/) is the record of the interop pin `c67894b9`, not a claim about `b17415d20`.
At that pin, empty slots were padded with `hashLeaf({0,0,0})` (finding H2). The `PinnedGate`
topic shows that at that padding the deployed check accepts a reclaim for every nonzero value on
reached snapshots whose leaf count is not a power of two, so both capstone readings fail
(`IMTAbstract.ReclaimGateFaithful.History.Properties.Pinned…`).

Hash-tree behaviour and proof soundness are in `../FullMerkle/` and `../Merkle/`. That compiled
code implements these models is an obligation in `../../Refinement.lean`.
