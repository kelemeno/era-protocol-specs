# IndexedMerkleTree

Source: `contracts/common/libraries/IndexedMerkleTree.sol` in the pinned
era-contracts tree. This folder owns the library's abstract IMT theory even
though the proofs are mathematical and shared by other contracts.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| InsertGuard | [Specs/InsertGuard.lean](Specs/InsertGuard.lean) | [Properties/InsertGuard.lean](Properties/InsertGuard.lean) | [Proofs/InsertGuard.lean](Proofs/InsertGuard.lean) |
| ResetAndZero | [Specs/ResetAndZero.lean](Specs/ResetAndZero.lean) | [Properties/ResetAndZero.lean](Properties/ResetAndZero.lean) | [Proofs/ResetAndZero.lean](Proofs/ResetAndZero.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| UnboundedSearchAtV35 | [Specs/UnboundedSearchAtV35.lean](Specs/UnboundedSearchAtV35.lean) | [Properties/UnboundedSearchAtV35.lean](Properties/UnboundedSearchAtV35.lean) | [Proofs/UnboundedSearchAtV35.lean](Proofs/UnboundedSearchAtV35.lean) |

`UnboundedSearchAtV35` is pinned to `draft/v0.35.0` at `b17415d20` (the cited files are
byte-identical at `d9f6789`), where `insert`'s low-leaf walk has no hop bound
(`IndexedMerkleTree.sol:90-93`; `MAX_LOW_INDEX_SEARCH_ATTEMPTS` was removed in `b8cc61203`). It
models the walk as a relation over the abstract leaf set, with no gas and indices erased. No
hash premise.
- The walk exits in the weak window with no invariant (`WalkSoundV35`); on a sound set it exits
  from every leaf (`WalkTerminatesV35`), is unique (`WalkDeterministicV35`), takes exactly as many
  hops as there are keys strictly between the hint's key and the value (`WalkLengthIsGapV35`), and
  for an absent value ends at the one straddling leaf whatever the hint (`WalkFindsLowLeafV35`,
  `WalkHintIndependentV35`).
- A successful v35 insert is a `GuardedEvolution` step (`InsertV35IsGuardedStep`), so the
  history capstones hold of v35 histories (`RunV35IsEvolution`, `ReclaimableIffAbsentV35`,
  `DeliveredAvailableForeverV35`, `DeliveryExactlyOnceV35`; reclaim witnesses are leaves of the
  set). On a sound set its result does not depend on the hint (`InsertV35HintIndependent`).
- Liveness: on a sound set an insert of a nonzero absent value succeeds from every member hint
  below it (`HonestInsertNeverSearchRevertsV35`); along a history the key-0 leaf always works
  and a hint key that passed the checks once still does (`SentinelHintAlwaysWorksV35`,
  `OnceValidHintStaysValidV35`, the claim of `protocol-docs/message-root.md:95` read through
  keys).
- A sound leaf set is determined by its keys, so the inserted values determine every leaf set
  of a history (`SoundLeafSetDeterminedByKeysV35`, `ValuesDetermineTreeV35`).
- The pin's counted loop is the walk cut off at the bound and reverts exactly when the gap
  exceeds it (`BoundedWalkIsTruncatedWalkV35`, `BoundedWalkRevertsIffGapExceedsV35`);
  `PinBoundRevertsWhereV35InsertsV35` is the six-hop insert the pin's bound of five reverts.
- Witnesses: `WalkPremisesSatisfiableV35`, `InsertOrderForgottenV35`, `RunV35Satisfiable`,
  `RunV35PremisesMetV35`. The lift to the indexed state is
  `../L2InteropCommitmentTree/`'s topic of the same name.

The deployed wrapper's indexed storage/search model is
`../L2InteropCommitmentTree/Specs/Model.lean`, which projects into this abstract theory.
Hash-tree behavior and proof soundness live under `../FullMerkle/` and `../Merkle/`.
These results do not alone establish compiled storage/root correspondence,
authorized callers, or the wrapper's one-time initialization guard; see
`../../Refinement.lean`.
