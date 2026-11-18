# IndexedMerkleTree

Source: `contracts/common/libraries/IndexedMerkleTree.sol` in the pinned
era-contracts tree. This folder owns the library's abstract IMT theory even
though the proofs are mathematical and shared by other contracts.
Topics named `…AtHead` or `…AtV35` are pinned to a later era-contracts commit instead, as
their sections say.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas. Some spec modules
only import a shared specification when the topic needs no additional definitions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| InsertGuard | [Specs/InsertGuard.lean](Specs/InsertGuard.lean) | [Properties/InsertGuard.lean](Properties/InsertGuard.lean) | [Proofs/InsertGuard.lean](Proofs/InsertGuard.lean) |
| ResetAndZero | [Specs/ResetAndZero.lean](Specs/ResetAndZero.lean) | [Properties/ResetAndZero.lean](Properties/ResetAndZero.lean) | [Proofs/ResetAndZero.lean](Proofs/ResetAndZero.lean) |
| Model | [Specs/Model.lean](Specs/Model.lean) | [Properties/Model.lean](Properties/Model.lean) | [Proofs/Model.lean](Proofs/Model.lean) |
| ReclaimGateFaithful | [Specs/ReclaimGateFaithful.lean](Specs/ReclaimGateFaithful.lean) | [Properties/ReclaimGateFaithful.lean](Properties/ReclaimGateFaithful.lean) | [Proofs/ReclaimGateFaithful.lean](Proofs/ReclaimGateFaithful.lean) |

`ReclaimGateFaithful` (c67894b9, and b17415d20 for the dedicated padding constant) reads the
genesis-rooted reclaim capstones of `Model` with the deployed absence check
`verifyNonInclusion` (`DeployedGate`) in place of their member-leaf hypothesis, along runs
from `setup` at each step's own `_height`. No hash premise except two pinned inequalities:
`DedicatedPadding` (`hashLeaf({0,0,0}) ≠ z0`) and, in one statement, `hl ℓ ≠ z0` for the
presented leaf.
- At the pin's padding `hashLeaf({0,0,0})`, for every hash: on every reached snapshot whose
  leaf count is not a power of two, the zero leaf at the first empty index is accepted for
  every nonzero value, delivered ones included, and its located break is exactly `paddingHit`
  (`PinnedGateAcceptsEveryValueOffPowersOfTwo`, `ReachedBelowCapacityIffNotPowerOfTwo`). So
  both readings are false (`PinnedReclaimDichotomyReadingFails`,
  `PinnedDeliveryFinalityReadingFails`) on a run meeting the capstones' hypotheses
  (`PinnedCounterexampleMeetsCapstoneHypotheses`).
- Restricted to submissions with no located `TreeRootBreak` (`BreakFreeGate`), both capstones
  hold at every padding constant (`BreakFreeGateDichotomy`, `BreakFreeGateMatchesMemberGate`,
  `BreakFreeDeliveryFinality`), and every absent nonzero value passes the deployed check
  (`DeployedGateLiveness`).
- On every reached snapshot, at every padding constant, an absence proof accepted for a
  delivered value carries a `wrongLength`, `pathCollision` or `leafCollision` break, or is a
  padding hit at the published height (`DeliveredRefundLocatesCollisionOrPaddingHit`). At full
  snapshots, or for a presented leaf that does not hash to the padding constant, only the
  first three remain (`FullSnapshotRefundOfDeliveredNeedsCollision`,
  `DedicatedPaddingRefundOfDeliveredNeedsCollision`). Under `DedicatedPadding`, the pin's
  submission shape needs a `PathCollision` (`DedicatedPaddingZeroLeafNeedsPathCollision`).
- With the padding constant a parameter of `setup` (b17415d20 passes `IMT_EMPTY_LEAF_HASH`),
  the transcribed `root()` is the published root on every reached state
  (`StoredRootAtPaddingIsPublished`, `ReachedStatesLiftAtPadding`, `SetupAtPaddingIsPinnedSetup`).
- The dedicated constant alone does not make either reading hold for every hash: both fail
  under the toy hashes at padding `1` (`DedicatedPaddingReadingsFailUnderToyHashes`).
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
