# AtomicInteropProof

Source: `l1-contracts/contracts/atomic-interop/libraries/AtomicInteropProof.sol` at era-contracts
`draft/v0.35.0` `b17415d20`. The library authenticates a claimed IMT root against an imported
interop root (`_authenticateRoot`) and checks a leg's commit value present in it (`verifyInclusion`)
or absent from it (`verifyTimeoutAbsence`, with the last-batch check `_verifyLastBatchInRoot`).
`History/` is the record of the extraction pin `c67894b9`, not a claim about `b17415d20`.

## Headline guarantees

Each holds for every parser and hash function the model takes as a parameter unless it says
otherwise; none takes a global hash-injectivity premise.

| Headline | Premises, in plain words |
|---|---|
| `AttackVectors.AuthenticateRootAtV35.Properties.AuthenticateRootSoundV35` | `_authenticateRoot` (word-level transcription at `b17415d20`) accepted the claimed root for `(src, batch)` at some leaf index; the imported root at the returned coordinates is the settlement layer's shared tree (`SharedTreeBacking`, `PROTO-SHARED-ROOT`); every shared-tree slot registered to `src` was last written with the root of `src`'s chain tree; that tree's entries are batch leaves of height-3 chain batch roots (`ChainTreeEntries`). Conclusion: the claimed root is that leaf of the chain batch root of an entry with the proof's batch number and the returned timestamp, or a located `AuthBreak` / `SLHopBreak`. |
| `AttackVectors.AuthenticateRootAtV35.Properties.EndBranchSoundV35` | The same premises, the source chain's tree fits its height, and the end branch of `verifyTimeoutAbsence` passed up to and including `_verifyLastBatchInRoot` (leaf 3). Conclusion: the claimed root is the IMT end root of the source chain's LAST entry in the imported root, or a located break. |
| `AttackVectors.AuthenticateRootAtV35.Properties.EndBranchTwoHopLastLeafOrBreakV35` | The end branch passed up to the last-batch check; `SharedTreeBacking`; the source chain's tree fits its height; every slot registered to `src` holds that tree's root. No premise on either path. Conclusion: the batch leaf is the tree's last leaf at the tree's height, or a located `LastLeafAnyLengthBreak` / `SLHopBreak`. |
| `AttackVectors.AuthenticateRootAtV35.Properties.HopReadTotalAfterAuthV35` | `_authenticateRoot` accepted the proof. Conclusion: `readAggregationHopPath` does not revert on it, so its final-node revert is unreachable from `verifyTimeoutAbsence`. |
| `MerkleSpec.LastLeafFaithful.Properties.AcceptedLastLeafAnyLengthOrBreak` | The chain tree fits its height; the submitted batch-leaf path, of any length and mask, passes the deployed checks (mask in range, the zero check over the submitted levels) and its walk reaches the chain tree's root (on chain the outer hop's conclusion, modelled as a premise here). Conclusion: the right length, the last leaf and its entry, or a located `LastLeafAnyLengthBreak`. |
| `AttackVectors.StaleSnapshotFaithful.Properties.StaleWitnessNotRedeemableOrBreak` | A commitment-tree run from `setup` (any padding constant), monotone settlement times, an absence proof accepted by `verifyNonInclusion` against snapshot `j`'s root (any index, any length), and the abstract deadline pin `D < t (j+1)` (`StaleSnapshot`'s model of the deadline gate, not a comparison the deployed gate makes; the deployed branches are mapped onto it by `StaleSnapshotBranches`). Conclusion: the value is in no on-time snapshot, or a located `TreeRootBreak` on the submitted proof. |
| `AttackVectors.StaleSnapshotFaithful.Properties.StaleWitnessNotRedeemableOrCollision` | As above, and the presented low leaf does not hash to the padding constant (at `b17415d20` the padding is `IMT_EMPTY_LEAF_HASH`). Conclusion: no on-time snapshot holds the value, or a genuine collision on the submitted proof (`HeightBreak`, `PathCollision`, or a leaf-hash collision at an occupied slot). |
| `AttackVectors.StaleSnapshotBranches.Properties.BeginBranchNotRedeemable` | An abstract batch history of IMT snapshots that evolves by guarded inserts from a sound base, monotone batch times, `begin(n+1) = end(n)` (`PROTO-BATCH-SNAPSHOT`, not checked on chain), and a begin-branch timeout (batch late, root after the deadline) whose absence witness is a genuine leaf of the begin snapshot. Conclusion: the value is in no on-time end snapshot. |
| `AttackVectors.StaleSnapshotBranches.Properties.EndBranchNotRedeemable` | The same history without monotone times, every batch numbered after the proven one settling no earlier than the root (`LaterBatchesLate`, from `PROTO-AGGREGATES` at the root's last batch), and an end-branch timeout whose absence witness is a genuine leaf of the end snapshot. Conclusion: the value is in no on-time end snapshot. |
| `AttackVectors.ProofPolarityFaithful.Properties.UpgradeExcludesMisdeclared` | Every chain's tree was written only by the `b17415d20` `append`, which requires the leg's declared chain to be the committing chain, starting from empty trees; a commit value's real source chain and declared chain are abstract functions of it. Conclusion: every committed value's declared chain is its real source chain. |

Witnesses: `EndBranchV35Satisfiable` (all `AuthenticateRootAtV35` headlines),
`AcceptedLastLeafNoHeightBreakOnSatisfiable`, `StaleWitnessOrCollisionSatisfiable`,
`BeginBranchNotRedeemableSatisfiable`, `EndBranchNotRedeemableSatisfiable`,
`UpgradeFinalitySatisfiable`. Countermodels: `WrongLengthLastLeafAccepted`,
`PaddedIndexLastLeafAccepted` (both pass every check the contract performs, excluded only by hash
domain separation), `BeginBranchNeedsBeginIsPrevEnd`, `EndBranchNeedsLaterBatchesLate`,
`PinDoesNotMakeSnapshotOnTime`, `BeginBranchPinMayBeLate`.

## Topics

The library is modelled at four layers, refinements of each other rather than competing models
(see `handoff/2026-11-19/consolidation/atomic-proof.md`):

1. **Proof words** — `AuthenticateRootAtV35`: `_authenticateRoot`, `_getProofData`, the L2
   verifier's one recursive hop, `readSettlementLayerReference`, `readAggregationHopPath` and
   `_verifyLastBatchInRoot`, transcribed at `b17415d20`. Canonical.
2. **The batch-leaf path** — `LastLeafFaithful` (length and mask the prover's) over `LastLeaf`
   (the hash-level last-leaf argument, `PinnedBreak`). `LastBatchCheckOnVerifiedWalkV35` joins it to
   layer 1. `LastLeaf.NotHashBreak` and `AcceptedLastLeafOrBreak` take global pair-injectivity and
   are vacuous (`ASSUMPTIONS.md`).
3. **Index level** — `LastBatchInRoot` (`RightEmpty`: the zero check as an index fact, hashes
   idealised) and `LastBatchInRootOffset` (leaf position and batch number kept apart; first pushed
   batch `f`, `PROTO-CONTIGUOUS-PUSH`).
4. **Batch histories and gates** — `TimeoutSoundness` and `TimeoutSoundnessStrong` (value sets,
   the branch flag and the authenticated leaf), `StaleSnapshot`, `Timestamps` and
   `StaleSnapshotBranches` (`IMTAbstract` snapshots), `StaleSnapshotFaithful` (commitment-tree runs
   and the deployed absence verifier), `ProofPolarity`, `ProofPolarityStrong` and
   `ProofPolarityFaithful` (the two source-chain checks of `AtomicFlowManager`).
   `HonestInsertionAgrees`, `BeginIsPrevEndProjects` and `OutsideRootLateIffNat` relate the
   duplicated premises of these topics.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| AuthenticateRootAtV35 | [Specs](Specs/AuthenticateRootAtV35.lean) | [Properties](Properties/AuthenticateRootAtV35.lean) | [Proofs](Proofs/AuthenticateRootAtV35.lean) |
| LastLeaf | [Specs](Specs/LastLeaf.lean) | [Properties](Properties/LastLeaf.lean) | [Proofs](Proofs/LastLeaf.lean) |
| LastLeafFaithful | [Specs](Specs/LastLeafFaithful.lean) | [Properties](Properties/LastLeafFaithful.lean) | [Proofs](Proofs/LastLeafFaithful.lean) |
| LastBatchInRoot | [Specs](Specs/LastBatchInRoot.lean) | [Properties](Properties/LastBatchInRoot.lean) | [Proofs](Proofs/LastBatchInRoot.lean) |
| LastBatchInRootOffset | [Specs](Specs/LastBatchInRootOffset.lean) | [Properties](Properties/LastBatchInRootOffset.lean) | [Proofs](Proofs/LastBatchInRootOffset.lean) |
| TimeoutSoundness | [Specs](Specs/TimeoutSoundness.lean) | [Properties](Properties/TimeoutSoundness.lean) | [Proofs](Proofs/TimeoutSoundness.lean) |
| TimeoutSoundnessStrong | [Specs](Specs/TimeoutSoundnessStrong.lean) | [Properties](Properties/TimeoutSoundnessStrong.lean) | [Proofs](Proofs/TimeoutSoundnessStrong.lean) |
| StaleSnapshot | [Specs](Specs/StaleSnapshot.lean) | [Properties](Properties/StaleSnapshot.lean) | [Proofs](Proofs/StaleSnapshot.lean) |
| Timestamps | [Specs](Specs/Timestamps.lean) | [Properties](Properties/Timestamps.lean) | [Proofs](Proofs/Timestamps.lean) |
| StaleSnapshotBranches | [Specs](Specs/StaleSnapshotBranches.lean) | [Properties](Properties/StaleSnapshotBranches.lean) | [Proofs](Proofs/StaleSnapshotBranches.lean) |
| StaleSnapshotFaithful | [Specs](Specs/StaleSnapshotFaithful.lean) | [Properties](Properties/StaleSnapshotFaithful.lean) | [Proofs](Proofs/StaleSnapshotFaithful.lean) |
| ProofPolarity | [Specs](Specs/ProofPolarity.lean) | [Properties](Properties/ProofPolarity.lean) | [Proofs](Proofs/ProofPolarity.lean) |
| ProofPolarityStrong | [Specs](Specs/ProofPolarityStrong.lean) | [Properties](Properties/ProofPolarityStrong.lean) | [Proofs](Proofs/ProofPolarityStrong.lean) |
| ProofPolarityFaithful | [Specs](Specs/ProofPolarityFaithful.lean) | [Properties](Properties/ProofPolarityFaithful.lean) | [Proofs](Proofs/ProofPolarityFaithful.lean) |

Older topics carry "Correction (<topic>)" notes pointing to the later topic that restates them
against the deployed code: `LastBatchInRootOffset` and `LastLeafFaithful` for `LastBatchInRoot` and
`LastLeaf`; `StaleSnapshotBranches` and `StaleSnapshotFaithful` for `StaleSnapshot` and
`Timestamps`; `ProofPolarityFaithful` for `ProofPolarity` and `ProofPolarityStrong`. The composed
timeout statements over the protocol model are in `Protocol/InteropAtomicity` (`Contracts.Timeout`).

## History (`c67894b9`)

`History/` records the extraction pin `c67894b9`. It is not a claim about `b17415d20`.

* `History/*/ProofPolarityFaithful.lean` (H1): the pinned `append` did not bind a leg's declared
  chain to the committing chain, and the misdeclared double mint it reaches
  (`PinnedMisdeclaredDoubleMint`, `RefundNotBlockedWhenPinnedToDeclared`, `PinnedReachHonest`).
  At `b17415d20` `append` binds them (`AtomicFlowManager.sol:140-146`).
* `History/*/StaleSnapshotFaithful.lean` (H2): with the pinned padding constant
  `hashLeaf({0,0,0})`, an accepted absence proof for a delivered leg
  (`PaddingReclaimRedeemsDeliveredLeg`). At `b17415d20` the tree pads with `IMT_EMPTY_LEAF_HASH`.
* `History/*/AuthenticateRootAtV35.lean`: the pin's `_authenticateRoot` and
  `readAggregationHopPath`, and the two statements that the `b17415d20` refactor is exact
  (`AuthenticateRootRefactorExactV35`, `EndBranchRefactorExactV35`).

These modules do not prove the compiled verifier, authenticate imported roots, or establish
settlement clocks. The cross-chain binding model is `../../Protocol/Spec.lean`; the reference
application composition is `../../Examples/BurnMintBridge/ProtocolComposition.lean`.
