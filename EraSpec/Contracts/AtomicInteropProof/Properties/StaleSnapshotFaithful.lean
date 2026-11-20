import EraSpec.Contracts.AtomicInteropProof.Specs.StaleSnapshotFaithful

/-!
# Properties: stale-snapshot reclaim against the deployed absence verifier

Statements over `../Specs/StaleSnapshotFaithful.lean`.  Proofs:
`../Proofs/StaleSnapshotFaithful.lean`.

* `StaleWitnessNotRedeemableOrBreak` and `PinningGateRejectsStaleWitnessOrBreak` are
  `StaleSnapshot.stale_witness_not_redeemable` / `pinning_gate_rejects_stale_witness`
  (and `Timestamps.monotone_blocks_the_attack`) for an absence proof ACCEPTED by
  `verifyNonInclusion` against a run's published root, with index and path length the
  prover's: no on-time delivery coexists with an accepted reclaim at a snapshot that
  meets the abstract pin `D < t (j+1)`, or the reclaim proof carries a located
  `TreeRootBreak`.  No hash premise.
* `StaleWitnessNotRedeemableOrCollision` is what a dedicated padding constant buys
  (`b17415d20` pads with `IMT_EMPTY_LEAF_HASH`, `IndexedMerkleTree.sol:51`): once the
  presented leaf does not hash to the padding constant, the only remaining ways out
  are genuine hash collisions (a wrong path length, a path collision, a leaf-hash
  collision), never a free padding hit.  `StaleWitnessOrCollisionSatisfiable` shows its
  premises hold, with no break, on an honest refund in a run that commits a value on
  time, at a pinned snapshot that is itself on time, so the first disjunct is not true
  of every value there.

History: at the extraction pin `c67894b9` (padding constant `hashLeaf({0,0,0})`) the original
headline's reading as a statement about the deployed absence check was false
(`History.Properties.PaddingReclaimRedeemsDeliveredLeg`, H2, break exactly `paddingHit`).

Scope.  The pin `D < t (j+1)` is `StaleSnapshot`'s abstract model of the deadline gate,
not a comparison the deployed gate makes.  The deployed branches are mapped onto it in
`AttackVectors.StaleSnapshotBranches`; that topic and this one are separate and not
composed, so "a reclaim of a delivered leg" here means the absence check plus the
abstract pin.

Readings this repair replaces, each now marked "Correction (StaleSnapshotFaithful)":

* `StaleSnapshot`'s header (in its Specs, Properties and Proofs files), its
  `stale_witness_not_redeemable` and `pinning_gate_rejects_stale_witness`, and
  `Timestamps.monotone_blocks_the_attack` and `delivered_and_reclaimed_impossible_local`
  (these four in their Properties and Proofs files);
* `Contracts.Protocol.AbsenceWitnessAt` (`MultichainGate` Specs) and the `MultichainGate`
  Properties header.

The same mark is on other readings of the absence check over a genuine leaf or under
`HashAssumptions`:

* `IndexedMerkleTree` (Specs/Model): the section docstrings on the temporal layer and on
  reclaim liveness; (Properties and Proofs/Model) the section on genesis-rooted capstones for
  real histories, `guardedEvolution_reclaimable_iff_absent` and
  `guardedEvolution_delivered_available_forever`;
* `Contracts.InteropCommitmentTree.genesis_run_reclaimable_iff_absent` (Properties and Proofs);
  `PredeployRunReclaimableIffAbsent` and the InitOnce Properties header;
* `AttackVectors.TimeoutSoundness` (TimeoutSoundnessStrong): the Properties header,
  `timeoutGate_deployed_leaf_sound`, `timeoutGate_sound_iff_not_end_flag_begin_leaf` and the
  Proofs lemma `timeoutGate_sound_of_ne`; `AttackVectors.LastBatchInRoot`:
  `end_branch_from_onchain_check` (Properties and Proofs);
* `AttackVectors.FlowAtomicity`'s header;
* `Protocol/InteropAtomicity`: the Timeout Properties header,
  `Contracts.Timeout.Properties.TimeoutMeansMissedDeadline`, `TimeoutExcludesFinality` and
  `AcceptedTimeoutMeansMissedDeadline`; the Refund Properties header,
  `Contracts.Refund.Properties.OneExecutionFreezesTheFlow`, `RefundedFlowMissedDeadline` and
  `AcceptedTimeoutForDeliveredFlowIsABreak` (and its Proofs twin);
  the Atomicity Properties header (two notes),
  `Contracts.Atomicity.Properties.WithoutDaCommittedLegIsStuck` and
  `Contracts.Atomicity.Properties.ExecutedExcludesAnyRefund` (and its Proofs twin);
* `ProofPolarity`'s set facts: the `ProofPolarityStrong` Specs module docstring and
  `CheckedAbsenceGate`; the `ProofPolarityStrong` Properties header,
  `checked_absence_gate_rejects_live_leg`, `checked_absence_gate_iff_absent`,
  `polarity_asymmetry` and `finalized_leg_passes_unchecked_absence_gate`; in the `ProofPolarity`
  Properties, `absence_at_every_wrong_chain`, `refund_blocked_when_chain_pinned` (and its Proofs
  twin) and `polarity_summary`; and the `ProofPolarityFaithful` Properties header,
  `UncheckedDoubleMintIffMisdeclared`, `FlowDoubleMintIffSomeMisdeclared` and
  `RefundBlockedIffDeclaredIsSource`;
* `Protocol/AssetBridgePreparation`: the `ResolutionEvidence` Specs section on the multichain
  gate, and `MultichainGateSound` (its Properties header bullet and docstring);
* the reference bridge's `EndBranch` (`Applications.BurnMintBridge.EndBranch`): the Specs module
  docstring and `GapWitness`; the Properties header, `BeginViaNeverFinalized`,
  `EndViaNeverFinalized`, `TimeoutViaImpliesMissing`, `CheckedEvidenceSound`,
  `CheckedBridgeNoDoublePayment`, `CheckedBridgeValueConserved`,
  `CheckedExecutionRemainsPossible`, `AcceptedEndOnTimeLocatesBreak` (and its Proofs twin),
  `PinnedBridgeNoDoublePaymentOrBreak` and `PinnedBridgeValueConservedOrBreak`.
-/

namespace AttackVectors.StaleSnapshotFaithful

open IMTAbstract MerkleSpec MerkleSpec.Verifier Contracts.InteropCommitmentTree

/-- **NO ON-TIME DELIVERY COEXISTS WITH AN ACCEPTED, DEADLINE-PINNED RECLAIM, OR THE
RECLAIM PROOF CARRIES A LOCATED BREAK.**  Along any contract run from `setup`, with
monotone settlement timestamps, if `verifyNonInclusion` accepts an absence proof for
`v` against snapshot `j`'s published root (at any height, any index, any path length)
and `j` is deadline-pinned (`D < t (j+1)`), then `v` is a key of no on-time snapshot,
or the submitted proof carries a `TreeRootBreak` against snapshot `j`'s root. -/
def Properties.StaleWitnessNotRedeemableOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree) (ht : ℕ → ℕ) (t : ℕ → UInt256)
    (D v : UInt256),
    Run R → R 0 = setup → Monotone t →
    ∀ (j : ℕ) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      D < t (j + 1) →
      NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k →
      (∀ i, t i ≤ D → v ∉ keys (toAbs (R i)))
        ∨ TreeRootBreak h z0 hl (R j) (ht j) sibs k idx ℓ

/-- **THE ATTACKER'S VIEW.**  Given a genuine on-time delivery of `v`, every absence
proof `verifyNonInclusion` accepts against a snapshot's root either fails the abstract
pin `D < t (j+1)` (`StaleSnapshot`'s model of the deadline gate; the deployed gate makes
no such comparison) or carries a located break. -/
def Properties.PinningGateRejectsStaleWitnessOrBreak : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree) (ht : ℕ → ℕ) (t : ℕ → UInt256)
    (D v : UInt256),
    Run R → R 0 = setup → Monotone t →
    ∀ i, t i ≤ D → v ∈ keys (toAbs (R i)) →
    ∀ (j : ℕ) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k →
      ¬ D < t (j + 1) ∨ TreeRootBreak h z0 hl (R j) (ht j) sibs k idx ℓ

/-- **WHAT A DEDICATED PADDING CONSTANT BUYS.**  As `StaleWitnessNotRedeemableOrBreak`, for a
presented low leaf whose hash is not the padding constant (`hl ℓ ≠ z0`; at `b17415d20` `z0 = IMT_EMPTY_LEAF_HASH`, so
this is a preimage problem; at the extraction pin `z0 = hl ⟨0,0,0⟩` and it failed for the
sentinel preimage): no coexistence, or the reclaim proof
exhibits a genuine collision — a wrong path length (`HeightBreak`), a path collision
at the tree's height, or an occupied slot holding a different leaf with the same leaf
hash. -/
def Properties.StaleWitnessNotRedeemableOrCollision : Prop :=
  ∀ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree) (ht : ℕ → ℕ) (t : ℕ → UInt256)
    (D v : UInt256),
    Run R → R 0 = setup → Monotone t →
    ∀ (j : ℕ) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
      D < t (j + 1) →
      NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k →
      hl ℓ ≠ z0 →
      (∀ i, t i ≤ D → v ∉ keys (toAbs (R i)))
        ∨ HeightBreak h z0 (leafHashes hl (R j)) sibs k (ht j) idx (hl ℓ)
        ∨ (k = ht j ∧ PathCollision h z0 (leafHashes hl (R j)) sibs 0 k idx (hl ℓ))
        ∨ (idx < (R j).leafCount ∧ (R j).leaf idx ≠ ℓ ∧ hl ((R j).leaf idx) = hl ℓ)

/-- **THE PREMISES ARE SATISFIABLE, WITH NO BREAK, AND THE FIRST DISJUNCT HAS CONTENT.**
An honest refund under a padding constant distinct from the sentinel's leaf hash (the
toy hashes, padding `1`): the run `oneInsertRun` (`setup; insert 2`) with
`oneInsertRunTime` and deadline `0`, the honest low-leaf absence proof for `1` at
snapshot `j = 1`, which meets the pin and is itself on time.  Every premise of
`StaleWitnessNotRedeemableOrCollision` holds, the proof carries no `TreeRootBreak`, and
the first disjunct holds for `1`.  A nonzero value (`2`) is a key of an on-time
snapshot, so that disjunct is false for it: on this run it is not true of every value. -/
def Properties.StaleWitnessOrCollisionSatisfiable : Prop :=
  ∃ (h : Hash) (z0 : UInt256) (hl : LeafHash) (R : ℕ → Tree) (ht : ℕ → ℕ) (t : ℕ → UInt256)
    (D v : UInt256) (j : ℕ) (ℓ : Leaf) (idx : ℕ) (sibs : ℕ → UInt256) (k : ℕ),
    Run R ∧ R 0 = setup ∧ Monotone t ∧ D < t (j + 1)
      ∧ NonInclusionAccepted h hl (root h z0 hl (R j) (ht j)) v ℓ idx sibs k
      ∧ hl ℓ ≠ z0
      ∧ ¬ TreeRootBreak h z0 hl (R j) (ht j) sibs k idx ℓ
      ∧ (∀ i, t i ≤ D → v ∉ keys (toAbs (R i)))
      ∧ t j ≤ D
      ∧ (∃ i w, t i ≤ D ∧ w ≠ 0 ∧ w ∈ keys (toAbs (R i)))

end AttackVectors.StaleSnapshotFaithful
