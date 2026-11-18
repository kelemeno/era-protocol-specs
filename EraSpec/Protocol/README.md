# Cross-contract protocol properties

These results compose multiple contracts or source chains. Contract-local models
and properties remain under `../Contracts/<SolidityName>/`.

- `MultichainGate/{Specs,Properties,Proofs}/Model.lean`: multi-chain
  source-bound refund gate (namespace `Contracts.Protocol`). Safety:
  `bound_gate_excludes_delivered`, `no_double_spend_multichain`, and
  `chains_no_double_spend` over valid per-chain contract states, for a genuine
  absence witness (at `c67894b9` the deployed check also accepts the padding
  sentinel at an empty slot: the Correction (StaleSnapshotFaithful) note in
  `MultichainGate/Properties/Model.lean`). Necessity of the
  source-chain check: `unbound_gate_refunds_delivered_leg` (abstract wrong-chain
  absence countermodel) and `chains_unbound_gate_refunds_delivered_leg` (the same
  attack realized by contract states: `setup` plus one guarded `insert`).
  Anti-vacuity: `bound_gate_not_dead`, `chains_bound_gate_iff_undelivered` (on a
  valid source-chain state and nonzero value the bound gate fires exactly on
  undelivered legs). No statement takes a hash premise; every property is an
  `abbrev Properties.x` with certificate `x`. `Spec.lean` is now a compatibility
  module that only imports the proofs module.
- `MultichainGate/{Specs,Properties,Proofs}/DeployedGate.lean` (namespace
  `Contracts.Protocol.DeployedGate`, `c67894b9`): the source-bound gate as
  `verifyNonInclusion` runs it, against the source chain's root at its own `_height`, with
  leaf, index, siblings and path length the prover's. Read as statements about this gate,
  `chains_no_double_spend` and `chains_bound_gate_iff_undelivered` fail at `c67894b9`
  (`ChainsNoDoubleSpendFailsForDeployedGate`,
  `ChainsBoundGateIffUndeliveredFailsForDeployedGate`): the padding sentinel at an empty slot
  passes for a delivered value, with located break exactly `paddingHit`
  (`PinnedPaddingDeployedGateRefundsDeliveredLeg`). With no hash premise: an accepted proof
  for a delivered value carries a located `TreeRootBreak`
  (`DeployedBoundGateExcludesDeliveredOrBreak`), a `CollisionBreak` when the presented leaf
  does not hash to the padding or the source tree is full
  (`DeployedBoundGateSeparatedPaddingNeedsCollision`,
  `DeployedBoundGateFullTreeNeedsCollision`; a reached tree is full iff its leaf count is a
  power of two, `FullAtOwnHeightIffPowerOfTwo`); the gate passes every undelivered nonzero
  value (`DeployedBoundGateLiveOnUndelivered`) and accepts exactly when `BoundGate` holds or
  an accepted proof carries a located break (`DeployedBoundGateIffAbstractOrBreak`).
  Witnesses: `DeployedGateCollisionPremisesSatisfiable`, `DeployedBoundGateLiveWitness`,
  `FullAtOwnHeightExamples`.
- `LocalHonesty.lean`: the center → manager → commitment-tree authorization chain
  supplying the honest-insertion assumption.
- `NoTheft.lean`: abstract per-leg commitment/reclaim exclusivity and provenance,
  with the caller's assumptions and limits stated explicitly.
- `FlowAtomicity.lean`: commitment-evidence persistence and per-leg outcomes;
  it does not by itself establish application execution or uniform flow outcomes.
- `FlowAtomicityPerChain/{Specs,Properties,Proofs}/Model.lean` (namespace
  `AttackVectors.FlowAtomicityPerChain`): the `FlowAtomicity` results with one commitment
  history per source chain, as the source keeps them (`LegsPresentAtLaterSnapshotsPerChain`,
  `FlowOutcomeDichotomyPerChain`), and `SharedHistoryMisreadsTwoChainFlow`: on a two-chain
  flow, the committing chain's history of one leg holds no key for the other leg and has a
  reclaim witness for it, so one shared history `S` misreads the flow. Leaf sets only, no
  hash premise.
- `DestinationCapstone.lean`: composition of destination replay, identity, and
  accounting properties, with their cross-contract assumptions exposed.
- [AssetBridgePreparation](AssetBridgePreparation/README.md): exact-burn
  composition, source supply plus pending-value conservation, and immutable
  prepared data across arbitrary preparation/spending traces. This topic uses
  separate specification, property, and proof folders; its pending ledger is
  trace bookkeeping rather than vault storage or a publication guarantee.
- [InteropAtomicity](InteropAtomicity/README.md): the destination's all-legs gate
  across chains and batches (none-or-all, given data availability), the timeout
  decision derived from what `verifyTimeoutAbsence` checks, and one outcome per
  obligation over every interleaving of every chain's manager calls. The forms
  without a hash premise end in "or a located break" (for example
  `ExecutedObligationNeverRefundedOrBreak`), and at `c67894b9` the padding forgery
  can supply the absence-proof break of the refund and timeout forms when the tree
  has an empty slot (for example `PaddingRefundOfExecutedObligationLocatesAbsenceBreak`;
  see the note at `HashAssumptions`).
- [ZKsyncOSDA](ZKsyncOSDA/README.md): at `b17415d20`, each DA validator composed with the
  committer's check of its output on ZKsync OS (namespace `Contracts.ZKsyncOSCommitterDA`): the
  exact inputs each accepts, and what that puts on L1. An acceptance through the rollup validator
  puts the pubdata in the commit calldata only under a named premise on the off-chain program
  (`RollupPubdataPublishedOrCollision`; without it, `RollupProgramPremiseLoadBearing`); the gateway
  validator needs none.

The illustrative prepared application is under `../Examples/BurnMintBridge/`.
The actual source/compiled implementation obligations are in `../Refinement.lean`.
