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
- [BatchCounters](BatchCounters/README.md) (`b17415d20`, namespace `Contracts.BatchCounters`):
  each diamond's `totalBatchesExecuted` against its layer's `MessageRootBase` counter
  `currentChainBatchNumber`. With migrations disabled, every chain of a layer reachable from the
  empty one has the two equal (`ReachableHeadHubsSynced`). On a layer satisfying the layer
  invariant `HubInv`, an execute that passes the executor's own modelled checks with nonzero logs
  roots exists iff they are equal (`ExecuteEnabledIffSynced`); with migrations disabled a chain
  whose counters disagree never executes again (`DriftPersistsAtHead`), for example one registered
  before v31 whose v31 counter was never saved (`LegacyUnsavedChainIsWedged`). Batch roots are
  write-once (`BatchRootsWriteOnce`). Across the (disabled) migration path, for two copies of one
  chain and an honest at-most-once channel, along every run from a state satisfying `TwoInv` (by
  `TwoInvInit`, any state with both layers satisfying `HubInv`, the chain synced and settling on
  L1, no settlement-layer diamond for it and nothing in flight): exactly one copy settles or a
  migration is in flight (`ExactlyOneCopySettles`), the batch numbers executed on both layers are
  consecutive (`ExecutedLogContiguous`), and neither copy's executed count goes down
  (`CopiesNeverGoBack`). Countermodel: a mint from a stale commitment lowers the executed count
  (`StaleMintRewritesHistory`). No hash premise.
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

- [L2BridgeConfig](L2BridgeConfig/README.md): the L1 chain id and base-token asset id
  copies held by the L2 built-ins (`b17415d20`). Genesis establishes one value for each,
  every admissible step keeps it, a default upgrade succeeds only with the stored ids, and
  only the upgrader's transactions write the scalar words. Countermodels: without either of
  the vault's freezes, or with the router's `updateL2` called outside the helper, the copies
  diverge; a default upgrade with the stored ids may rewrite the base token's origin data.
- [PriorityRequests](PriorityRequests/README.md): every L1 entry that appends a priority
  operation (`draft/v0.35.0` at `b17415d20`). A relay leaf forwards the hash pushed just before it
  in the same transaction, service leaves carry one of three fixed calls, and no user request
  yields either privileged sender, under stated account premises and genuine Bridgehub roles; a
  redirected role breaks the service purposes.
- [InteropPeerRegistry](InteropPeerRegistry/README.md) (`b17415d20`): each chain's
  `L2Bridgehub.isPeerAllowed` equals `ChainRegistrationSender.interopPeerAllowed` once the
  pair's last executed queue entry succeeded (or every service entry did), with a deployed-model
  desync after a failed service entry, and a countermodel for out-of-order execution; every chain's `baseTokenAssetId[p]` is `0` or
  L1's, and L1's never changes once set, across the (disabled) migration path, where a settled
  chain's entry stays L1's. No hash premise.
- [L1WithdrawalProvenance](L1WithdrawalProvenance/README.md) (`b17415d20`): composition of
  `Contracts/L1InteropHandler` `WithdrawalGate` (the L1 handler) with `Contracts/L1Messenger`
  `SenderKeying` (each source chain's modelled L2→L1 output).

- [NativeValueLegs](NativeValueLegs/README.md): native-value atomic legs at head `b17415d20`. On
  the source chain, a successful refund moves exactly the leg's collected value, to its sender, in
  the destination's base-token asset, and is the negation of the send's collection
  (`ClaimReturnsCollected`, `RefundIsCollectionInverse`); along runs each refund is bound to the
  send that committed its leg, up to a keccak collision on two named byte strings
  (`EveryClaimRefundsItsSenderOrCollision`; the amount is stated except for a claim that is the
  tracker's first registration of a token native to the source chain). Countermodel: an indirect
  call carrying value. The frame premise on router-call recovery reduces, through the vault's own
  refund at head, to handlers other than the vault (`HeadRouterRecoveryFramesOthers`,
  `HeadCodeFrames`).

- [CtmRecord](CtmRecord/README.md) (`b17415d20`): across L1 and settlement layers, the
  Bridgehub's `chainTypeManager[c]` agrees with the CTM the chain's diamond obeys along every
  run whose CTM asset registrations keep each layer's asset maps a partial bijection
  (`CtmRecordAgreesWithDiamond`). On those runs the CTM whose version check a migration step
  runs, and the CTM whose pause gates it (for a burn, whenever its asset id is nonzero), is the
  CTM that can upgrade or freeze the chain, and a chain burned on L1 towards a settlement layer
  with an L1 diamond goes to one whose L1 diamond is under the chain's own CTM. Countermodels
  without that premise; a repaired mint, and the exact per-mint condition for keeping the
  agreement; the premise at the tracker's level.

The illustrative prepared application is under `../Examples/BurnMintBridge/`.
The actual source/compiled implementation obligations are in `../Refinement.lean`.
