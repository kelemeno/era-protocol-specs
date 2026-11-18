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
- `LocalHonesty.lean`: the center → manager → commitment-tree authorization chain
  supplying the honest-insertion assumption.
- `NoTheft.lean`: abstract per-leg commitment/reclaim exclusivity and provenance,
  with the caller's assumptions and limits stated explicitly.
- `FlowAtomicity.lean`: commitment-evidence persistence and per-leg outcomes;
  it does not by itself establish application execution or uniform flow outcomes.
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

The illustrative prepared application is under `../Examples/BurnMintBridge/`.
The actual source/compiled implementation obligations are in `../Refinement.lean`.
