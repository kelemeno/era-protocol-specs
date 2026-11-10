# Cross-contract protocol properties

These results compose multiple contracts or source chains. Contract-local models
and properties remain under `../Contracts/<SolidityName>/`.

- `Spec.lean`: multi-chain source-bound refund gate, safety theorem, and an
  explicit wrong-chain absence countermodel.
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
- [InteropAtomicity](InteropAtomicity/README.md): the destination's all-legs gate
  across chains and batches (none-or-all, given data availability), the timeout
  decision derived from what `verifyTimeoutAbsence` checks, and one outcome per
  obligation over every interleaving of every chain's manager calls.

The illustrative prepared application is under `../Examples/BurnMintBridge/`.
The actual source/compiled implementation obligations are in `../Refinement.lean`.
