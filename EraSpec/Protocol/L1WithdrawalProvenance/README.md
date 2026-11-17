# L1WithdrawalProvenance

Composition of `Contracts/L1InteropHandler` `WithdrawalGate` (the L1 handler) with
`Contracts/L1Messenger` `SenderKeying` (each source chain's L2→L1 output), at era-contracts
`draft/v0.35.0` head `b17415d20`.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Provenance | [Specs/Provenance.lean](Specs/Provenance.lean) | [Properties/Provenance.lean](Properties/Provenance.lean) | [Proofs/Provenance.lean](Proofs/Provenance.lean) |

Namespace `Contracts.L1WithdrawalProvenance`.

## Joining premises

- `InclusionSoundOn` (`PROTO-EVIDENCE`): every committed verification's queried message log is in the
  output of the chain its proof names. Only the run's own accepted queries are constrained.
- `ChainsRunTheModel`: every chain id's output is that of a run from genesis of the modelled L2 code.
- `HooksAsDocumented` on every chain (the VM premise of `SenderKeying`).
- `RoundTripOn` (`SOL-ABI`): `abi.decode` inverts `abi.encode` on the dispatched bundles.

## Results

- `ProvenBundlesAreDispatchedOrCollide`: every committed verification checked the encoding of a bundle
  its chain's center dispatched to L1 (one call, from `L2_ASSET_ROUTER_ADDR`, zero value), or the
  queried message collides under keccak with a message the center sent. This discharges the single-call
  evidence premise of `WithdrawalGate` `SingleCallEvidenceDeliversOneCall` up to that collision.
- `DeliveredWithdrawalWasDispatchedOrCollision` (headline): from fresh L1 storage, every delivered call
  is call `0` of a one-call bundle that the center of the sender's chain dispatched to L1, sent by
  `L2_ASSET_ROUTER_ADDR`, with value zero, to `L1_ASSET_ROUTER`, while the handler was not paused; or
  the delivered bytes collide with verified bytes; or a queried message collides with a sent one.
- `ProvenanceEndToEndWitness`: all four premises hold on a run that delivers one call.
- `UngatedHookDeliversUndispatchedCalls` (countermodel): with a messenger hook that records for every
  caller, the other premises hold on a run where L1 verifies and unbundles a two-call bundle no center
  dispatched, and no delivery satisfies any disjunct of the headline; with the documented hooks the same
  L1 run fails `InclusionSoundOn`.

Out of scope: bundles published before v0.35 by older centers, EraVM chains, and the settlement-layer
authentication behind `InclusionSoundOn`.
