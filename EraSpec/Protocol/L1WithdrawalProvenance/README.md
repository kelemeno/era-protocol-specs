# L1WithdrawalProvenance

Composition of `Contracts/L1InteropHandler` `WithdrawalGate` (the L1 handler) with
`Contracts/L1Messenger` `SenderKeying` (each source chain's modelled L2→L1 output), at era-contracts
`draft/v0.35.0` head `b17415d20`.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Provenance | [Specs/Provenance.lean](Specs/Provenance.lean) | [Properties/Provenance.lean](Properties/Provenance.lean) | [Proofs/Provenance.lean](Proofs/Provenance.lean) |

Namespace `Contracts.L1WithdrawalProvenance`.

## Headline guarantees

These are the area's `@[headline]` statements (see [CONSOLIDATION.md](../../../CONSOLIDATION.md)),
about `b17415d20`. Both carry the four joining premises below, each only for the chains the run's
committed verifications name.

| Guarantee | Premises | Statement |
|---|---|---|
| Every committed verification checked a bundle its chain's interop center dispatched to L1, or a message hash collides | Any L1 start state and transactions; the four joining premises | `ProvenBundlesAreDispatchedOrCollide` |
| Every committed delivery is a dispatched withdrawal, or a hash collides | L1 starts from fresh storage; the four joining premises | `DeliveredWithdrawalWasDispatchedOrCollision` |

Witness (`@[witness]`): `ProvenanceEndToEndWitness`. Countermodel (`@[countermodel]`):
`UngatedHookDeliversUndispatchedCalls` (without the messenger hook's caller gate, L1 delivers calls
no center dispatched).

## Joining premises

Each constrains only the chains that the L1 run's committed verifications name (as the proof's chain
id); other chains, EraVM chains among them, are unconstrained.

- `InclusionSoundOn` (`PROTO-EVIDENCE`): every committed verification's queried message log is in the
  output of the chain its proof names. Only the run's own accepted queries are constrained.
- `ChainsRunTheModelOn`: each such chain's output is that of a run from genesis of the modelled L2 code.
- `HooksAsDocumentedOn`: the VM premise `HooksAsDocumented` of `SenderKeying` on each such chain.
- `DispatchRoundTripOn` (`SOL-ABI`): `abi.decode` inverts `abi.encode` on the bundles those chains
  dispatched.

## Results

In the source-chain model the center's L1 dispatch is a `withdrawal` step guarded by `WithdrawalShape`
(one zero-value call from `L2_ASSET_ROUTER_ADDR`, to L1, with L1's ETH asset id). The shape is argued
from the center's source in `L1Messenger/Specs/SenderKeying.lean` (`InteropCenter.sol:262-264`,
`:552-556`, `:629-658`, `:782-822`), not derived from transcribed center code; the one-call conclusions
below come from that guard.

- `ProvenBundlesAreDispatchedOrCollide`: every committed verification checked the encoding of a bundle
  its chain's modelled center dispatched to L1 (so of `WithdrawalShape`: one call, from
  `L2_ASSET_ROUTER_ADDR`, zero value), or the queried message collides under keccak with a message the
  center sent. Under the four premises, this discharges the single-call evidence premise of
  `WithdrawalGate` `SingleCallEvidenceDeliversOneCall`, up to that message collision.
- `DeliveredWithdrawalWasDispatchedOrCollision` (headline): from fresh L1 storage, every delivered call
  is call `0` of a one-call bundle that the modelled center of the sender's chain dispatched to L1, sent
  by `L2_ASSET_ROUTER_ADDR`, with value zero, to `L1_ASSET_ROUTER`, while the handler was not paused; or
  the delivered bytes collide with verified bytes; or a queried message collides with a sent one.
- `ProvenanceEndToEndWitness`: all four premises hold, non-vacuously (one verification, naming chain
  `270`, whose run dispatched one bundle), on a run that delivers one call.
- `UngatedHookDeliversUndispatchedCalls` (countermodel): with a messenger hook that records for every
  caller, the other three premises hold and `HooksAsDocumentedOn` fails on a run where L1 verifies and
  unbundles a two-call bundle no center dispatched, and no delivery satisfies any disjunct of the
  headline; with the documented hooks the same L1 run fails `InclusionSoundOn`.

Out of scope: bundles published before v0.35 by older centers, deliveries verified against EraVM
chains, and the settlement-layer authentication behind `InclusionSoundOn`.
