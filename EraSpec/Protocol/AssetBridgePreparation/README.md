# Asset bridge preparation trace

This protocol slice composes the local
[NativeTokenVaultBase preparation model](../../Contracts/NativeTokenVaultBase/README.md)
with ordinary source-token transfers. Its `pending` list is ghost trace bookkeeping:
it is not vault storage and does not prove that any router or interop center
published the prepared data.

The [assumption register](../../../ASSUMPTIONS.md) distinguishes `MODEL-TRACE`
and `REP-PUBLISH` from the token/vault laws being composed. `OPS-CONFIG` records
the need to include or frame other production transitions; progress has the
separate `OPS-PROGRESS` boundary.

| Review | File |
|---|---|
| Trace state, preparation/spend steps, reachability, and pending-value fold | [Specs/Model.lean](Specs/Model.lean) |
| Reachable conservation, initial backing, and persistence properties | [Properties/Model.lean](Properties/Model.lean) |
| Checked trace-property derivations | [Proofs/Model.lean](Proofs/Model.lean) |
| Initialization-to-preparation composition statement | [Properties/Initialization.lean](Properties/Initialization.lean) |
| Checked initialization composition | [Proofs/Initialization.lean](Proofs/Initialization.lean) |
| Trace with token version and metadata, reinitialization steps, `PendingNamesToken` | [Specs/Reinitialization.lean](Specs/Reinitialization.lean) |
| Conservation, persistence, pending-asset binding, registration-to-trace composition | [Properties/Reinitialization.lean](Properties/Reinitialization.lean) |
| Checked reinitialization derivations and concrete witness | [Proofs/Reinitialization.lean](Proofs/Reinitialization.lean) |
| Per-destination pending total | [Specs/RegistryCorrespondence.lean](Specs/RegistryCorrespondence.lean) |
| The trace against the registry model's flow audit | [Properties/RegistryCorrespondence.lean](Properties/RegistryCorrespondence.lean) |
| Checked registry-correspondence derivation and witness | [Proofs/RegistryCorrespondence.lean](Proofs/RegistryCorrespondence.lean) |

## Allowed trace and context

A trace step either performs a successful vault preparation and appends its exact
returned mint data once, or performs an ordinary successful source-token transfer
while leaving pending entries unchanged. Thus later source transfers are allowed
between preparations. This closed transition system has no independent mint,
refund, destination delivery, router publication, or external-call step.

Each pending record pairs the returned mint-data tuple with the outer request's
asset ID and destination chain. Those outer fields are trace context; they are not
fields of the mint-data tuple and the trace does not prove they are encoded or
published by production code.

## Proven local targets

- **Local exact burn:** every successful preparation contributes the exact amount
  debited from the depositor and removed from token total supply, by the vault
  preparation property.
- **Pending-value conservation:** from a well-formed starting vault state,
  circulating token supply plus the total pending amount stays constant through
  every reachable preparation and ordinary transfer.
- **Pending value remains initially backed:** when the initial trace has no pending
  records, total pending value never exceeds the initial source-token supply.
- **Prefix persistence:** later preparations and ordinary transfers only append to
  the pending list; previously prepared data is retained unchanged.
- **Reinitialization:** the trace extended with `reinitializeToken` steps by any
  caller (`ReinitReach`) keeps `WellFormed`, circulating supply plus pending value,
  the vault configuration, the token identity, and all previously prepared data
  (`ReinitTraceConservation`, `ReinitTracePreparedDataPersists`; step cases
  `ReinitStepCases`). Every pending obligation keeps naming the token's original asset
  id and origin token (`PendingObligationsKeepTheirAsset`). The existing trace embeds
  unchanged (`TraceRunsEmbed`). Witness: `ReinitTraceWitness`.

These conclusions rely on the vault's `WellFormed` registry and token-ledger
assumptions, and on its modeled accounting hook and `Option` commit behavior. The
trace's conservation proof is a theorem about these abstract transitions, not about
vault storage, EVM rollback, actual publication, or a destination's readiness.

The initialization composition derives the starting ledger and representation
invariants from the successful fresh-registration branch. It then permits a local
token-operation phase to establish nonzero balances before the preparation trace;
otherwise a freshly created zero-supply token could only yield an empty trace.
This theorem has no input `WellFormed` or `RepresentationConsistent` hypothesis.
The token phase permits mint/burn/transfer under the existing token guards; it
does not prove the cross-chain authorization or economic backing of those mints.
`InitializedTraceWithReinitialization` composes the same registration with a funding
phase and a trace that both include reinitializations, again with no input invariant.

## Against the registry model

`TightTraceIsRegistryOutflow` runs the initialization composition starting from the
tightened registration (`registerFreshBranch'`, see the
[NativeTokenVaultBase README](../../Contracts/NativeTokenVaultBase/README.md)). A
bounded registry-model run simulates it:

- the registry vault is the registration's write throughout, and it corresponds to
  the final ledger;
- `Valid` and `WellFormed` hold;
- during the trace the registry records no inflow of the asset, and records exactly
  the pending total as outflow, per destination chain (`pendingAmountTo`).

The registry run is the matching run the simulation builds, so the pending list and
that run's flow audit agree. Other registry runs are not constrained: the registry
model does not bound a bridged asset's flows
(`Contracts.NativeTokenVaultBase.Properties.LifecycleIdentityNotRegistryInvariant`). Token-model
mints and burns carry no chain id, so per-destination outflow is claimed only for
preparations. Neither ghost record is evidence of publication. Witness:
`TightTraceIsRegistryOutflowSatisfiable`.

This model does not prove router correspondence, unique resolution, replay
protection, delivery/refund exclusion, or completion of M1. It must not be read as
showing that a production router cannot publish the same data twice. See the
[refinement obligations](../../Refinement.lean) and the
[full asset-bridging plan](../../../ASSET_BRIDGING_VERIFICATION_PLAN.md) for the
separate open work.
