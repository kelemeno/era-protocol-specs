# AssetRouterBase

## Headline guarantees

All about `l1-contracts/contracts/bridge/asset-router/{AssetRouterBase,L1AssetRouter,L2AssetRouter}.sol`
(and the refund path through `atomic-interop/AtomicFlowManager.sol` and the native token vault) at
era-contracts `draft/v0.35.0` head `b17415d20`.

"A writer run" (`MODEL-ROUTER-WRITERS`) is a sequence of successful calls of the router's map
writers: registration `_setAssetHandlerAddressThisChain`, the `_finalizeDeposit` fallback, the seed
(`setNativeTokenVault` on L1, `initL2` on L2), the L2 counterpart's `setAssetHandlerAddress` and the
L1 owner's `setAssetDeploymentTracker`. The router's configuration (encoding, chain id, vault
address, seeded id) is fixed for the run and the router is not upgraded; `finalize` admits every
caller and the initializers are repeatable, which only adds runs. "Fresh storage" means both maps
start empty.

- `Contracts.AssetRouter.AllWriters.Properties.RunWeakValid`: along a writer run, every live route
  has a nonzero tracker or is a vault route (handler the vault, id a vault id). Premises: fresh
  storage; the vault's `bridgeMint` succeeds only on vault ids (`MintsOnlyNtvIds`, proved from the
  vault model by `VaultModelDischargesMintPremise`); the seeded id is a vault id (on L2 the
  upgrader's input, `OPS-CONFIG`); no counterpart write and no owner tracker write naming zero in
  the run. No hash premise.
- `Contracts.AssetRouter.AllWriters.Properties.L1RunWeakValidOn`: the same on every L1 writer run.
  Premises: the L1 router with a nonzero vault address; fresh storage; `MintsOnlyNtvIds`; the seeded
  id is a vault id; `encodeAssetId` injective on the triples the run's calls hashed.
- `Contracts.AssetRouter.AllWriters.Properties.L2OnlyVaultRegisters`: on L2 every tracker is zero or
  the vault, and every registration in the run was the vault's. Premises: the L2 router; fresh
  storage. No hash premise.
- `Contracts.AssetRouter.AllWriters.Properties.NoHijackOnExceptCounterpart`: one call of any writer
  but the counterpart leaves the route of every id hashed from another sender unchanged. Premises:
  `MintsOnlyNtvIds`; the seeded id is a vault id; any router state; `encodeAssetId` injective on the
  two triples compared.
- `Contracts.AssetRouter.AllWriters.Properties.CounterpartCannotMisrouteVaultTriple`: on L2, the
  route of a vault triple's id is always unset, tracked, or the L2 vault. Premises: the L1 and L2
  routers share the encoding and `L2_NATIVE_TOKEN_VAULT_ADDR`, and the L2 vault is at that address;
  the L1 trackers approve as `VaultApprovals` says (no code at `0x10004` on L1); fresh L2 storage;
  every counterpart write to that id was sent by the L1 router from a state its own run reached
  (`PROTO-EVIDENCE`), with `encodeAssetId` injective on that L1 run's triples and the vault triple.
- `Contracts.AssetRouter.AllWriters.Properties.RunTrackerRecorded`: every nonzero tracker was
  recorded by a logged call at that call's own id (an owner tracker write naming it, or its own
  registration). Premises: fresh storage. No hash premise.
- `Contracts.AssetRouter.Properties.LoggedRouteIsLastOwnWrite`: in a run of registrations only,
  from any router state, the route and tracker of a triple's id are what the last call hashing that
  triple wrote, or the start state's. Premises: no other writer between the registrations;
  `encodeAssetId` injective on the run's triples and the watched triple.
- `Contracts.AssetRouter.HandlerGateAtV35.Properties.MovementsUseExemptHandlerOrEnabledChain`: on
  L1, every event that moves an asset at chain `c` moved it through the router's vault or the chain
  asset handler of the state it ran in, or `c` was interop-enabled in that state. Premises: a v35 L1
  run from any state; the gate model's boundary (`MODEL-ROUTER-GATE-V35`: handler calls taken to
  succeed, other entry-point checks not modelled).
- `Contracts.AssetRouter.HandlerGateAtV35.Properties.StrandedUntilListedCall`: a stranded
  `(chain, asset)` (custom handler, chain without interop) stays stranded, and nothing moves the
  asset at that chain, until `enableInterop(c)`, `setAddresses`, a registration of the asset, or
  `setNativeTokenVault` seeding it. Premises: stranded at the start; no listed call in the run; the
  gate model's boundary.
- `Contracts.AssetRouter.HandlerGateAtV35.Properties.OpenGateStaysOpen`: once a gated entry point at
  `(c, a)` has a step, every gated entry point at `(c, a)` keeps one, through the same handler.
  Premises: no `setAddresses` and no call that can rewrite `a`'s handler in the run; the gate
  model's boundary.
- `Contracts.AssetRouter.AtomicRecoveryAtHead.Properties.RouterLegReachesBurnHandler`: the refund
  of a router leg is the burn handler's own `bridgeRecoverFailedTransfer` on the burn's bytes.
  Premises: a non-L1 destination; a nonzero vault address; between burn and claim the maps change
  only by a writer run with no call rotating the asset away from the burn handler; the refund
  model's boundary (`MODEL-ATOMIC-RECOVERY-HEAD`: typed call data, one `L1_CHAIN_ID` and one
  `BASE_TOKEN_ASSET_ID` value across contracts, vault hooks and base-token holder write only the
  rest of the world, other handlers' code arbitrary).
- `Contracts.AssetRouter.AtomicRecoveryAtHead.Properties.VaultBurnRefundsDepositorAfterRunAtHead`:
  after a vault burn and any writer run that does not rotate the asset away from the vault, the
  router leg's refund re-mints the burned amount to the depositor. Premises: the burn is the vault's
  preparation from a well-formed state; the call's bytes decode to its mint data; a non-L1
  destination; a nonzero vault address; not this chain's base token; the vault unpaused, knowing the
  asset as bridged; its tracker hook returns; the refund model's boundary.
- `Contracts.AssetRouter.AtomicRecoveryAtHead.Properties.RevertingCallBlocksClaimAtHead`: one call
  that reverts in every reachable world blocks the claim of its whole bundle, in every leg state.
  Premises: an invariant the bundle's returning calls keep, under which that call reverts; the
  refund model's boundary.
- `Contracts.AssetRouter.AtomicRecoveryAtHead.Properties.DirectBundleClaimIsNoOpAtHead`: a bundle of
  zero-value calls none of which is from the router is claimed as a no-op: the leg is `Reverted` and
  the world unchanged, whatever data the calls carry. Premises: a non-L1 destination; the refund
  model's boundary.
- `Contracts.AssetRouter.AtomicRecoveryAtHead.Properties.L1DestinationClaimRevertsAtHead`: a claim
  with an L1 destination reverts. Premises: the destination is `L1_CHAIN_ID`; the refund model's
  boundary.

Each headline has a `@[witness]` showing its premises can hold. The `@[countermodel]`s show that
each premise is needed or that a stronger reading is false: `RunValid` fails after one deposit
(`RunValidFailsAfterOneDeposit`); the counterpart, a non-vault seed or mint, and a zero tracker
under a collision break `WeakValid`; the counterpart can point any id anywhere
(`CounterpartRepointsAnyRoute`); a collision hands a tracker to another sender or takes over a live
route; without the `require` the hash alone does not protect vault routes; `setAddresses` or a
re-registration closes an open gate; a handler rotation between burn and claim strands or blocks a
refund (upstream known issue, `protocol-docs/atomicity/security.md`).

## Topics

Specs model the code, Properties state the guarantees (only `def` statements), Proofs prove each
statement under the same name without the `Properties` segment.

| Topic | Namespace | What it models |
|---|---|---|
| HandlerRegistration | `Contracts.AssetRouter` | `_setAssetHandlerAddressThisChain` (`AssetRouterBase.sol:65-77`); the router-map vocabulary (`Router`, `IdInjOn`) |
| HandlerRegistrationRuns | `Contracts.AssetRouter` | logged runs of registrations from any state |
| AllWriters | `Contracts.AssetRouter.AllWriters` | every writer of the two maps: the router's one model of its maps |
| AllWritersStrong, CounterpartGate, VaultMintGate | `Contracts.AssetRouter.AllWriters` | trackers named by logged calls; the L1 side of the counterpart path; `MintsOnlyNtvIds` from the vault model |
| HandlerGateAtV35 | `Contracts.AssetRouter.HandlerGateAtV35` | v35's `_checkAssetHandlerAllowed` (`L1AssetRouter.sol:276-288`) on `AllWriters`' L1 steps |
| AtomicRecoveryAtHead | `Contracts.AssetRouter.AtomicRecoveryAtHead` | the atomic refund: the manager's loop (`AtomicFlowManager.sol:292-325`), `recoverAtomicCall` (`L2AssetRouter.sol:269-303`), `bridgehubRecoverBaseToken`, the L2 vault override |
| AtomicRecovery | `Contracts.AssetRouter.AtomicRecovery` | the vault's refund (`NativeTokenVaultBase.sol:195-214, 264-286`), `_burn`'s handler choice; plus the `c67894b9` record of the pin refund (see below) |

How the models fit: `HandlerRegistration` is `AllWriters`' register-only fragment
(`SingleWriterIsRegisterOnlyFragment`); every v35 gated run projects onto an `AllWriters` L1 run
(`RunProjectsToAllWriters`); `AtomicRecoveryAtHead` reuses `AtomicRecovery`'s vault refund and
`AllWriters`' runs; the vault refund is the canonical NativeTokenVaultBase recovery on the
registered bridged branch (`AtomicRecovery.Properties.VaultRefundRefinesResolution`).

## Assumptions to review

- `NoHijack` and `NtvTouchesOnlyItsOwnIds` take `IdAssumptions enc`, whose `inj` asks
  `encodeAssetId` to be injective on all triples: no map into 256-bit words satisfies it
  (`IdAssumptionsUnsatisfiable`), so they hold vacuously (`CRYPTO-ID`). They are untagged; the
  bounded forms are `NoHijackOn`, `NtvTouchesOnlyItsOwnIdsOn`, the logged-run results and
  `AllWriters.NoHijackOnExceptCounterpart`.
- `IsNtvId` is existential, so the id conjunct of a vault route is weak; the handler conjunct is the
  informative part (`VaultRunIdShape` pins it).
- The router's and the vault's `BASE_TOKEN_ASSET_ID` slots on L2 hold one value (`OPS-CONFIG`):
  `L2AssetRouter.finalizeDeposit` rejects that id (`:258`), which is why the vault's unchecked
  base-token registry write is never minted through the fallback.
- Not modelled: events, `msg.value`, pause outside the vault refund, `nonReentrant`, router upgrades,
  the L1 failed-deposit path beyond the v35 gate, and ABI encoding of the id preimage.

## History

`History/` is the record of the abandoned interop pin `c67894b9`, not a claim about `b17415d20`.

- `History/{Properties,Proofs}/AtomicRecovery.lean` (`Contracts.AssetRouter.AtomicRecovery.History`):
  the pin's `recoverAtomicCall` always called the vault, and the pin loop reverted when nothing was
  recovered. The fixed finding M1 is kept as countermodels: a custom-handler asset's refund reverts
  (`CustomHandlerDepositRefundReverts`) and blocks its whole bundle
  (`CustomHandlerBundleNeverRefunded`, `CustomHandlerBundleIsStranded`); a direct call was refunded
  as if it were a burn (`DirectCallIsRefunded`, `DirectCallMintsUnbacked`). At `b17415d20` the refund
  goes to the registered handler and a direct call's claim is a no-op
  (`AtomicRecoveryAtHead.Properties.PinStrandedBundleRefundedAtHead`, `DirectCallIsRefundedFailsAtHead`).
  The pin definitions these use (`recoverAtomicCall`, `recoverCall`, `recoverBundle`, `claimRefund`,
  `routerCall`, `directCall`) stay in `Specs/AtomicRecovery.lean`, marked as the record, because
  `AtomicRecoveryAtHead`, AtomicFlowManager `RecoveryTargets` and Protocol `FullRecovery` use them.
- `History/*/AtomicRecoveryFaithful.lean`: the pin's router call to L1 targets `L1_ASSET_ROUTER`, and
  the pin's send checks admitted an atomic one-call bundle to L1 whose refund could not reach the
  router. At `b17415d20` the send rejects it (`InteropCenter.sol:552-553`) and `recoverAtomicCall`
  rejects an L1 destination (`L2AssetRouter.sol:275`).
- `History/*/PausedRecovery.lean`: the vault pause on the pin loop (a paused vault blocks a claim
  with a router deposit; unpausing restores it). Restating it on `AtomicRecoveryAtHead` is open.
