# ChainAssetHandler

Chains migrating between settlement layers through the chain asset handlers (L1's and every
settlement layer's) at era-contracts `draft/v0.35.0` `b17415d20`, with their bridgehubs, CTMs,
diamonds and pause switches.

## Headline guarantees

The folder's real guarantees about `b17415d20`, each with every premise. They are meant to carry
`@[headline]` (the lists after the table: `@[witness]`, `@[countermodel]`) once the tag attributes
of `EraSpec.Core.Headline` are on this branch; they are not tagged yet.
"Reachable" means reached from a fresh deployment by any interleaving of the model's steps, for one
fixed `World` (whitelists, CTM registries and owners). Message delivery is the environment's
guarantee (`PROTO-CAH-DELIVERY`: an L1 → L2 transaction executes once with a truthful status that
L1 consumes once; an L2 → L1 message is finalized at most once). Reject-only checks are omitted,
so the safety results cover the source; at `b17415d20` `CHAIN_MIGRATIONS_ENABLED` is `false`, so
the migration results describe the kept machinery.

| Guarantee | Premises | Statement |
|---|---|---|
| A chain registered on L1 has exactly one holder: one hub whose own bridgehub says it settles there, or one live migration message; an unregistered chain has none | Reachable state | `ExactlyOneSettlementLayer` |
| L1's `migrationNumber[c]` changes only 0 → 1 (L1 burn), 1 → 2 (L1 mint) or 1 → 0 (failed-deposit confirmation) | None (one step) | `L1MigrationNumberTransitions` |
| A chain completes at most one L1 → settlement layer → L1 round trip, however many failed attempts | Starts from a reachable state | `AtMostOneRoundTrip` |
| Right after an L1 burn, the deposit's failure and L1's confirmation are steps, and they restore every field of every hub | Starts from a reachable state; the L1 asset router's and nullifier's pauses and the status proof are not modelled | `FailedMigrationRecoveryRestoresSource` |
| L1's `isMigrationInProgress[c]` is set exactly while an L1-originated message for `c` is unconfirmed | Reachable state | `InProgressTracksUnconfirmedDeparture` |
| With `CHAIN_MIGRATIONS_ENABLED = false` (the value at `b17415d20`) no message exists and every chain registered on L1 stays there | Reachable state | `MigrationsDisabledFreezeSettlement` |
| A pending message out of L1 is minted by its settlement layer on a fresh diamond | Reachable state; migrations enabled; that layer's three switches off for the asset's CTM there; that CTM nonzero; the carried version is its version | `GatewayAcceptsArrival` |
| A pending message into L1 is minted by L1, reusing the chain's L1 diamond | Reachable state; migrations enabled; L1's three switches off; the CTM nonzero; L1's diamond at its own CTM's version | `L1AcceptsReturn` |
| A failed deposit out of L1 can be confirmed, with no pause switch or release flag | Reachable state; L1's diamond at the version the burn data carries | `FailedDepositConfirmable` |
| Every burn and mint on a hub needs migrations enabled and that hub's `paused()`, ecosystem pause and CTM pause off | None | `PauseBlocksMigrationSteps` |
| Only a CTM's owner toggles its pause, only the handler owner the ecosystem pause | Any run | `OnlyOwnersTogglePauses` |
| L1's confirmation of a failed deposit reads no pause switch and no release flag | None | `RecoveryIgnoresPauses` |

Witnesses: `CahRoundTripWitness`, `CahInFlightWitness`, `CahGatewayWitness`,
`CahFailedAttemptWitness`, `CahReturnedChainWitness`, `CahDisabledWitness`, `CahArrivalWitness`,
`CahReturnInFlightWitness`, `CahRecoveryWitness`, `CahCTMPauseWitness`, `CahPausedHubWitness`,
`CahPauseHoldsWitness`. Countermodel:
`CahMismatchedRegistryReadsAnotherPause`. The other statements are supporting lemmas.

## Source

era-contracts `draft/v0.35.0` at commit **`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**, under
`l1-contracts/contracts/`; every `file:line` is at that commit:

- `core/chain-asset-handler/ChainAssetHandlerBase.sol` (`CAH`), `L1ChainAssetHandler.sol`
  (`L1CAH`), `L2ChainAssetHandler.sol` (`L2CAH`)
- the callees whose effects or checks are part of a step: `core/bridgehub/BridgehubBase.sol`
  (`BH`), `core/bridgehub/L1Bridgehub.sol` (`L1BH`), `state-transition/ChainTypeManager.sol`
  (`CTM`), `state-transition/chain-deps/DiamondInit.sol` (`DI`), the diamond's `Migrator` and
  `Admin` facets (`MIG`, `ADM`), `common/Config.sol` (`CFG`)

At `main` `70096e2ea` these files differ: among other changes the handler there has a single
`migrationPaused` switch and no per-CTM pause, and L1's handler has an owner-only writer of
interval 0 (`setHistoricalMigrationInterval`). The model describes `draft/v0.35.0` only.

Review `Specs/` for state, operations and assumptions, then `Properties/` for the guarantees
and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact named
propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Migration | [Specs/Migration.lean](Specs/Migration.lean) | [Properties/Migration.lean](Properties/Migration.lean) | [Proofs/Migration.lean](Proofs/Migration.lean) |
| Pause | (uses [Specs/Migration.lean](Specs/Migration.lean)) | [Properties/Pause.lean](Properties/Pause.lean) | [Proofs/Pause.lean](Proofs/Pause.lean) |

Namespace: `Contracts.ChainAssetHandler`. Statements are
`Contracts.ChainAssetHandler.Properties.*`; each certificate has the same name without the
`Properties` segment. No statement takes a hash premise.

## The model

One state holds every hub at once: for each hub (a chain id whose handler, bridgehub, CTMs and
diamonds are tracked; L1 and every settlement layer) its bridgehub's `settlementLayer`,
registration and `chainTypeManager` per chain, its handler's `migrationNumber` and three pause
switches, its CTMs' versions, and each chain's diamond there (version, own CTM, whether it is
away). L1 adds `isMigrationInProgress` and the two modelled fields of `_migrationInterval[c][1]`
(`isActive`, `settlementLayerChainId`). Migration messages carry source, destination, chain,
CTM asset id, migration number and protocol version, with a delivery status
(`pending`, `executed`, `failed`, `done`).

`Label` has fifteen constructors (`Step` has sixteen: `bridgeMint` has two branches): L1's
`createNewChain` and `registerAlreadyDeployedZKChain`, any hub's `bridgeBurn`, `bridgeMint`
(fresh diamond or returning diamond), the failure of an L1 → settlement-layer transaction, L1's
`bridgeConfirmTransferResult` (success or failure), an L2's `setSettlementLayerChainId`, the six
pause entry points, and two environment steps raising a CTM's or a diamond's version. A revert
is the absence of a step; reject-only checks are
omitted (listed in the Specs header), so every safety result covers the source. `Reach` is
any interleaving from a fresh deployment, for one fixed `World` (whitelists, CTM asset-id
registries, CTM registration and owners, handler owners; `OPS-CONFIG`).
`CHAIN_MIGRATIONS_ENABLED` is a parameter: `false` at this commit (`CFG:320`).

The delivery statuses are the environment's guarantees (`PROTO-CAH-DELIVERY` in
[ASSUMPTIONS.md](../../../ASSUMPTIONS.md)): an L1 → L2 transaction executes once, with a
truthful status that L1 consumes once; an L2 → L1 message is finalized at most once and does not
fail.

## What to check

**Migration** (`Properties/Migration.lean`):

- One holder. A chain registered on L1 has exactly one holder, a hub whose own bridgehub says
  it settles there or one live (pending, or failed and unconfirmed) message, and a chain not
  registered on L1 has none (`ExactlyOneSettlementLayer`). A registered diamond is away exactly
  when its hub's bridgehub does not record that hub (`BridgehubAgreesWithDiamond`). L1's
  bridgehub records the settlement layer that holds the chain, or the far end of the message
  that holds it (`L1SettlementLayerTracksHolder`).
- Messages run between L1 and a settlement layer whitelisted on the source, never name their
  own chain as an endpoint, and carry number 1 out of L1 and 2 into it
  (`MessagesRunBetweenL1AndALayer`).
- L1's migration number is at most 2 and mirrors the chain's position and interval 1
  (`L1MigrationBookkeeping`); it moves only 0 → 1, 1 → 2 and 1 → 0
  (`L1MigrationNumberTransitions`); a returned chain never moves again
  (`ReturnedChainStaysOnL1`); a chain completes at most one round trip, however many failed
  attempts it makes (`AtMostOneRoundTrip`).
- Delivery. A pending message out of L1 is minted by its settlement layer, on a fresh diamond,
  whenever that layer's switches are off for the asset's CTM there, migrations are enabled,
  that CTM is not zero, and the carried version is its version (`GatewayAcceptsArrival`). A
  pending message into L1 is minted by L1, reusing the chain's L1 diamond, under the same
  conditions on L1 with the version condition replaced by "L1's diamond is at its own CTM's
  version" (`L1AcceptsReturn`). The migration numbers, interval 1 and the away checks never
  block either.
- Recovery. Directly after an L1 burn, the deposit's failure and its confirmation restore
  every field (`FailedMigrationRecoveryRestoresSource`). From any reachable state a failed
  deposit can be confirmed while L1's diamond is at the version the burn data carries
  (`FailedDepositConfirmable`). `isMigrationInProgress` is set exactly while an L1-originated
  message is unconfirmed, whatever happened to the chain since
  (`InProgressTracksUnconfirmedDeparture`).
- Versions at burn and mint (`VersionEqualityAtBurnAndMint`), and the production constant:
  with migrations disabled no message exists and every chain registered on L1 stays there
  (`MigrationsDisabledFreezeSettlement`).

**Pause** (`Properties/Pause.lean`): every burn and mint on a hub needs that hub's three
switches off and migrations enabled (`PauseBlocksMigrationSteps`); the CTM switch read is the
chain's own when the hub's registry maps that CTM's asset id back to it
(`PausedCTMChainsDoNotMove`; `CahMismatchedRegistryReadsAnotherPause` shows the premise is
needed); a switch set at the start of a run blocks every burn or mint it guards in a run that
does not lift it (`PauseHoldsUntilUnpaused`); only the right owner writes the CTM and
ecosystem switches (`OnlyOwnersTogglePauses`); a hub's burn or mint reads no other hub's
switches (`PausesArePerHub`); L1's confirmation reads none (`RecoveryIgnoresPauses`).

**Witnesses**, in `cahWorld` (L1 `1`, gateway `2`, chain `3`, CTM `7`, asset id `5`):
a complete round trip, the chain in flight and on the gateway, a failed attempt and its
recovery, a run after the return, the production constant, the arrival with L1 paused, the
return accepted after L1's CTM and diamonds were upgraded, a failed deposit confirmed after a
CTM upgrade with L1 paused, and the pause scenarios. Each witness's docstring names the
properties whose premises it instantiates; together they cover every property.

## Not covered

- Batch numbers, the message root, the intervals' batch fields and `isValidSettlementLayer`;
  priority trees and the deposit-pause timestamp; base-token data in the mint message.
- Callers of the handler (the asset router), the chain admin checks, `isReadyForMigration`,
  and the other reject-only checks listed in the Specs header.
- Registry, whitelist and ownership changes during a run; CTM, handler or diamond code swaps;
  a CTM owner's arbitrary cut of a diamond (`OPS-CONFIG`).
- The L1 asset router's and nullifier's own pauses and the status proof on the confirmation
  path; message transport itself (`PROTO-CAH-DELIVERY`).
- Eventual delivery: the enabledness results say when a step is possible, not that it is
  taken (`OPS-PROGRESS`).
- Storage, ABI and call correspondence.

The `ChainTypeManager` folder's `ChainMigration` topic models the same `bridgeMint` reuse of a
diamond for routing (`ChainAssetHandlerBase.sol:397-417`), and `../L1ChainAssetHandler/` models
the same burn, mint and confirmation code for one chain with its batch numbers and migration
intervals. Neither state is a projection of this one; the models are not composed.
