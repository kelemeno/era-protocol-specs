# CTM record: the Bridgehub's `chainTypeManager[c]` against the diamond's own CTM

Source: era-contracts `draft/v0.35.0` at `b17415d20`, paths relative to
`l1-contracts/contracts/`. The Bridgehub writes modelled here are the same on `main` at
`70096e2ea` (line numbers there are in the spec's header); `main` has no per-CTM migration
pause.

A chain has two notions of its chain type manager on each layer it lives on. The Bridgehub's
record `chainTypeManager[c]` decides which CTM's `forwardedBridgeBurn` and version check run
when the chain migrates, and, through `ctmAssetIdFromChainId`, which CTM's migration pause
gates the burn. The diamond's `s.chainTypeManager`, written once by `DiamondInit`, is the only
CTM that the diamond's `onlyChainTypeManager` admits, so the only one that can upgrade or
freeze the chain. The record is rewritten on every migration mint from the asset id the
message carries (`BridgehubBase.forwardedBridgeMint`), with no comparison against the diamond.

The model is one state over every layer (L1 and each settlement layer): per layer the record,
the diamond `zkChainMap` holds for each chain (as its `s.chainTypeManager`), the two CTM asset
maps and `settlementLayer`, plus the migration messages sent. Its steps are every writer of
those fields: L1 `createNewChain` and `registerAlreadyDeployedZKChain`, `setCTMAssetAddress` on
any layer, and the chain asset handler's `bridgeBurn`, `bridgeMint` and L1
`bridgeConfirmTransferResult` (failure).

| Review | File |
|---|---|
| State, steps with per-guard citations, the discipline `NoRebind`, the gate CTMs, the diamond's gate `diamondAdmits`, the agreement `RecordAgrees`, the invariant `CtmInv`, the repaired mint, `PairDiscipline`, witness data | [Specs/Agreement.lean](Specs/Agreement.lean) |
| Invariant, corollaries (gates, admitted CTM, settlement layer's CTM), witnesses, countermodels, repaired mint, weakest per-call conditions for registrations and mints, runs without a mint, tracker-level discipline | [Properties/Agreement.lean](Properties/Agreement.lean) |
| Checked proofs and concrete runs | [Proofs/Agreement.lean](Proofs/Agreement.lean) |

## Headline guarantees

These are the area's `@[headline]` statements (see [CONSOLIDATION.md](../../../CONSOLIDATION.md)),
about `b17415d20`. A "disciplined run" is one in which every `setCTMAssetAddress(d, y)` keeps that
layer's two asset maps a partial bijection (`NoRebind`: the asset id is nonzero, not already mapped
to another CTM, and the CTM is not already mapped to another asset id); every other call is
unrestricted. The disciplined and pair-discipline results allow `bridgeMint`, which `b17415d20`
never lets succeed (`CHAIN_MIGRATIONS_ENABLED = false`), so they cover more runs than the target
commit has; `CtmRecordAgreesWithoutMints` is the one that needs no discipline.

| Guarantee | Premises | Statement |
|---|---|---|
| Every registered chain's Bridgehub record is its diamond's CTM, on every layer | The run starts from fresh storage and has no `bridgeMint` call (every run at `b17415d20`) | `CtmRecordAgreesWithoutMints` |
| Every registered chain's Bridgehub record is its diamond's CTM, on every layer | The run starts from fresh storage and is disciplined | `CtmRecordAgreesWithDiamond` |
| A CTM passes a diamond's `onlyChainTypeManager` gate exactly when it is the Bridgehub's record for that chain | The run starts from fresh storage and is disciplined | `CtmRecordNamesAdmittedCtm` |
| Every registered chain's Bridgehub record is its diamond's CTM, on every layer | The run starts from fresh storage; its registrations satisfy `PairDiscipline` (on each layer, additional data and CTM determine each other, and the registered words' asset ids are nonzero and do not collide) | `CtmRecordAgreesUnderPairDiscipline` |
| A registration keeps the two asset maps mutually inverse exactly when it is `NoRebind` | The maps are mutually inverse on their nonzero entries before the call (`AssetBij`); the call succeeds | `CtmRecordNoRebindIffKeepsBijection` |

Witnesses (`@[witness]`): `CtmRecordDisciplinedRoundTripWitness`, `CtmRecordAgreesWithoutMintsWitness`,
`CtmRecordPairDisciplineWitness` and `CtmRecordNoRebindIffKeepsBijectionWitness`. Countermodels
(`@[countermodel]`): `CtmRecordUndisciplinedRoundTripDrifts` and `CtmRecordDriftAdmitsForeignLayer`
(without the discipline, a run with a mint drifts the record).

## Results

| Result | Statement |
|---|---|
| `CtmRecordAgreesWithDiamond` (headline) | Along every run in which each `setCTMAssetAddress` keeps its layer's asset maps a partial bijection (`NoRebind`), on every layer every chain's record is its diamond's CTM. From `CtmInv` (`CtmRecordInvInit`, `CtmRecordInvStep`, `CtmRecordInvReachable`). |
| `CtmRecordSettlementDiamondFollowsL1Ctm` | On those runs a chain's diamond on a settlement layer is the CTM that layer maps the asset id of the chain's L1 CTM to. |
| `CtmRecordBurnGatesAreDiamondCtm`, `CtmRecordMintGatesAreDiamondCtm` | On those runs the CTM whose version a burn or mint checks, and the CTM whose migration pause gates it (for a burn, when its asset id is nonzero, always so off L1), is the diamond's CTM. |
| `CtmRecordNamesAdmittedCtm` | On those runs, for every chain a layer holds, a CTM passes the diamond's `onlyChainTypeManager` gate (the gate of `executeUpgrade`, `freezeDiamond`, `unfreezeDiamond`) exactly when it is the Bridgehub's record. |
| `CtmRecordBurnTargetsSameCtmLayer`, `…Witness` | In every state whose records all agree with their diamonds (`RecordAgrees`), a chain burned on L1 towards a layer that has a diamond on L1 goes to a layer whose L1 diamond is under the chain's own CTM: the burn's two CTM checks (`ChainAssetHandlerBase.sol:232-237`, `Migrator.sol:181-189`) read L1's record of the settlement layer. |
| `CtmRecordDisciplinedRoundTripWitness` | The premises of the invariant and of the gate corollaries, on a round trip L1 → settlement layer → L1 with two CTM families and an exact repeat registration; the state after the return mint is reachable by a disciplined run. |
| `CtmRecordUndisciplinedRoundTripDrifts` (countermodel) | One settlement-layer registration giving a CTM a second asset id: after the round trip L1's record for the chain names CTM `11` while its diamond's CTM is `10`. The return mint is gated by `11`'s pause and checks `10`'s version. |
| `CtmRecordDriftAdmitsForeignLayer` (countermodel) | Continuing that run, a chain created on L1 under CTM `11` is burned towards the returned chain, whose diamond admits `10` and not `11`: both CTM checks pass on the drifted record. |
| `CtmRecordStaleReverseEntryMisgatesPause` (countermodel) | One registration re-pointing an asset id: the record still agrees with the diamond on both layers, but the burn on the settlement layer is gated by another CTM's pause. |
| `CtmRecordRepairedMintAgrees`, `CtmRecordRepairAdmitsDisciplinedRuns`, `CtmRecordRepairedRoundTripWitness` | A mint that compared an existing diamond's CTM with the asset's CTM (not in the source) keeps the agreement on every run, with no discipline, and rejects no mint of a disciplined run. |
| `CtmRecordRepairedMintKeepsStalePauseGate` (countermodel) | That repair alone leaves the stale pause gate of the previous countermodel. |
| `CtmRecordMintKeepsAgreementIff`, `…Witness` | From a state whose records all agree with their diamonds, a mint keeps them so exactly when it passes the repaired mint's check; both sides are exhibited with an existing diamond. |
| `CtmRecordNoRebindIffKeepsBijection`, `…Witness` | From mutually inverse asset maps, a registration keeps them so exactly when it is `NoRebind`; both sides are exhibited. |
| `CtmRecordAgreesWithoutMints`, `…Witness` | Along every run with no `bridgeMint`, disciplined or not, the record agrees with the diamond. At `b17415d20` and `70096e2ea` `CHAIN_MIGRATIONS_ENABLED = false` makes every `bridgeMint` revert. |
| `CtmRecordPairDisciplineGivesNoRebind`, `CtmRecordAgreesUnderPairDiscipline`, `CtmRecordPairDisciplineWitness` | The tracker-level form: if on each layer the registered `(additionalData, CTM)` pairs determine each other and their asset ids are nonzero and do not collide, every registration is `NoRebind`. The witness's run satisfies it; the drifting run does not. |

## Model boundaries

* **Reject-only checks are omitted** (callers, pauses, `whenMigrationsEnabled`, the
  settlement-layer whitelist, protocol versions, migration numbers, priority queues, deposit
  pauses, batches, base tokens, the message root, chain-count limits, part of
  `_validateChainParams`, `isReadyForMigration`). Omitting them only adds runs, so the
  invariant covers the source's runs; the countermodels pass every check the model keeps, and
  the omitted ones are argued from source (for example, the tracker owner can register the
  chain asset handler as the settlement layer's handler of both asset ids through
  `L1AssetRouter.bridgehubDeposit`, `bridge/asset-router/L1AssetRouter.sol:216-227` and
  `:158-183`, checked by `CTMDeploymentTracker.sol:139-148`; a chain back on L1 can be
  whitelisted as a settlement layer, `L1Bridgehub.sol:94-100`). In the source a chain makes at
  most one round trip (`MAX_ALLOWED_NUMBER_OF_MIGRATIONS = 2`, `common/Config.sol:329`); each
  chain in the countermodels makes at most one.
* **Runs start from fresh storage.** `CtmRecordInvStep` is the inductive step, so the agreement
  also holds along disciplined runs from any state that satisfies `CtmInv`. Whether a deployed
  Bridgehub's state does is not checked here.
* **Messages persist**: a mint needs its message to have been sent and does not consume it.
* **Genuine code** (`OPS-CONFIG`): every CTM the Bridgehub calls runs `ChainTypeManager.sol`, so
  the diamond it deploys has `s.chainTypeManager` equal to that CTM (`DiamondInit.sol:91`); the
  Bridgehub's `chainAssetHandler` and `l1CtmDeployer` are the chain asset handler and the
  `CTMDeploymentTracker` on every layer. A CTM cut whose init writes `s.chainTypeManager`, CTM
  code swaps and Bridgehub upgrades are outside the model.
* **The discipline is a premise** about the tracker owner's registrations. On L1 the tracker
  registers `(bytes32(x), x)` (`CTMDeploymentTracker.sol:79`), so there only the asset-id
  conditions remain; on a settlement layer the owner chooses the pair
  (`CTMDeploymentTracker.sol:106-126`).
* **Asset ids** are an uninterpreted function of the layer and `additionalData`; the asset id
  travels verbatim in the migration message.

See `MODEL-CTM-RECORD` in the [assumption register](../../../ASSUMPTIONS.md).
