# L1ChainAssetHandler

Source: era-contracts `draft/v0.35.0` at commit
**`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**, under `l1-contracts/contracts/`:

- `core/chain-asset-handler/L1ChainAssetHandler.sol`: `isValidSettlementLayer` (`:218-267`), the
  interval recorders (`:277-320`), the failure branch of `bridgeConfirmTransferResult`
  (`:151-161`)
- `core/chain-asset-handler/ChainAssetHandlerBase.sol` (`bridgeBurn`, `_finalizeBridgeBurn`,
  `bridgeMint`: `:188-300`, `:361-420`) and `L2ChainAssetHandler.sol` (`:136-151`)
- `core/message-root/MessageRootBase.sol` (`currentChainBatchNumber` and its writers,
  `:145-157`, `:183-197`) and `L1MessageRoot.sol` (the only caller, `:96-120`)
- `state-transition/chain-deps/facets/Executor.sol`, `Migrator.sol`, `ZKChainBase.sol`
- `core/bridgehub/BridgehubBase.sol` (`:403-468`), `L1Bridgehub.sol` (`:94-100`, `:134`, `:316`)
- `common/Config.sol` (`:320-329`)

At `main` `70096e2ea` the function differs only in starting its loop at index 0
(`isValidSettlementLayerMain`). The other differences on this path at `main` (an owner-only writer
of index 0, a v31 writer of L1's counter, a relaxed mint check, reject-only checks) are listed in
the Specs module docstring, with the proved facts on which they do not fire.

Review `Specs/` for state, operations and assumptions, then `Properties/` for the guarantees and
their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact named
propositions, plus auxiliary lemmas.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| SettlementLayerValidation | [Specs/SettlementLayerValidation.lean](Specs/SettlementLayerValidation.lean) | [Properties/SettlementLayerValidation.lean](Properties/SettlementLayerValidation.lean) | [Proofs/SettlementLayerValidation.lean](Proofs/SettlementLayerValidation.lean), invariant and step lemmas in [Proofs/SettlementLayerValidationSteps.lean](Proofs/SettlementLayerValidationSteps.lean) |

Namespace `Contracts.L1ChainAssetHandler.SettlementLayerValidation`. Statements are
`Contracts.L1ChainAssetHandler.SettlementLayerValidation.Properties.*`; each certificate has the
same name without the `Properties` segment. No statement takes a hash premise.

## The model

`isValidSettlementLayer` is transcribed as a scan over the intervals it visits
(`scanIntervals`). Around it, `ValState` holds one migrating chain `c`: L1's `migrationNumber[c]`
and `_migrationInterval[c]`, L1's message-root counters of `c` and of every settlement layer,
`c`'s L1 diamond (`totalBatchesExecuted`, whether it settles elsewhere), `c`'s diamond and
message-root entry on each settlement layer, each layer's handler `migrationNumber[c]` and open
batch, one migration message in each direction, and two ghosts: where each executed batch ran
(the layer and, on a settlement layer, the layer batch open at the time), and how many batches
ran. `valStep` has ten labels: a batch executed on L1 or on a layer, a layer sealing its batch,
L1 executing a layer's next batch, L1's `bridgeBurn`, the layer's `bridgeMint`, the failure of
that transaction, L1's `bridgeConfirmTransferResult` of the failure, the layer's `bridgeBurn`
back, and L1's `bridgeMint` of the return. A revert is `none`. Reject-only checks are dropped,
so the model admits more runs than the contracts.

The environment `ValEnv` has two switches: L1 executes only sealed layer batches
(`sealedOnly`), and the return message is finalized only after the layer batch containing the
burn was executed on L1 (`finalizedAfterExec`). `ValEnv.real` has both. `ValWorld` fixes L1's
chain id, `c`, the whitelist and `CHAIN_MIGRATIONS_ENABLED` (`false` at this commit). Start
states (`ValInit`) are chains that settle on L1 and have never migrated, with both L1 counters
equal.

## Results

- **The function.** With `migrationNumber ≤ 2` and an uninitialized index-2 interval the loop is
  a closed form over interval 1 (`IsValidUnrolled`); the head never reads index 0, and `main`'s
  loop agrees with it unless the index-0 interval is initialized (`LegacyIndexZero`). No step
  writes index 0, so on the model's runs from a state without a legacy interval the two loops
  agree throughout (`MainAgreesWithoutLegacyInterval`).
- **The executed log.** On every reachable state the call never reverts
  (`ReachableNeverReverts`), the executed batches are exactly `1 .. total`
  (`ExecutedLogContiguous`), and no recorded batch is rewritten (`ExecutedBatchNeverRewritten`).
  The two L1 counters of the chain agree, and while its L1 diamond settles elsewhere
  `migrationNumber` is 1 (`CountersEqualAndAwayMeansMigrationOne`).
- **Soundness, exactly.** In a world where chain id 0 is not whitelisted, for every executed
  batch the call accepts `(X, k)` iff `X` is the layer that executed it and, off L1, `k` is at
  least interval 1's lower bound and, once the interval is closed, at most its upper bound
  (`ExecutedBatchAnswer`); so an accepted claim names the executing layer
  (`ExecutedBatchSound`). These hold in every environment.
- **The bounds.** A batch executed off L1 ran on interval 1's layer, in
  `(migrateToGWBatchNumber, migrateFromGWBatchNumber]`; under `sealedOnly` the lower bound is
  strictly below the layer batch open at its execution, and under `finalizedAfterExec` that batch
  is at most the upper bound (`SLBatchWithinBounds`). Conversely every executed batch in that
  range ran on interval 1's layer (`IntervalBatchesRanOnLayer`).
- **Completeness.** In the real environment the call accepts the executing layer with that layer
  batch and with every later one up to the upper bound (`ExecutedBatchComplete`).
- **Failure and the head.** After a confirmed failure the call accepts exactly the claims naming
  L1 (`FailureClassifiesAllOnL1`). With migrations disabled, from any state, the classification
  state is unchanged or reset by one failure confirmation, so every accepted claim naming another
  layer was accepted at the start (`MigrationsDisabledOnlyHistoricalIntervals`); from a start
  state every batch runs on L1 (`MigrationsDisabledEveryBatchOnL1`).
- **What the premises do.** Without `sealedOnly` the claim at the layer batch open at execution
  can be rejected (`CompletenessNeedsSealedOnly`); without `finalizedAfterExec` the upper bound
  can lie below it (`CompletenessNeedsFinalizedAfterExec`); a whitelisted chain id 0 would be read
  as an uninitialized interval (`SoundnessNeedsNonzeroLayerIds`). The lower bound is not tight:
  a layer batch below the first one containing the batch is accepted, and only the inclusion
  proof that follows the call can reject it (`ClaimBelowFirstContainingBatchAccepted`).
- **Witnesses.** `RoundTripWitness` (L1 → layer 5 → L1 with batches on both layers and bounds
  `[1, 3]`), `FailedMigrationWitness`, `MigrationsDisabledWitness`.

## Not covered

- The inclusion proof after the call (`L1MessageRoot.sol:111-119`) and the Merkle structure of
  the roots. Reading the open layer batch as the first one whose root contains the batch assumes
  each layer batch commits the layer's message root as of its end (the layer's system contracts).
- Start states with migration history (legacy Era Gateway intervals, a chain that already
  migrated) and chains whose two L1 counters differ; the head corollary
  `MigrationsDisabledOnlyHistoricalIntervals` takes any state.
- Other chains, except through a layer's batches and L1's counter of them; a whitelist that
  changes during a run; settlement layers that do not run this code.
- Storage, ABI and call correspondence (`MODEL-SL-VALIDATION` in [ASSUMPTIONS.md](../../../ASSUMPTIONS.md)).
