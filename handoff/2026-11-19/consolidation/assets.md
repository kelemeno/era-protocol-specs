# Consolidation inventory: assets (L2AssetTracker, NativeTokenVaultBase, L1NativeTokenVault)

Unit `assets`, branch `consol9/assets` from `claude/proof-round-9` (`35d2eb9`). Target commit:
era-contracts `draft/v0.35.0` head `b17415d20`. The pin `c67894b9` source was read from a local clone that
has it (`git show`); `b17415d20` from the extracted tree.

## What the sources say (pin `c67894b9` against `b17415d20`)

- `bridge/ntv/NativeTokenVaultBase.sol`: with comments removed, only renames (`_assetRouter` ->
  `_getAssetRouter`, `_l1ChainId` -> `_getL1ChainId`, `_baseTokenAssetId` -> `_getBaseTokenAssetId`,
  `_wethToken` -> `_getWethToken`, locals `originToken` -> `parsedOriginToken`/`resolvedOriginToken`,
  `tokenAddress` -> `parsedTokenAddress`, `originChainId` -> `tokenOriginChainId`), one new import, and
  `_disburseFailedTransfer` made `virtual`. Some comments the pin models quote are gone: the three
  "It is assumed ... atomically populated" notes are rephrased; the `bridgeMint` NatSpec "assetIdcheck
  must be performed" and "no on-chain per-chain balance enforcement", and the two `setLegacyTokenAssetId`
  comments, are removed.
- `bridge/ntv/L2NativeTokenVault.sol`: bridged tokens are deployed with `Create2.deploy` instead of the
  `ContractDeployer` system call; the `_ensureAndSaveTokenDeployed` override is gone (the base one is
  used); `updateL2` checks a frozen `BASE_TOKEN_ASSET_ID`; and `_disburseFailedTransfer` is overridden
  to call `L2AssetTracker.assertRecoveryIsAccountingNeutral` first and to refund the base asset through
  `BaseTokenHolder`. The two tracker hooks are unchanged.
- `bridge/asset-tracker/L2AssetTracker.sol`: `backFillZKSyncOSBaseTokenV31MigrationData`,
  `registerBaseTokenDuringUpgrade` and `initL2`'s backfill flag are gone; `assertRecoveryIsAccountingNeutral`
  and `assertBaseTokenRecoveryIsAccountingNeutral` are new. Every other function is the same code.
- `bridge/ntv/L1NativeTokenVault.sol`: the per-chain ledger, the interop pool and `populateBridgedOut`
  are new; `bridgedOut`'s updates in the two hooks are the pin's, now next to the per-chain totals.

## Topics

"Importers" lists every file outside the topic's own three files that imports one of them.

### L2AssetTracker

| Topic | Commit modelled (checked) | Model | Importers | Decision |
|---|---|---|---|---|
| Accounting | pin `c67894b9` (header); the functions it models other than the backfill, `registerBaseTokenDuringUpgrade` and `initL2`'s flag are the same code at `b17415d20` | `Storage`, `Config`, `Sys`, `Op`, `exec`, `Step`, `Reach`, `Inv` (namespace `Contracts.L2AssetTracker`) | L2AssetTracker HookOrdering, LaterHeads; NativeTokenVaultBase TrackerHooks (Specs, Proofs) | **canonical** tracker model (state, functions). Re-pin: cite `b17415d20` lines; the header states that `Step` also has the three pin-only operations and that the `b17415d20` step is `HeadStep` (LaterHeads), whose runs are `Step` runs. Pin-only results `BackfillOnlyBaseFromZero`, `BackfillAtMostOnce`, `BackfillSatisfiable` -> **History**. |
| HookOrdering | pin (header) | `VaultPath`, `runPath`, `runPathEffectFirst` on the Accounting model and the token model | NativeEscrow, LaterHeads | **canonical**; re-pin lines (the vault paths and the hook order are the same code). |
| NativeEscrow | pin (header) | `EscrowSys`, `EscrowStep`, `EscrowInv` over Accounting and the token model | LaterHeads | **canonical**; re-pin lines (`HeadEscrowStep` runs are `EscrowStep` runs, `HeadEscrowRunIsEscrowRun`). |
| LaterHeads | `b17415d20` (and `main` `70096e2ea`) | `HeadOp`, `execHead`, `HeadStep`, `HeadEscrowStep`, `RecoveryAccountingNeutral`, `headRecover` | none | **canonical** `b17415d20` step relation of the tracker model; its refinement lemmas `HeadRunIsPinRun`, `HeadEscrowRunIsEscrowRun` already exist. |
| RecoveryNeutrality | `b17415d20` | own `Tracker`, `Sys` (tracker, vault maps, handler, holder, ghost log), `Op`, `Guards`, `run`, `runNested` (namespace `...RecoveryNeutrality`) | none | **refinement-lemma**: a second, richer model of the same tracker code together with the vault, router, holder and flow manager. Restating its 27 properties over the canonical model is impractical: they need the vault maps, the holder and the log, which the canonical model fixes in `Config` or lacks. New topic `RecoveryNeutralityRefinement` proves each of its tracker functions is the canonical one on the projected storage, and its vault recovery check is `RecoveryAccountingNeutral`. Kept. |

### NativeTokenVaultBase

| Topic | Commit modelled (checked) | Model | Importers | Decision |
|---|---|---|---|---|
| RepresentationPreparation | pin (header) | `Config`, `Registry`, `State`, `Hooks`, `prepare`, `transact`, `WellFormed` (namespace `Contracts.NativeTokenVaultBase`) | AssetRouterBase AtomicRecovery (and Faithful, AtHead), PausedRecovery; Codegen VaultPreparationSlice; Protocol AssetBridgePreparation Model; this folder | **canonical** per-token vault model; header cites `b17415d20`. |
| Initialization | none cited | `RegistrationState`, `registerRepresentation`, `registerFreshBranch` | Protocol AssetBridgePreparation; this folder | canonical (part of the per-token model); header cites `b17415d20`. |
| PreparationGuards | none (properties only) | uses RepresentationPreparation | Codegen Witnesses; Pause | canonical. |
| Resolution | pin | `ResolutionCall`, `ResolutionHooks`, `bridgeMint`, `bridgeRecoverFailedTransfer`, `bridgeMintFirst` | Pause, ResolutionCorrespondence, TrackerHooks; Protocol AssetBridgePreparation Resolution | canonical; re-pin lines; the header states the L2 recovery guard and base-asset route at `b17415d20` (modelled in LaterHeads `headRecover`). |
| Reinitialization | pin | `trackedStorage`, `MetaHooks` | Protocol AssetBridgePreparation Reinitialization | canonical; re-pin lines. |
| Pause | pin | `vaultPause`, `VaultEntryCall` | none | canonical; re-pin lines. |
| LegacyFallback | pin | `prepareLegacy`, `LegacyIdBreak` | none | canonical; re-pin lines; the pin's `setLegacyTokenAssetId` comments are gone at `b17415d20` (README). |
| TrackerHooks | pin | `L1Ledger`, `l1ToChain`, `l1FromChain`, `L2Accounting`, `l2Hooks`, `HooksCancelModulo` | L2AssetTracker HookOrdering, LaterHeads; Codegen L1TrackerHooks | canonical for the L2 hooks (the L2 vault's hooks are the same code at `b17415d20`). The L1 hooks are the pin's `bridgedOut`-only hooks: the header states that at `b17415d20` they also write the per-chain totals and can revert on the per-chain cap; new refinement lemmas (L1NativeTokenVault `LedgerRefinement`) show every successful `b17415d20` hook (InteropPool) is the `L1Ledger` hook on `bridgedOut`. |
| RegistryAndEscrow | pin (quoted comments) | `Vault`, `World`, `Step`, `Reach`, `StepIn`, `ReachLog`, `Valid` (namespace `Contracts.NativeTokenVault`) | AssetRouterBase AtomicRecovery, VaultMintGate; DataEncoding AssetId; this folder | **refinement-lemma**: the whole-registry model, linked to the per-token model by `Corr` (ModelCorrespondence) and `lifecycleSimulation` (RegistrationUnified). Its ledger is `bridgedOut` without the per-chain totals; new lemmas (`LedgerRefinement`) show that the `b17415d20` hooks' successful calls on an L1-native asset make its `bridgeOut`/`bridgeIn` ledger updates. Re-pin header. `PerChainIsolationFails` (no per-chain enforcement: true of the pin's code; at `b17415d20` the L1 vault has the per-chain cap) -> **History**. The twelve `IdAssumptions` properties stay (vacuous and documented; not this unit's mandate). |
| ModelCorrespondence | pin | `Corr`, `RegistryOnlyGuards` | AssetRouterBase AtomicRecovery; DataEncoding AssetId; Protocol AssetBridgePreparation FullRecovery; this folder | existing refinement lemma between the two vault models; re-pin header. |
| RegistrationUnified | pin | `Step'`, `RepStep`, `LifecycleRel`, `SourceRegistrationInput` | Protocol AssetBridgePreparation RegistryCorrespondence; RegistrationUnifiedStrong | existing refinement (simulation) lemma; re-pin lines. |
| RegistrationUnifiedStrong | none cited | `LifecycleOp`, `LifecycleReachLog` | none | existing refinement; header cites `b17415d20`. |
| ResolutionCorrespondence | none (properties only) | uses Resolution and ModelCorrespondence | none | existing refinement lemma. |
| EscrowLedgerAtHead | `main` `70096e2ea` and `b17415d20` (lines were `main`'s) | `WorldAtHead`, `StepOpAtHead`, `ReachLogAtHead`, `UpgradeStartAtHead` | none | **refinement-lemma** (registry model plus `populateBridgedOut`); re-pin lines to `b17415d20`; `LedgerRefinement` relates a `populateBridgedOut` entry to InteropPool's. |

### L1NativeTokenVault

| Topic | Commit modelled (checked) | Model | Importers | Decision |
|---|---|---|---|---|
| InteropPool | `b17415d20` | `PoolSys`, `PoolCall`, `poolCall`, `PoolRun` (namespace `...InteropPool`) | BulkheadPoolSimulation | **canonical** L1 vault ledger model at `b17415d20`; lines checked. |
| BulkheadIsolation | `b17415d20` | `CapState`, `CapLabel`, `capStep`, `CapRun` (namespace `...Bulkhead`) | BulkheadPoolSimulation, BulkheadIsolationSteps | **refinement-lemma**: the same code transcribed separately with an origin map and release ghosts; `BulkheadRunsArePoolRuns` already proves its runs are InteropPool runs. Kept. |
| BulkheadPoolSimulation | `b17415d20` | `CapPoolCorr` | none | existing refinement lemma. |
| LedgerRefinement (new) | `b17415d20` | relates InteropPool's hooks and `populateBridgedOut` to NativeTokenVaultBase `L1Ledger` and the `Contracts.NativeTokenVault` ledger | none | new refinement lemmas. |

## Chosen models

- **Vault ledger (L1 `bridgedOut` and the per-chain totals):** L1NativeTokenVault `InteropPool`. The other
  `bridgedOut` models (NativeTokenVaultBase `TrackerHooks.L1Ledger`, `RegistryAndEscrow`'s ledger,
  `EscrowLedgerAtHead`, `Bulkhead`) are related to it by refinement lemmas.
- **Vault registry and per-token paths:** the NativeTokenVaultBase representation model (`State`, `prepare`,
  `bridgeMint`, `bridgeRecoverFailedTransfer`), with the whole-registry model `Contracts.NativeTokenVault`
  linked by the existing `Corr` and `lifecycleSimulation`. Not merged: the registry model covers every
  asset and the representation model one token's ledger, and other folders use each.
- **Tracker:** L2AssetTracker `Storage`/`exec` with `HeadStep` (LaterHeads) as the `b17415d20` step.
  `RecoveryNeutrality` is linked by `RecoveryNeutralityRefinement`.

## Not done in this unit

- No model is deleted: every second model has properties that need state the canonical one does not keep,
  and restating them would mean rebuilding the canonical model. The refinement lemmas are the link.
- The twelve vacuous `IdAssumptions` properties of `RegistryAndEscrow` are untouched (see `CRYPTO-ID`).
