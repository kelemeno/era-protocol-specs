# Consolidation unit `ctm-a`: ChainTypeManager re-pin, slice A

Branch `consol9/ctm-a`, from `claude/proof-round-9`. HANDOFF consolidation step 1 only (one
target commit) for nine `ChainTypeManager` topics: `VersionRegistry`, `ChainRouting`,
`ChainMigration`, `ChainLocal`, `DiamondStorage`, `LiveRouting`, `DuplicateSelectorScan`,
`MutableSelectors` and `GenesisWriters`. Model unification, History moves and headline tags are
left to the unification unit. No Lean definition or statement changed; no Properties def was
removed or renamed (`../renames/ctm-a.json` is empty).

## Method

- Eight topics were written against `e561b9cc2` (`feat/upgrade-simplification` of the zksync-era
  `contracts` repository). Its `l1-contracts/contracts` tree is byte-identical to that of
  `ccf00623c` (the squash-merge into `draft/v0.35.0`), checked file by file. `MutableSelectors`
  was already written against `b17415d20`.
- Every file the topics cite was diffed between `e561b9cc2` and `b17415d20`. Each `file:line`
  citation was attributed to its file and moved through a line map built from that diff (only
  lines that are equal at both commits are mapped). The few that fell into changed lines were
  re-read by hand (`CTMRelease.sol`'s `_requireUniqueFacetRows` comment; the design-doc quote in
  `ChainLocal`). `MutableSelectors`' citations were checked against `b17415d20` directly.
- Every Specs header now names `b17415d20` and says what changed on its paths since `e561b9cc2`.

## What changed between `e561b9cc2` and `b17415d20` on the modelled paths

| File | Change | Effect on these topics |
|---|---|---|
| `state-transition/ChainTypeManager.sol` | `INTEROP_CENTER` immutable and constructor argument removed; one comment renamed `upgradeEngine` | lines only (−3 / −4 / −5) |
| `state-transition/chain-deps/facets/Admin.sol` | `_executeDiamondCut` ends with the second-proof-system check; `setProofSystemStatus` caller depends on the flag; new `permanentlyRequireSecondProofSystem`; `selectors()` one longer | reject-only on the modelled cut paths; noted in `ChainRouting`, `ChainLocal`, `GenesisWriters` |
| `upgrades/BaseZkSyncUpgrade.sol` | `_setVerifier` gains the second-proof-system check | reject-only; `GenesisUpgrade` passes verifier `0` and never reaches it |
| `state-transition/chain-deps/ZKChainStorage.sol` | new field `secondProofSystemRequired` (slot 70) | not in `GenesisWriters.AppStorage`; zero on a fresh diamond |
| `state-transition/chain-deps/facets/Getters.sol`, `ZKChainBase.sol` | `isSecondProofSystemRequired`, `_getProofMode` | lines only |
| `upgrades/registry/objects/CTMRelease.sol` | constructor refuses zero facet addresses (it skipped them), an empty facet set (own error), a wrapped-base-token L2 row and non-canonical bytecode infos; `validate()` unchanged | lines only; see note 2 |
| `upgrades/registry/objects/CTMTransition.sol` | `upgradeEngine` renamed `chainUpgradeEngine`; L2-table comparison member-wise (`_l2TableChanged`) | rename in `ChainRouting`'s prose; the L2-table change is outside this slice |
| `upgrades/registry/RegistryTypes.sol`, `CTMUpgradeComposer.sol`, `RegistryBootstrapMigration.sol` | rename `chainUpgradeEngine`; new `ProxyUpgradeContext` and `proxyUpgradeEngine` | lines only |
| `upgrades/registry/executors/CTMUpgradeExecutor.sol` | now `ProxyUpgradeExecutorBase`; infrastructure leg through an engine | `_requireTransitionApplied` unchanged, lines +5 |
| `upgrades/DefaultUpgrade.sol` | doc comment only | lines −1 |
| `core/bridgehub/BridgehubBase.sol`, `deploy-scripts/ctm/DeployCTMUtils.s.sol` | one-line changes elsewhere | cited lines unchanged |
| `Diamond.sol`, `DiamondProxy.sol`, `DiamondInit.sol`, `LiveRoutingReader.sol`, `ReleaseFacetReader.sol`, `TransitionDerivationLib.sol`, `BootstrapUpgrade.sol`, `L1GenesisUpgrade.sol`, `BaseZkSyncUpgradeGenesis.sol`, `Migrator.sol`, `ChainAssetHandlerBase.sol` | unchanged | none |

The only diamond-routing writers at `b17415d20` are the same as at `e561b9cc2`: the
`DiamondProxy` constructor, `DiamondInit`, `Admin.sol:586/594/608` through `_executeDiamondCut`,
and `_applyDerivedFacetCuts` in `DefaultUpgrade`/`BootstrapUpgrade`.

## Notes for the unification unit (no Specs definition changed)

1. **Second-proof-system check.** `Admin._executeDiamondCut` (`Admin.sol:117-128`) now reverts,
   for a chain with `secondProofSystemRequired`, unless the verifier reports the multi-proof
   mode. Every model here omits it as a reject-only check, which keeps the safety results. The
   repair step of `ChainLocal` and the enabledness results (`RepairEnablesTransition`, the
   `GenesisWriters` exactness/enabledness results) are "in the model"; this is one more
   source-side condition they do not check. `GenesisWriters.AppStorage` has no
   `secondProofSystemRequired` field; adding it (zero on `ChainState.fresh`, written by nothing on
   the creation path) would make `Admin.genesisUpgrade`'s transcription exact again. The flag is
   modelled in `SecondProofSystem`/`ProofGateAtV35` (other units).
2. **`CTMRelease` constructor.** It now also refuses a zero facet address. `GenesisWriters.ReleaseWf`
   and `LiveRouting.ReleaseValid` both state what `CTMRelease` checks; neither needs to change
   (`ReleaseValid.facetsNonzero` and `ReleaseWf.facetsHaveCode` already follow from `validate()`'s
   code check), but a shared release-wellformedness predicate could cite both.

## Per topic

Importers are Lean imports at the branch point. "Direct" lists modules importing the topic's
Specs or Proofs module; "transitively" lists further topics reached.

### VersionRegistry
- **Pin:** `e561b9cc2` → `b17415d20` (lines only).
- **Model types:** `Address`, `Selector`, `Route`, `ReleaseRows`, `TransitionView`, `World`
  (`World.Genuine`), `LegacyCut`, `CTM`, `Op`, `CStep`, `CRun`, `CtmInv`, `initState`,
  `bootstrapState`; witness world `wWorld`.
- **Imported by:** CTM `ChainRouting`, `CommittedEdgeExecutable`, `DuplicateSelectorCheck`
  (proofs), `L2Convergence` (proofs); transitively every CTM topic. Outside CTM:
  `ProxyUpgradeExecutorBase.ExecutorOwnerCallsV35` directly; `ProxyUpgradeExecutorBase.NotifierBindingV35`,
  `SecondProofSystem.UpgradeGateV35`, `Diamond.DiamondProxy` transitively.
- **Duplication:** it is the base CTM version-state model; `ExecutorForward`, `UpgradeTiming` and
  the `…AtV35` topics extend it rather than re-model it. Recommendation: **keep as the shared CTM
  model** (it is the most complete model of `protocolVersion`/`currentRelease`/`upgradeTransition`).

### ChainRouting
- **Pin:** `e561b9cc2` → `b17415d20` (lines; `chainUpgradeEngine` rename; reject-only check noted).
- **Model types:** `Routing`, `rowsRouting`, `removeSel`/`addSel`/`removeAll`/`addAll`,
  `applyDerived`, `Chain`, `ChainId`, `Sys`, `Label`, `Step`, `Run`, `UnguardedCrossing`,
  `ChainOk`, `SysInv`; witnesses `bgExtra`, `bgMissing`, `wSys0`, `wBootSys`.
- **Imported by:** CTM `ChainMigration`, `DiamondStorage`, `Enabledness`, `ExecutorForward`,
  `GenesisWriters`, `L2Convergence`; transitively most CTM topics. Outside CTM (transitively):
  `Diamond.DiamondProxy`, `ProxyUpgradeExecutorBase.NotifierBindingV35`,
  `SecondProofSystem.UpgradeGateV35`.
- **Duplication:** the abstract chain-routing model. `LiveRouting.DStep` re-models it over diamond
  storage with refinement lemmas (`CountedStepRefinesStep`, `CountedRunRefinesRun`), and
  `GenesisWriters.CodeStep` refines its creation steps (`CodeStepIsExact`, `CodeRunIsARun`).
  Recommendation: **keep as the abstraction layer**; the shared concrete model should be
  `LiveRouting`'s, with these refinements as the bridge.

### ChainMigration
- **Pin:** `e561b9cc2` → `b17415d20` (lines only).
- **Model types:** `MSys` (adds `away`), `MLabel`, `MStep`, `MRun`, `MLabel.writesDiamond`.
- **Imported by:** CTM `ChainLocal`; transitively `ChainLocalExecutor`, `EngineGettersFaithful`,
  `LegacyCrossingFaithful`, `ProofGateAtV35`, `UpgradeTimingAtV35`. Nothing outside CTM.
- **Duplication:** extends `ChainRouting` (every routing step kept). Recommendation: **keep**, an
  extension, related by `ChainLocal.MigrationRunIsARoutingRun`.

### ChainLocal
- **Pin:** `e561b9cc2` → `b17415d20` (lines; doc quote moved to `docs/registry-driven-upgrades.md:785-786`).
- **Model types:** no new state or step; `Label.writesChain`, `LastWriteNotBreakGlass`,
  `repairCut`, `MLabel.base?`; witness world `wDupWorld`.
- **Imported by:** CTM `ChainLocalExecutor`, `ProofGateAtV35`; transitively
  `LegacyCrossingFaithful`, `EngineGettersFaithful`, `UpgradeTimingAtV35`. Nothing outside CTM.
- **Duplication:** none. Recommendation: **keep**.

### DiamondStorage
- **Pin:** `e561b9cc2` → `b17415d20` (unchanged code; one `BaseZkSyncUpgrade` line moved).
- **Model types:** `SelectorToFacet`, `FacetToSelectors`, `DiamondStorage` (no `isFrozen`),
  `saveFacetIfNew`, `addOneFunction`, `addFunctions`, `replaceFunctions`, `removeFunctions`,
  `CutAction`, `FacetCut`, `facetCut`, `diamondCut` (facet-cut loop), `DiamondOk`.
- **Imported by:** CTM `LiveRouting` (and through it `DuplicateSelectorScan`, `MutableSelectors`);
  outside CTM `Diamond.DiamondProxy` (Specs and Proofs), which reuses it unchanged and adds
  `isFrozen`, the init call and the proxy fallback.
- **Duplication:** **`GenesisWriters` transcribes the same `Diamond.sol` code independently**
  (`GenesisWriters.SelectorToFacet`, `FacetToSelectors`, `DiamondStorage` with `isFrozen`,
  `addOneFunction`, `addSelectors`, `removeOneFunction`, `removeFacet`, `replaceSelectors`,
  `applyFacetCuts`, `initializeDiamondCut`, `diamondCut`), and `Diamond.DiamondProxy` adds a third
  view of the init call (`diamondCutFull`). Recommendation: **unify** on this file's storage plus
  `Diamond.DiamondProxy`'s additions; restate `GenesisWriters` over them, or first prove a
  refinement lemma (`GenesisWriters.applyFacetCuts` projected without `isFrozen` equals
  `DiamondStorage.diamondCut`, both reverting together).

### LiveRouting
- **Pin:** `e561b9cc2` → `b17415d20` (lines only; quote of `CTMRelease.sol:214-218` updated to the
  new comment wording).
- **Model types:** `FacetRow`, `flattenRows`, `DWorld` (`toWorld`, `rows`), `RowsWf`,
  `ReleaseValid`, `CountCheck`, `newChainInstallations`, `deriveFacetCuts`, `DChain`, `DSys`,
  `DLabel`, `Op.installs`, `DStep`, `DRun`, views to `ChainRouting`, `StoreInv`, `DSysInv`;
  countermodel data `cmSelectors`, `cmRows`, `cmRepeatedRows`, `cmCuts`, `cmStore`.
- **Imported by:** CTM `DuplicateSelectorScan`, `MutableSelectors`; outside CTM
  `Diamond.DiamondProxy` (Specs and Proofs).
- **Duplication:** the concrete routing model; refines `ChainRouting` (see above).
  `GenesisWriters.Env`/`releaseRows` and `MutableSelectors.MutWorld` re-state its `DWorld`
  (releases as facet rows plus `selectors()`); `MutableSelectors` has explicit bridges
  (`MutWorld.at`, `StableRunIsACountedRun`, `CountedRunIsAStableRun`), `GenesisWriters` does not.
  `GenesisWriters.ReleaseWf` and `Enabledness.ReleaseWf` re-state `ReleaseValid`/`RowsWf`.
  Recommendation: **make `LiveRouting` the shared concrete model** of chain routing; add a
  projection `GenesisWriters.Env → DWorld` with `releaseRows = DWorld.rows`, and one shared
  release-wellformedness predicate with equivalence lemmas for the other two.

### DuplicateSelectorScan
- **Pin:** `e561b9cc2` → `b17415d20` (code unchanged, lines +48).
- **Model types:** `scanEntry`, `scanProbe`, `scanLoop`, `NoDuplicateScanPasses`,
  `ValidateRowsPasses`.
- **Imported by:** nothing but its own Properties/Proofs.
- **Duplication:** **`DuplicateSelectorCheck` (other slice) transcribes the same function**
  (`_requireNoDuplicateSelectors`) over `Enabledness.ReleaseWf` (`probeSlot`, `insertSelector`,
  `insertSelectors`, `insertRouting`, `noDuplicateSelectors`). Recommendation: **unify**: prove
  `NoDuplicateScanPasses ↔ noDuplicateSelectors` on the same input, keep one transcription, and
  move the other's properties (`DuplicateCheckIsExact`, `DuplicateCheckExactForAnyLargerTable`,
  `ReleaseWfIsTheDuplicateCheck` / `DuplicateScanIffNodup`, `ValidateRowsIffRowsWf`,
  `CountCheckExactAfterValidate`) onto it.

### MutableSelectors
- **Pin:** already `b17415d20`; header updated now that the topics it reuses are re-pinned. All its
  citations were checked at `b17415d20`.
- **Model types:** `MutWorld` (`at`, `FrozenUnder`, `GenuineUnder`, `ofDWorld`), `MutSys`,
  `MutLabel`, `MutStep`, `MutRun`, `StableSelectors`, `StableSelectorsOn`, `MutLabel.records`;
  adds `DecidableEq FacetCut`.
- **Imported by:** nothing but its own Properties/Proofs.
- **Duplication:** relaxes `LiveRouting`'s fixed-`selectors()` assumption, with refinements both
  ways under `StableSelectors`. Recommendation: **keep separate** (it is a countermodel family for an
  assumption, not a second model of the same behaviour).

### GenesisWriters
- **Pin:** `e561b9cc2` → `b17415d20` (lines; second-proof-system check documented as omitted;
  `ZKChainStorage` struct range corrected to `:74-305`).
- **Model types:** its own diamond layer (see `DiamondStorage`), `AppStorage`, `ChainState`,
  `InitCalldata`, `DiamondCutData`, `ProxyCall`, `Code`, `GenesisFacet`, `Env`, `releaseRows`,
  `diamondInitialize`, `l1GenesisUpgradeRun`, `runInit`, `adminGenesisUpgrade`, `pauseDeposits`,
  `migratorForwardedBridgeMint`, `runFacet`, `proxyCall`, `deployNewChain`, `createNewChain`,
  `migrateInNewChain`, `CodeCreation`, `CodeStep`, `CodeRun`, `GenuineRelease`, `ReleaseWf`,
  `RoutesTo`; witness data `gWorld`, `gSys0`.
- **Imported by:** CTM `MutableSelectors` (proofs only). Nothing outside CTM.
- **Duplication:** its diamond layer duplicates `DiamondStorage` and `Diamond.DiamondProxy` (above);
  its proxy dispatch (`proxyCall`) duplicates `Diamond.DiamondProxy.fallbackTarget`; `AppStorage`
  overlaps `AdminFacet.State`'s slice of `ZKChainStorage`. Recommendation: **unify** the diamond
  layer and proxy onto `DiamondStorage` + `Diamond.DiamondProxy` (refinement lemma first), keep the
  creation-path code (`diamondInitialize`, `l1GenesisUpgradeRun`, `CodeStep`) as this topic.
