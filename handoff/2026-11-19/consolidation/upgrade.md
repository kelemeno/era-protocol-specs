# Consolidation inventory: the upgrade unit

Unit contracts: `ProxyUpgradeExecutorBase`, `SecondProofSystem`, `ProxyUpgradeRowLib`,
`RegistryBootstrapMigration`, `EcosystemUpgradeExecutor`. Branch `consol9/upgrade`, from
`claude/proof-round-9` at `35d2eb9`. Target commit: era-contracts `draft/v0.35.0` head
`b17415d20` (`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`).

`e561b9cc2` is not in the local era-contracts clone. The re-pins below from `e561b9cc2` therefore
compare each Specs file's own transcription of the `e561b9cc2` code with the source at
`b17415d20`, not the two trees.

"Importers" lists every module outside the topic's own Specs/Properties/Proofs triple that imports
it (a grep of `EraSpec/`). Every topic's Proofs module is also imported by `EraSpec.lean`. No
`Protocol/` file imports any module of this unit.

## ProxyUpgradeExecutorBase

Source: `upgrades/registry/executors/ProxyUpgradeExecutorBase.sol`, the two domain executors,
`engines/DefaultProxyUpgradeEngine.sol`. Five topics, five independent models of the same leg
(`_applyProxyUpgradeTransition`, `:51-104`, and `_domainHolders`, `:118-148`).

| Topic | Commit (verified) | Model | Imports / importers | Decision |
|---|---|---|---|---|
| CoreLegV35 | `b17415d20` (first `d9f678900`) | `CoreLeg.World` (executor owner and pending owner, `ProxyAdmin` owner, per-proxy implementation and admin slots), `Exec`, `EngineSem`, `applyProxyUpgradeTransition`; Core domain only, CTM branch opaque | imports `ProxyUpgradeRowLib` `RowsCurrent` (Specs, Proofs); no importers | re-pin (citations checked; no change needed) |
| DomainHoldersV35 | `b17415d20`; contains the `d9f678900` leg as `D9` | `World` (executor ownership, `ProxyAdmin` owner, per-proxy `Tup`, implementation answers, CTM and notifier fields), `Bindings`, `Engine`, `leg`; both domains | none / none | **canonical leg model**; the `D9` namespace is a pin record of `d9f678900` and moves to `History` with the properties that use it |
| EngineLegV35 | `b17415d20` (first `d9f6789`) | abstract `Env σ κ` (arbitrary getters, `CallRun`), `Leg`; concrete `WState`/`WStep` world | imports `RowsCurrent`, `InteropDataEncoding` `BundleHashEncoding`/`BundleHashPinned`; no importers | re-pin (checked); step 2 deferred, see below |
| ExecutorOwnerCallsV35 | `b17415d20` (first `d9f6789`) | CTM executor `State`, `Frame`, `FwdStep`, `EngStep` over `ChainTypeManager` `VersionRegistry` | imports `ChainTypeManager` `VersionRegistry`; no importers | re-pin (checked); step 2 deferred |
| NotifierBindingV35 | `b17415d20` | `State` (CTM store, notifier stores), `Step`, `Run`, `DomainRun`, `LegAccepted` | imports `ChainTypeManager` `UpgradeTiming` (`e561b9cc2`, CTM unit); no importers | re-pin (checked); step 2 deferred |

Step 2 for this contract is **not done** in this wave. The five models differ in what they make
state (CoreLeg: Core domain, world-dependent implementation answers, reinitializers that write
both slots; DomainHolders: both domains, per-proxy answers; EngineLeg: an arbitrary getter
environment plus call traces; ExecutorOwnerCalls: the CTM's version state and `forward`;
NotifierBinding: the notifier stores and the chain-scheduling gate). A simulation between any two
of them needs a projection of one world onto the other and a restriction of the engine classes
(for example CoreLeg's `implAnswer` depends on the world, DomainHolders' does not). Each is a
proof project of its own; none was attempted here. The README's "Related topics" paragraph names
the overlapping results.

## SecondProofSystem

| Topic | Commit (verified) | Model | Imports / importers | Decision |
|---|---|---|---|---|
| FlagAuthorityV35 | `b17415d20` (first `d9f678900`) | one diamond: `St`, `Call`, `Init`, `ReachWith`/`Reach`/`ReachEnvs` | none / none | **canonical** (the diamond) |
| MigrationV35 | `b17415d20` (Solidity byte-identical to `d9f678900`) | one chain, two diamonds (`Diamond`, `Sys`), `DCall`, `Call`, `Run` | none / DiamondRefinement | keep; refinement lemma onto FlagAuthorityV35 (see below) |
| UpgradeGateV35 | `b17415d20`, over `ChainTypeManager` `UpgradeTiming` (`e561b9cc2`) | `GateConfig`, `GState`, `GSys`, `GStep`, `GRun` extending `TimedSys` | imports `ChainTypeManager` `UpgradeTiming`, `Enabledness`; no importers | keep; it extends the CTM unit's model and is consolidated with it |

Step 2, done in part: the new topic DiamondRefinement maps MigrationV35's diamonds and diamond
calls onto FlagAuthorityV35 (`DiamondStepRefines`: every successful `dstep` is a successful
FlagAuthorityV35 `step` of the same entry point on the projection) and derives MigrationV35's
one-diamond facts from FlagAuthorityV35's theorems (`DiamondFlagMonotoneStep`,
`DiamondMaskWrittenOnlyBySetStatus`, `DiamondZiskOffOnFlaggedIsOwners`). MigrationV35's own
system (two diamonds, migration, `interopEnabled`) has no counterpart in FlagAuthorityV35, so its
model stays; its run proofs still use its own `dstep_frame`. UpgradeGateV35 extends the CTM
unit's model and is not related by a theorem.

## ProxyUpgradeRowLib

| Topic | Commit (verified) | Model | Imports / importers | Decision |
|---|---|---|---|---|
| Rows | `612a71ccc` | `Contracts.ProxyUpgrade`: `Row` with `admin`, `ApplyRow`, `ApplyRows`, `ValidRows` | none / none | **History** (pin record: the row `admin` field and the later-transaction gate are gone) |
| RowsStrong | `612a71ccc` | predicates over Rows | imports Rows / none | **History** |
| RowsCurrent | `e561b9cc2` | `Contracts.ProxyUpgradeCurrent`: `Row`, `Config`, `ApplyRow`, `ApplyLoop`, `ApplyRows`, `ValidRows`, `Transition`, `ApplyTransition` | none / `ChainTypeManager` `ExecutorForward` (Specs, Proofs), `ProxyUpgradeExecutorBase` `CoreLegV35`, `EngineLegV35` | **canonical**; re-pin to `b17415d20`: `applyRows` reads and swaps as before, the verification pass is now the function `requireRowsApplied`; `applyTransition` is gone, so `ApplyTransition` is re-described as the transition checks of the leg followed by the default engine's `applyRows` |
| RowsUnvalidated | `e561b9cc2` | `Transition.Genuine` and witness data over RowsCurrent | imports RowsCurrent / `ChainTypeManager` `ExecutorRowsUnvalidated`, `ExecutorEngineAtV35` | re-pin |
| RowsOrder | `e561b9cc2` | predicates over RowsCurrent | imports RowsUnvalidated / none | re-pin |
| RowsCurrentStrong | `e561b9cc2` | `LocalSwap`, `RowApplies` over RowsCurrent | imports RowsOrder / none | re-pin |
| RowsAdminSlot | `e561b9cc2`, OZ `dc44c9f` | `Contracts.ProxyUpgradeCurrent.AdminSlot`: two ERC-1967 slots, admin dispatch | imports RowsCurrent / none | re-pin; already a proved refinement of RowsCurrent (`LiftedCallIsRowsCurrentCall`, `ApplyRowsCorrespond`) |

After the move one Specs model remains (RowsCurrent), with RowsAdminSlot as its refinement.

## RegistryBootstrapMigration

| Topic | Commit (verified) | Model | Imports / importers | Decision |
|---|---|---|---|---|
| Authority | `e561b9cc2` | `AState`, `MigrateStep`, `Label`, `AStep`, `ARun` | none / none | **canonical**; re-pin to `b17415d20` (logic unchanged; manifest field `upgradeEngine` renamed `chainUpgradeEngine`; line numbers moved) |
| Forward | `e561b9cc2` | `Op`, `OpStep`, `FRun`, `XStep`, `XRun` over `AState` | imports Authority / none | re-pin (`forward` gained a code check on targets of calls with calldata, which only rejects) |
| AuthorityStrong | `e561b9cc2` | witness data over Forward | imports Forward / none | re-pin |
| AuthorityEngineV35 | `b17415d20` | `VState` extends `AState`, reuses `MigrateStep`/`OpStep`; `EngineLeg`, `VSysRun` | imports Forward / none | re-pin (checked) |

Already one model: Forward and AuthorityEngineV35 extend Authority's state and steps.

## EcosystemUpgradeExecutor

| Topic | Commit (verified) | Model | Imports / importers | Decision |
|---|---|---|---|---|
| Lifecycle | `afa407085` | `Sys`, `Label`, `Step`, `Run` | none / none | **History** (the coordinator and its timer were deleted before `e561b9cc2` and are absent at `b17415d20`) |
| LifecycleStrong | `afa407085` | over Lifecycle | none / none | **History** |

## Files outside the unit that the moves touch

- `EraSpec.lean` (module list).
- `ChainTypeManager/README.md` mentions `../EcosystemUpgradeExecutor/` and `../ProxyUpgradeRowLib/`
  `Rows` (prose only).
- `ASSUMPTIONS.md`: rows that name renamed Lean declarations (`Contracts.ProxyUpgrade.*`). Only
  those names are updated.
