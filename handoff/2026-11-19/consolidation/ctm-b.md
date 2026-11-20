# Consolidation inventory: ChainTypeManager, slice b

Slice topics (`EraSpec/Contracts/ChainTypeManager/{Specs,Properties,Proofs}/<topic>.lean`):
`Enabledness`, `DuplicateSelectorCheck`, `ExecutorForward`, `ExecutorUpgradeChain`,
`ChainLocalExecutor`, `EngineGettersFaithful`, `ExecutorEngineAtV35`, `LegacyCrossingFaithful`,
`ProofGateAtV35`. Branch `consol9/ctm-b`, from `claude/proof-round-9` at `35d2eb9`. Target
commit: era-contracts `draft/v0.35.0` head `b17415d20`. This slice does HANDOFF consolidation
step 1 only (re-pin); model unification, `History` moves and headline tags are left to the
unification unit.

## How the re-pin was checked

`e561b9cc2` is not in the local era-contracts clone. `ccf00623c` (the squash-merge of
`feat/upgrade-simplification` into `draft/v0.35.0`) is, and `ProofGateAtV35`'s header records
that `git diff ccf00623c e561b9cc2 -- l1-contracts/contracts` is empty. Every `e561b9cc2`
citation of this slice was checked to point at the quoted code in `ccf00623c`, then mapped to
`b17415d20` by a line alignment of the two versions of each changed file and re-checked by
content. Files with no change between the two commits kept their numbers (`Diamond.sol`,
`DiamondInit.sol`, `DiamondProxy.sol`, `BootstrapUpgrade.sol`, `LiveRoutingReader.sol`,
`TransitionDerivationLib.sol`, `ICTMUpgradeExecutor.sol`, `IAdminWithCut.sol`). Changed and
re-numbered: `ChainTypeManager.sol` (-5 after the constructor), `Admin.sol` (+31 around the
upgrade entry points), `CTMRelease.sol`, `CTMTransition.sol`, `DefaultUpgrade.sol`,
`BaseZkSyncUpgrade.sol`, `CTMUpgradeExecutor.sol`, `UpgradeExecutorBase.sol`, `ZKChainBase.sol`,
and the docs `docs/registry-driven-upgrades.md`, `protocol-docs/ecosystem-upgrade-coordination.md`.
The `c67894b9` citations of `LegacyCrossingFaithful` (the pre-v35 chain-side `Admin` facet, which
`b17415d20` does not contain) were checked against `c67894b9` in `zksync-era4/contracts` and kept.
`ExecutorEngineAtV35` and `ProofGateAtV35` were already at `b17415d20`; every citation was
re-checked and found correct.

No Lean definition or statement changed. Only module docstrings and comments did, so no property
was removed or renamed (`renames/ctm-b.json` is empty).

## Logic differences found (for the unification unit)

1. **`applyInfrastructureUpgrade` delegatecalls an engine** (#2654). `ExecutorForward.XStep.infra`
   (`ProxyUpgradeCurrent.ApplyTransition`, i.e. `applyRows` on the rows) is now exactly the leg of
   a transition that pins `DefaultProxyUpgradeEngine`, up to reject-only checks
   (`ExecutorEngineAtV35`'s `DefaultEngineLegIsAnInfraStep`, `InfraStepIsADefaultEngineLeg`).
   A leg of any other engine is not an `XStep`. `XStep` is imported by `UpgradeTiming` and
   `ExecutorRowsUnvalidated` (other slices), so it was not changed; the Specs and Properties
   headers of `ExecutorForward` and `ChainLocalExecutor` now say their run results are about
   `b17415d20` runs whose infrastructure transitions pin the default engine.
2. **`forward` requires code at a target with calldata** (`UpgradeExecutorBase.sol:39-44`).
   Reject-only; `FStep` unchanged (documented in `ExecutorForward`).
3. **The second-proof-system gate on the transition path** (`Admin._executeDiamondCut`,
   `Admin.sol:121-126`; `BaseZkSyncUpgrade._setVerifier`, `:143-148`). `ChainRouting.Step.transition`
   (other slice) omits it. It only rejects, so the safety results of `Enabledness`,
   `ExecutorUpgradeChain`, `EngineGettersFaithful` and `LegacyCrossingFaithful` stand; for
   liveness it is one more omitted check, now listed in `Enabledness`'s Specs header.
   `ProofGateAtV35` models it. If `ChainRouting` is re-pinned with the gate in its step,
   `Enabledness.TransitionEnabledIff` (and its relatives) gain the gate's condition as a premise,
   which `ProofGateAtV35.TransitionEnabledIff` already states.
4. **Release and transition object constructors** (`CTMRelease`: a zero facet now reverts instead
   of being skipped, no `L2WrappedBaseToken` row, canonical bytecode-info lengths;
   `CTMTransition`: L2 tables compared member by member). Not modelled by this slice (the objects
   are `World` data of `VersionRegistry`/`ChainRouting`, other slice). `CTMRelease.validate()` and
   `_requireNoDuplicateSelectors` are unchanged, so `DuplicateSelectorCheck` and `ReleaseWf` hold
   as stated.
5. **Renames only:** `TransitionManifest.upgradeEngine` -> `chainUpgradeEngine` (and the
   `ICTMTransition` getter); not a value any model of this slice reads.

## Per topic

"Importers" lists modules outside the topic's own triple that import any of its three modules
(a grep of `EraSpec/`); every Proofs module is also imported by `EraSpec.lean`.

| Topic | Modelled commit (verified) | Model types | CTM importers | Importers outside CTM | Re-models | Recommendation |
|---|---|---|---|---|---|---|
| Enabledness | `b17415d20` (was `e561b9cc2`; only line numbers changed, plus the omitted gate) | no state of its own: predicates over `ChainRouting.Sys`/`World` (`ReleaseWf`, `RecordedReleasesWf`, `ChainsOnWfReleases`, `Op.InstallsWf`, `DepartedBelow`, `ChainsAtDepartedVersions`), `Sys.crossEdge`, `Sys.deployNew`, witness worlds | `DuplicateSelectorCheck`, `LegacyCrossingFaithful`, `ProofGateAtV35` (Specs, Proofs), `UpgradeTimingStrong` (Specs, Proofs) | `SecondProofSystem/{Specs,Proofs}/UpgradeGateV35` | `ProofGateAtV35` restates the liveness results with the gate (`TransitionEnabledIff`, `UpgradesStayEnabled`, `ValidatedRunsKeepEverythingEnabled` exist in both) | **refinement lemma / unify**: make the gated `ProofGateAtV35` system the b17415d20 routing model and keep `Enabledness`'s results as the gate-free case (no chain requires the second proof system), linked by `ProofGateAtV35.E561RunsAreRunsWithoutTheRequirement`; not History (they are true of b17415d20 chains without the requirement) |
| DuplicateSelectorCheck | `b17415d20` (code unchanged) | `ProbeTable`, `probeSlot`, `insertSelector(s)`, `insertRouting`, `selectorTotal`, `noDuplicateSelectors` (a transcription of `_requireNoDuplicateSelectors`) | none | none | none; it is the bridge `ReleaseWfIsTheDuplicateCheck` between the transcription and `Enabledness.ReleaseWf` | **keep separate** (it is already the refinement lemma) |
| ExecutorForward | `b17415d20` for default-engine legs (was `e561b9cc2`) | `XConfig`, `XState` (= `ChainRouting.Sys` + `ProxyUpgradeCurrent.Impl`), `FCall`/`FStep`/`FRun`, `XLabel`/`XStep`/`XRun`, `FCall.Tame`, `XLabel.Tame`, `MovesOnlyAlongRows` | `ExecutorUpgradeChain`, `ChainLocalExecutor`, `ExecutorEngineAtV35` (Specs, Proofs), `UpgradeTiming` (Specs, Proofs), `ExecutorRowsUnvalidated` (Properties, Proofs), `ProofGateAtV35` (Proofs) | none (but `ProxyUpgradeExecutorBase/ExecutorOwnerCallsV35` is an independent model of the same executor over `VersionRegistry`, see the upgrade unit's inventory) | `ExecutorEngineAtV35` extends it (`V35State` contains `XState`) | **unify with ExecutorEngineAtV35**: the v35 executor step `V35Step` should be the executor model; keep `XStep` as its default-engine projection (the bridge lemmas exist). Unify `ExecutorOwnerCallsV35` into the same model or prove a simulation |
| ExecutorUpgradeChain | `b17415d20` (was `e561b9cc2`; only line numbers changed) | `ULabel`/`UStep`/`URun` (refines `XLabel.upgradeChain` by the transition-argument lookup and adds the admin's direct call), `ULabel.toX`/`ofX`, `ULabel.Tame`, `SlotsReport` | `EngineGettersFaithful`, `LegacyCrossingFaithful` (Specs, Proofs) | none | refinement of `ExecutorForward` (`URun` <-> `XRun` lemmas) | **refinement lemma, then unify**: fold `ULabel` into the unified executor label set |
| ChainLocalExecutor | `b17415d20` for default-engine legs (was `e561b9cc2`) | no new state: `FCall.sys?`, `FCall.KeepsCtmCode`, `XLabel.KeepsCtmCode`, `XLabel.sysLabels` over `ExecutorForward`; witness runs | `EngineGettersFaithful`, `LegacyCrossingFaithful` (Specs, Proofs) | none | lifts `ChainLocal` (other slice) to executor runs | **keep separate** until the executor model is unified, then restate on it |
| EngineGettersFaithful | `b17415d20` (was `e561b9cc2`; only line numbers changed) | namespace `EngineGetters`: `SelCut`, `applySel`, `applyCuts`, `derivedCuts`, `Engine` (the `facetCuts()`/`upgradeTarget()` getters), `EngineDerived`, `SlotsDerived`, `EStep`, `EFStep`/`EFRun`, `EUStep`/`EURun`, `FInstalls`, `Installs` | none | none | re-models `ChainRouting.Step.transition` with explicit engine getters, over `ExecutorUpgradeChain` | **refinement lemma**: keep as the faithfulness layer of the transition step (`EngineDerived` premise); when `ChainRouting` is unified, state its step as the `EngineDerived` case of `EStep` |
| ExecutorEngineAtV35 | `b17415d20` (first `d9f6789`) | namespace `ExecutorEngineAtV35`: `V35Transition`, `DomainHolders`, `V35State`, `EngineCode`, `EngineCore`, `V35Config`, `EngineIsDefault`, `EngineReviewed`, `EngineIsTame`, `V35Label`/`V35Step`/`V35Run`, `PostChecks`, `V35MovesOnlyAlongRows` | none | none (but `ProxyUpgradeExecutorBase/{DomainHoldersV35,CoreLegV35,EngineLegV35}` model the same leg independently; the upgrade unit names `DomainHoldersV35` canonical for the leg) | extends `ExecutorForward` | **unify**: the canonical CTM executor model; its leg should become a refinement of (or be restated over) the upgrade unit's canonical leg model `DomainHoldersV35` |
| LegacyCrossingFaithful | `b17415d20` CTM, `c67894b9` pre-v35 `Admin` facet (was `e561b9cc2` CTM) | namespace `LegacyCrossing`: `landAt`, `CrossStep`, `LLabel`/`LStep`/`LRun`, `LLabel.ExecTame`/`Tame`/`KeepsCtmCode`/`ForwardsReplace`/`sysLabels`, `CrossLandsOk`, `LRunOk` | none | none | adds the chain-side crossing of opaque legacy edges to `ExecutorUpgradeChain` | **keep separate** (not History: the legacy entry points are present at b17415d20, removed only by the unmerged v36 PR 2650); on unification, add `CrossStep` to the shared executor's other-actor labels |
| ProofGateAtV35 | `b17415d20` (first `d9f6789`) | namespace `ProofGateAtV35`: `ProofWorld`, `ProofState`, `ProofGate`, `arrivingVerifier`, `Sys35` (= `ChainRouting.Sys` + per-chain proof state), `ProofEffect`, `Label35`/`Step35`/`Run35`, `GateHolds`, `ProofInv`, `NoChainRequires` | `UpgradeTimingAtV35` (Specs, Proofs) | none (but `SecondProofSystem/UpgradeGateV35` is an independent model of the same gate, also over `ChainRouting`/`Enabledness`) | re-models `ChainRouting` + `Enabledness` with the gate (`StepIsTheE561StepPlusTheGate`, `RunIsARun`) | **unify**: the b17415d20 routing system (see `Enabledness`); merge or bridge `SecondProofSystem/UpgradeGateV35` onto it. Its docstrings still call `ChainRouting`'s step "the `e561b9cc2` step"; rename that wording (and `StepIsTheE561StepPlusTheGate`, `E561RunsAreRunsWithoutTheRequirement`, `E561RunLiftWitness`, recorded in a renames file) once `ChainRouting` is re-pinned |

## Notes

- `ExecutorEngineAtV35`'s docstrings name `XStep.infra` "the `e561b9cc2` infrastructure step".
  That is still accurate as a description of where the step came from, and the Specs header now
  says what it is at `b17415d20`; the unification unit may rename the wording.
- No headline tags were added: `EraSpec/Core/Headline.lean` had not landed on
  `claude/proof-round-9` during this run, and headlines are the unification unit's step.
