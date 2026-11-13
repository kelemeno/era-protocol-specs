# era-protocol-specs: proof backlog (Lean and Mathlib only)

Read-only survey of `/Users/samsara/code/era-protocol-specs` on branch `claude/port-lean-4.35`, working tree as of 2026-11-11. No file was edited and lake/lean was not run, so build status is not re-checked here. Solidity checkouts:
- `PIN` = era-contracts `c67894b9`, at `.../scratchpad/src/pinned-c67894b9/l1-contracts/contracts/`.
- `UPG` = `e561b9cc2`, at `.../scratchpad/src/upgrade-e561b9cc2/l1-contracts/contracts/`.

## Answers to the two handoff leads

### Lead 1: is `ChainsRunTheirVersionsRelease` fully proved?

**It is proved in Lean. It rests on model-boundary assumptions, not on unproved Lean premises.**

- **The proof.** It is at `EraSpec/Contracts/ChainTypeManager/Proofs/ChainRouting.lean:324-327`, by `run_sysInv`.
  - There is no `sorry` or axiom anywhere in `EraSpec`.
  - The last audit message, in commit `b05bde6`, reports 0 unclean.
- **Visible premises.** The run starts in a `SysInv` state and contains no `arbitraryCut` label.
  - `FreshSystemSatisfiesInvariant` and `BootstrapSystemSatisfiesInvariant` discharge `SysInv` for fresh and just-bootstrapped CTMs.
  - There is no hash premise.

Unproved things it rests on, all model boundaries:

1. **`requireReleaseRouting` is modelled by its documented meaning.** The live routing must equal the release's routing exactly. The source's counting argument is "not re-proved" (`Specs/ChainRouting.lean:66-70`, README:120-121, `UPG/upgrades/registry/libraries/LiveRoutingReader.sol:32-59`). This is the largest gap that can be closed in Lean: item U1.
2. **Every engine is assumed to run `DefaultUpgrade`/`BootstrapUpgrade` logic, and a transition's cuts are its derived cuts** (`Specs/ChainRouting.lean:77-84`).
   - The engine is named by governance in the manifest (`UPG/upgrades/registry/RegistryTypes.sol:141-148`).
   - `CTMTransition.validate()` only checks that the engine has code (`UPG/upgrades/registry/objects/CTMTransition.sol:227-233`).
   - So this is a trust assumption on governance, not something Lean can prove.
3. **Objects are their getters**, and `selectors()` self-descriptions are fixed functions.
4. **Diamond writes outside the model are omitted:**
   - the delegatecalled `DiamondInit` beyond the routing install;
   - `L1GenesisUpgrade` and `genesisUpgrade`;
   - arbitrary code an engine delegatecalls;
   - chains on other CTMs.

   See `Specs/ChainRouting.lean:85-94` and `ASSUMPTIONS.md:93`.
5. **The bootstrap entry state is the post-`migrate` state**, and caller and timing checks are omitted (`ASSUMPTIONS.md:93`). Omitting reject-only checks is sound for safety; it does matter for liveness (item U3).
6. **CTM code swaps.** These are now modelled in `ExecutorForward`.
   - `TameRunKeepsChainsOnTheirRelease` extends the headline to executor runs, but only under `Tame` and `ReinitFrames`.
   - `ForwardCtmSwapBreaksInvariants` shows that `Tame` is needed.
   - **Caveat:** `ExecutorForward` and `ProxyUpgradeRowLib/RowsCurrent` arrived in `f98c40f`, "WIP … committed as-is for handoff". No audit message after that commit confirms they build or pass the audit, and both are modified in the working tree by the current port. Re-run the audit after the port.
   - `ASSUMPTIONS.md:93` still lists "CTM proxy implementation swaps (`applyInfrastructureUpgrade`)" as not modelled, which is stale. Neither topic has a row in the results table at `ASSUMPTIONS.md:175-195`.

Upgrade-system results still open, in Lean: U1–U8 below.
- U1: counting check.
- U2: per-chain headline and repair.
- U3: timestamp gates.
- U4: transition enabledness.
- U5: drop the duplicate-row premise.
- U6: executor `upgradeChain` getter lookup.
- U7: bootstrap `forward` coverage.
- U8: init and genesis writers.

### Lead 2: the `upgradeChain` timestamp NatSpec (`UPG/upgrades/registry/executors/ICTMUpgradeExecutor.sol:47-54`)

The NatSpec:

```
/// @dev Callers:
///      - the OWNER may upgrade any chain at any time;
///      - a CHAIN'S OWN ADMIN may upgrade that chain at any time — upgrading is the chain's
///        decision to make, ...
///      The chain's own `upgradeTimestamp` gate does NOT apply here: the chain sees the CTM as
///      the caller, and the CTM is exempt from it.
```

The code path:

- `CTMUpgradeExecutor.upgradeChain` (`CTMUpgradeExecutor.sol:87-102`) calls `CHAIN_TYPE_MANAGER.upgradeChainFromVersion(_chainId, oldProtocolVersion)`.
- `ChainTypeManager.upgradeChainFromVersion` is `onlyOwner` (`ChainTypeManager.sol:623-626`). It calls `IZKChain(chainAddress).upgradeChainFromVersion(...)`, so the diamond sees `msg.sender` = the CTM.
- The CTM is the diamond's `s.chainTypeManager`, because `DiamondInit.sol:91` sets `s.chainTypeManager = msg.sender` and the CTM deploys the proxy (`ChainTypeManager.sol:693`).
- `Admin.upgradeChainFromVersion` (`Admin.sol:543-554`):

  ```
  // Check that the auto upgrade timestamp has passed if the sender is not admin or chainTypeManager.
  if (msg.sender != s.admin && msg.sender != s.chainTypeManager) {
      ... uint256 timestamp = serverNotifier.protocolVersionToUpgradeTimestamp(s.chainId, _oldProtocolVersion);
      if (timestamp == 0 || block.timestamp < timestamp) { revert UpgradeTimestampNotReached(timestamp, block.timestamp); }
  }
  ```

- The engine then runs `_executeDiamondCut(diamondCut)` with the cut's init `DefaultUpgrade.upgradeFromTransition`. That calls `_upgradeFromCommittedObject` (`DefaultUpgrade.sol:66-76`), which reads `(newProtocolVersion, upgradeTimestamp, newRelease) = _object.upgradeTarget()` and passes `_upgradeTimestamp: upgradeTimestamp`.
- That reaches `BaseZkSyncUpgrade._upgrade` (`BaseZkSyncUpgrade.sol:76-78`):

  ```
  if (block.timestamp < _upgradeTimestamp) { revert TimeNotReached(_upgradeTimestamp, block.timestamp); }
  ```

  `upgradeTimestamp` is the manifest's field (`CTMTransition.sol:197-204`, `RegistryTypes.sol:146`), described as "From when chains may cross the edge" (`VersionEdgeLib.sol:33`).

**Verdict:**
- **The sentence at lines 53-54 is true of the code** if "the chain's own `upgradeTimestamp` gate" means the per-chain ServerNotifier gate in `Admin.sol:546-554`. That gate is set by the chain admin (`ServerNotifier.sol:113-131`), and the CTM is exempt from it.
- **The surrounding claim at lines 48-49 is false.** "the OWNER may upgrade any chain at any time" and "a CHAIN'S OWN ADMIN may upgrade that chain at any time" do not hold:
  - before the transition manifest's `upgradeTimestamp`, every `upgradeChain` reverts with `TimeNotReached` (`BaseZkSyncUpgrade.sol:76-78`);
  - so is every direct `Admin.upgradeChainFromVersion`, whoever the caller;
  - it also reverts while any batch is committed but unexecuted (`DefaultUpgrade.sol:31`);
  - and when the chain's settlement layer is behind (`BaseZkSyncUpgrade.sol:83-88`).
- The same "at any time" wording is in `docs/registry-driven-upgrades.md:659` and `protocol-docs/system/contracts/chain_management/upgrade_process.md:41`.
- The sentence at lines 53-54 is also easy to misread. Both gates are called `upgradeTimestamp`, and only the per-chain one is skipped.

This is for the user to report. It is not claimed in the repo. Item U3 turns it into checked statements plus a countermodel.

## Current coverage, one line per contract or folder

- **AssetRouterBase**: one writer (`_setAssetHandlerAddressThisChain`) of handler and tracker. `RunValid`, `OnlyTrackerOrNtvWrites`, `FreshIdNeedsNtv`. `NoHijack` and `NtvTouches…` are repaired as `…On`/`…OrCollision`. The other writers at the pin are not modelled.
- **AtomicFlowManager**: per-leg state machine (rank monotone, `no_double_claim`, `no_double_append`, CEI before interaction), flow canonical ordering, and `RecoveryLimits` countermodels (partial and terminal recovery, one revert blocks all).
- **AtomicInteropProof**: both timeout branches (`TimeoutSoundness`), last batch (`LastBatchInRoot`), stale snapshot, timestamps, polarity. The vacuous `LastLeaf` results are repaired as `…PinnedBreak`/`…On`.
- **BridgedStandardERC20**: initialized nonlegacy mint/burn/transfer ledger and bounds; fresh-proxy initializer; codegen refinement of the same slice. Legacy fallback, reinitializer, allowances and permit are absent.
- **ChainTypeManager** (UPG): version registry, routing headline, migration round trips, executor `forward` with the `Tame` boundary. `ExecutorForward` is from a WIP commit.
- **EcosystemUpgradeExecutor** (`afa407085`): staged coordinator and timer lifecycle. The code is deleted at UPG.
- **FullMerkle**: abstract fold, capacity, tree-shape countermodels. Its global-hinj results are vacuous; only some have `_on` forms. The cached `_nodes` algorithm is not modelled.
- **IndexedMerkleTree**: abstract IMT list/order theory, insert-guard countermodels, reset and zero sentinel.
- **InteropDataEncoding**: decoder round trip for `abi.encode(uint256,bytes)`, packed-encoding lemmas. `distinct_sends_distinct_hashes` takes global injectivity.
- **InteropHandlerBase**: bundle and call status machine, self-call authority. No CEI or reentrancy model.
- **L2InteropCommitmentTree**: wrapper model, `Reaches`, hint search (including the fuel caveat), `TreeRoot` (repaired `…OrBreak`), `RunHeight` (capacity premise discharged).
- **L2InteropHandler**: `AtomicSourceBinding`. Its positive result's premise is its conclusion (item S4).
- **Merkle**: `Verifier`, `ProofSound`, `RootBinding`, `RootForgery`. `PathCollision` is the repair; most of `RootForgery`/`RootBinding` is still vacuous (global-hinj).
- **NativeTokenVaultBase**: fresh registration, representation preparation (`bridgeBurn` branch), guards, `RegistryAndEscrow` (all eleven `IdAssumptions` results repaired as `…On` plus `LoggedRunSound`), and `ModelCorrespondence` (four disagreement countermodels). No destination mint or recovery model.
- **ProxyUpgradeRowLib**: `Rows` at `612a71ccc` and `RowsCurrent` at UPG (WIP commit).
- **RegistryBootstrapMigration**: authority parking, one-shot, two countermodels.
- **Protocol**:
  - `MultichainGate`: source-bound gate, no hash premise.
  - `InteropAtomicity`: all headlines have no-hash `…OrBreak` forms; the vacuous originals are kept.
  - `AssetBridgePreparation`: preparation and spending trace conservation; no resolution steps.
  - Legacy `NoTheft`, `LocalHonesty`, `FlowAtomicity`, `DestinationCapstone`.
- **Examples/BurnMintBridge**: reference application. P1–P7 are composed; the END (halted-chain) branch is not.
- **Codegen**: token-slice interpreter, two-way refinement, `GEN-EMIT` trusted.
- **Not modelled at all**:
  - `InteropCenter`;
  - `L1AssetRouter`/`L2AssetRouter` beyond the handler writer;
  - `L1Nullifier`, `L2AssetTracker`, `BaseTokenHolder`, wrapped base token;
  - `MessageVerification`/`L2InteropRootStorage`, Bridgehub.

**Doc hygiene noticed (not proof items):**
- `ASSUMPTIONS.md:112` (`CRYPTO-ID`) and `AssetRouterBase/README.md:33-34` say restating with a bounded premise "is open". Every affected property already has an `…On` and/or `…OrCollision` form (vault: `RegisterNativeIdFreshOn` … `UnguardedInflowUnbackedOn`, `LoggedRunSound`; router: `NoHijackOn`, `NtvTouchesOnlyItsOwnIdsOn`). Only the doc text is stale; item R3 is the one remaining strengthening.
- `NativeTokenVaultBase/README.md:44` says "Twelve of its fourteen"; `ASSUMPTIONS.md:112` says eleven.
- `Refinement.lean:218-267` still exports the vacuous `root_guarantee`, `atomicity_guarantee`, `all_or_nothing` and `timeout_justified` next to the repaired ones.
- `MODEL-CTM-ROUTING` is stale (Lead 1, item 6).

## Backlog (priority order)

Size key: S ≈ ≤1 day, M ≈ 2–5 days, L ≈ >1 week. Items are numbered within lanes: B = bridge, A = atomicity, U = upgrade, S = strengthen, R = router/registry, O = other.

### B1. Atomic recovery always routes through the NTV, whatever the asset's handler (possible finding)
- **kind**: model-gap (expected result: a countermodel).
- **where**:
  - `REVIEW.md:203` ("only the manager invokes atomic recovery; recovery restores the depositor").
  - `ASSET_BRIDGING_VERIFICATION_PLAN.md:94` (B12).
  - `AtomicFlowManager/README.md` and `Specs/RecoveryLimits.lean` (limit 2).
  - New topic `EraSpec/Contracts/AssetRouterBase/{Specs,Properties,Proofs}/AtomicRecovery.lean`.
- **statement sketch**: Model the router's handler map, `L2AssetRouter.recoverAtomicCall`, and the NTV's `bridgeRecoverFailedTransfer` guard chain as far as `assetIdCheck`. Then:
  - (a) for any `assetId` whose handler is not the NTV and that is not `encodeNTVAssetId(c, t)` for the decoded `(c, t)` (under `IdAssumptionsOn` on the two named pairs), `recoverAtomicCall` reverts rather than returning `false`;
  - (b) composed with `RecoveryLimits.revert_anywhere_blocks`, any atomic bundle containing such a call can never be refunded, and neither can its other calls;
  - (c) positive side: for NTV-registered assets, recovery reaches `bridgeRecoverFailedTransfer` with the burn's `originalCaller`.
- **source refs**:
  - `PIN/bridge/asset-router/L2AssetRouter.sol:281-296` (ignores `assetHandlerAddress`, always calls NTV, `return true`).
  - `PIN/bridge/asset-router/AssetRouterBase.sol:313-336` (source burn uses the custom handler).
  - `PIN/bridge/ntv/NativeTokenVaultBase.sol:213-233, 284-306, 573-586` (`assetIdCheck` at :580).
  - `PIN/common/libraries/DataEncoding.sol:208-214`.
  - `PIN/atomic-interop/AtomicFlowManager.sol:205-206` ("Targets must return `false` (not revert) for calls they do not recognise") and `:215-218`.
- **size/deps**: M. Independent, but reuses `HandlerRegistration` and `RecoveryLimits`.
- **risk**: The countermodel is the expected outcome, so this is a candidate source finding. It could be "intended" if custom-handler assets are barred from atomic bundles elsewhere, e.g. in `InteropCenter` attribute checks not read here. Check `InteropCenter._processCallStarter` (`PIN/interop/InteropCenter.sol:701-730`) before reporting.

### B2. Destination mint and failed-transfer recovery: exact amount, recipient and asset
- **kind**: model-gap (M2/M3 milestones).
- **where**:
  - `ASSET_BRIDGING_VERIFICATION_PLAN.md:195-196` (M2, M3) and `:83-94` (B4, B5, B12).
  - `NativeTokenVaultBase/README.md` L141-145 ("do not establish … destination execution, refund").
  - `BridgedStandardERC20/README.md:69-72`.
  - New `EraSpec/Contracts/NativeTokenVaultBase/{Specs,Properties,Proofs}/Resolution.lean`, built on `RepresentationPreparation`'s state and the token model.
- **statement sketch**: For the registered bridged-representation branch, with `md = (originalCaller, remoteReceiver, originToken, amount, meta)`:
  - (a) a successful `bridgeMint(chain, assetId, md)` credits exactly `amount` to `remoteReceiver`, raises supply by `amount`, and calls the tracker hook `fromChain(chain, assetId, amount)` before the mint;
  - (b) a successful `bridgeRecoverFailedTransfer(chain, assetId, md)` credits exactly `amount` to `originalCaller`, ignoring `remoteReceiver`;
  - (c) round trip: `prepare` followed by `recover` with the returned `md` restores the depositor's balance and total supply exactly, and the tracker hooks cancel;
  - (d) failure atomicity under `transact`, and the paused, non-router and value≠0 guards.
- **source refs**: `PIN/bridge/ntv/NativeTokenVaultBase.sol:193-205, 213-233, 240-267, 284-306`; `PIN/bridge/BridgedStandardERC20.sol:170-185`.
- **size/deps**: L. Depends on the existing NTV preparation and token models.
- **risk**: (c) can fail if the tracker hooks are not inverse. They are parametric, so state the inverse law as a premise, with a countermodel for non-inverse hooks. The first-bridge deploy branch (`token == 0`) needs the registration model.

### B3. Close the preparation trace with resolution steps: conservation and single resolution across both chains
- **kind**: new-property (B5, B6).
- **where**:
  - `Protocol/AssetBridgePreparation/README.md:27-28, 61-63` ("no independent mint, refund … step"; "does not prove … unique resolution").
  - `ASSET_BRIDGING_VERIFICATION_PLAN.md:56-63`.
  - New `EraSpec/Protocol/AssetBridgePreparation/{Specs,Properties,Proofs}/Resolution.lean`.
- **statement sketch**: Add `deliver i` (destination `bridgeMint` of pending entry `i`) and `refund i` (source `bridgeRecoverFailedTransfer`), each consuming pending entry `i` at most once, gated by an `Evidence.Sound` oracle as in `BurnMintBridge`. For every reachable state:
  - `srcSupply + dstSupply + Σpending = srcSupply₀ + dstSupply₀`;
  - no entry is both delivered and refunded;
  - each entry resolves at most once.

  Instantiate the oracle with `MultichainGate`/`InteropAtomicity` `…OrBreak` evidence to get "or a located break".
- **source refs**: as in B2; `PIN/atomic-interop/AtomicFlowManager.sol:165-180`.
- **size/deps**: L. Depends on B2, `Protocol/InteropAtomicity` (Refund `…OrBreak`), and `MultichainGate`.
- **risk**: Low for conservation. Exclusivity is only as strong as the evidence: unsound evidence gives `conflicting_evidence_double_pays`.

### A1. FullMerkle's cached `_nodes` algorithm computes the abstract root and path (O7, source side)
- **kind**: model-gap, discharging the model side of an open obligation.
- **where**:
  - `Refinement.lean:86-88` ("the source side of O7 narrows to one statement: `FullMerkle.updateLeaf` followed by `pushNewLeaf` computes `rootOf` …").
  - `L2InteropCommitmentTree/README.md:56-57`; `FullMerkle/README.md:19-20`.
  - New `EraSpec/Contracts/FullMerkle/{Specs,Properties,Proofs}/CachedNodes.lean`.
- **statement sketch**: Transcribe `setup`, `pushNewLeaf`, `updateLeaf`, `root` and `merklePath` over a state `(_height, _leafNumber, _zeros : List W, _nodes : List (List W))` as pure Lean functions. Prove the invariant `_zeros[i] = zeros h z i` and `_nodes[i][j] = level i of rootOf-fold over leaves`. Consequences:
  - `root = rootOf h z leaves _height`, matching `RootAfterInsertOwnHeight`;
  - `merklePath i` is exactly the sibling list the abstract walk uses, so `InclusionComplete` and `HonestProofNoBreak` apply to the contract's own path;
  - `updateLeaf` with `_index > _leafNumber-1` has no step.
- **source refs**: `PIN/common/libraries/FullMerkle.sol:29-35, 41-66, 73-94, 99-121`; `PIN/common/libraries/IndexedMerkleTree.sol:42-51`.
- **size/deps**: M–L. Depends on the `FullMerkle` `Model` and `CapacityInvariant` push counters.
- **risk**: Should be true. A failure would be a real off-by-one in the height-growth branch (`:45-52`) or in the zero-sibling choice (`:84`). The proof attempt would produce that countermodel.

### A2. `ExecutedImpliesRealFlowFinalizable` without `FlowHashInj`, in logged-clash form
- **kind**: discharge-open.
- **where**:
  - `ASSUMPTIONS.md:164` (vacuous via `HashAssumptions`, `FlowHashInj`) and `:197-200` ("Recorded but without protocol content: `FlowIdCheckPinsLegListOrCollision`, `SubsetFlowCheckedOnlyByCollision` …").
  - `Refinement.lean:111-120` (O8 item 2: "the check's sufficiency is not yet proved").
  - New `EraSpec/Protocol/InteropAtomicity/{Properties,Proofs}/FlowBinding.lean`.
- **statement sketch**: Over a logged run (as for `RefundImpliesOwnFlowTimeoutOrLoggedClash`): if leg `ℓ` was executed through a flow `F` whose id check passed, and any other logged call checked a flow `F'` with `F'.flowId = F.flowId`, then one of the following holds:
  - every leg of `F'` is finalizable;
  - an `InclusionBreak` sits on a named leg of `F`'s gate proof;
  - a `FlowIdClash fh F F'` holds, where both flows come from the run's own log.

  The witness pair (no break, nonempty log) and the subset-flow attack should land in the clash disjunct.
- **source refs**: `PIN/atomic-interop/AtomicFlowManager.sol:105-131, 247-259`.
- **size/deps**: M. Depends on `Atomicity` `…OrBreak`, the `Refund` log machinery (`ReachLog`), and `CrossFlowIdClashIsPinnedCollision`.
- **risk**: Low. It must avoid the excluded-middle trap noted at `ASSUMPTIONS.md:197`, which means pinning `F'` to a logged call, not to a free variable.

### A3. Once-per-leg result: commitment binding plus `no_double_append` plus `dedup_gate_sound`
- **kind**: discharge-open.
- **where**:
  - `Protocol/InteropAtomicity/README.md:69-71` ("composing `CommitmentPinsLeg` (once restated) with the manager's `no_double_append` and the tree's `dedup_gate_sound` into a once-per-leg result" is open).
  - `ASSUMPTIONS.md:165` (`CommitmentPinsLeg` vacuous; `…On` is contraposition).
  - New `EraSpec/Protocol/InteropAtomicity/{Properties,Proofs}/OncePerLeg.lean`.
- **statement sketch**: On a per-chain run (center → manager → tree), each `(flowId, bundleHash)` is appended at most once and occupies exactly one tree key. Any two tree keys equal to the commit value of two logged obligations name the same obligation, or a `CommitClash` holds on those two logged obligations' `(tag, flowId, bundleHash)` preimages.
- **source refs**: `PIN/atomic-interop/AtomicFlowManager.sol:87-102`; `PIN/atomic-interop/libraries/AtomicInteropProof.sol:100-102`; `PIN/atomic-interop/L2InteropCommitmentTree.sol:53-59`.
- **size/deps**: M. Depends on `AtomicFlowManager.Model`, `L2InteropCommitmentTree.Model`, and `Protocol/LocalHonesty.lean`.
- **risk**: Low.

### A4. Compose the halted-chain (END) timeout branch into the reference bridge's evidence
- **kind**: discharge-open (P4).
- **where**:
  - `REVIEW.md:135-137` ("The halted-chain last-batch branch is not composed into this application theorem yet").
  - `Examples/BurnMintBridge/ProtocolComposition.lean:14-16`.
  - New `EraSpec/Examples/BurnMintBridge/EndBranchComposition.lean`, or a Protocol topic.
- **statement sketch**: Extend `Missing` to the disjunction of the current successor-pinned form and the END form `∃ B T, settledAt B ≤ D < T ∧ (∀ n > B, T ≤ settledAt n) ∧ v ∉ endSet B` (as in `TimeoutSoundness.timeout_implies_never_finalized`). Re-prove `onTime_excludes_missing` and `evidence_sound`, so `prepared_bridge_no_double_payment` and `prepared_bridge_value_conserved` cover both branches. Add a variant taking the last-batch fact from `LastBatchInRoot.end_branch_from_onchain_check` or `AcceptedImpliesRefundablePinned` (pinned-break form).
- **source refs**: `PIN/atomic-interop/libraries/AtomicInteropProof.sol:152-205, 217-226`.
- **size/deps**: M. Depends on `TimeoutSoundness`, `LastBatchInRoot`, and `Timeout` (pinned).
- **risk**: Low with `AppendOnly` and `TimeOrdered` premises. The `Aggregates` premise stays load-bearing (`StaleRootRefundsDeliveredLeg`).

### U1. `requireReleaseRouting`'s counting check equals exact routing (upgrade headline's largest model boundary)
- **kind**: strengthen (replaces a modelled-by-meaning guard) and model-gap.
- **where**:
  - `Specs/ChainRouting.lean:66-70`; `ChainTypeManager/README.md:120-121`; `ASSUMPTIONS.md:93`.
  - New `EraSpec/Contracts/ChainTypeManager/{Specs,Properties,Proofs}/LiveRouting.lean`.
- **statement sketch**: Model diamond storage `(facets, facetToSelectors, selectorToFacet)` with `DiamondOk`:
  - no duplicate facets;
  - every listed facet has ≥1 selector and every unlisted facet has none;
  - `selectorToFacet x = some (f, b)` iff `x ∈ facetToSelectors f`.

  Prove that `diamondCut` add/remove (`Diamond.sol:141-300`, including `_removeOneFunction`/`_removeFacet` at :260, :289) preserves `DiamondOk`. Then, for release rows with unique facets, nonempty selector lists and globally unique selectors:
  - `CountCheck ds rows ↔ selectorToFacet = rowsRouting (flatten rows)`.

  **Countermodel (expected):** drop "nonempty selectors". A release `{A:[s1], B:[]}` passes the count check against a live diamond `{A:[s1], C:[s2]}`, which routes `s2`. So the guard relies on `CTMRelease.validate()` refusing empty selector lists.

  Finally replace the semantic guard in `Step.transition` by `CountCheck` and re-derive `ChainsRunTheirVersionsRelease`.
- **source refs**:
  - `UPG/upgrades/registry/libraries/LiveRoutingReader.sol:32-59`.
  - `UPG/upgrades/registry/objects/CTMRelease.sol:105-128` (empty-selector refusal at :120-122), `:175-206` (duplicate facet rows and selectors).
  - `UPG/state-transition/libraries/Diamond.sol:110-300`.
- **size/deps**: M. Depends on `ChainRouting`.
- **risk**:
  - The equivalence is false without the nonempty-selectors premise; the countermodel above is itself a result.
  - `validate()` runs only when a release is installed (`ChainTypeManager.sol:310`), while `selectors()` is re-read at check time. If a facet's self-description could change, the premise could fail. That is a model boundary to state.

### U2. Per-chain headline and break-glass repair
- **kind**: strengthen.
- **where**: `ChainTypeManager/README.md:51-64, 77-80` (`DriftedReturnerIsStuck`); `UPG/upgrades/DefaultUpgrade.sol:33-36` ("Restoring the release's routing is the last step of such a recovery"). New `EraSpec/Contracts/ChainTypeManager/{Properties,Proofs}/ChainLocal.lean`.
- **statement sketch**:
  - (a) Per-chain headline: along any run from `SysInv`, if chain `id`'s last routing-writing step is not an `arbitraryCut` of `id`, then `ChainOk` holds for `id`. Break-glass cuts on other chains are irrelevant. The current headline forbids every break-glass cut system-wide.
  - (b) Repair: an `arbitraryCut id v (rowsRouting (relRows (relAt v)))` with `relAt v ≠ 0` and `v ≤ ctm.pv` restores `ChainOk`. After it, a committed edge at `v` is enabled (via U4), which un-sticks `DriftedReturnerIsStuck`.
- **source refs**: `UPG/state-transition/ChainTypeManager.sol:631-633`; `UPG/state-transition/chain-deps/facets/Admin.sol:562-564`.
- **size/deps**: S. Depends on `ChainRouting` and `ChainMigration`.
- **risk**: Low. `relAt w` is never rewritten for `w ≤ pv`; check this against `CStep`.

### U3. Upgrade timestamp gates, and the `upgradeChain` NatSpec as theorems
- **kind**: model-gap (Lead 2).
- **where**: `ChainTypeManager/README.md:128-129` ("Upgrade timestamps, deadlines and the all-batches-executed check are not modelled"); `ASSUMPTIONS.md:93`. New `EraSpec/Contracts/ChainTypeManager/{Specs,Properties,Proofs}/UpgradeTiming.lean`, extending `Step.transition` and `XStep.upgradeChain` with a block time `τ`, a caller, and `notifier : ChainId → ℕ → ℕ`.
- **statement sketch**:
  - (a) `ExecutorPathIgnoresNotifier`: for `XLabel.upgradeChain`, the chain sees caller = CTM, and step existence does not depend on `notifier`. This proves `ICTMUpgradeExecutor.sol:53-54`.
  - (b) `ManifestTimestampGates`: any transition step across slot `v` at time `τ` has `τ ≥ (W.tr (ut v)).upgradeTimestamp`, whatever the caller.
  - (c) Countermodel `NotAtAnyTime`: a committed edge with `upgradeTimestamp = 10`. At `τ = 9`, no executor `upgradeChain` step exists, whether called by the owner or the chain admin. This refutes `ICTMUpgradeExecutor.sol:48-49`.
  - (d) Any other caller (a validator) needs `notifier id v ≠ 0 ∧ τ ≥ notifier id v`.
  - (e) Optional: `VersionEdgeLib.requireValidEdge` gives `oldVersionDeadline ≥ upgradeTimestamp`, so the upgrade window is nonempty at commit.
- **source refs**: `UPG/upgrades/registry/executors/ICTMUpgradeExecutor.sol:47-54`; `CTMUpgradeExecutor.sol:87-102`; `ChainTypeManager.sol:623-626`; `Admin.sol:528-559`; `ZKChainBase.sol:126-131`; `DiamondInit.sol:91`; `DefaultUpgrade.sol:30-44, 66-85`; `BaseZkSyncUpgrade.sol:66-88`; `VersionEdgeLib.sol:47-62`; `ServerNotifier.sol:113-131`.
- **size/deps**: S–M. Depends on `ChainRouting` and `ExecutorForward`.
- **risk**: (a) is true if `s.chainTypeManager` equals the CTM proxy for every chain. Chains created by a pre-registry CTM implementation behind the same proxy also have it. A chain whose `chainTypeManager` was rewritten by a legacy migration would be a counterexample; this was not checked.

### U4. Transition enabledness (liveness of upgrades)
- **kind**: new-property (B11 analogue for upgrades).
- **where**: `ASSET_BRIDGING_VERIFICATION_PLAN.md:93` (B11); `ChainTypeManager/README.md:62-64` (only negative enabledness facts exist: `DriftBlocksTransition`, `MissingSelectorBricksTransition`). Same new file as U2 or `Enabledness.lean`.
- **statement sketch**: Assume `SysInv`, a chain `c` with `ChainOk`, `ut c.pv ≠ 0`, and `ReleaseWf W r` (unique selectors in `relRows r`) for the edge's two releases. Then `∃ s', Step W s (.transition id) s'`, and likewise for `migrateIn`/`genesis`.
- **source refs**: `UPG/upgrades/registry/objects/CTMRelease.sol:175-206`; `TransitionDerivationLib.sol:47-80`.
- **size/deps**: S. Depends on `ChainRouting`.
- **risk**: False without `ReleaseWf`, because `addAll` fails on a duplicate selector; give that countermodel. Also note that `CTMRelease.validate()` is omitted in the model, so `ReleaseWf` must be stated.

### B4. Pause: safety unaffected, liveness delayed, and recovery or execution blocked while paused
- **kind**: model-gap (B7, B11, B12).
- **where**: `REVIEW.md:204` ("identify which pause … conditions can block pending execution or recovery"); `ASSET_BRIDGING_VERIFICATION_PLAN.md:89, 199`. New `EraSpec/Protocol/InteropAtomicity/{Specs,Properties,Proofs}/Pause.lean` plus a small NTV extension.
- **statement sketch**: Add per-chain `paused` flags (handler `_ensureNotPaused`, NTV `whenNotPaused` on `bridgeMint`/`bridgeRecoverFailedTransfer`, NTV `bridgeBurn`). Then:
  - (a) every existing safety result (`ExecutedObligationNeverRefundedOrBreak`, `NoneOrAllOrBreak`) holds verbatim, since pause only removes steps;
  - (b) a paused destination handler leaves a committed, on-time flow neither executable nor refundable, because no absence proof exists;
  - (c) unpausing restores enabledness;
  - (d) a paused NTV makes `claimRefund` revert, so the leg stays `Revertable` and can be retried after unpause.
- **source refs**: `PIN/interop/interop-handler/L2InteropHandler.sol:49-50`; `PIN/bridge/ntv/NativeTokenVaultBase.sol:197, 217, 661-668`; `PIN/atomic-interop/AtomicFlowManager.sol:165-180`.
- **size/deps**: S. Depends on `InteropAtomicity`, `RecoveryLimits`, and B2 for (d).
- **risk**: Low.

### R1. Close the `ModelCorrespondence` guard gap between the two vault models
- **kind**: model-gap.
- **where**: `NativeTokenVaultBase/README.md` L185-188 ("Adding the three registry-only conditions to the representation model's registration … and `ot ≠ 0` to `RegisterBridgedGuard`, would close the gap. Neither model is changed here."); `Refinement.lean:143-144` (unifying the two models is open). New `EraSpec/Contracts/NativeTokenVaultBase/{Specs,Properties,Proofs}/RegistrationUnified.lean`, so the existing models stay unchanged.
- **statement sketch**: Define `registerRepresentation'`, which adds token ≠ 0, token unmapped, and origin chain ≠ 0 (derived from `tokenDataOriginChainId` normalisation with `_l1ChainId ≠ 0`). Define `RegisterBridgedGuard'`, which adds origin token ≠ 0. Prove:
  - (a) `registerRepresentation'` success implies a registry `Step` with no side conditions, and `Valid` is carried under `IdAssumptionsOn`;
  - (b) the four disagreement countermodels become impossible;
  - (c) `Corr` is preserved by both registration and preparation.
- **source refs**: `PIN/bridge/ntv/NativeTokenVaultBase.sol:538-598, 565-571`; `PIN/bridge/BridgedStandardERC20.sol:85-100` (`_originToken != 0`).
- **size/deps**: S–M. Depends on `ModelCorrespondence`.
- **risk**: Freshness ("token unmapped") rests on CREATE2 reverting at an occupied address. That is `VM-DEPLOY` and must stay a premise.

### R2. Asset router: model the other handler writers (expected countermodel to `RunValid`)
- **kind**: model-gap.
- **where**: `AssetRouterBase/README.md:3-11` ("It is NOT the only writer at the pin … So `RunValid` … is a property of the model's single writer, not of the deployed router"). New `EraSpec/Contracts/AssetRouterBase/{Specs,Properties,Proofs}/AllWriters.lean`.
- **statement sketch**: Add these writers:
  - `_finalizeDeposit`'s fallback (sets the NTV handler without a tracker);
  - `L2AssetRouter.setAssetHandlerAddress` (L1-counterpart only);
  - `L1AssetRouter.setAssetDeploymentTracker`.

  Prove:
  - (a) a countermodel: `RunValid` ("live route has an accountable tracker") fails after one `_finalizeDeposit`;
  - (b) the weakened invariant "every live route has a tracker, or its handler is the NTV and its id is an NTV id" holds along all runs;
  - (c) `NoHijackOn` holds against every caller except the L1 counterpart, which is a trusted exception made explicit.
- **source refs**: `PIN/bridge/asset-router/AssetRouterBase.sol:73-100, 275-301`; `PIN/bridge/asset-router/L2AssetRouter.sol:91-102, 200-214`; `PIN/bridge/asset-router/L1AssetRouter.sol:169-190`.
- **size/deps**: M. Depends on `HandlerRegistration`.
- **risk**: (a) is expected to be a countermodel, which is the intended outcome. (b) may need the NTV's `tryRegisterTokenFromBurnData` behaviour.

### B5. Conditional full recovery for router/NTV-only bundles (positive P8/B12)
- **kind**: new-property.
- **where**:
  - `REVIEW.md:183-192` (P8 "OPEN as a system guarantee"); `ASSET_BRIDGING_VERIFICATION_PLAN.md:94` (B12).
  - `PIN/atomic-interop/AtomicFlowManager.sol:215-218` (the flow author's responsibility).
  - New `EraSpec/Protocol/AssetBridgePreparation/{Properties,Proofs}/FullRecovery.lean`.
- **statement sketch**: Take a `Revertable` leg whose bundle's calls are all `finalizeDeposit` calls to the router for NTV-registered assets prepared on this chain. If the NTV is unpaused and the token behaves as in the local model, then `claimRefund` succeeds with `recovered = callsLen`, and each call restores exactly its `amount` to its `originalCaller`. Restoration is full, not merely best-effort. Combined with `RecoveryLimits`, this characterises exactly when the manager's terminality equals full restoration.
- **source refs**: as in B1, B2 and B4.
- **size/deps**: M. Depends on B1, B2, B4 and `RecoveryLimits`.
- **risk**: B1 may show custom-handler legs always break this, which is why the premise is "NTV-registered". Tracker-hook inverse laws are premises.

### S4. `AtomicSourceBinding.atomic_source_bound` is tautological; reduce it to local honesty and pinned hash binding
- **kind**: strengthen.
- **where**: `L2InteropHandler/Properties/AtomicSourceBinding.lean:73-75` (the conclusion `declared h = c` is literally the premise `HonestCommits`, `Specs/AtomicSourceBinding.lean:69`); `L2InteropHandler/README.md:15-19`. New `EraSpec/Contracts/L2InteropHandler/{Properties,Proofs}/SourceBindingReduced.lean`.
- **statement sketch**: Replace `HonestCommits` with:
  - `LocalHonesty` guards on chain `c`, under which every key in `tree c` is the commit value of an `append` by `c`'s center;
  - the center computes `bundleHash = keccak(abi.encode(block.chainid, bundle))`.

  Conclude: the declared source of `h` is `c`, or a pinned collision on the commit-value or bundle-hash preimages of the two logged bundles. This uses `BundleHashEncoding.abiDecode_abiEncode`.
- **source refs**: `PIN/interop/InteropCenter.sol:639-660`; `PIN/atomic-interop/AtomicFlowManager.sol:87-102`; `PIN/atomic-interop/libraries/AtomicInteropProof.sol:100-102`.
- **size/deps**: M. Depends on `LocalHonesty`, `InteropDataEncoding`, and A3.
- **risk**: Low, but it still assumes the source chain executes honestly (`PROTO-EVIDENCE`), so say so in the statement.

### O1. InteropCenter: salt replay, atomic-value validation, and a non-tautological `validation_unbypassable`
- **kind**: model-gap and strengthen.
- **where**:
  - `REVIEW.md:202` (InteropCenter row: "sender salts cannot replay; atomic calls carry no unsupported native value"), `:238-242` (suggested first path).
  - `AtomicFlowManager/Properties/RecoveryLimits.lean:121-123`: `validation_unbypassable` takes `sole_path : ∀ b, Committed b → Validated b` and concludes `Validated b`, which is a tautology.
  - New `EraSpec/Contracts/InteropCenter/{Specs,Properties,Proofs}/Dispatch.lean`.
- **statement sketch**: Model `isInteropBundleSaltUsed`, `_validateAtomicBundle`, and `_dispatchBundle` → `append` for each atomic leg. Prove:
  - (a) each `(sender, salt)` dispatches at most one bundle;
  - (b) every appended atomic bundle has all `calls[i].value = 0`, so `sole_path` becomes a derived lemma about the center's only `append` call site;
  - (c) with `packed_addr_salt_inj`, distinct dispatches give distinct bundle-hash preimages.
- **source refs**: `PIN/interop/InteropCenter.sol:129, 262-300, 478-483, 639-676`.
- **size/deps**: M. Independent.
- **risk**: Low. The center's other `append` callers need a source inventory; there should be one call site.

### S1. `distinct_sends_distinct_hashes` takes global injectivity into `Hash`
- **kind**: strengthen.
- **where**: `InteropDataEncoding/Properties/BundleHashEncoding.lean:148-160` (`hsalt_inj : Function.Injective saltHash`, `hbundle_inj : Function.Injective bundleHashOf`). At `Hash = UInt256` with `List UInt8` and `Bundle` domains this cannot hold, yet it is not in the vacuity table at `ASSUMPTIONS.md:151-166`. New `.../Properties/BundleHashPinned.lean`.
- **statement sketch**: Without injectivity premises: distinct `(a, s)` versus `(a', s')` give distinct hashes, or a collision of `saltHash` on the two named packed preimages, or a collision of `bundleHashOf` on `b`, `b'`. Add a witness showing the collision disjunct is false for an honest instance. Also prove `Function.Injective saltHash → False` at `Hash = UInt256`, for the register.
- **source refs**: `PIN/interop/InteropCenter.sol:478-483`; `PIN/interop/InteropDataEncoding.sol`.
- **size/deps**: S. Independent.
- **risk**: None.

### S2. `SharedCommitmentYieldsCollision` is unpinned (always true)
- **kind**: strengthen.
- **where**: `ASSUMPTIONS.md:139-149` and `Protocol/InteropAtomicity/README.md:37-39` (`UnpinnedCollisionsAlwaysExist`); `Properties/Refund.lean:202-206`. Add to `OncePerLeg.lean` (A3) or a new `Refund` topic.
- **statement sketch**: For obligations `o`, `o'` drawn from the run's log: if `cv o = cv o'`, then `o` and `o'` name the same leg, or `CommitClash cv o o'` holds. Show that for `honestCommitValue` the clash is false on a nonempty log.
- **source refs**: as in A3.
- **size/deps**: S. Depends on the `Refund` `ReachLog`; it is subsumed if A3 is done.
- **risk**: None.

### S3. Restate the remaining global-hinj Merkle results in pinned form
- **kind**: strengthen.
- **where**: `ASSUMPTIONS.md:155-162` (`Merkle` `RootForgery` ×9, `RootBinding` ×3, `ProofSound` ×3; `FullMerkle` `Model` ×7, `TreeShape.capacity_ok_root_commits`); only `PathCollision` and the `_on` forms repair a subset. New `EraSpec/Contracts/Merkle/{Properties,Proofs}/RootForgeryPinned.lean`.
- **statement sketch**:
  - `root_ne_of_leaf_ne`, `no_append_forgery`, `rootOf_append_inj`, `rootOf_set_inj`, `single_sibling_substitution`: if two leaf lists of the same height have equal roots but differ at index `i`, a named level `k` on `i`'s path has distinct child pairs with equal hash.
  - `capacity_ok_root_commits`: the same, or derive it from `RunHeight`.
  - Give a non-tautology witness for each.
- **source refs**: `PIN/common/libraries/Merkle.sol`, `FullMerkle.sol`.
- **size/deps**: M. Reuses `PathCollision`'s `WalkPinsOrCollision`.
- **risk**: Low. A pinned collision may need the padding/domain case, as `TreeRootBreak` has.

### B6. `BridgedStandardERC20.reinitializeToken` preserves ledger and identity
- **kind**: model-gap (B9).
- **where**: `BridgedStandardERC20/README.md:66-68` ("metadata contents and reinitializers … upgrades"); `REVIEW.md:205` ("initialization/reinitialization cannot change the asset represented by pending obligations"). New `EraSpec/Contracts/BridgedStandardERC20/{Specs,Properties,Proofs}/Reinitialization.lean`.
- **statement sketch**: A successful `reinitializeToken(getters, name, symbol, v)` requires:
  - `v = initializedVersion + 1`;
  - caller = beacon owner, which is configuration.

  It changes only `name`, `symbol`, `availableGetters` and `initializedVersion`. Balances, supply, `nativeTokenVault`, `assetId` and `originToken` are unchanged, so `WellFormed`, `RepresentationConsistent` and every pending entry's mint data stay valid. `initializedVersion` strictly increases, and a version jump > 1 has no step.
- **source refs**: `PIN/bridge/BridgedStandardERC20.sol:66-71, 148-164`.
- **size/deps**: S. Depends on the token and NTV `RepresentationConsistent` models.
- **risk**: None for the ledger. Permit domain separators change, which is out of model.

### B7. Legacy zero-vault fallback in `onlyNTV`
- **kind**: model-gap (B9).
- **where**: `BridgedStandardERC20/README.md:66` (legacy zero-vault fallback); `ASSET_BRIDGING_VERIFICATION_PLAN.md:203-204`. New `.../Specs,Properties,Proofs/LegacyFallback.lean`.
- **statement sketch**: From a legacy state (`nativeTokenVault = 0`), the first `bridgeMint`/`bridgeBurn` writes `nativeTokenVault := L2_NTV` and `assetId := encodeNTVAssetId(L1_CHAIN_ID, originToken)`, then behaves as the nonlegacy branch. The token's `assetId` agrees with the vault's registry entry iff the vault registered the legacy token with origin chain `L1_CHAIN_ID` and the same origin token. Give a countermodel otherwise (bounded `IdAssumptionsOn` on the two pairs).
- **source refs**: `PIN/bridge/BridgedStandardERC20.sol:50-64`; `PIN/bridge/ntv/NativeTokenVaultBase.sol:155-170` (`addLegacyTokenToBridgedTokensList`).
- **size/deps**: S–M. Depends on the token model and `RegistryAndEscrow`.
- **risk**: The countermodel is plausible for a legacy token registered under a non-L1 origin. Whether that state is reachable needs the L2 NTV's legacy setters (`L2NativeTokenVault.sol`), which were not read here.

### U5. Drop the distinct-proxies premise from `OnlyNamedEdgesAcrossCall` and `FixedEntrypointsMoveProxiesOnlyAlongRows`
- **kind**: strengthen.
- **where**: `ProxyUpgradeRowLib/Properties/RowsCurrent.lean:118-121`; `ChainTypeManager/Properties/ExecutorForward.lean:79-83`; `ProxyUpgradeRowLib/README.md:87-91` (non-genuine objects are not validated, so they can have duplicate rows). Add a `…AnyRows` variant in a new `ProxyUpgradeRowLib/{Properties,Proofs}/RowsUnvalidated.lean`.
- **statement sketch**: Under `ReinitFrames` alone, for any row list, including one from a non-genuine `IProxyUpgradeTransition`, a successful `ApplyRows` moves each proxy `p` only from some row's `expectedOldImpl` to that row's `implNew`. Proof idea: the in-call verification forces all rows for `p` to share `implNew` (`TwoTargetsForOneProxyRevert`), and the first row that moves `p` found it at its `expectedOldImpl`.
- **source refs**: `UPG/upgrades/registry/libraries/ProxyUpgradeRowLib.sol:102-147`.
- **size/deps**: S. Depends on `RowsCurrent`.
- **risk**: Low. A reinitializer that moves its own proxy and is then skipped by a later `alreadyAtTarget` row is caught by verification (`ReinitMovingOwnProxyIsCaught`). Check that case in the proof.

### U6. Executor `upgradeChain` reads `_transition.oldProtocolVersion()`: a non-genuine replacement bricks the executor path
- **kind**: model-gap (liveness).
- **where**: `ChainTypeManager/Specs/ExecutorForward.lean` (`XStep.upgradeChain` is just `Step.transition`, with no getter lookup); `VersionRegistry` `NonGenuineReplacementBreaksSlotVersion`. Extend in a new `ChainTypeManager/{Properties,Proofs}/ExecutorUpgradeChain.lean`.
- **statement sketch**: Refine `upgradeChain(t, id)` to require `ut (W.tr t).old = t` and then the transition at `c.pv`. Prove:
  - (a) for genuine slot contents it is exactly `Step.transition`;
  - (b) after `replace 300 500` (where 500 reports `old = 7`), no `upgradeChain(_, id)` step exists for chains at version 1, while a direct `Admin.upgradeChainFromVersion(id, 1)` (chain-admin caller) and a forwarded CTM call still exist.

  So the CTM's missing departure check costs liveness of the fixed entry point, not safety.
- **source refs**: `UPG/upgrades/registry/executors/CTMUpgradeExecutor.sol:87-102`; `UPG/state-transition/ChainTypeManager.sol:429-448`.
- **size/deps**: S. Depends on `ExecutorForward`.
- **risk**: Low.

### U7. `RegistryBootstrapMigration`: forwarded calls are covered by the label set (make the argument a theorem)
- **kind**: strengthen.
- **where**: `RegistryBootstrapMigration/README.md:70-80` ("this is an argument about the label set, not a separate theorem"), `:67-68` (the CTM swap keeps `Ownable2Step` storage, which is assumed). New `RegistryBootstrapMigration/{Specs,Properties,Proofs}/Forward.lean`.
- **statement sketch**: Define the executor's `forward` over calls to the CTM (nominate, accept), the `ProxyAdmin` (`transferOwnership`) and CTM version writers. Prove every successful `forward` by a genuine executor is a run of the model's existing other-actor steps. Hence `NoReparkingAfterMigrate` and `ParkedCTMLeavesOnlyByNomineeAccept` cover it. State explicitly that `upgradeAndCall` on the CTM proxy is excluded, linking to `ForwardCtmSwapBreaksInvariants`.
- **source refs**: `UPG/governance/UpgradeExecutorBase.sol:32-46`; `UPG/upgrades/registry/bootstrap/RegistryBootstrapMigration.sol:48-50, 255-292`.
- **size/deps**: S–M. Depends on `Authority` and `ExecutorForward`.
- **risk**: Low.

### O2. Commitment tree: setup runs once, so the history cannot be reset
- **kind**: model-gap.
- **where**: `IndexedMerkleTree/README.md:21-23` (the wrapper's one-time initialization guard is not established); `REVIEW.md:207` ("initialization cannot reset live history"); `ResetAndZero.resetHistory_not_evolution`. New `L2InteropCommitmentTree/{Specs,Properties,Proofs}/InitOnce.lean`.
- **statement sketch**: With `initL2` as a step guarded by `leafCount = 0` (`IMT.setup` reverts otherwise), no run from `setup` contains a second successful `initL2`. Every run's key set is monotone (`ReachesKeysMono`), so `resetHistory` is unreachable. Drop the guard and the reset countermodel fires.
- **source refs**: `PIN/atomic-interop/L2InteropCommitmentTree.sol:30-50`; `PIN/common/libraries/IndexedMerkleTree.sol:42-51`.
- **size/deps**: S. Depends on the commitment-tree `Model`/`Reaches` and `ResetAndZero`.
- **risk**: None in the model. `onlyUpgrader` (complex upgrader) authority is out of model.

### O3. Handler CEI: re-entrant execution cannot run a bundle twice
- **kind**: model-gap (B8).
- **where**: `REVIEW.md:210` ("reentrancy cannot reopen execution; failing calls roll back the bundle"); `InteropHandlerBase/README.md:16-21`. New `InteropHandlerBase/{Specs,Properties,Proofs}/Reentrancy.lean`.
- **statement sketch**: Model `executeAtomicBundle`/`executeBundle` as status write, then a call loop where each call may invoke any handler entry point re-entrantly (bounded depth), with `Option` rollback. Prove:
  - (a) no bundle hash is ever executed twice in any nested trace;
  - (b) a failing call rolls back the status write, so the bundle stays `Unreceived` and can be retried;
  - (c) a countermodel with the status write moved after the calls admits double execution.
- **source refs**: `PIN/interop/interop-handler/L2InteropHandler.sol:45-100`; `PIN/interop/interop-handler/InteropHandlerBase.sol:86-140, 164-220`.
- **size/deps**: M. Depends on `BundleStatusMachine`.
- **risk**: Low. (b) depends on `VM-REVERT` semantics as modelled.

### R3. Router: run-level `NoHijack` under a logged, bounded premise
- **kind**: strengthen (the one real gap left behind the stale `CRYPTO-ID` "open" text).
- **where**: `ASSUMPTIONS.md:112, 191`; `AssetRouterBase/README.md:33-34`. `NoHijackOn` is per call. Add to `HandlerRegistration` as a new topic `HandlerRegistrationRuns.lean`.
- **statement sketch**: As in `NativeTokenVault.LoggedRunSound`: log the run. Take `S` to be the triples hashed by logged registrations (at most one per step). Under `IdInjOn enc S`, no run lets a non-vault caller overwrite a handler installed by the NTV. Give a satisfiability witness with an encoding that collides off the log.
- **source refs**: `PIN/bridge/asset-router/AssetRouterBase.sol:73-100`; `PIN/common/libraries/DataEncoding.sol` (`encodeAssetId`).
- **size/deps**: S. Depends on `HandlerRegistration`; R2 would widen it.
- **risk**: None.

### A5. Operational projection for `InteropAtomicity`'s fixed history
- **kind**: discharge-open.
- **where**: `Protocol/InteropAtomicity/README.md:65-69` ("An operational model (or a projection theorem from one) is open"). `SourceHeight` already does the heights. New `Protocol/InteropAtomicity/{Specs,Properties,Proofs}/Operational.lean`.
- **statement sketch**: Define a global interleaving of per-chain steps (center append → tree insert, batch seal with a monotone settlement time, handler execute, manager authorize and claim) where evidence may only cite already-sealed batches. Prove every operational run projects to a `System` with `Wf` and `Aggregates`-compatible roots, and the logged calls embed into the fixed-history `ReachLog`. All `…OrBreak` headlines then transfer.
- **source refs**: the `PIN/atomic-interop/*` files.
- **size/deps**: L. Depends on `SourceHeight`, `Refund`, A3, and O2.
- **risk**: `Aggregates` is a settlement-layer property and must stay a premise of the projection. Otherwise expected true, since the fixed history admits more runs.

### U8. Diamond writers outside the model: `DiamondInit`, `genesisUpgrade` / `L1GenesisUpgrade`
- **kind**: model-gap.
- **where**: `ASSUMPTIONS.md:93` ("Not modelled: … the delegatecalled `DiamondInit` and `L1GenesisUpgrade`"); `Specs/ChainRouting.lean:85-89`. New `ChainTypeManager/{Specs,Properties,Proofs}/GenesisWriters.lean`.
- **statement sketch**: Transcribe the routing-relevant parts of `DiamondInit.initialize` and `L1GenesisUpgrade.genesisUpgrade`, then prove:
  - `DiamondInit` writes exactly `newChainInstallations(currentRelease)` and `s.protocolVersion = ctm.protocolVersion()`;
  - `genesisUpgrade` performs no facet cut (its `facetCuts` is empty), and its init writes no `Diamond` storage slot.

  The genesis label of `ChainRouting` then becomes a theorem rather than a modelling choice.
- **source refs**: `UPG/state-transition/chain-deps/DiamondInit.sol:55-115`; `UPG/state-transition/chain-deps/facets/Admin.sol:567-578`; `UPG/upgrades/L1GenesisUpgrade.sol`.
- **size/deps**: M. Depends on `ChainRouting`.
- **risk**: `L1GenesisUpgrade` goes through `BaseZkSyncUpgrade._upgrade` (`_upgradeTimestamp: 0`, `L1GenesisUpgrade.sol:44`), which could in principle touch storage beyond routing. Re-read it; a write to diamond storage would be a countermodel.

### O4. Second codegen slice: the vault preparation path
- **kind**: model-gap (`REP-VAULT` at interpreter level).
- **where**: `CODE_GENERATION.md:151-153` ("Natural next steps: extend the slice to the vault's preparation path (`REP-VAULT`)"); `ASSUMPTIONS.md:90`. New `EraSpec/Codegen/VaultPreparationSlice/{Specs,Properties,Proofs}/…`.
- **statement sketch**: Transcribe `bridgeBurn`'s registered-representation branch in `Codegen.Lang`. Prove two-way refinement against `RepresentationPreparation.prepare`: model rejection iff revert, and on success a related state with exact returned bytes. Transfer `preparation_backed` by `safety_transfer`.
- **source refs**: `PIN/bridge/ntv/NativeTokenVaultBase.sol:315-432`.
- **size/deps**: L. Depends on `Codegen` and the NTV preparation model.
- **risk**: Medium. The language may need external calls (token, tracker) and ABI bytes, which `Codegen.Lang` may not support yet.

## Suggested order

| Step | Items | Reason |
|---|---|---|
| 1 | B1, U3 | Possible source findings. Small and independent. |
| 2 | A1, U1, A2, A3 | Close the biggest remaining model-by-assumption gaps behind the interop and upgrade headlines. |
| 3 | B2 → B3 → B5 | The M2/M3 bridge spine: delivery and refund, conservation across chains, conditional full recovery. |
| 4 | A4, U2, U4, B4, R1, R2 | Medium value; mostly independent. |
| 5 | S1–S4, B6, B7, U5–U8, O1–O4, R3, A5 | Hygiene, strengthening, and larger extensions. |

Before any of this, after the Lean 4.35 port, re-run `./scripts/audit-axioms.sh` to confirm that `ExecutorForward` and `RowsCurrent` (WIP commit `f98c40f`) build and pass the audit.
