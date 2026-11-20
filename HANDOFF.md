# Current handoff — 2026-11-20 (end of round-9 run)

Continue from **`claude/proof-round-9`**. Round 9 started from `claude/proof-round-8` (`35d2eb9`) and works on
the round-8 handoff's Priority 1, **consolidation**. That note is kept verbatim in
[handoff/2026-11-18/HANDOFF.md](handoff/2026-11-18/HANDOFF.md); its plan, rules and "done when" list still
apply. The conventions round 9 introduced are in [CONSOLIDATION.md](CONSOLIDATION.md).

Nothing was pushed to `master` and no PR was opened. Ask Kalman before pushing to `master`, opening or merging
PRs, or publishing anything about a possible upstream (era-contracts) issue.

## State of `claude/proof-round-9`

- **Toolchain:** Lean v4.35.0 + Mathlib v4.35.0, unchanged.
- **Build:** `lake build EraSpec` builds 4042 jobs.
- **Audit** (`lake env lean scripts/Audit.lean`):
  - 28588 theorems and 4544 properties, each with its full named theorem;
  - 0 axioms, 0 NOT clean, 0 tag findings;
  - 428 headline, 398 witness and 324 countermodel properties, plus 3394 untagged supporting lemmas;
  - a per-folder line for each contract and Protocol area.
- **One target commit.** Every model is being moved to era-contracts v35 `b17415d20` (`draft/v0.35.0` head).
  Records of older pins live in `History/` folders with a `History` namespace segment.
- **Bootstrap code is current.** The bootstrap and legacy-crossing code (`RegistryBootstrapMigration`,
  `BootstrapUpgrade`, the CTM legacy commit/cut path) is still present at `b17415d20`, so those topics are
  current, not History. Only the unmerged v36 PR 2650 removes them.

## What round 9 merged

Every unit was independently and adversarially reviewed before merging. Reviewers checked:
- the full build and the audit;
- no weakened statement, checking the renames mechanically;
- Solidity citations spot-checked against `b17415d20`;
- non-vacuity;
- that the docs match the Lean.

| Unit | Contracts | Notes |
|---|---|---|
| infra | `EraSpec/Core/Headline.lean`, `scripts/Audit.lean`, self-test | Adds `@[headline]`/`@[witness]`/`@[countermodel]`. The audit counts them and rejects tags off Properties defs, double tags, History headlines, headlines without a docstring, and private declarations in Properties modules. The self-test has 22 cases. |
| roots | MessageRoot, L2InteropRootStorage, ChainBatchRootTree, L2MessageVerification, MessageVerification | Re-pinned; pin records moved to History. |
| assets | L2AssetTracker, NativeTokenVaultBase, L1NativeTokenVault | Re-pinned. Second models are kept and linked to the canonical one by refinement lemmas. |
| upgrade | ProxyUpgradeExecutorBase, SecondProofSystem, ProxyUpgradeRowLib, RegistryBootstrapMigration, EcosystemUpgradeExecutor | Re-pinned. EcosystemUpgradeExecutor is History, because its code does not exist at v35. |
| imt | IndexedMerkleTree, L2InteropCommitmentTree | One v35 IMT model. The H2 padding countermodels are History. |
| smalls-l1 | AdminFacet, Bridgehub, ChainAssetHandler, L1ChainAssetHandler, Diamond, ExecutorFacet, MailboxFacet, ValidatorTimelock, Governance, ChainAdminOwnable, PriorityTree, L1Nullifier, BlobsL1DAValidatorZKsyncOS | Re-pinned and checked, with headline lists. |
| smalls-enc | DataEncoding, InteropDataEncoding, MessageHashing, L1Messenger, L1InteropHandler, L2InteropHandler | Re-pinned. The c67894b9 source-binding and bundle-hash results are History, with no b17415d20 counterpart yet. |
| ctm | ChainTypeManager (26 topics) | Every topic pinned to `b17415d20`. The `…AtV35` re-models are folded into the base topics where they model the same code. GenesisWriters now models the second-proof-system check. **Partial:** see `handoff/2026-11-19/consolidation/ctm.md`. |
| tagging | all merged folders | Tags applied from each unit's plan. Model-bridge statements are untagged, and missing premises were added to headline docstrings. |
| atomic-flow | AtomicFlowManager | Re-pinned. `FlowCanonicalAtV35` is the canonical entry-point model. `FlowCanonicalAtHead` is linked to it by refinement lemmas but not merged, because Protocol `FlowBindingAtHead` builds on its types. `FlowCanonical` is the neighbour-check vocabulary both share. RecoveryLimitsStrong and the pin half of RecoveryLimitsFaithful are History. RecoveryLimits and RecoveryTargets still model only `c67894b9`; they stay at their paths, untagged, until their importers move. RecoveryLimits is imported by AssetRouterBase, InteropCenter `Send` and Protocol/AssetBridgePreparation. RecoveryTargets is now imported only by InteropCenter History, so it can move. |
| handler-base | InteropHandlerBase | Re-pinned. One stack: the status machine, the `Reentrancy` engine, its `b17415d20` layer (`ReentrancyAtV35`, folded into topic `Reentrancy` but still in its own files) and the dispatch tables. The pin-only parts of BundleStatusMachine and BundleStatusMachineFaithful, and all of BundleStatusMachineStrong, are History. SelfCallAuthorityFaithful and SelfCallAuthorityStrong stay two models of the same dispatch, with no refinement lemma yet. **Partial:** see `handler-base.md`. |
| interop-center | InteropCenter | The shared vocabulary is in `Specs/Common.lean`, at `b17415d20`. Dispatch, ClaimBinding and AtomicRouting moved to History (`c67894b9`). SendAtHead became topic `Send`, at `b17415d20`. **Partial:** `Send` and FeeState/FeeReentry are not linked into one model. |
| atomic-proof | AtomicInteropProof | Re-pinned. Four layers of one library, not competing models: the `b17415d20` proof-word transcription (`AuthenticateRootAtV35`), batch-leaf path acceptance (`LastLeafFaithful`), the index level, and the abstract gates. New bridge lemmas join the duplicate definitions (`HonestInsertionAgrees`, `BeginIsPrevEndProjects`, `OutsideRootLateIffNat`). The H1 (`PinnedReach`) and H2 (padding) records and the pin `_authenticateRoot` transcription are History; 6 statements moved. 10 headlines. |
| merkle-libs | Merkle, FullMerkle, DynamicIncrementalMerkle | Re-pinned; every library line re-checked at `b17415d20`. The eight pin-padding statements of `DomainSeparation` are History. New topic `DynamicIncrementalMerkle/PriorityTreeBridge`: within the `uint256` range the PriorityTree folder's `push`, `setup` and `root` equal this folder's. New headline `ContractPathVerifiesInRange` carries the `2^255` bound. 14 headlines. The vacuous `global-hinj` results stay untagged. |
| asset-router | AssetRouterBase | Re-pinned. 59 statements moved to History: 31 of AtomicRecovery, all of AtomicRecoveryFaithful and PausedRecovery; the M1 countermodels are tagged there. New refinement lemma `VaultRefundRefinesResolution` onto the canonical NativeTokenVaultBase refund. 15 headlines. The `c67894b9` record definitions in `Specs/AtomicRecovery.lean` stay in place for their importers. |
| protocol-smalls | ten small Protocol areas: AssetBridgePreparation (Reinitialization), BatchCounters, CtmRecord, InteropPeerRegistry, L1WithdrawalProvenance, L2BridgeConfig, NativeValueLegs, PriorityMirror, PriorityRequests, ZKsyncOSDA | Tags and READMEs only; no statement changed, so no renames file. AssetBridgePreparation Reinitialization re-cited at `b17415d20` (only line numbers moved). 49 headlines. MultichainGate, FlowAtomicityPerChain and the AssetBridgePreparation Resolution, ResolutionEvidence and FullRecovery files model `c67894b9`; their READMEs say so, and they stay untagged. No per-unit note; see the merge commit `834bf13`. |

- **Per-unit notes:** `handoff/2026-11-19/consolidation/<unit>.md`. Each note records the inventory, the
  decisions, and what was not done.
- **Renames:** `handoff/2026-11-19/renames/<unit>.json`, 405 entries. They map every removed or renamed
  property to its replacement.

## What is left

1. **Wave-2 remainder.** Wave 2 is complete: every contract folder is consolidated and tagged. What the
   units deferred (from `atomic-flow.md`, `handler-base.md`, `interop-center.md`, `atomic-proof.md`,
   `merkle-libs.md`, `asset-router.md`):
   - move RecoveryLimits and RecoveryTargets to History once their importers move, and add their renames;
   - move the `c67894b9` record definitions in AssetRouterBase `Specs/AtomicRecovery.lean`
     (`recoverAtomicCall`, `recoverBundle`, `claimRefund`, …) to History with their importers
     (AtomicRecoveryAtHead's pin-against-head statements, RecoveryTargets, Protocol `FullRecovery`);
   - merge FlowCanonicalAtHead into FlowCanonicalAtV35, with the Protocol unit;
   - AssetRouterBase `AtomicRecovery` and RecoveryLimitsFaithful model the pin loop over different call
     types, with no refinement between them (`MODEL-ATOMIC-RECOVERY`);
   - restate the PausedRecovery results (History only) on `AtomicRecoveryAtHead`;
   - restate `ValueLedgerFaithful` and three bundle-status engine statements (`WholeBundleWriteIgnoresCallStatus`,
     `CallStatusDoesNotStopWholeBundleRedelivery`, `AdmittedBundleHasOnlyUnprocessedCalls`) on the
     `b17415d20` layer;
   - a refinement lemma between SelfCallAuthorityStrong and SelfCallAuthorityFaithful;
   - merge the `ReentrancyAtV35` files into `Reentrancy` (needs ReentrancyStrong and the
     BundleStatusMachineFaithful gate lemmas merged too; no statement change);
   - update `scripts/check-interop-handler-inventory.sh`, which still checks the pin layout;
   - link InteropCenter `Send` and FeeState/FeeReentry into one model;
   - re-check the line numbers of the InteropCenter History records against `c67894b9`;
   - AtomicInteropProof: no formal refinement from `LastBatchInRoot.RightEmpty` (index level) to the
     hash-level `zeroCheck`; `ASSUMPTIONS.md` rows `PROTO-BATCH-SNAPSHOT` and `PROTO-CONTIGUOUS-PUSH`
     still cite `c67894b9` lines;
   - DynamicIncrementalMerkle `ChainTreeBacking` still builds on `Protocol/InteropAtomicity`'s
     `Timeout.RootBacking`, a `c67894b9` model;
   - `Protocol/InteropAtomicity/ExecutionLiveness` and `Protocol/DestinationCapstone` now import History
     records; the Protocol unit re-pins them.
   - **Open judgement: the AtomicInteropProof stale-witness headlines.** `StaleWitnessNotRedeemableOrBreak`
     and `StaleWitnessNotRedeemableOrCollision` are headlines, but they take the abstract pin
     `D < t (j+1)` as a hypothesis. The deployed gate never checks that comparison. Their docstrings and
     the README say so plainly. There is no composed headline over the deployed branches yet. Decide
     whether they stay headlines or are untagged until one exists.
2. **Protocol areas: the next big item.** `Protocol/InteropAtomicity` (537 properties, all untagged, 17
   Specs files still citing older pins) is next. MultichainGate, FlowAtomicityPerChain and the
   AssetBridgePreparation Resolution, ResolutionEvidence and FullRecovery files model `c67894b9`
   and stay untagged until re-modelled at `b17415d20`. The ten small areas are tagged (protocol-smalls).
3. **Cross-contract model bridges.** The handoff's step 2 across contracts is not done for:
   - ChainTypeManager ↔ ProxyUpgradeExecutorBase / SecondProofSystem (listed in `ctm.md`);
   - MessageRoot Aggregation onto the canonical MessageRoot model (`roots.md`);
   - the duplicate `L2Log` in ChainBatchRootTree and MessageHashing;
   - the assets second models (kept, with refinement lemmas).
4. **ChainTypeManager remainder** (`ctm.md`):
   - `GenuineReplacementsKeepUpgradeChainLive` is not restated over the engine model;
   - there is no gated pending model;
   - the duplicate transcriptions are bridged but not merged.
5. **Old-pin mentions.** 178 non-History Specs files still mention an older commit (a `git grep` for the
   older pin hashes). Many of these
   legitimately say "byte-identical at …" or cite pre-v35 code a v35 path still talks to (for example the
   v34 Admin facet in the legacy crossing). Each should be checked; this is the final citation re-check in
   the round-8 plan.
6. **Step 4: split `ASSUMPTIONS.md` by area.** Not started.
7. **Tagging follow-ups:**
   - a few `@[witness]` defs (`CoreLegIsDomainHoldersLegSatisfiable`, `PackedTimestampsWitness`,
     `LibMapWitness`) witness statements that are no longer headlines;
   - check that the other ChainAssetHandler Migration headlines name the `W.l1 ≠ 0` premise;
   - the vacuous `IdAssumptions` (assets) and `HashAssumptions` (IMT `TreeRoot`) results are untouched and
     untagged.
8. **The audit checks names, not statements.** The renames completeness check compares names only, so a
   statement weakened in place under the same name is caught only by review. A statement-hash baseline would
   close that gap.

## Environment

- **Toolchain:** elan at `~/.elan`.
- **Build cache.** Share `.lake/packages` by symlink between worktrees and copy `.lake/build` with
  `cp -cR`. Never run `lake update` or `lake exe cache get`.
- **Sources.** Make a `--filter=blob:none` clone of matter-labs/era-contracts and extract `b17415d20`
  outside `/tmp`. Other pins are available via `git show <sha>:<path>`.

## Previous handoffs

- [2026-11-18](handoff/2026-11-18/HANDOFF.md): round 8, the consolidation plan this round follows.
- [2026-11-16](handoff/2026-11-16/README.md), [2026-11-13](handoff/2026-11-13/README.md), 2026-11-11: rounds
  7, 6 and 5. They are historical.
