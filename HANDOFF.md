# Current handoff — 2026-11-20 (updated after wave 2, part 1)

Continue from **`claude/proof-round-9`**. Round 9 started from `claude/proof-round-8` (`35d2eb9`) and works on
the round-8 handoff's Priority 1, **consolidation**. That note is kept verbatim in
[handoff/2026-11-18/HANDOFF.md](handoff/2026-11-18/HANDOFF.md); its plan, rules and "done when" list still
apply. The conventions round 9 introduced are in [CONSOLIDATION.md](CONSOLIDATION.md).

Nothing was pushed to `master` and no PR was opened. Ask Kalman before pushing to `master`, opening or merging
PRs, or publishing anything about a possible upstream (era-contracts) issue.

## State of `claude/proof-round-9`

- **Toolchain:** Lean v4.35.0 + Mathlib v4.35.0, unchanged.
- **Build:** `lake build EraSpec` builds 4026 jobs.
- **Audit** (`lake env lean scripts/Audit.lean`):
  - 28543 theorems and 4535 properties, each with its full named theorem;
  - 0 axioms, 0 NOT clean, 0 tag findings;
  - 340 headline, 340 witness and 270 countermodel properties, plus 3585 untagged supporting lemmas;
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

- **Per-unit notes:** `handoff/2026-11-19/consolidation/<unit>.md`. Each note records the inventory, the
  decisions, and what was not done.
- **Renames:** `handoff/2026-11-19/renames/<unit>.json`, 332 entries. They map every removed or renamed
  property to its replacement.

## What is left

1. **Wave 2 (part 1 merged).** AtomicFlowManager, InteropHandlerBase and InteropCenter are merged. AtomicInteropProof
   (the H1 countermodels go to History), the Merkle libraries (Merkle, FullMerkle, DynamicIncrementalMerkle)
   and AssetRouterBase (the M1 countermodels go to History) are in progress. They may or may not land before
   the usage limit; check `git log` and the audit's folder lines. Start any that did not land fresh from
   `claude/proof-round-9`.

   **Wave-2 remainder** (from `atomic-flow.md`, `handler-base.md`, `interop-center.md`):
   - move RecoveryLimits and RecoveryTargets to History once their importers move, and add their renames;
   - merge FlowCanonicalAtHead into FlowCanonicalAtV35, with the Protocol unit;
   - AssetRouterBase `AtomicRecovery` and RecoveryLimitsFaithful model the pin loop over different call
     types, with no refinement between them (`MODEL-ATOMIC-RECOVERY`);
   - restate `ValueLedgerFaithful` and three bundle-status engine statements (`WholeBundleWriteIgnoresCallStatus`,
     `CallStatusDoesNotStopWholeBundleRedelivery`, `AdmittedBundleHasOnlyUnprocessedCalls`) on the
     `b17415d20` layer;
   - a refinement lemma between SelfCallAuthorityStrong and SelfCallAuthorityFaithful;
   - merge the `ReentrancyAtV35` files into `Reentrancy` (needs ReentrancyStrong and the
     BundleStatusMachineFaithful gate lemmas merged too; no statement change);
   - update `scripts/check-interop-handler-inventory.sh`, which still checks the pin layout;
   - link InteropCenter `Send` and FeeState/FeeReentry into one model;
   - re-check the line numbers of the InteropCenter History records against `c67894b9`;
   - `Protocol/InteropAtomicity/ExecutionLiveness` and `Protocol/DestinationCapstone` now import History
     records; the Protocol unit re-pins them.
2. **Protocol areas.** These come after wave 2, since they compose the contracts: `Protocol/InteropAtomicity`
   (537 properties, 17 Specs files still citing older pins) and the other areas. All Protocol areas are
   untagged.
3. **Cross-contract model bridges.** The handoff's step 2 across contracts is not done for:
   - ChainTypeManager ↔ ProxyUpgradeExecutorBase / SecondProofSystem (listed in `ctm.md`);
   - MessageRoot Aggregation onto the canonical MessageRoot model (`roots.md`);
   - the duplicate `L2Log` in ChainBatchRootTree and MessageHashing;
   - the assets second models (kept, with refinement lemmas).
4. **ChainTypeManager remainder** (`ctm.md`):
   - `GenuineReplacementsKeepUpgradeChainLive` is not restated over the engine model;
   - there is no gated pending model;
   - the duplicate transcriptions are bridged but not merged.
5. **Old-pin mentions.** 187 non-History Specs files still mention an older commit. Many of these
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
