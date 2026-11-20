# Current handoff — 2026-11-20

Continue from **`claude/proof-round-9`**. Round 9 started from `claude/proof-round-8` (`35d2eb9`) and works on
the round-8 handoff's Priority 1, **consolidation**. That note is kept verbatim in
[handoff/2026-11-18/HANDOFF.md](handoff/2026-11-18/HANDOFF.md); its plan, rules and "done when" list still
apply. The conventions round 9 introduced are in [CONSOLIDATION.md](CONSOLIDATION.md).

Nothing was pushed to `master` and no PR was opened. Ask Kalman before pushing to `master`, opening or merging
PRs, or publishing anything about a possible upstream (era-contracts) issue.

## State of `claude/proof-round-9`

- **Toolchain:** Lean v4.35.0 + Mathlib v4.35.0, unchanged.
- **Build:** `lake build EraSpec` builds 4011 jobs.
- **Audit** (`lake env lean scripts/Audit.lean`):
  - 28522 theorems and 4528 properties, each with its full named theorem;
  - 0 axioms, 0 NOT clean, 0 tag findings;
  - 291 headline, 310 witness and 233 countermodel properties, plus 3694 untagged supporting lemmas;
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

- **Per-unit notes:** `handoff/2026-11-19/consolidation/<unit>.md`. Each note records the inventory, the
  decisions, and what was not done.
- **Renames:** `handoff/2026-11-19/renames/<unit>.json`, 157 entries. They map every removed or renamed
  property to its replacement.

## What is left

1. **Wave 2 (not started).** Six units were launched, but the session ended before any of them committed:
   - InteropCenter;
   - InteropHandlerBase;
   - AtomicFlowManager (timeout refund only; the PR 2642 expiry refund is not at v35);
   - AtomicInteropProof (the H1 countermodels go to History);
   - the Merkle libraries (Merkle, FullMerkle, DynamicIncrementalMerkle);
   - AssetRouterBase (the M1 countermodels go to History).

   Start them fresh from `claude/proof-round-9`. These folders show `0` headlines in the audit.
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
