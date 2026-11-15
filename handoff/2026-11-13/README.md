# Continuation handoff — 2026-11-13

Valera can continue from **`claude/proof-round-6`** in
[`kelemeno/era-protocol-specs`](https://github.com/kelemeno/era-protocol-specs/tree/claude/proof-round-6).
This branch contains the latest reviewed integration work found locally, including
round 5 and the recent strengthen/faithfulness salvage merges. Its code checkpoint
before this documentation update is `6fa71e0f383760b3d42955687683bcaab72cdfd0`.

## What was saved

- Inventoried 95 existing local branches and all 80 registered worktrees.
- Created 44 WIP checkpoint commits covering 199 changed or newly added file entries.
  These preserve the existing proof/specification and documentation work as-is.
- Recovered changes from three detached worktrees into named branches (below),
  bringing the local branch total to 98.
- Pushed every outstanding local branch head to the same branch name on `origin`
  using one atomic regular push. All 98 local heads were then checked against
  `git ls-remote`; every head matched. All 80 worktrees were clean at that point.
- Set tracking to the same-name remote branches for the branches pushed. Older
  remote `wip/*` branches remain available; the former tracking names are recorded
  in the inventory. Some historical branch names described as deleted in the
  November 11 handoff were recreated from surviving local refs during this backup.
- Excluded `.DS_Store` through the shared local Git exclude file. Existing ignored
  build caches and worktree directories remain local.

The [complete branch inventory](branches.json) records all 98 branch names, exact
checkpoint commits, whether each was already contained in the round-6 checkpoint,
previous tracking names, and the files saved by each new WIP commit. The inventory
is the snapshot before this handoff documentation commit; the documentation commit
then advances `claude/proof-round-6` alone.

## Where to continue

| Branch family | Purpose / continuation point |
| --- | --- |
| `claude/proof-round-6` | Primary integration branch; latest reviewed merges and the saved ProxyUpgradeRowLib README edits. |
| `claude/proof-round-5` | Earlier integration baseline, already contained in round 6. |
| `salvage/codex-findings-*` | Saved review repairs; new checkpoints on 11, 12 and 14 concern InteropHandlerBase reentrancy/atomic unbundling, mutable selectors, and interop batch positions. |
| `salvage/head-fixes-1` through `-6` | Saved current-head/v35 proof and documentation edits for padding, recovery, flow binding, source filters, executor authority, and proof/upgrade gates. |
| `salvage/faithfulness-repair-*`, `salvage/strengthen-*` | Model fidelity and stronger-property work. Some tips are already integrated; consult the inventory and compare before selecting work. |
| `cov/*`, `cov2/*` | Contract and end-to-end coverage work, much of it newly saved source. Many topics still need properties, proofs, imports, or documentation. |
| `up/*` | v35 upgrade-path investigations and partially written modules. |
| `worktree-wf_*`, other `claude/*` and `codex/*` | Retained prior work and alternative slices; compare with round 6 before reusing. |

The recovered detached worktrees are independently preserved, even where their
files overlap other branches:

| Recovery branch | Original worktree name |
| --- | --- |
| `codex/handoff-2026-11-13-cov-chain-admin-wt` | `cov-chain-admin-wt` |
| `codex/handoff-2026-11-13-cov2-e2e-deposit` | scratchpad `cov2-e2e-deposit` |
| `codex/handoff-2026-11-13-proof-attempt-4f3778` | `proof-attempt-4f3778` |

## Review and verification still needed

This session backed up work and verified Git state. It did **not** build the Lean
package, run the axiom audit, validate new proof statements, or establish source
correspondence. A WIP checkpoint is a continuation point and carries no review or
proof-validation claim. No branches were merged during this backup.

1. Fetch `origin` and start from `claude/proof-round-6`. Compare each candidate
   branch with that integration branch before carrying changes across. Several
   branches share a base or duplicate partially integrated work.
2. Review the intended Solidity pin and each topic's `Specs/`, `Properties/`,
   `Proofs/`, README, and assumption entries. Consult `PROVENANCE.md`,
   `ASSUMPTIONS.md`, `REVIEW.md`, and `ASSET_BRIDGING_VERIFICATION_PLAN.md`.
3. Finish the selected modules and wire their imports into `EraSpec.lean`.
   The default build/audit cannot establish coverage of files it never imports.
4. Run the repository checks for the resulting candidate:

   ```bash
   lake build EraSpec
   ./scripts/audit-axioms.sh
   ./scripts/check-word-fidelity.sh
   ./scripts/emit-solidity.sh --check
   ```

   The round-6 toolchain is `leanprover/lean4:v4.35.0`. The historical handoff
   records a pending human review of Word.lean/baseline changes; investigate any
   fidelity failure rather than automatically accepting a new baseline. The
   current audit script includes planted-defect self-tests; rerun the current
   script rather than relying on the historical round-5 audit counts.
5. Review and integrate selected branches individually after checks. Model proofs
   and logical dependency audits do not establish deployed Solidity/EVM behavior.

[The November 11 handoff](../../HANDOFF.md#historical-handoff--2026-11-11) remains
historical context. Its branch inventory, proposed audit fixes, review counts,
and environment paths may be superseded. Its note that separate local-only
findings material existed does not mean that material is available in this
checkout; this session found no `local/handoff-full` branch.
