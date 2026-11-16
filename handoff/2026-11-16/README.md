# Continuation handoff — 2026-11-16

Kalman can continue from **`claude/proof-round-7`**. It is `claude/proof-round-6`
(`dffd2dc`) plus three reviewed salvage merges and the fixes from an independent review of
the merged result. Its code checkpoint before this documentation commit is
`d92dad53587832b4e202a6c44e63c51ee718f12b`. Nothing was pushed to `master` and no PR was
opened.

## What this session did

1. **Checked round 6.** At `dffd2dc`, `lake build EraSpec`, the axiom audit and
   `emit-solidity.sh --check` pass, and `check-word-fidelity.sh` lists the 9 entries still
   pending sign-off. The 2026-11-13 note had not run these checks.
2. **Reviewed candidate branches.** Independent adversarial reviews of
   `salvage/strengthen-12`, `salvage/strengthen-13`, `salvage/faithfulness-repair-1` and of
   the branches merged below. A clean build and audit were not enough: on several branches
   the headline docstrings claimed more than the statements prove.
3. **Merged into `claude/proof-round-7`**, in this order, each as `Merge … (reviewed)`:
   - `salvage/codex-findings-9`: the destination half of the atomic-interop gate
     (`Contracts.RootImport`: `ImportAvailable`, `SettlementDataAvailable`, destination
     forms of none-or-all). It answers the Codex-review item "finalizable ignores destination
     root import" listed in `HANDOFF.md`.
   - `salvage/faithfulness-repair-2`: five `AtomicInteropProof` repair topics
     (`LastBatchInRootOffset`, `LastLeafFaithful`, `ProofPolarityFaithful`,
     `StaleSnapshotFaithful`, `StaleSnapshotBranches`). `LastBatchInRootOffset` and the
     `PROTO-CONTIGUOUS-PUSH` assumption answer the item "timeout composition conflates batch
     number with leaf position".
   - `salvage/strengthen-13`: pinned witnesses for the reference bridge's END branch
     (`Examples/BurnMintBridge`, `EndBranchStrong`), then its review-fix commit `3468939`.
4. **Reviewed the merged result** at `3468939`, per topic and for integration, with every
   finding re-checked by a skeptic: 16 should-fix findings and about 25 nits, and no proved
   statement false. Most were documentation that claimed more than the Lean shows, and
   witnesses that held for a trivial reason (an empty flow, a zero value, every example at
   batch 0).
5. **Fixed them** in eight commits, `ac870ba` to `d92dad5`. A fresh checker reviewed each
   fix commit, and commit messages were corrected where a sentence did not match the diff.
   New statements back claims that were only prose before, for example the stale-root
   countermodel `StaleImportFlowSitsHalfExecuted`, `WithoutCoverageCrossDestinationFails`,
   the BEGIN-branch gaps `BeginBranchRefundWitnessBranchGap` and
   `BeginBranchRefundWitnessSingleRootGap`, and satisfiability witnesses that commit real
   values.
6. **Padding-forgery notes.** Many older headline docstrings read as guarantees for the
   deployed contract, while the statement rests on `HashAssumptions` (unsatisfiable) or on a
   genuine-leaf absence witness. At `c67894b9`, `IndexedMerkleTree.setup` pads empty slots
   with `hashLeaf({0,0,0})`, so the deployed `verifyNonInclusion` can accept a forged absence
   proof with no hash collision. This is H2 in the 2026-11-11 handoff, fixed upstream by
   `78e14b3bc`. There is now one note at `HashAssumptions`
   (`L2InteropCommitmentTree/Specs/TreeRoot.lean`), and a "Correction
   (StaleSnapshotFaithful)" note or pointer on every docstring that needed one. A final check
   went through all 464 statements involving an absence or refund check. The marked readings
   are listed in `AtomicInteropProof/Properties/StaleSnapshotFaithful.lean`. No statement or
   proof changed in this step.
7. **Fixed two more branches without merging them** (see the table below).

## Checks at the round-7 checkpoint (`d92dad5`)

- `lake build EraSpec`: 3574 jobs, success.
- `./scripts/audit-axioms.sh`: OK. 9421 theorems, 1948 properties (each with its named
  theorem), 10850 other declarations, 2326 axiom-free, 0 axioms, 0 not clean. Before the fix
  commits, at `3468939`: 9304 theorems, 1930 properties.
- `./scripts/emit-solidity.sh --check`: passes.
- `./scripts/check-word-fidelity.sh`: fails with the same 9 entries as round 6 (the Lean
  4.35 port of `Core/Word.lean`). `scripts/word-baseline.json` was not updated; it still
  needs a human sign-off.
- From `3468939` to `d92dad5`, code changed only in the round-7 topics (`RootImport`, the five
  `AtomicInteropProof` repair topics, `EndBranchStrong`). Every older Lean file changed in
  comments only.

## Branches

| Branch | Commit | State |
| --- | --- | --- |
| `claude/proof-round-7` | this commit | Integration branch. |
| `salvage/faithfulness-repair-1-fixed` | `f07cb6d` | `salvage/faithfulness-repair-1` plus review fixes, merged with round 6 and round 7 at `3468939`. Re-reviewed independently. Merges into `claude/proof-round-7` without conflicts. Not merged. |
| `salvage/strengthen-12-fixed` | `aa19ce8` | `salvage/strengthen-12` plus review fixes, merged with round 6 and round 7 at `3468939`. The fixes have not had an independent re-review. One `ASSUMPTIONS.md` conflict with `claude/proof-round-7`. Not merged. |

The `-fixed` names keep the original `salvage/*` branches on `origin` unchanged.
[`branches.json`](branches.json) lists these with full SHAs. It also records, for every
`origin` branch not contained in `claude/proof-round-7`, whether it merges into it cleanly:
of 107 such branches, 91 merge cleanly and 16 conflict, most of them only on `EraSpec.lean`
import lines.

## Still open

1. Merge `salvage/faithfulness-repair-1-fixed`.
2. Re-review the `salvage/strengthen-12-fixed` fixes, resolve its `ASSUMPTIONS.md` conflict,
   then merge.
3. The other unmerged branches were not reviewed in this session. `up/*`,
   `salvage/head-fixes-5`/`-6` and `salvage/codex-findings-12` cite files that changed
   upstream: `draft/v0.35.0` was at `9775be9` when last fetched (2026-11-14), two commits
   after the `d9f6789` pin. Re-read them against the new head before merging.
4. The word-fidelity sign-off (above).
5. Not in this public repository: the reviews behind the two unmerged branches, and a
   re-check of the v35-pinned branches against `9775be9`. They are delivered to Kalman
   separately. The re-check found two possible upstream findings for him to assess first.
   Round 7's own review reports are not handed over: each fix commit's message lists the
   findings it addresses.

Commits in round 7 are authored by Valera Grinenko (work address), with `Co-Authored-By`
trailers naming the Claude model that did the work.
