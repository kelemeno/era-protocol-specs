# Current handoff — 2026-11-18

Continue from **`claude/proof-round-8`**. This note covers the code up to `ad42117`; the only later commit adds
this note.
Nothing was pushed to `master` and no PR was opened. Ask Kalman before pushing to `master`, opening or merging
PRs, or publishing anything about a possible upstream (era-contracts) issue.

**Do consolidation first.** Round 8 roughly doubled the spec, so the next job is to make what exists coherent:
one target commit, shared models, and a short list of real guarantees. Only after that should anyone add new
statements. The plan is below.

## State of `claude/proof-round-8`

- **Toolchain:** Lean v4.35.0 + Mathlib v4.35.0, unchanged since round 5.
- **Audit at `ad42117`** (`./scripts/audit-axioms.sh`): 28198 theorems, 4447 properties each with its full
  named theorem, 0 axioms, 0 NOT clean. `lake build EraSpec` builds 3963 jobs.
- **Round 8 merged about 90 work units on top of round 7.** Every unit had an independent adversarial review
  covering faithfulness to the cited Solidity, non-vacuity of witnesses, and docstring precision. Units sent
  back for fixes were repaired and re-reviewed before merging, and a later pass applied the reviewers' minor
  issues. The units fall into these families:
  - **Salvage of the earlier unmerged branches:** `strengthen-12`; the `codex-findings` 12 and 14 fixes;
    `faithfulness-repair` 5–10; `head-fixes` 1–8; the `up/*` v35 upgrade-system topics; the `repin-v35` 13–21
    re-pins; `wave3a` 1 and 3–10; and the `cov/*` coverage topics AdminFacet, Bridgehub, ChainAssetHandler,
    Diamond, ExecutorFacet, InteropRoot, L1Nullifier, MessageRoot and ValidatorTimelock.
  - **New v35 targets:** about 20 new topics proved against `draft/v0.35.0` head `b17415d20`, covering the
    InteropPool ledger, Merkle root paths, the ZKsync OS DA validators, L2 tables, the leg-source filter,
    ChainBatchRootTree, the peer mirror, Stage-1, the priority-tree mirror, recovery neutrality and others.
- **Held back locally:** a few finished units pending Kalman's sign-off, plus the local-only branches named in
  the 2026-11-11 note. Do not recreate or publish them.

## Priority 1: consolidation (before any new statements)

### Why

- **Too many targets.** The models are spread over six era-contracts commits. 125 Specs files cite the
  abandoned interop pin `c67894b9` and 113 cite the v35 head `b17415d20`; others cite `e561b9cc2`, `d9f6789`,
  `70096e2ea` and `3605e82`.
- **Re-models next to originals.** 32 topics are `…AtHead` / `…AtV35` / `…V35` re-models that sit next to
  their pin original. IndexedMerkleTree, for example, has the pin model, `UnboundedSearchAtV35` and
  `HintSearchAtHead`.
- **Duplicated models.** Several contracts have more than one independent model. Some topic READMEs say so
  explicitly ("does not reuse another topic's tracker model"). Results over different models don't compose.
- **A misleading count.** The 4447 "properties" include witnesses, countermodels and supporting lemmas, and
  no single place lists the headline guarantees.
- **Docs past usefulness.** `ASSUMPTIONS.md` has about 314 rows. Many READMEs carry several pin sentences
  that were patched merge after merge, and the namespaces reuse parent names (`State`, `Step`, `Inv`, ...).

### Plan, in order

1. **One target commit: v35 `b17415d20`.** Kalman chose v35; v36 is unfinished.
   - Where a topic has both a pin model and a v35 or head re-model, keep the v35 one as the topic and move the
     pin one into a `History` namespace and folder, or delete it if it adds nothing.
   - Keep the countermodels that document the fixed pin findings (H1 forged refund, H2 IMT padding, M1 custom
     handlers; see the 2026-11-11 note). They are the record of those fixes.
   - Re-pin the topics that exist only at `c67894b9`, `d9f6789` or `e561b9cc2` to `b17415d20`, or state
     exactly what differs. This replaces the old "re-pin wave".
2. **One shared model per contract.** Pick the most complete Specs model of each contract and restate the
   other topics' properties over it, or prove a refinement or simulation lemma between the models (several
   such bridges already exist). Delete the redundant models once their properties move.
   - Start with the most duplicated: the interop and atomic stack (InteropCenter, InteropHandlerBase,
     AtomicFlowManager, Protocol/InteropAtomicity); L2AssetTracker together with NativeTokenVaultBase and
     L1NativeTokenVault; IndexedMerkleTree with L2InteropCommitmentTree; MessageRoot with
     L2InteropRootStorage and ChainBatchRootTree; and ProxyUpgradeExecutorBase with SecondProofSystem and
     ChainTypeManager.
3. **A headline index.** For each contract and protocol area, write a short list in its README of the real
   guarantees, each with every premise in plain words. Make the audit report headlines separately from
   witnesses and lemmas, for example by a naming or attribute convention plus a check in `scripts/Audit.lean`,
   so the property count means something.
4. **Split `ASSUMPTIONS.md` by area.** Drop rows that only restate model boundaries already in a Specs header,
   and keep the ids stable, since docstrings cite them.

### Rules for consolidation

The tags, the `History` folder convention and the renames file format are in
[CONSOLIDATION.md](CONSOLIDATION.md).

- **Never weaken a statement.** Moving a property to a shared model must keep it at least as strong. If it
  cannot, say so and keep the old one.
- **Every step must pass the checks.** Each step keeps `lake build EraSpec` and the audit passing.
- **Review each step.** One folder or contract per step, each independently reviewed for no lost guarantee,
  no vacuous witness and docs that match the Lean.
- **Track every removal.** Keep a mapping from every removed or renamed property to its replacement, for
  example `handoff/<date>/renames.json`. External references and the audit history depend on the names.

### Done when

- Every model cites one commit (`b17415d20`, or `History/` for pin records).
- Each contract has one Specs model.
- Every README starts with its headline guarantees.
- The audit reports headlines and witnesses separately.

## Priority 2, only after consolidation

- **Unfinished coverage units.** They are on these `origin` branches: `cov/mailbox`; `cov2/da`, `e2e-deposit`,
  `e2e-migration`, `encodings`, `l2-bridge`, `l2-system`, `l2-upgrades`, `merkle-libs`, `misc-core` and
  `verifier-routing`; and `cov/chain-admin`, which is held. Round 8 progressed several of them in local
  worktrees, unreviewed.
- **The Codex review fixes** from the round-6/7 review: claim and witness gaps in the root-import, refund and
  timeout topics. Partly done locally, unchecked. Several will be resolved by consolidation.
- **A final citation re-check** of every Solidity file:line against `b17415d20`, after step 1.
- **New statements**, only on the consolidated models.

## Branches on `origin`

- **`master`** is untouched.
- **`claude/proof-round-5` to `-8`** are the continuation line; round 8 contains round 7.
- **124 branches fully contained in round 8 were deleted on 2026-11-18.** Containment was checked twice:
  ancestry, and GitHub's compare API.
- **8 more branches are now contained:** the `cov/*` units merged this afternoon and `wip/repin-v35/20`.
  They can be deleted the same way.
- **37 hold work not in round 8:**
  - the unfinished `cov` and `cov2` units above;
  - `wip/modernize/1-15`, which modernizes proof bodies for the 4.35 tactics with statements untouched.
    They were never reviewed, so redo them after consolidation instead of merging them;
  - `wip/wave3a/2` and `wip/wave3a/7`, `up/second-proof-across-migration-v35` and
    `up/second-proof-upgrade-gate-v35`. Round 8 used their content, but not their commits, so git doesn't
    count them as contained;
  - `salvage/codex-findings-11` and `wip/codex-findings/11`, which are held;
  - three `codex/handoff-2026-11-13-*` branches and `claude/proof-attempt-handoff-caa64d`, which are earlier
    saves of the same coverage work.

## Environment

- **Machine:** Kalman's Mac mini (`samsara` account). elan is at `~/.elan`; the Mathlib cache is in
  `.lake/packages`.
- **era-contracts sources.** Make a `--filter=blob:none` clone of matter-labs/era-contracts, then fetch
  `e561b9cc2b946672d1f5f61dd0c993f27bd7acab` by full SHA (its branch was deleted). Add a detached
  `git worktree add` for each commit: `b17415d20` (draft/v0.35.0 head; the target), `70096e2ea` (main head),
  `d9f6789`, `c67894b9`, `e561b9cc2` and `3605e82`. `git archive` produces nothing on a blob-less clone. The
  macOS cleaner deletes `/tmp` files left untouched for 3 days, so keep the trees outside `/tmp` or recreate them.
- **Local notes.** Round-8 notes, backlogs, review journals and the held units' details are local only, in
  `~/code/era-round8-local/` on the Mac mini (`STATUS.md`). Ask Kalman before using anything from there in a
  public file.
- **`scripts/check-word-fidelity.sh`** still lists the `Core/Word.lean` port entries pending Kalman's sign-off.

## Previous handoffs

- [2026-11-16](handoff/2026-11-16/README.md): round 7, merged and reviewed salvage, the padding-forgery
  correction notes, and a [branch inventory](handoff/2026-11-16/branches.json).
- [2026-11-13](handoff/2026-11-13/README.md): round 6 and the 98-branch inventory.
- 2026-11-11: round 5, the Lean 4.35 port, the source findings at the interop pin (H1, H2, M1, fixed on every
  current head) and the low-severity items already in `ASSUMPTIONS.md`. Its text, together with the 2026-11-13
  and 2026-11-16 pointers, is the previous `HANDOFF.md`, kept verbatim in
  [handoff/2026-11-16/HANDOFF-previous.md](handoff/2026-11-16/HANDOFF-previous.md). Its reports are in
  [handoff/2026-11-11/](handoff/2026-11-11/).

These are historical. Their branch lists and review results do not describe round 8.
