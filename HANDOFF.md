# Current handoff — 2026-11-13

Continue from **`claude/proof-round-6`**. The current [continuation note](handoff/2026-11-13/README.md)
records the saved work, review queue, validation limits, and next steps. Its
[branch inventory](handoff/2026-11-13/branches.json) lists all 98 local branch heads
preserved on `origin`, including three recovered detached worktrees.

The November 11 note below is historical context. Use the current continuation
note for branch locations and backup status; historical review and audit results
are not validation of the newly saved WIP work.

## Historical handoff — 2026-11-11

### End of the round-5 session

Branch **`claude/proof-round-5`** on GitHub (`kelemeno/era-protocol-specs`) is the single line of work.
GitHub has: `master` (3a1c799, untouched), `claude/proof-round-5`, and 72 `wip/*` branches (below).
Every older branch (proof-attempt, codegen-token-slice, codex/prepared-application-guarantees,
port-bridge-upgrade, worktree-wf_137a7bf5-*) was verified contained and deleted.

Rules that still hold: ask Kalman before pushing to `master` or opening/merging PRs. Never claim a
source finding upstream without telling him first.

## State of `claude/proof-round-5`

- **Toolchain: Lean v4.35.0 + Mathlib v4.35.0** (ported from 4.9.1, which does not run on this
  macOS). `Core/Word.lean` re-registers `Fin.instCommRing` for `UInt256` (Mathlib scoped it);
  `rfl` checks show numerals/casts/ring ops compute as on 4.9.1. `scripts/Audit.lean` ported.
- **Audit (`./scripts/audit-axioms.sh`): 7836 theorems, 1588 properties each with its full named
  theorem, 0 axioms, 0 unclean.** `./scripts/emit-solidity.sh --check` passes (generated Solidity
  byte-identical after the port).
- **Pending your sign-off:** `scripts/check-word-fidelity.sh` flags the Word.lean port edits against
  `scripts/word-baseline.json` (the baseline is a human review gate; not updated).
- Round 5 merged: backlog items B1–B7, A1–A5, U1–U8, R1–R3, S1–S4, O1–O4 (31 items), each proved
  in its own worktree, adversarially reviewed, repaired where needed. Round-5 docs are in
  ASSUMPTIONS.md / READMEs (wave-1 items; wave-2 docs B3–B5, S2, S4, A5 not yet written — their
  doc text is in `handoff/2026-11-11/reports/wave2.json`, `results[].prove.docUpdates`).

## Source findings (era-contracts)

Spec-side reports: `handoff/2026-11-11/`. Source-finding reports and PoCs: local-only (see below).

**Real at the interop pin c67894b9, fixed on every current head** (pin is an abandoned
`ad-atomic-interop` lineage; Foundry PoCs pass against real pinned bytecode, judged independently):
- H1 forged atomic refund — direct call in an atomic bundle mints unbacked tokens (500,000e18 in
  the PoC). Upstream knew: PR #2282 (closed), fixed by #2315/#2348.
- H2 IMT padding forgery — absence proof for a delivered leg. Fixed by 78e14b3bc ("F-04").
- M1 custom-handler legs unrefundable and lock the bundle refund. Fixed by #2339.

**Live on current branches (low severity, already listed in ASSUMPTIONS.md):**
- `replaceUpgradeTransition` never checks the replacement's `oldProtocolVersion` (needs governance
  to approve a non-genuine transition).
- CTM `renounceOwnership` not disabled; zero receiver accepted at burn.
- `ICTMUpgradeExecutor.upgradeChain` NatSpec "upgrade at any time" is false (timestamp, batches
  executed, settlement-layer checks apply) — unchanged on every head.

**Not in this public repo:** this repository is PUBLIC. Further findings on current heads — one of
them potentially high severity — together with the Foundry PoCs, the Codex reviews and the
source-finding reports, are kept in the local-only branch `local/handoff-full` (commit ddcb709) on
Kalman's Mac mini. Ask Kalman before publishing any of them.

## Spec problems found (not yet fixed on the branch)

- Codex review: 3 `Audit.lean` loopholes (universe-specialized proofs pass; unused `sorry` defs
  escape; `opaque` properties skip coverage); emitter prints Bool literal 2 as `true` (GEN-EMIT
  counterexample, current program unaffected); timeout composition conflates batch number with leaf
  position; "finalizable" ignores destination root import. Full reviews: local-only.
- Faithfulness audit: 29 confirmed model-vs-Solidity mismatches (12 major) — report local-only.
- Property-strength hunt: 46 confirmed weak properties — report local-only.
- Upstream drift: 23 models stale vs heads, 9 findings fixed upstream (report local-only).

## `wip/*` branches (unreviewed — do not merge blindly)

Seven workflows were stopped mid-run for budget. Each agent's work was committed as-is and pushed as
`wip/<workflow>/<n>` (base 427ba4a or a1e1a41). Some are finished and committed by the agent; others
are a "WIP, unreviewed" commit of a half-done worktree. None passed review. List with last commit
subject: `handoff/2026-11-11/wip-branches.txt`.

| workflow | what it was doing | backlog |
|---|---|---|
| `wip/wave3a/*` | 19 discovery items (W-INT, W-UP, W-X, W-MER, W-BR) | local-only |
| `wip/head-fixes/*` | H-1..H-8: prove the upstream fixes at main, model v35 changes | local-only |
| `wip/strengthen/*` | strengthened forms of the 46 weak properties | local-only |
| `wip/faithfulness-repair/*` | refined models for the 29 mismatches (new files only) | local-only |
| `wip/codex-findings/*` | CF-1..CF-9 (Audit fix, timeout fields, …) | local-only |
| `wip/repin-v35/*` | re-pin interop/bridge models to draft/v0.35.0 d9f6789 | — |
| `wip/modernize/*` | proof bodies with 4.35 tactics, statements untouched | — |

To resume one: check it out, `lake build EraSpec` + its new modules, run the audit with its modules
imported, review against the Solidity, then merge into `claude/proof-round-5` (watch for
declaration-name clashes across items: `handoff/2026-11-11/scripts/declash.py`).

## Suggested next steps

1. Ask Kalman for the local-only findings branch; triage the open finding there first.
2. Fix the three `Audit.lean` loopholes (small, and it protects everything else).
3. Salvage the finished `wip/*` branches that build and pass audit (review each).
4. Re-pin to **draft/v0.35.0 (d9f6789)** — Kalman's chosen target (v36 unfinished).
5. Write the wave-2 docs; apply docstring corrections from faithful/strength reports.

## Environment notes

- Mac mini (`samsara` account): elan at `~/.elan`, Mathlib cache in `.lake/packages`.
- era-contracts sources for the pins/heads were checked out in a session scratchpad (now gone):
  re-create with `git worktree add` from a `--filter=blob:none` clone of matter-labs/era-contracts
  at c67894b9, e561b9cc2, 3605e82 (main), d9f6789 (draft/v0.35.0).
- Forge: `/Users/kalman/.foundry/bin/forge` (1.7.1). Codex: `~/.local/bin/codex exec -s read-only`.
