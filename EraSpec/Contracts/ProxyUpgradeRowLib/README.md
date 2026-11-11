# ProxyUpgradeRowLib

Source: `l1-contracts/contracts/upgrades/registry/libraries/ProxyUpgradeRowLib.sol`
in the registry-driven upgrade system. That code is **not** in the pinned
era-contracts tree. It lives on branch `feat/upgrade-simplification` of the
zksync-era `contracts` repository. The branch was called `claude/musing-clarke-8b5f2c`
when the model was written, and the model's original commit cites that name.

The branch moves, so this model is a snapshot. The model's own header and
commit cite no source commit. The library it describes was last changed at
`ae0698588` (2026-09-16); a later check found the modelled library unchanged at
`612a71cccb65d6db97674997b21427a50bec6206` (2026-09-22). Treat that commit as the
snapshot. The library has changed since. For example, the branch head on
2026-10-19 (`e561b9cc2`) removes `adminOf` and the foreign-admin skip, applies
every row through the applier's own bound admin, and adds a self-edge row check.
The results below describe the snapshot, not the current branch. Re-check the
source before relying on them.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for
the guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence
for those exact named propositions, plus auxiliary lemmas and countermodels.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| Rows | [Specs/Rows.lean](Specs/Rows.lean) | [Properties/Rows.lean](Properties/Rows.lean) | [Proofs/Rows.lean](Proofs/Rows.lean) |

Namespace: `Contracts.ProxyUpgrade`. Statements are `Contracts.ProxyUpgrade.Properties.*`;
each certificate has the same name without the `Properties` segment.

## What to check

Idempotence and replay safety hold as the library claims. The gate claim
(`applyRows` then `requireRowsApplied`) holds only under two side conditions, and
each has a countermodel:

- duplicate rows (`DuplicateRowsBreakPostcondition`, `DuplicateRowsBreakOrder`,
  `DuplicateRowsBreakIdempotence`), which `validateRows` excludes;
- a row naming a foreign `ProxyAdmin` (`ForeignRowLeavesGateOpen`).

`AppliedGatePasses` has an explicit frame premise: between the apply and check
transactions, nothing moved the rows' proxies. The library does not establish
this. Any `ProxyAdmin` owner can move a proxy in between.

Model boundaries (see `MODEL-ROWS` in the [assumption register](../../../ASSUMPTIONS.md)):
a revert is the absence of a step; admin ownership is fixed configuration; the
live implementation is one mapping, read as if every row names the admin that
actually administers its proxy; `callInitializeUpgrade` and events have no effect.
