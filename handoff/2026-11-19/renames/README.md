# Renames, 2026-11-19 consolidation

One file per consolidation unit: `<unit>.json`. It records every property statement (a `def` in a
Properties module) that the unit removed or renamed, so that external references to the old names
can be followed. The conventions are in [CONSOLIDATION.md](../../../CONSOLIDATION.md).

## Format

Each file is a JSON array of objects:

```json
[
  {
    "old": "<fully qualified old Properties name>",
    "new": "<fully qualified new name or null>",
    "kind": "moved",
    "justification": "<one sentence>"
  }
]
```

| Field | Content |
|---|---|
| `old` | The fully qualified name of the Properties def at the unit's branch point, e.g. `Contracts.BridgedStandardERC20.Properties.burn_exact`. |
| `new` | The fully qualified name of its replacement at the unit's head, or `null` when there is none. |
| `kind` | One of `moved`, `renamed`, `restated-on-shared-model`, `history`, `removed-duplicate`, `removed-obsolete`. |
| `justification` | One sentence. For `restated-on-shared-model`: why the new statement is at least as strong as the old one. For `removed-duplicate`: the surviving equivalent name. |

The kinds:

- `moved`: the same statement under a new name, for example in another module or namespace.
- `renamed`: the same statement, renamed in place.
- `restated-on-shared-model`: restated over the contract's shared model, at least as strong.
- `history`: moved under a `History` folder and namespace, as the record of an older pin.
- `removed-duplicate`: removed because an equivalent statement survives (named in `justification`).
- `removed-obsolete`: removed with no replacement; `justification` says why nothing is lost.

## Completeness

Every Properties def name that exists on `claude/proof-round-9` at the unit's branch point but not
at its head must appear as an `old`. Check it mechanically: after a full `lake build EraSpec` at
each commit, run `lake env lean scripts/ListProperties.lean > before.txt` (then `after.txt`). It
lists every property statement, sorted. `comm -23 before.txt after.txt` prints the names that must
appear as an `old`.
