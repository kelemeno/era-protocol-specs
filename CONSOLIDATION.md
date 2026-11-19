# Consolidation conventions

These conventions implement the consolidation plan in [HANDOFF.md](HANDOFF.md) (Priority 1): one
target commit, one shared model per contract, and a headline index that the audit can count. They
apply to every consolidation step.

The target commit is era-contracts `b17415d20` (draft/v0.35.0 head).

## Headline tags

`EraSpec/Core/Headline.lean` defines three tag attributes for property statements, that is for
the `def`s in Properties modules. Import it and tag the statement itself, not its proof:

```lean
import EraSpec.Core.Headline

@[headline] abbrev Properties.balance_bounded … := …
@[witness] abbrev Properties.one_unit_roundtrip … := …
```

| Tag | Meaning |
|---|---|
| `@[headline]` | A real guarantee about the behaviour of `b17415d20`. Its docstring states every premise in plain words, and the folder README lists it. |
| `@[witness]` | A non-vacuity or satisfiability witness for some headline: its premises can all hold, or the guarded call can succeed. |
| `@[countermodel]` | Shows that a stronger reading of some headline is false, or that one of its premises is necessary. |
| none | A supporting lemma. It is proved and audited like every other property, but it is not a headline. |

`scripts/Audit.lean` counts the headlines, witnesses, countermodels and untagged properties
separately. It prints the same four counts for each contract folder (`EraSpec.Contracts.<C>`) and
protocol area (`EraSpec.Protocol.<A>`) as `FOLDER <area> : headline / witness / countermodel /
untagged` lines, so that a README's headline index can be checked against them. The audit rejects:

- a tag on anything that is not a property statement (a `def` in a Properties module), including
  the proof theorem of a property;
- a statement that carries two of the tags;
- a `@[headline]` in a `History` module or namespace (see below). Witnesses and countermodels may
  stay in History.

With `ERASPEC_HEADLINES_OUT=<file>` set, the audit also writes every tagged property to `<file>`,
one per line: tag, folder, statement name and module, separated by tabs.

`scripts/audit-selftest.sh` plants each of these defects and requires the audit to reject it.
[BridgedStandardERC20](EraSpec/Contracts/BridgedStandardERC20/README.md) is the worked example of
a tagged folder with a headline index.

## History folders

Models and properties that are kept only as the record of an older pin, such as the countermodels
of the fixed H1, H2 and M1 findings at `c67894b9`, go under

```
EraSpec/Contracts/<C>/History/{Specs,Properties,Proofs}/...
```

with a `History` namespace segment, for example
`EraSpec.Contracts.IndexedMerkleTree.History.Properties.PinnedGate…`. The folder README says
plainly that History is the record of an older commit, not a claim about `b17415d20`. History
statements are never `@[headline]`s.

## Renames

Every Properties def that is removed or renamed in a consolidation step is recorded in
`handoff/2026-11-19/renames/<unit>.json`. External references and the audit history depend on
these names. The file is a JSON array of objects:

```json
{"old": "<fully qualified old Properties name>",
 "new": "<fully qualified new name or null>",
 "kind": "moved" | "renamed" | "restated-on-shared-model" | "history" | "removed-duplicate" | "removed-obsolete",
 "justification": "<one sentence; for restated: why new is at least as strong; for removed-duplicate: the surviving equivalent name>"}
```

Every Properties def name that exists at a step's branch point but not at its head must appear as
an `"old"`. Check this mechanically: after a full build at each commit, run
`lake env lean scripts/ListProperties.lean`, which lists every property statement sorted, and diff
the two lists (`comm -23 before.txt after.txt` prints the names that must be in the file). See
[handoff/2026-11-19/renames/README.md](handoff/2026-11-19/renames/README.md).

## Rules

These repeat the rules in [HANDOFF.md](HANDOFF.md):

- Never weaken a statement. A property moved to a shared model stays at least as strong; if it
  cannot, keep the old one (possibly under History) and say so.
- Every step keeps `lake build EraSpec`, the audit and the audit self-test passing.
- Each step covers one folder or contract and is reviewed on its own.
