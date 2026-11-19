import EraSpec

/-!
# List every property statement, for the renames check

Prints the fully qualified name of every property statement, one per line and sorted, so that two
commits can be diffed. A property statement is a `def` (or `abbrev`) in a Properties module of
`EraSpec` (a module with a `Properties` name segment), exactly what `scripts/Audit.lean` counts as
a property, by the same predicates (`EraSpec.Core.Headline`):

```bash
lake build EraSpec && lake env lean scripts/ListProperties.lean > before.txt
# ... after the consolidation step ...
lake build EraSpec && lake env lean scripts/ListProperties.lean > after.txt
comm -23 before.txt after.txt   # every line must be an "old" in the unit's renames file
```

Internal auxiliaries (`_proof_1`, …) are left out. With `ERASPEC_PROPERTIES_OUT=<file>` set, the
list goes to that file instead of the output. See `CONSOLIDATION.md`.
-/

open Lean Elab Command
open EraSpec.Headline (isPropertiesModule isUserDecl)

-- The same predicate as the audit's (`EraSpec.Core.Headline`): a `def` in a Properties module,
-- not a Lean auxiliary. Private declarations are listed too (the audit rejects them).
run_cmd do
  let env ← getEnv
  let mut names : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some modIdx := env.getModuleIdxFor? n | continue
    let some modName := env.header.moduleNames[modIdx.toNat]? | continue
    unless ci matches .defnInfo _ do continue
    unless isPropertiesModule modName && isUserDecl n do continue
    names := names.push s!"{n}"
  let text := String.intercalate "\n" (names.qsort (· < ·)).toList ++ "\n"
  match ← IO.getEnv "ERASPEC_PROPERTIES_OUT" with
  | some path =>
    IO.FS.writeFile path text
    logInfo m!"{names.size} names written to {path}"
  | none => IO.print text
