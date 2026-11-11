import EraSpec.Contracts.ChainTypeManager.Specs.DuplicateSelectorCheck

/-!
# Properties: `_requireNoDuplicateSelectors` is exactly `ReleaseWf`

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.DuplicateSelectorCheck`. Proofs
are in `EraSpec.Contracts.ChainTypeManager.Proofs.DuplicateSelectorCheck`.

* **The check is exact** (`DuplicateCheckIsExact`): `_requireNoDuplicateSelectors` returns iff
  no selector appears twice across all of a release's facets. It has no false alarm and misses
  no repeat, and the loop never runs out of slots.
* **Any table with more slots than selectors would do**
  (`DuplicateCheckExactForAnyLargerTable`). The `2 * total + 1` sizing keeps probes short; it
  is not needed for correctness.
* **`ReleaseWf` is what `validate()` checks** (`ReleaseWfIsTheDuplicateCheck`). When the model's
  flattened routing of a release lists the facets' selectors in row order, which is how
  `World.relRows` reads `genesisFacets()` and `selectors()`, `ReleaseWf` holds iff the check
  returns. So `Op.InstallsWf` for a commit is the statement that `validate()`'s duplicate check
  passed on the arriving release, which every successful `_setCurrentRelease` requires.
-/

namespace Contracts.ChainTypeManager

/-- **THE DUPLICATE CHECK IS EXACT.** `_requireNoDuplicateSelectors(routing)` returns, rather
than reverting, iff the selectors of all facets together list no selector twice. -/
def Properties.DuplicateCheckIsExact : Prop :=
  ∀ routing : List (List Selector), noDuplicateSelectors routing = true ↔ routing.flatten.Nodup

/-- **ANY TABLE LARGER THAN THE SELECTOR COUNT GIVES THE SAME ANSWER.** Run with any table size
`n` above the number of selectors, the loops return iff no selector repeats. -/
def Properties.DuplicateCheckExactForAnyLargerTable : Prop :=
  ∀ (routing : List (List Selector)) (n : ℕ), selectorTotal routing < n →
    ((insertRouting n (fun _ => 0) routing).isSome = true ↔ routing.flatten.Nodup)

/-- **`ReleaseWf` IS WHAT `validate()` CHECKS.** Suppose the model's flattened routing of release
`r` lists the facets' self-described selectors in row order, as `World.relRows` reads
`genesisFacets()` and each facet's `selectors()`. Then `ReleaseWf W r` holds iff
`_requireNoDuplicateSelectors` returns on those lists. -/
def Properties.ReleaseWfIsTheDuplicateCheck : Prop :=
  ∀ (W : World) (r : Address) (routing : List (List Selector)),
    (W.relRows r).map Prod.fst = routing.flatten →
    (ReleaseWf W r ↔ noDuplicateSelectors routing = true)

/-- **THE CHECK RUNS AS DESCRIBED, PROBING INCLUDED.**

* Releases `100` and `260` of the duplicate-selector witness world meet the premise of
  `ReleaseWfIsTheDuplicateCheck` with their per-facet lists `[[1, 2]]` and `[[1, 2], [1]]`.
  The check passes on the first and reverts on the second.
* With three selectors the table has 7 slots, and `0`, `7` and `14` (entries 1, 8 and 15) all
  hash to slot 1. The check stores all three by probing past occupied slots. The check reverts
  when `7` comes back, which it finds only after probing past `0`'s slot. -/
def Properties.DuplicateCheckWitness : Prop :=
  (wEnDupWorld.relRows 100).map Prod.fst = [[1, 2]].flatten ∧
    noDuplicateSelectors [[1, 2]] = true ∧
    (wEnDupWorld.relRows 260).map Prod.fst = [[1, 2], [1]].flatten ∧
    noDuplicateSelectors [[1, 2], [1]] = false ∧
    noDuplicateSelectors [[0, 7], [14]] = true ∧ noDuplicateSelectors [[0, 7], [7]] = false

end Contracts.ChainTypeManager
