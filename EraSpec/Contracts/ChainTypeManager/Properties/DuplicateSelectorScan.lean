import EraSpec.Contracts.ChainTypeManager.Specs.DuplicateSelectorScan

/-!
# Properties: the duplicate-selector scan is exact

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.DuplicateSelectorScan`. Proofs are
in `EraSpec.Contracts.ChainTypeManager.Proofs.DuplicateSelectorScan`.

* **The open-addressing scan reverts exactly when a selector appears twice**
  (`DuplicateScanIffNodup`), for 4-byte selectors. Linear probing with no deletions finds a
  repeated entry on its own probe path before any empty slot, and a table of `2·n + 1` slots
  holding fewer than `n + 1` entries always has an empty slot, so the `while` loop ends.
* **So `validate()`'s facet checks, as coded, are `RowsWf`** (`ValidateRowsIffRowsWf`), and
  `LiveRouting`'s equivalence holds for every release that passed the code of `validate()`
  (`CountCheckExactAfterValidate`): the counting check is exact, from `validate()`'s code to
  `requireReleaseRouting`'s code, on consistent diamond storage.

`DuplicateScanWitness` exercises a home-slot collision, both duplicate shapes, and the witness
world's release.
-/

namespace Contracts.ChainTypeManager

/-- **THE SCAN REVERTS EXACTLY ON A REPEATED SELECTOR.** For selectors that are 4-byte values,
`_requireNoDuplicateSelectors(routing)` succeeds if and only if no selector appears twice in
the rows, read in order. -/
def Properties.DuplicateScanIffNodup : Prop :=
  ∀ routing : List (List Selector), (∀ x ∈ routing.flatten, x < 2 ^ 32) →
    (NoDuplicateScanPasses routing ↔ routing.flatten.Nodup)

/-- **`validate()`'s FACET CHECKS, AS CODED, ARE `RowsWf`.** For 4-byte selectors, the
nonempty-list check and the scan pass exactly when every row self-describes a selector and no
selector appears twice. -/
def Properties.ValidateRowsIffRowsWf : Prop :=
  ∀ (sel : Address → List Selector) (rows : List FacetRow),
    (∀ fb ∈ rows, ∀ x ∈ sel fb.1, x < 2 ^ 32) →
    (ValidateRowsPasses sel rows ↔ RowsWf sel rows)

/-- **HEADLINE, CODE TO CODE: AFTER `validate()`, THE COUNTING CHECK IS EXACT ROUTING.** On
diamond storage satisfying `DiamondOk`, for a release whose rows pass `validate()`'s facet
checks as coded (4-byte selectors), `requireReleaseRouting` passes if and only if the proxy
routes exactly the release's flattened rows. -/
def Properties.CountCheckExactAfterValidate : Prop :=
  ∀ (sel : Address → List Selector) (ds : DiamondStorage) (rows : List FacetRow),
    DiamondOk ds → (∀ fb ∈ rows, ∀ x ∈ sel fb.1, x < 2 ^ 32) → ValidateRowsPasses sel rows →
    (CountCheck sel ds rows ↔ ds.routing = rowsRouting (flattenRows sel rows))

/-- **THE SCAN RESULTS ARE NOT VACUOUS.** Selectors `1` and `6` have entries `2` and `7`, which
share home slot `2` of a 5-slot table, and still pass; a repeated selector fails, in one row
or across rows; and release `100` of the witness world passes `validate()`'s facet checks,
with 4-byte selectors, while its genesis diamond satisfies `DiamondOk` and passes the count
check. -/
def Properties.DuplicateScanWitness : Prop :=
  scanEntry 1 % 5 = scanEntry 6 % 5 ∧ NoDuplicateScanPasses [[1, 6]] ∧
    ¬ NoDuplicateScanPasses [[1], [1]] ∧ ¬ NoDuplicateScanPasses [[1, 6], [6]] ∧
    (∀ fb ∈ wDWorld.genesisFacets 100, ∀ x ∈ wDWorld.selectors fb.1, x < 2 ^ 32) ∧
    ValidateRowsPasses wDWorld.selectors (wDWorld.genesisFacets 100) ∧
    ∃ ds, diamondCut DiamondStorage.fresh (newChainInstallations wDWorld 100) = some ds ∧
      DiamondOk ds ∧ CountCheck wDWorld.selectors ds (wDWorld.genesisFacets 100)

end Contracts.ChainTypeManager
