import EraSpec.Contracts.ChainTypeManager.Specs.LiveRouting

/-!
# Model: `CTMRelease._requireNoDuplicateSelectors`, an open-addressing set

Source: branch `feat/upgrade-simplification` at `e561b9cc2`, as for the rest of this folder.
Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.DuplicateSelectorScan` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.DuplicateSelectorScan`.

## Why this is modelled

`LiveRouting` states what `CTMRelease.validate()` checks of a release's rows by meaning
(`RowsWf`): no selector appears twice. The code does not compare pairs; it inserts every
selector into a hash table (`upgrades/registry/objects/CTMRelease.sol:186-213`):

    /// @dev An open-addressing set over the release's selectors: a pairwise scan of the ~a hundred
    ///      selectors costs ~0.9M gas. A slot holds
    ///      `selector + 1`, so zero marks it empty; the table is never more than half full, so a
    ///      probe always ends at an empty slot.
    function _requireNoDuplicateSelectors(bytes4[][] memory _routing) private pure {
        uint256 total = 0;
        for (uint256 i = 0; i < routingLength; ++i) { total += _routing[i].length; }
        uint256 tableSize = 2 * total + 1;
        uint256[] memory table = new uint256[](tableSize);
        for (uint256 i = 0; i < routingLength; ++i) {
            bytes4[] memory selectors = _routing[i];
            for (uint256 j = 0; j < selectorsLength; ++j) {
                uint256 entry = uint256(uint32(selectors[j])) + 1;
                uint256 slot = entry % tableSize;
                while (table[slot] != 0) {
                    if (table[slot] == entry) { revert RegistryDuplicateSelector(selectors[j]); }
                    slot = (slot + 1) % tableSize;
                }
                table[slot] = entry;
            }
        }
    }

This file transcribes it; `Properties.DuplicateScanIffNodup` says it reverts exactly when a
selector appears twice.

## Modelling choices

* **The table is a map `ℕ → ℕ`**, zero everywhere at the start (`new uint256[](tableSize)`).
  Every index the code touches is below `tableSize` (it is reduced `% tableSize`).
* **`uint32(selector)` is `selector % 2^32`.** A `bytes4` selector is a value below `2^32`, on
  which this is the identity; the theorem assumes it.
* **The `while` loop gets `tableSize` iterations of fuel**, running out being a revert. The
  source loop always ends at an empty slot because the table is never full; the proof shows
  the fuel is never exhausted, so the bound changes nothing.
* **`total` is the number of selectors** (the sum of the row lengths; the checked addition
  cannot overflow for any list that fits in memory).
-/

namespace Contracts.ChainTypeManager

/-- `uint256(uint32(selector)) + 1` (`CTMRelease.sol:202`): a selector's table entry; zero
marks an empty slot. -/
def scanEntry (x : Selector) : ℕ := x % 2 ^ 32 + 1

/-- The probe of one selector (`CTMRelease.sol:203-210`), from slot `slot`, with `fuel`
iterations of the `while` loop left: an empty slot takes the entry, a slot holding the same
entry reverts, any other slot moves on to the next one, cyclically. -/
def scanProbe (size : ℕ) (table : ℕ → ℕ) (entry : ℕ) : ℕ → ℕ → Option (ℕ → ℕ)
  | 0, _ => none
  | fuel + 1, slot =>
      if table slot = 0 then some (upd table slot entry)
      else if table slot = entry then none
      else scanProbe size table entry fuel ((slot + 1) % size)

/-- The loop over every selector of every row, in order (`CTMRelease.sol:198-212`): each one
is probed from its entry's home slot `entry % tableSize`. -/
def scanLoop (size : ℕ) : (ℕ → ℕ) → List Selector → Option (ℕ → ℕ)
  | table, [] => some table
  | table, x :: xs =>
      (scanProbe size table (scanEntry x) size (scanEntry x % size)).bind fun t =>
        scanLoop size t xs

/-- **`_requireNoDuplicateSelectors(routing)` does not revert** (`CTMRelease.sol:190-213`):
the table has `2 * total + 1` slots, `total` being the number of selectors. -/
def NoDuplicateScanPasses (routing : List (List Selector)) : Prop :=
  (scanLoop (2 * routing.flatten.length + 1) (fun _ => 0) routing.flatten).isSome

/-- The facet-row part of `CTMRelease.validate()` as the code does it (`CTMRelease.sol:112-128`):
every row's self-described selector list is nonempty, then the scan over all of them. -/
def ValidateRowsPasses (sel : Address → List Selector) (rows : List FacetRow) : Prop :=
  (∀ fb ∈ rows, sel fb.1 ≠ []) ∧ NoDuplicateScanPasses (rows.map fun fb => sel fb.1)

end Contracts.ChainTypeManager
