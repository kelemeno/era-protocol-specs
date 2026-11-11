import EraSpec.Contracts.ChainTypeManager.Specs.Enabledness

/-!
# Model: `CTMRelease._requireNoDuplicateSelectors`, the check behind `ReleaseWf`

Source: `upgrades/registry/objects/CTMRelease.sol` on branch `feat/upgrade-simplification` at
`e561b9cc2`, as for the rest of this folder. Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.DuplicateSelectorCheck` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.DuplicateSelectorCheck`.

`CTMRelease.validate()` reads every facet's self-described selectors,
`routing[i] = ISelfDescribingFacet(facet).selectors()` (:118), and ends with
`_requireNoDuplicateSelectors(routing)` (:128). `Specs/Enabledness.lean` states that check's
documented meaning as `ReleaseWf`. This topic transcribes the check itself (:186-213):

    function _requireNoDuplicateSelectors(bytes4[][] memory _routing) private pure {
        uint256 routingLength = _routing.length;
        uint256 total = 0;
        for (uint256 i = 0; i < routingLength; ++i) {
            total += _routing[i].length;                                    // :193-195
        }
        uint256 tableSize = 2 * total + 1;                                  // :196
        uint256[] memory table = new uint256[](tableSize);                  // :197
        for (uint256 i = 0; i < routingLength; ++i) {                       // :198
            bytes4[] memory selectors = _routing[i];
            uint256 selectorsLength = selectors.length;
            for (uint256 j = 0; j < selectorsLength; ++j) {                 // :201
                uint256 entry = uint256(uint32(selectors[j])) + 1;          // :202
                uint256 slot = entry % tableSize;                           // :203
                while (table[slot] != 0) {                                  // :204
                    if (table[slot] == entry) {
                        revert RegistryDuplicateSelector(selectors[j]);     // :205-207
                    }
                    slot = (slot + 1) % tableSize;                          // :208
                }
                table[slot] = entry;                                        // :210
            }
        }
    }

The NatSpec (:186-189) says the table is an open-addressing set, that a slot holds
`selector + 1` so zero marks it empty, and that a probe always ends at an empty slot because
the table is never more than half full.

## Modelling choices

* **Selectors are `Selector` (`ℕ`)**, and `uint256(uint32(s)) + 1` is `s + 1`. The conversion
  from `bytes4` is injective and the sum is at most `2^32`, so nothing wraps (`SOL-ARITH`,
  `SOL-ABI`).
* **The table is a function `ℕ → ℕ`**, zero everywhere at first (`new uint256[]` zero-fills
  memory). Only slots below `tableSize` are ever read or written.
* **`2 * total + 1` does not overflow** for any array that fits in memory.
* **The `while` loop gets `tableSize` iterations.** By then it has visited every slot. A loop
  that would go on revisits them forever and runs out of gas, so the model reverts there. The
  results show this never happens.
* **A revert is `none`.** The check is `pure`, so it has no other effect.
-/

namespace Contracts.ChainTypeManager

/-- The check's table: each slot holds `selector + 1`, or `0` if it is empty. -/
abbrev ProbeTable := ℕ → ℕ

/-- The `while` loop (:204-209) for `entry`, starting at `slot`, with `fuel` iterations left.
`none` is a revert: the entry is already stored (`RegistryDuplicateSelector`), or the loop has
run out. `some j` is the empty slot where the loop stops. -/
def probeSlot (T : ProbeTable) (n entry : ℕ) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | slot, fuel + 1 =>
    if T slot = 0 then some slot
    else if T slot = entry then none
    else probeSlot T n entry ((slot + 1) % n) fuel

/-- One iteration of the inner loop (:202-210): probe from `entry % tableSize` with
`tableSize` iterations, then store the entry in the empty slot found. -/
def insertSelector (n : ℕ) (T : ProbeTable) (x : Selector) : Option ProbeTable :=
  (probeSlot T n (x + 1) ((x + 1) % n) n).map (fun j => upd T j (x + 1))

/-- The inner loop over one facet's selectors (:201-211). -/
def insertSelectors (n : ℕ) : ProbeTable → List Selector → Option ProbeTable
  | T, [] => some T
  | T, x :: xs => (insertSelector n T x).bind (fun T' => insertSelectors n T' xs)

/-- The outer loop over the release's facets (:198-212). -/
def insertRouting (n : ℕ) : ProbeTable → List (List Selector) → Option ProbeTable
  | T, [] => some T
  | T, sels :: rest => (insertSelectors n T sels).bind (fun T' => insertRouting n T' rest)

/-- `total` (:192-195): the number of selectors across all facets. -/
def selectorTotal (routing : List (List Selector)) : ℕ := (routing.map List.length).sum

/-- `_requireNoDuplicateSelectors(routing)` returns (`true`) rather than reverting (`false`). -/
def noDuplicateSelectors (routing : List (List Selector)) : Bool :=
  (insertRouting (2 * selectorTotal routing + 1) (fun _ => 0) routing).isSome

end Contracts.ChainTypeManager
