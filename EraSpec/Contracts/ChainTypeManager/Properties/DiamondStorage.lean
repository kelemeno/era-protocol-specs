import EraSpec.Contracts.ChainTypeManager.Specs.DiamondStorage

/-!
# Properties: `Diamond.diamondCut` keeps a diamond's storage consistent

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.DiamondStorage`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.DiamondStorage`.

## What holds

* **The invariant.** A fresh diamond satisfies `DiamondOk` (`FreshStorageOk`), and what it
  says in plain terms is `DiamondOkMeans`: no facet is listed twice, a facet is listed
  exactly when it has selectors, no facet lists a selector twice, address zero is never
  listed, and the proxy routes `x` to `f` exactly when `x` is in `f`'s selector list.
* **Every cut keeps it.** Each of `Add`, `Remove` and `Replace` (`AddFunctionsPreservesOk`,
  `RemoveFunctionsPreservesOk`, `ReplaceFunctionsPreservesOk`), and so any `diamondCut` whose
  init writes no diamond storage (`DiamondCutPreservesOk`). This covers the swap-and-pop in
  `_removeOneFunction` (`Diamond.sol:260-285`) and `_removeFacet` (:289-306): the recorded
  positions are what makes them remove the right element.
* **Every cut does what `ChainRouting` says it does.** On the routing the proxy implements,
  `Add` is `ChainRouting.addAll` and `Remove` is `ChainRouting.removeAll`
  (`AddFunctionsRoutes`, `RemoveFunctionsRoutes`); `Replace` reroutes exactly its selectors,
  each of which was routed (`ReplaceFunctionsRoutes`). These need no invariant.
* **The empty-cut check is load-bearing.** Without `NoFunctionsForDiamondCut`
  (`Diamond.sol:120-122`), an `Add` with no selectors would list a facet that routes nothing
  (`EmptyAddBreaksOk`).

`DiamondCutWitness` runs all three actions, through both swap-and-pop branches.
-/

namespace Contracts.ChainTypeManager

/-! ## The invariant -/

/-- **A FRESH DIAMOND'S STORAGE SATISFIES THE INVARIANT.** -/
def Properties.FreshStorageOk : Prop := DiamondOk DiamondStorage.fresh

/-- **WHAT THE INVARIANT SAYS.** On storage satisfying `DiamondOk`: no facet is listed twice;
a facet is listed exactly when it has a selector; no facet lists a selector twice; address
zero is never listed; and `x` is in `facetToSelectors[f].selectors` exactly when the proxy
routes `x` to `f` (with some freezability). -/
def Properties.DiamondOkMeans : Prop :=
  ∀ ds : DiamondStorage, DiamondOk ds →
    ds.facets.Nodup ∧
    (∀ f, f ∈ ds.facets ↔ (ds.facetToSelectors f).selectors ≠ []) ∧
    (∀ f, (ds.facetToSelectors f).selectors.Nodup) ∧
    (0 : Address) ∉ ds.facets ∧
    ∀ f x, x ∈ (ds.facetToSelectors f).selectors ↔ ∃ b, ds.routing x = some (f, b)

/-! ## Every cut keeps it -/

/-- **`_addFunctions` KEEPS THE INVARIANT** for a nonempty selector list (`diamondCut` refuses
an empty one). -/
def Properties.AddFunctionsPreservesOk : Prop :=
  ∀ (ds d : DiamondStorage) (f : Address) (xs : List Selector) (b : Bool), DiamondOk ds →
    xs ≠ [] → addFunctions ds f xs b = some d → DiamondOk d

/-- **`_removeFunctions` KEEPS THE INVARIANT.** -/
def Properties.RemoveFunctionsPreservesOk : Prop :=
  ∀ (ds d : DiamondStorage) (f : Address) (xs : List Selector), DiamondOk ds →
    removeFunctions ds f xs = some d → DiamondOk d

/-- **`_replaceFunctions` KEEPS THE INVARIANT.** -/
def Properties.ReplaceFunctionsPreservesOk : Prop :=
  ∀ (ds d : DiamondStorage) (f : Address) (xs : List Selector) (b : Bool), DiamondOk ds →
    replaceFunctions ds f xs b = some d → DiamondOk d

/-- **`diamondCut` KEEPS THE INVARIANT.** Any list of facet cuts that succeeds on storage
satisfying `DiamondOk` leaves storage satisfying it. -/
def Properties.DiamondCutPreservesOk : Prop :=
  ∀ (ds d : DiamondStorage) (cuts : List FacetCut), DiamondOk ds →
    diamondCut ds cuts = some d → DiamondOk d

/-! ## Every cut does what `ChainRouting` says -/

/-- **AN `Add` CUT IS `ChainRouting.addAll`** on the routing the proxy implements: every
selector must be unrouted, and ends up routed to the cut's facet with its freezability. No
invariant is needed. -/
def Properties.AddFunctionsRoutes : Prop :=
  ∀ (ds d : DiamondStorage) (f : Address) (xs : List Selector) (b : Bool),
    addFunctions ds f xs b = some d →
    addAll ds.routing (xs.map fun x => (x, (f, b))) = some d.routing

/-- **A `Remove` CUT IS `ChainRouting.removeAll`**: every selector must be routed, and ends up
unrouted. No invariant is needed. -/
def Properties.RemoveFunctionsRoutes : Prop :=
  ∀ (ds d : DiamondStorage) (f : Address) (xs : List Selector),
    removeFunctions ds f xs = some d → removeAll ds.routing xs = some d.routing

/-- **A `Replace` CUT REROUTES EXACTLY ITS SELECTORS**, to a nonzero facet, and each of them
was routed before. -/
def Properties.ReplaceFunctionsRoutes : Prop :=
  ∀ (ds d : DiamondStorage) (f : Address) (xs : List Selector) (b : Bool),
    replaceFunctions ds f xs b = some d →
    f ≠ 0 ∧ (∀ y ∈ xs, ds.routing y ≠ none) ∧
      ∀ y, d.routing y = if y ∈ xs then some (f, b) else ds.routing y

/-! ## The empty-cut check -/

/-- **WITHOUT `NoFunctionsForDiamondCut`, AN EMPTY `Add` BREAKS THE INVARIANT.** Called
directly with no selectors, `_addFunctions` lists facet `11` while it routes nothing;
`diamondCut` refuses the same cut. -/
def Properties.EmptyAddBreaksOk : Prop :=
  ∃ d, addFunctions DiamondStorage.fresh 11 [] false = some d ∧ ¬ DiamondOk d ∧
    11 ∈ d.facets ∧ (d.facetToSelectors 11).selectors = [] ∧
    facetCut DiamondStorage.fresh ⟨11, .add, false, []⟩ = none

/-! ## Witness -/

/-- **THE PRESERVATION RESULTS ARE NOT VACUOUS.** From a fresh diamond: add facet `13` with
selector `2` and facet `11` with `1`, `3`, `4`; then remove `2` (facet `13` leaves and `11`
takes its slot), remove `1` (selector `4` takes its slot) and replace `3` by the new facet
`12`. Every cut succeeds, both storages satisfy the invariant, and the final diamond lists
`[11, 12]`, routes `4` to `11` and `3` to `12`, and routes neither `1` nor `2`. -/
def Properties.DiamondCutWitness : Prop :=
  ∃ d₁ d₂, diamondCut DiamondStorage.fresh wTwoFacetCuts = some d₁ ∧
    diamondCut d₁ wRemoveReplaceCuts = some d₂ ∧ DiamondOk d₁ ∧ DiamondOk d₂ ∧
    d₁.facets = [13, 11] ∧ d₂.facets = [11, 12] ∧ (d₂.facetToSelectors 11).selectors = [4] ∧
    d₂.routing 4 = some (11, false) ∧ d₂.routing 3 = some (12, false) ∧
    d₂.routing 1 = none ∧ d₂.routing 2 = none

end Contracts.ChainTypeManager
