import EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting

/-!
# Model: a chain diamond's own storage and `Diamond.diamondCut`

Source: `state-transition/libraries/Diamond.sol` on branch `feat/upgrade-simplification` at
`e561b9cc2`, as for the rest of this folder (the branch moves; every `file:line` below is at
that commit). Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.DiamondStorage` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.DiamondStorage`.

## Why this is modelled

`ChainRouting` models a chain's routing as one map, `selectorToFacet`, and models the guard
`LiveRoutingReader.requireReleaseRouting` by its documented meaning. The guard does not read
that map alone: it **counts** the facet list and each facet's selector list
(`upgrades/registry/libraries/LiveRoutingReader.sol:38-59`). Whether counting is enough depends
on the three storage structures agreeing with each other, which only `Diamond.sol` maintains.
This file transcribes that storage and every function that writes it; `LiveRouting` uses it.

## The storage (`Diamond.sol:42-67`)

    struct SelectorToFacet { address facetAddress; uint16 selectorPosition; bool isFreezable; }
    struct FacetToSelectors { bytes4[] selectors; uint16 facetPosition; }
    struct DiamondStorage {
        mapping(bytes4 selector => SelectorToFacet selectorInfo) selectorToFacet;
        mapping(address facetAddress => FacetToSelectors facetInfo) facetToSelectors;
        address[] facets;
        bool isFrozen;
    }

The proxy's fallback routes a call by `selectorToFacet[msg.sig]` alone and refuses a zero
`facetAddress` (`state-transition/chain-deps/DiamondProxy.sol:32-35`): that is
`DiamondStorage.routing`, the `Routing` of `ChainRouting`.

## Modelling choices

* **Storage arrays are lists.** `push` appends, `pop` drops the last element,
  `a[i] = v` is `List.set`. An out-of-bounds write and the underflow of `length - 1` revert
  in Solidity (`Panic`); both are modelled as reverts. Reads in the source are always in
  bounds (the last index of a nonempty list).
* **Positions are `ℕ`.** The source stores them as `uint16` through `SafeCast.toUint16`,
  which reverts above `2^16 - 1`: a check that only rejects, so it is omitted.
* **The code-existence check** `_facet.code.length == 0` (`Diamond.sol:147-149`, :174-176) is
  modelled by its consequence for address zero, which has no code: adding or replacing with
  facet `0` reverts. For a nonzero codeless address the check only rejects, so it is omitted.
  (Address zero routes nothing: a zero `facetAddress` *means* unrouted.)
* **`isFrozen` is omitted**: no cut writes it, and routing does not read it.
* **The init call is not modelled here.** `diamondCut` below is the facet-cut loop
  (`Diamond.sol:114-133`) with `initAddress == address(0)` and empty calldata, which is what
  every diamond cut this folder models has once the engine runs (`DiamondInit.sol:84-86`,
  `BaseZkSyncUpgrade.sol:118-123`): `_initializeDiamondCut(0, "")` does nothing
  (`Diamond.sol:311-315`). An init that `delegatecall`s arbitrary code could write diamond
  storage directly; that is outside this file (see `LiveRouting`'s break-glass step).
-/

namespace Contracts.ChainTypeManager

/-! ## Storage -/

/-- `Diamond.SelectorToFacet` (`Diamond.sol:42-46`). A zero `facetAddress` means the
selector is not routed. -/
structure SelectorToFacet where
  /-- The facet the selector routes to; zero if none. -/
  facetAddress : Address
  /-- The selector's index in its facet's `selectors` list. -/
  selectorPosition : ℕ
  /-- Whether the selector can be frozen. -/
  isFreezable : Bool

/-- An untouched `selectorToFacet` slot, and what `delete` leaves (`Diamond.sol:279`). -/
def SelectorToFacet.zero : SelectorToFacet := ⟨0, 0, false⟩

/-- `Diamond.FacetToSelectors` (`Diamond.sol:51-54`). -/
structure FacetToSelectors where
  /-- `selectors`: every selector routed to the facet. -/
  selectors : List Selector
  /-- The facet's index in `facets`. -/
  facetPosition : ℕ

/-- `Diamond.DiamondStorage` (`Diamond.sol:62-67`), without `isFrozen`. -/
structure DiamondStorage where
  /-- `selectorToFacet`. -/
  selectorToFacet : Selector → SelectorToFacet
  /-- `facetToSelectors`. -/
  facetToSelectors : Address → FacetToSelectors
  /-- `facets`. -/
  facets : List Address

/-- A newly deployed diamond proxy's storage: every slot zero. -/
def DiamondStorage.fresh : DiamondStorage :=
  ⟨fun _ => SelectorToFacet.zero, fun _ => ⟨[], 0⟩, []⟩

/-- What the proxy's fallback routes (`DiamondProxy.sol:32-35`): `selectorToFacet[x]`, unless
its `facetAddress` is zero. -/
def DiamondStorage.routing (ds : DiamondStorage) : Routing := fun x =>
  if (ds.selectorToFacet x).facetAddress = 0 then none
  else some ((ds.selectorToFacet x).facetAddress, (ds.selectorToFacet x).isFreezable)

/-! ## The private helpers -/

/-- `_saveFacetIfNew` (`Diamond.sol:219-228`):

    uint256 selectorsLength = ds.facetToSelectors[_facet].selectors.length;
    if (selectorsLength == 0) {
        ds.facetToSelectors[_facet].facetPosition = ds.facets.length.toUint16();
        ds.facets.push(_facet);
    } -/
def saveFacetIfNew (ds : DiamondStorage) (f : Address) : DiamondStorage :=
  if (ds.facetToSelectors f).selectors.length = 0 then
    { ds with
      facetToSelectors := upd ds.facetToSelectors f
        { ds.facetToSelectors f with facetPosition := ds.facets.length },
      facets := ds.facets ++ [f] }
  else ds

/-- `_addOneFunction` (`Diamond.sol:235-256`):

    uint16 selectorPosition = (ds.facetToSelectors[_facet].selectors.length).toUint16();
    if (selectorPosition != 0) {
        bytes4 selector0 = ds.facetToSelectors[_facet].selectors[0];
        if (_isSelectorFreezable != ds.selectorToFacet[selector0].isFreezable) {
            revert SelectorsMustAllHaveSameFreezability();
        }
    }
    ds.selectorToFacet[_selector] = SelectorToFacet({facetAddress: _facet,
        selectorPosition: selectorPosition, isFreezable: _isSelectorFreezable});
    ds.facetToSelectors[_facet].selectors.push(_selector); -/
def addOneFunction (ds : DiamondStorage) (f : Address) (x : Selector) (b : Bool) :
    Option DiamondStorage :=
  let sels := (ds.facetToSelectors f).selectors
  if sels.length ≠ 0 ∧ b ≠ (ds.selectorToFacet (sels.getD 0 0)).isFreezable then none
  else some
    { ds with
      selectorToFacet := upd ds.selectorToFacet x ⟨f, sels.length, b⟩,
      facetToSelectors := upd ds.facetToSelectors f
        { ds.facetToSelectors f with selectors := sels ++ [x] } }

/-- `_removeFacet` (`Diamond.sol:289-306`):

    uint256 facetPosition = ds.facetToSelectors[_facet].facetPosition;
    uint256 lastFacetPosition = ds.facets.length - 1;
    if (facetPosition != lastFacetPosition) {
        address lastFacet = ds.facets[lastFacetPosition];
        ds.facets[facetPosition] = lastFacet;
        ds.facetToSelectors[lastFacet].facetPosition = facetPosition.toUint16();
    }
    ds.facets.pop();

The subtraction reverts on an empty list, and the write reverts out of bounds. -/
def removeFacet (ds : DiamondStorage) (f : Address) : Option DiamondStorage :=
  let p := (ds.facetToSelectors f).facetPosition
  if ds.facets.length = 0 then none
  else
    let last := ds.facets.length - 1
    let moved : Option DiamondStorage :=
      if p = last then some ds
      else if p < ds.facets.length then
        let g := ds.facets.getD last 0
        some { ds with
          facets := ds.facets.set p g,
          facetToSelectors := upd ds.facetToSelectors g
            { ds.facetToSelectors g with facetPosition := p } }
      else none
    moved.map fun d => { d with facets := d.facets.dropLast }

/-- `_removeOneFunction` (`Diamond.sol:260-285`):

    uint256 selectorPosition = ds.selectorToFacet[_selector].selectorPosition;
    uint256 lastSelectorPosition = ds.facetToSelectors[_facet].selectors.length - 1;
    if (selectorPosition != lastSelectorPosition) {
        bytes4 lastSelector = ds.facetToSelectors[_facet].selectors[lastSelectorPosition];
        ds.facetToSelectors[_facet].selectors[selectorPosition] = lastSelector;
        ds.selectorToFacet[lastSelector].selectorPosition = selectorPosition.toUint16();
    }
    ds.facetToSelectors[_facet].selectors.pop();
    delete ds.selectorToFacet[_selector];
    if (lastSelectorPosition == 0) { _removeFacet(_facet); }

The subtraction reverts on an empty list, and the write reverts out of bounds. -/
def removeOneFunction (ds : DiamondStorage) (f : Address) (x : Selector) :
    Option DiamondStorage :=
  let sels := (ds.facetToSelectors f).selectors
  let p := (ds.selectorToFacet x).selectorPosition
  if sels.length = 0 then none
  else
    let last := sels.length - 1
    let moved : Option DiamondStorage :=
      if p = last then some ds
      else if p < sels.length then
        let y := sels.getD last 0
        some { ds with
          facetToSelectors := upd ds.facetToSelectors f
            { ds.facetToSelectors f with selectors := sels.set p y },
          selectorToFacet := upd ds.selectorToFacet y
            { ds.selectorToFacet y with selectorPosition := p } }
      else none
    moved.bind fun d =>
      let d' : DiamondStorage :=
        { d with
          facetToSelectors := upd d.facetToSelectors f
            { d.facetToSelectors f with selectors := (d.facetToSelectors f).selectors.dropLast },
          selectorToFacet := upd d.selectorToFacet x SelectorToFacet.zero }
      if last = 0 then removeFacet d' f else some d'

/-! ## The three actions -/

/-- The loop of `_addFunctions` (`Diamond.sol:155-163`):

    SelectorToFacet memory oldFacet = ds.selectorToFacet[selector];
    if (oldFacet.facetAddress != address(0)) { revert FacetExists(selector, oldFacet.facetAddress); }
    _addOneFunction(_facet, selector, _isFacetFreezable); -/
def addLoop : DiamondStorage → Address → List Selector → Bool → Option DiamondStorage
  | ds, _, [], _ => some ds
  | ds, f, x :: xs, b =>
      if (ds.selectorToFacet x).facetAddress ≠ 0 then none
      else (addOneFunction ds f x b).bind fun d => addLoop d f xs b

/-- `_addFunctions` (`Diamond.sol:141-164`): the code check (for address zero), then
`_saveFacetIfNew(_facet)` once, then the loop. -/
def addFunctions (ds : DiamondStorage) (f : Address) (xs : List Selector) (b : Bool) :
    Option DiamondStorage :=
  if f = 0 then none else addLoop (saveFacetIfNew ds f) f xs b

/-- The loop of `_removeFunctions` (`Diamond.sol:205-214`):

    SelectorToFacet memory oldFacet = ds.selectorToFacet[selector];
    if (oldFacet.facetAddress == address(0)) { revert RemoveFunctionFacetAddressZero(); }
    _removeOneFunction(oldFacet.facetAddress, selector); -/
def removeLoop : DiamondStorage → List Selector → Option DiamondStorage
  | ds, [] => some ds
  | ds, x :: xs =>
      if (ds.selectorToFacet x).facetAddress = 0 then none
      else (removeOneFunction ds (ds.selectorToFacet x).facetAddress x).bind fun d =>
        removeLoop d xs

/-- `_removeFunctions` (`Diamond.sol:196-215`): the cut's facet must be zero (:200-202),
then the loop. -/
def removeFunctions (ds : DiamondStorage) (f : Address) (xs : List Selector) :
    Option DiamondStorage :=
  if f ≠ 0 then none else removeLoop ds xs

/-- The loop of `_replaceFunctions` (`Diamond.sol:179-191`):

    SelectorToFacet memory oldFacet = ds.selectorToFacet[selector];
    if (oldFacet.facetAddress == address(0)) { revert ReplaceFunctionFacetAddressZero(); }
    _removeOneFunction(oldFacet.facetAddress, selector);
    _saveFacetIfNew(_facet);
    _addOneFunction(_facet, selector, _isFacetFreezable); -/
def replaceLoop : DiamondStorage → Address → List Selector → Bool → Option DiamondStorage
  | ds, _, [], _ => some ds
  | ds, f, x :: xs, b =>
      if (ds.selectorToFacet x).facetAddress = 0 then none
      else (removeOneFunction ds (ds.selectorToFacet x).facetAddress x).bind fun d =>
        (addOneFunction (saveFacetIfNew d f) f x b).bind fun d' => replaceLoop d' f xs b

/-- `_replaceFunctions` (`Diamond.sol:168-192`): the code check (for address zero), then the
loop. -/
def replaceFunctions (ds : DiamondStorage) (f : Address) (xs : List Selector) (b : Bool) :
    Option DiamondStorage :=
  if f = 0 then none else replaceLoop ds f xs b

/-! ## `diamondCut` -/

/-- `Diamond.Action` (`Diamond.sol:93-97`). -/
inductive CutAction
  | add
  | replace
  | remove
deriving DecidableEq

/-- `Diamond.FacetCut` (`Diamond.sol:75-80`). -/
structure FacetCut where
  /-- The facet the cut adds or replaces with; zero for a removal. -/
  facet : Address
  /-- `Add`, `Replace` or `Remove`. -/
  action : CutAction
  /-- Freezability of the added selectors. -/
  isFreezable : Bool
  /-- The selectors. -/
  selectors : List Selector

/-- One iteration of `Diamond.diamondCut`'s loop (`Diamond.sol:115-132`):

    if (selectors.length == 0) { revert NoFunctionsForDiamondCut(); }
    if (action == Action.Add) { _addFunctions(facet, selectors, isFacetFreezable); }
    else if (action == Action.Replace) { _replaceFunctions(facet, selectors, isFacetFreezable); }
    else if (action == Action.Remove) { _removeFunctions(facet, selectors); } -/
def facetCut (ds : DiamondStorage) (c : FacetCut) : Option DiamondStorage :=
  if c.selectors = [] then none
  else match c.action with
    | .add => addFunctions ds c.facet c.selectors c.isFreezable
    | .replace => replaceFunctions ds c.facet c.selectors c.isFreezable
    | .remove => removeFunctions ds c.facet c.selectors

/-- `Diamond.diamondCut` with `initAddress == address(0)` and empty calldata
(`Diamond.sol:109-137`): the facet cuts in order; any revert reverts the whole cut. -/
def diamondCut : DiamondStorage → List FacetCut → Option DiamondStorage
  | ds, [] => some ds
  | ds, c :: cs => (facetCut ds c).bind fun d => diamondCut d cs

/-! ## The storage invariant

`Diamond.sol` keeps three structures that describe the same routing, plus two position
fields that make removal constant-time ("swap with the last element, then pop"). The
invariant says they agree, position by position. Its plain consequences — no facet listed
twice, a facet is listed exactly when it has selectors, and `selectorToFacet[x]` names `f`
exactly when `x` is in `facetToSelectors[f].selectors` — are
`Properties.DiamondOkMeans`. -/

/-- **The diamond storage invariant.** -/
structure DiamondOk (ds : DiamondStorage) : Prop where
  /-- Every entry of a facet's selector list routes to that facet, recording its position. -/
  selsBack : ∀ f i x, (ds.facetToSelectors f).selectors[i]? = some x →
    (ds.selectorToFacet x).facetAddress = f ∧ (ds.selectorToFacet x).selectorPosition = i
  /-- Every routed selector sits at its recorded position in its facet's selector list. -/
  selsThere : ∀ x, (ds.selectorToFacet x).facetAddress ≠ 0 →
    (ds.facetToSelectors (ds.selectorToFacet x).facetAddress).selectors[
      (ds.selectorToFacet x).selectorPosition]? = some x
  /-- Every entry of the facet list has selectors and records its position. -/
  facetsBack : ∀ i f, ds.facets[i]? = some f →
    (ds.facetToSelectors f).facetPosition = i ∧ (ds.facetToSelectors f).selectors ≠ []
  /-- Every facet with selectors sits at its recorded position in the facet list. -/
  facetsThere : ∀ f, (ds.facetToSelectors f).selectors ≠ [] →
    ds.facets[(ds.facetToSelectors f).facetPosition]? = some f
  /-- Address zero has no selectors: a selector listed under it would look unrouted. -/
  zeroNoSels : (ds.facetToSelectors 0).selectors = []

/-! ## Witness data -/

/-- Two facets added to a fresh diamond: `13` with selector `2`, then `11` with selectors
`1`, `3`, `4`. The facet list is `[13, 11]`. -/
def wTwoFacetCuts : List FacetCut := [⟨13, .add, false, [2]⟩, ⟨11, .add, false, [1, 3, 4]⟩]

/-- Then: remove selector `2` (facet `13` loses its only selector and leaves the facet list,
so `11` is moved into its slot), remove selector `1` (the first of `11`'s three, so `4` is
moved into its slot), and replace selector `3` by facet `12` (the last of `11`'s list; `12`
is a new facet). -/
def wRemoveReplaceCuts : List FacetCut :=
  [⟨0, .remove, false, [2]⟩, ⟨0, .remove, false, [1]⟩, ⟨12, .replace, false, [3]⟩]

end Contracts.ChainTypeManager
