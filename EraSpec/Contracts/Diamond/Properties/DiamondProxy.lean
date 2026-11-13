import EraSpec.Contracts.Diamond.Specs.DiamondProxy

/-!
# Properties: the diamond proxy's routing, freezing and init call

Statements about `EraSpec.Contracts.Diamond.Specs.DiamondProxy`. Proofs are in
`EraSpec.Contracts.Diamond.Proofs.DiamondProxy`. The storage-level results of
`Contracts.ChainTypeManager.Properties.DiamondStorage` (`DiamondCutPreservesOk`,
`AddFunctionsRoutes`, …) are not restated; they are used.

## What holds

* **Run-level invariant.** Every state any deployment reaches, through any interleaving of
  cuts (with any init the model admits), freezes, unfreezes and other calls, keeps the
  storage consistent (`DiamondOk`) and gives each facet one freezability
  (`ReachableInvariant`). So in every reachable state the getters `isFacetFreezable` and
  `isFunctionFreezable` report exactly what the proxy enforces while frozen
  (`ReachableGettersMatchDispatch`).
* **Dispatch.** The proxy delegatecalls `f` exactly when the calldata has a full selector (or
  none), the selector is routed to `f`, and the diamond is unfrozen or the route is not
  freezable (`DispatchExact`). Freezing blocks exactly the freezable routes and changes
  nothing else (`FreezeBlocksExactlyFreezable`).
* **Who freezes.** Only a call by `s.chainTypeManager` flips `isFrozen`, and that call
  changes nothing else (`OnlyCtmTogglesFreeze`); a run with no such call keeps the flag
  (`RunsWithoutCtmKeepFreeze`). The chain admin cannot freeze or unfreeze
  (`ChainAdminCannotFreeze`), although the getters' NatSpec says freezable selectors "can be
  frozen by the admin". A constructed proxy is unfrozen and on its chain
  (`ConstructedProxyIsUnfrozen`).
* **Cut guards.** A successful facet cut has selectors; `Add` names a nonzero facet and new,
  distinct selectors; `Replace` names a nonzero facet and routed selectors; `Remove` names
  facet zero and routed, distinct selectors; and each reroutes exactly its selectors
  (`FacetCutGuards`). On consistent storage, `Add` succeeds exactly when these guards and the
  freezability check pass (`AddEnabledIff`). Cuts keep each facet's freezability uniform
  (`DiamondCutKeepsFreezeUniform`).
* **Init.** A successful `diamondCut` with an init returned exactly the 32 bytes of
  `DIAMOND_INIT_SUCCESS_RETURN_VALUE`, and a cut without one had empty calldata; `isFrozen` is
  unchanged (`InitReturnChecked`).

## What the checks are for (countermodels)

* Without the freezability check in `_addOneFunction`, a facet gets mixed freezability and
  `isFacetFreezable` reports "not freezable" for a facet a frozen proxy partly blocks
  (`FreezabilityCheckLoadBearing`).
* Without `FacetExists`, `Add` silently reroutes a routed selector and the loupe keeps listing
  it under the old facet (`FacetExistsCheckLoadBearing`).
* Without the return-data checks, a delegatecall to an address with no code is accepted as an
  init (`ReturnDataCheckLoadBearing`), as the comment at `Diamond.sol:317` relies on.
* If the cut and `unfreezeDiamond` entry points are routed freezable, a frozen diamond stays
  frozen and unchangeable forever (`FreezableEntrypointsMakeFreezePermanent`,
  `FreezePermanentWitness`). Nothing in `Diamond.sol` or `CTMRelease` prevents a release from
  marking the Admin facet freezable; that is a configuration obligation.

## Not a check

* `Replace` does not require the new facet to differ from the old one (unlike the EIP-2535
  reference implementation): replacing a selector by its own facet succeeds, and for a facet
  with one selector it can flip that selector's freezability
  (`ReplaceWithSameFacetAccepted`).

`ProxyRunWitness` runs construction, freeze, a cut while frozen, and unfreeze.
-/

namespace Contracts.Diamond

open Clear
open Contracts.ChainTypeManager

/-! ## The run-level invariant -/

/-- **EVERY REACHABLE STATE IS CONSISTENT AND FREEZE-UNIFORM.** For any facet behaviour `E`,
every state reached by a successful constructor followed by any run satisfies `DiamondOk` (the
three routing structures agree position by position) and `FreezeUniform` (all selectors of a
facet share one `isFreezable`). -/
def Properties.ReachableInvariant : Prop :=
  ∀ (E : Env) (s : ProxyState), Reach E s → DiamondOk s.ds ∧ FreezeUniform s.ds

/-- **IN EVERY REACHABLE STATE THE FREEZABILITY GETTERS ARE ACCURATE.** If a reachable state
routes `x` to `f` with freezability `b`, then `isFacetFreezable(f)` and
`isFunctionFreezable(x)` both return `b`, `f` is in `facets`, `x` is in `f`'s selector list, and
a call on `x` (with well-formed calldata) reaches `f` exactly when the diamond is unfrozen or
`isFacetFreezable(f)` is false. -/
def Properties.ReachableGettersMatchDispatch : Prop :=
  ∀ (E : Env) (s : ProxyState), Reach E s →
    ∀ (x : Selector) (f : Address) (b : Bool), s.ds.routing x = some (f, b) →
      isFacetFreezable s.ds f = b ∧ isFunctionFreezable s.ds x = b ∧ f ∈ s.ds.facets ∧
      x ∈ (s.ds.facetToSelectors f).selectors ∧
      ∀ cd : Calldata, cd.sig = x → (4 ≤ cd.len ∨ cd.len = 0) →
        (fallbackTarget s cd = some f ↔
          (s.isFrozen = false ∨ isFacetFreezable s.ds f = false))

/-! ## Dispatch and freezing -/

/-- **THE PROXY ROUTES EXACTLY BY THE MAP.** In any state, the fallback delegatecalls `f`
iff the calldata length is 0 or at least 4, `selectorToFacet[msg.sig]` routes to `f` with some
freezability `b`, and the diamond is unfrozen or `b` is false. -/
def Properties.DispatchExact : Prop :=
  ∀ (s : ProxyState) (cd : Calldata) (f : Address),
    fallbackTarget s cd = some f ↔
      (4 ≤ cd.len ∨ cd.len = 0) ∧
        ∃ b, s.ds.routing cd.sig = some (f, b) ∧ (s.isFrozen = false ∨ b = false)

/-- **FREEZING BLOCKS EXACTLY THE FREEZABLE ROUTES.** On the same routing, a frozen and an
unfrozen proxy dispatch identically except on a selector routed freezable, which the frozen
proxy refuses and the unfrozen one (given well-formed calldata) sends to its facet. -/
def Properties.FreezeBlocksExactlyFreezable : Prop :=
  ∀ (ds : DiamondStorage) (cd : Calldata),
    ((∀ f, ds.routing cd.sig ≠ some (f, true)) →
      fallbackTarget ⟨ds, true⟩ cd = fallbackTarget ⟨ds, false⟩ cd) ∧
    (∀ f, ds.routing cd.sig = some (f, true) →
      fallbackTarget ⟨ds, true⟩ cd = none ∧
      ((4 ≤ cd.len ∨ cd.len = 0) → fallbackTarget ⟨ds, false⟩ cd = some f))

/-- **ONLY THE CTM FLIPS `isFrozen`, AND THAT CALL CHANGES NOTHING ELSE.** Any step that
changes `isFrozen` was made by `E.ctm` (`s.chainTypeManager`) and leaves the routing storage
unchanged. In particular no cut changes `isFrozen` (in the model's init class), and the chain
admin, if not the CTM, cannot freeze or unfreeze. -/
def Properties.OnlyCtmTogglesFreeze : Prop :=
  ∀ (E : Env) (c : Address) (s s' : ProxyState), Step E c s s' →
    s'.isFrozen ≠ s.isFrozen → c = E.ctm ∧ s'.ds = s.ds

/-- **THE CHAIN ADMIN CANNOT FREEZE OR UNFREEZE.** Any caller other than `s.chainTypeManager`
(in particular the chain admin, when it is not the CTM) makes no step that changes `isFrozen`.
The NatSpec of `IGetters.isFunctionFreezable` / `isFacetFreezable` (`IGetters.sol:188-192`)
says a freezable selector "can be frozen by the admin"; freezing is `onlyChainTypeManager`
(`Admin.sol:616`), reached through `ChainTypeManager.freezeChain` (owner or bridgehub owner,
`ChainTypeManager.sol:574-578`). -/
def Properties.ChainAdminCannotFreeze : Prop :=
  ∀ (E : Env) (a : Address), a ≠ E.ctm → ∀ (s s' : ProxyState), Step E a s s' →
    s'.isFrozen = s.isFrozen

/-- **A CONSTRUCTED PROXY IS UNFROZEN, ON ITS CHAIN.** The constructor succeeds only when the
given chain id is `block.chainid` (`DiamondProxy.sol:19`), and its result is not frozen. -/
def Properties.ConstructedProxyIsUnfrozen : Prop :=
  ∀ (chainId blockChainId : ℕ) (cut : CutData) (r : InitRun) (s : ProxyState),
    construct chainId blockChainId cut r = some s → chainId = blockChainId ∧ s.isFrozen = false

/-- **A RUN WITH NO CTM CALL KEEPS THE FREEZE FLAG.** -/
def Properties.RunsWithoutCtmKeepFreeze : Prop :=
  ∀ (E : Env) (cs : List Address) (s s' : ProxyState), Run E cs s s' → E.ctm ∉ cs →
    s'.isFrozen = s.isFrozen

/-- **FREEZABLE CUT AND UNFREEZE ENTRY POINTS MAKE A FREEZE PERMANENT.** If a frozen state
routes every selector whose facet function is a cut entry point or `unfreezeDiamond` as
freezable, then every run from it, by any callers, ends in that same state: nothing can
unfreeze or change it. -/
def Properties.FreezableEntrypointsMakeFreezePermanent : Prop :=
  ∀ (E : Env) (cs : List Address) (s s' : ProxyState), s.isFrozen = true →
    (∀ (x : Selector) (f : Address) (b : Bool), s.ds.routing x = some (f, b) →
      (E.fn f x = .executeCut ∨ E.fn f x = .unfreeze) → b = true) →
    Run E cs s s' → s' = s

/-- **THE PERMANENT FREEZE IS REACHABLE.** A deployment whose init installs the Admin-like
facet as freezable (`wInit true`) is frozen by the CTM, after which every run, by any callers,
stays in that state. -/
def Properties.FreezePermanentWitness : Prop :=
  ∃ s₀ s₁ : ProxyState, construct 1 1 wCtorCut (wInit true) = some s₀ ∧
    Step wEnv 99 s₀ s₁ ∧ s₁.isFrozen = true ∧ Reach wEnv s₁ ∧
    ∀ (cs : List Address) (s' : ProxyState), Run wEnv cs s₁ s' → s' = s₁

/-! ## The cut -/

/-- **THE GUARDS OF A FACET CUT.** A successful facet cut has a nonempty selector list
(`NoFunctionsForDiamondCut`) and:

* `Add`: a nonzero facet (`AddressHasNoCode` for address zero), pairwise distinct selectors
  none of which was routed (`FacetExists`), and afterwards exactly those selectors route to the
  facet with the cut's freezability;
* `Replace`: a nonzero facet, every selector routed before (`ReplaceFunctionFacetAddressZero`),
  and afterwards exactly those selectors route to the facet with the cut's freezability;
* `Remove`: facet zero (`RemoveFunctionFacetAddressNotZero`), pairwise distinct selectors each
  routed before (`RemoveFunctionFacetAddressZero`), and afterwards exactly those are
  unrouted. -/
def Properties.FacetCutGuards : Prop :=
  ∀ (ds d : DiamondStorage) (c : FacetCut), facetCut ds c = some d →
    c.selectors ≠ [] ∧
    (c.action = .add → c.facet ≠ 0 ∧ c.selectors.Nodup ∧
      (∀ x ∈ c.selectors, ds.routing x = none) ∧
      ∀ y, d.routing y = if y ∈ c.selectors then some (c.facet, c.isFreezable)
        else ds.routing y) ∧
    (c.action = .replace → c.facet ≠ 0 ∧ (∀ x ∈ c.selectors, ds.routing x ≠ none) ∧
      ∀ y, d.routing y = if y ∈ c.selectors then some (c.facet, c.isFreezable)
        else ds.routing y) ∧
    (c.action = .remove → c.facet = 0 ∧ c.selectors.Nodup ∧
      (∀ x ∈ c.selectors, ds.routing x ≠ none) ∧
      ∀ y, d.routing y = if y ∈ c.selectors then none else ds.routing y)

/-- **`Add` IS ENABLED EXACTLY UNDER ITS GUARDS.** On consistent, freeze-uniform storage, an
`Add` cut succeeds iff its selector list is nonempty, its facet is nonzero, its selectors are
pairwise distinct and unrouted, and every selector already routed to the facet has the cut's
freezability (the check of `_addOneFunction`, `Diamond.sol:243-248`). -/
def Properties.AddEnabledIff : Prop :=
  ∀ (ds : DiamondStorage) (f : Address) (b : Bool) (xs : List Selector),
    DiamondOk ds → FreezeUniform ds →
    ((∃ d, facetCut ds ⟨f, .add, b, xs⟩ = some d) ↔
      xs ≠ [] ∧ f ≠ 0 ∧ xs.Nodup ∧ (∀ x ∈ xs, ds.routing x = none) ∧
        ∀ (y : Selector) (c : Bool), ds.routing y = some (f, c) → c = b)

/-- **CUTS KEEP EACH FACET'S FREEZABILITY UNIFORM.** On consistent storage, a successful
facet-cut list leaves every facet with one freezability. -/
def Properties.DiamondCutKeepsFreezeUniform : Prop :=
  ∀ (ds d : DiamondStorage) (cuts : List FacetCut), DiamondOk ds → FreezeUniform ds →
    diamondCut ds cuts = some d → FreezeUniform d

/-- **`Replace` DOES NOT REQUIRE A DIFFERENT FACET.** Replacing selector `1` of facet `11` by
facet `11` itself succeeds and flips its freezability (`11` has no other selector), and doing
it again succeeds and changes no route. -/
def Properties.ReplaceWithSameFacetAccepted : Prop :=
  ∃ d₀ d₁ d₂ : DiamondStorage, facetCut DiamondStorage.fresh ⟨11, .add, false, [1]⟩ = some d₀ ∧
    facetCut d₀ ⟨11, .replace, true, [1]⟩ = some d₁ ∧
    d₀.routing 1 = some (11, false) ∧ d₁.routing 1 = some (11, true) ∧
    facetCut d₁ ⟨11, .replace, true, [1]⟩ = some d₂ ∧ d₂.routing = d₁.routing ∧ DiamondOk d₂

/-! ## The init call -/

/-- **A SUCCESSFUL `diamondCut` CHECKED ITS INIT.** If `diamondCut` (cuts, then init)
succeeds, then `isFrozen` is unchanged and the facet cuts succeeded with some storage `d₁`;
either there was no init (`initAddress == 0`) and the calldata was empty and the result is
`d₁`, or the init's delegatecall succeeded returning exactly the 32 bytes of
`DIAMOND_INIT_SUCCESS_RETURN_VALUE` and the result is what its nested cuts make of `d₁`. -/
def Properties.InitReturnChecked : Prop :=
  ∀ (s s' : ProxyState) (c : CutData) (r : InitRun), diamondCutFull s c r = some s' →
    s'.isFrozen = s.isFrozen ∧
    ∃ d₁, diamondCut s.ds c.facetCuts = some d₁ ∧
      ((c.initAddress = 0 ∧ c.initCalldata = [] ∧ s'.ds = d₁) ∨
       (c.initAddress ≠ 0 ∧ r.outcome = .returned magicBytes ∧
         diamondCut d₁ r.nested = some s'.ds))

/-! ## Countermodels -/

/-- **THE RETURN-DATA CHECKS ARE LOAD-BEARING.** For every state and nonzero init address: a
delegatecall to an address with no code (success, no data) is refused, while the variant
without the checks accepts it; and any other successful 32-byte return is refused. -/
def Properties.ReturnDataCheckLoadBearing : Prop :=
  ∀ (s : ProxyState) (init : Address) (cd : Bytes), init ≠ 0 →
    initializeDiamondCut s init cd codelessInit = none ∧
    initializeNoReturnCheck s init cd codelessInit = some s ∧
    ∀ data : Bytes, data.length = 32 → data ≠ magicBytes →
      initializeDiamondCut s init cd ⟨[], .returned data⟩ = none

/-- **THE FREEZABILITY CHECK IS LOAD-BEARING.** Facet `11` routes `1`, not freezable. Adding
`2` to it as freezable reverts; without the check it succeeds, the facet is no longer
freeze-uniform, `isFacetFreezable(11)` reports `false`, and yet a frozen proxy refuses `2` while
serving `1`. -/
def Properties.FreezabilityCheckLoadBearing : Prop :=
  ∃ d₀ d₁ : DiamondStorage, addFunctions DiamondStorage.fresh 11 [1] false = some d₀ ∧
    addFunctions d₀ 11 [2] true = none ∧
    addFunctionsNoFrzCheck d₀ 11 [2] true = some d₁ ∧
    ¬ FreezeUniform d₁ ∧ isFacetFreezable d₁ 11 = false ∧ d₁.routing 2 = some (11, true) ∧
    fallbackTarget ⟨d₁, true⟩ ⟨4, 2⟩ = none ∧ fallbackTarget ⟨d₁, true⟩ ⟨4, 1⟩ = some 11

/-- **THE `FacetExists` CHECK IS LOAD-BEARING.** Facet `11` routes `1`. Adding `1` to facet
`12` reverts; without the check it succeeds, reroutes `1` to `12`, leaves `1` in `11`'s selector
list, and breaks `DiamondOk`. -/
def Properties.FacetExistsCheckLoadBearing : Prop :=
  ∃ d₀ d₁ : DiamondStorage, addFunctions DiamondStorage.fresh 11 [1] false = some d₀ ∧
    addFunctions d₀ 12 [1] false = none ∧
    addFunctionsNoExistsCheck d₀ 12 [1] false = some d₁ ∧
    d₁.routing 1 = some (12, false) ∧ 1 ∈ (d₁.facetToSelectors 11).selectors ∧ ¬ DiamondOk d₁

/-! ## Witness -/

/-- **THE RESULTS ARE NOT VACUOUS.** Construct a proxy whose init installs the Admin-like facet
`21` (not freezable) and the freezable facet `22`; the CTM freezes it (selector `5` of facet `22`
refused, `unfreezeDiamond` still served); a cut through the non-freezable cut entry point adds facet
`23` while frozen; the CTM unfreezes it. The final state is reachable and serves `5` and `6`. -/
def Properties.ProxyRunWitness : Prop :=
  ∃ s₀ s₁ s₂ s₃ : ProxyState,
    construct 1 1 wCtorCut (wInit false) = some s₀ ∧
    Step wEnv 99 s₀ s₁ ∧ Step wEnv 99 s₁ s₂ ∧ Step wEnv 99 s₂ s₃ ∧
    s₀.isFrozen = false ∧ fallbackTarget s₀ ⟨4, 5⟩ = some 22 ∧
    s₁.isFrozen = true ∧ fallbackTarget s₁ ⟨4, 5⟩ = none ∧ fallbackTarget s₁ ⟨4, 3⟩ = some 21 ∧
    s₂.isFrozen = true ∧ s₂.ds.routing 6 = some (23, true) ∧
    s₃.isFrozen = false ∧ fallbackTarget s₃ ⟨4, 5⟩ = some 22 ∧
    fallbackTarget s₃ ⟨4, 6⟩ = some 23 ∧
    Reach wEnv s₃ ∧ isFacetFreezable s₃.ds 22 = true ∧ isFacetFreezable s₃.ds 21 = false

end Contracts.Diamond
