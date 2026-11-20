import EraSpec.Contracts.Diamond.Specs.DiamondProxy
import EraSpec.Core.Headline

/-!
# Properties: the diamond proxy's routing, freezing and init call

Statements about `EraSpec.Contracts.Diamond.Specs.DiamondProxy` (`draft/v0.35.0` at
`b17415d20`). Proofs are in `EraSpec.Contracts.Diamond.Proofs.DiamondProxy`. The storage-level
results of `Contracts.ChainTypeManager.Properties.DiamondStorage` (`DiamondCutPreservesOk`,
`AddFunctionsRoutes`, …) are not restated; they are used.

## What holds

* **Run-level invariant.** Every state any deployment reaches, through any interleaving of
  cuts (with any init in the model's `InitRun` class), freezes, unfreezes and other calls, keeps
  the storage consistent (`DiamondOk`) and gives each facet one freezability
  (`ReachableInvariant`). So in every reachable state the getters `isFacetFreezable` and
  `isFunctionFreezable` report exactly what the proxy enforces while frozen
  (`ReachableGettersMatchDispatch`), and on that storage, or after further facet cuts, the count
  check of `requireReleaseRouting` against rows that pass `validate()` is exact routing
  (`ReachableCountCheckExact`).
* **Dispatch.** The proxy delegatecalls `f` exactly when the calldata has a full selector (or
  none), the selector is routed to `f`, and the diamond is unfrozen or the route is not
  freezable (`DispatchExact`). Freezing blocks exactly the freezable routes and changes
  nothing else (`FreezeBlocksExactlyFreezable`).
* **Who freezes.** Only a call by `s.chainTypeManager` flips `isFrozen`, and that call
  changes nothing else (`OnlyCtmTogglesFreeze`). Exactly: a call flips the flag iff its caller
  is the CTM and some calldata the proxy dispatches reaches `freezeDiamond` (unfrozen) or
  `unfreezeDiamond` (frozen) (`FreezeToggleExact`); so the CTM can unfreeze exactly when some
  selector routed not freezable reaches `unfreezeDiamond` (`FreezeUnfreezeEnabledIff`). Any
  other caller, the chain admin among them, makes no step that changes the flag
  (`ChainAdminCannotFreeze`), and a run with no call by the CTM keeps it, cuts included
  (`RunsWithoutCtmKeepFreeze`). A constructed proxy is unfrozen and on its chain
  (`ConstructedProxyIsUnfrozen`).
* **Cut guards.** A successful facet cut has selectors; `Add` names a nonzero facet and new,
  distinct selectors; `Replace` names a nonzero facet and routed selectors; `Remove` names
  facet zero and routed, distinct selectors; and each reroutes exactly its selectors
  (`FacetCutGuards`). On consistent, freeze-uniform storage the guards are exact: `Add` succeeds
  exactly under them and the freezability check (`AddEnabledIff`); `Replace` exactly when,
  besides them, every selector already routed to the facet other than the cut's first selector
  has the cut's freezability (`ReplaceEnabledIff`); `Remove` exactly under them
  (`RemoveEnabledIff`; consistency alone suffices). Cuts keep each facet's freezability uniform
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
* If the cut and `unfreezeDiamond` entry points are routed freezable, a frozen diamond admits no
  further change in the model (`FreezableEntrypointsMakeFreezePermanent`), and a deployment
  reaches such a state (`FreezePermanentWitness`). Which facets a release marks freezable is
  release configuration (`OPS-CONFIG`).

## Not a check

* `Replace` does not require the new facet to differ from the old one: replacing a selector by
  its own facet succeeds, and for a facet with one selector it can flip that selector's
  freezability (`ReplaceWithSameFacetAccepted`).

## Witnesses

`ProxyRunWitness` runs construction, a freeze by the CTM, a cut and a getter call by the chain
admin while frozen, and an unfreeze by the CTM. `CutEnablednessWitness` exercises the
freezability, routing and distinctness clauses of the three enabledness results on a reachable
storage, `InitCallWitness` an upgrade-like cut whose init makes a nested cut, and
`ReachableCountCheckWitness` both outcomes of the count check on reachable storage.
-/

namespace Contracts.Diamond

open Clear
open Contracts.ChainTypeManager

/-! ## The run-level invariant -/

/-- **EVERY REACHABLE STATE IS CONSISTENT AND FREEZE-UNIFORM.** For any facet behaviour `E`,
every state reached by a successful constructor followed by any run satisfies `DiamondOk` (the
three routing structures agree position by position) and `FreezeUniform` (all selectors of a
facet share one `isFreezable`). -/
@[headline] def Properties.ReachableInvariant : Prop :=
  ∀ (E : Env) (s : ProxyState), Reach E s → DiamondOk s.ds ∧ FreezeUniform s.ds

/-- **IN EVERY REACHABLE STATE THE FREEZABILITY GETTERS ARE ACCURATE.** If a reachable state
routes `x` to `f` with freezability `b`, then `isFacetFreezable(f)` and
`isFunctionFreezable(x)` both return `b`, `f` is in `facets`, `x` is in `f`'s selector list, and
a call on `x` (with well-formed calldata) reaches `f` exactly when the diamond is unfrozen or
`isFacetFreezable(f)` is false. -/
@[headline] def Properties.ReachableGettersMatchDispatch : Prop :=
  ∀ (E : Env) (s : ProxyState), Reach E s →
    ∀ (x : Selector) (f : Address) (b : Bool), s.ds.routing x = some (f, b) →
      isFacetFreezable s.ds f = b ∧ isFunctionFreezable s.ds x = b ∧ f ∈ s.ds.facets ∧
      x ∈ (s.ds.facetToSelectors f).selectors ∧
      ∀ cd : Calldata, cd.sig = x → (4 ≤ cd.len ∨ cd.len = 0) →
        (fallbackTarget s cd = some f ↔
          (s.isFrozen = false ∨ isFacetFreezable s.ds f = false))

/-- **ON REACHABLE STORAGE THE LIVE-ROUTING COUNT CHECK IS EXACT.** The counting check of
`LiveRoutingReader.requireReleaseRouting`, as `Contracts.ChainTypeManager.LiveRouting` models it
(`CountCheck`), against release rows whose self-descriptions are nonempty and duplicate-free
(`RowsWf`, what `CTMRelease.validate()` checks), passes exactly when the storage routes exactly
the release's flattened rows. The storage is a reachable state's, or what a successful list of
facet cuts makes of it: the storage a cut's delegatecalled init reads, as
`DefaultUpgrade.upgradeFromTransition` does when it runs the check before its own cuts
(`upgrades/DefaultUpgrade.sol:36`). This is `CountCheckIffExactRouting` with its `DiamondOk`
premise discharged by `ReachableInvariant` and `DiamondCutPreservesOk`;
`CorruptStorageFoolsCountCheck` shows the check is not exact on inconsistent storage. -/
@[headline] def Properties.ReachableCountCheckExact : Prop :=
  ∀ (E : Env) (s : ProxyState) (cuts : List FacetCut) (d : DiamondStorage)
    (sel : Address → List Selector) (rows : List FacetRow),
    Reach E s → diamondCut s.ds cuts = some d → RowsWf sel rows →
    (CountCheck sel d rows ↔ d.routing = rowsRouting (flattenRows sel rows))

/-- **THE COMPOSITION IS NOT VACUOUS.** Two reachable states `s₀` and `s₃` (in the proof, the
constructed witness proxy and the state `ProxyRunWitness` reaches after the chain admin's cut),
and the facet cuts of `proxyWitnessFrozenCut` succeed on `s₀`'s storage with result `d`. Both
row lists satisfy
`RowsWf` under `proxyWitnessSelectors`. The check passes on `s₀` against
`proxyWitnessGenesisRows`, and on `d` and on `s₃` against `proxyWitnessCutRows`; it fails on `d`
against `proxyWitnessGenesisRows` (the cut added facet `23`). -/
@[witness] def Properties.ReachableCountCheckWitness : Prop :=
  ∃ (s₀ s₃ : ProxyState) (d : DiamondStorage), Reach proxyWitnessEnv s₀ ∧
    Reach proxyWitnessEnv s₃ ∧ diamondCut s₀.ds proxyWitnessFrozenCut.facetCuts = some d ∧
    RowsWf proxyWitnessSelectors proxyWitnessGenesisRows ∧
    RowsWf proxyWitnessSelectors proxyWitnessCutRows ∧
    CountCheck proxyWitnessSelectors s₀.ds proxyWitnessGenesisRows ∧
    CountCheck proxyWitnessSelectors d proxyWitnessCutRows ∧
    ¬ CountCheck proxyWitnessSelectors d proxyWitnessGenesisRows ∧
    CountCheck proxyWitnessSelectors s₃.ds proxyWitnessCutRows

/-! ## Dispatch and freezing -/

/-- **THE PROXY ROUTES EXACTLY BY THE MAP.** In any state, the fallback delegatecalls `f`
iff the calldata length is 0 or at least 4, `selectorToFacet[msg.sig]` routes to `f` with some
freezability `b`, and the diamond is unfrozen or `b` is false. -/
@[headline] def Properties.DispatchExact : Prop :=
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
unchanged. In particular no cut changes `isFrozen` (with an init in the model's `InitRun`
class). -/
@[headline] def Properties.OnlyCtmTogglesFreeze : Prop :=
  ∀ (E : Env) (c : Address) (s s' : ProxyState), Step E c s s' →
    s'.isFrozen ≠ s.isFrozen → c = E.ctm ∧ s'.ds = s.ds

/-- **WHEN A CALL FLIPS `isFrozen`, EXACTLY.** A step by `c` from `s` to `s'` flips the flag iff
`c` is `E.ctm`, `s'` is `s` with the flag negated, and some calldata that the proxy dispatches in
`s` (to some facet `f`) reaches `freezeDiamond` if `s` is unfrozen, `unfreezeDiamond` if it is
frozen. -/
@[headline] def Properties.FreezeToggleExact : Prop :=
  ∀ (E : Env) (c : Address) (s s' : ProxyState),
    (Step E c s s' ∧ s'.isFrozen ≠ s.isFrozen) ↔
      (c = E.ctm ∧ s' = { s with isFrozen := !s.isFrozen } ∧
        ∃ (cd : Calldata) (f : Address), fallbackTarget s cd = some f ∧
          E.fn f cd.sig = if s.isFrozen then .unfreeze else .freeze)

/-- **WHEN THE CTM CAN FREEZE AND UNFREEZE.** In any state: if it is unfrozen, the CTM has a step
to a frozen state iff some selector is routed (with either freezability) to a facet function
that is `freezeDiamond`; if it is frozen, the CTM has a step to an unfrozen state iff some
selector is routed **not freezable** to a facet function that is `unfreezeDiamond`. -/
def Properties.FreezeUnfreezeEnabledIff : Prop :=
  ∀ (E : Env) (s : ProxyState),
    (s.isFrozen = false →
      ((∃ s', Step E E.ctm s s' ∧ s'.isFrozen = true) ↔
        ∃ (x : Selector) (f : Address) (b : Bool),
          s.ds.routing x = some (f, b) ∧ E.fn f x = .freeze)) ∧
    (s.isFrozen = true →
      ((∃ s', Step E E.ctm s s' ∧ s'.isFrozen = false) ↔
        ∃ (x : Selector) (f : Address), s.ds.routing x = some (f, false) ∧ E.fn f x = .unfreeze))

/-- **NO OTHER CALLER CHANGES THE FREEZE FLAG.** A caller other than `E.ctm`
(`s.chainTypeManager`) — the chain admin `s.admin`, for one, whenever it is not the CTM — makes
no step that changes `isFrozen`. -/
def Properties.ChainAdminCannotFreeze : Prop :=
  ∀ (E : Env) (a : Address), a ≠ E.ctm → ∀ (s s' : ProxyState), Step E a s s' →
    s'.isFrozen = s.isFrozen

/-- **A CONSTRUCTED PROXY IS UNFROZEN, ON ITS CHAIN.** The constructor succeeds only when the
given chain id is `block.chainid` (`DiamondProxy.sol:19`), and its result is not frozen. -/
def Properties.ConstructedProxyIsUnfrozen : Prop :=
  ∀ (chainId blockChainId : ℕ) (cut : CutData) (r : InitRun) (s : ProxyState),
    construct chainId blockChainId cut r = some s → chainId = blockChainId ∧ s.isFrozen = false

/-- **A RUN WITH NO CALL BY THE CTM KEEPS THE FREEZE FLAG.** Cuts included: any run whose callers
are all other than `E.ctm` ends with the flag it started with. -/
def Properties.RunsWithoutCtmKeepFreeze : Prop :=
  ∀ (E : Env) (cs : List Address) (s s' : ProxyState), Run E cs s s' → E.ctm ∉ cs →
    s'.isFrozen = s.isFrozen

/-- **FREEZABLE CUT AND UNFREEZE ENTRY POINTS MAKE A FREEZE PERMANENT.** If a frozen state
routes every selector whose facet function is a cut entry point or `unfreezeDiamond` as
freezable, then every run from it, by any callers, ends in that same state: no step of the model
unfreezes it or changes its routing. -/
@[headline] def Properties.FreezableEntrypointsMakeFreezePermanent : Prop :=
  ∀ (E : Env) (cs : List Address) (s s' : ProxyState), s.isFrozen = true →
    (∀ (x : Selector) (f : Address) (b : Bool), s.ds.routing x = some (f, b) →
      (E.fn f x = .executeCut ∨ E.fn f x = .unfreeze) → b = true) →
    Run E cs s s' → s' = s

/-- **THE PERMANENT FREEZE IS REACHABLE.** A deployment whose init installs the Admin-like
facet as freezable (`proxyWitnessInit true`) is frozen by the CTM (`99`). The frozen state `s₁`
is reachable; calls still go through to the non-freezable Getters-like selector `7` (a run of two
calls, by `77` and by the CTM, from `s₁` back to `s₁`); the proxy refuses the cut entry point `1`
and `unfreezeDiamond` (`3`); and every run from `s₁`, by any callers, ends in `s₁`. -/
@[witness] def Properties.FreezePermanentWitness : Prop :=
  ∃ s₀ s₁ : ProxyState, construct 1 1 proxyWitnessCtorCut (proxyWitnessInit true) = some s₀ ∧
    Step proxyWitnessEnv 99 s₀ s₁ ∧ s₁.isFrozen = true ∧ Reach proxyWitnessEnv s₁ ∧
    Run proxyWitnessEnv [77, 99] s₁ s₁ ∧ fallbackTarget s₁ ⟨4, 7⟩ = some 24 ∧
    fallbackTarget s₁ ⟨4, 1⟩ = none ∧ fallbackTarget s₁ ⟨4, 3⟩ = none ∧
    ∀ (cs : List Address) (s' : ProxyState), Run proxyWitnessEnv cs s₁ s' → s' = s₁

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

/-- **`Replace` IS ENABLED EXACTLY UNDER ITS GUARDS AND A FREEZABILITY CONDITION ON THE FIRST
SELECTOR.** On consistent, freeze-uniform storage, a `Replace` cut by facet `f` with freezability
`b` and selectors `xs` succeeds iff `f` is nonzero, every selector of `xs` is routed, `xs` has a
first element `x₀`, and every selector already routed to `f`, other than `x₀`, has freezability
`b`. Duplicates in `xs` are allowed. The condition reads only `x₀` because `_replaceFunctions`
removes each selector before re-adding it (`Diamond.sol:187-190`): only the first iteration's
check (`Diamond.sol:243-248`) can meet a selector of `f` with another freezability. -/
def Properties.ReplaceEnabledIff : Prop :=
  ∀ (ds : DiamondStorage) (f : Address) (b : Bool) (xs : List Selector),
    DiamondOk ds → FreezeUniform ds →
    ((∃ d, facetCut ds ⟨f, .replace, b, xs⟩ = some d) ↔
      f ≠ 0 ∧ (∀ x ∈ xs, ds.routing x ≠ none) ∧
        ∃ (x₀ : Selector) (rest : List Selector), xs = x₀ :: rest ∧
          ∀ (y : Selector) (c : Bool), ds.routing y = some (f, c) → y ≠ x₀ → c = b)

/-- **`Remove` IS ENABLED EXACTLY UNDER ITS GUARDS.** On consistent storage, a `Remove` cut
succeeds iff its selector list is nonempty, its facet is zero, and its selectors are pairwise
distinct and routed. Its `isFreezable` field is ignored. -/
def Properties.RemoveEnabledIff : Prop :=
  ∀ (ds : DiamondStorage) (f : Address) (b : Bool) (xs : List Selector), DiamondOk ds →
    ((∃ d, facetCut ds ⟨f, .remove, b, xs⟩ = some d) ↔
      xs ≠ [] ∧ f = 0 ∧ xs.Nodup ∧ ∀ x ∈ xs, ds.routing x ≠ none)

/-- **CUTS KEEP EACH FACET'S FREEZABILITY UNIFORM.** On consistent storage, a successful
facet-cut list leaves every facet with one freezability. -/
def Properties.DiamondCutKeepsFreezeUniform : Prop :=
  ∀ (ds d : DiamondStorage) (cuts : List FacetCut), DiamondOk ds → FreezeUniform ds →
    diamondCut ds cuts = some d → FreezeUniform d

/-- **`Replace` DOES NOT REQUIRE A DIFFERENT FACET.** Replacing selector `1` of facet `11` by
facet `11` itself succeeds and flips its freezability (`11` has no other selector), and doing
it again succeeds and changes no route. -/
@[countermodel] def Properties.ReplaceWithSameFacetAccepted : Prop :=
  ∃ d₀ d₁ d₂ : DiamondStorage, facetCut DiamondStorage.fresh ⟨11, .add, false, [1]⟩ = some d₀ ∧
    facetCut d₀ ⟨11, .replace, true, [1]⟩ = some d₁ ∧
    d₀.routing 1 = some (11, false) ∧ d₁.routing 1 = some (11, true) ∧
    facetCut d₁ ⟨11, .replace, true, [1]⟩ = some d₂ ∧ d₂.routing = d₁.routing ∧ DiamondOk d₂

/-- **THE CUT RESULTS ARE NOT VACUOUS.** A reachable state `s` (in the proof, the witness proxy
after construction: `21` not freezable routing `1, 2, 3`, `22` freezable routing `5`, `24` not
freezable routing `7`) has consistent, freeze-uniform storage that routes `5` to `22` freezable
and `7` to `24` not freezable, and on it:

* `Add` of `8` to `22` succeeds as freezable and reverts as not freezable; `Add` of the routed
  `7` to a new facet `25` reverts;
* `Replace` by `22` as not freezable succeeds for `[5, 7]` and reverts for `[7, 5]` (in the
  second order the first selector is not `22`'s, and `22`'s selector `5` is freezable);
* `Remove` of `[5, 7]` succeeds and of `[5, 5]` reverts;
* a three-cut list (remove `7`, replace `5` by `22` as not freezable, add `7, 8` to `25` as
  freezable) succeeds. -/
@[witness] def Properties.CutEnablednessWitness : Prop :=
  ∃ s : ProxyState, Reach proxyWitnessEnv s ∧ DiamondOk s.ds ∧ FreezeUniform s.ds ∧
    s.ds.routing 5 = some (22, true) ∧ s.ds.routing 7 = some (24, false) ∧
    (∃ d, facetCut s.ds ⟨22, .add, true, [8]⟩ = some d) ∧
    facetCut s.ds ⟨22, .add, false, [8]⟩ = none ∧ facetCut s.ds ⟨25, .add, false, [7]⟩ = none ∧
    (∃ d, facetCut s.ds ⟨22, .replace, false, [5, 7]⟩ = some d) ∧
    facetCut s.ds ⟨22, .replace, false, [7, 5]⟩ = none ∧
    (∃ d, facetCut s.ds ⟨0, .remove, false, [5, 7]⟩ = some d) ∧
    facetCut s.ds ⟨0, .remove, false, [5, 5]⟩ = none ∧
    ∃ d, diamondCut s.ds
      [⟨0, .remove, false, [7]⟩, ⟨22, .replace, false, [5]⟩, ⟨25, .add, true, [7, 8]⟩] = some d

/-! ## The init call -/

/-- **A SUCCESSFUL `diamondCut` CHECKED ITS INIT.** If `diamondCut` (cuts, then init)
succeeds, then `isFrozen` is unchanged and the facet cuts succeeded with some storage `d₁`;
either there was no init (`initAddress == 0`) and the calldata was empty and the result is
`d₁`, or the init's delegatecall succeeded returning exactly the 32 bytes of
`DIAMOND_INIT_SUCCESS_RETURN_VALUE` and the result is what its nested cuts make of `d₁`. -/
@[headline] def Properties.InitReturnChecked : Prop :=
  ∀ (s s' : ProxyState) (c : CutData) (r : InitRun), diamondCutFull s c r = some s' →
    s'.isFrozen = s.isFrozen ∧
    ∃ d₁, diamondCut s.ds c.facetCuts = some d₁ ∧
      ((c.initAddress = 0 ∧ c.initCalldata = [] ∧ s'.ds = d₁) ∨
       (c.initAddress ≠ 0 ∧ r.outcome = .returned magicBytes ∧
         diamondCut d₁ r.nested = some s'.ds))

/-- **AN INIT'S NESTED CUT TAKES EFFECT.** From the constructed witness proxy, the CTM's call to
the cut entry point `1` runs `proxyWitnessUpgradeCut` (remove `7`, then the init at `60`, whose
nested cut adds `7` and `9` to facet `26`, returning the magic value). The step succeeds, the
result is reachable and routes `7` and `9` to `26`. The same cut reverts when the init returns
32 zero bytes, when it has no code, and when it reverts. -/
@[witness] def Properties.InitCallWitness : Prop :=
  ∃ s₀ s₁ : ProxyState, construct 1 1 proxyWitnessCtorCut (proxyWitnessInit false) = some s₀ ∧
    diamondCutFull s₀ proxyWitnessUpgradeCut proxyWitnessUpgradeInit = some s₁ ∧
    Step proxyWitnessEnv 99 s₀ s₁ ∧ Reach proxyWitnessEnv s₁ ∧
    s₀.ds.routing 7 = some (24, false) ∧
    s₁.ds.routing 7 = some (26, false) ∧ s₁.ds.routing 9 = some (26, false) ∧
    diamondCutFull s₀ proxyWitnessUpgradeCut
      ⟨proxyWitnessUpgradeInit.nested, .returned (List.replicate 32 0)⟩ = none ∧
    diamondCutFull s₀ proxyWitnessUpgradeCut codelessInit = none ∧
    diamondCutFull s₀ proxyWitnessUpgradeCut ⟨proxyWitnessUpgradeInit.nested, .reverted []⟩ = none

/-! ## Countermodels -/

/-- **THE RETURN-DATA CHECKS ARE LOAD-BEARING.** For every state and nonzero init address: a
delegatecall to an address with no code (success, no data) is refused, while the variant
without the checks accepts it; and a successful return of any other 32 bytes is refused, whatever
nested cuts the init made. -/
@[countermodel] def Properties.ReturnDataCheckLoadBearing : Prop :=
  ∀ (s : ProxyState) (init : Address) (cd : Bytes), init ≠ 0 →
    initializeDiamondCut s init cd codelessInit = none ∧
    initializeNoReturnCheck s init cd codelessInit = some s ∧
    ∀ (nested : List FacetCut) (data : Bytes), data.length = 32 → data ≠ magicBytes →
      initializeDiamondCut s init cd ⟨nested, .returned data⟩ = none

/-- **THE FREEZABILITY CHECK IS LOAD-BEARING.** Facet `11` routes `1`, not freezable. Adding
`2` to it as freezable reverts; without the check it succeeds, the facet is no longer
freeze-uniform, `isFacetFreezable(11)` reports `false`, and yet a frozen proxy refuses `2` while
serving `1`. -/
@[countermodel] def Properties.FreezabilityCheckLoadBearing : Prop :=
  ∃ d₀ d₁ : DiamondStorage, addFunctions DiamondStorage.fresh 11 [1] false = some d₀ ∧
    addFunctions d₀ 11 [2] true = none ∧
    addFunctionsNoFrzCheck d₀ 11 [2] true = some d₁ ∧
    ¬ FreezeUniform d₁ ∧ isFacetFreezable d₁ 11 = false ∧ d₁.routing 2 = some (11, true) ∧
    fallbackTarget ⟨d₁, true⟩ ⟨4, 2⟩ = none ∧ fallbackTarget ⟨d₁, true⟩ ⟨4, 1⟩ = some 11

/-- **THE `FacetExists` CHECK IS LOAD-BEARING.** Facet `11` routes `1`. Adding `1` to facet
`12` reverts; without the check it succeeds, reroutes `1` to `12`, leaves `1` in `11`'s selector
list, and breaks `DiamondOk`. -/
@[countermodel] def Properties.FacetExistsCheckLoadBearing : Prop :=
  ∃ d₀ d₁ : DiamondStorage, addFunctions DiamondStorage.fresh 11 [1] false = some d₀ ∧
    addFunctions d₀ 12 [1] false = none ∧
    addFunctionsNoExistsCheck d₀ 12 [1] false = some d₁ ∧
    d₁.routing 1 = some (12, false) ∧ 1 ∈ (d₁.facetToSelectors 11).selectors ∧ ¬ DiamondOk d₁

/-! ## Witness -/

/-- **THE RUN RESULTS ARE NOT VACUOUS.** The constructor refuses a wrong chain id and builds
`s₀` on the right one: the init installs the Admin-like facet `21` (not freezable), the
freezable `22` and the Getters-like `24`. The CTM (`99`) freezes it (`s₁`, reachable): selector
`5` of the freezable facet is refused, `unfreezeDiamond` (`3`) and the getter `7` are served,
and the getters report `22` freezable. The chain admin `77` then runs a cut through the
non-freezable cut entry point, adding the freezable facet `23` routing `6`, and calls the getter
(a run by `77` alone, `s₁` to `s₂`, which keeps the flag). The CTM unfreezes (`s₃`, reachable),
after which `5` and `6` are served. -/
@[witness] def Properties.ProxyRunWitness : Prop :=
  ∃ s₀ s₁ s₂ s₃ : ProxyState,
    construct 1 2 proxyWitnessCtorCut (proxyWitnessInit false) = none ∧
    construct 1 1 proxyWitnessCtorCut (proxyWitnessInit false) = some s₀ ∧
    s₀.isFrozen = false ∧ fallbackTarget s₀ ⟨4, 5⟩ = some 22 ∧
    Step proxyWitnessEnv 99 s₀ s₁ ∧ Reach proxyWitnessEnv s₁ ∧
    s₁.isFrozen = true ∧ s₁.ds.routing 5 = some (22, true) ∧ isFacetFreezable s₁.ds 22 = true ∧
    fallbackTarget s₁ ⟨4, 5⟩ = none ∧ fallbackTarget s₁ ⟨4, 3⟩ = some 21 ∧
    fallbackTarget s₁ ⟨4, 7⟩ = some 24 ∧
    Run proxyWitnessEnv [77, 77] s₁ s₂ ∧ s₂.isFrozen = true ∧ s₁.ds.routing 6 = none ∧
    s₂.ds.routing 6 = some (23, true) ∧
    Step proxyWitnessEnv 99 s₂ s₃ ∧ Reach proxyWitnessEnv s₃ ∧
    s₃.isFrozen = false ∧ fallbackTarget s₃ ⟨4, 5⟩ = some 22 ∧
    fallbackTarget s₃ ⟨4, 6⟩ = some 23 ∧ isFacetFreezable s₃.ds 21 = false

end Contracts.Diamond
