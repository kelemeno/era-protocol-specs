# Diamond

The chain diamond proxy at era-contracts `draft/v0.35.0` `b17415d20`: dispatch, the freeze flag,
facet cuts and the init call, over runs of every entry point that writes diamond storage.

## Headline guarantees

The folder's real guarantees about `b17415d20`, each with every premise. They are meant to carry
`@[headline]` (the lists after the table: `@[witness]`, `@[countermodel]`) once the tag attributes
of `EraSpec.Core.Headline` are on this branch; they are not tagged yet.
"Reachable" means a successful constructor followed by any run of calls through the proxy, by any
callers, for any facet behaviour. A cut's init is in the `InitRun` class: nested
`Diamond.diamondCut` calls without an init of their own, then a revert or return data. Init code
that writes diamond storage directly is outside the model (`MODEL-DIAMOND-PROXY`).

| Guarantee | Premises | Statement |
|---|---|---|
| The three routing structures agree position by position, and all selectors of a facet share one freezability | Reachable state | `ReachableInvariant` |
| `isFacetFreezable` and `isFunctionFreezable` report the freezability the proxy enforces, and a call on a routed selector reaches its facet exactly when the diamond is unfrozen or the facet is not freezable | Reachable state | `ReachableGettersMatchDispatch` |
| The fallback delegatecalls `f` iff the calldata is empty or at least 4 bytes, `msg.sig` is routed to `f`, and the diamond is unfrozen or the route is not freezable | None | `DispatchExact` |
| Only a call by `s.chainTypeManager` flips `isFrozen`, and that call changes no routing; no cut changes the flag | None | `OnlyCtmTogglesFreeze` |
| A call flips `isFrozen` iff the caller is the CTM and the proxy dispatches it to `freezeDiamond` (unfrozen) or `unfreezeDiamond` (frozen) | None | `FreezeToggleExact` |
| A frozen diamond whose cut entry points and `unfreezeDiamond` are all routed freezable never changes again | None | `FreezableEntrypointsMakeFreezePermanent` |
| A successful `diamondCut` leaves `isFrozen` unchanged, and either had no init and empty calldata, or its init returned exactly the 32 bytes of `DIAMOND_INIT_SUCCESS_RETURN_VALUE` | None | `InitReturnChecked` |
| On reachable storage, and on what further facet cuts make of it, the CTM's live-routing count check against well-formed release rows passes exactly when the storage routes exactly the release's rows | Reachable state; release rows nonempty and duplicate-free (what `CTMRelease.validate()` checks) | `ReachableCountCheckExact` |

Witnesses: `ProxyRunWitness`, `FreezePermanentWitness`, `CutEnablednessWitness`,
`InitCallWitness`, `ReachableCountCheckWitness`. Countermodels:
`ReplaceWithSameFacetAccepted`, `ReturnDataCheckLoadBearing`, `FreezabilityCheckLoadBearing`,
`FacetExistsCheckLoadBearing`. The other statements are supporting lemmas.

## Source

era-contracts `draft/v0.35.0` at **`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`**, paths under
`l1-contracts/contracts/`; every `file:line` is at that commit.

- `state-transition/libraries/Diamond.sol`: storage, `diamondCut`, Add/Replace/Remove, the init call;
- `state-transition/chain-deps/DiamondProxy.sol`: constructor and `fallback`;
- `state-transition/chain-deps/DiamondInit.sol`: the init chain creation uses (modelled by what
  it does to diamond storage and what it returns);
- `state-transition/chain-deps/facets/Admin.sol:559-639`: the facet functions that write diamond
  storage (`upgradeChainFromVersion`, `executeUpgrade`, `genesisUpgrade`, `freezeDiamond`,
  `unfreezeDiamond`), with `_executeDiamondCut` at `:117-128`;
- `state-transition/chain-deps/facets/ZKChainBase.sol:85-90`: `onlyChainTypeManager`;
- `state-transition/chain-deps/facets/Getters.sol:207-217, 245-252`: `isFacetFreezable`,
  `isFunctionFreezable`.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| DiamondProxy | [Specs/DiamondProxy.lean](Specs/DiamondProxy.lean) | [Properties/DiamondProxy.lean](Properties/DiamondProxy.lean) | [Proofs/DiamondProxy.lean](Proofs/DiamondProxy.lean) |

Namespace `Contracts.Diamond`. Statements are `Contracts.Diamond.Properties.*`; each proof has
the same name without the `Properties` segment.

## Reuse of the ChainTypeManager model

`Diamond.sol`, `DiamondProxy.sol` and `DiamondInit.sol` are byte-identical at `b17415d20` and at
`e561b9cc2`, the commit [`ChainTypeManager/Specs/DiamondStorage.lean`](../ChainTypeManager/Specs/DiamondStorage.lean)
transcribes. This folder imports that model unchanged: the routing storage, the three actions,
the facet-cut loop, and the invariant `DiamondOk`, with its preservation proofs
(`DiamondCutPreservesOk`) and routing lemmas (`AddFunctionsRoutes`, …). It does not restate them.
It adds what that model leaves out: `isFrozen`, the proxy's dispatch, the init call and its
return-data check, the entry points that write diamond storage, and runs over all of them. It
also uses `ChainTypeManager/LiveRouting`'s model of the count check `requireReleaseRouting`
(`ReachableCountCheckExact`).

## What is modelled

- `ProxyState`: the whole `Diamond.DiamondStorage`, that is the routing structures plus `isFrozen`.
- `fallbackTarget`: `DiamondProxy.fallback`'s three `require`s in source order, and the facet
  it delegatecalls.
- `initializeDiamondCut` / `diamondCutFull`: the facet cuts, then the init. A nonzero init's
  delegatecall is an `InitRun`: the nested `Diamond.diamondCut` calls it makes (each without an
  init of its own), then reverted or returned with return data. The return data must be exactly
  32 bytes decoding to `DIAMOND_INIT_SUCCESS_RETURN_VALUE`.
- `construct`: the constructor's chain-id check, then the cut on fresh storage.
- `Step` (labelled by caller), `Run`, `Reach`: every call through the proxy. The facet function
  the proxy reaches is a cut entry point, `freezeDiamond`, `unfreezeDiamond`, or any other
  function, and only the first three write diamond storage (`Env.fn`). `freezeDiamond` and
  `unfreezeDiamond` keep `onlyChainTypeManager` and their flag checks. `Env` (the facet
  functions and `s.chainTypeManager`) is fixed for a run.
- Countermodel variants with one check deleted each: the freezability check, `FacetExists`,
  and the return-data checks.

## What is not modelled

- The cut entry points' own guards (callers, protocol-version and timestamp checks, the
  proof-mode check after the cut): any cut by any caller is a step. That only adds runs, so the
  safety results still hold.
- Facet storage (`ZKChainStorage`). `Env.ctm` stands for `s.chainTypeManager`, which at the pin
  only `DiamondInit.sol:91` writes.
- Init or facet code that writes diamond storage other than through `Diamond.diamondCut`,
  `freezeDiamond` and `unfreezeDiamond`, for example an upgrade contract's raw `sstore`, and
  nested cuts with an init of their own. At the pin, `Admin.sol` is the only facet that writes
  diamond storage. Init code is arbitrary delegatecalled code and is a model boundary
  (`MODEL-DIAMOND-PROXY`).
- Calls into the proxy made while another call is running: a run lists complete calls.
- The code-existence check, except for address zero, and the `toUint16` casts. Both are inherited
  from the reused model; each omission only removes reverts.
- Gas, return data forwarding of the fallback, events, `DiamondInit`'s writes to
  `ZKChainStorage`, and its `reentrancyGuardInitializer`.

## What to check

**Run-level** (any interleaving of all entry points, from any successful constructor):

- Every reachable state satisfies `DiamondOk` and `FreezeUniform`, which means every facet has
  one freezability (`ReachableInvariant`).
- In every reachable state, `isFacetFreezable(f)` and `isFunctionFreezable(x)` equal the
  freezability the proxy enforces for a selector `x` routed to `f`. A call on `x` reaches `f`
  exactly when the diamond is unfrozen or the getter says `f` is not freezable
  (`ReachableGettersMatchDispatch`).
- On every reachable state, and on what further facet cuts make of it (the storage a cut's init
  reads, as `DefaultUpgrade.upgradeFromTransition` does at `upgrades/DefaultUpgrade.sol:36`), the
  count check of `requireReleaseRouting` against release rows that pass `validate()`'s row checks
  is exact routing (`ReachableCountCheckExact`: the `DiamondOk` premise of `ChainTypeManager`
  `CountCheckIffExactRouting`, discharged).
- Only a call by `s.chainTypeManager` flips `isFrozen`, and that call changes no routing
  (`OnlyCtmTogglesFreeze`); exactly when it reaches `freezeDiamond` or `unfreezeDiamond` through
  the dispatch (`FreezeToggleExact`), so the CTM can unfreeze iff some selector routed not
  freezable reaches `unfreezeDiamond` (`FreezeUnfreezeEnabledIff`). No other caller changes the
  flag (`ChainAdminCannotFreeze`), and a run with no CTM call keeps it, cuts included
  (`RunsWithoutCtmKeepFreeze`).
- If every cut entry point and `unfreezeDiamond` is routed freezable, a frozen diamond never
  changes again (`FreezableEntrypointsMakeFreezePermanent`). This is reachable: an init that
  installs the Admin-like facet as freezable, then one freeze; calls to a non-freezable getter
  still succeed there (`FreezePermanentWitness`).

**Dispatch:**

- `fallbackTarget s cd = some f` holds iff the calldata length is 0 or at least 4, `msg.sig` is
  routed to `f`, and the diamond is unfrozen or the route is not freezable (`DispatchExact`).
- Freezing blocks exactly the freezable routes. It changes nothing for any other calldata
  (`FreezeBlocksExactlyFreezable`).

**The cut:**

- Guards: a nonempty selector list for every action. `Add` needs a nonzero facet and distinct,
  unrouted selectors. `Replace` needs a nonzero facet and routed selectors. `Remove` needs facet
  zero and distinct, routed selectors. Each reroutes exactly its selectors (`FacetCutGuards`).
- On consistent, freeze-uniform storage these guards are exact. `Add` is enabled exactly under
  them plus the freezability check (`AddEnabledIff`). `Replace` is enabled exactly when, besides
  them, every selector already routed to the target facet other than the cut's first selector
  has the cut's freezability (`ReplaceEnabledIff`); duplicates are allowed, and the selector
  order matters (`CutEnablednessWitness`: `[5, 7]` succeeds where `[7, 5]` reverts). `Remove`
  is enabled exactly under its guards, on consistent storage alone (`RemoveEnabledIff`).
- Cuts keep `FreezeUniform` (`DiamondCutKeepsFreezeUniform`).
- `Replace` does **not** require a different facet. Replacing a selector by its own facet
  succeeds; for a one-selector facet it flips the freezability (`ReplaceWithSameFacetAccepted`).

**The init call:**

- A successful `diamondCut` leaves `isFrozen` unchanged. Either it had no init and empty calldata,
  or its init returned exactly the 32 bytes of `DIAMOND_INIT_SUCCESS_RETURN_VALUE`
  (`InitReturnChecked`). "Exactly those bytes" uses injectivity of 32-byte big-endian decoding,
  proved in `decode_eq_magic`, not assumed.
- `InitCallWitness`: an upgrade-like cut whose init makes a nested cut succeeds as a CTM step and
  its nested routes take effect; it reverts when the init returns 32 zero bytes, has no code, or
  reverts.
- `ConstructedProxyIsUnfrozen`: the constructor needs `_chainId == block.chainid` and yields an
  unfrozen diamond.

**Countermodels** (each check is load-bearing):

- `FreezabilityCheckLoadBearing`: without the check in `_addOneFunction`, facet `11` gets one
  non-freezable and one freezable selector. `isFacetFreezable(11)` then reports `false`, yet a
  frozen proxy refuses one of its selectors.
- `FacetExistsCheckLoadBearing`: without `FacetExists`, `Add` silently reroutes a routed selector.
  The old facet still lists it, and `DiamondOk` fails.
- `ReturnDataCheckLoadBearing`: an init address with no code (delegatecall succeeds, no return
  data) is rejected, and so is any other 32-byte answer, whatever nested cuts the init made.
  Without the checks the codeless init is accepted. This confirms the comment at `Diamond.sol:317`
  ("Do not check whether `_init` is a contract since later we check that it returns data").

**Witnesses:** `ProxyRunWitness` constructs a proxy whose init installs an Admin-like facet
(not freezable), a freezable Executor-like facet and a non-freezable Getters-like facet, and
shows the chain-id check refusing a wrong id. The CTM freezes it; the chain admin (not the CTM)
runs a cut through the non-freezable cut entry point while it is frozen, adding a facet, and calls
a getter; the CTM unfreezes it. The intermediate and final states are reachable.
`CutEnablednessWitness`, `InitCallWitness` and `ReachableCountCheckWitness` instantiate the
premises of the cut, init and count-check results on reachable states.

## Configuration

Which facets a release marks freezable is release configuration (`OPS-CONFIG`): nothing in
`Diamond.sol` or `CTMRelease` constrains a row's `isFreezable`. The deploy scripts at the pin
mark the Admin and Getters facets not freezable (`l1-contracts/deploy-scripts/ctm/
DeployCTMUtils.s.sol:103-104`). With the cut entry points and `unfreezeDiamond` routed freezable,
the model admits no change after a freeze (`FreezableEntrypointsMakeFreezePermanent`).

The facet-level counterparts of the freeze results, with the per-selector freezable bit as state
and routing assumed, are in the `AdminFacet` topic merged separately (`FreezeUnfreezeExact`,
`FreezableUnfreezeStrandsTheChain`); this folder states them over the proxy's own routing storage
and its cuts.

## Open

- The `InitRun` class excludes init code that writes diamond storage directly. For an arbitrary
  init, `ReachableInvariant` does not hold (`CorruptStorageFoolsCountCheck` in
  `ChainTypeManager/LiveRouting` shows the consequence for the routing check).
- No connection to deployed bytecode (`VM-CALL`, `VM-REVERT`, `BUILD-PRESERVATION`).

## Review order

1. `Specs/DiamondProxy.lean`, against the source files above.
2. `Properties/DiamondProxy.lean`: each statement and its docstring.
3. `Proofs/DiamondProxy.lean` only if needed. The audit checks that every property has its
   full named theorem.
