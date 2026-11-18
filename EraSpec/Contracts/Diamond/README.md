# Diamond

Source: era-contracts `draft/v0.35.0` at **`d9f678900e1bc8286412b78f56d4a9f443983c29`**, paths
under `l1-contracts/contracts/`:

- `state-transition/libraries/Diamond.sol`: storage, `diamondCut`, Add/Replace/Remove, the init call;
- `state-transition/chain-deps/DiamondProxy.sol`: constructor and `fallback`;
- `state-transition/chain-deps/DiamondInit.sol`: the init chain creation uses (modelled by what
  it does to diamond storage and what it returns);
- `state-transition/chain-deps/facets/Admin.sol:559-639`: the facet functions that write diamond
  storage (`upgradeChainFromVersion`, `executeUpgrade`, `genesisUpgrade`, `freezeDiamond`,
  `unfreezeDiamond`);
- `state-transition/chain-deps/facets/Getters.sol:207-217, 245-252`: `isFacetFreezable`,
  `isFunctionFreezable`.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| DiamondProxy | [Specs/DiamondProxy.lean](Specs/DiamondProxy.lean) | [Properties/DiamondProxy.lean](Properties/DiamondProxy.lean) | [Proofs/DiamondProxy.lean](Proofs/DiamondProxy.lean) |

Namespace `Contracts.Diamond`. Statements are `Contracts.Diamond.Properties.*`; each proof has
the same name without the `Properties` segment.

## Reuse of the ChainTypeManager model

`Diamond.sol`, `DiamondProxy.sol` and `DiamondInit.sol` are byte-identical at `d9f6789` and at
`e561b9cc2`, the commit [`ChainTypeManager/Specs/DiamondStorage.lean`](../ChainTypeManager/Specs/DiamondStorage.lean)
transcribes. This folder imports that model unchanged: the routing storage, the three actions,
the facet-cut loop, and the invariant `DiamondOk`, with its preservation proofs
(`DiamondCutPreservesOk`) and routing lemmas (`AddFunctionsRoutes`, …). It does not restate them.
It adds what that model leaves out: `isFrozen`, the proxy's dispatch, the init call and its
return-data check, the entry points that write diamond storage, and runs over all of them.

## What is modelled

- `ProxyState`: the whole `Diamond.DiamondStorage`, that is the routing structures plus `isFrozen`.
- `fallbackTarget`: `DiamondProxy.fallback`'s three `require`s in source order, and the facet
  it delegatecalls.
- `initializeDiamondCut` / `diamondCutFull`: the facet cuts, then the init. A nonzero init's
  delegatecall is an `InitRun`: the nested `Diamond.diamondCut` calls it makes, then reverted
  or returned with return data. The return data must be exactly 32 bytes decoding to
  `DIAMOND_INIT_SUCCESS_RETURN_VALUE`.
- `construct`: the constructor's chain-id check, then the cut on fresh storage.
- `Step` (labelled by caller), `Run`, `Reach`: every call through the proxy. The facet function
  the proxy reaches is a cut entry point, `freezeDiamond`, `unfreezeDiamond`, or any other
  function, and only the first three write diamond storage (`Env.fn`). `freezeDiamond` and
  `unfreezeDiamond` keep `onlyChainTypeManager` and their flag checks.
- Countermodel variants with one check deleted each: the freezability check, `FacetExists`,
  and the return-data checks.

## What is not modelled

- The cut entry points' own guards (caller, protocol-version checks): any cut by any caller is a
  step. That only adds runs, so the safety results still hold.
- Facet storage (`ZKChainStorage`). `Env.ctm` stands for `s.chainTypeManager`.
- Init or facet code that writes diamond storage other than through `Diamond.diamondCut`,
  `freezeDiamond` and `unfreezeDiamond`, for example an upgrade contract's raw `sstore`. At the
  pin, `Admin.sol` is the only facet that writes diamond storage. Init code is arbitrary
  delegatecalled code and is a model boundary (`MODEL-DIAMOND-PROXY`).
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
- Only a call by `s.chainTypeManager` flips `isFrozen`, and that call changes no routing
  (`OnlyCtmTogglesFreeze`). A run with no CTM call keeps the flag (`RunsWithoutCtmKeepFreeze`).
- If every cut entry point and `unfreezeDiamond` is routed freezable, a frozen diamond never
  changes again (`FreezableEntrypointsMakeFreezePermanent`). This is reachable: an init that
  installs the Admin-like facet as freezable, then one freeze (`FreezePermanentWitness`).

**Dispatch:**

- `fallbackTarget s cd = some f` holds iff the calldata length is 0 or at least 4, `msg.sig` is
  routed to `f`, and the diamond is unfrozen or the route is not freezable (`DispatchExact`).
- Freezing blocks exactly the freezable routes. It changes nothing for any other calldata
  (`FreezeBlocksExactlyFreezable`).

**The cut:**

- Guards: a nonempty selector list for every action. `Add` needs a nonzero facet and distinct,
  unrouted selectors. `Replace` needs a nonzero facet and routed selectors. `Remove` needs facet
  zero and distinct, routed selectors. Each reroutes exactly its selectors (`FacetCutGuards`).
- `Add` is enabled exactly under these guards plus the freezability check, on consistent
  storage (`AddEnabledIff`).
- Cuts keep `FreezeUniform` (`DiamondCutKeepsFreezeUniform`).
- `Replace` does **not** require a different facet. Replacing a selector by its own facet
  succeeds; for a one-selector facet it flips the freezability (`ReplaceWithSameFacetAccepted`).
  The EIP-2535 reference implementation rejects this. The source has no such check, and nothing
  depends on one.

**The init call:**

- A successful `diamondCut` leaves `isFrozen` unchanged. Either it had no init and empty calldata,
  or its init returned exactly the 32 bytes of `DIAMOND_INIT_SUCCESS_RETURN_VALUE`
  (`InitReturnChecked`). "Exactly those bytes" uses injectivity of 32-byte big-endian decoding,
  proved in `decode_eq_magic`, not assumed.
- `ConstructedProxyIsUnfrozen`: the constructor needs `_chainId == block.chainid` and yields an
  unfrozen diamond.

**Countermodels** (each check is load-bearing):

- `FreezabilityCheckLoadBearing`: without the check in `_addOneFunction`, facet `11` gets one
  non-freezable and one freezable selector. `isFacetFreezable(11)` then reports `false`, yet a
  frozen proxy refuses one of its selectors.
- `FacetExistsCheckLoadBearing`: without `FacetExists`, `Add` silently reroutes a routed selector.
  The old facet still lists it, and `DiamondOk` fails.
- `ReturnDataCheckLoadBearing`: an init address with no code (delegatecall succeeds, no return
  data) is rejected, and so is any other 32-byte answer. Without the checks the codeless init is
  accepted. This confirms the comment at `Diamond.sol:317` ("Do not check whether `_init` is a
  contract since later we check that it returns data").

**Witness:** `ProxyRunWitness` constructs a proxy whose init installs an Admin-like facet
(not freezable) and a freezable facet. The CTM freezes it, a cut adds a facet while it is frozen
(cuts are not blocked by freezing when their entry point is not freezable), and the CTM unfreezes
it. The final state is reachable.

## Findings (internal)

- **NatSpec:** `IGetters.isFunctionFreezable` / `isFacetFreezable` (`IGetters.sol:188-192`) say a
  freezable selector "can be frozen by the admin". `freezeDiamond` is `onlyChainTypeManager`
  (`Admin.sol:616`), reached through `ChainTypeManager.freezeChain` (owner or bridgehub owner).
  The chain admin cannot freeze (`ChainAdminCannotFreeze`). This is a wording issue.
- **Configuration obligation:** nothing in `Diamond.sol` or `CTMRelease` stops a release from
  marking the Admin facet freezable. If it does, one `freezeChain` bricks the chain's diamond for
  good (`FreezableEntrypointsMakeFreezePermanent`, `FreezePermanentWitness`). Freezability is
  set per facet by release configuration (`OPS-CONFIG`).
- **Not a bug, for the record:** a same-facet `Replace` is accepted (above).

## Open

- Enabledness of `Replace` and `Remove` (the converse of their guards) is not proved. It needs a
  success lemma for `_removeOneFunction`'s swap-and-pop and `_removeFacet` on `DiamondOk` storage.
- The `InitRun` class excludes init code that writes diamond storage directly. For an arbitrary
  init, `ReachableInvariant` does not hold (`CorruptStorageFoolsCountCheck` in
  `ChainTypeManager/LiveRouting` shows the consequence for the routing check).
- No connection to deployed bytecode (`VM-CALL`, `VM-REVERT`, `BUILD-PRESERVATION`).

## Review order

1. `Specs/DiamondProxy.lean`, against the four source files above.
2. `Properties/DiamondProxy.lean`: each statement and its docstring.
3. `Proofs/DiamondProxy.lean` only if needed. The audit checks that every property has its
   full named theorem.
