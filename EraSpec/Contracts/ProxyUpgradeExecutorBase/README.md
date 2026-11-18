# ProxyUpgradeExecutorBase

Source: `l1-contracts/contracts/upgrades/registry/executors/ProxyUpgradeExecutorBase.sol` and
`CoreUpgradeExecutor.sol`, with the engine it delegatecalls
(`engines/DefaultProxyUpgradeEngine.sol`) and `libraries/ProxyUpgradeRowLib.sol`. The code is
**not** in the pinned era-contracts tree. It lives on branch `draft/v0.35.0` of the era-contracts
repository, and the `CoreLegV35` model is written against commit **`b17415d20`**
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, 2026-11-16); a first draft cited `d9f678900`.
**The branch moves**: every `file:line` quoted in the spec is at that commit. OpenZeppelin lines
are at the submodule that commit pins (`dc44c9f1a4c3`, release 4.9.6).

`ProxyUpgradeExecutorBase.sol` is the base of both registry-driven domain executors
(`CTMUpgradeExecutor`, `CoreUpgradeExecutor`); each topic names the commit its `file:line`s are at.

| Topic | Source commit | Namespace | Specification | Property statements | Checked proofs |
|---|---|---|---|---|---|
| CoreLegV35 | `b17415d20` (2026-11-16) | `Contracts.ProxyUpgradeExecutorV35.CoreLeg` | [Specs/CoreLegV35.lean](Specs/CoreLegV35.lean) | [Properties/CoreLegV35.lean](Properties/CoreLegV35.lean) | [Proofs/CoreLegV35.lean](Proofs/CoreLegV35.lean) |
| DomainHoldersV35 | `b17415d20` (2026-11-16); the `d9f678900` leg kept as `D9.leg` | `Contracts.DomainHoldersV35` | [Specs/DomainHoldersV35.lean](Specs/DomainHoldersV35.lean) | [Properties/DomainHoldersV35.lean](Properties/DomainHoldersV35.lean) | [Proofs/DomainHoldersV35.lean](Proofs/DomainHoldersV35.lean) |

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions. Statements are `<namespace>.Properties.*`; each certificate has the same
name without the `Properties` segment.

## The Core leg (topic CoreLegV35)

`CoreUpgradeExecutor.applyL1Upgrade(T)` (`CoreUpgradeExecutor.sol:33-36`) is `onlyOwner`. It
runs `_applyProxyUpgradeTransition` with the ecosystem `ProxyAdmin` and a zero CTM
(`ProxyUpgradeExecutorBase.sol:51-104`): the transition and the engine it pins must be code and
the domain `Core`; the executor DELEGATECALLS the engine's `executeUpgrade`, so the engine acts
with the executor's storage and its ownership of the `ProxyAdmin`; afterwards the executor
requires its owner and pending owner unchanged, `keccak256(abi.encode(PROXY_ADMIN.owner()))`
unchanged (the zero-CTM branch of `_domainHolders`, `:119-121`), and every row's proxy at its
`implNew` as `ProxyAdmin.getProxyImplementation` reads it (`requireRowsApplied`). At
`e561b9cc2` (branch `feat/upgrade-simplification`) the executor applied the rows itself
(`../ProxyUpgradeRowLib/`, `RowsCurrent`).

### What to check

- `CoreLegChecks`, `CoreLegExact`: what a successful leg establishes, and that the leg checks
  exactly that, for every engine. The `ProxyAdmin`'s owner is unchanged or its `keccakOwner`
  collides with the old owner's on that one pair; `CorePAOwnerMoveCaught` is the revert form,
  with the non-collision premise pinned to the pair.
- Each check is load-bearing: `CorePAOwnerCheckIsLoadBearing`,
  `CoreExecutorOwnerCheckIsLoadBearing`, `CorePendingOwnerCheckIsLoadBearing`,
  `CoreRowsCheckIsLoadBearing` (an engine that does nothing) and `CoreRowsCheckCatchesAfterHook`
  (a follow-up hook moving a row's proxy back, caught by the executor's second
  `requireRowsApplied`). `CorePAOwnerMoveUnderCollisionPasses` shows the collision disjunct
  cannot be dropped while `keccakOwner` is an arbitrary function.
- What the checks read: `CorePostCheckScopeIsRows` (two engine results agreeing on the owners,
  the `ProxyAdmin` owner's hash and the row reads pass or fail together) and
  `CorePostCheckScopeAdministered` (the same with implementation slots, when the `ProxyAdmin`
  administers the rows' proxies); `CorePostCheckScopeWitness` instantiates both with two
  different results. `CoreUnnamedAdminMoveAlwaysPasses` and `CoreUnnamedImplMoveAlwaysPasses`:
  for every successful default leg that leaves every row's proxy under the `ProxyAdmin`, a
  release engine whose `_afterSwaps` moves the admin or the implementation of a proxy that no row
  names and the `ProxyAdmin` administers also completes, with exactly that change. The runs
  `CoreEngineMovesUnnamedSingletonAdmin` and `CoreEngineMovesUnnamedSingletonImpl` instantiate
  them. `IProxyUpgradeEngine.sol:16-21` states this boundary: what an engine does through the
  `ProxyAdmin` beyond the holders and the rows rests on the review of the engine's code.
- Row proxies after the leg: `CoreRowAdministeredIsAtImplNew` (a row proxy the `ProxyAdmin`
  administers after the leg is at `implNew`); `CoreRowAdminMoveCaught` and `CoreRowAdminMoveReverts`
  (for a row proxy the `ProxyAdmin` does not administer, the check reads the answer of the
  implementation's code to `implementation()`), with `CoreRowAdminMoveRevertsWitness`;
  `CoreRowAdminMoveUncaughtWhenAnswerMatches` shows the answer premise is needed.
- The default engine: `DefaultCoreLegIsTheEngineRun` (the post-checks never reject a run of
  `DefaultProxyUpgradeEngine`), `DefaultCoreLegReplayIsNoop` (applying a transition again
  changes nothing), both with no premise on administration or reinitializers;
  `DefaultCoreLegNeedsOwnedAdmin`; `DefaultCoreLegIsApplyRows` (the leg is
  `RowsCurrent.ApplyRows` when the `ProxyAdmin` administers every row's proxy and no
  reinitializer writes an admin slot) and `DefaultCoreLegOnlyNamedEdges`
  (`OnlyNamedEdgesAcrossCall` carried over). Both premises are needed
  (`DefaultLegNeedsAdministeredRows`, `DefaultLegReinitMovesRowAdmin`); the ownership conjunct
  is new at this pin (`UnownedReplayRevertsAtV35`). `CoreLegWitness` instantiates every premise
  of the default-engine results on one run whose row calls a reinitializer.

### Model boundaries

`MODEL-PROXY-LEG` in the [assumption register](../../../ASSUMPTIONS.md). The world is the
executor's owner and pending owner, the `ProxyAdmin`'s owner, and each proxy's EIP-1967
implementation and admin slots; every address read as a proxy runs
`TransparentUpgradeableProxy` code. The engine is any function of the context, the inventory and
the world. A read of a proxy the `ProxyAdmin` does not administer is an arbitrary answer of the
implementation's code, which may depend on the world; a `ProxyAdmin` call forwarded to such a
proxy's implementation (`upgradeTo`, `changeAdmin`) is a revert, so UUPS-style implementations
are not covered. A reinitializer is an arbitrary function from the world after its swap to the
two mappings, and never reverts. `keccak256(abi.encode(owner))` is an arbitrary function. The
CTM side of `_domainHolders` and the CTM-only check are opaque (`CoreLegIgnoresCTMBranch`).
Events, ETH and other storage are not modelled. The witnesses use toy data (identity owner
hash, small addresses).

### Re-pin from `d9f678900`

`git diff d9f678900 b17415d20` changes `_applyProxyUpgradeTransition` and `_domainHolders` only
on the CTM side (a new CTM-only check at `:72-77`; the ServerNotifier read moved into
`_domainHolders`), gives each `DefaultProxyUpgradeEngine` hook and `toRows` its own memory copy of
the calldata inventory (`:38-46`; the model passes each hook the inventory as pinned, the
`b17415d20` code), and adds a `@dev` paragraph to `ProxyUpgradeRowLib.sol` (`:28-32`), moving its
lines by five. `CoreUpgradeExecutor.sol`, `ICoreUpgradeExecutor.sol` and
`objects/ProxyUpgradeTransition.sol` are unchanged.

## The domain-holder check (topic DomainHoldersV35)

`_applyProxyUpgradeTransition` (`:51-104` at `b17415d20`) delegatecalls the engine a transition
pins, with the executor's authority. Before and after, it hashes who holds the domain
(`_domainHolders`, `:118-148`) and reverts if the two hashes differ. With a CTM the hash covers
the `ProxyAdmin`'s owner; the CTM's owner, pending owner, `admin()`, `getProxyAdmin` answer and
`serverNotifierAddress()`; and that notifier's owner, pending owner, `getProxyAdmin` answer and
`chainTypeManager()`. Before the engine runs, the leg also refuses a CTM whose `admin()` is the
`ProxyAdmin` (`:75-77`).

`ProxyUpgradeExecutorBase.sol` changed between `d9f678900` and `b17415d20` in one commit,
`9775be946` (#2669): the check at `:75-77` is new, the hash gained `admin()`, the notifier
address and the notifier's `chainTypeManager()`, and the notifier is read afresh by each
`_domainHolders` call instead of once before the engine. `b17415d20` itself changes no contract.
The model is the `b17415d20` leg (`leg`); the `d9f678900` leg is `D9.leg`.

### What to check

- `PassingLegKeepsHolderReads`: a successful leg leaves every hashed read unchanged, or the
  leg's own compared word lists collide (`HolderPairCollides`, pinned to the instance). No hash
  premise. `PendingAdminLegWitness` is a passing leg.
- `MovedCtmCaught`: if the `ProxyAdmin` administered the CTM proxy before the leg and the
  engine moved the admin slot away, the leg reverts or the compared pair collides. There is no
  premise on what the CTM's `admin()` answers afterwards. `MovedCtmCaughtNotVacuous` fires it
  with the aliasing engine below; `MovedCtmCollisionDisjunctLoadBearing` shows the collision
  disjunct is needed (constant hash).
- The check at `:75-77`: `CtmAdminIsProxyAdminReverts`. `CtmAdminCheckLoadBearing`: from a CTM
  whose `admin()` is the `ProxyAdmin`, moving the CTM proxy's admin leaves the hashed word list
  unchanged for every hash, and every other check of the leg passes.
- `MovedNotifierReverts`: a nonzero notifier the CTM points at after the engine, not under the
  `ProxyAdmin` and without `admin()`, reverts the leg. No hash premise.
  `NotifierAdminGetterLoadBearing`: with a notifier implementation that answered `admin()` with
  the `ProxyAdmin`, the same move would pass for every hash.
- `CtmPendingAdminOutsideHash`: in the standing configuration with the check at `:75-77`
  passing and the rows applied, an engine that only calls `ctm.setPendingAdmin(Y)` passes, for
  every `Y` and hash, as the `@dev` at `:115-116` says.
- `MovedCtmWithCtmRowReverts`: a moved CTM whose implementation has no `implementation()` and
  that has a participating row reverts at the rows post-check, at both commits.
- **Comparison with `d9f678900`** (`AliasingPassesAtD9CaughtAtB17`). The aliasing engine sets
  the CTM's `pendingAdmin` to the `ProxyAdmin`, has the `ProxyAdmin` run
  `upgradeAndCall(ctm, liveImpl, acceptAdmin())` (so `acceptAdmin` sees
  `msg.sender = ProxyAdmin`), then moves the CTM proxy's admin to `X`. In the standing
  configuration, after a prefix that applies the rows (none on the CTM proxy) and leaves the
  holder reads alone: at `d9f678900` this passes every check for every hash, the hashed tuples
  are equal word for word, and afterwards `X`, not the executor's `ProxyAdmin`, administers the
  CTM proxy; at `b17415d20` the same engine reverts or its compared pair collides. The comment
  at `:72-74`, added with the check in `9775be946` (#2669), describes this case.

### Model boundaries

- A revert is the absence of a result; events and `msg.value` are not modelled.
- Proxies are their two EIP-1967 slots. What an implementation answers (`owner`,
  `pendingOwner`, `admin`, `implementation`, `chainTypeManager`) is a per-proxy field of the
  world and does not depend on the caller; `owner`, `pendingOwner` and `chainTypeManager`
  always answer. `ChainTypeManager` and `ServerNotifier` declare no fallback, so selectors they
  lack revert.
- `keccak256(abi.encode(...))` is an arbitrary function of the word list; results that need
  distinct hashes carry a collision disjunct on the leg's own word lists.
- The engine is an arbitrary function of the executor's address, the context, the manifest's
  slots and the world. The named engines use `setPendingAdmin`, `acceptAdmin`,
  `upgradeAndCall` (re-installing the live implementation), `changeProxyAdmin` and `upgradeTo`.
- Not modelled: `forward`, the rows' own implementation swaps (see `../ProxyUpgradeRowLib/`),
  the executor's other entry points.
- `MODEL-DOMAIN-HOLDERS-V35` in the [assumption register](../../../ASSUMPTIONS.md).
