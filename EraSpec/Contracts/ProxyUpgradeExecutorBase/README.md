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
Both domain executors (`CoreUpgradeExecutor.applyL1Upgrade`,
`CTMUpgradeExecutor.applyInfrastructureUpgrade`) apply a `ProxyUpgradeTransition` through
`_applyProxyUpgradeTransition`, which delegatecalls the engine the transition pins and then
checks what the engine did.

| Topic | Source commit | Namespace | Specification | Property statements | Checked proofs |
|---|---|---|---|---|---|
| CoreLegV35 | `b17415d20` (2026-11-16) | `Contracts.ProxyUpgradeExecutorV35.CoreLeg` | [Specs/CoreLegV35.lean](Specs/CoreLegV35.lean) | [Properties/CoreLegV35.lean](Properties/CoreLegV35.lean) | [Proofs/CoreLegV35.lean](Proofs/CoreLegV35.lean) |
| DomainHoldersV35 | `b17415d20` (2026-11-16); the `d9f678900` leg kept as `D9.leg` | `Contracts.DomainHoldersV35` | [Specs/DomainHoldersV35.lean](Specs/DomainHoldersV35.lean) | [Properties/DomainHoldersV35.lean](Properties/DomainHoldersV35.lean) | [Proofs/DomainHoldersV35.lean](Proofs/DomainHoldersV35.lean) |
| EngineLegV35 | `b17415d20` (first written at `d9f6789`) | `Contracts.EngineLegV35` | [Specs/EngineLegV35.lean](Specs/EngineLegV35.lean) | [Properties/EngineLegV35.lean](Properties/EngineLegV35.lean) | [Proofs/EngineLegV35.lean](Proofs/EngineLegV35.lean) |
| ExecutorOwnerCallsV35 | `b17415d20` (2026-11-16) | `Contracts.ExecutorOwnerCallsV35` | [Specs/ExecutorOwnerCallsV35.lean](Specs/ExecutorOwnerCallsV35.lean) | [Properties/ExecutorOwnerCallsV35.lean](Properties/ExecutorOwnerCallsV35.lean) | [Proofs/ExecutorOwnerCallsV35.lean](Proofs/ExecutorOwnerCallsV35.lean) |
| NotifierBindingV35 | `b17415d20` (2026-11-16) | `Contracts.NotifierBindingV35` | [Specs/NotifierBindingV35.lean](Specs/NotifierBindingV35.lean) | [Properties/NotifierBindingV35.lean](Properties/NotifierBindingV35.lean) | [Proofs/NotifierBindingV35.lean](Proofs/NotifierBindingV35.lean) |

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

## The engine leg (topic EngineLegV35)

The leg is modelled for every engine (an arbitrary relation choosing the executor's storage at
return and the calls it sends) and every world (arbitrary getters), with `keccak256` an
arbitrary function. A successful leg:

- ran the engine the manifest names, with the context built from the executor's bindings, after
  the checks before the engine passed (`LegRunsThePinnedEngine`);
- left the executor's owner and pending owner alone, so only undeclared executor storage can
  change (`LegKeepsExecutorOwnership`, `LegChangesOnlyUndeclaredExecutorStorage`);
- left the domain's holder tuple alone, or two compared `abi.encode` preimages collide
  (`LegKeepsDomainHoldersOrCollides`, getter by getter in
  `LegKeepsNamedHoldersUnlessCollision`). The tuple is the `ProxyAdmin`'s owner, and with a CTM
  the CTM's owner, pending owner, `admin()`, proxy admin and ServerNotifier, and that
  notifier's owner, pending owner, proxy admin and CTM, the notifier being read in each world;
- where `getProxyAdmin(ctm)` falls through to the CTM's `admin()` role once the `ProxyAdmin` no
  longer administers the CTM proxy (`AdminFallsThrough`), kept the CTM proxy with the
  `ProxyAdmin`, unless a compared preimage collides
  (`LegKeepsCtmProxyAdministeredUnlessCollision`);
- landed every row (`LegLandsEveryRow`, `LegLandsEveryActiveSlot`).

In a concrete world, `DefaultProxyUpgradeEngine` is the `e561b9cc2` `applyTransition` plus four
requirements (`DefaultEngineLegIsApplyTransition`; witnesses `DefaultEngineLegWitness`,
`DefaultEngineCoreLegWitness`; `UnownedAdminReplayNowReverts`). Each of the six checks is
load-bearing: `OwnerSlotWriteIsCaught`, `CtmNominationIsCaught`, `NotifierRepointIsCaught`,
`RowMovedBackIsCaught`, `AliasedCtmMoveIsCaughtByTheAdminCheck`, the codeless-engine results
(`CodelessEngineLegIff`, `CodelessEngineMovesNothing`, `CodelessEngineReplayIsCaught`,
`CodelessEngineEmptyTransitionIsCaught`) and `ForeignDomainManifestIsCaught`; the domain check
adds nothing for a manifest of its own domain's length
(`DomainCheckRedundantAtConstructorLength`). Boundaries: the collision disjunct is needed
(`HoldersCollisionIsNeeded`), and proxies no row names and undeclared executor storage are not
checked (`UnlistedProxyMovePassesEveryCheck`, `UndeclaredSlotWritePassesEveryCheck`), as the
source says (`ProxyUpgradeExecutorBase.sol:40-41`).

### What to check

- The model was re-pinned from `d9f6789` to `b17415d20`. Between them `_domainHolders` began
  reading the ServerNotifier itself and hashing its address, the CTM's `admin()` and the
  notifier's CTM, and `_applyProxyUpgradeTransition` gained the CTM-admin check (`:72-77`). The
  spec's last section lists the diff.
- `AdminFallsThrough` is a premise, not a theorem: it describes OpenZeppelin v4's transparent
  proxy and a CTM implementation whose `admin()` getter does not depend on the caller. The
  OpenZeppelin submodule was not available at the pin, so its lines are not cited.
- `DefaultEngineLegIsApplyTransition` holds in the concrete world from states where the
  `ProxyAdmin` administers every proxy, as `applyRows` assumes of its bound admin.

### Model boundaries

`MODEL-ENGINE-LEG` in the [assumption register](../../../ASSUMPTIONS.md). A revert is the
absence of a step; the entry points' `onlyOwner` is not modelled; getters are total, so a
reverting getter only removes legs; events, the executor's ETH and the bubbled revert data are
not modelled. The concrete world has inert reinitializers and four call kinds.

## The executor's owner calls (topic ExecutorOwnerCallsV35)

Source: the CTM-domain executor (`executors/CTMUpgradeExecutor.sol`) and the `forward` it
inherits (`governance/UpgradeExecutorBase.sol`), besides `ProxyUpgradeExecutorBase.sol`. The
topic was first written against commit `d9f6789` and is pinned to **`b17415d20`**; its Specs
header lists what changed in the modelled code between the two.

Which frames of the CTM executor make the CTM's owner calls, and what the executor logs for
them, now that `applyInfrastructureUpgrade` delegatecalls the engine its transition pins. A
frame is one successful invocation of an executor entry point; its trace is what that
invocation's own code did, the engine included. The CTM's commit and replacement are
`../ChainTypeManager/` `VersionRegistry`'s `CStep`, unchanged at this commit.

What to check:

- `EntryFixesOwnerCallsAndLog`: in every frame, the CTM owner calls and the executor's log are
  read off the entry. A `forward` logs one `CallForwarded` per listed call, in order; an
  infrastructure leg makes exactly its engine's CTM calls and logs the engine's own logs, then
  `CTMInfrastructureUpgradeApplied`.
- `OwnerCallOrigins`: every owner call comes from `applyCTMUpgrade`, `upgradeChain` (the
  executor's owner or that chain's admin), a `forward`, or the pinned engine of an
  infrastructure leg. `OwnerCallOriginsEachOccur` realizes all four.
- `OwnerCallsOutsideEngineLegsAreLogged`: outside legs whose engine calls the CTM, the
  executor's log names every owner call. `EngineOwnerCallsNotLoggedByExecutor` and
  `EngineLegReplacesAndMovesDeadlineWithoutForward`: a leg whose engine replaces a committed
  transition and moves a deadline succeeds, and its log names neither call
  (`docs/registry-driven-upgrades.md:473-478` describes this route).
- `EngineLegKeepsHoldersOrCollides`, with `HoldersViewUnchangedIff`: a leg keeps the
  executor's ownership, its rows, and every holder the post-check reads, unless the holders
  hash collides on the leg's own two lists. The disjunction is the post-check split by cases;
  its content is which holders the list covers. `EngineNominationRefusedOnlyByHoldersHash`:
  a hash that reads the pending owner refuses an engine's nomination of a CTM owner, one that
  reads nothing lets it through; `ForwardNominatesCtmOwner`: through `forward` it passes for
  every hash. `EngineLegNominatesCtmAdmin`: the CTM's `pendingAdmin` is not among the holders,
  as `ProxyUpgradeExecutorBase.sol:114-116` states.
- `TameFramesKeepTheVersionInvariant`: a frame with no call or act whose effect the model
  leaves arbitrary keeps `CtmInv` and never lowers `protocolVersion`, whichever route carries
  the commits and replacements. `VersionInvariantPremisesMetAndNeeded`: the witness leg meets
  the premises, and one arbitrary engine act can break `CtmInv` while keeping every holder.

Model boundaries (details in the Specs header): a CTM owner call is a call whose owner gate
passes because the executor owns the CTM, and only `FwdCall.ctm` and `EngAct.ctm` are such
calls; every other forwarded call and engine act has an arbitrary effect. The CTM runs
`ChainTypeManager.sol` at this commit: a swap of the CTM's or the ServerNotifier's code is an
arbitrary-effect call or act, and so is every later call to a swapped CTM. Which act lists a
given engine contract can produce is not modelled, nor is governance's approval of a
transition. The holders hash `H` is an arbitrary function of the list `_domainHolders` reads,
and no statement assumes anything about it. Reverts are the absence of a frame; reject-only
checks that read nothing modelled are omitted. `value`, ETH, the OpenZeppelin ownership events,
the chains, and re-entrant frames inside a frame's calls (each is its own frame) are not part of
a trace.

## The ServerNotifier binding (topic NotifierBindingV35)

Source: besides `ProxyUpgradeExecutorBase.sol` (the check a domain executor makes around the
engine it delegatecalls), the contracts whose state that check reads:
`state-transition/ChainTypeManager.sol`, `governance/ServerNotifier.sol` and
`upgrades/registry/libraries/RegistryAuthorityLib.sol`, at **`b17415d20`**; the results describe
that commit only. `_domainHolders` changed in `9775be946`, between `d9f6789` and `b17415d20`;
the model does not describe `d9f6789`.

A chain's validators may upgrade it once the chain's entry in the ServerNotifier the CTM points
at is set and reached (`Admin.sol:577-585`). Who may write that entry is decided by two
pointers: the CTM's `serverNotifierAddress` and the notifier's `chainTypeManager`, which names
every chain's admin. `RegistryAuthorityLib.requireNotifierHandedOver` checks both, and the
notifier's ownership, when the bootstrap runs. The CTM executor owns the CTM, its `ProxyAdmin`
and the notifier, and lends that authority to the engine of every infrastructure transition.
The NatSpec (`ProxyUpgradeExecutorBase.sol:34-41`) says what the executor compares afterwards,
and that a re-pointed ServerNotifier is a `forward`, not a leg.

### What to check

- **What the comparison reads.** `PostCheckComparesExactly`: with the reading before the engine
  defined, the comparison of the tuples passes exactly when the `ProxyAdmin`'s owner, the CTM's
  owner, pending owner, `admin()` and `getProxyAdmin` reading, the CTM's notifier pointer and,
  for a nonzero notifier, `pa`'s administration of it and its owner, pending owner and
  `chainTypeManager` are unchanged; otherwise a hash passes only by colliding on the two
  readings. `DomainHoldersReadOnly`: nothing else is read, in particular not the CTM's
  `pendingAdmin` or any notifier's schedule or checkers.
- **Both pointers are compared.** `PostCheckRejectsRepoint`, `PostCheckRejectsRebind`;
  `EngineRepointAndRebindRejected` shows one-call legs of each kind that succeed as calls and
  are rejected.
- **Headline: an accepted leg keeps the registry shape.** `AcceptedLegKeepsShape`: from the
  shape (`requireNotifierHandedOver`, the CTM and `ProxyAdmin` owned by the executor with no
  nomination, `pa` administering both proxies), every leg accepted with the comparison of the
  tuples ends in the shape, whatever its calls. For an arbitrary hash
  (`AcceptedLegKeepsShapeOrCollision`) the alternative is a collision on the leg's two readings;
  for the source's two `keccak256` calls (`AcceptedLegKeepsShapeOrKeccakCollision`, via
  `DomainHashCollisionIsKeccakCollision`) it is a keccak collision on two named, distinct
  preimages. `AcceptedLegWitness` is an accepted leg that changes the state (a notifier
  checker and a CTM admin nomination, neither of which the comparison reads).
- **The check before the engine is load-bearing.** `PreCheckIsLoadBearing`: without it, a leg
  that moves the CTM proxy to another admin passes the comparison when the CTM's `admin` role
  is the `ProxyAdmin` (the case `ProxyUpgradeExecutorBase.sol:72-74` describes).
- **Along runs.** `ShapeKeptAlongDomainRuns`: from the shape, every run of calls by anyone but
  the executor and the zero address, accepted engine legs and the executor's
  `acceptCTMOwnership` ends in the shape (`ShapeKeptAlongDomainRunsOrCollision` for an
  arbitrary hash, with the collision on one of the run's own legs). `ShapeKeptByOtherCallers`
  is the part without legs. `DomainRunWitness` fires it with a chain admin's call and a leg.
  **Countermodel** `CallsOutsideLegsMoveTheBinding`: a call the executor sends outside a leg,
  as `forward` does, re-points the CTM or re-binds the notifier; afterwards a contract other
  than the diamond's admin schedules the chain and opens its validator gate.
- **Writers.** `NotifierEntryWritersV35` (an entry changes only by its chain admin, as the
  notifier's CTM names it, or by a code swap), `NotifierBindingWritersV35` (the two pointers),
  `LiveEntryWritersV35` (the entry the diamond reads), `BindingMovedOnlyByItsHolders`.
- **Under the binding.** `BoundNotifierAdminIsDiamondAdmin`, `BoundStepRefinesUpgradeTiming`
  (a scheduling step on the bound notifier is a `TimedStep.setUpgradeTimestamp` of
  `../ChainTypeManager/Specs/UpgradeTiming.lean`), `BoundLiveEntryWrittenOnlyByItsChainAdmin`,
  `BoundLiveEntryWritersV35` (in the shape, a live entry changes only by the diamond's admin or
  by the executor). `OnlyDiamondAdminSchedulesAlongDomainRuns` composes the last with the run
  result: after any `DomainRun` from the shape, a call by anyone but the executor that changes
  a live entry is the diamond's admin scheduling its chain (`OnlyDiamondAdminSchedulesWitness`).
  Both premises are load-bearing (`BoundRefinementPremisesAreLoadBearing`) and hold together
  (`BoundPremisesSatisfiable`). `UpgradeTiming` is pinned at `e561b9cc2`; these results relate
  the two models, not the two commits.

### Model boundaries

- A revert is the absence of a step. What other contracts answer (`getChainAdmin`,
  `getProtocolVersion`, whether a version is scheduled, whether a checker accepts) is fixed
  configuration, `Env`. `CtmAnswersDiamondAdmin` (the real CTM's `getChainAdmin` is the
  diamond's `s.admin`) is a premise where used (`MODEL-NOTIFIER-BINDING` in `ASSUMPTIONS.md`).
- Every address has ServerNotifier-shaped proxy storage; after a code swap a proxy is read as
  running its contract's code on the storage the swap leaves.
- `getProxyAdmin` is modelled with OpenZeppelin v4's forwarding: it answers the `ProxyAdmin`
  when that administers the proxy, the CTM's `admin` role otherwise, and reverts for a
  notifier. Calls a proxy's own admin makes to non-admin functions, and getters on addresses
  without code, revert in the source but not in the model; that only adds accepted legs.
- The executor's own-ownership check and row check, and the reject-only checks before the
  engine, are left out of `LegAccepted`, which admits at least the legs the source admits.
- Not steps: `ServerNotifier.initialize` (every notifier store is read as initialised), and
  events. The executor's `applyCTMUpgrade` and `upgradeChain` write no field of the state and
  are not `DomainEvent`s. `DomainRun` leaves out `forward`, whose calls are `Step`s by the
  executor (`CallsOutsideLegsMoveTheBinding`).
