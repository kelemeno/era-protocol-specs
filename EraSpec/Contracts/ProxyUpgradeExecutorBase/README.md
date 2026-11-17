# ProxyUpgradeExecutorBase

Source: `l1-contracts/contracts/upgrades/registry/executors/ProxyUpgradeExecutorBase.sol` (the
check a domain executor makes around the engine it delegatecalls), with the contracts whose
state that check reads: `state-transition/ChainTypeManager.sol`, `governance/ServerNotifier.sol`
and `upgrades/registry/libraries/RegistryAuthorityLib.sol`.

That code is **not** in the pinned era-contracts tree. It lives on branch `draft/v0.35.0` of
era-contracts, and the topic below was written against commit **`b17415d20`**
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, 2026-11-16). **The branch moves**: every
`file:line` quoted in the spec is at that commit, and the results describe that commit only.
`_domainHolders` changed in `9775be946`, between `d9f6789` and `b17415d20`; the model does not
describe `d9f6789`.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions.

| Topic | Specification | Property statements | Checked proofs |
|---|---|---|---|
| NotifierBindingV35 | [Specs/NotifierBindingV35.lean](Specs/NotifierBindingV35.lean) | [Properties/NotifierBindingV35.lean](Properties/NotifierBindingV35.lean) | [Proofs/NotifierBindingV35.lean](Proofs/NotifierBindingV35.lean) |

Namespace: `Contracts.NotifierBindingV35`. Statements are
`Contracts.NotifierBindingV35.Properties.*`; each certificate has the same name without the
`Properties` segment.

## The ServerNotifier binding (topic NotifierBindingV35)

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
