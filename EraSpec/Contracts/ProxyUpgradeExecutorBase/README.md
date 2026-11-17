# ProxyUpgradeExecutorBase

Source: `l1-contracts/contracts/upgrades/registry/executors/ProxyUpgradeExecutorBase.sol` in
era-contracts, branch `draft/v0.35.0`. Both domain executors
(`CoreUpgradeExecutor.applyL1Upgrade`, `CTMUpgradeExecutor.applyInfrastructureUpgrade`) apply a
`ProxyUpgradeTransition` through `_applyProxyUpgradeTransition`, which delegatecalls the
engine the transition pins and then checks what the engine did.

| Topic | Source commit | Namespace | Specification | Property statements | Checked proofs |
|---|---|---|---|---|---|
| EngineLegV35 | `b17415d20` (first written at `d9f6789`) | `Contracts.EngineLegV35` | [Specs/EngineLegV35.lean](Specs/EngineLegV35.lean) | [Properties/EngineLegV35.lean](Properties/EngineLegV35.lean) | [Proofs/EngineLegV35.lean](Proofs/EngineLegV35.lean) |

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions, plus auxiliary lemmas and countermodels. Statements are
`<namespace>.Properties.*`; each certificate has the same name without the `Properties`
segment.

## EngineLegV35

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

## What to check

- The model was re-pinned from `d9f6789` to `b17415d20`. Between them `_domainHolders` began
  reading the ServerNotifier itself and hashing its address, the CTM's `admin()` and the
  notifier's CTM, and `_applyProxyUpgradeTransition` gained the CTM-admin check (`:72-77`). The
  spec's last section lists the diff.
- `AdminFallsThrough` is a premise, not a theorem: it describes OpenZeppelin v4's transparent
  proxy and a CTM implementation whose `admin()` getter does not depend on the caller. The
  OpenZeppelin submodule was not available at the pin, so its lines are not cited.
- `DefaultEngineLegIsApplyTransition` holds in the concrete world from states where the
  `ProxyAdmin` administers every proxy, as `applyRows` assumes of its bound admin.

## Model boundaries

`MODEL-ENGINE-LEG` in the [assumption register](../../../ASSUMPTIONS.md). A revert is the
absence of a step; the entry points' `onlyOwner` is not modelled; getters are total, so a
reverting getter only removes legs; events, the executor's ETH and the bubbled revert data are
not modelled. The concrete world has inert reinitializers and four call kinds.
