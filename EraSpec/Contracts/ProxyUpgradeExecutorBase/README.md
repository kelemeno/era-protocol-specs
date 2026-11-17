# ProxyUpgradeExecutorBase

Source: `l1-contracts/contracts/upgrades/registry/executors/ProxyUpgradeExecutorBase.sol`, the
base of both registry-driven domain executors (`CTMUpgradeExecutor`, `CoreUpgradeExecutor`), on
era-contracts branch `draft/v0.35.0`. **The branch moves**: each topic names the commit its
`file:line`s are at.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions. Statements are `<namespace>.Properties.*`; each certificate has the same
name without the `Properties` segment.

| Topic | Source commit | Namespace | Specification | Property statements | Checked proofs |
|---|---|---|---|---|---|
| DomainHoldersV35 | `b17415d20` (2026-11-16); the `d9f678900` leg kept as `D9.leg` | `Contracts.DomainHoldersV35` | [Specs/DomainHoldersV35.lean](Specs/DomainHoldersV35.lean) | [Properties/DomainHoldersV35.lean](Properties/DomainHoldersV35.lean) | [Proofs/DomainHoldersV35.lean](Proofs/DomainHoldersV35.lean) |

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

## What to check

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

## Model boundaries

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
