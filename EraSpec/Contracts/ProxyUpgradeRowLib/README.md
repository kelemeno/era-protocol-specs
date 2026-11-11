# ProxyUpgradeRowLib

Source: `l1-contracts/contracts/upgrades/registry/libraries/ProxyUpgradeRowLib.sol`
in the registry-driven upgrade system. That code is **not** in the pinned
era-contracts tree. It lives on branch `feat/upgrade-simplification` of the zksync-era
`contracts` repository. The branch was called `claude/musing-clarke-8b5f2c`
when the first model was written, and that model's original commit cites that name.

The branch moves, so each model here is a snapshot. This folder has two:

| Topic | Source commit | Namespace | Specification | Property statements | Checked proofs |
|---|---|---|---|---|---|
| Rows | `612a71ccc` (2026-09-22) | `Contracts.ProxyUpgrade` | [Specs/Rows.lean](Specs/Rows.lean) | [Properties/Rows.lean](Properties/Rows.lean) | [Proofs/Rows.lean](Proofs/Rows.lean) |
| RowsCurrent | `e561b9cc2` (2026-10-19) | `Contracts.ProxyUpgradeCurrent` | [Specs/RowsCurrent.lean](Specs/RowsCurrent.lean) | [Properties/RowsCurrent.lean](Properties/RowsCurrent.lean) | [Proofs/RowsCurrent.lean](Proofs/RowsCurrent.lean) |

`Rows` is kept unchanged. Its header and commit cite no source commit; the library it
describes was last changed at `ae0698588` (2026-09-16), and a later check found it
unchanged at `612a71cccb65d6db97674997b21427a50bec6206`. `RowsCurrent` is pinned to
`e561b9cc2`, the commit `../ChainTypeManager/` and `../RegistryBootstrapMigration/` use.
Re-check the source before relying on either.

Review `Specs/` for state, operations, and assumptions; review `Properties/` for the
guarantees and their hypotheses. `Proofs/` contains the Lean-checked evidence for those exact
named propositions, plus auxiliary lemmas and countermodels. Statements are
`<namespace>.Properties.*`; each certificate has the same name without the `Properties`
segment.

## What changed in the library between the two pins

`git diff 612a71ccc e561b9cc2 -- l1-contracts/contracts/upgrades/registry/libraries/ProxyUpgradeRowLib.sol`:

- `ProxyUpgradeRow` lost its `admin` field. `adminOf`, the foreign-admin skip and the
  `ProxyRowLeftToAdministrator` event are gone. Every row goes through the applier's bound
  `ProxyAdmin`.
- `requireRowsApplied` is gone. `applyRows` ends with the same check as a second loop over
  the rows (`:142-147`), in the same call.
- `applyRows` starts with `requireRowCode` (every `implNew` is code).
- `validateRows` refuses a self-edge, `expectedOldImpl == implNew` (`:78-80`).
- `applyTransition` (`:102-113`) checks the transition object's code and domain, then
  applies its `rows()`.

## Status of the `612a71ccc` properties at `e561b9cc2`

| `Rows` (612a71ccc) | `RowsCurrent` (e561b9cc2) | What changed |
|---|---|---|
| `OnlyTheNamedEdge` | holds, `OnlyTheNamedEdge` | new premise `RowInert`: the reinitializer is now modelled (the old model made it inert by construction) |
| `StaleObjectCannotDowngrade` | holds, same name | foreign-admin premise gone; no premise |
| `StaleObjectReverts` | holds, same name | as above |
| `ApplyRowsDeterministic` | holds, same name | none |
| `ApplyRowsIdempotent` | holds, same name | **distinct-proxies premise dropped** (the in-call verification makes every row skip on a re-run) |
| `UnmovedProxiesFrame` | holds, same name | frame for proxies no row names; needs `ReinitFrames` (countermodel `ReinitLeakIsNotCaught`) |
| `ApplyRowsPostcondition` | holds, same name | **no premise** (was: distinct proxies and no foreign-admin row) |
| `AppliedGatePasses` | holds, same name | `ValidRows` and foreign-admin premises dropped; the frame hypothesis stays. The library no longer has a later-transaction gate. |
| `OrderIndependent` | holds, same name | distinct-proxies premise dropped; needs `ReinitFrames` (countermodel `ReinitMakesOrderMatter`). `OrderIndependentOnRowProxies` holds with no premise. |
| `DuplicateRowsBreakPostcondition` | **no longer holds** | the same pair now reverts: `DuplicateRowsNowRevert`, generally `TwoTargetsForOneProxyRevert` |
| `DuplicateRowsBreakOrder` | **still holds**, same name, new witness | rows `5: 10 → 11` and `5: 12 → 11`: one order applies, the other reverts |
| `DuplicateRowsBreakIdempotence` | **no longer holds** | `ApplyRowsIdempotent` has no premise; the old witness's first run now reverts (`DuplicateRowsNowRevert`) |
| `ForeignRowLeavesGateOpen` | **no longer expressible** | rows have no `admin`; the gap it showed is closed by `ApplyRowsPostcondition`. `UnownedAdminMovesNothing` is the remaining ownership fact. |
| `ToRowsKeepsActiveSlots` | holds, same name | none |
| `InertSlotNeverUpgraded` | holds, same name | needs `ReinitFrames` |

New at `e561b9cc2`:

- `OnlyNamedEdgesAcrossCall`: replay safety for a whole call. For rows naming distinct
  proxies and reinitializers that move at most their own proxy, every proxy that moved went
  from some row's `expectedOldImpl` to that row's `implNew`.
- `ValidSourceIsNotApplied` and `SelfEdgeAppliesWithoutMoving`: what the self-edge check
  does. Under the current `validateRows`, a state with a row's proxy at its source fails the
  verification, so a successful call from it moves the proxy. A self-edge row passed the old
  checks, and from its source it "applies" without moving anything.
- `ReinitMovingOwnProxyIsCaught`: the verification catches a reinitializer that moves its own
  proxy, as the source's `@dev` (`:119-120`) says.
- `UnownedAdminMovesNothing`, `WrongDomainTransitionReverts`, `CurrentRowsWitness`.

## What to check

- `ApplyRowsPostcondition` is now a field of the model (`ApplyRows.verified`), because
  the source checks it in-call. The content is in what it removes: no duplicate or foreign
  premise is needed for the gate any more.
- The duplicate check in `validateRows` is still load-bearing for order independence of
  *executability* (`DuplicateRowsBreakOrder`), not for the post-state.
- The reinitializer premise `ReinitFrames` is a model assumption about code: a
  reinitializer runs in its own proxy's storage, and moving another proxy needs authority
  over it. `ReinitLeakIsNotCaught` and `ReinitMakesOrderMatter` use reinitializers that
  break it. The source's claim covers only the row set ("a reinitializer that moves any
  proxy of the row set is caught too"), and the countermodels agree.
- `applyTransition` checks the object's code and `domain()`, not its rows. `validateRows`
  runs in `ProxyUpgradeTransition`'s constructor (`objects/ProxyUpgradeTransition.sol:36`).
  A different contract answering `domain()` and `rows()` gets its rows applied
  unvalidated. The results that need `ValidRows` or distinct proxies (`ValidSourceIsNotApplied`,
  `OnlyNamedEdgesAcrossCall`) assume a genuine object.

## Model boundaries

`MODEL-ROWS` in the [assumption register](../../../ASSUMPTIONS.md) describes the `612a71ccc`
model. For `RowsCurrent`: a revert is the absence of a step; the live implementation is one
mapping read through the bound admin (a proxy the admin does not administer is outside the
model); the reinitializer's effect on the mapping is an arbitrary deterministic function of
the row and the mapping, and its other effects are not modelled; code existence is a
predicate; events have no effect; `toRows`' length check is the caller's side condition.
