# ProxyUpgradeRowLib

## Headline guarantees

About `l1-contracts/contracts/upgrades/registry/libraries/ProxyUpgradeRowLib.sol` at
era-contracts `draft/v0.35.0` commit `b17415d20`, model `Contracts.ProxyUpgradeCurrent`
(`MODEL-ROWS`: a revert is the absence of a step, the live implementation is one mapping read
through the bound `ProxyAdmin`, a reinitializer's effect on it is an arbitrary function).

- `Contracts.ProxyUpgradeCurrent.Properties.ApplyRowsPostcondition`: after a successful
  `applyRows`, every row's proxy is at its `implNew`. No premise.
- `Contracts.ProxyUpgradeCurrent.Properties.StaleObjectCannotDowngrade`: a row whose proxy is
  neither at its `expectedOldImpl` nor at its `implNew` reverts. No premise.
- `Contracts.ProxyUpgradeCurrent.Properties.ApplyRowsIdempotent`: applying the same rows again
  after a successful call succeeds and changes nothing. No premise.
- `Contracts.ProxyUpgradeCurrent.Properties.OnlyNamedEdgesAcrossCallAnyRows`: premise: every
  reinitializer moves at most its own proxy (`ReinitFrames`). Then in a successful call over
  any rows (validated or not, duplicates included) every proxy either did not move or went
  from some row's `expectedOldImpl` to that row's `implNew`.
- `Contracts.ProxyUpgradeCurrent.AdminSlot.Properties.OnlyNamedEdgesAcrossCallOnSlots`: the
  same on each proxy's two ERC-1967 slots through the OpenZeppelin transparent proxy's admin
  dispatch; premises: reinitializers write only their own proxy's slots (`SelfOnly`), leave
  its admin slot alone (`KeepsAdmin`), and the `ProxyAdmin` administers every row's proxy when
  the call starts (`Administered`). The admin slots are unchanged too.

Witnesses: `CurrentRowsWitness`, `AnyRowsWitness`, `AdminSlotWitness`. Countermodels:
`ReinitLeakIsNotCaught`, `DuplicateRowHidesReinitMove`, `AdminRewritePassesVerification`,
`UnadministeredRowSkippedWhileOffTarget`.

## Source and layout

One model, `RowsCurrent`, pinned to **`b17415d20`** (`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`),
and its refinement `RowsAdminSlot` (with OpenZeppelin v4.9.6 at `dc44c9f`). The other current
topics add predicates and witness data over `RowsCurrent` only. `History/` keeps the record of
the earlier snapshot `612a71ccc`; it is not a claim about `b17415d20`.

| Topic | Namespace | Specification | Property statements | Checked proofs |
|---|---|---|---|---|
| RowsCurrent | `Contracts.ProxyUpgradeCurrent` | [Specs/RowsCurrent.lean](Specs/RowsCurrent.lean) | [Properties/RowsCurrent.lean](Properties/RowsCurrent.lean) | [Proofs/RowsCurrent.lean](Proofs/RowsCurrent.lean) |
| RowsUnvalidated | `Contracts.ProxyUpgradeCurrent` | [Specs/RowsUnvalidated.lean](Specs/RowsUnvalidated.lean) | [Properties/RowsUnvalidated.lean](Properties/RowsUnvalidated.lean) | [Proofs/RowsUnvalidated.lean](Proofs/RowsUnvalidated.lean) |
| RowsOrder | `Contracts.ProxyUpgradeCurrent` | [Specs/RowsOrder.lean](Specs/RowsOrder.lean) | [Properties/RowsOrder.lean](Properties/RowsOrder.lean) | [Proofs/RowsOrder.lean](Proofs/RowsOrder.lean) |
| RowsCurrentStrong | `Contracts.ProxyUpgradeCurrent` | [Specs/RowsCurrentStrong.lean](Specs/RowsCurrentStrong.lean) | [Properties/RowsCurrentStrong.lean](Properties/RowsCurrentStrong.lean) | [Proofs/RowsCurrentStrong.lean](Proofs/RowsCurrentStrong.lean) |
| RowsAdminSlot | `Contracts.ProxyUpgradeCurrent.AdminSlot` | [Specs/RowsAdminSlot.lean](Specs/RowsAdminSlot.lean) | [Properties/RowsAdminSlot.lean](Properties/RowsAdminSlot.lean) | [Proofs/RowsAdminSlot.lean](Proofs/RowsAdminSlot.lean) |
| History: Rows (`612a71ccc`) | `Contracts.ProxyUpgrade.History` | [History/Specs/Rows.lean](History/Specs/Rows.lean) | [History/Properties/Rows.lean](History/Properties/Rows.lean) | [History/Proofs/Rows.lean](History/Proofs/Rows.lean) |
| History: RowsStrong (`612a71ccc`) | `Contracts.ProxyUpgrade.History` | [History/Specs/RowsStrong.lean](History/Specs/RowsStrong.lean) | [History/Properties/RowsStrong.lean](History/Properties/RowsStrong.lean) | [History/Proofs/RowsStrong.lean](History/Proofs/RowsStrong.lean) |

At `b17415d20` `applyRows` (`:106-128`) reads and swaps as it did at `e561b9cc2`, where
`RowsCurrent` was first written; its verification pass is now the function
`requireRowsApplied` (`:133-141`), which the executors call again after their engine
(`executors/ProxyUpgradeExecutorBase.sol:103`). `applyTransition` is gone: `ApplyTransition`
is now the leg's object checks (`ProxyUpgradeExecutorBase.sol:57-61`) followed by the default
engine's `applyRows` (`engines/DefaultProxyUpgradeEngine.sol:41-44`). Statements are
`<namespace>.Properties.*`; each certificate has the same name without the `Properties`
segment.

## When a call succeeds, and in which orders

The base files say what a *successful* `applyRows` establishes, and `OrderIndependent`
compares two successful calls. These topics say when a call succeeds at all, and whether a
permutation of a successful call succeeds.

- History `RowsStrong` (`612a71ccc`): `RowStepIffEnabled`: one loop iteration succeeds exactly when
  the row is `RowEnabled` (left to a foreign administrator, already at its target, or owned
  and at its source). `ApplyRowsEnabledIff`: on rows naming distinct proxies, and with
  reinitializers inert as the `612a71ccc` model assumes (the Solidity also calls
  `upgradeAndCall(initializeUpgrade)`, `ProxyUpgradeRowLib.sol:137-139`), `applyRows`
  succeeds iff every row is enabled in the starting state. `ApplyRowsPassesGateWhenEnabled`
  is the liveness companion of `ApplyRowsPostcondition` and `AppliedGatePasses`.
  `OrderIndependentExecutability`: on distinct proxies, with reinitializers inert as above, a
  permutation of a successful run is a successful run to the same state. `RowsStrongWitness`: two owned rows on distinct proxies
  apply in both orders; a stale row makes the call revert.
- `RowsOrder`: validation and `ReinitFrames` do not make executability
  order-independent (`ReinitReadBreaksOrder`, a reinitializer that reads another proxy);
  `ReinitFrames` with `ReinitReadsOwnProxy` does (`DistinctRowsApplyInAnyOrder`), and each
  premise is needed (`ReinitLeakBreaksOrder`, `DuplicateRowsBreakOrder`).
- `RowsCurrentStrong`: `ApplyRowsEnabledIff`: for rows on distinct proxies whose
  swaps are local (`LocalSwap`: the swap, reinitializer included, sets the row's proxy to one
  fixed implementation and nothing else), `applyRows` succeeds iff `requireRowCode` passes and
  every row applies on its own from the starting state (`RowApplies`).
  `OrderIndependentExecutability` follows, with a premise on the call's rows only; the
  configuration-wide premises of `DistinctRowsApplyInAnyOrder` give it
  (`LocalSwapOfFramesAndReadsOwn`), and so do inert rows (`LocalSwapOfInert`,
  `OrderIndependentExecutabilityInert`) and own-proxy reinitializers
  (`LocalSwapOfOwnProxyReinit`). `ReinitReadIsNotLocalSwap`: the countermodel of
  `ReinitReadBreaksOrder` is a swap that is not local, and it reverts at the verification
  pass after the first loop succeeded. `RowsCurrentStrongWitness`: a local reinitializer that
  is not inert, valid rows applying in both orders under it, and a local swap that does not
  apply (`wSelfMoving`).

## The read through the proxy's admin dispatch (`RowsAdminSlot`)

`RowsCurrent` reads `_admin.getProxyImplementation(proxy)` as the implementation the proxy
runs, and its reinitializer changes only that one mapping. `RowsAdminSlot` (with the
OpenZeppelin v4.9.6 proxy code at `dc44c9f`) models what is behind the read: each proxy's
ERC-1967 implementation and admin slots, and the transparent proxy's dispatch, which answers
`implementation()`, `upgradeTo` and `upgradeToAndCall` itself only when the caller is its admin
and otherwise delegates them to its current implementation. A reinitializer runs in its proxy's
storage and can write both of that proxy's slots.

- `RowsCurrent` is a fragment of this model. Every `RowsCurrent` configuration, lifted, has
  exactly its `RowsCurrent` calls (`LiftedCallIsRowsCurrentCall`, no premise). Under
  `SelfOnly` (the slot reading of `ReinitFrames`), `KeepsAdmin` (a reinitializer leaves its
  proxy's admin slot alone) and `Administered` (`_admin` administers every row's proxy when the
  call starts), every call is the `RowsCurrent` call of its projection on the implementation
  slots (`ApplyRowsCorrespond`). The headlines restated on the slots follow:
  `ApplyRowsPostconditionOnSlots`, `OnlyNamedEdgesAcrossCallOnSlots`,
  `OnlyNamedEdgesAcrossTransitionOnSlots`, `ReinitMovesAreCaughtOnLastRowOnSlots`,
  `ReinitMovesAreCaughtOnDistinctRowsOnSlots`, `OrderIndependentOnSlots` (witness
  `AdminSlotWitness`).
- Each premise is needed. Without `KeepsAdmin`, a reinitializer that writes only its own
  proxy's slots can point the admin slot away from `_admin` and the implementation slot at code
  whose forwarded `implementation()` returns the row's target; the call then succeeds with the
  implementation slot on no row's edge, while the `RowsCurrent` projection of the call reverts
  (`AdminRewritePassesVerification`; also `AdminRewriteMakesOrderMatter` and
  `MoveBackWithAdminRewriteIsNotCaught`). Without `Administered`, a row is skipped while its
  proxy runs other code (`UnadministeredRowSkippedWhileOffTarget`). Without `SelfOnly`,
  `ReinitLeakIsNotCaught` carries over to the slots (`SelfOnlyIsNeededOnSlots`).
- Without `KeepsAdmin`, each `RowsCurrent` conclusion holds on the slots, or the proxy's admin
  slot no longer holds `_admin` and a row naming it called `initializeUpgrade()`:
  `AdministeredRowRunsItsTarget`, `AdminLostOnlyByOwnReinitializer`,
  `OnlyNamedEdgesOrAdminLost`, `ReinitMovesAreCaughtOrAdminLost`, `SourceIsNotAppliedOnSlots`
  (witness `AdminSlotCasesWitness`, in which every case occurs).

## What to check

- `ApplyRowsPostcondition` is now a field of the model (`ApplyRows.verified`), because
  the source checks it in-call. The content is in what it removes: no duplicate or foreign
  premise is needed for the gate any more.
- The duplicate check in `validateRows` is still load-bearing for order independence of
  *executability* (`DuplicateRowsBreakOrder`), not for the post-state.
- The reinitializer premise `ReinitFrames` is a model assumption about code: a
  reinitializer runs in its own proxy's storage, and moving another proxy needs authority
  over it. `ReinitLeakIsNotCaught`, `ReinitMakesOrderMatter` and
  `ReinitLeakMovesNamedProxyOffEdge` use reinitializers that break it. The source's claim
  ("a reinitializer that moves any proxy of the row set is caught too") is about the row set,
  so `ReinitLeakIsNotCaught` (an unnamed proxy) does not contradict it. It is proved for the
  last row per proxy (`ReinitMovesAreCaughtOnLastRow`), and it fails for a duplicate row
  (`DuplicateRowHidesReinitMove`) and, for a reinitializer with authority over another row's
  proxy, on valid rows (`ReinitLeakMovesNamedProxyOffEdge`).
- `RowsCurrent`'s mapping describes the implementation slots under `RowsAdminSlot`'s
  `SelfOnly`, `KeepsAdmin` and `Administered` (`ApplyRowsCorrespond`). `KeepsAdmin` and
  `Administered` are premises, not checks the library makes, and each is needed
  (`AdminRewritePassesVerification`, `UnadministeredRowSkippedWhileOffTarget`).
- The executor checks the object's code and domain, not its rows. `validateRows`
  runs in `ProxyUpgradeTransition`'s constructor (`objects/ProxyUpgradeTransition.sol:37`).
  A different contract answering `getManifest()` gets its rows applied unvalidated. Replay safety does not depend on validation: `OnlyNamedEdgesAcrossCallAnyRows`
  and `SourceIsNotAppliedAnyRows` (`RowsUnvalidated`) restate `OnlyNamedEdgesAcrossCall` and
  `ValidSourceIsNotApplied` for any rows. Validation is still needed for order-independent
  executability (`DuplicateRowsBreakOrder`), though not sufficient for it under `ReinitFrames`
  alone (`ReinitReadBreaksOrder`), and the `@dev` claim that the verification catches
  every reinitializer move of a row's proxy (`ReinitMovesAreCaughtOnDistinctRows`; refuted for
  a duplicate row by `DuplicateRowHidesReinitMove`).

## Model boundaries

`MODEL-ROWS` in the [assumption register](../../../ASSUMPTIONS.md). For `RowsCurrent`: a revert is the absence of a step; the live implementation is one
mapping read through the bound admin (a proxy the admin does not administer is outside the
model); the reinitializer's effect on the mapping is an arbitrary deterministic function of
the row and the mapping, and its other effects are not modelled; code existence is a
predicate; events have no effect; `toRows`' length check is the caller's side condition.

`RowsAdminSlot` models the read through the bound admin: each row's proxy is an OpenZeppelin
v4.9.6 `TransparentUpgradeableProxy` with an implementation slot and an admin slot, and
`_admin` is an OpenZeppelin `ProxyAdmin`. Reads and swaps go through the proxy's admin dispatch,
and what forwarded code answers or does is an arbitrary deterministic function of the slots.
Storage other than the two slots, `changeProxyAdmin`, and the executors and engines are not
modelled here (`../ProxyUpgradeExecutorBase/`). `KeepsAdmin` is an assumption about reinitializer code and
`Administered` about configuration; `RowsCurrent` builds both in.

`RowsUnvalidated` adds no operation. A transition object is its manifest. `getManifest()` is
`view`, so it is called by `STATICCALL`, and the executor reads it once, so this describes any
object. `Transition.Genuine` records what a real `ProxyUpgradeTransition`
guarantees: nonempty rows that satisfy `ValidRows`. `ReinitFrames` stays a premise, an
assumption about reinitializer code and authority. The executors' legs are in `../ProxyUpgradeExecutorBase/`
(`EngineLegV35`'s `DefaultEngineLegIsApplyTransition`) and `../ChainTypeManager/`
(`FixedEntrypointsMoveProxiesOnlyAlongRowsAnyRows`).

## Source findings

Reported to the maintainer of this repo, not yet confirmed upstream. Each was checked by two
independent verifiers; only findings both upheld are listed, with the classification and
severity both gave. Paths are under `l1-contracts/contracts/`; first reported at `e561b9cc2`, re-checked at
`b17415d20`, where the cited `@dev` is `:104-105` and the executors accept any
`IProxyUpgradeTransition` from their owner (`ProxyUpgradeExecutorBase.sol:57-61` checks code
and domain only).

- *natspec-or-doc-wrong, info.* `upgrades/registry/libraries/ProxyUpgradeRowLib.sol:104-105`
  overstates what the post-swap verification catches. Nothing on the leg re-validates rows,
  and both executors accept any `IProxyUpgradeTransition` from their owner,
  so a non-genuine object can carry two rows on one proxy. A reinitializer can then move its
  own proxy to the later row's `expectedOldImpl`, and the later row moves it on to the target,
  uncaught (`DuplicateRowHidesReinitMove`). The net effect is still the first row's
  source-checked edge (`OnlyNamedEdgesAcrossCallAnyRows`).
- *natspec-or-doc-wrong, info.* Even on valid rows, a reinitializer that moves another row's
  proxy before that row runs can go uncaught (`ReinitLeakMovesNamedProxyOffEdge`).
  This needs authority over the other proxy, which a reinitializer does not have under the
  stated trust model.
## History: the `612a71ccc` snapshot

The record of an older commit, kept for the property names that cite it.

### What changed in the library between `612a71ccc` and `e561b9cc2`

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

### Status of the `612a71ccc` properties in `RowsCurrent`

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
- `RowsUnvalidated` covers the rows of an object that is not a genuine
  `ProxyUpgradeTransition`:
  - `OnlyNamedEdgesAcrossCallAnyRows` drops the distinct-proxies premise of
    `OnlyNamedEdgesAcrossCall`; only `ReinitFrames` remains. The edge belongs to the first row
    naming the proxy (`FirstRowCarriesTheEdge`); `LaterDuplicateRowIsNotAnEdgeFromStart` shows
    why the old proof needed distinct proxies.
  - `OnlyNamedEdgesAcrossTransitionAnyRows` is the same for `applyTransition` on any object,
    the entry point of both executors. `SourceIsNotAppliedAnyRows` needs only the row's own
    self-edge check.
  - The source's `@dev` (`:119-120`), "a reinitializer that moves any proxy of the row set is
    caught too", holds for the last row per proxy (`ReinitMovesAreCaughtOnLastRow`) and hence
    on distinct rows (`ReinitMovesAreCaughtOnDistinctRows`). It fails with a duplicate row
    (`DuplicateRowHidesReinitMove`); `DetourThenSkipIsCaught` is the variant that is caught.
  - Without `ReinitFrames`, a proxy named by valid rows can move along no row's edge
    (`ReinitLeakMovesNamedProxyOffEdge`).
  - Witnesses: `AnyRowsWitness`, `ReinitMovesCaughtWitness`.

