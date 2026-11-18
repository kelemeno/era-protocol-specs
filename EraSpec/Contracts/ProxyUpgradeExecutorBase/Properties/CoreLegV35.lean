import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.CoreLegV35

/-!
# Properties: the Core-domain leg at `b17415d20`

Statements about `EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.CoreLegV35`. Proofs are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.CoreLegV35`.

## What changed since `e561b9cc2`

At `e561b9cc2` `applyL1Upgrade` applied the transition's rows itself
(`ProxyUpgradeRowLib.applyTransition`, modelled in `ProxyUpgradeRowLib/Specs/RowsCurrent.lean`).
At `b17415d20` it delegatecalls the code the transition pins, with the authority of the
executor, which owns the ecosystem `ProxyAdmin`. Then it checks three things: the executor's own
owner and pending owner, the `ProxyAdmin`'s owner (through a hash), and every row's proxy at its
`implNew` as `getProxyImplementation` reads it. The CTM leg also checks the CTM's and
ServerNotifier's holders. The Core leg checks only the `ProxyAdmin`'s owner, because
`_domainHolders` returns early on a zero CTM (`ProxyUpgradeExecutorBase.sol:119-121`).

## Groups

* **(a) What a successful leg establishes**: `CoreLegChecks`, and exactly that:
  `CoreLegExact`, `CoreLegIgnoresCTMBranch`.
* **Each check is load-bearing**: `CorePAOwnerMoveCaught` (non-collision pinned to the one
  pair), `CorePAOwnerMoveUnderCollisionPasses`, `CorePAOwnerCheckIsLoadBearing`,
  `CoreExecutorOwnerCheckIsLoadBearing`, `CorePendingOwnerCheckIsLoadBearing`,
  `CoreRowsCheckIsLoadBearing`, `CoreRowsCheckCatchesAfterHook`.
* **What the checks read**: `CorePostCheckScopeIsRows` (for every pair of engines),
  `CorePostCheckScopeAdministered`, with `CorePostCheckScopeWitness`; for every successful
  default leg, `CoreUnnamedAdminMoveAlwaysPasses` and `CoreUnnamedImplMoveAlwaysPasses`, with
  the runs `CoreEngineMovesUnnamedSingletonAdmin` and `CoreEngineMovesUnnamedSingletonImpl`.
* **(b) A row proxy whose admin moved**: `CoreRowAdministeredIsAtImplNew`,
  `CoreRowAdminMoveCaught`, `CoreRowAdminMoveReverts` (with a run:
  `CoreRowAdminMoveRevertsWitness`); the answer premise is needed:
  `CoreRowAdminMoveUncaughtWhenAnswerMatches`.
* **(c) The default engine**: `DefaultCoreLegIsTheEngineRun` (no further premise),
  `DefaultCoreLegReplayIsNoop` (no further premise), `DefaultCoreLegNeedsOwnedAdmin`,
  `DefaultCoreLegIsApplyRows`, `DefaultCoreLegOnlyNamedEdges`, `UnownedReplayRevertsAtV35`; both
  premises of `DefaultCoreLegIsApplyRows` are needed: `DefaultLegNeedsAdministeredRows`,
  `DefaultLegReinitMovesRowAdmin`.
* **(d) Witness**: `CoreLegWitness`.

## What is not claimed

Nothing here says what a reviewed release engine does; the engine is a parameter. The CTM side
of the executor is opaque. Other state of the executor, the `ProxyAdmin` and the proxies is not
modelled (see the modelling choices in the Specs file). The witnesses use the toy data at the
end of the Specs file (identity owner hash, addresses below `101`).
-/

namespace Contracts.ProxyUpgradeExecutorV35.CoreLeg

open Contracts.ProxyUpgradeCurrent (Address Row Impl upd toRows Domain ValidRows Config ApplyRows
  ReinitFrames)

/-! ## (a) What a successful leg establishes -/

/-- **WHAT A SUCCESSFUL CORE LEG ESTABLISHES** (`ProxyUpgradeExecutorBase.sol:51-104` with
`_chainTypeManager = address(0)`). If `applyL1Upgrade(T)` by `caller` succeeds from `W` and ends
in `W'`, then: the caller is the executor's owner; the transition and its engine are code and
the domain is `Core`; the engine, run with the Core context (`coreContext`: zero CTM, the
executor's `ProxyAdmin`), turned `W` into `W'`; the executor's owner and pending owner are
exactly unchanged (`:93-95`); the `ProxyAdmin`'s owner is unchanged, or it changed to an address
whose `keccakOwner` equals the old one's (`:96-98`, `:119-121`); the inventory has
`L1_ECOSYSTEM_CONTRACT_COUNT` slots; and every row of `toRows(inventory)`, read through
`getProxyImplementation`, answers its `implNew` (`:99-103`). -/
def Properties.CoreLegChecks : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    applyL1Upgrade X E caller T W = some W' →
      caller = W.owner ∧ X.hasCode T.addr = true ∧ T.manifest.domain = .core ∧
      X.hasCode T.manifest.engine = true ∧
      E T.manifest.engine (coreContext X T) T.manifest.proxyUpgrades W = some W' ∧
      W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner ∧
      (W'.paOwner = W.paOwner ∨
        (W'.paOwner ≠ W.paOwner ∧ X.keccakOwner W'.paOwner = X.keccakOwner W.paOwner)) ∧
      T.manifest.proxyUpgrades.length = L1_ECOSYSTEM_CONTRACT_COUNT ∧
      ∀ r ∈ toRows T.manifest.proxyUpgrades, getProxyImplementation X W' r.proxy = some r.implNew

/-- **THE CORE LEG CHECKS EXACTLY THAT.** `applyL1Upgrade` succeeds from `W` with result `W'` if
and only if: the caller is the owner, the transition and engine are code, the domain is `Core`,
the engine's run with the Core context yields `W'`, the executor's owner and pending owner are
unchanged, the `ProxyAdmin` owner's `keccakOwner` is unchanged, the inventory length is
`L1_ECOSYSTEM_CONTRACT_COUNT`, and every row answers its `implNew` (`RowsAppliedW`). The leg puts
no other condition on `W'`. -/
def Properties.CoreLegExact : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    applyL1Upgrade X E caller T W = some W' ↔
      (caller = W.owner ∧ X.hasCode T.addr = true ∧ T.manifest.domain = .core ∧
        X.hasCode T.manifest.engine = true ∧
        E T.manifest.engine (coreContext X T) T.manifest.proxyUpgrades W = some W' ∧
        W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner ∧
        X.keccakOwner W'.paOwner = X.keccakOwner W.paOwner ∧
        T.manifest.proxyUpgrades.length = L1_ECOSYSTEM_CONTRACT_COUNT ∧
        RowsAppliedW X W' (toRows T.manifest.proxyUpgrades))

/-- **THE CORE LEG NEVER CONSULTS THE CTM SIDE.** Replacing the opaque CTM branch of
`_domainHolders` (`ProxyUpgradeExecutorBase.sol:122-147`) and the CTM-only check (`:75-77`) by any
other functions does not change the Core leg's outcome, for every engine, caller, transition and
world: with a zero CTM only `keccak256(abi.encode(_proxyAdmin.owner()))` (`:119-121`) is
compared. -/
def Properties.CoreLegIgnoresCTMBranch : Prop :=
  ∀ (X : Exec) (h : Address → World → Option UInt256) (c : Address → World → Bool)
    (E : Engines) (caller : Address) (T : TransitionObj) (W : World),
    applyL1Upgrade { X with ctmHolders := h, ctmCheck := c } E caller T W =
      applyL1Upgrade X E caller T W

/-! ## Each check is load-bearing -/

/-- **A `ProxyAdmin` OWNERSHIP MOVE IS CAUGHT, UNLESS THE HASHES COLLIDE.** If the engine's run
from `W` with the Core context ends in `M`, and `keccakOwner` of `M`'s `ProxyAdmin` owner differs
from that of `W`'s, the leg reverts. The premise is about that one pair, not injectivity. -/
def Properties.CorePAOwnerMoveCaught : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W M : World),
    E T.manifest.engine (coreContext X T) T.manifest.proxyUpgrades W = some M →
    X.keccakOwner M.paOwner ≠ X.keccakOwner W.paOwner →
    applyL1Upgrade X E caller T W = none

/-- **UNDER A COLLISION, A `ProxyAdmin` OWNERSHIP MOVE PASSES.** With a toy owner hash that maps
the executor `1` and address `9` to the same value, a genuine Core transition whose release
engine applies its row and then calls `PROXY_ADMIN.transferOwnership(9)` completes, and the
executor no longer owns the `ProxyAdmin`. So the collision disjunct of `CoreLegChecks` cannot be
dropped in this model, where `keccakOwner` is an arbitrary function. -/
def Properties.CorePAOwnerMoveUnderCollisionPasses : Prop :=
  ∃ W', Genuine coreTransition ∧
    applyL1Upgrade coreExecCollide (coreReleaseEngines coreExecCollide [.transferPAOwnership 9])
      coreWorld.owner coreTransition coreWorld = some W' ∧
    W'.impl coreRow.proxy = coreRow.implNew ∧
    coreWorld.paOwner = coreExecCollide.self ∧ W'.paOwner = 9 ∧
    W'.paOwner ≠ coreExecCollide.self ∧
    coreExecCollide.keccakOwner W'.paOwner = coreExecCollide.keccakOwner coreWorld.paOwner

/-- **THE `ProxyAdmin`-OWNER CHECK IS WHAT REJECTS AN OWNERSHIP MOVE.** With the identity owner
hash, the release engine of `CorePAOwnerMoveUnderCollisionPasses` runs successfully on the genuine
`coreTransition`: its result keeps the executor's owner and pending owner, has the row applied,
and has a different `ProxyAdmin` owner, with a different `keccakOwner`. The leg reverts. Every
premise of `CorePAOwnerMoveCaught` holds. -/
def Properties.CorePAOwnerCheckIsLoadBearing : Prop :=
  ∃ M, Genuine coreTransition ∧
    coreReleaseEngines coreExec [.transferPAOwnership 9] coreTransition.manifest.engine
      (coreContext coreExec coreTransition) coreTransition.manifest.proxyUpgrades coreWorld
      = some M ∧
    M.owner = coreWorld.owner ∧ M.pendingOwner = coreWorld.pendingOwner ∧
    RowsAppliedW coreExec M (toRows coreTransition.manifest.proxyUpgrades) ∧
    M.paOwner ≠ coreWorld.paOwner ∧
    coreExec.keccakOwner M.paOwner ≠ coreExec.keccakOwner coreWorld.paOwner ∧
    applyL1Upgrade coreExec (coreReleaseEngines coreExec [.transferPAOwnership 9]) coreWorld.owner
      coreTransition coreWorld = none

/-- **THE EXECUTOR-OWNER CHECK IS LOAD-BEARING** (`:93-95`). On the genuine `coreTransition`, a
release engine whose `_afterSwaps` writes the executor's owner slot runs successfully; its result
keeps the pending owner and the `ProxyAdmin`'s owner, has the row applied, and has a different
executor owner. The leg reverts. -/
def Properties.CoreExecutorOwnerCheckIsLoadBearing : Prop :=
  ∃ M, Genuine coreTransition ∧
    coreReleaseEngines coreExec [.writeOwner 9] coreTransition.manifest.engine
      (coreContext coreExec coreTransition) coreTransition.manifest.proxyUpgrades coreWorld
      = some M ∧
    M.owner ≠ coreWorld.owner ∧ M.pendingOwner = coreWorld.pendingOwner ∧
    M.paOwner = coreWorld.paOwner ∧
    RowsAppliedW coreExec M (toRows coreTransition.manifest.proxyUpgrades) ∧
    applyL1Upgrade coreExec (coreReleaseEngines coreExec [.writeOwner 9]) coreWorld.owner
      coreTransition coreWorld = none

/-- **THE PENDING-OWNER CHECK IS LOAD-BEARING** (`:93-95`). As
`CoreExecutorOwnerCheckIsLoadBearing`, for the pending-owner slot. -/
def Properties.CorePendingOwnerCheckIsLoadBearing : Prop :=
  ∃ M, Genuine coreTransition ∧
    coreReleaseEngines coreExec [.writePendingOwner 9] coreTransition.manifest.engine
      (coreContext coreExec coreTransition) coreTransition.manifest.proxyUpgrades coreWorld
      = some M ∧
    M.owner = coreWorld.owner ∧ M.pendingOwner ≠ coreWorld.pendingOwner ∧
    M.paOwner = coreWorld.paOwner ∧
    RowsAppliedW coreExec M (toRows coreTransition.manifest.proxyUpgrades) ∧
    applyL1Upgrade coreExec (coreReleaseEngines coreExec [.writePendingOwner 9]) coreWorld.owner
      coreTransition coreWorld = none

/-- **THE ROWS CHECK IS LOAD-BEARING** (`:99-103`). A genuine Core transition pinning an engine
that does nothing: the engine's run returns the world unchanged, so the ownership and holder
checks pass, and the leg reverts because its row's proxy does not answer `implNew`. -/
def Properties.CoreRowsCheckIsLoadBearing : Prop :=
  Genuine coreTransition ∧
    coreNoopEngines coreTransition.manifest.engine (coreContext coreExec coreTransition)
      coreTransition.manifest.proxyUpgrades coreWorld = some coreWorld ∧
    ¬ RowsAppliedW coreExec coreWorld (toRows coreTransition.manifest.proxyUpgrades) ∧
    applyL1Upgrade coreExec coreNoopEngines coreWorld.owner coreTransition coreWorld = none

/-- **THE EXECUTOR'S ROWS CHECK CATCHES A FOLLOW-UP HOOK.** A genuine Core transition whose
release engine applies its row (passing `applyRows`' own `requireRowsApplied`) and then, in
`_afterSwaps`, calls `PROXY_ADMIN.upgrade(5, 10)`, moving the row's proxy back to its
`expectedOldImpl`. The engine's run succeeds and keeps the executor's owner, pending owner and the
`ProxyAdmin`'s owner; proxy `5` stays under the `ProxyAdmin`. The executor's second
`requireRowsApplied` (`ProxyUpgradeExecutorBase.sol:103`) reverts the leg. This is the case
`ProxyUpgradeRowLib.sol:130-132` describes. -/
def Properties.CoreRowsCheckCatchesAfterHook : Prop :=
  ∃ M, Genuine coreTransition ∧
    coreReleaseEngines coreExec [.upgrade 5 10] coreTransition.manifest.engine
      (coreContext coreExec coreTransition) coreTransition.manifest.proxyUpgrades coreWorld
      = some M ∧
    M.owner = coreWorld.owner ∧ M.pendingOwner = coreWorld.pendingOwner ∧
    M.paOwner = coreWorld.paOwner ∧
    M.admin coreRow.proxy = coreExec.pa ∧ M.impl coreRow.proxy = coreRow.expectedOldImpl ∧
    ¬ RowsAppliedW coreExec M (toRows coreTransition.manifest.proxyUpgrades) ∧
    applyL1Upgrade coreExec (coreReleaseEngines coreExec [.upgrade 5 10]) coreWorld.owner
      coreTransition coreWorld = none

/-! ## What the checks read -/

/-- **THE CORE LEG SEES THE ENGINE'S RESULT ONLY THROUGH THE OWNERS AND THE ROW READS.** Take
two engines whose runs from `W` with the Core context end in `M` and `M'`. If `M` and `M'` have the
same executor owner and pending owner, the same `keccakOwner` of the `ProxyAdmin`'s owner, and the
same `getProxyImplementation` answer at every row's proxy, then the leg succeeds with `M` under
the first engine exactly when it succeeds with `M'` under the second. Nothing is assumed about
any other proxy's implementation or admin slot in `M` and `M'`. -/
def Properties.CorePostCheckScopeIsRows : Prop :=
  ∀ (X : Exec) (E E' : Engines) (caller : Address) (T : TransitionObj) (W M M' : World),
    E T.manifest.engine (coreContext X T) T.manifest.proxyUpgrades W = some M →
    E' T.manifest.engine (coreContext X T) T.manifest.proxyUpgrades W = some M' →
    M'.owner = M.owner → M'.pendingOwner = M.pendingOwner →
    X.keccakOwner M'.paOwner = X.keccakOwner M.paOwner →
    (∀ r ∈ toRows T.manifest.proxyUpgrades,
      getProxyImplementation X M' r.proxy = getProxyImplementation X M r.proxy) →
    (applyL1Upgrade X E caller T W = some M ↔ applyL1Upgrade X E' caller T W = some M')

/-- **THE SAME, WHEN THE `ProxyAdmin` ADMINISTERS THE ROWS' PROXIES.** As
`CorePostCheckScopeIsRows`, with the row reads replaced by slots: if the `ProxyAdmin` administers
every row's proxy in both `M` and `M'`, and `M` and `M'` have the same executor owner, pending
owner and `ProxyAdmin` owner and the same implementation slot at every row's proxy, the two legs
succeed together. -/
def Properties.CorePostCheckScopeAdministered : Prop :=
  ∀ (X : Exec) (E E' : Engines) (caller : Address) (T : TransitionObj) (W M M' : World),
    E T.manifest.engine (coreContext X T) T.manifest.proxyUpgrades W = some M →
    E' T.manifest.engine (coreContext X T) T.manifest.proxyUpgrades W = some M' →
    M'.owner = M.owner → M'.pendingOwner = M.pendingOwner → M'.paOwner = M.paOwner →
    (∀ r ∈ toRows T.manifest.proxyUpgrades,
      M.admin r.proxy = X.pa ∧ M'.admin r.proxy = X.pa ∧ M'.impl r.proxy = M.impl r.proxy) →
    (applyL1Upgrade X E caller T W = some M ↔ applyL1Upgrade X E' caller T W = some M')

/-- **THE PREMISES OF BOTH SCOPE RESULTS HOLD WITH TWO DIFFERENT RESULTS.** For the genuine
`coreTransition` from `coreWorld`: the default engine ends in `M`; a release engine whose
`_afterSwaps` calls `PROXY_ADMIN.changeProxyAdmin(6, 9)` ends in `M'`. Every premise of
`CorePostCheckScopeIsRows` and `CorePostCheckScopeAdministered` holds, `M' ≠ M` (they differ in
proxy `6`'s admin slot), and both legs succeed. -/
def Properties.CorePostCheckScopeWitness : Prop :=
  ∃ M M', Genuine coreTransition ∧
    coreDefaultEngines coreExec coreTransition.manifest.engine (coreContext coreExec coreTransition)
      coreTransition.manifest.proxyUpgrades coreWorld = some M ∧
    coreReleaseEngines coreExec [.changeProxyAdmin 6 9] coreTransition.manifest.engine
      (coreContext coreExec coreTransition) coreTransition.manifest.proxyUpgrades coreWorld
      = some M' ∧
    M'.owner = M.owner ∧ M'.pendingOwner = M.pendingOwner ∧ M'.paOwner = M.paOwner ∧
    coreExec.keccakOwner M'.paOwner = coreExec.keccakOwner M.paOwner ∧
    (∀ r ∈ toRows coreTransition.manifest.proxyUpgrades,
      M.admin r.proxy = coreExec.pa ∧ M'.admin r.proxy = coreExec.pa ∧
        M'.impl r.proxy = M.impl r.proxy) ∧
    (∀ r ∈ toRows coreTransition.manifest.proxyUpgrades,
      getProxyImplementation coreExec M' r.proxy = getProxyImplementation coreExec M r.proxy) ∧
    M' ≠ M ∧
    applyL1Upgrade coreExec (coreDefaultEngines coreExec) coreWorld.owner coreTransition coreWorld
      = some M ∧
    applyL1Upgrade coreExec (coreReleaseEngines coreExec [.changeProxyAdmin 6 9]) coreWorld.owner
      coreTransition coreWorld = some M'

/-- **A HOOK CAN MOVE THE ADMIN OF ANY PROXY NO ROW NAMES.** Suppose a Core leg whose transition
pins `DefaultProxyUpgradeEngine` succeeds from `W` with result `W'`, and the `ProxyAdmin`
administers every row's proxy in `W'`. Take any proxy `p` that no row names and that the
`ProxyAdmin` administers in `W'`, and any nonzero `a`. Then the same leg, with the engine replaced
by a `DefaultProxyUpgradeEngine` subclass whose `_afterSwaps` calls
`PROXY_ADMIN.changeProxyAdmin(p, a)`, also succeeds, and its result is `W'` with `p`'s admin slot
set to `a`. No premise on the reinitializers. -/
def Properties.CoreUnnamedAdminMoveAlwaysPasses : Prop :=
  ∀ (X : Exec) (E E' : Engines) (caller : Address) (T : TransitionObj) (W W' : World)
    (p a : Address),
    E T.manifest.engine = defaultEngine X →
    E' T.manifest.engine = releaseEngine X [.changeProxyAdmin p a] →
    applyL1Upgrade X E caller T W = some W' →
    (∀ r ∈ toRows T.manifest.proxyUpgrades, r.proxy ≠ p ∧ W'.admin r.proxy = X.pa) →
    W'.admin p = X.pa → a ≠ 0 →
    applyL1Upgrade X E' caller T W = some { W' with admin := upd W'.admin p a }

/-- **A HOOK CAN MOVE THE IMPLEMENTATION OF ANY PROXY NO ROW NAMES.** As
`CoreUnnamedAdminMoveAlwaysPasses`, with `_afterSwaps` calling `PROXY_ADMIN.upgrade(p, x)` for
any `x` that is code: the leg succeeds and its result is `W'` with `p`'s implementation slot set
to `x`. Nothing relates `x` to `p`'s old implementation or to any row. -/
def Properties.CoreUnnamedImplMoveAlwaysPasses : Prop :=
  ∀ (X : Exec) (E E' : Engines) (caller : Address) (T : TransitionObj) (W W' : World)
    (p x : Address),
    E T.manifest.engine = defaultEngine X →
    E' T.manifest.engine = releaseEngine X [.upgrade p x] →
    applyL1Upgrade X E caller T W = some W' →
    (∀ r ∈ toRows T.manifest.proxyUpgrades, r.proxy ≠ p ∧ W'.admin r.proxy = X.pa) →
    W'.admin p = X.pa → X.hasCode x = true →
    applyL1Upgrade X E' caller T W = some { W' with impl := upd W'.impl p x }

/-- **AN UNNAMED SINGLETON'S ADMIN MOVES IN A COMPLETED LEG.** The premises of
`CoreUnnamedAdminMoveAlwaysPasses` on concrete data: from `coreWorld`, where the `ProxyAdmin`
administers every proxy, the genuine `coreTransition` with the default engine completes with
`W'`; the `ProxyAdmin` administers proxy `5`, the one row's proxy, and proxy `6`, which no row
names, in `W'`. The same transition with a release engine whose `_afterSwaps` calls
`PROXY_ADMIN.changeProxyAdmin(6, 9)` completes with `W'` except that proxy `6` is administered by
`9`. Every check of the leg passed. The executor's post-checks do not read proxy `6`
(`CorePostCheckScopeIsRows`); `IProxyUpgradeEngine.sol:16-21` leaves what an engine does
through the `ProxyAdmin` beyond the holders and the rows to the review of the engine's code. -/
def Properties.CoreEngineMovesUnnamedSingletonAdmin : Prop :=
  ∃ W', Genuine coreTransition ∧
    coreDefaultEngines coreExec coreTransition.manifest.engine = defaultEngine coreExec ∧
    coreReleaseEngines coreExec [.changeProxyAdmin 6 9] coreTransition.manifest.engine =
      releaseEngine coreExec [.changeProxyAdmin 6 9] ∧
    applyL1Upgrade coreExec (coreDefaultEngines coreExec) coreWorld.owner coreTransition coreWorld
      = some W' ∧
    (∀ r ∈ toRows coreTransition.manifest.proxyUpgrades,
      r.proxy ≠ 6 ∧ W'.admin r.proxy = coreExec.pa) ∧
    W'.admin 6 = coreExec.pa ∧ (9 : Address) ≠ 0 ∧ (∀ p, coreWorld.admin p = coreExec.pa) ∧
    applyL1Upgrade coreExec (coreReleaseEngines coreExec [.changeProxyAdmin 6 9]) coreWorld.owner
      coreTransition coreWorld = some { W' with admin := upd W'.admin 6 9 } ∧
    (upd W'.admin 6 9) 6 = 9 ∧ (upd W'.admin 6 9) 6 ≠ coreExec.pa

/-- **AN UNNAMED SINGLETON'S IMPLEMENTATION MOVES OFF-ROW IN A COMPLETED LEG.** The premises of
`CoreUnnamedImplMoveAlwaysPasses` on the data of `CoreEngineMovesUnnamedSingletonAdmin`, with
`_afterSwaps` calling `PROXY_ADMIN.upgrade(7, 13)`: proxy `7`, which no row names, ends at `13`,
which no row names either, and stays under the `ProxyAdmin`. Every check of the leg passed. -/
def Properties.CoreEngineMovesUnnamedSingletonImpl : Prop :=
  ∃ W', Genuine coreTransition ∧
    coreDefaultEngines coreExec coreTransition.manifest.engine = defaultEngine coreExec ∧
    coreReleaseEngines coreExec [.upgrade 7 13] coreTransition.manifest.engine =
      releaseEngine coreExec [.upgrade 7 13] ∧
    applyL1Upgrade coreExec (coreDefaultEngines coreExec) coreWorld.owner coreTransition coreWorld
      = some W' ∧
    (∀ r ∈ toRows coreTransition.manifest.proxyUpgrades,
      r.proxy ≠ 7 ∧ r.implNew ≠ 13 ∧ W'.admin r.proxy = coreExec.pa) ∧
    W'.admin 7 = coreExec.pa ∧ coreExec.hasCode 13 = true ∧
    applyL1Upgrade coreExec (coreReleaseEngines coreExec [.upgrade 7 13]) coreWorld.owner
      coreTransition coreWorld = some { W' with impl := upd W'.impl 7 13 } ∧
    coreWorld.impl 7 = 10 ∧ (upd W'.impl 7 13) 7 = 13

/-! ## (b) A row proxy whose admin moved -/

/-- **A ROW PROXY UNDER THE `ProxyAdmin` AFTER THE LEG IS AT ITS `implNew`.** After a successful
leg, a row whose proxy the `ProxyAdmin` administers in the final world has its implementation
slot at `implNew`. No premise about the admin before the leg. -/
def Properties.CoreRowAdministeredIsAtImplNew : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    applyL1Upgrade X E caller T W = some W' →
    ∀ r ∈ toRows T.manifest.proxyUpgrades, W'.admin r.proxy = X.pa → W'.impl r.proxy = r.implNew

/-- **A ROW PROXY OUTSIDE THE `ProxyAdmin` AFTER THE LEG PASSED BY ITS CODE'S ANSWER.** After a
successful leg, a row whose proxy is not administered by the `ProxyAdmin` has a current
implementation whose code, asked `implementation()` for that proxy in the final world, answers the
row's `implNew`: `requireRowsApplied` reads through the proxy's non-admin path
(`TransparentUpgradeableProxy.sol:104-105`). Nothing is said about that proxy's implementation
slot. No premise about the admin before the leg. The name is historical: the statement describes
how a moved row proxy passes the check, not that the move is caught;
`CoreRowAdminMoveUncaughtWhenAnswerMatches` shows such a move need not be caught. -/
def Properties.CoreRowAdminMoveCaught : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    applyL1Upgrade X E caller T W = some W' →
    ∀ r ∈ toRows T.manifest.proxyUpgrades, W'.admin r.proxy ≠ X.pa →
      X.implAnswer (W'.impl r.proxy) r.proxy W' = some r.implNew

/-- **AN ENGINE THAT LEAVES A ROW PROXY OUTSIDE THE `ProxyAdmin` REVERTS THE LEG, UNLESS THE CODE
ANSWERS `implNew`.** `CoreRowAdminMoveCaught` as a revert. If the engine's run from `W` with the
Core context ends in `M`, some row's proxy is not administered by the `ProxyAdmin` in `M`, and the
code at that proxy's implementation in `M` does not answer `implementation()` with the row's
`implNew` (it reverts or answers something else), then `applyL1Upgrade` reverts
(`ProxyUpgradeRowLib.sol:133-141`). `CoreRowAdminMoveUncaughtWhenAnswerMatches` shows the last
premise cannot be dropped. -/
def Properties.CoreRowAdminMoveReverts : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W M : World),
    E T.manifest.engine (coreContext X T) T.manifest.proxyUpgrades W = some M →
    ∀ r ∈ toRows T.manifest.proxyUpgrades, M.admin r.proxy ≠ X.pa →
      X.implAnswer (M.impl r.proxy) r.proxy M ≠ some r.implNew →
      applyL1Upgrade X E caller T W = none

/-- **`CoreRowAdminMoveReverts` HAS A RUN, AND THE CHECK READS THE ANSWER, NOT THE SLOT.** A
genuine Core transition with a release engine whose `_afterSwaps` calls
`PROXY_ADMIN.changeProxyAdmin(5, 9)` on its own row's proxy. The engine's run succeeds: it keeps
the executor's owner and pending owner and the `ProxyAdmin`'s owner, and proxy `5`'s
implementation slot IS the row's `implNew`. But `5` is no longer administered by the `ProxyAdmin`
and the code at `11` does not answer `implementation()`, so the leg reverts. Every premise of
`CoreRowAdminMoveReverts` holds. -/
def Properties.CoreRowAdminMoveRevertsWitness : Prop :=
  ∃ M, Genuine coreTransition ∧
    coreReleaseEngines coreExec [.changeProxyAdmin 5 9] coreTransition.manifest.engine
      (coreContext coreExec coreTransition) coreTransition.manifest.proxyUpgrades coreWorld
      = some M ∧
    coreRow ∈ toRows coreTransition.manifest.proxyUpgrades ∧
    coreWorld.admin coreRow.proxy = coreExec.pa ∧ M.admin coreRow.proxy ≠ coreExec.pa ∧
    M.impl coreRow.proxy = coreRow.implNew ∧
    coreExec.implAnswer (M.impl coreRow.proxy) coreRow.proxy M ≠ some coreRow.implNew ∧
    M.owner = coreWorld.owner ∧ M.pendingOwner = coreWorld.pendingOwner ∧
    M.paOwner = coreWorld.paOwner ∧
    applyL1Upgrade coreExec (coreReleaseEngines coreExec [.changeProxyAdmin 5 9]) coreWorld.owner
      coreTransition coreWorld = none

/-- **THE ANSWER PREMISE OF `CoreRowAdminMoveReverts` IS NEEDED.** A genuine Core transition
with a release engine whose `_afterSwaps` calls `PROXY_ADMIN.upgrade(5, 12)` and then
`PROXY_ADMIN.changeProxyAdmin(5, 9)` completes, where implementation `12` answers
`implementation()` with `11`. Row proxy `5`, administered by the `ProxyAdmin` before the leg, ends
administered by `9` with its implementation slot at `12`, not the row's `implNew` `11`. What
`requireRowsApplied` compared is the answer `getProxyImplementation` read, which is the
implementation slot only while the `ProxyAdmin` administers the proxy
(`CoreRowAdministeredIsAtImplNew`). -/
def Properties.CoreRowAdminMoveUncaughtWhenAnswerMatches : Prop :=
  ∃ W', Genuine coreTransition ∧
    applyL1Upgrade coreExecSpoof
      (coreReleaseEngines coreExecSpoof [.upgrade 5 12, .changeProxyAdmin 5 9])
      coreWorld.owner coreTransition coreWorld = some W' ∧
    coreRow ∈ toRows coreTransition.manifest.proxyUpgrades ∧
    coreWorld.admin coreRow.proxy = coreExecSpoof.pa ∧ W'.admin coreRow.proxy ≠ coreExecSpoof.pa ∧
    W'.impl coreRow.proxy ≠ coreRow.implNew ∧
    getProxyImplementation coreExecSpoof W' coreRow.proxy = some coreRow.implNew

/-! ## (c) The default engine -/

/-- **WITH THE DEFAULT ENGINE, THE CORE LEG IS THE ENGINE'S RUN.** If the transition pins
`DefaultProxyUpgradeEngine`, the leg succeeds from `W` with result `W'` if and only if the caller
is the owner, the transition and engine are code, the domain is `Core`, and the default engine's
run with the Core context turns `W` into `W'`. So the executor's post-checks never reject a run of
the default engine. No premise on who administers the rows' proxies or on the reinitializers. -/
def Properties.DefaultCoreLegIsTheEngineRun : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    E T.manifest.engine = defaultEngine X →
    (applyL1Upgrade X E caller T W = some W' ↔
      (caller = W.owner ∧ X.hasCode T.addr = true ∧ T.manifest.domain = .core ∧
        X.hasCode T.manifest.engine = true ∧
        defaultEngine X (coreContext X T) T.manifest.proxyUpgrades W = some W'))

/-- **WITH THE DEFAULT ENGINE, APPLYING A CORE TRANSITION AGAIN CHANGES NOTHING.** If the
transition pins `DefaultProxyUpgradeEngine` and the leg succeeds from `W` with result `W'`, the
same call (same caller, same transition object and manifest) from `W'` succeeds with result `W'`.
No premise on who administers the rows' proxies or on the reinitializers: in `W'` every row
reads its `implNew`, so every row is skipped. This is the replay
`DefaultProxyUpgradeEngine.sol:20-23` describes ("a transition can be applied again (every row
already installed)"), for the engine with empty hooks. -/
def Properties.DefaultCoreLegReplayIsNoop : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    E T.manifest.engine = defaultEngine X →
    applyL1Upgrade X E caller T W = some W' →
    applyL1Upgrade X E caller T W' = some W'

/-- **WITH THE DEFAULT ENGINE, AN EXECUTOR THAT DOES NOT OWN THE `ProxyAdmin` CANNOT COMPLETE A
CORE LEG** (`DefaultProxyUpgradeEngine.sol:33-37`). No other premise: this holds also when every
row is already at its `implNew`. -/
def Properties.DefaultCoreLegNeedsOwnedAdmin : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W : World),
    E T.manifest.engine = defaultEngine X → W.paOwner ≠ X.self →
    applyL1Upgrade X E caller T W = none

/-- **WITH THE DEFAULT ENGINE, THE CORE LEG IS `RowsCurrent.ApplyRows`.** If the transition pins
`DefaultProxyUpgradeEngine`, the `ProxyAdmin` administers every row's proxy before the leg, and
no reinitializer writes an admin slot (`ReinitKeepsAdmins`), then the leg succeeds with result
`W'` if and only if: the caller is the owner, the transition and engine are code, the domain is
`Core`, the executor owns the `ProxyAdmin`, the inventory has `L1_ECOSYSTEM_CONTRACT_COUNT` slots,
`RowsCurrent.ApplyRows` relates the implementation mappings over `toRows(inventory)` under the
executor's configuration (`rowsConfig`), and `W'` differs from `W` only in the implementation
mapping. -/
def Properties.DefaultCoreLegIsApplyRows : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    E T.manifest.engine = defaultEngine X →
    (∀ r ∈ toRows T.manifest.proxyUpgrades, W.admin r.proxy = X.pa) →
    ReinitKeepsAdmins X →
    (applyL1Upgrade X E caller T W = some W' ↔
      (caller = W.owner ∧ X.hasCode T.addr = true ∧ T.manifest.domain = .core ∧
        X.hasCode T.manifest.engine = true ∧ W.paOwner = X.self ∧
        T.manifest.proxyUpgrades.length = L1_ECOSYSTEM_CONTRACT_COUNT ∧
        ApplyRows (rowsConfig X W) W.impl (toRows T.manifest.proxyUpgrades) W'.impl ∧
        W' = { W with impl := W'.impl }))

/-- **WITH THE DEFAULT ENGINE, A CORE LEG MOVES PROXIES ONLY ALONG ROW EDGES.** Under the
premises of `DefaultCoreLegIsApplyRows`, for rows naming distinct proxies (as a genuine
transition's are) and reinitializers that move at most their own proxy (`ReinitFrames` of
`rowsConfig X W`): after a successful leg, no admin slot changed, the `ProxyAdmin`'s owner and the
executor's owner and pending owner are unchanged, and every proxy is where it was or went from
some row's `expectedOldImpl` to that row's `implNew`. This is
`ProxyUpgradeCurrent.OnlyNamedEdgesAcrossCall`, carried over to the Core leg. -/
def Properties.DefaultCoreLegOnlyNamedEdges : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    E T.manifest.engine = defaultEngine X →
    (∀ r ∈ toRows T.manifest.proxyUpgrades, W.admin r.proxy = X.pa) →
    ReinitKeepsAdmins X →
    (toRows T.manifest.proxyUpgrades).Pairwise (fun a b => a.proxy ≠ b.proxy) →
    ReinitFrames (rowsConfig X W) →
    applyL1Upgrade X E caller T W = some W' →
      W'.admin = W.admin ∧ W'.paOwner = W.paOwner ∧ W'.owner = W.owner ∧
      W'.pendingOwner = W.pendingOwner ∧
      ∀ p, W'.impl p = W.impl p ∨
        ∃ r ∈ toRows T.manifest.proxyUpgrades,
          r.proxy = p ∧ W.impl p = r.expectedOldImpl ∧ W'.impl p = r.implNew

/-- **THE OWNERSHIP CONJUNCT OF `DefaultCoreLegIsApplyRows` DOES NOT FOLLOW FROM `ApplyRows`.**
Proxy `5` is already at the row's `implNew` and `7`, not the executor, owns the `ProxyAdmin`.
`RowsCurrent.ApplyRows` holds from that state to itself (every row skips; at `e561b9cc2` the
library let such a replay through, `ProxyUpgradeCurrent.UnownedAdminMovesNothing`), and the
`b17415d20` leg with the default engine reverts. Every premise of
`DefaultCoreLegNeedsOwnedAdmin` holds. -/
def Properties.UnownedReplayRevertsAtV35 : Prop :=
  ∃ W : World, Genuine coreTransition ∧
    coreDefaultEngines coreExec coreTransition.manifest.engine = defaultEngine coreExec ∧
    W.paOwner ≠ coreExec.self ∧
    (∀ r ∈ toRows coreTransition.manifest.proxyUpgrades, W.admin r.proxy = coreExec.pa) ∧
    ApplyRows (rowsConfig coreExec W) W.impl (toRows coreTransition.manifest.proxyUpgrades)
      W.impl ∧
    applyL1Upgrade coreExec (coreDefaultEngines coreExec) W.owner coreTransition W = none

/-- **THE ADMINISTRATION PREMISE OF `DefaultCoreLegIsApplyRows` IS NEEDED.** The genuine
`coreTransition` pins the default engine and no reinitializer writes an admin slot, but row proxy
`5` is administered by `8`, not the `ProxyAdmin`, and runs `12`, which answers `implementation()`
with `11`. The default engine reads `11`, skips the row as already applied, and the leg completes
without changing anything; but proxy `5` is not at `11`, so `RowsCurrent.ApplyRows` does not
hold. -/
def Properties.DefaultLegNeedsAdministeredRows : Prop :=
  Genuine coreTransition ∧
    coreDefaultEngines coreExecSpoof coreTransition.manifest.engine = defaultEngine coreExecSpoof ∧
    ReinitKeepsAdmins coreExecSpoof ∧
    applyL1Upgrade coreExecSpoof (coreDefaultEngines coreExecSpoof) coreWorldForeign.owner
      coreTransition coreWorldForeign = some coreWorldForeign ∧
    coreWorldForeign.admin coreRow.proxy ≠ coreExecSpoof.pa ∧
    coreWorldForeign.impl coreRow.proxy ≠ coreRow.implNew ∧
    ¬ ApplyRows (rowsConfig coreExecSpoof coreWorldForeign) coreWorldForeign.impl
      (toRows coreTransition.manifest.proxyUpgrades) coreWorldForeign.impl

/-- **THE `ReinitKeepsAdmins` PREMISE OF `DefaultCoreLegIsApplyRows` IS NEEDED.** A genuine Core
transition pins the default engine, and its one row sets `callInitializeUpgrade`. The
`ProxyAdmin` administers the row's proxy `5` before the leg. The reinitializer of `11`, running in
proxy `5`'s storage, writes that proxy's admin slot to `9`. If `11` answers `implementation()`
with `11`, the leg completes: proxy `5` is at `11` and no longer administered by the
`ProxyAdmin`, so the conclusion `W' = { W with impl := W'.impl }` fails. If `11` does not answer
`implementation()`, the default engine's own run reverts (its `applyRows` ends with
`requireRowsApplied`, `ProxyUpgradeRowLib.sol:127`), and so does the leg. -/
def Properties.DefaultLegReinitMovesRowAdmin : Prop :=
  ∃ W', Genuine coreTransitionInit ∧
    coreDefaultEngines coreExecReinit coreTransitionInit.manifest.engine =
      defaultEngine coreExecReinit ∧
    (∀ r ∈ toRows coreTransitionInit.manifest.proxyUpgrades,
      coreWorld.admin r.proxy = coreExecReinit.pa) ∧
    ¬ ReinitKeepsAdmins coreExecReinit ∧
    applyL1Upgrade coreExecReinit (coreDefaultEngines coreExecReinit) coreWorld.owner
      coreTransitionInit coreWorld = some W' ∧
    W'.impl 5 = coreRowInit.implNew ∧ W'.admin 5 = 9 ∧ W'.admin 5 ≠ coreExecReinit.pa ∧
    W' ≠ { coreWorld with impl := W'.impl } ∧
    defaultEngine coreExecReinitSilent (coreContext coreExecReinitSilent coreTransitionInit)
      coreTransitionInit.manifest.proxyUpgrades coreWorld = none ∧
    applyL1Upgrade coreExecReinitSilent (coreDefaultEngines coreExecReinitSilent) coreWorld.owner
      coreTransitionInit coreWorld = none

/-! ## (d) Witness -/

/-- **A GENUINE CORE TRANSITION WITH A REINITIALIZER APPLIES WITH THE DEFAULT ENGINE.** The
premise bundles of `DefaultCoreLegIsTheEngineRun`, `DefaultCoreLegReplayIsNoop`,
`DefaultCoreLegIsApplyRows` and `DefaultCoreLegOnlyNamedEdges` hold together on one run: a
genuine Core transition pinning the default engine, whose one row (proxy `5`, `10 → 11`) calls its
reinitializer; an executor that owns the `ProxyAdmin`, which administers the row's proxy; and a
reinitializer that writes no admin slot and only its own proxy's implementation slot. Governance's
call succeeds through the `upgradeAndCall` branch, moves proxy `5` from `10` to `11`, and leaves
the unnamed singletons `6` and `7` and every admin slot alone. The reinitializer's non-identity
conjunct is evaluated at the pre-swap `coreWorld.impl`; in the run it writes `implNew` into its
own proxy, which the swap already did, so it changes nothing there. Under `ReinitFrames`,
`ReinitKeepsAdmins` and a successful leg every reinitializer is inert on the run;
`DefaultLegReinitMovesRowAdmin` is the run where a reinitializer does act. -/
def Properties.CoreLegWitness : Prop :=
  ∃ W', Genuine coreTransitionInit ∧ coreTransitionInit.manifest.domain = .core ∧
    coreDefaultEngines coreExec coreTransitionInit.manifest.engine = defaultEngine coreExec ∧
    coreWorld.paOwner = coreExec.self ∧
    (∀ r ∈ toRows coreTransitionInit.manifest.proxyUpgrades,
      coreWorld.admin r.proxy = coreExec.pa) ∧
    ReinitKeepsAdmins coreExec ∧
    (toRows coreTransitionInit.manifest.proxyUpgrades).Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    ReinitFrames (rowsConfig coreExec coreWorld) ∧
    coreRowInit ∈ toRows coreTransitionInit.manifest.proxyUpgrades ∧
    coreRowInit.callInitializeUpgrade = true ∧
    (rowsConfig coreExec coreWorld).reinit coreRowInit coreWorld.impl ≠ coreWorld.impl ∧
    applyL1Upgrade coreExec (coreDefaultEngines coreExec) coreWorld.owner coreTransitionInit
      coreWorld = some W' ∧
    coreWorld.impl 5 = coreRowInit.expectedOldImpl ∧ W'.impl 5 = coreRowInit.implNew ∧
    coreRowInit.expectedOldImpl ≠ coreRowInit.implNew ∧ W'.impl 6 = coreWorld.impl 6 ∧
    W'.impl 7 = coreWorld.impl 7 ∧ W'.admin = coreWorld.admin

end Contracts.ProxyUpgradeExecutorV35.CoreLeg
