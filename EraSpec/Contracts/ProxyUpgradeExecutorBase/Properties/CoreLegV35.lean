import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.CoreLegV35

/-!
# Properties: the Core-domain leg at `d9f678900`

Statements about `EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.CoreLegV35`. Proofs are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.CoreLegV35`.

## What changed since `e561b9cc2`

At `e561b9cc2` `applyL1Upgrade` applied the transition's rows itself
(`ProxyUpgradeRowLib.applyTransition`, modelled in `ProxyUpgradeRowLib/Specs/RowsCurrent.lean`).
At `d9f678900` it delegatecalls the code the transition pins, with the authority of the
executor, which owns the ecosystem `ProxyAdmin`. Then it checks three things: the executor's own
owner and pending owner, the `ProxyAdmin`'s owner (through a hash), and every row's proxy at its
`implNew`. The CTM leg also checks the CTM's and ServerNotifier's holders. The Core leg checks
only the `ProxyAdmin`'s owner, because `_domainHolders` returns early on a zero CTM
(`ProxyUpgradeExecutorBase.sol:114-116`).

## Groups

* **(a) What a successful leg establishes**: `CoreLegChecks`, and exactly that:
  `CoreLegExact`, `CoreLegIgnoresCTMBranch`.
* **The checks are load-bearing**: `CorePAOwnerMoveCaught` (collision-pinned),
  `CorePAOwnerMoveUnderCollisionPasses`, `CorePAOwnerCheckIsLoadBearing`,
  `CoreExecutorOwnerCheckIsLoadBearing`, `CorePendingOwnerCheckIsLoadBearing`,
  `CoreRowsCheckIsLoadBearing`.
* **What the checks do not cover**: `CorePostCheckScopeIsRows` (for every engine),
  `CoreUnnamedAdminMoveAlwaysPasses`, `CoreUnnamedImplMoveAlwaysPasses` (for every default leg
  that passes), and the concrete runs `CoreEngineMovesUnnamedSingletonAdmin`,
  `CoreEngineMovesUnnamedSingletonImpl`.
* **(b) A row proxy whose admin moved**: `CoreRowAdministeredIsAtImplNew`,
  `CoreRowAdminMoveCaught`, `CoreRowAdminMoveReverts` (with a run: `CoreRowAdminMoveRevertsWitness`);
  the answer premise is needed: `CoreRowAdminMoveUncaughtWhenAnswerMatches`.
* **(c) The default engine**: `DefaultCoreLegIsApplyRows`, `DefaultCoreLegOnlyNamedEdges`,
  `DefaultCoreLegReplayIsNoop`, `DefaultCoreLegNeedsOwnedAdmin`, `UnownedReplayRevertsAtV35`; both
  premises are needed: `DefaultLegNeedsAdministeredRows`, `DefaultLegReinitMovesRowAdmin`.
* **(d) Witness**: `CoreLegWitness`.

## What is not claimed

Nothing here says what a reviewed release engine does; the engine is a parameter. The CTM branch
of `_domainHolders` is opaque. Other state of the executor, the `ProxyAdmin` and the proxies is
not modelled (see the modelling choices in the Specs file).
-/

namespace Contracts.ProxyUpgradeExecutorV35.CoreLeg

open Contracts.ProxyUpgradeCurrent (Address Row Impl upd toRows Domain ValidRows Config ApplyRows
  ReinitFrames)

/-! ## (a) What a successful leg establishes -/

/-- **WHAT A SUCCESSFUL CORE LEG ESTABLISHES** (`ProxyUpgradeExecutorBase.sol:48-98` with
`_chainTypeManager = address(0)`). If `applyL1Upgrade(T)` by `caller` succeeds from `W` and ends
in `W'`:
the caller is the executor's owner; the transition and its engine are code and the domain is
`Core`; the engine, run with the Core context (zero CTM, the executor's `ProxyAdmin`), turned `W`
into `W'`; the executor's owner and pending owner are exactly unchanged (`:87-89`); the
`ProxyAdmin`'s owner is unchanged, or it changed to an address whose `keccakOwner` collides with
the old one's (`:90-92`, `:114-116`); the inventory has `L1_ECOSYSTEM_CONTRACT_COUNT` slots; and
every row of `toRows(inventory)`, read through `getProxyImplementation`, answers its `implNew`
(`:93-97`). -/
def Properties.CoreLegChecks : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    applyL1Upgrade X E caller T W = some W' →
      caller = W.owner ∧ X.hasCode T.addr = true ∧ T.manifest.domain = .core ∧
      X.hasCode T.manifest.engine = true ∧
      E T.manifest.engine ⟨T.addr, T.manifest.engine, .core, X.pa, 0⟩ T.manifest.proxyUpgrades W
        = some W' ∧
      W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner ∧
      (W'.paOwner = W.paOwner ∨
        (W'.paOwner ≠ W.paOwner ∧ X.keccakOwner W'.paOwner = X.keccakOwner W.paOwner)) ∧
      T.manifest.proxyUpgrades.length = L1_ECOSYSTEM_CONTRACT_COUNT ∧
      ∀ r ∈ toRows T.manifest.proxyUpgrades, getProxyImplementation X W' r.proxy = some r.implNew

/-- **THE CORE LEG CHECKS EXACTLY THAT.** `applyL1Upgrade` succeeds from `W` with result `W'` if
and only if: the caller is the owner, the transition and engine are code, the domain is `Core`,
the engine run yields `W'`, the executor's owner and pending owner are unchanged, the
`ProxyAdmin` owner's hash is unchanged, the inventory length is right and every row answers its
`implNew`. Nothing else about `W'` is checked: no other proxy's implementation or admin slot. -/
def Properties.CoreLegExact : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    applyL1Upgrade X E caller T W = some W' ↔
      (caller = W.owner ∧ X.hasCode T.addr = true ∧ T.manifest.domain = .core ∧
        X.hasCode T.manifest.engine = true ∧
        E T.manifest.engine ⟨T.addr, T.manifest.engine, .core, X.pa, 0⟩ T.manifest.proxyUpgrades W
          = some W' ∧
        W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner ∧
        X.keccakOwner W'.paOwner = X.keccakOwner W.paOwner ∧
        T.manifest.proxyUpgrades.length = L1_ECOSYSTEM_CONTRACT_COUNT ∧
        RowsAppliedW X W' (toRows T.manifest.proxyUpgrades))

/-- **THE CORE LEG NEVER CONSULTS THE CTM BRANCH.** Changing what the CTM branch of
`_domainHolders` (`ProxyUpgradeExecutorBase.sol:117-138`) and the server-notifier read (`:71-73`)
compute does not change the Core leg's outcome: with a zero CTM only `keccak256(abi.encode(
_proxyAdmin.owner()))` (`:114-116`) is compared. -/
def Properties.CoreLegIgnoresCTMBranch : Prop :=
  ∀ (X : Exec) (h : Address → Address → World → UInt256) (s : Address → World → Address)
    (E : Engines) (caller : Address) (T : TransitionObj) (W : World),
    applyL1Upgrade { X with ctmHolders := h, serverNotifierOf := s } E caller T W =
      applyL1Upgrade X E caller T W

/-! ## Each check is load-bearing -/

/-- **A `ProxyAdmin` OWNERSHIP MOVE IS CAUGHT, UNLESS THE HASHES COLLIDE.** If the engine's run
moves the `ProxyAdmin`'s owner to an address whose `keccakOwner` differs from the old owner's,
the leg reverts. The premise is about that one pair, not injectivity. -/
def Properties.CorePAOwnerMoveCaught : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W M : World),
    E T.manifest.engine ⟨T.addr, T.manifest.engine, .core, X.pa, 0⟩ T.manifest.proxyUpgrades W
      = some M →
    X.keccakOwner M.paOwner ≠ X.keccakOwner W.paOwner →
    applyL1Upgrade X E caller T W = none

/-- **UNDER A COLLISION, A `ProxyAdmin` OWNERSHIP MOVE PASSES.** With an owner hash that
collides on the executor and `9`, a genuine Core transition whose release engine applies its row
and then calls `PROXY_ADMIN.transferOwnership(9)` completes, and the executor no longer owns
the `ProxyAdmin`. So the collision disjunct of `CoreLegChecks` cannot be dropped in this model. -/
def Properties.CorePAOwnerMoveUnderCollisionPasses : Prop :=
  ∃ W', Genuine coreTransition ∧
    applyL1Upgrade wExecCollide (wRelease wExecCollide [.transferPAOwnership 9]) wWorld.owner
      coreTransition wWorld = some W' ∧
    wWorld.paOwner = wExecCollide.self ∧ W'.paOwner = 9 ∧ W'.paOwner ≠ wExecCollide.self

/-- **THE `ProxyAdmin`-OWNER CHECK IS WHAT REJECTS AN OWNERSHIP MOVE.** With the identity hash,
the same release engine's run succeeds and leaves the executor's owner and pending owner
unchanged and the row applied, but moves the `ProxyAdmin`'s owner; the leg reverts. -/
def Properties.CorePAOwnerCheckIsLoadBearing : Prop :=
  ∃ M, releaseEngine wExec [.transferPAOwnership 9] (coreContext wExec coreTransition)
      coreInventory wWorld = some M ∧
    M.owner = wWorld.owner ∧ M.pendingOwner = wWorld.pendingOwner ∧
    RowsAppliedW wExec M (toRows coreInventory) ∧ M.paOwner ≠ wWorld.paOwner ∧
    applyL1Upgrade wExec (wRelease wExec [.transferPAOwnership 9]) wWorld.owner coreTransition
      wWorld = none

/-- **THE EXECUTOR-OWNER CHECK IS LOAD-BEARING** (`:87-89`). A release engine that writes the
executor's owner slot runs successfully, keeps the `ProxyAdmin`'s owner and applies the row; only
the owner check rejects it. -/
def Properties.CoreExecutorOwnerCheckIsLoadBearing : Prop :=
  ∃ M, releaseEngine wExec [.writeOwner 9] (coreContext wExec coreTransition) coreInventory wWorld
      = some M ∧
    M.owner ≠ wWorld.owner ∧ M.pendingOwner = wWorld.pendingOwner ∧ M.paOwner = wWorld.paOwner ∧
    RowsAppliedW wExec M (toRows coreInventory) ∧
    applyL1Upgrade wExec (wRelease wExec [.writeOwner 9]) wWorld.owner coreTransition wWorld = none

/-- **THE PENDING-OWNER CHECK IS LOAD-BEARING** (`:87-89`). As above, for the pending-owner
slot. -/
def Properties.CorePendingOwnerCheckIsLoadBearing : Prop :=
  ∃ M, releaseEngine wExec [.writePendingOwner 9] (coreContext wExec coreTransition) coreInventory
      wWorld = some M ∧
    M.owner = wWorld.owner ∧ M.pendingOwner ≠ wWorld.pendingOwner ∧ M.paOwner = wWorld.paOwner ∧
    RowsAppliedW wExec M (toRows coreInventory) ∧
    applyL1Upgrade wExec (wRelease wExec [.writePendingOwner 9]) wWorld.owner coreTransition wWorld
      = none

/-- **THE ROWS CHECK IS LOAD-BEARING** (`:93-97`). A transition pinning an engine that does
nothing passes the ownership and holder checks, and the leg reverts only because its row's proxy
is not at `implNew`. -/
def Properties.CoreRowsCheckIsLoadBearing : Prop :=
  Genuine coreTransition ∧
    noHook (coreContext wExec coreTransition) coreInventory wWorld = some wWorld ∧
    ¬ RowsAppliedW wExec wWorld (toRows coreInventory) ∧
    applyL1Upgrade wExec wNoop wWorld.owner coreTransition wWorld = none

/-! ## What the checks do not cover -/

/-- **THE CORE LEG SEES THE ENGINE'S RESULT ONLY THROUGH THE OWNERS AND THE ROW PROXIES.** Take
two engines whose runs from `W` end in `M` and `M'`. If `M` and `M'` have the same executor
owner, pending owner and `ProxyAdmin` owner, and the same implementation and admin slot at every
row's proxy, then the leg succeeds with `M` under the first engine exactly when it succeeds with
`M'` under the second. `M` and `M'` may differ arbitrarily in the implementation and admin slot
of every proxy no row names. This is the general form of the two countermodels below. -/
def Properties.CorePostCheckScopeIsRows : Prop :=
  ∀ (X : Exec) (E E' : Engines) (caller : Address) (T : TransitionObj) (W M M' : World),
    E T.manifest.engine ⟨T.addr, T.manifest.engine, .core, X.pa, 0⟩ T.manifest.proxyUpgrades W
      = some M →
    E' T.manifest.engine ⟨T.addr, T.manifest.engine, .core, X.pa, 0⟩ T.manifest.proxyUpgrades W
      = some M' →
    M'.owner = M.owner → M'.pendingOwner = M.pendingOwner → M'.paOwner = M.paOwner →
    (∀ r ∈ toRows T.manifest.proxyUpgrades,
      M'.impl r.proxy = M.impl r.proxy ∧ M'.admin r.proxy = M.admin r.proxy) →
    (applyL1Upgrade X E caller T W = some M ↔ applyL1Upgrade X E' caller T W = some M')

/-- **A HOOK CAN MOVE THE ADMIN OF ANY PROXY NO ROW NAMES.** Suppose a Core leg whose transition
pins `DefaultProxyUpgradeEngine` succeeds from `W` with result `W'`. Take any proxy `p` that no
row names and that the `ProxyAdmin` administers in `W'`, and any nonzero `a`. Then the same leg,
with the engine replaced by a `DefaultProxyUpgradeEngine` subclass whose `_afterSwaps` calls
`PROXY_ADMIN.changeProxyAdmin(p, a)`, also succeeds, and its result is `W'` with `p`'s admin slot
set to `a`. No premise on the reinitializers or on who administers the rows' proxies. -/
def Properties.CoreUnnamedAdminMoveAlwaysPasses : Prop :=
  ∀ (X : Exec) (E E' : Engines) (caller : Address) (T : TransitionObj) (W W' : World)
    (p a : Address),
    E T.manifest.engine = defaultEngine X →
    E' T.manifest.engine = releaseEngine X [.changeProxyAdmin p a] →
    applyL1Upgrade X E caller T W = some W' →
    (∀ r ∈ toRows T.manifest.proxyUpgrades, r.proxy ≠ p) →
    W'.admin p = X.pa → a ≠ 0 →
    applyL1Upgrade X E' caller T W = some { W' with admin := upd W'.admin p a }

/-- **A HOOK CAN MOVE THE IMPLEMENTATION OF ANY PROXY NO ROW NAMES.** As
`CoreUnnamedAdminMoveAlwaysPasses`, with `_afterSwaps` calling `PROXY_ADMIN.upgrade(p, x)` for
any `x` that is code: the leg succeeds and its result is `W'` with `p`'s implementation slot set
to `x`. No source check applies: `x` is not related to `p`'s old implementation or to any row. -/
def Properties.CoreUnnamedImplMoveAlwaysPasses : Prop :=
  ∀ (X : Exec) (E E' : Engines) (caller : Address) (T : TransitionObj) (W W' : World)
    (p x : Address),
    E T.manifest.engine = defaultEngine X →
    E' T.manifest.engine = releaseEngine X [.upgrade p x] →
    applyL1Upgrade X E caller T W = some W' →
    (∀ r ∈ toRows T.manifest.proxyUpgrades, r.proxy ≠ p) →
    W'.admin p = X.pa → X.hasCode x = true →
    applyL1Upgrade X E' caller T W = some { W' with impl := upd W'.impl p x }

/-- **AN UNNAMED ECOSYSTEM SINGLETON'S ADMIN CAN MOVE.** A genuine Core transition whose engine
is `DefaultProxyUpgradeEngine` with an `_afterSwaps` that calls
`PROXY_ADMIN.changeProxyAdmin(6, 9)` completes. Before the leg the `ProxyAdmin` administers every
proxy (the state `CoreUpgradeExecutor.sol:21-22` describes: "admin of every shared singleton
proxy"). Proxy `6` is one no row names; it ends administered by `9`, so that description no
longer holds. Every check of the leg passed. -/
def Properties.CoreEngineMovesUnnamedSingletonAdmin : Prop :=
  ∃ W', Genuine coreTransition ∧ coreTransition.manifest.domain = .core ∧
    applyL1Upgrade wExec (wRelease wExec [.changeProxyAdmin 6 9]) wWorld.owner coreTransition wWorld
      = some W' ∧
    (∀ r ∈ toRows coreTransition.manifest.proxyUpgrades, r.proxy ≠ 6) ∧
    (∀ p, wWorld.admin p = wExec.pa) ∧ W'.admin 6 = 9 ∧ W'.admin 6 ≠ wExec.pa ∧
    W'.paOwner = wWorld.paOwner ∧ W'.owner = wWorld.owner

/-- **AN UNNAMED ECOSYSTEM SINGLETON'S IMPLEMENTATION CAN MOVE OFF-ROW.** As above with
`PROXY_ADMIN.upgrade(7, 13)`: proxy `7`, which no row names, ends at `13`, which no row names
either. Every check of the leg passed. -/
def Properties.CoreEngineMovesUnnamedSingletonImpl : Prop :=
  ∃ W', Genuine coreTransition ∧
    applyL1Upgrade wExec (wRelease wExec [.upgrade 7 13]) wWorld.owner coreTransition wWorld
      = some W' ∧
    (∀ r ∈ toRows coreTransition.manifest.proxyUpgrades, r.proxy ≠ 7 ∧ r.implNew ≠ 13) ∧
    wWorld.impl 7 = 10 ∧ W'.impl 7 = 13 ∧ W'.admin 7 = wExec.pa

/-! ## (b) A row proxy whose admin moved -/

/-- **A ROW PROXY STILL UNDER THE `ProxyAdmin` IS AT ITS `implNew`.** After a successful leg,
a row whose proxy the `ProxyAdmin` still administers has its implementation slot at `implNew`. -/
def Properties.CoreRowAdministeredIsAtImplNew : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    applyL1Upgrade X E caller T W = some W' →
    ∀ r ∈ toRows T.manifest.proxyUpgrades, W'.admin r.proxy = X.pa → W'.impl r.proxy = r.implNew

/-- **A ROW PROXY WHOSE ADMIN MOVED IS CAUGHT, UNLESS ITS CODE ANSWERS `implNew`.** After a
successful leg, a row whose proxy is no longer administered by the `ProxyAdmin` has a current
implementation whose code answers `implementation()` with the row's `implNew`. Equivalently: if
the engine moves a row proxy's admin away and the code then behind it does not answer `implNew`,
`requireRowsApplied` reverts the leg. The answer is the explicit premise of the exception: the
check reads `implementation()` through the proxy's non-admin path
(`TransparentUpgradeableProxy.sol:84-107`). No premise about the admin before the leg is needed. -/
def Properties.CoreRowAdminMoveCaught : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    applyL1Upgrade X E caller T W = some W' →
    ∀ r ∈ toRows T.manifest.proxyUpgrades, W'.admin r.proxy ≠ X.pa →
      X.implAnswer (W'.impl r.proxy) r.proxy = some r.implNew

/-- **AN ENGINE THAT MOVES A ROW PROXY'S ADMIN REVERTS THE LEG, UNLESS THE CODE ANSWERS
`implNew`.** The same fact as a revert. If the engine's run from `W` ends in `M`, some row's
proxy is not administered by the `ProxyAdmin` in `M`, and the code at that proxy's implementation
in `M` does not answer `implementation()` with the row's `implNew` (it reverts or answers
something else), then `applyL1Upgrade` reverts (`ProxyUpgradeRowLib.sol:128-136`). The third
hypothesis is the explicit premise; `CoreRowAdminMoveUncaughtWhenAnswerMatches` shows it cannot
be dropped. -/
def Properties.CoreRowAdminMoveReverts : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W M : World),
    E T.manifest.engine ⟨T.addr, T.manifest.engine, .core, X.pa, 0⟩ T.manifest.proxyUpgrades W
      = some M →
    ∀ r ∈ toRows T.manifest.proxyUpgrades, M.admin r.proxy ≠ X.pa →
      X.implAnswer (M.impl r.proxy) r.proxy ≠ some r.implNew →
      applyL1Upgrade X E caller T W = none

/-- **`CoreRowAdminMoveReverts` HAS A RUN, AND THE CHECK READS THE ANSWER, NOT THE SLOT.** A
genuine Core transition with a release engine whose `_afterSwaps` calls
`PROXY_ADMIN.changeProxyAdmin(5, 9)` on its own row's proxy. The engine's run succeeds: it leaves
the executor's owner and pending owner and the `ProxyAdmin`'s owner unchanged, and proxy `5`'s
implementation slot IS the row's `implNew`. But `5` is no longer administered by the `ProxyAdmin`
and the code at `11` does not answer `implementation()`, so `requireRowsApplied` reverts the leg.
Only the rows check rejects this run. -/
def Properties.CoreRowAdminMoveRevertsWitness : Prop :=
  ∃ M, Genuine coreTransition ∧
    wRelease wExec [.changeProxyAdmin 5 9] coreTransition.manifest.engine
      (coreContext wExec coreTransition) coreTransition.manifest.proxyUpgrades wWorld = some M ∧
    coreRow ∈ toRows coreTransition.manifest.proxyUpgrades ∧
    wWorld.admin coreRow.proxy = wExec.pa ∧ M.admin coreRow.proxy ≠ wExec.pa ∧
    M.impl coreRow.proxy = coreRow.implNew ∧
    wExec.implAnswer (M.impl coreRow.proxy) coreRow.proxy ≠ some coreRow.implNew ∧
    M.owner = wWorld.owner ∧ M.pendingOwner = wWorld.pendingOwner ∧ M.paOwner = wWorld.paOwner ∧
    applyL1Upgrade wExec (wRelease wExec [.changeProxyAdmin 5 9]) wWorld.owner coreTransition wWorld
      = none

/-- **THE ANSWER PREMISE OF `CoreRowAdminMoveCaught` IS NEEDED.** A genuine Core transition with
a release engine whose `_afterSwaps` calls `PROXY_ADMIN.upgrade(5, 12)` and then
`PROXY_ADMIN.changeProxyAdmin(5, 9)` completes, where implementation `12` answers
`implementation()` with `11`. Row proxy `5`, administered by the `ProxyAdmin` before, ends
administered by `9` and running `12`, not the row's `implNew` `11`, and the leg's
`requireRowsApplied` passed. Read literally, the NatSpec "verifies every row at its `implNew`"
(`ICoreUpgradeExecutor.sol:15-16`) and "Reverts unless every row's proxy runs its `implNew`"
(`ProxyUpgradeRowLib.sol:125`) do not hold of this run: what is verified is the answer to
`implementation()`, which is the implementation slot only while the `ProxyAdmin` administers
the proxy (`CoreRowAdministeredIsAtImplNew`). -/
def Properties.CoreRowAdminMoveUncaughtWhenAnswerMatches : Prop :=
  ∃ W', Genuine coreTransition ∧
    applyL1Upgrade wExecSpoof (wRelease wExecSpoof [.upgrade 5 12, .changeProxyAdmin 5 9])
      wWorld.owner coreTransition wWorld = some W' ∧
    coreRow ∈ toRows coreTransition.manifest.proxyUpgrades ∧
    wWorld.admin coreRow.proxy = wExecSpoof.pa ∧ W'.admin coreRow.proxy ≠ wExecSpoof.pa ∧
    W'.impl coreRow.proxy ≠ coreRow.implNew ∧
    wExecSpoof.implAnswer (W'.impl coreRow.proxy) coreRow.proxy = some coreRow.implNew

/-! ## (c) The default engine -/

/-- **WITH THE DEFAULT ENGINE, THE CORE LEG IS `RowsCurrent.ApplyRows`.** If the transition pins
`DefaultProxyUpgradeEngine`, the `ProxyAdmin` administers every row's proxy before the leg, and
no reinitializer writes an admin slot, then the leg succeeds with result `W'` if and only if:
the caller is the owner, the transition and engine are code, the domain is `Core`, the executor
owns the `ProxyAdmin`, the inventory has `L1_ECOSYSTEM_CONTRACT_COUNT` slots,
`RowsCurrent.ApplyRows` relates the implementation mappings over `toRows(inventory)` under the
executor's configuration, and `W'` differs from `W` only in the implementation mapping. -/
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
transition's are) and reinitializers that move at most their own proxy's implementation: after a
successful leg, no admin slot changed, the `ProxyAdmin`'s owner and the executor's owner and
pending owner are unchanged, and every proxy is where it was or went from some row's
`expectedOldImpl` to that row's `implNew`. This is `ProxyUpgradeCurrent.OnlyNamedEdgesAcrossCall`,
carried over to the Core leg. -/
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

/-- **WITH THE DEFAULT ENGINE, APPLYING A CORE TRANSITION AGAIN CHANGES NOTHING.** Under the
premises of `DefaultCoreLegIsApplyRows`: if the leg succeeds from `W` with result `W'`, the same
call from `W'` succeeds with result `W'`. This is the replay
`DefaultProxyUpgradeEngine.sol:20-23` describes ("a transition can be applied again (every row
already installed)"), for the engine with empty hooks. -/
def Properties.DefaultCoreLegReplayIsNoop : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W W' : World),
    E T.manifest.engine = defaultEngine X →
    (∀ r ∈ toRows T.manifest.proxyUpgrades, W.admin r.proxy = X.pa) →
    ReinitKeepsAdmins X →
    applyL1Upgrade X E caller T W = some W' →
    applyL1Upgrade X E caller T W' = some W'

/-- **WITH THE DEFAULT ENGINE, AN EXECUTOR THAT DOES NOT OWN THE `ProxyAdmin` CANNOT COMPLETE A
CORE LEG** (`DefaultProxyUpgradeEngine.sol:34-37`). No other premise: this holds also when every
row is already at its `implNew`. -/
def Properties.DefaultCoreLegNeedsOwnedAdmin : Prop :=
  ∀ (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W : World),
    E T.manifest.engine = defaultEngine X → W.paOwner ≠ X.self →
    applyL1Upgrade X E caller T W = none

/-- **THE OWNERSHIP CONJUNCT OF `DefaultCoreLegIsApplyRows` DOES NOT FOLLOW FROM `ApplyRows`.**
Proxy `5` is already at the row's `implNew` and `7`, not the executor, owns the `ProxyAdmin`.
`RowsCurrent.ApplyRows` holds from that state to itself (every row skips; at `e561b9cc2` the
library let such a replay through, `ProxyUpgradeCurrent.UnownedAdminMovesNothing`), and the
`d9f678900` leg with the default engine reverts. -/
def Properties.UnownedReplayRevertsAtV35 : Prop :=
  ∃ W : World, Genuine coreTransition ∧ W.paOwner ≠ wExec.self ∧
    (∀ r ∈ toRows coreTransition.manifest.proxyUpgrades, W.admin r.proxy = wExec.pa) ∧
    ApplyRows (rowsConfig wExec W) W.impl (toRows coreTransition.manifest.proxyUpgrades) W.impl ∧
    applyL1Upgrade wExec (wDefault wExec) W.owner coreTransition W = none

/-- **THE ADMINISTRATION PREMISE OF `DefaultCoreLegIsApplyRows` IS NEEDED.** Row proxy `5` is
administered by `8`, not the `ProxyAdmin`, and runs `12`, which answers `implementation()` with
`11`. The default engine reads `11`, skips the row as already applied, and the leg completes
without changing anything; but proxy `5` is not at `11`, so `RowsCurrent.ApplyRows` does not
hold. -/
def Properties.DefaultLegNeedsAdministeredRows : Prop :=
  Genuine coreTransition ∧
    applyL1Upgrade wExecSpoof (wDefault wExecSpoof) wWorldForeign.owner coreTransition wWorldForeign
      = some wWorldForeign ∧
    wWorldForeign.admin coreRow.proxy ≠ wExecSpoof.pa ∧
    wWorldForeign.impl coreRow.proxy ≠ coreRow.implNew ∧
    ¬ ApplyRows (rowsConfig wExecSpoof wWorldForeign) wWorldForeign.impl
      (toRows coreTransition.manifest.proxyUpgrades) wWorldForeign.impl

/-- **THE `ReinitKeepsAdmins` PREMISE OF `DefaultCoreLegIsApplyRows` IS NEEDED.** A genuine Core
transition pins the default engine, and its one row sets `callInitializeUpgrade`. The
`ProxyAdmin` administers the row's proxy `5` before the leg. The reinitializer of `11`, running
in proxy `5`'s storage, hands that proxy's admin slot to `9`. If `11` answers `implementation()`
with `11`, the leg completes: proxy `5` is at `11` and no longer administered by the
`ProxyAdmin`, so the conclusion `W' = { W with impl := W'.impl }` fails. If `11` does not answer
`implementation()`, the same leg reverts, already in `applyRows`' own `requireRowsApplied`
(`ProxyUpgradeRowLib.sol:122`). So with the default engine too, what catches a row proxy leaving
the `ProxyAdmin` is the answer of the code behind it. -/
def Properties.DefaultLegReinitMovesRowAdmin : Prop :=
  ∃ W', Genuine coreTransitionInit ∧
    wDefault wExecReinit coreTransitionInit.manifest.engine = defaultEngine wExecReinit ∧
    (∀ r ∈ toRows coreTransitionInit.manifest.proxyUpgrades,
      wWorld.admin r.proxy = wExecReinit.pa) ∧
    ¬ ReinitKeepsAdmins wExecReinit ∧
    applyL1Upgrade wExecReinit (wDefault wExecReinit) wWorld.owner coreTransitionInit wWorld
      = some W' ∧
    W'.impl 5 = coreRowInit.implNew ∧ W'.admin 5 = 9 ∧ W'.admin 5 ≠ wExecReinit.pa ∧
    W' ≠ { wWorld with impl := W'.impl } ∧
    applyL1Upgrade wExecReinitSilent (wDefault wExecReinitSilent) wWorld.owner coreTransitionInit
      wWorld = none

/-! ## (d) Witness -/

/-- **A GENUINE CORE TRANSITION APPLIES WITH THE DEFAULT ENGINE.** The premise bundles of
`DefaultCoreLegIsApplyRows` and `DefaultCoreLegOnlyNamedEdges` hold together: a genuine Core
transition pinning the default engine, an executor that owns the `ProxyAdmin`, which administers
the row's proxy, and reinitializers that write no admin slot and move at most their own proxy's
implementation. Governance's call succeeds, moves proxy `5` from `10` to `11`, and leaves the
unnamed singletons `6` and `7` alone. -/
def Properties.CoreLegWitness : Prop :=
  ∃ W', Genuine coreTransition ∧ coreTransition.manifest.domain = .core ∧
    wDefault wExec coreTransition.manifest.engine = defaultEngine wExec ∧
    wWorld.paOwner = wExec.self ∧
    (∀ r ∈ toRows coreTransition.manifest.proxyUpgrades, wWorld.admin r.proxy = wExec.pa) ∧
    ReinitKeepsAdmins wExec ∧
    (toRows coreTransition.manifest.proxyUpgrades).Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    ReinitFrames (rowsConfig wExec wWorld) ∧
    applyL1Upgrade wExec (wDefault wExec) wWorld.owner coreTransition wWorld = some W' ∧
    wWorld.impl 5 = coreRow.expectedOldImpl ∧ W'.impl 5 = coreRow.implNew ∧
    coreRow.expectedOldImpl ≠ coreRow.implNew ∧ W'.impl 6 = wWorld.impl 6 ∧
    W'.impl 7 = wWorld.impl 7 ∧ W'.admin = wWorld.admin

end Contracts.ProxyUpgradeExecutorV35.CoreLeg
