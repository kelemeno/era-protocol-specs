import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorForward

/-!
# Model: `applyInfrastructureUpgrade` at `draft/v0.35.0`, which delegatecalls the engine a transition names

Source: matter-labs/era-contracts branch `draft/v0.35.0` at commit **`b17415d20`**
(`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`, 2026-11-16). It contains #2654 (`95b5c469d`, the
pinned engine) and #2669 (`9775be946`). Paths are relative to `l1-contracts/contracts/`, and
every `file:line` below is at `b17415d20` unless another commit is named. This file was first
written against `d9f6789` (2026-11-06) and then re-read at `b17415d20`; the section "Re-read at
`b17415d20`" lists what changed in the code it models.

The rest of this folder is pinned to `feat/upgrade-simplification` at `e561b9cc2`. This file
extends the `ExecutorForward` model (`Specs/ExecutorForward.lean`, at `e561b9cc2`), which it
imports unchanged, and reuses the row library model `ProxyUpgradeCurrent` (`e561b9cc2`).
`RowsCurrent`'s transcription of `applyRows` matches `b17415d20`'s `applyRows` and
`requireRowsApplied` (`upgrades/registry/libraries/ProxyUpgradeRowLib.sol:106-128, 133-141`);
the second loop has moved into `requireRowsApplied`. The CTM, its chains and its release and
transition objects are `ExecutorForward`'s `e561b9cc2` model and were not re-read at
`b17415d20`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.ExecutorEngineAtV35` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorEngineAtV35`. The namespace is
`Contracts.ChainTypeManager.ExecutorEngineAtV35`.

## What changed since `e561b9cc2`

At `e561b9cc2`, `applyInfrastructureUpgrade(T)` ran `ProxyUpgradeRowLib.applyTransition`:
code and `domain()` checks on `T`, then `applyRows(CTM_PROXY_ADMIN, T.rows())`. That
function is deleted. Now (`upgrades/registry/executors/CTMUpgradeExecutor.sol:64-72`):

    function applyInfrastructureUpgrade(IProxyUpgradeTransition _infrastructureTransition) external onlyOwner {
        _applyProxyUpgradeTransition(CTM_PROXY_ADMIN, _infrastructureTransition, ProxyUpgradeDomain.CTM,
            address(CHAIN_TYPE_MANAGER));
        emit CTMInfrastructureUpgradeApplied(address(_infrastructureTransition));
    }

and `_applyProxyUpgradeTransition` (`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:51-104`):

    ObjectAnchorLib.requireCode(address(_transition));                                   // :57
    ProxyUpgradeTransitionManifest memory manifest = _transition.getManifest();         // :58
    if (manifest.domain != _domain) { revert ProxyUpgradeDomainMismatch(...); }         // :59-61
    ObjectAnchorLib.requireCode(manifest.proxyUpgradeEngine);                           // :63
    ProxyUpgradeContext memory context = ProxyUpgradeContext({...});                    // :65-71
    if (_chainTypeManager != address(0) &&
        IChainTypeManager(_chainTypeManager).admin() == address(_proxyAdmin)) {
        revert ProxyUpgradeCTMAdminIsProxyAdmin(_chainTypeManager); }                  // :75-77
    address ownerBefore = owner();                                                      // :78
    address pendingOwnerBefore = pendingOwner();                                        // :79
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager);       // :80
    (bool success, bytes memory returnData) = manifest.proxyUpgradeEngine.delegatecall(
        abi.encodeCall(IProxyUpgradeEngine.executeUpgrade, (context, manifest.proxyUpgrades))); // :82-84
    if (!success) { assembly { revert(add(returnData, 0x20), mload(returnData)) } }    // :85-91
    if (owner() != ownerBefore || pendingOwner() != pendingOwnerBefore) {
        revert ProxyUpgradeEngineChangedExecutorOwnership(manifest.proxyUpgradeEngine); } // :93-95
    if (_domainHolders(_proxyAdmin, _chainTypeManager) != domainHoldersBefore) {
        revert ProxyUpgradeEngineMovedDomainAuthority(manifest.proxyUpgradeEngine); }    // :96-98
    ProxyUpgradeRow[] memory rows = ProxyUpgradeRowLib.toRows(manifest.proxyUpgrades,
        ProxyUpgradeRowLib.inventoryLength(_domain));                                   // :99-102
    ProxyUpgradeRowLib.requireRowsApplied(_proxyAdmin, rows);                           // :103

In the CTM domain `_domainHolders` (`:118-148`) reads the CTM's `serverNotifierAddress()`
(`:123`) and returns `keccak256(abi.encode(...))` of the `ProxyAdmin`'s `owner()`, the CTM's
`owner()`, `pendingOwner()` and `admin()`, `getProxyAdmin(ctm)` and that notifier address
(`:124-133`). If the notifier address is nonzero it hashes that value again with the notifier's
`owner()`, `pendingOwner()`, `getProxyAdmin(notifier)` and `chainTypeManager()` (`:134-147`).

**Which engine runs.** The transition object names it. `ProxyUpgradeTransition`'s
constructor only requires it to be nonzero
(`upgrades/registry/objects/ProxyUpgradeTransition.sol:39-41`), and the executor only
requires it to have code (`ProxyUpgradeExecutorBase.sol:63`). The only engine in the tree is
`DefaultProxyUpgradeEngine` (`upgrades/registry/engines/DefaultProxyUpgradeEngine.sol:32-47`):

    ProxyAdmin proxyAdmin = ProxyAdmin(_context.proxyAdmin);
    address proxyAdminOwner = proxyAdmin.owner();
    if (proxyAdminOwner != address(this)) { revert ProxyUpgradeEngineAuthorityMismatch(...); } // :33-37
    _beforeSwaps(_context, _inventory);                                                 // :40
    ProxyUpgradeRowLib.applyRows(proxyAdmin,
        ProxyUpgradeRowLib.toRows(_inventory, ProxyUpgradeRowLib.inventoryLength(_context.domain))); // :41-44
    _afterSwaps(_context, _inventory);                                                  // :45
    _checkPostconditions(_context, _inventory);                                         // :46

`_inventory` is calldata, and each of the four uses converts it into a fresh memory copy
(`:38-39`), so the rows `applyRows` applies are the manifest's whatever a hook does with its
own copy. The three hooks are empty `internal virtual` functions (`:52`, `:57`, `:63-66`) that a
release's subclass overrides with its follow-up calls. `executeUpgrade` itself is not virtual.
Under the delegatecall `address(this)` is the executor, so the first check is "the executor
owns its `ProxyAdmin`".

**What an engine can do.** It runs with the executor's storage and authority
(`IProxyUpgradeEngine.sol:10-21`; `ProxyUpgradeExecutorBase.sol:34-41`). The executor owns
the CTM and the CTM domain's `ProxyAdmin` (`CTMUpgradeExecutor.sol:20-22`, `:38-40`), so an
engine can make every call a `forward` can make to them
(`governance/UpgradeExecutorBase.sol:35-55`), including the CTM's break-glass
`executeUpgrade` (`state-transition/ChainTypeManager.sol:626-628`, `onlyOwner`) and
`ProxyAdmin.upgrade`/`upgradeAndCall` of any proxy the admin administers, the CTM's own
included. The repository's documentation says the same: "every `forward` cell below holds for
it too", except the holder changes the post-check refuses (`docs/registry-driven-upgrades.md:473-478`,
repository root), and the engine "can still rewrite the storage of any proxy under its
`ProxyAdmin` ... so that rests on the engine's review" (`:262-264`).

**What the executor checks** is exactly the list above: before the engine runs, that the CTM's
`admin()` is not its `ProxyAdmin`; afterwards, its own `owner` and `pendingOwner`, the
domain-holders hash, and every row at its `implNew`. Its NatSpec: "Anything else the engine does
is what governance reviewed when it approved the transition, and the engine's own
postconditions" (`ProxyUpgradeExecutorBase.sol:40-41`).

**What governance must check** of the engine is named here as two premises. `EngineIsTame`
(the engine makes no break-glass cut and does not move the CTM proxy) is what the CTM's
invariants need. `EngineReviewed` (the engine runs `DefaultProxyUpgradeEngine`'s core on the
manifest's rows, and its hooks make only CTM calls that are not break-glass cuts) is what the
row library's source check needs; for rows that do not name the CTM proxy it implies
`EngineIsTame`. `DefaultProxyUpgradeEngine` meets both.

## Re-read at `b17415d20`

`git diff d9f6789 b17415d20` changes the modelled code in four places; the model follows
`b17415d20`.

* The pre-check on the CTM's `admin()` (`ProxyUpgradeExecutorBase.sol:72-77`) is new: a step
  premise on the start state.
* `_domainHolders` hashed seven values at `d9f6789`. It now also hashes the CTM's `admin()`,
  its notifier address and the notifier's `chainTypeManager()`, and it reads the notifier
  address on each call instead of once before the engine (`:118-148`). `DomainHolders` has the
  ten values.
* `DefaultProxyUpgradeEngine.executeUpgrade` passes each hook and `toRows` its own copy of the
  calldata inventory (`:38-46`); at `d9f6789` the four uses shared one memory copy (`:38-45`
  there). `EngineCore` applies the manifest's rows, as `b17415d20` does.
* `UpgradeExecutorBase.forward` now requires code at the target of every call that carries
  calldata (`governance/UpgradeExecutorBase.sol:39-44`). Every modelled forwarded call goes to
  the CTM proxy or to `CTM_PROXY_ADMIN`, which the model takes to hold code, so
  `ExecutorForward`'s `forward` step is used unchanged.

In the other cited files only comments changed and lines moved (`ProxyUpgradeRowLib.sol` by 5,
`upgrades/registry/RegistryTypes.sol` by 2), and the interfaces gained the getters
`_domainHolders` now reads (`state-transition/IChainTypeManager.sol:93`,
`governance/IServerNotifier.sol:42`). `CTMUpgradeExecutor.sol`, `ICTMUpgradeExecutor.sol`,
`ProxyUpgradeTransition.sol` and `ObjectAnchorLib.sol` are unchanged since `d9f6789`.

## Modelling choices

* **State** (`V35State`): `ExecutorForward`'s `XState` (the CTM, its chains, the CTM domain's
  implementations), plus the executor's own `owner()` and `pendingOwner()`, plus the ten values
  `_domainHolders` reads. The latter two are **ghosts**: only the executor's checks read them.
  As in `ExecutorForward`, the `ProxyAdmin`'s owner that the row library reads is the fixed
  configuration `XConfig.rc.adminOwner`, ownership and admin transfers through `forward` are not
  modelled, and so no other step changes the ghosts. The ghost `proxyAdminOwner` is not tied to
  `rc.adminOwner`.
* **A transition object** (`V35Transition`) is its address and its manifest as
  `getManifest()` returns it (`ProxyUpgradeExecutorBase.sol:58`): domain, inventory and engine
  address. `getManifest()` is `view` and is read once, so this describes any object, genuine
  or not. Its rows are `toRows(inventory)` (`ProxyUpgradeRowLib.sol:58-66`); the length check
  in `toRows` (`:62-64`) is the step premise `inventory.length = inventoryLength(CTM)`.
* **An engine** (`EngineCode`) is what the code at an address does when the executor
  delegatecalls `executeUpgrade` on it for a given transition: a relation from start states to
  end states, with no end state for a revert. `V35Config.code` gives the code at every
  address. Nothing constrains it: every engine governance could approve is covered.
* **The engines of the witnesses** are built from `ExecutorForward`'s forwarded calls
  (`FCall`): what an engine does to the modelled state is a sequence of calls the executor
  makes. `EngineCore` is `DefaultProxyUpgradeEngine.executeUpgrade` between its hooks, with
  the CTM's version state unknown afterwards if the rows moved the CTM proxy, exactly as in
  `XStep.infra`. These engines leave the executor's `owner` and `pendingOwner` alone. What their
  swaps and reinitializers do to the domain holders is not modelled, so the holders are left
  arbitrary and the executor's check filters. Two witness engines write the ghosts, to exercise
  the ownership and holders post-checks, and a third moves a row's proxy after the swaps, to
  exercise the rows post-check.
* **The hash** `_domainHolders` returns, both `keccak256` calls and the branch on the notifier
  address together, is `V35Config.holdersHash`, an arbitrary function of the ten values: no
  property of keccak is assumed. Where a result depends on the holders being unchanged, it says
  "unchanged, or `holdersHash` collides on the logged pair (before, after)". When the notifier
  address is zero the four notifier values are not read, so such a pair can differ in them
  alone without any keccak collision.
* **The other entry points** (`applyCTMUpgrade`, `upgradeChain`, `forward`) and the other
  actors are `ExecutorForward`'s steps, unchanged. The bodies of the first two at `b17415d20`
  (`CTMUpgradeExecutor.sol:77-121`) do what `ExecutorForward` quotes from `e561b9cc2`; for
  `forward`, see above.
* **Reject-only checks.** `_checkPostconditions` (a `view` hook) only rejects and is omitted.
  The `onlyOwner` caller check is omitted, as in `ExecutorForward`. So is the revert of
  `_domainHolders` when the notifier has left the `ProxyAdmin` (`:112-114`). Calls an engine
  makes that touch no modelled state (the notifier's setters, `setValidatorTimelockPostV29`,
  events) are not represented: in the model they are no-ops.
-/

namespace Contracts.ChainTypeManager.ExecutorEngineAtV35

open Clear

/-! ## Transition objects -/

/-- A `ProxyUpgradeTransition` as the executor reads it: its address and its manifest
(`ProxyUpgradeTransitionManifest`, `upgrades/registry/RegistryTypes.sol:205-209`), read once
through `getManifest()` (`ProxyUpgradeExecutorBase.sol:58`). -/
structure V35Transition where
  /-- The object's address. -/
  addr : Address
  /-- `manifest.domain`. -/
  domain : ProxyUpgradeCurrent.Domain
  /-- `manifest.proxyUpgrades`: the enum-indexed inventory, inert slots included. -/
  inventory : List ProxyUpgradeCurrent.Row
  /-- `manifest.proxyUpgradeEngine`: the code the executor delegatecalls. -/
  engine : Address

/-- The rows: `toRows(manifest.proxyUpgrades, inventoryLength(domain))`
(`ProxyUpgradeExecutorBase.sol:99-102`; `DefaultProxyUpgradeEngine.sol:41-44` computes the
same list). The length check is a separate step premise. -/
def V35Transition.rows (T : V35Transition) : List ProxyUpgradeCurrent.Row :=
  ProxyUpgradeCurrent.toRows T.inventory

/-- The same object as the `e561b9cc2` executor read it, through `domain()` and `rows()`. -/
def V35Transition.toCurrent (T : V35Transition) : ProxyUpgradeCurrent.Transition :=
  ⟨T.addr, T.domain, T.rows⟩

/-- **A GENUINE `ProxyUpgradeTransition`.** What its constructor establishes
(`ProxyUpgradeTransition.sol:27-42`): the inventory has the domain's length (`toRows`,
`:28-31`), at least one row participates (`:34-36`), the rows pass `validateRows` (`:37`) and
the engine is nonzero (`:39-41`). Nothing is established about the engine's code. `n` is
`inventoryLength(T.domain)`. -/
def V35Transition.Genuine (n : ℕ) (T : V35Transition) : Prop :=
  T.inventory.length = n ∧ T.rows ≠ [] ∧ ProxyUpgradeCurrent.ValidRows T.rows ∧ T.engine ≠ 0

/-! ## State -/

/-- The ten values `_domainHolders` reads in the CTM domain
(`ProxyUpgradeExecutorBase.sol:118-148`). The last four are read only when `serverNotifier` is
nonzero (`:134-136`). -/
structure DomainHolders where
  /-- `_proxyAdmin.owner()` (`:126`). -/
  proxyAdminOwner : Address
  /-- The CTM's `owner()` (`:127`). -/
  ctmOwner : Address
  /-- The CTM's `pendingOwner()` (`:128`). -/
  ctmPendingOwner : Address
  /-- The CTM's `admin()` (`:129`; `state-transition/ChainTypeManager.sol:113`). -/
  ctmAdmin : Address
  /-- `_proxyAdmin.getProxyAdmin(ctm)` (`:130`). -/
  ctmProxyAdmin : Address
  /-- The CTM's `serverNotifierAddress()` (`:123`, `:131`). -/
  serverNotifier : Address
  /-- The notifier's `owner()` (`:142`). -/
  notifierOwner : Address
  /-- The notifier's `pendingOwner()` (`:143`). -/
  notifierPendingOwner : Address
  /-- `_proxyAdmin.getProxyAdmin(serverNotifier)` (`:144`). -/
  notifierProxyAdmin : Address
  /-- The notifier's `chainTypeManager()` (`:145`). -/
  notifierCtm : Address
deriving DecidableEq

/-- The executor model's state, plus what the executor reads around the delegatecall. -/
structure V35State where
  /-- The CTM, its chains and the CTM domain's implementations (`ExecutorForward`). -/
  x : XState
  /-- Ghost: the executor's `owner()` (`Ownable2Step`, the executor's own storage). -/
  owner : Address
  /-- Ghost: the executor's `pendingOwner()`. -/
  pendingOwner : Address
  /-- Ghost: the domain holders. -/
  holders : DomainHolders

/-! ## Engines -/

/-- What code does when the executor delegatecalls `executeUpgrade(context, inventory)` on it
(`ProxyUpgradeExecutorBase.sol:82-84`) to apply a transition: the end states it can reach from
a start state. A revert has no end state. The context is built from the executor's bindings
and the transition (`:65-71`), so the transition determines it. -/
abbrev EngineCode := V35Transition → V35State → V35State → Prop

/-- `DefaultProxyUpgradeEngine.executeUpgrade` between its hooks
(`DefaultProxyUpgradeEngine.sol:33-44`): the executor must own its `ProxyAdmin`, then
`applyRows(proxyAdmin, toRows(inventory))` on the manifest's inventory, which is
`ProxyUpgradeCurrent.ApplyRows` (code check, the source-checked loop and the verification
pass). If the rows moved the CTM proxy, the CTM runs other code afterwards and its version
state is unknown, as in `XStep.infra`. -/
inductive EngineCore (X : XConfig) (T : V35Transition) : XState → XState → Prop
  | mk {x : XState} {J : ProxyUpgradeCurrent.Impl} {c' : CTM} :
      X.rc.adminOwner = X.rc.self →
      ProxyUpgradeCurrent.ApplyRows X.rc x.impl T.rows J →
      (J X.ctmProxy = x.impl X.ctmProxy → c' = x.sys.ctm) →
      EngineCore X T x ⟨{ x.sys with ctm := c' }, J⟩

/-- **`DefaultProxyUpgradeEngine`**, the genuine row engine: its core with the empty hooks. It
has no storage of its own and writes none of the executor's
(`DefaultProxyUpgradeEngine.sol:25-26`). What the swaps and reinitializers do to the domain
holders is not modelled: any value. -/
def defaultEngine (X : XConfig) : EngineCode := fun T s s' =>
  EngineCore X T s.x s'.x ∧ s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner

/-- A `DefaultProxyUpgradeEngine` subclass whose `_beforeSwaps` makes the calls `pre` and whose
`_afterSwaps` makes the calls `post`, each sent by the executor (the engine runs as the
executor). The core applies the manifest's rows whatever the hooks do with their copies of the
inventory. Holders as in `defaultEngine`. The calls are fixed lists: this is a family of witness
engines, not every subclass (a real hook may choose its calls from the live state). -/
def subclassEngine (X : XConfig) (pre post : List FCall) : EngineCode := fun T s s' =>
  (∃ x₁ x₂, FRun X s.x pre x₁ ∧ EngineCore X T x₁ x₂ ∧ FRun X x₂ post s'.x) ∧
    s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner

/-- An engine that is not built on `DefaultProxyUpgradeEngine`: it makes the calls `calls` and
nothing else; in particular it never runs `applyRows`. Holders as in `defaultEngine`. -/
def callingEngine (X : XConfig) (calls : List FCall) : EngineCode := fun _ s s' =>
  FRun X s.x calls s'.x ∧ s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner

/-- A hook call a release review can admit: a CTM call that is not a break-glass cut. Not
`ProxyAdmin.upgrade`/`upgradeAndCall` on any proxy (the CTM's included), and not the CTM's
`executeUpgrade`. Calls that touch no modelled state are not represented at all. The label set
is `ExecutorForward`'s `FCall.sys`, an over-approximation of the CTM calls the executor can
make: it admits every `ChainRouting` label that is not an `arbitraryCut`, including steps the
executor does not make (for example `genesis` and `migrateIn`). A larger set makes
`EngineReviewed` a weaker premise, so the results that assume it only get stronger. -/
def ReviewedHookCall : FCall → Prop
  | .sys l => ¬ l.isArbitrary
  | _ => False

/-- A hook run: some calls the executor makes, each a `ReviewedHookCall`. -/
def HookRun (X : XConfig) (x x' : XState) : Prop :=
  ∃ cs : List FCall, (∀ c ∈ cs, ReviewedHookCall c) ∧ FRun X x cs x'

/-! ## Configuration -/

/-- The `b17415d20` executor. -/
structure V35Config where
  /-- The `ExecutorForward` executor: the world, the row library's configuration (`self` is the
  executor, `adminOwner` the `ProxyAdmin`'s owner), the CTM proxy. -/
  base : XConfig
  /-- `address(CTM_PROXY_ADMIN)` (`CTMUpgradeExecutor.sol:40`), which the pre-check compares
  with the CTM's `admin()`. -/
  proxyAdmin : Address
  /-- `ProxyUpgradeRowLib.inventoryLength(domain)` (`ProxyUpgradeRowLib.sol:47-49`):
  `CTM_CONTRACT_COUNT` for the CTM domain. -/
  inventoryLength : ProxyUpgradeCurrent.Domain → ℕ
  /-- The code at every address, as an engine. -/
  code : Address → EngineCode
  /-- What `_domainHolders` returns, as a function of the ten values it reads: an arbitrary
  function. -/
  holdersHash : DomainHolders → UInt256

/-- The transition pins `DefaultProxyUpgradeEngine`: the code at its engine address is the
genuine row engine. -/
def EngineIsDefault (X : V35Config) (T : V35Transition) : Prop :=
  X.code T.engine = defaultEngine X.base

/-- **WHAT GOVERNANCE MUST CHECK OF THE ENGINE, FOR SOURCE-CHECKED SWAPS.** Every leg the
engine's code can run for this transition is, on the modelled state, a `_beforeSwaps` hook run,
then `DefaultProxyUpgradeEngine`'s core on the manifest's rows, then an `_afterSwaps` hook run,
where the hooks make only CTM calls that are not break-glass cuts. So the review must establish:

* the engine executes `DefaultProxyUpgradeEngine.executeUpgrade` (the admin-owner check and
  `applyRows` on exactly `toRows(inventory)`), not swaps of its own; for a subclass of it the
  code fixes this (`executeUpgrade` is not virtual, and each hook gets its own inventory copy);
* no hook calls `ProxyAdmin.upgrade`/`upgradeAndCall`, on any proxy, the CTM's own included;
* no hook calls the CTM's `executeUpgrade` (a break-glass cut of a chain).

The executor checks none of these (`ProxyUpgradeExecutorBase.sol:92-103`). It does check its own
ownership and the domain holders; the condition says nothing about them. For a transition whose
rows do not name the CTM proxy, this condition implies `EngineIsTame` below, which is all the
CTM's invariants need. -/
def EngineReviewed (X : V35Config) (T : V35Transition) : Prop :=
  ∀ s s', X.code T.engine T s s' →
    ∃ x₁ x₂, HookRun X.base s.x x₁ ∧ EngineCore X.base T x₁ x₂ ∧ HookRun X.base x₂ s'.x

/-! ## Steps -/

/-- What happens at `b17415d20`. -/
inductive V35Label
  /-- `applyInfrastructureUpgrade(T)`. -/
  | infra (T : V35Transition)
  /-- `applyCTMUpgrade(t)`. -/
  | commit (t : Address)
  /-- `upgradeChain(_, id)`. -/
  | upgradeChain (id : ChainId)
  /-- `forward(calls)`. -/
  | forward (calls : List FCall)
  /-- Another actor's step. -/
  | env (l : Label)

/-- The `ExecutorForward` label of an entry point modelled as at `e561b9cc2`. The
infrastructure leg has none: the function it called at `e561b9cc2` is deleted. -/
def V35Label.toX? : V35Label → Option XLabel
  | .infra _ => none
  | .commit t => some (.commit t)
  | .upgradeChain id => some (.upgradeChain id)
  | .forward calls => some (.forward calls)
  | .env l => some (.env l)

/-- The executor's checks after the engine returns (`ProxyUpgradeExecutorBase.sol:92-103`). -/
structure PostChecks (X : V35Config) (T : V35Transition) (s s' : V35State) : Prop where
  /-- `owner()` unchanged (`:93-95`). -/
  owner : s'.owner = s.owner
  /-- `pendingOwner()` unchanged (`:93-95`). -/
  pendingOwner : s'.pendingOwner = s.pendingOwner
  /-- The domain-holders hash unchanged (`:96-98`). -/
  holders : X.holdersHash s'.holders = X.holdersHash s.holders
  /-- `requireRowsApplied(_proxyAdmin, rows)` (`:99-103`). -/
  rows : ProxyUpgradeCurrent.RowsApplied s'.x.impl T.rows

/-- One successful transaction at `b17415d20`. -/
inductive V35Step (X : V35Config) : V35State → V35Label → V35State → Prop
  /-- `applyInfrastructureUpgrade(T)` (`CTMUpgradeExecutor.sol:64-72`,
  `ProxyUpgradeExecutorBase.sol:51-104`): the object has code (`:57`), is of the CTM domain
  (`:59-61`), its engine has code (`:63`), the CTM's `admin()` is not the `ProxyAdmin` (`:72-77`),
  its inventory has the CTM domain's length (the `toRows` check, `:99-102` and
  `ProxyUpgradeRowLib.sol:62-64`), the engine's leg succeeds (`:82-91`), and the post-checks pass
  (`:92-103`). -/
  | infra {s s' : V35State} {T : V35Transition} :
      X.base.rc.hasCode T.addr →
      T.domain = .ctm →
      X.base.rc.hasCode T.engine →
      s.holders.ctmAdmin ≠ X.proxyAdmin →
      T.inventory.length = X.inventoryLength .ctm →
      X.code T.engine T s s' →
      PostChecks X T s s' →
      V35Step X s (.infra T) s'
  /-- Every other entry point and actor: `ExecutorForward`'s step, the ghosts untouched. -/
  | other {s : V35State} {l : V35Label} {x : XLabel} {x' : XState} :
      l.toX? = some x → XStep X.base s.x x x' → V35Step X s l { s with x := x' }

/-- A sequence of successful transactions. -/
inductive V35Run (X : V35Config) : V35State → List V35Label → V35State → Prop
  | nil {s : V35State} : V35Run X s [] s
  | cons {s s' s'' : V35State} {l : V35Label} {ls : List V35Label} :
      V35Step X s l s' → V35Run X s' ls s'' → V35Run X s (l :: ls) s''

/-- `ExecutorForward`'s `XLabel.Tame`, read at `b17415d20`: an infrastructure transition whose
rows do not name the CTM proxy, or a forward of tame calls. At `e561b9cc2` this was the whole
premise of the run invariants (`Properties.TameRunPreservesSysInv`); at `b17415d20` it says
nothing about the engine. -/
def V35Label.Tame (X : V35Config) : V35Label → Prop
  | .infra T => ∀ r ∈ T.rows, r.proxy ≠ X.base.ctmProxy
  | .forward calls => ∀ c ∈ calls, c.Tame
  | _ => True

/-- **WHAT GOVERNANCE MUST CHECK OF THE ENGINE, FOR THE CTM'S INVARIANTS.** Every successful
`applyInfrastructureUpgrade(T)` is, on the modelled state, a run of tame `e561b9cc2` executor
transactions (`XLabel.Tame`): something the owner could have done by `forward`s of CTM calls that
are not break-glass cuts and of `ProxyAdmin.upgrade` on proxies other than the CTM's, and by
`applyInfrastructureUpgrade`s of rows that do not name the CTM proxy. Read in source terms, the
engine's net effect on the modelled state is that of transactions that make no break-glass cut
and do not move the CTM proxy; this is a net-effect condition, so an engine that swaps the CTM
proxy and swaps it back to the same modelled state also counts as tame. The executor checks
none of this.
Only the engine's code varies between the legs of `T`, so this is a condition on the engine. -/
def EngineIsTame (X : V35Config) (T : V35Transition) : Prop :=
  ∀ s s', V35Step X s (.infra T) s' →
    ∃ xs : List XLabel, XRun X.base s.x xs s'.x ∧ ∀ x ∈ xs, x.Tame X.base

/-- `ExecutorForward`'s `MovesOnlyAlongRows`, read at `b17415d20`: every proxy whose
implementation changed moved along an edge of a row of the infrastructure transition the step
applied. -/
def V35MovesOnlyAlongRows (s s' : V35State) (l : V35Label) : Prop :=
  ∀ p, s'.x.impl p = s.x.impl p ∨
    ∃ T r, l = .infra T ∧ r ∈ T.rows ∧ r.proxy = p ∧
      s.x.impl p = r.expectedOldImpl ∧ s'.x.impl p = r.implNew

/-! ## Witness data

`ExecutorForward`'s witness executor `wX`: the `ChainRouting` witness world, the row library's
witness configuration (the executor `1` owns its admin, every address has code, reinitializers
inert) and the CTM proxy `8`. The `ProxyAdmin` is at `60`, the ServerNotifier at `9`, the CTM's
admin is `50`. Toy inventories have two slots. The engine addresses `70`-`79` hold the engines
below; every other address holds code that reverts. -/

/-- `_afterSwaps` replaces the committed transition `300` by `400` on the CTM. -/
def wHookCalls : List FCall := [.sys (.ctm (.replace 300 400))]

/-- `_afterSwaps` makes the break-glass cut of chain `0` to version 1 with `bgExtra`. -/
def wCutCalls : List FCall := [.sys (.arbitraryCut 0 1 bgExtra)]

/-- `_afterSwaps` swaps the CTM's code for code that leaves the CTM as `initialize(100)` would:
the call of `ExecutorForward`'s `ForwardCtmSwapBreaksInvariants`. -/
def wSwapCalls : List FCall := [.swapCtm 42 (initState wWorld 100)]

/-- Engine `77`: `DefaultProxyUpgradeEngine`'s core, plus a hook that writes `66` into the
executor's `_pendingOwner` slot (the engine runs in the executor's storage). Holders unchanged. -/
def wExecutorNominatingEngine : EngineCode := fun T s s' =>
  EngineCore wX T s.x s'.x ∧ s'.owner = s.owner ∧ s'.pendingOwner = 66 ∧ s'.holders = s.holders

/-- Engine `78`: `DefaultProxyUpgradeEngine`'s core, plus a hook that calls the CTM's
`transferOwnership(66)` (the executor owns the CTM), so the CTM's `pendingOwner()` becomes `66`.
The executor's own ownership is unchanged. -/
def wCtmNominatingEngine : EngineCode := fun T s s' =>
  EngineCore wX T s.x s'.x ∧ s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner ∧
    s'.holders = { s.holders with ctmPendingOwner := 66 }

/-- The engine code of the witnesses. -/
def wCode : Address → EngineCode := fun a =>
  if a = 70 then defaultEngine wX
  else if a = 71 then subclassEngine wX [] wHookCalls
  else if a = 72 then subclassEngine wX [] wCutCalls
  else if a = 73 then subclassEngine wX [] wSwapCalls
  else if a = 74 then callingEngine wX [.upgradeProxy 5 11]
  else if a = 75 then subclassEngine wX [] [.upgradeProxy 7 42]
  else if a = 76 then subclassEngine wX [.upgradeProxy 5 10] []
  else if a = 77 then wExecutorNominatingEngine
  else if a = 78 then wCtmNominatingEngine
  else if a = 79 then subclassEngine wX [] [.upgradeProxy 5 42]
  else fun _ _ _ => False

/-- The domain holders of the witness: the executor `1` owns the `ProxyAdmin` `60`, which
administers the CTM and the ServerNotifier `9`; the executor owns both, the CTM's admin is `50`,
and the notifier serves the CTM `8`. -/
def wHolders : DomainHolders := ⟨1, 1, 0, 50, 60, 9, 1, 0, 60, 8⟩

/-- A holders hash that tells the witness holders apart from every other value, so it has no
collision on any pair the witnesses compare. -/
def wHoldersHash (h : DomainHolders) : UInt256 := if h = wHolders then 1 else 0

/-- The witness executor at `b17415d20`. -/
def wV35 : V35Config where
  base := wX
  proxyAdmin := 60
  inventoryLength := fun _ => 2
  code := wCode
  holdersHash := wHoldersHash

/-- The same executor with a holders hash under which every pair collides. -/
def wV35Blind : V35Config := { wV35 with holdersHash := fun _ => 0 }

/-- The start: `ExecutorForward`'s fresh state, the executor owned by governance `77`. -/
def wV0 : V35State := ⟨wX0, 77, 0, wHolders⟩

/-- The CTM-domain transition with rows `5: 10 → 11` and `6: 10 → 12`, pinning the engine at
`e`. -/
def wTAB (e : Address) : V35Transition :=
  ⟨3, .ctm, [ProxyUpgradeCurrent.rowA, ProxyUpgradeCurrent.rowB], e⟩

/-- The transition with the one row `5: 10 → 11` (and an inert slot), at address `a`, pinning the
engine at `e`. -/
def wTA (a e : Address) : V35Transition :=
  ⟨a, .ctm, [ProxyUpgradeCurrent.rowA, ProxyUpgradeCurrent.slotInert], e⟩

/-- The later transition with the one row `5: 11 → 12` (and an inert slot), pinning the
default engine. -/
def wTA2 : V35Transition :=
  ⟨31, .ctm, [ProxyUpgradeCurrent.rowA2, ProxyUpgradeCurrent.slotInert], 70⟩

/-- A run whose one infrastructure leg pins the default engine: apply `wTAB 70`, create chain
`0`, commit `300` (1→2), upgrade chain `0`. -/
def wDefaultRun : List V35Label :=
  [.infra (wTAB 70), .env (.genesis 0), .commit 300, .upgradeChain 0]

/-- The witness run: `wDefaultRun`, then apply `wTAB 71`, whose `_afterSwaps` replaces `300` by
`400`. -/
def wReviewedRun : List V35Label := wDefaultRun ++ [.infra (wTAB 71)]

/-- Two default-engine legs: proxy `5` goes `10 → 11` (`wTA 30 70`), then `11 → 12` (`wTA2`). -/
def wStaleRun : List V35Label := [.infra (wTA 30 70), .infra wTA2]

end Contracts.ChainTypeManager.ExecutorEngineAtV35
