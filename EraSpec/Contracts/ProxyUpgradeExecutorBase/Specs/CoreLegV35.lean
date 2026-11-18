import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent

/-!
# Model: the Core-domain leg `CoreUpgradeExecutor.applyL1Upgrade` at `b17415d20`

Source: era-contracts branch `draft/v0.35.0` at commit
**`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`** (2026-11-16). Every `file:line` below is at that
commit, under `l1-contracts/contracts/`, unless it names OpenZeppelin. OpenZeppelin is the
submodule `lib/openzeppelin-contracts-v4` that commit pins, `dc44c9f1a4c3` (release 4.9.6):
`proxy/transparent/ProxyAdmin.sol`, `proxy/transparent/TransparentUpgradeableProxy.sol`,
`proxy/ERC1967/ERC1967Upgrade.sol`, `access/Ownable.sol`, `access/Ownable2Step.sol`.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.CoreLegV35`, proofs in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.CoreLegV35`.

## Re-pinned from `d9f678900`

The first draft of this model cited `d9f678900e1bc8286412b78f56d4a9f443983c29`, the same
branch ten days earlier (2026-11-06; `b17415d20` is of 2026-11-16). `git diff d9f678900
b17415d20` changes three things the model reads:

* `_applyProxyUpgradeTransition` gained a check that runs only with a nonzero CTM
  (`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:72-77`), and `_domainHolders`
  now reads the CTM's ServerNotifier itself and hashes more CTM fields (`:118-148`; at
  `d9f678900` the caller read the ServerNotifier once, before the engine). With a zero CTM
  neither is reached: at both commits `_domainHolders` returns
  `keccak256(abi.encode(_proxyAdmin.owner()))`. The CTM side is opaque here (below).
* `DefaultProxyUpgradeEngine.executeUpgrade` now hands each hook and `toRows` its own memory
  copy of the calldata inventory (`upgrades/registry/engines/DefaultProxyUpgradeEngine.sol:38-46`);
  at `d9f678900` the hooks and `toRows` shared one memory copy. The model passes every hook the
  inventory as pinned, which is the `b17415d20` code.
* `ProxyUpgradeRowLib.sol` gained a `@dev` paragraph (`:28-32`), which moves its lines by five;
  its code is unchanged. `CoreUpgradeExecutor.sol`, `ICoreUpgradeExecutor.sol`,
  `objects/ProxyUpgradeTransition.sol` and the two enum member counts are unchanged.

## The leg

`upgrades/registry/executors/CoreUpgradeExecutor.sol:33-36`:

    function applyL1Upgrade(IProxyUpgradeTransition _coreTransition) external onlyOwner {
        _applyProxyUpgradeTransition(PROXY_ADMIN, _coreTransition, ProxyUpgradeDomain.Core, address(0));
        emit L1UpgradeApplied(address(_coreTransition));
    }

`_applyProxyUpgradeTransition` (`ProxyUpgradeExecutorBase.sol:51-104`): the transition must be
code (`:57`); its manifest is read once (`:58`) and must be of the executor's domain
(`:59-61`); the pinned engine must be code (`:63`); with a nonzero CTM, the CTM's `admin()` must
not be the `ProxyAdmin` (`:75-77`); the executor snapshots its `owner()`/`pendingOwner()`
(`:78-79`) and the hash of its domain's holders (`:80`); it DELEGATECALLS
`executeUpgrade(context, manifest.proxyUpgrades)` on the engine (`:82-84`), bubbling a revert
(`:85-91`); then it requires the owner and pending owner unchanged (`:93-95`), the holders' hash
unchanged (`:96-98`), and every row of `toRows(manifest.proxyUpgrades, inventoryLength(domain))`
at its `implNew` (`:99-103`).

With a zero CTM, `_domainHolders` (`:118-148`) takes its first branch (`:119-121`):

    if (_chainTypeManager == address(0)) {
        return keccak256(abi.encode(_proxyAdmin.owner()));
    }

so in the Core domain the only domain holder compared is the `ProxyAdmin`'s owner.

`ProxyUpgradeRowLib.requireRowsApplied`
(`upgrades/registry/libraries/ProxyUpgradeRowLib.sol:133-141`) reads each row's proxy through
`ProxyAdmin.getProxyImplementation`, which (OpenZeppelin
`ProxyAdmin.sol:21-27`) STATICCALLs `implementation()` on the proxy and decodes the answer. A
`TransparentUpgradeableProxy` answers that itself only when the caller is its admin
(`TransparentUpgradeableProxy.sol:84-107`, `:130-135`); for any other caller it delegates the
call to its implementation's code. So for a proxy whose admin slot no longer holds the
`ProxyAdmin`, the check reads whatever the current implementation's code answers to
`implementation()`.

## The default engine

`upgrades/registry/engines/DefaultProxyUpgradeEngine.sol:32-47`: the `ProxyAdmin`'s owner must be
`address(this)`, which under the delegatecall is the executor (`:33-37`); then `_beforeSwaps`
(`:40`), `ProxyUpgradeRowLib.applyRows(proxyAdmin, toRows(inventory, inventoryLength(domain)))`
(`:41-44`), `_afterSwaps` (`:45`) and `_checkPostconditions` (`:46`). The three hooks are empty
virtual functions (`:52`, `:57`, `:63-66`); a release engine INHERITS this contract and overrides
them (`:18-23`). `releaseEngine` below is such an engine whose `_afterSwaps` makes a fixed list of
calls.

## Modelling choices

* **A revert is `none`.** Every function here returns `Option World`.
* **Reused definitions.** `Row`, `toRows`, `Domain`, `ValidRows`, `upd` and (in the statements)
  `ApplyRows` and `ReinitFrames` are those of `Contracts.ProxyUpgradeCurrent`
  (`ProxyUpgradeRowLib/Specs/RowsCurrent.lean`, written against `e561b9cc2`). They were re-read
  against `b17415d20`: `ProxyUpgradeRow` (`upgrades/registry/RegistryTypes.sol:170-175`),
  `ProxyUpgradeDomain` (`:180-187`), `validateRows` (`ProxyUpgradeRowLib.sol:74-90`) and
  `_dropInertSlots` (`:145-161`) say the same there. Since `e561b9cc2` the library lost
  `applyTransition`, and `applyRows`' verification loop became the function
  `requireRowsApplied` (`:133-141`), which `applyRows` still calls last (`:127`); the loop body is
  unchanged.
* **The world** is the executor's two ownership slots, the `ProxyAdmin`'s owner, and each
  proxy's EIP-1967 implementation and admin slots. Other state is not modelled. Every address
  read as a proxy is taken to run `TransparentUpgradeableProxy` code.
* **One `ProxyAdmin`.** The executor's immutable `PROXY_ADMIN` (`CoreUpgradeExecutor.sol:23`) is
  `Exec.pa`. The engine gets it in `ProxyUpgradeContext.proxyAdmin`
  (`ProxyUpgradeExecutorBase.sol:65-71`) and uses that.
* **`getProxyImplementation`** returns the implementation slot if the proxy's admin slot is
  `pa`, and otherwise `Exec.implAnswer` of the code at the implementation, for that proxy, in the
  current world; `none` is a revert (no such function, codeless implementation, or undecodable
  return data). The answer may depend on the whole modelled world: that code runs in the proxy's
  storage and may read other contracts.
* **`ProxyAdmin` calls** (`upgrade`, `upgradeAndCall`, `changeProxyAdmin`, `transferOwnership`;
  OpenZeppelin `ProxyAdmin.sol:51-80`, `Ownable.sol:69-72`) are `onlyOwner`, and the engine makes
  them with `msg.sender` the executor, so each needs the `ProxyAdmin`'s owner to be `Exec.self`.
  A proxy whose admin slot is not `pa` forwards `upgradeTo`/`changeAdmin` to its implementation.
  The model treats that as a revert, so an implementation with its own `upgradeTo` (UUPS style) is
  not covered. `changeAdmin` refuses a zero admin, `upgradeTo` a codeless implementation
  (`ERC1967Upgrade.sol:105`, `:40`), and `transferOwnership` a zero owner.
* **The reinitializer** `initializeUpgrade()` runs by delegatecall in its proxy's storage
  (`ProxyUpgradeRowLib.sol:119-121`; OpenZeppelin `ERC1967Upgrade.sol:59-64`), so it can write
  that proxy's two EIP-1967 slots. `Exec.reinit` gives, for the row and the world right after
  the swap, the implementation and admin mappings it leaves. It is an arbitrary function, which
  over-approximates: real code moves another proxy only with authority over it. It does not
  touch the executor's ownership or the `ProxyAdmin`'s owner (the proxy holds neither authority).
  A result that needs the admin slots left alone takes `ReinitKeepsAdmins` as a premise. As in
  `RowsCurrent`, a reinitializer never reverts in the model, and its effects on other state are
  not modelled.
* **The engine** is `Engines`: the semantics of the code at each address, as a function of the
  context, the inventory and the world. Any engine is allowed. No result assumes it behaves
  well unless it says so. Code existence (`Exec.hasCode`) is fixed for the call.
* **`keccak256(abi.encode(owner))`** is `Exec.keccakOwner`, an arbitrary function. Nothing
  assumes it is injective; a result that needs two hashes to differ takes that for the one pair.
* **The CTM side is opaque.** The CTM branch of `_domainHolders`
  (`ProxyUpgradeExecutorBase.sol:122-147`) is `Exec.ctmHolders` (`none` is a revert of one of
  its reads), and the CTM-only check at `:75-77` is `Exec.ctmCheck`. The CTM's own state is not in
  `World`. The Core leg never reaches either (`CoreLegIgnoresCTMBranch`).
* **Events have no effect.** `emit L1UpgradeApplied` is omitted.
* **The transition object** is its address and what its `getManifest()` returns, read once
  (`ProxyUpgradeExecutorBase.sol:58`): `TransitionObj.manifest`. Any object is allowed, genuine
  or not; an object whose `getManifest()` reverts only adds reverts and is not represented.
-/

namespace Contracts.ProxyUpgradeExecutorV35.CoreLeg

open Contracts.ProxyUpgradeCurrent (Address Row Impl upd toRows Domain ValidRows Config)

/-- `L1_ECOSYSTEM_CONTRACT_COUNT` (`upgrades/registry/libraries/ContractIdentifiers.sol:133`): the
nine members of `L1EcosystemContract` (`:117-127`). -/
def L1_ECOSYSTEM_CONTRACT_COUNT : Nat := 9

/-- `CTM_CONTRACT_COUNT` (`ContractIdentifiers.sol:134`): the 21 members of `CTMContract`
(`:64-92`). -/
def CTM_CONTRACT_COUNT : Nat := 21

/-- `ProxyUpgradeRowLib.inventoryLength` (`ProxyUpgradeRowLib.sol:47-49`). -/
def inventoryLength : Domain → Nat
  | .core => L1_ECOSYSTEM_CONTRACT_COUNT
  | .ctm => CTM_CONTRACT_COUNT

/-- `ProxyUpgradeRowLib.toRows` (`ProxyUpgradeRowLib.sol:58-66`): the length check, then the
drop of inert slots. -/
def toRowsChecked (slots : List Row) (n : Nat) : Option (List Row) :=
  if slots.length = n then some (toRows slots) else none

/-- The state the leg reads and the engine may change. -/
structure World where
  /-- The executor's `owner()` (`Ownable2Step`, `governance/UpgradeExecutorBase.sol:23`). -/
  owner : Address
  /-- The executor's `pendingOwner()` (OpenZeppelin `Ownable2Step.sol:27-29`). -/
  pendingOwner : Address
  /-- `PROXY_ADMIN.owner()` (a plain `Ownable`, `ProxyAdmin.sol:13`). -/
  paOwner : Address
  /-- Each proxy's EIP-1967 implementation slot. -/
  impl : Address → Address
  /-- Each proxy's EIP-1967 admin slot. -/
  admin : Address → Address

/-- A deployed `CoreUpgradeExecutor` and the fixed facts about code it relies on. -/
structure Exec where
  /-- `address(this)`: the executor, and the engine while it is delegatecalled. -/
  self : Address
  /-- `PROXY_ADMIN` (`CoreUpgradeExecutor.sol:23`). -/
  pa : Address
  /-- `ObjectAnchorLib.requireCode` passes
  (`upgrades/registry/libraries/ObjectAnchorLib.sol:21-25`); also OpenZeppelin's
  `Address.isContract`. -/
  hasCode : Address → Bool
  /-- What the code at an implementation answers to `implementation()` when a proxy delegates the
  call to it, for that proxy, in the given world; `none` is a revert. -/
  implAnswer : Address → Address → World → Option Address
  /-- What a row's `initializeUpgrade()` leaves, given the row and the world right after its
  swap: the implementation mapping and the admin mapping. -/
  reinit : Row → World → Impl × (Address → Address)
  /-- `keccak256(abi.encode(owner))`. -/
  keccakOwner : Address → UInt256
  /-- The CTM branch of `_domainHolders` (`ProxyUpgradeExecutorBase.sol:122-147`), opaque;
  `none` is a revert. -/
  ctmHolders : Address → World → Option UInt256
  /-- The CTM-only check at `:75-77` (`IChainTypeManager(ctm).admin()` answers and is not the
  `ProxyAdmin`), opaque. -/
  ctmCheck : Address → World → Bool

/-- `ProxyUpgradeTransitionManifest` (`upgrades/registry/RegistryTypes.sol:205-209`). -/
structure Manifest where
  /-- `domain`. -/
  domain : Domain
  /-- `proxyUpgrades`: the enum-indexed inventory. -/
  proxyUpgrades : List Row
  /-- `proxyUpgradeEngine`. -/
  engine : Address

/-- A transition object: its address and what its `getManifest()` returns. -/
structure TransitionObj where
  /-- The object's address. -/
  addr : Address
  /-- `getManifest()`. -/
  manifest : Manifest

/-- What `ProxyUpgradeTransition`'s constructor
(`upgrades/registry/objects/ProxyUpgradeTransition.sol:27-42`) guarantees of a deployed
transition: the inventory length is the domain's (`:28-31`), some slot participates (`:34-36`),
the participating rows pass `validateRows` (`:37`), and the engine is nonzero (`:39-41`). The
executor does not require it: of these it checks only the inventory length
(`ProxyUpgradeExecutorBase.sol:99-102`), after the engine has run. -/
structure Genuine (T : TransitionObj) : Prop where
  /-- `toRows`' length check (`:28-31`). -/
  length : T.manifest.proxyUpgrades.length = inventoryLength T.manifest.domain
  /-- `participating.length != 0` (`:34-36`). -/
  nonempty : toRows T.manifest.proxyUpgrades ≠ []
  /-- `validateRows(participating)` (`:37`). -/
  valid : ValidRows (toRows T.manifest.proxyUpgrades)
  /-- `proxyUpgradeEngine != address(0)` (`:39-41`). -/
  engineNonzero : T.manifest.engine ≠ 0

/-- `ProxyUpgradeContext` (`RegistryTypes.sol:221-227`). -/
structure Context where
  /-- `transition`. -/
  transition : Address
  /-- `proxyUpgradeEngine`. -/
  engine : Address
  /-- `domain`. -/
  domain : Domain
  /-- `proxyAdmin`. -/
  proxyAdmin : Address
  /-- `chainTypeManager`. -/
  chainTypeManager : Address

/-- What an engine does when delegatecalled with a context and an inventory. -/
abbrev EngineSem := Context → List Row → World → Option World

/-- The code at each address, as an engine. -/
abbrev Engines := Address → EngineSem

/-! ## Reads and `ProxyAdmin` calls -/

/-- `PROXY_ADMIN.getProxyImplementation(p)` (OpenZeppelin `ProxyAdmin.sol:21-27`): the proxy
answers `implementation()` itself to its admin (`TransparentUpgradeableProxy.sol:96-97`,
`:130-135`), and delegates it to its implementation's code for anyone else (`:104-105`). -/
def getProxyImplementation (X : Exec) (W : World) (p : Address) : Option Address :=
  if W.admin p = X.pa then some (W.impl p) else X.implAnswer (W.impl p) p W

/-- `PROXY_ADMIN.upgrade(p, x)` called by the executor (`ProxyAdmin.sol:62-64`). -/
def paUpgrade (X : Exec) (p x : Address) (W : World) : Option World :=
  if W.paOwner = X.self ∧ W.admin p = X.pa ∧ X.hasCode x = true then
    some { W with impl := upd W.impl p x }
  else none

/-- `PROXY_ADMIN.changeProxyAdmin(p, a)` called by the executor (`ProxyAdmin.sol:51-53`). -/
def paChangeProxyAdmin (X : Exec) (p a : Address) (W : World) : Option World :=
  if W.paOwner = X.self ∧ W.admin p = X.pa ∧ a ≠ 0 then
    some { W with admin := upd W.admin p a }
  else none

/-- `PROXY_ADMIN.transferOwnership(a)` called by the executor (`Ownable.sol:69-72`). -/
def paTransferOwnership (X : Exec) (a : Address) (W : World) : Option World :=
  if W.paOwner = X.self ∧ a ≠ 0 then some { W with paOwner := a } else none

/-- One step an engine can take with the executor's authority and storage. -/
inductive EngineOp
  /-- `PROXY_ADMIN.upgrade(p, x)`. -/
  | upgrade (p x : Address)
  /-- `PROXY_ADMIN.changeProxyAdmin(p, a)`. -/
  | changeProxyAdmin (p a : Address)
  /-- `PROXY_ADMIN.transferOwnership(a)`. -/
  | transferPAOwnership (a : Address)
  /-- An `SSTORE` to the executor's owner slot (the engine runs in the executor's storage). -/
  | writeOwner (a : Address)
  /-- An `SSTORE` to the executor's pending-owner slot. -/
  | writePendingOwner (a : Address)

/-- The effect of one `EngineOp`. -/
def runOp (X : Exec) : EngineOp → World → Option World
  | .upgrade p x, W => paUpgrade X p x W
  | .changeProxyAdmin p a, W => paChangeProxyAdmin X p a W
  | .transferPAOwnership a, W => paTransferOwnership X a W
  | .writeOwner a, W => some { W with owner := a }
  | .writePendingOwner a, W => some { W with pendingOwner := a }

/-- A sequence of `EngineOp`s, in order; any revert reverts the whole. -/
def runOps (X : Exec) : List EngineOp → World → Option World
  | [], W => some W
  | o :: os, W => (runOp X o W).bind (runOps X os)

/-! ## `ProxyUpgradeRowLib.applyRows` against the world -/

/-- The state after the swap at `ProxyUpgradeRowLib.sol:119-124`: `upgradeAndCall` with the
reinitializer (`:119-121`), or a plain `upgrade` (`:122-124`). -/
def swapW (X : Exec) (r : Row) (W : World) : World :=
  if r.callInitializeUpgrade then
    { W with impl := (X.reinit r { W with impl := upd W.impl r.proxy r.implNew }).1,
             admin := (X.reinit r { W with impl := upd W.impl r.proxy r.implNew }).2 }
  else { W with impl := upd W.impl r.proxy r.implNew }

/-- No reinitializer writes an admin slot. -/
def ReinitKeepsAdmins (X : Exec) : Prop :=
  ∀ (r : Row) (W : World), (X.reinit r W).2 = W.admin

/-- One iteration of `applyRows`' loop (`ProxyUpgradeRowLib.sol:109-126`). The `upgrade` or
`upgradeAndCall` needs the executor to own the `ProxyAdmin` and the `ProxyAdmin` to administer
the proxy. The earlier `requireRowCode` already gives `upgradeTo`'s code check. -/
def applyRowW (X : Exec) (W : World) (r : Row) : Option World :=
  match getProxyImplementation X W r.proxy with
  | none => none
  | some live =>
    if live = r.implNew then some W
    else if live ≠ r.expectedOldImpl then none
    else if W.paOwner = X.self ∧ W.admin r.proxy = X.pa then some (swapW X r W)
    else none

/-- The loop, in order. -/
def applyLoopW (X : Exec) : World → List Row → Option World
  | W, [] => some W
  | W, r :: rs => (applyRowW X W r).bind (fun W' => applyLoopW X W' rs)

/-- `requireRowCode` (`ProxyUpgradeRowLib.sol:93-98`) passes. -/
def RowCodeW (X : Exec) (rows : List Row) : Prop :=
  ∀ r ∈ rows, X.hasCode r.implNew = true

instance (X : Exec) (rows : List Row) : Decidable (RowCodeW X rows) := by
  unfold RowCodeW; infer_instance

/-- `requireRowsApplied` (`ProxyUpgradeRowLib.sol:133-141`) passes: each row's proxy, read
through `PROXY_ADMIN.getProxyImplementation`, answers its `implNew`. -/
def RowsAppliedW (X : Exec) (W : World) (rows : List Row) : Prop :=
  ∀ r ∈ rows, getProxyImplementation X W r.proxy = some r.implNew

instance (X : Exec) (W : World) (rows : List Row) : Decidable (RowsAppliedW X W rows) := by
  unfold RowsAppliedW; infer_instance

/-- `applyRows(PROXY_ADMIN, rows)` (`ProxyUpgradeRowLib.sol:106-128`). -/
def applyRowsW (X : Exec) (rows : List Row) (W : World) : Option World :=
  if RowCodeW X rows then
    (applyLoopW X W rows).bind (fun W' => if RowsAppliedW X W' rows then some W' else none)
  else none

/-! ## Engines -/

/-- An empty hook. -/
def noHook : EngineSem := fun _ _ W => some W

/-- `DefaultProxyUpgradeEngine.executeUpgrade` (`DefaultProxyUpgradeEngine.sol:32-47`) with the
hooks a release engine supplies. Each hook gets the inventory as pinned (`:38-39`).
`ctx.proxyAdmin` is the model's one `ProxyAdmin`. The postcondition hook is a `view`
(`:63-66`): it can only revert. -/
def defaultEngineWith (X : Exec) (beforeSwaps afterSwaps : EngineSem)
    (post : Context → List Row → World → Bool) : EngineSem :=
  fun ctx inv W =>
    if W.paOwner ≠ X.self then none
    else
      (beforeSwaps ctx inv W).bind fun W1 =>
      (toRowsChecked inv (inventoryLength ctx.domain)).bind fun rows =>
      (applyRowsW X rows W1).bind fun W2 =>
      (afterSwaps ctx inv W2).bind fun W3 =>
      if post ctx inv W3 = true then some W3 else none

/-- `DefaultProxyUpgradeEngine` itself: all three hooks empty (`:52`, `:57`, `:63-66`). -/
def defaultEngine (X : Exec) : EngineSem :=
  defaultEngineWith X noHook noHook (fun _ _ _ => true)

/-- A release engine inheriting `DefaultProxyUpgradeEngine` whose `_afterSwaps` makes the calls
`ops` and whose other hooks are empty (`DefaultProxyUpgradeEngine.sol:18-23`). -/
def releaseEngine (X : Exec) (ops : List EngineOp) : EngineSem :=
  defaultEngineWith X noHook (fun _ _ W => runOps X ops W) (fun _ _ _ => true)

/-! ## The leg -/

/-- `_domainHolders` (`ProxyUpgradeExecutorBase.sol:118-148`); `none` is a revert. -/
def domainHolders (X : Exec) (ctm : Address) (W : World) : Option UInt256 :=
  if ctm = 0 then some (X.keccakOwner W.paOwner) else X.ctmHolders ctm W

/-- The context built at `:65-71`. -/
def context (X : Exec) (T : TransitionObj) (d : Domain) (ctm : Address) : Context :=
  ⟨T.addr, T.manifest.engine, d, X.pa, ctm⟩

/-- The checks after the engine returns (`:92-103`): `W` is the state before it ran, `h` the
holders' hash taken then (`:80`), `W'` the engine's result. -/
def postChecks (X : Exec) (d : Domain) (ctm : Address) (slots : List Row) (h : UInt256)
    (W W' : World) : Option World :=
  if W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner then
    if domainHolders X ctm W' = some h then
      (toRowsChecked slots (inventoryLength d)).bind fun rows =>
        if RowsAppliedW X W' rows then some W' else none
    else none
  else none

/-- `_applyProxyUpgradeTransition(PROXY_ADMIN, T, d, ctm)` (`ProxyUpgradeExecutorBase.sol:51-104`).
The checks after the engine are views, so the final state is the engine's. -/
def applyProxyUpgradeTransition (X : Exec) (E : Engines) (T : TransitionObj) (d : Domain)
    (ctm : Address) (W : World) : Option World :=
  if X.hasCode T.addr = true ∧ T.manifest.domain = d ∧ X.hasCode T.manifest.engine = true ∧
      (ctm = 0 ∨ X.ctmCheck ctm W = true) then
    (domainHolders X ctm W).bind fun h =>
      (E T.manifest.engine (context X T d ctm) T.manifest.proxyUpgrades W).bind
        (postChecks X d ctm T.manifest.proxyUpgrades h W)
  else none

/-- The context the Core leg hands its engine: the transition, its engine, `Core`,
`PROXY_ADMIN` and a zero CTM (`CoreUpgradeExecutor.sol:34`,
`ProxyUpgradeExecutorBase.sol:65-71`). -/
def coreContext (X : Exec) (T : TransitionObj) : Context := context X T .core 0

/-- `CoreUpgradeExecutor.applyL1Upgrade(T)` called by `caller` (`CoreUpgradeExecutor.sol:33-36`),
`onlyOwner`. -/
def applyL1Upgrade (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W : World) :
    Option World :=
  if caller = W.owner then applyProxyUpgradeTransition X E T .core 0 W else none

/-- The `RowsCurrent` configuration the default engine runs under in world `W`: the executor,
the `ProxyAdmin`'s owner, code existence, and the reinitializers' effect on the implementation
mapping with the rest of `W` fixed. -/
def rowsConfig (X : Exec) (W : World) : Config where
  self := X.self
  adminOwner := W.paOwner
  hasCode := fun a => X.hasCode a = true
  reinit := fun r I => (X.reinit r { W with impl := I }).1

/-! ## Witness data

Executor `1`, `ProxyAdmin` `2`, transition `3`, engine `4`, governance (the executor's owner)
`100`. Proxy `5` is the singleton the transition's one row names; `6` and `7` are singletons it
does not name. Every proxy starts at implementation `10` under admin `2`. -/

/-- A Core-domain executor: every address has code, no implementation answers `implementation()`
to a non-admin, each reinitializer writes its own proxy's implementation slot to its row's
`implNew` and nothing else, the owner hash is the identity. -/
def coreExec : Exec where
  self := 1
  pa := 2
  hasCode := fun _ => true
  implAnswer := fun _ _ _ => none
  reinit := fun r W => (upd W.impl r.proxy r.implNew, W.admin)
  keccakOwner := fun a => a
  ctmHolders := fun _ _ => none
  ctmCheck := fun _ _ => false

/-- As `coreExec`, but implementation `12` answers `implementation()` with `11`, for every proxy
and world. -/
def coreExecSpoof : Exec :=
  { coreExec with implAnswer := fun i _ _ => if i = 12 then some 11 else none }

/-- As `coreExec`, but the owner hash collides on the executor `1` and address `9`. -/
def coreExecCollide : Exec := { coreExec with keccakOwner := fun a => if a = 9 then 1 else a }

/-- As `coreExec`, but every reinitializer hands its own proxy's admin slot to `9` and leaves the
implementation mapping as the swap left it. -/
def coreExecReinitSilent : Exec :=
  { coreExec with reinit := fun r W => (W.impl, upd W.admin r.proxy 9) }

/-- As `coreExecReinitSilent`, and implementation `11` answers `implementation()` with `11`. -/
def coreExecReinit : Exec :=
  { coreExecReinitSilent with implAnswer := fun i _ _ => if i = 11 then some 11 else none }

/-- Before the leg: governance owns the executor, the executor owns the `ProxyAdmin`, the
`ProxyAdmin` administers every proxy, and every proxy is at `10`. -/
def coreWorld : World where
  owner := 100
  pendingOwner := 0
  paOwner := 1
  impl := fun _ => 10
  admin := fun _ => 2

/-- As `coreWorld`, but proxy `5` is administered by `8`, not the `ProxyAdmin`, and runs `12`. -/
def coreWorldForeign : World :=
  { coreWorld with admin := upd coreWorld.admin 5 8, impl := upd coreWorld.impl 5 12 }

/-- The one participating row: proxy `5`, `10 → 11`, no reinitializer. -/
def coreRow : Row := ⟨5, 10, 11, false⟩

/-- An inert slot. -/
def coreInertSlot : Row := ⟨0, 0, 0, false⟩

/-- A Core inventory of nine slots; slot 0 (`L1Bridgehub`) carries `coreRow`. -/
def coreInventory : List Row := coreRow :: List.replicate 8 coreInertSlot

/-- The Core transition at `3`, pinning engine `4`. -/
def coreTransition : TransitionObj := ⟨3, ⟨.core, coreInventory, 4⟩⟩

/-- `coreRow` with `callInitializeUpgrade` set. -/
def coreRowInit : Row := ⟨5, 10, 11, true⟩

/-- As `coreInventory`, with `coreRowInit` in slot 0. -/
def coreInventoryInit : List Row := coreRowInit :: List.replicate 8 coreInertSlot

/-- The Core transition whose one row calls its reinitializer. -/
def coreTransitionInit : TransitionObj := ⟨3, ⟨.core, coreInventoryInit, 4⟩⟩

/-- `coreWorld` after its row is applied: proxy `5` at `11`. -/
def coreAfter : World := { coreWorld with impl := upd coreWorld.impl 5 11 }

/-- Every address runs the default engine. -/
def coreDefaultEngines (X : Exec) : Engines := fun _ => defaultEngine X

/-- Every address runs the release engine making `ops`. -/
def coreReleaseEngines (X : Exec) (ops : List EngineOp) : Engines := fun _ => releaseEngine X ops

/-- Every address runs an engine that does nothing. -/
def coreNoopEngines : Engines := fun _ => noHook

end Contracts.ProxyUpgradeExecutorV35.CoreLeg
