import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent

/-!
# Model: the Core-domain leg `CoreUpgradeExecutor.applyL1Upgrade` at `d9f678900`

Source: era-contracts branch `draft/v0.35.0` at commit
**`d9f678900e1bc8286412b78f56d4a9f443983c29`**. Every `file:line` below is at that commit,
under `l1-contracts/contracts/`, unless it names OpenZeppelin. OpenZeppelin is the submodule
`lib/openzeppelin-contracts-v4` that commit pins, `dc44c9f1a4c3` (release 4.9.6):
`proxy/transparent/ProxyAdmin.sol`, `proxy/transparent/TransparentUpgradeableProxy.sol`,
`proxy/ERC1967/ERC1967Upgrade.sol`, `access/Ownable.sol`.

**This file is definitions only.** Statements are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.CoreLegV35`, proofs in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.CoreLegV35`.

## The leg

`upgrades/registry/executors/CoreUpgradeExecutor.sol:33-36`:

    function applyL1Upgrade(IProxyUpgradeTransition _coreTransition) external onlyOwner {
        _applyProxyUpgradeTransition(PROXY_ADMIN, _coreTransition, ProxyUpgradeDomain.Core, address(0));
        emit L1UpgradeApplied(address(_coreTransition));
    }

`_applyProxyUpgradeTransition` (`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:48-98`):
the transition must be code (`:54`); its manifest is read once (`:55`) and must be of the
executor's domain (`:56-58`); the pinned engine must be code (`:60`); the executor snapshots
its `owner()`/`pendingOwner()` (`:69-70`) and the hash of its domain's holders (`:74`); it
DELEGATECALLS `executeUpgrade(context, manifest.proxyUpgrades)` on the engine (`:76-78`),
bubbling a revert (`:79-85`); then it requires the owner and pending owner unchanged (`:87-89`),
the holders' hash unchanged (`:90-92`), and every row of
`toRows(manifest.proxyUpgrades, inventoryLength(domain))` at its `implNew` (`:93-97`).

With a zero CTM, `_domainHolders` (`:109-139`) takes its first branch (`:114-116`):

    if (_chainTypeManager == address(0)) {
        return keccak256(abi.encode(_proxyAdmin.owner()));
    }

so in the Core domain the only domain holder checked is the `ProxyAdmin`'s owner.

`ProxyUpgradeRowLib.requireRowsApplied` (`upgrades/registry/libraries/ProxyUpgradeRowLib.sol:128-136`)
reads each row's proxy through `ProxyAdmin.getProxyImplementation`, which (OpenZeppelin
`ProxyAdmin.sol:21-27`) STATICCALLs `implementation()` on the proxy and decodes the answer. A
`TransparentUpgradeableProxy` answers that itself only when the caller is its admin
(`TransparentUpgradeableProxy.sol:84-107`); for any other caller it delegates to its
implementation's code. So for a proxy whose admin slot no longer holds the `ProxyAdmin`, the
check reads whatever the current implementation's code answers to `implementation()`.

## The default engine

`upgrades/registry/engines/DefaultProxyUpgradeEngine.sol:32-46`: the `ProxyAdmin`'s owner must be
`address(this)`, which under the delegatecall is the executor (`:34-37`); then `_beforeSwaps`
(`:39`), `ProxyUpgradeRowLib.applyRows(proxyAdmin, toRows(inventory, inventoryLength(domain)))`
(`:40-43`), `_afterSwaps` (`:44`) and `_checkPostconditions` (`:45`). The three hooks are empty
virtual functions (`:51`, `:56`, `:62-65`); a release engine INHERITS this contract and overrides
them (`:18-23`). `releaseEngine` below is such an engine whose `_afterSwaps` makes a fixed list of
calls.

## Modelling choices

* **A revert is `none`.** Every function here returns `Option World`.
* **Reused definitions.** `Row`, `toRows`, `Domain`, `ValidRows`, `upd` and (in the statements)
  `ApplyRows` are those of `Contracts.ProxyUpgradeCurrent`
  (`ProxyUpgradeRowLib/Specs/RowsCurrent.lean`, written against `e561b9cc2`). They were re-read
  against `d9f678900`: `ProxyUpgradeRow` (`upgrades/registry/RegistryTypes.sol:168-173`),
  `ProxyUpgradeDomain` (`:178-185`), `validateRows` (`ProxyUpgradeRowLib.sol:69-85`) and
  `_dropInertSlots` (`:140-156`) say the same there. Between the two commits the library lost
  `applyTransition` and `applyRows`' second loop became the function `requireRowsApplied`
  (`:128-136`), which `applyRows` still calls last (`:122`); the loop body is unchanged.
* **The world** is the executor's two ownership slots, the `ProxyAdmin`'s owner, and each
  proxy's EIP-1967 implementation and admin slots. Other state is not modelled. Every address
  read as a proxy is taken to run `TransparentUpgradeableProxy` code.
* **One `ProxyAdmin`.** The executor's immutable `PROXY_ADMIN` (`CoreUpgradeExecutor.sol:23`) is
  `Exec.pa`. The engine gets it in `ProxyUpgradeContext.proxyAdmin` (`ProxyUpgradeExecutorBase.sol:62-68`)
  and uses that.
* **`getProxyImplementation`** returns the implementation slot if the proxy's admin slot is
  `pa`, and otherwise `Exec.implAnswer` of the code at the implementation. That answer is fixed per
  (implementation, proxy); `none` is a revert (no such function, or undecodable return data).
  Real code could make the answer depend on the proxy's other storage; the model does not.
* **`ProxyAdmin` calls** (`upgrade`, `upgradeAndCall`, `changeProxyAdmin`, `transferOwnership`;
  OpenZeppelin `ProxyAdmin.sol:51-80`, `Ownable.sol:69-72`) are `onlyOwner`, and the engine makes
  them with `msg.sender` the executor, so each needs the `ProxyAdmin`'s owner to be `Exec.self`.
  A proxy whose admin slot is not `pa` forwards `upgradeTo`/`changeAdmin` to its implementation.
  The model treats that as a revert, so an implementation with its own `upgradeTo` (UUPS style) is
  not covered. `changeAdmin` refuses a zero admin, `upgradeTo` a codeless implementation
  (`ERC1967Upgrade.sol:40`, `:105`), and `transferOwnership` a zero owner.
* **The reinitializer** `initializeUpgrade()` runs by delegatecall in its proxy's storage
  (`ProxyUpgradeRowLib.sol:114-116`), so it can write that proxy's two EIP-1967 slots. It changes
  the implementation mapping by `Exec.reinit`, the same kind of function as `RowsCurrent`'s
  `Config.reinit`, and the admin mapping by `Exec.reinitAdmin`. Both are arbitrary functions, which
  over-approximates: real code moves another proxy only with authority over it. A result that
  needs the admin slots left alone takes `ReinitKeepsAdmins` as a premise. As in `RowsCurrent`, a
  reinitializer never reverts in the model, and its effects on other state are not modelled.
* **The engine** is `Engines`: the semantics of the code at each address, as a function of the
  context, the inventory and the world. Any engine is allowed. No result assumes it behaves
  well unless it says so.
* **`keccak256(abi.encode(owner))`** is `Exec.keccakOwner`, an arbitrary function. Nothing
  assumes it is injective; a result that needs two hashes to differ takes that for the one pair.
* **The CTM branch of `_domainHolders`** is the opaque `Exec.ctmHolders`, and
  `IChainTypeManager.serverNotifierAddress()` is `Exec.serverNotifierOf`. The Core leg never
  reaches them (`CoreLegIgnoresCTMBranch`).
* **Events have no effect.** `emit L1UpgradeApplied` is omitted.
* **`getManifest()`** is a view of the transition object, read once (`:55`): `TransitionObj.manifest`.
-/

namespace Contracts.ProxyUpgradeExecutorV35.CoreLeg

open Contracts.ProxyUpgradeCurrent (Address Row Impl upd toRows Domain ValidRows Config)

/-- `L1_ECOSYSTEM_CONTRACT_COUNT` (`upgrades/registry/libraries/ContractIdentifiers.sol:127`): the
nine members of `L1EcosystemContract` (`:111-121`). -/
def L1_ECOSYSTEM_CONTRACT_COUNT : Nat := 9

/-- `CTM_CONTRACT_COUNT` (`ContractIdentifiers.sol:128`): the 21 members of `CTMContract`. -/
def CTM_CONTRACT_COUNT : Nat := 21

/-- `ProxyUpgradeRowLib.inventoryLength` (`ProxyUpgradeRowLib.sol:42-44`). -/
def inventoryLength : Domain → Nat
  | .core => L1_ECOSYSTEM_CONTRACT_COUNT
  | .ctm => CTM_CONTRACT_COUNT

/-- `ProxyUpgradeRowLib.toRows` (`ProxyUpgradeRowLib.sol:53-61`): the length check, then the
drop of inert slots. -/
def toRowsChecked (slots : List Row) (n : Nat) : Option (List Row) :=
  if slots.length = n then some (toRows slots) else none

/-- The state the leg reads and the engine may change. -/
structure World where
  /-- The executor's `owner()` (Ownable2Step, `governance/UpgradeExecutorBase.sol:22`). -/
  owner : Address
  /-- The executor's `pendingOwner()`. -/
  pendingOwner : Address
  /-- `PROXY_ADMIN.owner()`. -/
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
  /-- `ObjectAnchorLib.requireCode` passes (`upgrades/registry/libraries/ObjectAnchorLib.sol:21-25`). -/
  hasCode : Address → Bool
  /-- What the code at an implementation answers to `implementation()` when a proxy delegates the
  call to it, for that proxy; `none` is a revert. -/
  implAnswer : Address → Address → Option Address
  /-- The reinitializer's effect on the implementation mapping (as `RowsCurrent`'s `Config.reinit`). -/
  reinit : Row → Impl → Impl
  /-- The reinitializer's effect on the admin mapping, given the row and the mapping before it
  ran. -/
  reinitAdmin : Row → (Address → Address) → (Address → Address)
  /-- `keccak256(abi.encode(owner))`. -/
  keccakOwner : Address → UInt256
  /-- The CTM branch of `_domainHolders` (`ProxyUpgradeExecutorBase.sol:117-138`), opaque. -/
  ctmHolders : Address → Address → World → UInt256
  /-- `IChainTypeManager(ctm).serverNotifierAddress()` (`:71-73`), opaque. -/
  serverNotifierOf : Address → World → Address

/-- `ProxyUpgradeTransitionManifest` (`upgrades/registry/RegistryTypes.sol:203-207`). -/
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
the participating rows pass `validateRows` (`:37`), and the engine is nonzero (`:39-41`). -/
structure Genuine (T : TransitionObj) : Prop where
  /-- `toRows`' length check (`:28-31`). -/
  length : T.manifest.proxyUpgrades.length = inventoryLength T.manifest.domain
  /-- `participating.length != 0` (`:34-36`). -/
  nonempty : toRows T.manifest.proxyUpgrades ≠ []
  /-- `validateRows(participating)` (`:37`). -/
  valid : ValidRows (toRows T.manifest.proxyUpgrades)
  /-- `proxyUpgradeEngine != address(0)` (`:39-41`). -/
  engineNonzero : T.manifest.engine ≠ 0

/-- `ProxyUpgradeContext` (`RegistryTypes.sol:219-225`). -/
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
answers `implementation()` itself to its admin, and delegates it to its implementation's code for
anyone else (`TransparentUpgradeableProxy.sol:84-105`). -/
def getProxyImplementation (X : Exec) (W : World) (p : Address) : Option Address :=
  if W.admin p = X.pa then some (W.impl p) else X.implAnswer (W.impl p) p

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

/-- The state after the swap at `ProxyUpgradeRowLib.sol:114-119`: `upgradeAndCall` with the
reinitializer (`:114-116`), or a plain `upgrade` (`:117-119`). -/
def swapW (X : Exec) (r : Row) (W : World) : World :=
  if r.callInitializeUpgrade then
    { W with impl := X.reinit r (upd W.impl r.proxy r.implNew), admin := X.reinitAdmin r W.admin }
  else { W with impl := upd W.impl r.proxy r.implNew }

/-- No reinitializer writes an admin slot. -/
def ReinitKeepsAdmins (X : Exec) : Prop :=
  ∀ (r : Row) (A : Address → Address), X.reinitAdmin r A = A

/-- One iteration of `applyRows`' loop (`ProxyUpgradeRowLib.sol:104-121`). The `upgrade` or
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

/-- `requireRowCode` (`ProxyUpgradeRowLib.sol:88-93`). -/
def RowCodeW (X : Exec) (rows : List Row) : Prop :=
  ∀ r ∈ rows, X.hasCode r.implNew = true

instance (X : Exec) (rows : List Row) : Decidable (RowCodeW X rows) := by
  unfold RowCodeW; infer_instance

/-- `requireRowsApplied` (`ProxyUpgradeRowLib.sol:128-136`) passes: each row's proxy, read
through `PROXY_ADMIN.getProxyImplementation`, answers its `implNew`. -/
def RowsAppliedW (X : Exec) (W : World) (rows : List Row) : Prop :=
  ∀ r ∈ rows, getProxyImplementation X W r.proxy = some r.implNew

instance (X : Exec) (W : World) (rows : List Row) : Decidable (RowsAppliedW X W rows) := by
  unfold RowsAppliedW; infer_instance

/-- `applyRows(PROXY_ADMIN, rows)` (`ProxyUpgradeRowLib.sol:101-123`). -/
def applyRowsW (X : Exec) (rows : List Row) (W : World) : Option World :=
  if RowCodeW X rows then
    (applyLoopW X W rows).bind (fun W' => if RowsAppliedW X W' rows then some W' else none)
  else none

/-! ## Engines -/

/-- An empty hook. -/
def noHook : EngineSem := fun _ _ W => some W

/-- `DefaultProxyUpgradeEngine.executeUpgrade` (`DefaultProxyUpgradeEngine.sol:32-46`) with the
hooks a release engine supplies. `ctx.proxyAdmin` is the model's one `ProxyAdmin`. -/
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

/-- `DefaultProxyUpgradeEngine` itself: all three hooks empty (`:51`, `:56`, `:62-65`). -/
def defaultEngine (X : Exec) : EngineSem :=
  defaultEngineWith X noHook noHook (fun _ _ _ => true)

/-- A release engine inheriting `DefaultProxyUpgradeEngine` whose `_afterSwaps` makes the calls
`ops` and whose other hooks are empty (`DefaultProxyUpgradeEngine.sol:18-23`). -/
def releaseEngine (X : Exec) (ops : List EngineOp) : EngineSem :=
  defaultEngineWith X noHook (fun _ _ W => runOps X ops W) (fun _ _ _ => true)

/-! ## The leg -/

/-- `_domainHolders` (`ProxyUpgradeExecutorBase.sol:109-139`). -/
def domainHolders (X : Exec) (ctm sn : Address) (W : World) : UInt256 :=
  if ctm = 0 then X.keccakOwner W.paOwner else X.ctmHolders ctm sn W

/-- The server notifier read at `:71-73`. -/
def serverNotifier (X : Exec) (ctm : Address) (W : World) : Address :=
  if ctm = 0 then 0 else X.serverNotifierOf ctm W

/-- The context built at `:62-68`. -/
def context (X : Exec) (T : TransitionObj) (d : Domain) (ctm : Address) : Context :=
  ⟨T.addr, T.manifest.engine, d, X.pa, ctm⟩

/-- The checks after the engine returns (`:86-97`), with `W` the state before it ran. -/
def postChecks (X : Exec) (d : Domain) (ctm sn : Address) (slots : List Row) (W W' : World) :
    Option World :=
  if W'.owner = W.owner ∧ W'.pendingOwner = W.pendingOwner then
    if domainHolders X ctm sn W' = domainHolders X ctm sn W then
      (toRowsChecked slots (inventoryLength d)).bind fun rows =>
        if RowsAppliedW X W' rows then some W' else none
    else none
  else none

/-- `_applyProxyUpgradeTransition(PROXY_ADMIN, T, d, ctm)` (`ProxyUpgradeExecutorBase.sol:48-98`).
The checks after the engine are views, so the final state is the engine's. -/
def applyProxyUpgradeTransition (X : Exec) (E : Engines) (T : TransitionObj) (d : Domain)
    (ctm : Address) (W : World) : Option World :=
  if X.hasCode T.addr = true ∧ T.manifest.domain = d ∧ X.hasCode T.manifest.engine = true then
    (E T.manifest.engine (context X T d ctm) T.manifest.proxyUpgrades W).bind
      (postChecks X d ctm (serverNotifier X ctm W) T.manifest.proxyUpgrades W)
  else none

/-- The context the Core leg hands its engine. -/
def coreContext (X : Exec) (T : TransitionObj) : Context := context X T .core 0

/-- `CoreUpgradeExecutor.applyL1Upgrade(T)` called by `caller` (`CoreUpgradeExecutor.sol:33-36`). -/
def applyL1Upgrade (X : Exec) (E : Engines) (caller : Address) (T : TransitionObj) (W : World) :
    Option World :=
  if caller = W.owner then applyProxyUpgradeTransition X E T .core 0 W else none

/-- The `RowsCurrent` configuration the default engine runs under in world `W`. -/
def rowsConfig (X : Exec) (W : World) : Config where
  self := X.self
  adminOwner := W.paOwner
  hasCode := fun a => X.hasCode a = true
  reinit := X.reinit

/-! ## Witness data

Executor `1`, `ProxyAdmin` `2`, transition `3`, engine `4`, governance (the executor's owner)
`100`. Proxy `5` is the singleton the transition's one row names; `6` and `7` are singletons it
does not name. Every proxy starts at implementation `10` under admin `2`. -/

/-- A Core-domain executor: every address has code, no implementation answers `implementation()`
to a non-admin, reinitializers do nothing, the owner hash is the identity. -/
def wExec : Exec where
  self := 1
  pa := 2
  hasCode := fun _ => true
  implAnswer := fun _ _ => none
  reinit := fun _ I => I
  reinitAdmin := fun _ A => A
  keccakOwner := fun a => a
  ctmHolders := fun _ _ _ => 0
  serverNotifierOf := fun _ _ => 0

/-- As `wExec`, but implementation `12` answers `implementation()` with `11` for every proxy. -/
def wExecSpoof : Exec := { wExec with implAnswer := fun i _ => if i = 12 then some 11 else none }

/-- As `wExec`, but the owner hash collides on the executor `1` and address `9`. -/
def wExecCollide : Exec := { wExec with keccakOwner := fun a => if a = 9 then 1 else a }

/-- As `wExec`, but every reinitializer hands its own proxy's admin slot to `9`. -/
def wExecReinitSilent : Exec := { wExec with reinitAdmin := fun r A => upd A r.proxy 9 }

/-- As `wExecReinitSilent`, and implementation `11` answers `implementation()` with `11`. -/
def wExecReinit : Exec :=
  { wExecReinitSilent with implAnswer := fun i _ => if i = 11 then some 11 else none }

/-- Before the leg: governance owns the executor, the executor owns the `ProxyAdmin`, the
`ProxyAdmin` administers every proxy, and every proxy is at `10`. -/
def wWorld : World where
  owner := 100
  pendingOwner := 0
  paOwner := 1
  impl := fun _ => 10
  admin := fun _ => 2

/-- As `wWorld`, but proxy `5` is administered by `8`, not the `ProxyAdmin`, and runs `12`. -/
def wWorldForeign : World :=
  { wWorld with admin := upd wWorld.admin 5 8, impl := upd wWorld.impl 5 12 }

/-- The one participating row: proxy `5`, `10 → 11`. -/
def coreRow : Row := ⟨5, 10, 11, false⟩

/-- An inert slot. -/
def inertSlot : Row := ⟨0, 0, 0, false⟩

/-- A Core inventory of nine slots; slot 0 (`L1Bridgehub`) carries `coreRow`. -/
def coreInventory : List Row := coreRow :: List.replicate 8 inertSlot

/-- The Core transition at `3`, pinning engine `4`. -/
def coreTransition : TransitionObj := ⟨3, ⟨.core, coreInventory, 4⟩⟩

/-- `coreRow` with `callInitializeUpgrade` set. -/
def coreRowInit : Row := ⟨5, 10, 11, true⟩

/-- As `coreInventory`, with `coreRowInit` in slot 0. -/
def coreInventoryInit : List Row := coreRowInit :: List.replicate 8 inertSlot

/-- The Core transition whose one row calls its reinitializer. -/
def coreTransitionInit : TransitionObj := ⟨3, ⟨.core, coreInventoryInit, 4⟩⟩

/-- `wWorld` after its row is applied: proxy `5` at `11`. -/
def wAfter : World := { wWorld with impl := upd wWorld.impl 5 11 }

/-- Every address runs the default engine. -/
def wDefault (X : Exec) : Engines := fun _ => defaultEngine X

/-- Every address runs the release engine making `ops`. -/
def wRelease (X : Exec) (ops : List EngineOp) : Engines := fun _ => releaseEngine X ops

/-- Every address runs an engine that does nothing. -/
def wNoop : Engines := fun _ => noHook

end Contracts.ProxyUpgradeExecutorV35.CoreLeg
