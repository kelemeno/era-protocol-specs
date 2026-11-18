import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: the domain-holder check of `ProxyUpgradeExecutorBase` at `b17415d`

Source: era-contracts `draft/v0.35.0` at commit
**`b17415d2068065a4a3e3f0e7a14a2e96f54212e5`** (`b17415d` below). Every `file:line` is at
that commit, relative to `l1-contracts/contracts/`, unless it names OpenZeppelin or the
commit `d9f6789`. The OpenZeppelin v4 library is the submodule `lib/openzeppelin-contracts-v4`
at `dc44c9f1a` (release 4.9.6), imported as `@openzeppelin/contracts-v4`.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.DomainHoldersV35` and are proved in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.DomainHoldersV35`.

## Two commits

This topic was first modelled at `d9f678900e1bc8286412b78f56d4a9f443983c29` (`d9f6789`).
Between `d9f6789` and `b17415d`, `upgrades/registry/executors/ProxyUpgradeExecutorBase.sol`
changed in one commit, `9775be946` (#2669). `b17415d` itself (#2673) changes no file under
`l1-contracts/contracts/`. Of the other files cited here, `ChainTypeManager.sol`,
`ServerNotifier.sol`, `CTMUpgradeExecutor.sol`, `CoreUpgradeExecutor.sol` and
`ProxyUpgradeTransition.sol` are identical at the two commits, and so is the OpenZeppelin
submodule; `RegistryTypes.sol` and `ProxyUpgradeRowLib.sol` changed only in comments (the
lines cited moved, by 2 and by 5); `UpgradeExecutorBase.sol` changed only in `forward`, which
is not modelled; `IChainTypeManager.sol` and `IServerNotifier.sol` gained the getters
`admin()` (`:93`) and `chainTypeManager()` (`:42`).

What `b17415d` changes is the deployment procedure: a CTM whose proxies still sit behind the
ecosystem `ProxyAdmin` gets its own CTM-domain `ProxyAdmin` before the bootstrap, so that the
`ProxyAdmin` the CTM executor owns administers every CTM-domain proxy (era-contracts
`docs/upgrade-operations.md:44-83`), and the ServerNotifier proxy is moved under that
`ProxyAdmin` (`:9-42` there; `governance/ServerNotifier.sol:25-27`). `ExecutorHoldsCtm` asks
for the first (the `ProxyAdmin` the executor owns administers the CTM proxy), and the
witnesses also put the notifier under that `ProxyAdmin`.

The model below is the `b17415d` leg (`leg`). The `d9f6789` leg is kept as `D9.leg` (section
"The `d9f6789` leg") so that the two can be compared on the same engines.

## What the executor does around the engine (`b17415d`)

`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:51-104`, `_applyProxyUpgradeTransition`:

    ObjectAnchorLib.requireCode(address(_transition));                          // :57
    ProxyUpgradeTransitionManifest memory manifest = _transition.getManifest(); // :58
    if (manifest.domain != _domain) revert ProxyUpgradeDomainMismatch(...);     // :59-61
    ObjectAnchorLib.requireCode(manifest.proxyUpgradeEngine);                   // :63
    ProxyUpgradeContext memory context = ProxyUpgradeContext({ ... });         // :65-71
    if (_chainTypeManager != address(0)
            && IChainTypeManager(_chainTypeManager).admin() == address(_proxyAdmin)) {
        revert ProxyUpgradeCTMAdminIsProxyAdmin(_chainTypeManager);            // :75-77
    }
    address ownerBefore = owner(); address pendingOwnerBefore = pendingOwner(); // :78-79
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager); // :80
    (bool success, bytes memory returnData) = manifest.proxyUpgradeEngine.delegatecall(...); // :82-84
    if (!success) { revert(...) }                                               // :85-91
    if (owner() != ownerBefore || pendingOwner() != pendingOwnerBefore) revert ...;          // :93-95
    if (_domainHolders(_proxyAdmin, _chainTypeManager) != domainHoldersBefore)  // :96-98
        revert ProxyUpgradeEngineMovedDomainAuthority(...);
    ProxyUpgradeRow[] memory rows = ProxyUpgradeRowLib.toRows(manifest.proxyUpgrades,
        ProxyUpgradeRowLib.inventoryLength(_domain));                           // :99-102
    ProxyUpgradeRowLib.requireRowsApplied(_proxyAdmin, rows);                   // :103

`_domainHolders` (`:118-148`) hashes `abi.encode(_proxyAdmin.owner())` in the `Core` domain
(`:119-121`). With a CTM it reads `serverNotifier = ctm.serverNotifierAddress()` (`:123`) and
hashes the six words

    _proxyAdmin.owner(), ctm.owner(), ctm.pendingOwner(), IChainTypeManager(ctm).admin(),
    _proxyAdmin.getProxyAdmin(ctm), serverNotifier                              // :124-133

and, with a nonzero notifier, the five words `holders, notifier.owner(),
notifier.pendingOwner(), _proxyAdmin.getProxyAdmin(notifier),
IServerNotifier(notifier).chainTypeManager()` (`:137-147`). Its `@dev` (`:112-117`) says that a
proxy `_proxyAdmin` no longer administers passes `getProxyAdmin`'s `admin()` query to its
implementation, that a moved CTM answers its own `admin()` (the caller refusing that being the
`ProxyAdmin`) and a moved ServerNotifier has none and reverts the leg, and that the CTM's
`pendingAdmin` is not compared.

## What the holder values read

* `ProxyAdmin.getProxyAdmin(proxy)` (OZ `ProxyAdmin.sol:36-42`) is `address(proxy).staticcall(
  hex"f851a440")` (`admin()`), `require(success)`, decode. The caller is the `ProxyAdmin`.
* `TransparentUpgradeableProxy._fallback` (OZ `TransparentUpgradeableProxy.sol:84-107`): if
  `msg.sender == _getAdmin()`, the five selectors `upgradeTo`, `upgradeToAndCall`,
  `changeAdmin`, `admin` and `implementation` are served from the EIP-1967 slots (`admin()`
  returns the admin slot, `_dispatchAdmin` `:116-121`) and every other selector reverts with
  "admin cannot fallback to proxy target" (`:99`); otherwise the call is delegated to the
  implementation (`super._fallback()`, `:105`).
* So `admin()` sent to the CTM proxy, by the `ProxyAdmin` through `getProxyAdmin` or by the
  executor at `:75` and `:129`, returns the admin slot when the sender is the CTM proxy's admin,
  and otherwise the implementation's public `admin` getter, `ChainTypeManager.admin`
  (`state-transition/ChainTypeManager.sol:113`): the CTM's "non critical updates" role.
* `ServerNotifier` (`governance/ServerNotifier.sol:28`, `Ownable2Step`, `ReentrancyGuard`,
  `Initializable`) declares no `admin()` and no fallback, so the fall-through reverts and
  `require(success)` reverts the call. Its public `chainTypeManager` is `:30`.

## The operations an engine leg can use here

The engine runs by `delegatecall`, so its external calls come from the executor's address.
The executor owns the CTM and the CTM domain's `ProxyAdmin` (`CTMUpgradeExecutor.sol:20-21`,
`:38-40`, and `acceptCTMOwnership` `:55-61`).

* `ChainTypeManager.setPendingAdmin` (`:354-360`) is `onlyOwnerOrAdmin` (`:208-213`) and
  writes `pendingAdmin` (`:116`).
* `ChainTypeManager.acceptAdmin` (`:363-375`) requires `msg.sender == pendingAdmin`, then sets
  `admin = msg.sender` and deletes `pendingAdmin`.
* `ProxyAdmin.upgradeAndCall` (OZ `ProxyAdmin.sol:74-80`, `onlyOwner`) calls
  `proxy.upgradeToAndCall`; the proxy's admin branch (`TransparentUpgradeableProxy.sol:168-172`)
  runs `_upgradeToAndCall(newImplementation, data, true)` (OZ `ERC1967Upgrade.sol:59-64`):
  the implementation slot is written and `data` is delegatecalled into the implementation
  (`Address.functionDelegateCall`, OZ `Address.sol:180-187`) **in the proxy's frame**, where
  `msg.sender` is still the `ProxyAdmin`. `ProxyUpgradeRowLib.applyRows` uses this route for
  `initializeUpgrade()` reinitializers (`upgrades/registry/libraries/ProxyUpgradeRowLib.sol:121`).
* `ProxyAdmin.changeProxyAdmin` (OZ `ProxyAdmin.sol:51-53`, `onlyOwner`) calls
  `proxy.changeAdmin`; the admin branch (`TransparentUpgradeableProxy.sol:142-148`) writes the
  admin slot, refusing zero (`ERC1967Upgrade.sol:104-105`).
* A proxy's admin calling `upgradeTo` on it directly (`TransparentUpgradeableProxy.sol:154-161`)
  writes the implementation slot, which must be code (`ERC1967Upgrade.sol:39-42`).

## Modelling choices

* **A revert is `none`.** Events have no effect.
* **One CTM executor's view.** `Bindings` are the executor's immutables
  (`CTMUpgradeExecutor.sol:36-40`, `CoreUpgradeExecutor.sol:23`) and its own address.
* **Proxies are their two EIP-1967 slots** (`Tup`). What the implementation behind a proxy
  answers to a fall-through call is a field of the world, per proxy: `owner`,
  `pendingOwner` (OZ `Ownable2Step`/`Ownable2StepUpgradeable`), `adminAnswer` (`some a` for a
  public `admin` getter holding `a`, as `ChainTypeManager.sol:113`; `none` for an
  implementation without `admin()` and without a fallback, as `ServerNotifier`),
  `implAnswer` (the answer to `implementation()`) and `notifierCtm` (the answer to
  `chainTypeManager()`, `ServerNotifier.sol:30`). These answers do not depend on the caller,
  as for the public getters of `ChainTypeManager` and `ServerNotifier`; implementations whose
  answers depend on `msg.sender` are not represented. `owner`, `pendingOwner` and
  `notifierCtm` always answer: an implementation without them would only add reverts, which
  every "the leg reverts" conclusion here allows, and results that conclude a leg passes apply
  to implementations that have them, as `ChainTypeManager` and `ServerNotifier` do.
  `ChainTypeManager`'s `pendingAdmin` and `serverNotifierAddress` (`:116`, `:125`) are single
  fields, as there is one CTM. That the bound CTM and its notifier ARE OZ 4.9.6
  `TransparentUpgradeableProxy` instances is a deployment fact the model takes as given
  (`MODEL-DOMAIN-HOLDERS-V35` in `ASSUMPTIONS.md`).
* **`ProxyAdmin` is not a proxy**; its `owner()` is the field `paOwner`.
* **`keccak256(abi.encode(...))` is an arbitrary function `Hash` of the word list.** Every
  argument is a static 32-byte word, so `abi.encode` is the concatenation of the words, and
  two calls hash the same byte string exactly when their word lists are equal. No property of
  `Hash` is assumed anywhere; results that need distinct hashes say so as a pinned collision
  disjunct on the encodings compared (`HolderPairCollides`).
* **The engine is an arbitrary function** of the executor's address, the context, the
  manifest's slots and the world (`Engine`). The named engines below are built from the
  operations above.
* **`requireCode` is the predicate `Env.hasCode`**; `toRows`' length check is
  `Env.invLen`. The one `upgradeAndCall` modelled re-installs the CTM proxy's live
  implementation, so `_setImplementation`'s `isContract` check passes (the live implementation
  is the code that has been answering the proxy's calls) and the slot keeps its value.
* **Selectors the implementations do not have revert.** `ChainTypeManager`
  (`state-transition/ChainTypeManager.sol:58`) and `ServerNotifier`
  (`governance/ServerNotifier.sol:28`) declare no `fallback`, no `receive`, and none of
  `upgradeTo`, `upgradeToAndCall`, `changeAdmin`, `implementation`; a `ProxyAdmin` call to a
  proxy it does not administer therefore reverts for the first three, and `implementation()`
  is the field `implAnswer`.

## Scope

The statements are about one `_applyProxyUpgradeTransition` call and the operations
above. Not modelled: what the rest of an engine does (it is the arbitrary `Engine`, or the
arbitrary prefix `pre` constrained by `D9.HolderFrame`), `forward`, the implementation swaps of
the rows themselves (see `../ProxyUpgradeRowLib/`), and `msg.value`.
-/

namespace Contracts.DomainHoldersV35

open Clear

/-- Addresses as 256-bit words; `0` is the zero address. -/
abbrev Address := UInt256

/-- A 32-byte ABI word. -/
abbrev Word := UInt256

/-- `keccak256(abi.encode(w₁, …, wₖ))` for static words: an arbitrary function of the word
list. -/
abbrev Hash := List Word → Word

/-- Point update of an address-keyed mapping. -/
def upd {α : Type} (f : Address → α) (p : Address) (v : α) : Address → α :=
  fun x => if x = p then v else f x

/-- A `TransparentUpgradeableProxy` (OZ 4.9.6): its EIP-1967 admin and implementation
slots. -/
structure Tup where
  /-- `_getAdmin()`. -/
  adminSlot : Address
  /-- `_implementation()`. -/
  impl : Address
deriving DecidableEq

/-- The state the leg reads and the engine operations write. -/
structure World where
  /-- The executor's `owner()` (`UpgradeExecutorBase`, `Ownable2Step`,
  `governance/UpgradeExecutorBase.sol:23`). -/
  execOwner : Address
  /-- The executor's `pendingOwner()`. -/
  execPendingOwner : Address
  /-- The bound `ProxyAdmin`'s `owner()`. -/
  paOwner : Address
  /-- The EIP-1967 slots of each proxy. -/
  proxy : Address → Tup
  /-- `owner()` as the implementation behind proxy `p` answers it in `p`'s storage. -/
  owner : Address → Address
  /-- `pendingOwner()`, likewise. -/
  pendingOwner : Address → Address
  /-- `admin()` as the implementation behind `p` answers it: `some a` for a public `admin`
  getter holding `a` (`ChainTypeManager.sol:113`), `none` when it has no `admin()` and no
  fallback (`ServerNotifier.sol:28`), so the call reverts. -/
  adminAnswer : Address → Option Address
  /-- `implementation()` as the implementation behind `p` answers it (`none`: reverts). -/
  implAnswer : Address → Option Address
  /-- `ChainTypeManager.pendingAdmin` (`:116`) of the bound CTM. -/
  ctmPendingAdmin : Address
  /-- `ChainTypeManager.serverNotifierAddress` (`:125`) of the bound CTM. -/
  serverNotifier : Address
  /-- `chainTypeManager()` as the implementation behind `p` answers it (the public
  `ServerNotifier.chainTypeManager`, `ServerNotifier.sol:30`). -/
  notifierCtm : Address → Address

/-- `ProxyUpgradeDomain` (`upgrades/registry/RegistryTypes.sol:180-187`). -/
inductive Domain
  | core
  | ctm
deriving DecidableEq

/-- The executor's immutables and its own address. `pa` is `CTM_PROXY_ADMIN`
(`CTMUpgradeExecutor.sol:40`) or `PROXY_ADMIN` (`CoreUpgradeExecutor.sol:23`); `ctm` is
`CHAIN_TYPE_MANAGER` (`CTMUpgradeExecutor.sol:36`) or zero in the `Core` domain; `domain` is
the constant each entry point passes (`CTMUpgradeExecutor.sol:65-70`,
`CoreUpgradeExecutor.sol:34`). -/
structure Bindings where
  /-- `address(this)`: the executor. -/
  self : Address
  /-- The bound `ProxyAdmin`. -/
  pa : Address
  /-- The executor's domain. -/
  domain : Domain
  /-- The bound CTM proxy, or zero. -/
  ctm : Address

/-- The two fields of `ProxyUpgradeRow` the post-check reads. -/
structure Row where
  /-- The proxy. -/
  proxy : Address
  /-- Its target implementation; zero marks an inert slot. -/
  implNew : Address
deriving DecidableEq

/-- `ProxyUpgradeTransitionManifest` (`RegistryTypes.sol:205-209`), as `getManifest()`
returns it. -/
structure Manifest where
  /-- `domain`. -/
  domain : Domain
  /-- `proxyUpgrades`, the enum-indexed inventory. -/
  proxyUpgrades : List Row
  /-- `proxyUpgradeEngine`. -/
  engine : Address

/-- `ProxyUpgradeContext` (`RegistryTypes.sol:221-227`). -/
structure Context where
  /-- `transition`. -/
  transition : Address
  /-- `proxyUpgradeEngine`. -/
  proxyUpgradeEngine : Address
  /-- `domain`. -/
  domain : Domain
  /-- `proxyAdmin`. -/
  proxyAdmin : Address
  /-- `chainTypeManager`. -/
  chainTypeManager : Address
deriving DecidableEq

/-- The context the executor builds (`ProxyUpgradeExecutorBase.sol:65-71`): `tr` is the
`_transition` argument the entry point received from its `onlyOwner` caller
(`CTMUpgradeExecutor.sol:64`, `CoreUpgradeExecutor.sol:33`). -/
def buildContext (B : Bindings) (tr : Address) (m : Manifest) : Context :=
  { transition := tr
    proxyUpgradeEngine := m.engine
    domain := B.domain
    proxyAdmin := B.pa
    chainTypeManager := B.ctm }

/-- What the engine's `delegatecall` does: given `address(this)`, the context and the
manifest's slots, the world afterwards, or `none` for a revert. -/
abbrev Engine := Address → Context → List Row → World → Option World

/-- Run `e₁`, then `e₂` on its result, in the same delegatecall. -/
def Engine.andThen (e₁ e₂ : Engine) : Engine :=
  fun self ctx rows w => (e₁ self ctx rows w).bind (e₂ self ctx rows)

/-- The environment: the hash, code existence and the inventory length per domain. -/
structure Env where
  /-- `keccak256(abi.encode(...))`. -/
  H : Hash
  /-- `ObjectAnchorLib.requireCode` passes. -/
  hasCode : Address → Bool
  /-- `ProxyUpgradeRowLib.inventoryLength` (`ProxyUpgradeRowLib.sol:47-49`). -/
  invLen : Domain → ℕ

/-! ## Reading through the proxy -/

/-- An external call from `sender` to proxy `p` with a selector other than the five the admin
branch serves (`upgradeTo`, `upgradeToAndCall`, `changeAdmin`, `admin`, `implementation`), for
example `owner()`, `pendingOwner()`, `serverNotifierAddress()` or `chainTypeManager()`: reverts
when `sender` is `p`'s admin (`TransparentUpgradeableProxy.sol:99`), otherwise is answered by
the implementation (`:105`) with `ans`. -/
def fallthrough {α : Type} (w : World) (sender p : Address) (ans : α) : Option α :=
  if sender = (w.proxy p).adminSlot then none else some ans

/-- `admin()` sent by `sender` to proxy `p`: the admin slot when `sender` is `p`'s admin
(`_dispatchAdmin`, `TransparentUpgradeableProxy.sol:116-121`), otherwise whatever the
implementation's `admin()` answers, a revert if it has none. With `sender` the `ProxyAdmin`
this is `ProxyAdmin.getProxyAdmin(p)` (OZ `ProxyAdmin.sol:36-42`); with `sender` the executor
it is `IChainTypeManager(ctm).admin()` (`ProxyUpgradeExecutorBase.sol:75`, `:129`). -/
def adminCall (w : World) (sender p : Address) : Option Address :=
  if sender = (w.proxy p).adminSlot then some (w.proxy p).adminSlot else w.adminAnswer p

/-- `ProxyAdmin(pa).getProxyImplementation(p)` (OZ `ProxyAdmin.sol:21-27`): the implementation
slot when `pa` is `p`'s admin, otherwise whatever the implementation's `implementation()`
answers. -/
def getProxyImplementation (w : World) (pa p : Address) : Option Address :=
  if pa = (w.proxy p).adminSlot then some (w.proxy p).impl else w.implAnswer p

/-! ## The holder hash, `_domainHolders` (`ProxyUpgradeExecutorBase.sol:118-148`) -/

/-- The six words of `abi.encode(_proxyAdmin.owner(), ctm.owner(), ctm.pendingOwner(),
IChainTypeManager(ctm).admin(), _proxyAdmin.getProxyAdmin(ctm), serverNotifier)`
(`:124-133`), `serverNotifier` being `serverNotifierAddress()` (`:123`). The executor sends
`serverNotifierAddress()`, `owner()` and `pendingOwner()` (all revert exactly when it is the
CTM proxy's admin) and `admin()`; the `ProxyAdmin` sends `getProxyAdmin`'s `admin()`. -/
def ctmTuple (B : Bindings) (w : World) : Option (List Word) :=
  if B.self = (w.proxy B.ctm).adminSlot then none
  else
    match adminCall w B.self B.ctm, adminCall w B.pa B.ctm with
    | some a, some ca =>
      some [w.paOwner, w.owner B.ctm, w.pendingOwner B.ctm, a, ca, w.serverNotifier]
    | _, _ => none

/-- The last four words of the outer `abi.encode(holders, notifier.owner(),
notifier.pendingOwner(), _proxyAdmin.getProxyAdmin(notifier),
IServerNotifier(notifier).chainTypeManager())` (`:138-147`) for the notifier `n`: the executor
sends `owner()`, `pendingOwner()` and `chainTypeManager()` (all revert exactly when it is
`n`'s admin), the `ProxyAdmin` sends `getProxyAdmin`'s `admin()`. -/
def notifierReads (B : Bindings) (w : World) (n : Address) : Option (List Word) :=
  if B.self = (w.proxy n).adminSlot then none
  else (adminCall w B.pa n).map fun na => [w.owner n, w.pendingOwner n, na, w.notifierCtm n]

/-- The word list `_domainHolders(_proxyAdmin, _chainTypeManager)` hashes and returns the hash
of (`:118-148`): `[_proxyAdmin.owner()]` without a CTM (`:119-121`); the CTM tuple when the
CTM's `serverNotifierAddress()` is zero (`:134-136`); otherwise the outer tuple, whose first
word is the hash of the CTM tuple (`:137-147`). `none` if a read reverts. -/
def holderPreimage (B : Bindings) (H : Hash) (w : World) : Option (List Word) :=
  if B.ctm = 0 then some [w.paOwner]
  else
    match ctmTuple B w with
    | none => none
    | some e =>
      if w.serverNotifier = 0 then some e
      else (notifierReads B w w.serverNotifier).map (H e :: ·)

/-- `_domainHolders(_proxyAdmin, _chainTypeManager)` (`:118-148`). -/
def domainHolders (B : Bindings) (H : Hash) (w : World) : Option Word :=
  (holderPreimage B H w).map H

/-! ## The check before the engine (`:72-77`) -/

/-- The check at `:75-77` passes: there is no CTM, or the CTM's `admin()`, sent by the
executor, answers with an address other than the `ProxyAdmin`. (A revert of that call reverts
the leg.) -/
def CtmAdminOk (B : Bindings) (w : World) : Prop :=
  B.ctm = 0 ∨ ∃ a, adminCall w B.self B.ctm = some a ∧ a ≠ B.pa

instance (B : Bindings) (w : World) : Decidable (CtmAdminOk B w) :=
  decidable_of_iff
    (B.ctm = 0 ∨ (adminCall w B.self B.ctm).any (fun a => decide (a ≠ B.pa)) = true)
    (by
      unfold CtmAdminOk
      rcases adminCall w B.self B.ctm with _ | a <;> simp)

/-! ## The rows post-check (`:99-103`) -/

/-- `_dropInertSlots` (`ProxyUpgradeRowLib.sol:145-161`): a slot participates iff `implNew` is
set. -/
def toRows (slots : List Row) : List Row :=
  slots.filter (fun r => decide (r.implNew ≠ 0))

/-- `requireRowsApplied(_proxyAdmin, rows)` (`ProxyUpgradeRowLib.sol:133-141`) passes. -/
def rowsApplied (B : Bindings) (w : World) (rows : List Row) : Prop :=
  ∀ r ∈ rows, getProxyImplementation w B.pa r.proxy = some r.implNew

instance (B : Bindings) (w : World) (rows : List Row) : Decidable (rowsApplied B w rows) := by
  unfold rowsApplied; infer_instance

/-! ## The leg -/

/-- The checks before the delegatecall (`:57-63`) plus `toRows`' length check (`:99-102`;
it reads only the manifest, so its position does not matter). -/
def Prechecks (E : Env) (B : Bindings) (tr : Address) (m : Manifest) : Prop :=
  E.hasCode tr = true ∧ m.domain = B.domain ∧ E.hasCode m.engine = true
    ∧ m.proxyUpgrades.length = E.invLen B.domain

instance (E : Env) (B : Bindings) (tr : Address) (m : Manifest) :
    Decidable (Prechecks E B tr m) := by
  unfold Prechecks; infer_instance

/-- `_applyProxyUpgradeTransition(B.pa, tr, B.domain, B.ctm)` with `getManifest() = m`
(`ProxyUpgradeExecutorBase.sol:51-104`): the world after a successful leg, or `none`. -/
def leg (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w : World) :
    Option World :=
  if ¬ Prechecks E B tr m then none else
  if ¬ CtmAdminOk B w then none else
  match domainHolders B E.H w with
  | none => none
  | some before =>
    match eng B.self (buildContext B tr m) m.proxyUpgrades w with
    | none => none
    | some w' =>
      if w'.execOwner ≠ w.execOwner ∨ w'.execPendingOwner ≠ w.execPendingOwner then none
      else
        match domainHolders B E.H w' with
        | none => none
        | some after =>
          if after ≠ before then none
          else if rowsApplied B w' (toRows m.proxyUpgrades) then some w' else none

/-! ## The `d9f6789` leg

At `d9f6789`, `_applyProxyUpgradeTransition` (`ProxyUpgradeExecutorBase.sol:48-98` at that
commit) had no check on the CTM's `admin()` before the engine. It read the notifier once,
before the engine (`:71-73` there: zero without a CTM, else `serverNotifierAddress()`), and
passed it to both `_domainHolders` calls (`:74`, `:90`). `_domainHolders` (`:109-139` there)
hashed `[_proxyAdmin.owner()]` without a CTM, the four words `_proxyAdmin.owner(),
ctm.owner(), ctm.pendingOwner(), _proxyAdmin.getProxyAdmin(ctm)` (`:118-125` there), and with
a nonzero notifier the four words `holders, notifier.owner(), notifier.pendingOwner(),
_proxyAdmin.getProxyAdmin(notifier)` (`:130-138` there). Everything else in the leg is as at
`b17415d`. -/

namespace D9

/-- The four CTM words of `_domainHolders` at `d9f6789` (`:118-125` there). -/
def ctmWords (B : Bindings) (w : World) : Option (List Word) :=
  if B.self = (w.proxy B.ctm).adminSlot then none
  else (adminCall w B.pa B.ctm).map
    fun ca => [w.paOwner, w.owner B.ctm, w.pendingOwner B.ctm, ca]

/-- `notifier.owner()`, `notifier.pendingOwner()` and `_proxyAdmin.getProxyAdmin(notifier)` at
`d9f6789` (`:133-136` there). -/
def notifierReads (B : Bindings) (w : World) (n : Address) :
    Option (Address × Address × Address) :=
  if B.self = (w.proxy n).adminSlot then none
  else (adminCall w B.pa n).map fun na => (w.owner n, w.pendingOwner n, na)

/-- The four words of the outer `abi.encode` at `d9f6789` (`:130-138` there), `holders` being
the hash of `ctmWords`. -/
def notifierWords (B : Bindings) (H : Hash) (w : World) (n : Address) : Option (List Word) :=
  match ctmWords B w, notifierReads B w n with
  | some e, some (no, npo, na) => some [H e, no, npo, na]
  | _, _ => none

/-- `_domainHolders(_proxyAdmin, _chainTypeManager, n)` at `d9f6789` (`:109-139` there). -/
def domainHolders (B : Bindings) (H : Hash) (w : World) (n : Address) : Option Word :=
  if B.ctm = 0 then some (H [w.paOwner])
  else if n = 0 then (ctmWords B w).map H
  else (notifierWords B H w n).map H

/-- The notifier the `d9f6789` executor fixes before the engine runs (`:71-73` there): zero
without a CTM, otherwise `serverNotifierAddress()` sent by the executor. -/
def preNotifier (B : Bindings) (w : World) : Option Address :=
  if B.ctm = 0 then some 0
  else fallthrough w B.self B.ctm w.serverNotifier

/-- `_applyProxyUpgradeTransition(B.pa, tr, B.domain, B.ctm)` at `d9f6789` (`:48-98` there):
the world after a successful leg, or `none`. -/
def leg (E : Env) (B : Bindings) (tr : Address) (m : Manifest) (eng : Engine) (w : World) :
    Option World :=
  if ¬ Prechecks E B tr m then none else
  match preNotifier B w with
  | none => none
  | some n =>
    match domainHolders B E.H w n with
    | none => none
    | some before =>
      match eng B.self (buildContext B tr m) m.proxyUpgrades w with
      | none => none
      | some w' =>
        if w'.execOwner ≠ w.execOwner ∨ w'.execPendingOwner ≠ w.execPendingOwner then none
        else
          match domainHolders B E.H w' n with
          | none => none
          | some after =>
            if after ≠ before then none
            else if rowsApplied B w' (toRows m.proxyUpgrades) then some w' else none

/-- What an engine prefix that runs before the aliasing calls must leave alone for the
`d9f6789` statement: everything the `d9f6789` holder check and the executor-ownership check
read, at the CTM and at the pre-leg notifier `n`. The rows of other proxies may move. -/
structure HolderFrame (B : Bindings) (n : Address) (w₀ w₁ : World) : Prop where
  /-- Executor `owner()`. -/
  execOwner : w₁.execOwner = w₀.execOwner
  /-- Executor `pendingOwner()`. -/
  execPendingOwner : w₁.execPendingOwner = w₀.execPendingOwner
  /-- `ProxyAdmin.owner()`. -/
  paOwner : w₁.paOwner = w₀.paOwner
  /-- The CTM proxy's slots. -/
  ctmProxy : w₁.proxy B.ctm = w₀.proxy B.ctm
  /-- The CTM's owner. -/
  ctmOwner : w₁.owner B.ctm = w₀.owner B.ctm
  /-- The CTM's pending owner. -/
  ctmPendingOwner : w₁.pendingOwner B.ctm = w₀.pendingOwner B.ctm
  /-- The notifier proxy's slots. -/
  notifierProxy : w₁.proxy n = w₀.proxy n
  /-- The notifier's owner. -/
  notifierOwner : w₁.owner n = w₀.owner n
  /-- The notifier's pending owner. -/
  notifierPendingOwner : w₁.pendingOwner n = w₀.pendingOwner n
  /-- The notifier implementation's `admin()` answer. -/
  notifierAdmin : w₁.adminAnswer n = w₀.adminAnswer n

end D9

/-! ## Engine operations (each an external call from the executor's address) -/

/-- `ChainTypeManager(ctm).setPendingAdmin(y)` called by `sender` (`:354-360`): falls through
the proxy, then `onlyOwnerOrAdmin` (`:208-213`). -/
def ctmSetPendingAdmin (w : World) (ctm sender y : Address) : Option World :=
  if sender = (w.proxy ctm).adminSlot then none
  else if w.adminAnswer ctm ≠ some sender ∧ w.owner ctm ≠ sender then none
  else some { w with ctmPendingAdmin := y }

/-- The body of `acceptAdmin()` (`:363-375`) in the CTM's storage, with `msg.sender = s`. -/
def ctmAcceptAdminBody (w : World) (ctm s : Address) : Option World :=
  if s ≠ w.ctmPendingAdmin then none
  else some { w with adminAnswer := upd w.adminAnswer ctm (some s), ctmPendingAdmin := 0 }

/-- `ProxyAdmin(pa).upgradeAndCall(ctm, liveImpl, abi.encodeCall(acceptAdmin, ()))` called by
`sender`, `liveImpl` being the CTM proxy's current implementation (which `pa` can read with
`getProxyImplementation` while it administers the proxy): `onlyOwner` (OZ
`ProxyAdmin.sol:78`); unless `pa` is the CTM proxy's admin, the `upgradeToAndCall` selector
falls through to `ChainTypeManager`, which has no such function and no fallback, and reverts;
otherwise the implementation slot is rewritten with the value it holds and `acceptAdmin()`
runs in the proxy's frame with `msg.sender = pa` (`TransparentUpgradeableProxy.sol:168-172`,
`ERC1967Upgrade.sol:59-64`, `Address.sol:180-187`). -/
def paReinstallAndAcceptAdmin (w : World) (pa sender ctm : Address) : Option World :=
  if sender ≠ w.paOwner then none
  else if pa ≠ (w.proxy ctm).adminSlot then none
  else ctmAcceptAdminBody w ctm pa

/-- `ProxyAdmin(pa).changeProxyAdmin(p, x)` called by `sender` (OZ `ProxyAdmin.sol:51-53`,
`TransparentUpgradeableProxy.sol:142-148`, `ERC1967Upgrade.sol:104-105`). When `pa` is not
`p`'s admin the `changeAdmin` selector falls through to the implementation; the model takes
that to revert, as it does for `ChainTypeManager` and `ServerNotifier`. -/
def paChangeProxyAdmin (w : World) (pa sender p x : Address) : Option World :=
  if sender ≠ w.paOwner then none
  else if pa ≠ (w.proxy p).adminSlot then none
  else if x = 0 then none
  else some { w with proxy := upd w.proxy p { (w.proxy p) with adminSlot := x } }

/-- `upgradeTo(impl)` sent by `sender` straight to a proxy with slots `t` whose implementation
has no `upgradeTo` and no fallback (the CTM proxy): the slots afterwards, or `none`. The admin
branch (`TransparentUpgradeableProxy.sol:154-161`) writes the implementation slot if `impl` is
code (`ERC1967Upgrade.sol:39-42`); any other sender falls through and reverts. This is also
what `ProxyAdmin.upgrade` (OZ `ProxyAdmin.sol:62-64`) does to the proxy, with the `ProxyAdmin`
as `sender`. -/
def tupAdminUpgradeTo (hasCode : Address → Bool) (t : Tup) (sender impl : Address) :
    Option Tup :=
  if sender = t.adminSlot ∧ hasCode impl = true then some { t with impl := impl } else none

/-! ## Named engines -/

/-- **The aliasing leg.** (i) as CTM owner, `ctm.setPendingAdmin(PA)`;
(ii) `PA.upgradeAndCall(ctm, liveImpl, acceptAdmin())`, so `ChainTypeManager.admin` becomes the
`ProxyAdmin`; (iii) `PA.changeProxyAdmin(ctm, X)`. Every address it uses other than `X` comes
from the context and `address(this)`. -/
def aliasCtmProxyAdmin (X : Address) : Engine := fun self ctx _ w =>
  (ctmSetPendingAdmin w ctx.chainTypeManager self ctx.proxyAdmin).bind fun w₁ =>
  (paReinstallAndAcceptAdmin w₁ ctx.proxyAdmin self ctx.chainTypeManager).bind fun w₂ =>
  paChangeProxyAdmin w₂ ctx.proxyAdmin self ctx.chainTypeManager X

/-- An engine whose only effect is `ctm.setPendingAdmin(y)`. -/
def setCtmPendingAdmin (y : Address) : Engine := fun self ctx _ w =>
  ctmSetPendingAdmin w ctx.chainTypeManager self y

/-- An engine whose only effect is `PA.changeProxyAdmin(p, x)`. -/
def moveProxyAdmin (p x : Address) : Engine := fun self ctx _ w =>
  paChangeProxyAdmin w ctx.proxyAdmin self p x

/-- The engine that does nothing. -/
def idle : Engine := fun _ _ _ w => some w

/-! ## Premise bundles -/

/-- The pinned collision the comparison at `:96-98` cannot see past: the two CTM tuples read
before and after the engine differ and hash equal, or the two word lists whose hashes
`_domainHolders` returned (`holderPreimage`) differ and hash equal. Both pairs are the leg's
own reads. -/
def HolderPairCollides (B : Bindings) (H : Hash) (w w' : World) : Prop :=
  (B.ctm ≠ 0 ∧ ∃ e e', ctmTuple B w = some e ∧ ctmTuple B w' = some e' ∧ e ≠ e' ∧ H e = H e')
  ∨ (∃ p p', holderPreimage B H w = some p ∧ holderPreimage B H w' = some p' ∧ p ≠ p'
        ∧ H p = H p')

/-- The CTM executor's standing configuration (`CTMUpgradeExecutor.sol:20-21,36-51`): CTM
domain, nonzero CTM, the executor owns the CTM and the `ProxyAdmin`, the `ProxyAdmin`
administers the CTM proxy, the executor is not the `ProxyAdmin`, the notifier is not the CTM,
and the notifier is zero or its reads succeed (the executor is not its proxy's admin and
`getProxyAdmin(notifier)` answers). It says nothing about `ChainTypeManager.admin`; the check at
`:75-77` is the separate premise `CtmAdminOk`. -/
structure ExecutorHoldsCtm (B : Bindings) (w : World) : Prop where
  /-- `ProxyUpgradeDomain.CTM`. -/
  domainCtm : B.domain = .ctm
  /-- `CHAIN_TYPE_MANAGER ≠ 0` (`CTMUpgradeExecutor.sol:47`). -/
  ctmNonzero : B.ctm ≠ 0
  /-- The executor owns the CTM. -/
  ownsCtm : w.owner B.ctm = B.self
  /-- The executor owns the `ProxyAdmin`. -/
  ownsPa : w.paOwner = B.self
  /-- The `ProxyAdmin` administers the CTM proxy. -/
  paAdministersCtm : (w.proxy B.ctm).adminSlot = B.pa
  /-- The executor is not the `ProxyAdmin`. -/
  selfNotPa : B.self ≠ B.pa
  /-- The notifier is a different contract from the CTM. -/
  notifierNotCtm : w.serverNotifier ≠ B.ctm
  /-- Zero notifier, or the executor is not its proxy's admin and `getProxyAdmin` answers. -/
  notifierReadable : w.serverNotifier = 0 ∨
    (B.self ≠ (w.proxy w.serverNotifier).adminSlot
      ∧ (adminCall w B.pa w.serverNotifier).isSome)

end Contracts.DomainHoldersV35
