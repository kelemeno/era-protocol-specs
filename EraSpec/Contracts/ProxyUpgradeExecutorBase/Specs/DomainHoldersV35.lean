import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: the domain-holder check of `ProxyUpgradeExecutorBase` at `d9f6789`

Source: era-contracts `draft/v0.35.0` at commit
**`d9f678900e1bc8286412b78f56d4a9f443983c29`** (`d9f6789` below). Every `file:line` is at
that commit, relative to `l1-contracts/contracts/` unless it names OpenZeppelin. The
OpenZeppelin v4 library is the submodule `lib/openzeppelin-contracts-v4` at `dc44c9f1a`
(release 4.9.6), imported as `@openzeppelin/contracts-v4`.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Properties.DomainHoldersV35` and are proved in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.DomainHoldersV35`.

## What the executor does around the engine

`upgrades/registry/executors/ProxyUpgradeExecutorBase.sol:48-98`, `_applyProxyUpgradeTransition`:

    ObjectAnchorLib.requireCode(address(_transition));                          // :54
    ProxyUpgradeTransitionManifest memory manifest = _transition.getManifest(); // :55
    if (manifest.domain != _domain) revert ProxyUpgradeDomainMismatch(...);     // :56-58
    ObjectAnchorLib.requireCode(manifest.proxyUpgradeEngine);                   // :60
    ProxyUpgradeContext memory context = ProxyUpgradeContext({                  // :62-68
        transition: address(_transition),
        proxyUpgradeEngine: manifest.proxyUpgradeEngine,
        domain: _domain,
        proxyAdmin: address(_proxyAdmin),
        chainTypeManager: _chainTypeManager
    });
    address ownerBefore = owner(); address pendingOwnerBefore = pendingOwner(); // :69-70
    address serverNotifier = _chainTypeManager == address(0)                    // :71-73
        ? address(0) : IChainTypeManager(_chainTypeManager).serverNotifierAddress();
    bytes32 domainHoldersBefore = _domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier); // :74
    (bool success, bytes memory returnData) = manifest.proxyUpgradeEngine.delegatecall(...);     // :76-78
    if (!success) { revert(...) }                                               // :79-85
    if (owner() != ownerBefore || pendingOwner() != pendingOwnerBefore) revert ...;             // :87-89
    if (_domainHolders(_proxyAdmin, _chainTypeManager, serverNotifier) != domainHoldersBefore)  // :90-92
        revert ProxyUpgradeEngineMovedDomainAuthority(...);
    ProxyUpgradeRow[] memory rows = ProxyUpgradeRowLib.toRows(manifest.proxyUpgrades,            // :93-96
        ProxyUpgradeRowLib.inventoryLength(_domain));
    ProxyUpgradeRowLib.requireRowsApplied(_proxyAdmin, rows);                   // :97

`_domainHolders` (`:109-139`) hashes `abi.encode(_proxyAdmin.owner())` in the `Core` domain;
with a CTM it hashes

    holders = keccak256(abi.encode(_proxyAdmin.owner(), ctm.owner(), ctm.pendingOwner(),
                                   _proxyAdmin.getProxyAdmin(ctm)))             // :118-125

and, with a nonzero notifier, `keccak256(abi.encode(holders, notifier.owner(),
notifier.pendingOwner(), _proxyAdmin.getProxyAdmin(notifier)))` (`:130-138`). Its `@dev`
(`:106-108`) is the claim under test:

    A proxy `_proxyAdmin` no longer administers passes `getProxyAdmin`'s `admin()` query to its
    implementation: a moved CTM answers its own `admin()` and fails the comparison, a moved
    ServerNotifier has none and reverts the leg.

## What the holder values actually read

* `ProxyAdmin.getProxyAdmin(proxy)` (OZ `ProxyAdmin.sol:36-42`) is `address(proxy).staticcall(
  hex"f851a440")` (`admin()`), `require(success)`, decode. The caller is the `ProxyAdmin`.
* `TransparentUpgradeableProxy._fallback` (OZ `TransparentUpgradeableProxy.sol:84-107`; the
  `ifAdmin` modifier at `:73-79` is deprecated there and takes the same branch on the same
  test): if
  `msg.sender == _getAdmin()`, the five admin selectors are served from the EIP-1967 slots
  (`admin()` returns the admin slot, `_dispatchAdmin` `:116-121`) and every other selector
  reverts with "admin cannot fallback to proxy target" (`:99`); otherwise the call is
  delegated to the implementation (`super._fallback()`, `:105`).
* So `getProxyAdmin(ctm)` returns the admin slot while the `ProxyAdmin` is the CTM proxy's
  admin, and otherwise the CTM implementation's public `admin` getter,
  `ChainTypeManager.admin` (`state-transition/ChainTypeManager.sol:113`), a different
  variable: the CTM's "non critical updates" role.
* `ServerNotifier` (`governance/ServerNotifier.sol:28`, `Ownable2Step`, `ReentrancyGuard`,
  `Initializable`) declares no `admin()` and no fallback, so the fall-through reverts and
  `require(success)` reverts the leg.

## The operations an engine leg can use here

The engine runs by `delegatecall`, so its external calls come from the executor's address.
The executor owns the CTM (`CTMUpgradeExecutor.sol:20`, and `acceptCTMOwnership` `:55-61`) and
the CTM domain's `ProxyAdmin` (`:38-40`).

* `ChainTypeManager.setPendingAdmin` (`:354-360`) is `onlyOwnerOrAdmin` (`:208-213`) and
  writes `pendingAdmin` (`:116`).
* `ChainTypeManager.acceptAdmin` (`:363-375`) requires `msg.sender == pendingAdmin`, then sets
  `admin = msg.sender` and deletes `pendingAdmin`.
* `ProxyAdmin.upgradeAndCall` (OZ `ProxyAdmin.sol:74-80`, `onlyOwner`) calls
  `proxy.upgradeToAndCall`; the proxy's admin branch (`TransparentUpgradeableProxy.sol:168-172`)
  runs `_upgradeToAndCall(newImplementation, data, true)` (OZ `ERC1967Upgrade.sol:59-64`):
  the implementation slot is written and `data` is delegatecalled into the implementation
  (`Address.functionDelegateCall`, OZ `Address.sol:180-187`) **in the proxy's frame**, where
  `msg.sender` is still the `ProxyAdmin`. This is the route `ProxyUpgradeRowLib.applyRows`
  itself uses for `initializeUpgrade()` reinitializers (`ProxyUpgradeRowLib.sol:116`).
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
  implementation without `admin()` and without a fallback, as `ServerNotifier`) and
  `implAnswer` (the answer to `implementation()`). `owner` and `pendingOwner` always answer:
  an implementation without them would add reverts, which every "the leg reverts" result
  here already allows, and the legs shown to pass run against `ChainTypeManager` and
  `ServerNotifier`, which have both. `ChainTypeManager`'s `pendingAdmin` and
  `serverNotifierAddress` (`:116`, `:125`) are single fields, as there is one CTM.
  That the bound CTM and its notifier ARE OZ 4.9.6 `TransparentUpgradeableProxy` instances is
  a deployment fact the model takes as given. `MODEL-DOMAIN-HOLDERS-V35` in `ASSUMPTIONS.md`.
* **`ProxyAdmin` is not a proxy**; its `owner()` is the field `paOwner`.
* **`keccak256(abi.encode(...))` is an arbitrary function `Hash` of the word list.** Every
  argument is a static 32-byte word, so `abi.encode` is the concatenation of the words, and
  two calls hash the same byte string exactly when their word lists are equal. No property of
  `Hash` is assumed anywhere; results that need distinct hashes say so as a pinned collision
  disjunct on the two encodings compared.
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
arbitrary prefix `pre` constrained by `HolderFrame`), `forward`, the implementation swaps of
the rows themselves (see `../ProxyUpgradeRowLib/`), `setServerNotifier` (the notifier the leg
compares is the one read before the engine ran, `:71-74`), and `msg.value`.
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
  /-- The executor's `owner()` (`UpgradeExecutorBase`, `Ownable2Step`). -/
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

/-- `ProxyUpgradeDomain` (`upgrades/registry/RegistryTypes.sol`). -/
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

/-- `ProxyUpgradeTransitionManifest` (`RegistryTypes.sol:203-207`), as `getManifest()`
returns it. -/
structure Manifest where
  /-- `domain`. -/
  domain : Domain
  /-- `proxyUpgrades`, the enum-indexed inventory. -/
  proxyUpgrades : List Row
  /-- `proxyUpgradeEngine`. -/
  engine : Address

/-- `ProxyUpgradeContext` (`RegistryTypes.sol:219-225`). -/
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

/-- The context the executor builds (`ProxyUpgradeExecutorBase.sol:62-68`): `tr` is the
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
  /-- `ProxyUpgradeRowLib.inventoryLength` (`ProxyUpgradeRowLib.sol:42-44`). -/
  invLen : Domain → ℕ

/-! ## Reading through the proxy -/

/-- An external call from `sender` to proxy `p` with a selector that is none of the five admin
selectors (`owner()`, `pendingOwner()`, `serverNotifierAddress()`, `setPendingAdmin`,
`acceptAdmin`, …): reverts when `sender` is `p`'s admin (`TransparentUpgradeableProxy.sol:99`),
otherwise is answered by the implementation (`:105`). -/
def fallthrough {α : Type} (w : World) (sender p : Address) (ans : α) : Option α :=
  if sender = (w.proxy p).adminSlot then none else some ans

/-- `ProxyAdmin(pa).getProxyAdmin(p)` (OZ `ProxyAdmin.sol:36-42`): the admin slot when `pa` is
`p`'s admin (`_dispatchAdmin`, `TransparentUpgradeableProxy.sol:116-121`), otherwise whatever
the implementation's `admin()` answers, a revert if it has none. -/
def getProxyAdmin (w : World) (pa p : Address) : Option Address :=
  if pa = (w.proxy p).adminSlot then some (w.proxy p).adminSlot else w.adminAnswer p

/-- `ProxyAdmin(pa).getProxyImplementation(p)` (OZ `ProxyAdmin.sol:21-27`), likewise. -/
def getProxyImplementation (w : World) (pa p : Address) : Option Address :=
  if pa = (w.proxy p).adminSlot then some (w.proxy p).impl else w.implAnswer p

/-! ## The holder hash, `_domainHolders` (`ProxyUpgradeExecutorBase.sol:109-139`) -/

/-- The four words of `abi.encode(_proxyAdmin.owner(), ctm.owner(), ctm.pendingOwner(),
_proxyAdmin.getProxyAdmin(ctm))` (`:118-125`). `ctm.owner()` and `ctm.pendingOwner()` are
called by the executor and revert exactly when it is the CTM proxy's admin. -/
def ctmWords (B : Bindings) (w : World) : Option (List Word) :=
  if B.self = (w.proxy B.ctm).adminSlot then none
  else (getProxyAdmin w B.pa B.ctm).map
    fun ca => [w.paOwner, w.owner B.ctm, w.pendingOwner B.ctm, ca]

/-- `notifier.owner()`, `notifier.pendingOwner()` and `_proxyAdmin.getProxyAdmin(notifier)`
(`:133-136`). -/
def notifierReads (B : Bindings) (w : World) (n : Address) :
    Option (Address × Address × Address) :=
  if B.self = (w.proxy n).adminSlot then none
  else (getProxyAdmin w B.pa n).map fun na => (w.owner n, w.pendingOwner n, na)

/-- The four words of the outer `abi.encode(holders, notifier.owner(), notifier.pendingOwner(),
_proxyAdmin.getProxyAdmin(notifier))` (`:130-138`), `holders` being the hash of `ctmWords`. -/
def notifierWords (B : Bindings) (H : Hash) (w : World) (n : Address) : Option (List Word) :=
  match ctmWords B w, notifierReads B w n with
  | some e, some (no, npo, na) => some [H e, no, npo, na]
  | _, _ => none

/-- `_domainHolders(_proxyAdmin, _chainTypeManager, n)` (`:109-139`). -/
def domainHolders (B : Bindings) (H : Hash) (w : World) (n : Address) : Option Word :=
  if B.ctm = 0 then some (H [w.paOwner])
  else if n = 0 then (ctmWords B w).map H
  else (notifierWords B H w n).map H

/-- The notifier the executor fixes before the engine runs (`:71-73`): zero without a CTM,
otherwise `serverNotifierAddress()` called by the executor. -/
def preNotifier (B : Bindings) (w : World) : Option Address :=
  if B.ctm = 0 then some 0
  else fallthrough w B.self B.ctm w.serverNotifier

/-! ## The rows post-check (`:93-97`) -/

/-- `_dropInertSlots` (`ProxyUpgradeRowLib.sol:140-156`): a slot participates iff `implNew` is
set. -/
def toRows (slots : List Row) : List Row :=
  slots.filter (fun r => decide (r.implNew ≠ 0))

/-- `requireRowsApplied(_proxyAdmin, rows)` (`ProxyUpgradeRowLib.sol:128-136`) passes. -/
def rowsApplied (B : Bindings) (w : World) (rows : List Row) : Prop :=
  ∀ r ∈ rows, getProxyImplementation w B.pa r.proxy = some r.implNew

instance (B : Bindings) (w : World) (rows : List Row) : Decidable (rowsApplied B w rows) := by
  unfold rowsApplied; infer_instance

/-! ## The leg -/

/-- The checks before the delegatecall (`:54-60`) plus `toRows`' length check (`:93-96`;
it reads only the manifest, so its position does not matter). -/
def Prechecks (E : Env) (B : Bindings) (tr : Address) (m : Manifest) : Prop :=
  E.hasCode tr = true ∧ m.domain = B.domain ∧ E.hasCode m.engine = true
    ∧ m.proxyUpgrades.length = E.invLen B.domain

instance (E : Env) (B : Bindings) (tr : Address) (m : Manifest) :
    Decidable (Prechecks E B tr m) := by
  unfold Prechecks; infer_instance

/-- `_applyProxyUpgradeTransition(B.pa, tr, B.domain, B.ctm)` with `getManifest() = m`
(`ProxyUpgradeExecutorBase.sol:48-98`): the world after a successful leg, or `none`. -/
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

/-- `ChainTypeManager(ctm).acceptAdmin()` called by `sender`: falls through the proxy. -/
def ctmAcceptAdmin (w : World) (ctm sender : Address) : Option World :=
  if sender = (w.proxy ctm).adminSlot then none else ctmAcceptAdminBody w ctm sender

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

/-- An engine that makes the executor the CTM's `admin`: `ctm.setPendingAdmin(this)` then
`ctm.acceptAdmin()`. -/
def takeCtmAdmin : Engine := fun self ctx _ w =>
  (ctmSetPendingAdmin w ctx.chainTypeManager self self).bind fun w₁ =>
  ctmAcceptAdmin w₁ ctx.chainTypeManager self

/-- An engine whose only effect is `PA.changeProxyAdmin(p, x)`. -/
def moveProxyAdmin (p x : Address) : Engine := fun self ctx _ w =>
  paChangeProxyAdmin w ctx.proxyAdmin self p x

/-- The engine that does nothing. -/
def idle : Engine := fun _ _ _ w => some w

/-! ## Premise bundles -/

/-- The pinned collision the `@dev` at `:106-108` needs ruled out: the CTM tuple read before
and after hashes the same although the encodings differ, or (with a notifier) the outer
tuples do. -/
def HolderPairCollides (B : Bindings) (H : Hash) (w w' : World) (n : Address) : Prop :=
  (∃ e e', ctmWords B w = some e ∧ ctmWords B w' = some e' ∧ e ≠ e' ∧ H e = H e')
  ∨ (n ≠ 0 ∧ ∃ o o', notifierWords B H w n = some o ∧ notifierWords B H w' n = some o'
        ∧ o ≠ o' ∧ H o = H o')

/-- The CTM executor's standing configuration (`CTMUpgradeExecutor.sol:20,36-51`): CTM domain,
nonzero CTM, the executor owns the CTM and the `ProxyAdmin`, the `ProxyAdmin` administers the
CTM proxy, the executor is not the `ProxyAdmin`, the notifier is not the CTM, and the notifier
reads succeed (as they must for any leg to pass the check at `:74`). -/
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
  /-- Zero notifier, or its three reads succeed. -/
  notifierReadable : w.serverNotifier = 0 ∨ (notifierReads B w w.serverNotifier).isSome

/-- What an engine prefix that runs before the aliasing calls must leave alone: everything the
holder check and the executor-ownership check read, at the CTM and at the pre-leg notifier
`n`. The rows of other proxies may move. -/
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

end Contracts.DomainHoldersV35
