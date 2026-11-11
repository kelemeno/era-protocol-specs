import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent

/-!
# Model: the rows at `e561b9cc2`, read through the proxies' admin dispatch

Source: `l1-contracts/contracts/upgrades/registry/libraries/ProxyUpgradeRowLib.sol` on
branch `feat/upgrade-simplification` of the zksync-era `contracts` repository at commit
**`e561b9cc2`**, the commit `Specs/RowsCurrent.lean` is pinned to, together with the
OpenZeppelin Contracts 4.9 proxy code it calls (`lib/openzeppelin-contracts-v4`, remapped as
`@openzeppelin/contracts-v4/` at `l1-contracts/foundry.toml:37`; line numbers below are from
v4.9.6, and none of the four proxy files cited has changed since v4.9.0). OpenZeppelin paths
are under `contracts/proxy/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsAdminSlot` and are proved in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsAdminSlot`. It refines
`Specs/RowsCurrent.lean`, which it imports and leaves unchanged, in the sub-namespace
`Contracts.ProxyUpgradeCurrent.AdminSlot`. Names it does not redefine (`Row`, `upd`,
`ValidRows`, `Transition`, `rowA`, ...) are the `RowsCurrent` ones.

## What `RowsCurrent` merges

`RowsCurrent` has one mapping, `Impl`. It stands both for what `applyRows` reads,
`_admin.getProxyImplementation(proxy)` (`ProxyUpgradeRowLib.sol:127`, `:143`), and for the
implementation each proxy runs. `Config.reinit` can change only that mapping. In the
contract these are different things:

* `getProxyImplementation` is a `staticcall` of `implementation()` on the proxy
  (`transparent/ProxyAdmin.sol:21-27`). A `TransparentUpgradeableProxy` answers it itself,
  from its implementation slot, only when the caller is the address in its ERC-1967 admin
  slot (`transparent/TransparentUpgradeableProxy.sol:84-103`, `_dispatchImplementation` at
  `:130-135`; `_getAdmin` reads `_ADMIN_SLOT`, `ERC1967/ERC1967Upgrade.sol:92-99`). For any
  other caller it delegates the call to its current implementation
  (`TransparentUpgradeableProxy.sol:104-106`, `Proxy.sol:58-61`), whose code decides the
  answer.
* `ProxyAdmin.upgrade` and `upgradeAndCall` (`transparent/ProxyAdmin.sol:62-80`) call
  `upgradeTo` and `upgradeToAndCall` on the proxy, which are dispatched the same way.
* `initializeUpgrade()` runs by `delegatecall` in the proxy's own storage, after
  `_upgradeTo` has set the implementation slot (`ERC1967/ERC1967Upgrade.sol:59-64`). It can
  write the admin slot as easily as the implementation slot. Nothing checks either slot
  again before the verification pass (`ProxyUpgradeRowLib.sol:142-147`), and that pass reads
  through `_admin` like the loop does.

So a reinitializer that writes only its own proxy's storage (the reading
`Specs/RowsCurrent.lean:70-77` gives `ReinitFrames`) can point its proxy's admin slot away
from `_admin` and its implementation slot at code whose `implementation()` returns
`implNew`. The verification read is then answered by that code.

## The refinement

* **Each proxy has two slots** (`Slots`): `impl` (`_IMPLEMENTATION_SLOT`) and `admin`
  (`_ADMIN_SLOT`).
* **The read goes through the dispatch** (`read`). It is the implementation slot when the
  admin slot holds `_admin` (`Config.proxyAdmin`). Otherwise it is the forwarded answer
  `Config.fwdRead`, where `none` is a revert.
* **The swap goes through the dispatch.** When `_admin` is the proxy's admin, the swap sets
  the implementation slot and then runs the reinitializer (`swap`). Otherwise the call is
  forwarded, and its effect is `Config.fwdCall` (`none`: it reverts).
* **The reinitializer can write both slots** (`Config.reinit : Row → Slots → Slots`).
* As in `RowsCurrent`, the reinitializer, the forwarded answer and the forwarded call are
  arbitrary deterministic functions of the row and the slots. A revert is the absence of a
  step, code existence is `Config.hasCode`, and events have no effect. Storage other than
  the two slots is not modelled, so code whose behaviour depends on it is covered only as far
  as some function of the slots describes it.

## Premises

* `SelfOnly`: the reinitializer and a forwarded call write only their own proxy's two
  slots. This is what "runs in its own proxy's storage" means. Every projection of a
  `SelfOnly` configuration meets `ReinitFrames` (`SelfOnlyProjectsToReinitFrames`).
* `KeepsAdmin`: the reinitializer does not write its own proxy's admin slot. This is an
  assumption about the new implementation's code, which `RowsCurrent` builds in.
* `Administered`: when the call starts, `_admin` is the admin of every row's proxy. This is
  the source's "administers every proxy of its domain" (`ProxyUpgradeRowLib.sol:116-117`),
  which `RowsCurrent` also builds in.

`RowsCurrent` is the `KeepsAdmin` and `Administered` fragment of this model. `lift` embeds
each `RowsCurrent` configuration, and `Config.project` reads a configuration at a fixed admin
mapping as a `RowsCurrent` one.
-/

namespace Contracts.ProxyUpgradeCurrent.AdminSlot

/-- The two ERC-1967 slots of every proxy (`ERC1967/ERC1967Upgrade.sol:27`, `:92`). -/
structure Slots where
  /-- `_IMPLEMENTATION_SLOT`: the code the proxy delegates to. -/
  impl : Address → Address
  /-- `_ADMIN_SLOT`: the one caller whose admin calls the proxy answers itself. -/
  admin : Address → Address

/-- `p`'s implementation slot set to `v`. -/
def Slots.setImpl (S : Slots) (p v : Address) : Slots := ⟨upd S.impl p v, S.admin⟩

/-- `p`'s admin slot set to `v`. -/
def Slots.setAdmin (S : Slots) (p v : Address) : Slots := ⟨S.impl, upd S.admin p v⟩

/-- The applying contract, its bound `ProxyAdmin`, and what code reached through a proxy
does. -/
structure Config where
  /-- `address(this)` of the applying contract. -/
  self : Address
  /-- `_admin.owner()`. -/
  adminOwner : Address
  /-- `address(_admin)`. -/
  proxyAdmin : Address
  /-- `ObjectAnchorLib.requireCode` passes: the address holds deployed code. -/
  hasCode : Address → Prop
  /-- What `initializeUpgrade()` does to the slots. It is delegatecalled in the row's proxy
  right after the proxy's implementation slot was set (`ERC1967/ERC1967Upgrade.sol:59-64`). -/
  reinit : Row → Slots → Slots
  /-- What the proxy at `p` answers to `implementation()` from a caller that is not its
  admin. The call is delegated to the code in `p`'s implementation slot
  (`transparent/TransparentUpgradeableProxy.sol:104-106`). `none`: it reverts. -/
  fwdRead : Slots → Address → Option Address
  /-- What `_admin.upgrade` or `upgradeAndCall` for the row does when `_admin` is not the
  proxy's admin. `upgradeTo` or `upgradeToAndCall` is delegated to the current
  implementation. `none`: it reverts. -/
  fwdCall : Row → Slots → Option Slots

/-- `_admin.getProxyImplementation(p)` (`transparent/ProxyAdmin.sol:21-27`): the
implementation slot if `_admin` is `p`'s admin (`_dispatchImplementation`), else whatever the
current implementation answers. `none`: the call reverts. -/
def read (C : Config) (S : Slots) (p : Address) : Option Address :=
  if S.admin p = C.proxyAdmin then some (S.impl p) else C.fwdRead S p

/-- The swap at `:134-139` when `_admin` is the proxy's admin: `_upgradeTo` sets the
implementation slot, then `upgradeAndCall` delegatecalls the reinitializer
(`ERC1967/ERC1967Upgrade.sol:59-64`). -/
def swap (C : Config) (r : Row) (S : Slots) : Slots :=
  if r.callInitializeUpgrade then C.reinit r (S.setImpl r.proxy r.implNew)
  else S.setImpl r.proxy r.implNew

/-- One iteration of the first loop (`:124-141`). `v` is `liveImpl`. A mismatch has no
constructor: the call reverts. -/
inductive ApplyRow (C : Config) : Slots → Row → Slots → Prop
  /-- `liveImpl == newImpl`: skipped (`:128-130`). -/
  | alreadyAtTarget {S r} : read C S r.proxy = some r.implNew → ApplyRow C S r S
  /-- The edge, with `_admin` as the proxy's admin: the proxy dispatches the swap itself. -/
  | upgrade {S r v} : C.adminOwner = C.self → read C S r.proxy = some v → v ≠ r.implNew →
      v = r.expectedOldImpl → S.admin r.proxy = C.proxyAdmin → ApplyRow C S r (swap C r S)
  /-- The edge, but `_admin` is not the proxy's admin: the swap call is delegated to the
  current implementation. -/
  | upgradeForwarded {S r v S'} : C.adminOwner = C.self → read C S r.proxy = some v →
      v ≠ r.implNew → v = r.expectedOldImpl → S.admin r.proxy ≠ C.proxyAdmin →
      C.fwdCall r S = some S' → ApplyRow C S r S'

/-- The first loop of `applyRows` (`:124-141`), in order. -/
inductive ApplyLoop (C : Config) : Slots → List Row → Slots → Prop
  | nil {S} : ApplyLoop C S [] S
  | cons {S K J r rs} : ApplyRow C S r K → ApplyLoop C K rs J → ApplyLoop C S (r :: rs) J

/-- The verification pass (`:142-147`): every row's proxy reads as its `implNew` through
`_admin`. -/
def RowsRead (C : Config) (S : Slots) (rows : List Row) : Prop :=
  ∀ r ∈ rows, read C S r.proxy = some r.implNew

/-- `requireRowCode` (`:89-95`). -/
def RowCode (C : Config) (rows : List Row) : Prop :=
  ∀ r ∈ rows, C.hasCode r.implNew

/-- A successful `applyRows(_admin, rows)` (`:121-148`) from `S` ending in `J`. -/
structure ApplyRows (C : Config) (S : Slots) (rows : List Row) (J : Slots) : Prop where
  /-- `requireRowCode(_rows)` (`:122`). -/
  code : RowCode C rows
  /-- The first loop. -/
  loop : ApplyLoop C S rows J
  /-- The second loop. -/
  verified : RowsRead C J rows

/-- A successful `applyTransition(_admin, T, d)` (`:102-113`). -/
def ApplyTransition (C : Config) (d : Domain) (T : Transition) (S J : Slots) : Prop :=
  C.hasCode T.addr ∧ T.domain = d ∧ ApplyRows C S T.rows J

/-- **Code running in a proxy writes only that proxy's two slots.** Both the reinitializer
and a forwarded swap call run by `delegatecall` in the proxy's storage. To move another proxy
they would need authority over it. -/
def SelfOnly (C : Config) : Prop :=
  (∀ (r : Row) (S : Slots) (q : Address), q ≠ r.proxy →
      (C.reinit r S).impl q = S.impl q ∧ (C.reinit r S).admin q = S.admin q) ∧
    ∀ (r : Row) (S S' : Slots), C.fwdCall r S = some S' → ∀ q, q ≠ r.proxy →
      S'.impl q = S.impl q ∧ S'.admin q = S.admin q

/-- **The reinitializer does not write its own proxy's admin slot.** -/
def KeepsAdmin (C : Config) : Prop :=
  ∀ (r : Row) (S : Slots), (C.reinit r S).admin r.proxy = S.admin r.proxy

/-- **`_admin` administers every row's proxy when the call starts.** -/
def Administered (C : Config) (S : Slots) (rows : List Row) : Prop :=
  ∀ r ∈ rows, S.admin r.proxy = C.proxyAdmin

/-- The `RowsCurrent` configuration of `C` at the fixed admin mapping `A`: the
reinitializer's effect on the implementation slots. -/
def Config.project (C : Config) (A : Address → Address) : ProxyUpgradeCurrent.Config where
  self := C.self
  adminOwner := C.adminOwner
  hasCode := C.hasCode
  reinit := fun r I => (C.reinit r ⟨I, A⟩).impl

/-- A `RowsCurrent` configuration as a refined one with `_admin` at `a`: the reinitializer
leaves every admin slot alone, and forwarded calls revert. -/
def lift (C0 : ProxyUpgradeCurrent.Config) (a : Address) : Config where
  self := C0.self
  adminOwner := C0.adminOwner
  proxyAdmin := a
  hasCode := C0.hasCode
  reinit := fun r S => ⟨C0.reinit r S.impl, S.admin⟩
  fwdRead := fun _ _ => none
  fwdCall := fun _ _ => none

/-! ## Witness data

As in `Specs/RowsCurrent.lean`: proxies `5`, `6`, `7`; implementations `10`, `11`, `12`;
applier `1`; `rowA` is `5: 10 → 11` and `rowB` is `6: 10 → 12` with a reinitializer.
`_admin` is `20`. Implementations `98` and `99` stand for code installed by a reinitializer,
and `66` for an admin slot pointed away from `_admin`. -/

/-- `address(_admin)` in the witnesses. -/
def wAdmin : Address := 20

/-- Every proxy runs implementation `10` and is administered by `_admin`. -/
def wSlots : Slots := ⟨wImpl, fun _ => wAdmin⟩

/-- `RowsCurrent`'s witness configuration, lifted: the applier owns `_admin`, every address
has code, reinitializers do nothing, and forwarded calls revert. -/
def wCfg : Config := lift wConfig wAdmin

/-- `rowB`'s reinitializer rewrites only its own proxy `6`: it points the admin slot at `66`
and the implementation slot at `99`. Implementation `99`'s `implementation()` returns `12`,
`rowB`'s target. Any other implementation reverts on `implementation()`. -/
def wAdminRewrite : Config :=
  { wCfg with
    reinit := fun r S => if r = rowB then (S.setAdmin 6 66).setImpl 6 99 else S
    fwdRead := fun S p => if S.impl p = 99 then some 12 else none }

/-- As `wAdminRewrite`, but the implementation `rowB`'s reinitializer installs depends on
where proxy `5` is when it runs: `98` if proxy `5` is at `11`, else `99`. It still writes
only proxy `6`. Both `98` and `99` answer `implementation()` with `12`. -/
def wAdminRewriteOrder : Config :=
  { wCfg with
    reinit := fun r S =>
      if r = rowB then (S.setAdmin 6 66).setImpl 6 (if S.impl 5 = 11 then 98 else 99) else S
    fwdRead := fun S p => if S.impl p = 98 ∨ S.impl p = 99 then some 12 else none }

/-- `rowB`'s reinitializer moves its own proxy `6` back to `10`, as `wSelfMoving`'s does,
and also points its admin slot at `66`. The source implementation `10` answers
`implementation()` with `12`, for instance through a getter of a storage word the
reinitializer wrote. -/
def wAdminRewriteBack : Config :=
  { wCfg with
    reinit := fun r S => if r = rowB then (S.setAdmin 6 66).setImpl 6 10 else S
    fwdRead := fun S p => if S.impl p = 10 then some 12 else none }

/-- `wSelfMoving` lifted: `rowB`'s reinitializer moves proxy `6` back to `10` and leaves
the admin slot alone. -/
def wKeepAdminSelfMoving : Config := lift wSelfMoving wAdmin

/-- Proxy `6` is administered by `66`, not `_admin`, and runs implementation `99`. Every
other proxy is as in `wSlots`. -/
def wSlotsForeign6 : Slots := ⟨upd wImpl 6 99, upd (fun _ => wAdmin) 6 66⟩

/-- Inert reinitializers, as in `wCfg`. Implementation `99` answers `implementation()` with
`12`. -/
def wForeignAnswers : Config :=
  { wCfg with fwdRead := fun S p => if S.impl p = 99 then some 12 else none }

end Contracts.ProxyUpgradeCurrent.AdminSlot
