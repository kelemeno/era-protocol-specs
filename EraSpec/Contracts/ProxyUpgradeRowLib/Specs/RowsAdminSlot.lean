import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent

/-!
# Model: the rows at `e561b9cc2`, read through the proxies' admin dispatch

Source: `l1-contracts/contracts/upgrades/registry/libraries/ProxyUpgradeRowLib.sol` on
branch `feat/upgrade-simplification` of the zksync-era `contracts` repository at commit
**`e561b9cc2`**, the commit `Specs/RowsCurrent.lean` is pinned to. Library line numbers are at
that commit. The library as it first appears on era-contracts `draft/v0.35.0`, at commit
`ccf00623c` (#2525, 2026-10-19), has every library line cited here at the same number.

The proxy code the library calls is OpenZeppelin Contracts v4.9.6: the submodule
`lib/openzeppelin-contracts-v4` at `dc44c9f`, remapped as `@openzeppelin/contracts-v4/`
(`l1-contracts/foundry.toml:37` at `ccf00623c` and at `b17415d20`). `e561b9cc2` pins that
submodule commit (`../../RegistryBootstrapMigration/Specs/Forward.lean`), and so do `ccf00623c`
and the current `draft/v0.35.0` head `b17415d20`. OpenZeppelin paths below are under its
`contracts/proxy/`, with line numbers at `dc44c9f`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsAdminSlot` and are proved in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsAdminSlot`. It refines
`Specs/RowsCurrent.lean`, which it imports and leaves unchanged, in the sub-namespace
`Contracts.ProxyUpgradeCurrent.AdminSlot`. Names it does not redefine (`Row`, `upd`,
`ValidRows`, `Transition`, `rowA`, ...) are the `RowsCurrent` ones.

## What `RowsCurrent` reads as one mapping

`RowsCurrent` has one mapping, `Impl`. It stands both for what `applyRows` reads,
`_admin.getProxyImplementation(proxy)` (`ProxyUpgradeRowLib.sol:127`, `:143`), and for the
implementation each proxy runs, and `Config.reinit` changes only that mapping. In the
OpenZeppelin code these are two storage slots of the proxy, related through its admin
dispatch:

* `getProxyImplementation` is a `staticcall` of `implementation()` on the proxy
  (`transparent/ProxyAdmin.sol:21-27`). A `TransparentUpgradeableProxy` answers it itself,
  from its implementation slot, only when the caller is the address in its ERC-1967 admin
  slot (`transparent/TransparentUpgradeableProxy.sol:84-103`, `_dispatchImplementation` at
  `:130-135`; `_getAdmin` reads `_ADMIN_SLOT`, `ERC1967/ERC1967Upgrade.sol:92-99`). For any
  other caller it delegates the call to the code in its implementation slot
  (`TransparentUpgradeableProxy.sol:104-106`, `Proxy.sol:58-61`), and returns that code's
  answer.
* `ProxyAdmin.upgrade` and `upgradeAndCall` (`transparent/ProxyAdmin.sol:62-64`, `:74-80`) call
  `upgradeTo` and `upgradeToAndCall` on the proxy, which go through the same dispatch
  (`_dispatchUpgradeTo` and `_dispatchUpgradeToAndCall`,
  `TransparentUpgradeableProxy.sol:154-173`).
* `upgradeToAndCall` sets the implementation slot and then runs `initializeUpgrade()` on the
  new implementation by `delegatecall`, in the proxy's own storage
  (`ERC1967/ERC1967Upgrade.sol:59-64`). Code running there can write any slot of that proxy,
  the admin slot included.
* Both passes of `applyRows` read through `_admin` (`ProxyUpgradeRowLib.sol:127`, `:143`).

## The refinement

* **Each proxy has two slots** (`Slots`): `impl` (`_IMPLEMENTATION_SLOT`,
  `ERC1967/ERC1967Upgrade.sol:27`) and `admin` (`_ADMIN_SLOT`, `:92`).
* **The read goes through the dispatch** (`read`). It is the implementation slot when the
  admin slot holds `_admin` (`Config.proxyAdmin`). Otherwise it is the forwarded answer
  `Config.fwdRead`, where `none` is a revert.
* **The swap goes through the dispatch.** When `_admin` is the proxy's admin, the swap sets
  the implementation slot and then, for `upgradeAndCall`, runs the reinitializer (`swap`).
  Otherwise the call is delegated to the current implementation, and its effect is
  `Config.fwdCall` (`none`: it reverts).
* **The reinitializer can write both slots** (`Config.reinit : Row → Slots → Slots`).

## Modelling choices

* As in `RowsCurrent`: a revert is the absence of a step; the reinitializer, the forwarded
  answer and the forwarded call are arbitrary deterministic functions of the row and the
  slots (the forwarded answer is read under `staticcall`, so it changes nothing); code
  existence is `Config.hasCode`; events have no effect.
* **Every row's `proxy` is an OpenZeppelin v4.9.6 `TransparentUpgradeableProxy`, and `_admin`
  is an OpenZeppelin v4.9.6 `ProxyAdmin`.** Code at a row's proxy address that is not such a
  proxy is not covered.
* **Storage other than the two slots is not modelled.** Code whose behaviour depends on other
  storage is covered only as far as some function of the slots describes it. Calls that the
  reinitializer or forwarded code make to other contracts are covered only through their
  effect on the slots.
* **Omitted reject-only checks:** `_setImplementation`'s contract check
  (`ERC1967/ERC1967Upgrade.sol:39-42`) and `_requireZeroValue`
  (`TransparentUpgradeableProxy.sol:188-190`; `applyRows` sends no value). Omitting them only
  adds runs.

## Premises

* `SelfOnly`: the reinitializer and a forwarded swap call write only their own proxy's two
  slots, which is what running in that proxy's storage allows. Every projection of a
  `SelfOnly` configuration meets `ReinitFrames` (`SelfOnlyProjectsToReinitFrames`).
* `KeepsAdmin`: the reinitializer does not write its own proxy's admin slot. This is an
  assumption about the new implementation's code, which `RowsCurrent` builds in.
* `Administered`: when the call starts, `_admin` is the admin of every row's proxy. This is
  the source's "administers every proxy of its domain" (`ProxyUpgradeRowLib.sol:116-117`),
  which `RowsCurrent` also builds in (`Specs/RowsCurrent.lean:66-69`).

`lift` embeds each `RowsCurrent` configuration, and `Config.project` reads a configuration at
a fixed admin mapping as a `RowsCurrent` one. `RowsCurrent` is the fragment of this model in
which reinitializers keep every admin slot and `_admin` administers every row's proxy
(`LiftedCallIsRowsCurrentCall`, `ApplyRowsCorrespond`).

## At the current `draft/v0.35.0` head `b17415d20`

The library now lives on era-contracts `draft/v0.35.0` (`ProxyUpgradeRowLib.sol` at
`b17415d20`):

* `applyRows` is `:106-128`. `requireRowCode` (`:107`), the loop (`:109-126`, read at `:112`)
  and the two `ProxyAdmin` calls (`:119-124`) are as at `e561b9cc2`. The verification pass is
  now the function `requireRowsApplied` (`:133-141`, read at `:136`), called at `:127`, with
  the same loop body. The bound-admin sentence and the `@dev` on the separate pass are at
  `:100-105`, with the same text. So `ApplyRows` also describes `applyRows` at that head. The
  new `@dev` at `:28-32` is about applying a transition again and changes no code.
* `applyTransition` is gone. An executor checks the transition object and its domain
  (`executors/ProxyUpgradeExecutorBase.sol:57-63`) and delegatecalls the engine the object
  pins (`:82-91`); the default engine calls `applyRows`
  (`engines/DefaultProxyUpgradeEngine.sol:41-44`). After the engine returns, the executor
  compares the holders of its domain, which in a CTM domain include `getProxyAdmin` of the
  CTM and ServerNotifier proxies (`ProxyUpgradeExecutorBase.sol:96-98`, `:118-148`), and
  calls `requireRowsApplied` again (`:99-103`). `ApplyTransition` describes `e561b9cc2` only;
  executors and engines are not modelled here.
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
  (`transparent/TransparentUpgradeableProxy.sol:104-106`). `none`: it reverts, or its return
  data does not decode as an address. -/
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
  /-- The edge, with `_admin` as the proxy's admin: the proxy dispatches the swap itself.
  `ProxyAdmin`'s `onlyOwner` needs the applier to own `_admin`. -/
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

/-- A successful `applyTransition(_admin, T, d)` (`:102-113`), at `e561b9cc2` only. -/
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
and `66` for an admin slot that no longer holds `_admin`. -/

/-- `address(_admin)` in the witnesses. -/
def wAdmin : Address := 20

/-- Every proxy runs implementation `10` and is administered by `_admin`. -/
def wSlots : Slots := ⟨wImpl, fun _ => wAdmin⟩

/-- `RowsCurrent`'s witness configuration, lifted: the applier owns `_admin`, every address
has code, reinitializers do nothing, and forwarded calls revert. -/
def wCfg : Config := lift wConfig wAdmin

/-- `rowB`'s reinitializer writes only its own proxy `6`: it points the admin slot at `66`
and the implementation slot at `99`. A proxy running `99` answers a forwarded
`implementation()` with `12`, `rowB`'s target; any other implementation reverts on a
forwarded `implementation()`. -/
def wAdminRewrite : Config :=
  { wCfg with
    reinit := fun r S => if r = rowB then (S.setAdmin 6 66).setImpl 6 99 else S
    fwdRead := fun S p => if S.impl p = 99 then some 12 else none }

/-- As `wAdminRewrite`, but the implementation `rowB`'s reinitializer installs depends on
where proxy `5` is when it runs: `98` if proxy `5`'s implementation slot holds `11`, else
`99`. It still writes only proxy `6`. A proxy running `98` or `99` answers a forwarded
`implementation()` with `12`. -/
def wAdminRewriteOrder : Config :=
  { wCfg with
    reinit := fun r S =>
      if r = rowB then (S.setAdmin 6 66).setImpl 6 (if S.impl 5 = 11 then 98 else 99) else S
    fwdRead := fun S p => if S.impl p = 98 ∨ S.impl p = 99 then some 12 else none }

/-- `rowB`'s reinitializer moves its own proxy `6` back to `10`, as `wSelfMoving`'s does,
and also points its admin slot at `66`. A proxy running `10` answers a forwarded
`implementation()` with `12`. -/
def wAdminRewriteBack : Config :=
  { wCfg with
    reinit := fun r S => if r = rowB then (S.setAdmin 6 66).setImpl 6 10 else S
    fwdRead := fun S p => if S.impl p = 10 then some 12 else none }

/-- `wSelfMoving` lifted: `rowB`'s reinitializer moves proxy `6` back to `10` and leaves
every admin slot alone. -/
def wKeepAdminSelfMoving : Config := lift wSelfMoving wAdmin

/-- `wLeaky` lifted: `rowB`'s reinitializer (on proxy `6`) also sets proxy `7`'s
implementation slot to `99`, and leaves every admin slot alone. -/
def wKeepAdminLeaky : Config := lift wLeaky wAdmin

/-- Proxy `6` is administered by `66`, not `_admin`, and runs implementation `99`. Every
other proxy is as in `wSlots`. -/
def wSlotsForeign6 : Slots := ⟨upd wImpl 6 99, upd (fun _ => wAdmin) 6 66⟩

/-- Inert reinitializers, as in `wCfg`. A proxy running `99` answers a forwarded
`implementation()` with `12`. -/
def wForeignAnswers : Config :=
  { wCfg with fwdRead := fun S p => if S.impl p = 99 then some 12 else none }

end Contracts.ProxyUpgradeCurrent.AdminSlot
