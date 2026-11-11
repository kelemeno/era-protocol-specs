import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `ProxyUpgradeRowLib` at `e561b9cc2`

Source: `l1-contracts/contracts/upgrades/registry/libraries/ProxyUpgradeRowLib.sol` on
branch `feat/upgrade-simplification` of the zksync-era `contracts` repository, at commit
**`e561b9cc2`** (2026-10-19), the commit `../../ChainTypeManager/` and
`../../RegistryBootstrapMigration/` are pinned to. The branch moves; every `file:line` below
is at that commit. `Specs/Rows.lean` models the same library at the earlier snapshot
`612a71ccc`; it is kept unchanged, and this file is a separate model in its own namespace
(`Contracts.ProxyUpgradeCurrent`).

**This file is definitions only.** The results are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsCurrent` and are proved in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrent`.

## What changed since `612a71ccc`

`git diff 612a71ccc e561b9cc2 -- …/ProxyUpgradeRowLib.sol`:

* `ProxyUpgradeRow` lost its `admin` field (`RegistryTypes.sol:168-173`), and `adminOf` and
  the foreign-admin skip (`ProxyRowLeftToAdministrator`) are gone. Every row is read and
  applied through the applier's one bound `ProxyAdmin` (`:121-141`).
* `requireRowsApplied` is gone. `applyRows` itself now ends with the same check, as a
  separate pass after every swap (`:142-147`):

      for (uint256 i = 0; i < length; ++i) {
          address liveImpl = _admin.getProxyImplementation(ITransparentUpgradeableProxy(_rows[i].proxy));
          if (liveImpl != _rows[i].implNew) {
              revert ProxyUpgradeRowMismatch(_rows[i].proxy, _rows[i].implNew, liveImpl);
          }
      }

  with the rationale (`:119-120`): "The verification is a separate pass after every swap, so
  a reinitializer that moves any proxy of the row set is caught too."
* `applyRows` begins with `requireRowCode(_rows)` (`:122`, `:89-95`): every `implNew` must
  be deployed code.
* `validateRows` refuses a self-edge (`:78-80`):

      if (row.expectedOldImpl == row.implNew) {
          revert RegistrySelfEdgeProxyRow(row.proxy);
      }

* `applyTransition` (`:102-113`) is the executors' entry: the transition object must be
  code, must report the applier's domain, and then `applyRows(_admin, _transition.rows())`.

## The loop body (`:124-141`)

    address liveImpl = _admin.getProxyImplementation(proxy);
    if (liveImpl == newImpl) { continue; }                                     // :128-130
    if (liveImpl != _rows[i].expectedOldImpl) { revert ProxyUpgradeRowMismatch(...); } // :131-133
    if (_rows[i].callInitializeUpgrade) {
        _admin.upgradeAndCall(proxy, newImpl, abi.encodeCall(IProxyUpgradeInitializable.initializeUpgrade, ()));
    } else {
        _admin.upgrade(proxy, newImpl);
    }                                                                          // :134-139

`ProxyAdmin.upgrade`/`upgradeAndCall` are `onlyOwner`, so the upgrade outcome requires the
applier to own `_admin`; a skip does not.

## Modelling choices

* **A revert is the absence of a step**, as in `Specs/Rows.lean`.
* **The live implementation is one mapping** (`Impl`), read through the bound admin. A
  proxy that `_admin` does not administer makes `getProxyImplementation` revert or return
  something else; the model does not cover that misconfiguration (the source says the bound
  admin "administers every proxy of its domain", `:116-117`).
* **The reinitializer is now modelled.** `upgradeAndCall` delegatecalls the new
  implementation's argument-less `initializeUpgrade()`. Its effect on the implementation
  mapping is `Config.reinit`, an arbitrary deterministic function of the row and the
  mapping. That over-approximates real code: a reinitializer runs in its own proxy's
  storage and can rewrite that proxy's implementation slot, but it can move another proxy
  only if it holds authority over it. `ReinitFrames` is the realistic case (it moves at
  most its own proxy) and is a premise where results need it. Its effects on other state
  are not modelled.
* **Code existence** (`ObjectAnchorLib.requireCode`) is a predicate `Config.hasCode`.
* **Events have no effect.**
* `toRows`'s length check only rejects; it is the caller's side condition, as before.
-/

namespace Contracts.ProxyUpgradeCurrent

open Clear

/-- Addresses as 256-bit words; `0` is the zero address, as in Solidity. -/
abbrev Address := UInt256

/-- Point update of a proxy-keyed mapping. -/
def upd (f : Address → Address) (p : Address) (v : Address) : Address → Address :=
  fun x => if x = p then v else f x

/-- `ProxyUpgradeRow` at `e561b9cc2` (`RegistryTypes.sol:168-173`): no `admin` field. -/
structure Row where
  /-- The proxy this row upgrades. -/
  proxy : Address
  /-- The implementation the proxy must be at for the row to apply. -/
  expectedOldImpl : Address
  /-- The implementation it is at afterwards. -/
  implNew : Address
  /-- Whether the swap is `upgradeAndCall(…, initializeUpgrade())`. -/
  callInitializeUpgrade : Bool
deriving DecidableEq

/-- The live implementation behind each proxy. -/
abbrev Impl := Address → Address

/-- The applying contract and its bound `ProxyAdmin`. -/
structure Config where
  /-- `address(this)` of the applying contract. -/
  self : Address
  /-- `_admin.owner()`. -/
  adminOwner : Address
  /-- `ObjectAnchorLib.requireCode` passes: the address holds deployed code. -/
  hasCode : Address → Prop
  /-- What `initializeUpgrade()` on the new implementation does to the implementation
  mapping, given the row and the mapping right after the swap. -/
  reinit : Row → Impl → Impl

/-- The reinitializers move at most their own proxy: they run in that proxy's storage. -/
def ReinitFrames (C : Config) : Prop :=
  ∀ (r : Row) (I : Impl) (q : Address), q ≠ r.proxy → C.reinit r I q = I q

/-- A row whose swap has no further effect on the mapping: no reinitializer, or an inert
one. -/
def RowInert (C : Config) (r : Row) : Prop :=
  r.callInitializeUpgrade = false ∨ ∀ I, C.reinit r I = I

/-- The state after the swap at `:134-139`. -/
def swap (C : Config) (r : Row) (I : Impl) : Impl :=
  if r.callInitializeUpgrade then C.reinit r (upd I r.proxy r.implNew) else upd I r.proxy r.implNew

/-- One iteration of the first loop. A mismatch has no constructor: the call reverts. -/
inductive ApplyRow (C : Config) : Impl → Row → Impl → Prop
  /-- `liveImpl == newImpl`: skipped (`:128-130`). -/
  | alreadyAtTarget {I r} : I r.proxy = r.implNew → ApplyRow C I r I
  /-- The edge: the proxy is at `expectedOldImpl` and the applier owns `_admin`. -/
  | upgrade {I r} : C.adminOwner = C.self → I r.proxy ≠ r.implNew →
      I r.proxy = r.expectedOldImpl → ApplyRow C I r (swap C r I)

/-- The first loop of `applyRows` (`:124-141`), in order. -/
inductive ApplyLoop (C : Config) : Impl → List Row → Impl → Prop
  | nil {I} : ApplyLoop C I [] I
  | cons {I J K r rs} : ApplyRow C I r J → ApplyLoop C J rs K → ApplyLoop C I (r :: rs) K

/-- The verification pass (`:142-147`): every row's proxy is at its `implNew`. -/
def RowsApplied (I : Impl) (rows : List Row) : Prop :=
  ∀ r ∈ rows, I r.proxy = r.implNew

/-- `requireRowCode` (`:89-95`). -/
def RowCode (C : Config) (rows : List Row) : Prop :=
  ∀ r ∈ rows, C.hasCode r.implNew

/-- A successful `applyRows(_admin, rows)` (`:121-148`) from `I` ending in `J`:
`requireRowCode`, the loop, then the verification pass on the final state. -/
structure ApplyRows (C : Config) (I : Impl) (rows : List Row) (J : Impl) : Prop where
  /-- `requireRowCode(_rows)` (`:122`). -/
  code : RowCode C rows
  /-- The first loop. -/
  loop : ApplyLoop C I rows J
  /-- The second loop. -/
  verified : RowsApplied J rows

/-- `validateRows` at `e561b9cc2` (`:71-87`). -/
structure ValidRows (rows : List Row) : Prop where
  /-- No placeholder rows (`:75-77`). -/
  fieldsNonzero : ∀ r ∈ rows, r.proxy ≠ 0 ∧ r.expectedOldImpl ≠ 0 ∧ r.implNew ≠ 0
  /-- No self-edge (`:78-80`). -/
  noSelfEdge : ∀ r ∈ rows, r.expectedOldImpl ≠ r.implNew
  /-- One row per proxy (`:81-85`). -/
  distinctProxies : rows.Pairwise (fun a b => a.proxy ≠ b.proxy)

/-- `validateRows` as it was at `612a71ccc`: the same checks without the self-edge one. -/
structure ValidRowsWithoutSelfEdgeCheck (rows : List Row) : Prop where
  /-- No placeholder rows. -/
  fieldsNonzero : ∀ r ∈ rows, r.proxy ≠ 0 ∧ r.expectedOldImpl ≠ 0 ∧ r.implNew ≠ 0
  /-- One row per proxy. -/
  distinctProxies : rows.Pairwise (fun a b => a.proxy ≠ b.proxy)

/-- `_dropInertSlots` (`:152-168`): a slot participates exactly when `implNew` is set. -/
def dropInertSlots (slots : List Row) : List Row :=
  slots.filter (fun r => decide (r.implNew ≠ 0))

/-- `toRows` (`:55-63`): the length check, then the drop. The check only rejects. -/
def toRows (slots : List Row) : List Row := dropInertSlots slots

/-- `ProxyUpgradeDomain` (`RegistryTypes.sol:178-185`). -/
inductive Domain
  | core
  | ctm
deriving DecidableEq

/-- A proxy upgrade transition object, read through its getters: its address, `domain()`
and `rows()`. -/
structure Transition where
  /-- The object's address. -/
  addr : Address
  /-- `domain()`. -/
  domain : Domain
  /-- `rows()`. -/
  rows : List Row

/-- A successful `applyTransition(_admin, T, d)` (`:102-113`). -/
def ApplyTransition (C : Config) (d : Domain) (T : Transition) (I J : Impl) : Prop :=
  C.hasCode T.addr ∧ T.domain = d ∧ ApplyRows C I T.rows J

/-! ## Witness data

Proxies `5`, `6`, `7`; implementations `10`, `11`, `12`; applier `1`. -/

/-- The applier owns its admin; every address has code; reinitializers do nothing. -/
def wConfig : Config where
  self := 1
  adminOwner := 1
  hasCode := fun _ => True
  reinit := fun _ I => I

/-- Every proxy starts at implementation `10`. -/
def wImpl : Impl := fun _ => 10

/-- Proxy `5`: `10 → 11`, no reinitializer. -/
def rowA : Row := ⟨5, 10, 11, false⟩

/-- Proxy `6`: `10 → 12`, with a reinitializer. -/
def rowB : Row := ⟨6, 10, 12, true⟩

/-- Proxy `5`: `11 → 12`. With `rowA`, two rows on one proxy. -/
def rowA2 : Row := ⟨5, 11, 12, false⟩

/-- Proxy `5`: `12 → 11`. With `rowA`, two rows on one proxy with the same target. -/
def rowA3 : Row := ⟨5, 12, 11, false⟩

/-- A self-edge on proxy `5`: `10 → 10`. -/
def rowSelf : Row := ⟨5, 10, 10, false⟩

/-- An inventory slot marked "not upgraded" for proxy `7`. -/
def slotInert : Row := ⟨7, 0, 0, false⟩

/-- The applier does not own its admin. -/
def wUnowned : Config := { wConfig with adminOwner := 2 }

/-- A reinitializer for `rowB` (proxy `6`) that also moves proxy `7` to `99`. -/
def wLeaky : Config := { wConfig with reinit := fun r I => if r = rowB then upd I 7 99 else I }

/-- A reinitializer for `rowB` (proxy `6`) that moves its own proxy back to `10`. -/
def wSelfMoving : Config := { wConfig with reinit := fun r I => if r = rowB then upd I 6 10 else I }

/-- A reinitializer for `rowB` (proxy `6`) whose effect on proxy `7` depends on where
proxy `5` is when it runs. -/
def wOrderSensitive : Config :=
  { wConfig with reinit := fun r I => if r = rowB then upd I 7 (if I 5 = 11 then 1 else 2) else I }

end Contracts.ProxyUpgradeCurrent
