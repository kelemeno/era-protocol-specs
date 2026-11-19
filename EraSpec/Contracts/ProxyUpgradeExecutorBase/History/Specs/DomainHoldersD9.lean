import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.DomainHoldersV35

/-!
# History: the `d9f6789` executor leg, next to the `b17415d20` one

**This is the record of an older commit, not a claim about `b17415d20`.** It keeps the leg of
`ProxyUpgradeExecutorBase._applyProxyUpgradeTransition` at era-contracts `draft/v0.35.0` commit
`d9f6789` (`d9f678900e1bc8286412b78f56d4a9f443983c29`), before `9775be946` (#2669) added the
check of the CTM's `admin()` before the engine and widened `_domainHolders`. It reuses the world,
the engine operations and the `b17415d20` leg of
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.DomainHoldersV35` unchanged, so the two legs
can be compared on the same engines (`Contracts.DomainHoldersV35.History.Properties.AliasingPassesAtD9CaughtAtB17`).
Every `file:line` marked "there" is at `d9f6789`.

**This file is definitions only.** The statements are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.History.Properties.DomainHoldersD9` and are proved
in `EraSpec.Contracts.ProxyUpgradeExecutorBase.History.Proofs.DomainHoldersD9`.
-/

namespace Contracts.DomainHoldersV35.History

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

end Contracts.DomainHoldersV35.History
