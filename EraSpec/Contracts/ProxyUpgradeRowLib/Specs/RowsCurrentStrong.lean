import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent

/-!
# Model: when the `e561b9cc2` rows apply, and in which orders

Source: `l1-contracts/contracts/upgrades/registry/libraries/ProxyUpgradeRowLib.sol` at commit
**`e561b9cc2`**, the commit `Specs/RowsCurrent.lean` is pinned to. Every `file:line` below is
in that file at that commit.

**This file adds no new operation.** It reuses the model of `Specs/RowsCurrent.lean` unchanged
(`ApplyRow`, `ApplyLoop`, `ApplyRows`, `swap`, `ReinitFrames`, `RowInert`, ...) and adds two
predicates, `LocalSwap` and `RowApplies`, and witness data. The results are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsCurrentStrong` and are proved in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsCurrentStrong`.

## Why

`OrderIndependent` (`Properties/RowsCurrent.lean`) says that two *successful* calls over
permutations of the same rows agree, under `ReinitFrames`. It does not say that a permutation
of a successful call succeeds. The folder README reads `DuplicateRowsBreakOrder` as showing
that validation buys order-independent executability. Validation is necessary for that, but
under `ReinitFrames` it is not sufficient. `ReinitFrames` bounds which proxies a
reinitializer *writes*, not which ones it *reads*. A reinitializer can read where another
proxy is, for example through the `ProxyAdmin`'s `getProxyImplementation` view, which the
library itself calls (`:127`, `:143`). Such a reinitializer can make one order of valid rows
apply and the other revert (`wReadsOther`).

`LocalSwap` is the missing condition: the row's swap (`:134-139`, reinitializer included)
moves only the row's proxy, to an implementation that does not depend on the rest of the
mapping.
-/

namespace Contracts.ProxyUpgradeCurrent

/-- **THE ROW'S SWAP IS LOCAL.** There is one implementation `c` such that, from every mapping,
the swap at `:134-139` (`upgrade`, or `upgradeAndCall` with the reinitializer) leaves the
row's proxy at `c` and every other proxy where it was. A row without a reinitializer has it
with `c = implNew`, and so does an inert one (`RowInert`). A reinitializer has it if it moves at
most its own proxy and what it leaves there does not depend on the other proxies.
`ReinitFrames` alone does not give it: `wReadsOther` writes only its own proxy, but the value
depends on another one. -/
def LocalSwap (C : Config) (r : Row) : Prop :=
  ∃ c : Address, ∀ I : Impl, swap C r I = upd I r.proxy c

/-- **THE ROW APPLIES ON ITS OWN FROM `I`.** Its loop iteration succeeds from `I` and leaves its
proxy at `implNew`, so the row passes its own check in the verification pass (`:142-147`).
Either the proxy is already at `implNew` (`:128-130`); or the applier owns `_admin`, the
proxy is at `expectedOldImpl` (`:131-133`), and the swap leaves it at `implNew`. -/
def RowApplies (C : Config) (I : Impl) (r : Row) : Prop :=
  I r.proxy = r.implNew ∨
    (C.adminOwner = C.self ∧ I r.proxy = r.expectedOldImpl ∧ swap C r I r.proxy = r.implNew)

/-! ## Witness data

As in `Specs/RowsCurrent.lean`: proxies `5`, `6`, `7`; every proxy starts at implementation
`10` (`wImpl`); `rowA` is `5: 10 → 11` without a reinitializer, and `rowB` is `6: 10 → 12` with
one. -/

/-- `rowB`'s reinitializer writes only its own proxy `6`, so `ReinitFrames` holds. What it writes
depends on proxy `5`: `12` (its own target) if proxy `5` is already at `11`, and `10` otherwise.
So it reads a proxy it does not write. -/
def wReadsOther : Config :=
  { wConfig with reinit := fun r I => if r = rowB then upd I 6 (if I 5 = 11 then 12 else 10) else I }

/-- `rowB`'s reinitializer sets its own proxy `6` to its target `12`, whatever the mapping. It
is not inert: from a mapping with `6` elsewhere it moves `6`. Its swap is local. -/
def wLocalReinit : Config :=
  { wConfig with reinit := fun r I => if r = rowB then upd I 6 12 else I }

end Contracts.ProxyUpgradeCurrent
