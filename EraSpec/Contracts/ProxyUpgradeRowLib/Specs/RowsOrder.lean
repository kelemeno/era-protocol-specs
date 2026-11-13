import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsUnvalidated

/-!
# Model: which row orders succeed (`e561b9cc2`)

Source: `l1-contracts/contracts/upgrades/registry/libraries/ProxyUpgradeRowLib.sol` on branch
`feat/upgrade-simplification` of the zksync-era `contracts` repository at commit
**`e561b9cc2`**, the commit `Specs/RowsCurrent.lean` is pinned to. Every `file:line` below is
at that commit.

**This file adds no new operation.** It reuses the `RowsCurrent` model unchanged (`ApplyRows`,
`ReinitFrames`, the witness rows) and the witness configuration `wLeakNamed` of
`Specs/RowsUnvalidated.lean`, and adds one predicate on reinitializers,
`ReinitReadsOwnProxy`, and one witness configuration. The results are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsOrder` and are proved in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsOrder`.

## Why the order can decide whether the call reverts

`applyRows` (`:121-148`) runs the swaps in row order (`:124-141`) and verifies every row
afterwards (`:142-147`). A reinitializer runs inside the first loop, right after its own
row's swap and before the swaps of every later row (`:134-136`). `OrderIndependent`
(`Properties/RowsCurrent.lean`) compares two calls that both succeeded; it does not say that
one order succeeds when the other does.

`ReinitFrames` bounds what a reinitializer *writes*: at most its own proxy. It does not bound
what it *reads*. A reinitializer can call another proxy like any other contract, and what it
gets back depends on that proxy's implementation. If it reads the proxy of another row, it
sees that row applied in one order and not yet applied in the other, and it can leave its own
proxy where the verification refuses it in one order only.

## Modelling choices

* As in `Specs/RowsCurrent.lean`, `Config.reinit` is an arbitrary deterministic function of
  the row and the whole mapping.
* `ReinitReadsOwnProxy` is the stronger premise under which the order does not matter: where
  the reinitializer leaves its own proxy depends only on where that proxy is. Together with
  `ReinitFrames`, each reinitializer is then a function of its own proxy's implementation
  alone. Like `ReinitFrames` it is an assumption about reinitializer code; the library checks
  neither.
-/

namespace Contracts.ProxyUpgradeCurrent

/-- **A REINITIALIZER READS ONLY ITS OWN PROXY.** Where the reinitializer leaves its own
proxy depends only on where that proxy is: two mappings that agree at the row's proxy give
the same value there. What it writes elsewhere is `ReinitFrames`'s concern, not this one's. -/
def ReinitReadsOwnProxy (C : Config) : Prop :=
  ∀ (r : Row) (I I' : Impl), I r.proxy = I' r.proxy →
    C.reinit r I r.proxy = C.reinit r I' r.proxy

/-! ## Witness data

As in `Specs/RowsCurrent.lean`: proxies `5`, `6`; every proxy starts at implementation `10`
(`wImpl`); `rowA` is `5: 10 → 11` and `rowB` is `6: 10 → 12` with a reinitializer. -/

/-- `rowB`'s reinitializer (on proxy `6`) leaves its proxy where the swap put it if proxy `5`
is at `11`, `rowA`'s target, and otherwise moves it back to `10`. It writes only proxy `6`, so
`ReinitFrames` holds; it reads proxy `5`, so `ReinitReadsOwnProxy` fails. -/
def wReadsOtherProxy : Config :=
  { wConfig with
    reinit := fun r I => if r = rowB then (if I 5 = 11 then I else upd I 6 10) else I }

end Contracts.ProxyUpgradeCurrent
