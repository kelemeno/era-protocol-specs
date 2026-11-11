import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent

/-!
# Model: rows that `validateRows` never checked (`e561b9cc2`)

Source: `l1-contracts/contracts/upgrades/registry/` on branch `feat/upgrade-simplification`
of the zksync-era `contracts` repository at commit **`e561b9cc2`**, the commit
`Specs/RowsCurrent.lean` is pinned to. Paths below are relative to that directory.

**This file adds no new operation.** It reuses the `RowsCurrent` model unchanged
(`ApplyRows`, `ApplyTransition`, `ReinitFrames`, ...) and adds one predicate, `Genuine`, and
witness data. The results are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsUnvalidated` and are proved in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsUnvalidated`.

## Where unvalidated rows come from

Both domain executors apply a transition object they are handed:

    function applyInfrastructureUpgrade(IProxyUpgradeTransition _infrastructureTransition) external onlyOwner {
        ProxyUpgradeRowLib.applyTransition(CTM_PROXY_ADMIN, _infrastructureTransition, ProxyUpgradeDomain.CTM);
                                                    // executors/CTMUpgradeExecutor.sol:64-67
    function applyL1Upgrade(IProxyUpgradeTransition _coreTransition) external onlyOwner {
        ProxyUpgradeRowLib.applyTransition(PROXY_ADMIN, _coreTransition, ProxyUpgradeDomain.Core);
                                                    // executors/CoreUpgradeExecutor.sol:33-36

and `applyTransition` (`libraries/ProxyUpgradeRowLib.sol:102-113`) checks only that the
object is code (`:107`) and reports the domain (`:108-111`), then runs
`applyRows(_admin, _transition.rows())` (`:112`). It does not check that the object is a
`ProxyUpgradeTransition`, and `applyRows` (`:121-148`) does not call `validateRows`.

Only a genuine `ProxyUpgradeTransition` validated its rows. Its constructor flattens the
manifest's inventory with `toRows`, refuses an empty result and runs `validateRows`
(`objects/ProxyUpgradeTransition.sol:26-37`, the refusal at `:33-35`, the check at `:36`),
and `rows()` recomputes the same list from the manifest (`:50-57`), which only the
constructor writes (`objects/ManifestStorage.sol:11-15`; the object has no state-mutating
function, `ProxyUpgradeTransition.sol:14-17`). Any other contract that answers `domain()`
and `rows()` gets its rows applied as they are: rows on the same proxy, self-edges and zero
fields included. The parameter is documented as "The write-once
transition approved by governance" (`executors/ICTMUpgradeExecutor.sol:35`,
`executors/ICoreUpgradeExecutor.sol:17`; `libraries/ProxyUpgradeRowLib.sol:100`), and the
off-chain review before the vote checks the object's code identity and its rows, duplicate
proxies included (`protocol-docs/ecosystem-upgrade.md:354`, repository root). Neither is
enforced by `applyTransition`; the executor's owner can pass any object.

## Modelling choices

* **The object is its two getters, each read once.** `domain()` and `rows()` are `view`
  (`objects/IProxyUpgradeTransition.sol:20`, `:24`), so Solidity calls them with
  `STATICCALL` and the object cannot change state while answering. `applyTransition` reads
  each once (`libraries/ProxyUpgradeRowLib.sol:108`, `:112`). So
  `ProxyUpgradeCurrent.Transition`, an address, a domain and a row list with no condition on
  the rows, describes any object, genuine or not.
* **`Genuine` is what a real `ProxyUpgradeTransition`'s rows satisfy**: nonempty and
  `ValidRows` (nonzero fields, no self-edge, one row per proxy). The inventory length check
  in `toRows` only rejects and leaves no trace in the rows, so it is not part of it.
* Everything else is as in `Specs/RowsCurrent.lean`. In particular a reinitializer's effect
  on the implementation mapping is the arbitrary function `Config.reinit`, and
  `ReinitFrames` (it moves at most its own proxy) is a premise where results need it.
-/

namespace Contracts.ProxyUpgradeCurrent

/-- **A GENUINE `ProxyUpgradeTransition`.** What the object's constructor established about
the rows `rows()` returns (`objects/ProxyUpgradeTransition.sol:26-37`, `:50-57`): there is at
least one row (`:33-35`) and the rows pass `validateRows` (`:36`). `ApplyTransition` does not
require it: `applyTransition` checks only the object's code and `domain()`
(`libraries/ProxyUpgradeRowLib.sol:102-113`). -/
def Transition.Genuine (T : Transition) : Prop :=
  T.rows ≠ [] ∧ ValidRows T.rows

/-! ## Witness data

As in `Specs/RowsCurrent.lean`: proxies `5`, `6`, `7`; every proxy starts at
implementation `10` (`wImpl`); `rowA` is `5: 10 → 11`, `rowA2` is `5: 11 → 12`, `rowA3` is
`5: 12 → 11`, and `rowB` is `6: 10 → 12` with a reinitializer. -/

/-- Proxy `6`: `11 → 12`, no reinitializer. With `rowB` (`6: 10 → 12`), a second row on one
proxy, with the same target. -/
def rowB2 : Row := ⟨6, 11, 12, false⟩

/-- Proxy `6`: `10 → 11`, no reinitializer. With `rowB`, a second row on one proxy, with a
different target. -/
def rowB3 : Row := ⟨6, 10, 11, false⟩

/-- `rowB`'s reinitializer moves its own proxy `6` on to `11`, `rowB2`'s source. It moves
nothing else, so `ReinitFrames` holds. -/
def wDetour : Config :=
  { wConfig with reinit := fun r I => if r = rowB then upd I 6 11 else I }

/-- `rowB`'s reinitializer (on proxy `6`) moves proxy `5` to `11`, `rowA2`'s source.
`ReinitFrames` fails. -/
def wLeakNamed : Config :=
  { wConfig with reinit := fun r I => if r = rowB then upd I 5 11 else I }

/-- A CTM-domain object that answers `domain()` and `rows()` but is not a genuine
`ProxyUpgradeTransition`: its rows `rowB`, `rowB2` name proxy `6` twice. -/
def wDupTransition : Transition := ⟨4, .ctm, [rowB, rowB2]⟩

end Contracts.ProxyUpgradeCurrent
