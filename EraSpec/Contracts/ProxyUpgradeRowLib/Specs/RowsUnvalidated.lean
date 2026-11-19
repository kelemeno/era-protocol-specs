import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsCurrent

/-!
# Model: rows that `validateRows` never checked (`b17415d20`)

Source: `l1-contracts/contracts/upgrades/registry/` on era-contracts branch `draft/v0.35.0` at
commit **`b17415d20`**, the commit `Specs/RowsCurrent.lean` is pinned to. Paths below are
relative to that directory. First written at `e561b9cc2`, where the executors called
`ProxyUpgradeRowLib.applyTransition` directly; the entry points are re-read below.

**This file adds no new operation.** It reuses the `RowsCurrent` model unchanged
(`ApplyRows`, `ApplyTransition`, `ReinitFrames`, ...) and adds one predicate, `Genuine`, and
witness data. The results are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsUnvalidated` and are proved in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsUnvalidated`.

## Where unvalidated rows come from

Both domain executors apply a transition object their owner hands them
(`executors/CTMUpgradeExecutor.sol:64-70`, `executors/CoreUpgradeExecutor.sol:33-36`), through
`_applyProxyUpgradeTransition` (`executors/ProxyUpgradeExecutorBase.sol:51-104`). It checks that
the object is code (`:57`), reads `getManifest()` once (`:58`), checks the manifest's domain
(`:59-61`) and the engine's code (`:63`), and delegatecalls the engine;
`DefaultProxyUpgradeEngine` applies `toRows` of the manifest's inventory
(`engines/DefaultProxyUpgradeEngine.sol:41-44`). After the engine the executor checks the
inventory length (`ProxyUpgradeExecutorBase.sol:99-102`) and `requireRowsApplied` (`:103`).
Nothing on this path calls `validateRows` or checks that the object is a
`ProxyUpgradeTransition`.

Only a genuine `ProxyUpgradeTransition` validated its rows. Its constructor flattens the
manifest's inventory with `toRows`, refuses an empty result and runs `validateRows`
(`objects/ProxyUpgradeTransition.sol:27-42`, the refusal at `:34-36`, the check at `:37`), and
`getManifest()` returns the manifest it pinned (`:44-47`), which only the constructor writes
(`objects/ManifestStorage.sol:13-15`; the object has no state-mutating function,
`ProxyUpgradeTransition.sol:14-17`). Any other contract that answers `getManifest()` with a
manifest pinning `DefaultProxyUpgradeEngine` gets its rows applied as they are: rows on the
same proxy, self-edges and zero `proxy` or `expectedOldImpl` fields included.

The object also pins its own engine: `manifest.proxyUpgradeEngine`, checked only for code
(`ProxyUpgradeExecutorBase.sol:63`) and delegatecalled (`:82`). `DefaultProxyUpgradeEngine`'s
hooks are empty at `b17415d20` (`engines/DefaultProxyUpgradeEngine.sol:51-65`), so its leg is
the object checks followed by `applyRows`, which `ApplyTransition` over-approximates (it omits
the engine-code check and the ownership check at `:34-37`). A leg with any other engine is
arbitrary code running with the executor's authority, bounded only by the executor's
post-checks; it is modelled in `../ProxyUpgradeExecutorBase/` (`DomainHoldersV35`,
`EngineLegV35`), not here. The parameter is documented as "The write-once transition
approved by governance" (`executors/ICTMUpgradeExecutor.sol:35`,
`executors/ICoreUpgradeExecutor.sol:17`), and the off-chain review before the vote checks the
object's code identity and its rows, duplicate proxies included
(`protocol-docs/ecosystem-upgrade.md:364`, repository root). Neither is enforced on chain.

## Modelling choices

* **The object is its manifest, read once.** `getManifest()` is `view`
  (`objects/IProxyUpgradeTransition.sol:17`), so Solidity calls it with `STATICCALL` and the
  object cannot change state while answering; the executor reads it once
  (`executors/ProxyUpgradeExecutorBase.sol:58`) and the engine receives the inventory as an
  argument. So `ProxyUpgradeCurrent.Transition`, an address, a domain and a row list with no
  condition on the rows, describes any object whose manifest pins `DefaultProxyUpgradeEngine`,
  genuine or not. (`toRows` drops the rows with a
  zero `implNew`, so the real row lists are a subset of the modelled ones; that only adds
  objects.)
* **`Genuine` is what a real `ProxyUpgradeTransition`'s rows satisfy**: nonempty and
  `ValidRows` (nonzero fields, no self-edge, one row per proxy). The inventory length check
  in `toRows` only rejects and leaves no trace in the rows, so it is not part of it.
* Everything else is as in `Specs/RowsCurrent.lean`. In particular a reinitializer's effect
  on the implementation mapping is the arbitrary function `Config.reinit`, and
  `ReinitFrames` (it moves at most its own proxy) is a premise where results need it.
-/

namespace Contracts.ProxyUpgradeCurrent

/-- **A GENUINE `ProxyUpgradeTransition`.** What the object's constructor established about
its participating rows (`objects/ProxyUpgradeTransition.sol:27-42`): there is at least one row
(`:34-36`) and the rows pass `validateRows` (`:37`). `ApplyTransition` does not require it: the
executor checks only the object's code and domain
(`executors/ProxyUpgradeExecutorBase.sol:57-61`). -/
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

/-- A CTM-domain object that answers `getManifest()` but is not a genuine
`ProxyUpgradeTransition`: its rows `rowB`, `rowB2` name proxy `6` twice. -/
def wDupTransition : Transition := ⟨4, .ctm, [rowB, rowB2]⟩

end Contracts.ProxyUpgradeCurrent
