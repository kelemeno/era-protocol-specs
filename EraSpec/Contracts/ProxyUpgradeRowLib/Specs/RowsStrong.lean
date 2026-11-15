import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.Rows

/-!
# Model: when the `612a71ccc` rows apply

**This file adds no new operation.** It reuses the model of `Specs/Rows.lean` unchanged
(`ApplyRow`, `ApplyRows`, `RowsApplied`, ...) and adds one predicate, `RowEnabled`, and witness
data. The results are in `EraSpec.Contracts.ProxyUpgradeRowLib.Properties.RowsStrong` and are
proved in `EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsStrong`.

## Why

`Properties/Rows.lean` states what a *successful* `applyRows` establishes: the frame, the
post-state gate, determinism, idempotence. Two things are left open there.

* **When `applyRows` succeeds at all.** Every result there takes a successful run as a
  premise, and the file's only nonempty successful runs use duplicate rows or a foreign-admin
  row, which break the gate's own premises.
* **Whether a permutation of a successful run succeeds.** `OrderIndependent` compares two
  successful runs only.

`RowEnabled` is the condition under which one loop iteration does not revert. It is read off
the three succeeding constructors of `ApplyRow`, and it reads the mapping only at the row's
own proxy. That is what makes the loop's success order-free on distinct proxies.
-/

namespace Contracts.ProxyUpgrade

/-- **THE ROW HAS A STEP FROM `I`.** One of the three succeeding outcomes of the loop body is
available: the row is left to a foreign administrator (logged and skipped); or its proxy is
already at `implNew` (skipped); or the applier owns the row's admin and the proxy is at
`expectedOldImpl` (the upgrade). It reads the mapping only at `r.proxy`. -/
def RowEnabled (C : Config) (I : Impl) (r : Row) : Prop :=
  LeftToAdministrator C r ∨ I r.proxy = r.implNew ∨
    (C.adminOwner (adminOf C r) = C.self ∧ I r.proxy = r.expectedOldImpl)

/-! ## Witness data

As in `Specs/Rows.lean`: the applier `1` owns every admin (`cmConfig`), every proxy starts at
implementation `10` (`cmImpl`), and `rowAB` is proxy `5`: `10 → 11`. -/

/-- Proxy `6`: `10 → 12`, under the applier's own bound admin. With `rowAB`, two rows on
distinct proxies. -/
def rowP6 : Row := ⟨6, 10, 12, false, 0⟩

/-- The state `[rowAB, rowP6]` reaches from `cmImpl`, in either order: proxy `5` at `11`,
proxy `6` at `12`, every other proxy at `10`. -/
def pairFinal : Impl := upd (upd cmImpl 5 11) 6 12

end Contracts.ProxyUpgrade
