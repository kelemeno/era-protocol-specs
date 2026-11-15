import EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsStrong

/-!
# Properties: when the `612a71ccc` rows apply, and in which orders

Statements about `EraSpec.Contracts.ProxyUpgradeRowLib.Specs.RowsStrong`, which is the model of
`Specs/Rows.lean` plus `RowEnabled` and witness data. Proofs are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.RowsStrong`.

## Liveness: when `applyRows` succeeds

`ApplyRowsPostcondition` and `AppliedGatePasses` (`Properties/Rows.lean`) say what a
successful `applyRows` establishes, under distinct proxies and no foreign-admin row. They do
not say that such a run exists. This file does.

* `RowStepIffEnabled`: one loop iteration succeeds exactly when the row is `RowEnabled`.
* `ApplyRowsEnabledIff`: on rows naming distinct proxies, `applyRows` succeeds exactly when
  every row is enabled in the state the call starts from. Enabledness reads the mapping only
  at the row's own proxy, which no other row touches.
* `ApplyRowsPassesGateWhenEnabled`: under the gate's own premises (distinct proxies, no row
  left to a foreign administrator), if each row's proxy is at its target, or at its source
  under an admin the applier owns, then `applyRows` succeeds, the gate passes on the state it
  leaves, and proxies no row names stay where they were.

## Order independence, executability included

`OrderIndependent` (`Properties/Rows.lean`) assumes that both orders succeed. On distinct
proxies, with reinitializers inert as this model assumes, the second order's success follows
from the first's (`OrderIndependentExecutability`): a permutation of a successful run is a
successful run to the same state. With a duplicate row
it fails (`DuplicateRowsBreakOrder`), which is outside the distinct-proxies premise.

## Witness

`RowsStrongWitness`: two valid owned rows on distinct proxies, both at their source, apply in
both orders to one state that moves both proxies and passes the gate. A row left to a foreign
administrator is enabled, and a stale row is not.
-/

namespace Contracts.ProxyUpgrade

/-! ## One row -/

/-- **ONE ROW HAS A STEP EXACTLY WHEN IT IS ENABLED.** A loop iteration does not revert iff the
row is left to a foreign administrator, or its proxy is already at `implNew`, or the applier
owns the row's admin and the proxy is at `expectedOldImpl`. -/
def Properties.RowStepIffEnabled : Prop :=
  ∀ (C : Config) (I : Impl) (r : Row), (∃ J, ApplyRow C I r J) ↔ RowEnabled C I r

/-! ## A run -/

/-- **ON DISTINCT PROXIES, `applyRows` SUCCEEDS EXACTLY WHEN EVERY ROW IS ENABLED WHERE THE CALL
STARTS.** For rows naming distinct proxies (as `validateRows` ensures), the loop reverts iff
some row is not `RowEnabled` in the starting state. No row can be enabled or disabled by an
earlier one, because no earlier row touches its proxy. This holds with reinitializers inert, as
the `612a71ccc` model assumes (`Specs/Rows.lean`): the Solidity does call `upgradeAndCall` with
`initializeUpgrade` (`ProxyUpgradeRowLib.sol:137-139`), and a reinitializer that moved another
row's proxy could enable or disable it. `RowsCurrentStrong` treats reinitializers. -/
def Properties.ApplyRowsEnabledIff : Prop :=
  ∀ (C : Config) (I : Impl) (rows : List Row), rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    ((∃ J, ApplyRows C I rows J) ↔ ∀ r ∈ rows, RowEnabled C I r)

/-- **UNDER THE GATE'S PREMISES, ENABLED ROWS APPLY AND PASS THE GATE.** The liveness companion
of `ApplyRowsPostcondition` and `AppliedGatePasses`. Take rows naming distinct proxies, none
left to a foreign administrator, each with its proxy at `implNew` or, under an admin the
applier owns, at `expectedOldImpl`. Then `applyRows` succeeds; on the state it leaves,
`requireRowsApplied` passes, and every proxy no row names is where it was. -/
def Properties.ApplyRowsPassesGateWhenEnabled : Prop :=
  ∀ (C : Config) (I : Impl) (rows : List Row), rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    (∀ r ∈ rows, ¬ LeftToAdministrator C r) →
    (∀ r ∈ rows, I r.proxy = r.implNew ∨
      (C.adminOwner (adminOf C r) = C.self ∧ I r.proxy = r.expectedOldImpl)) →
    ∃ J, ApplyRows C I rows J ∧ RowsApplied J rows ∧ ∀ p, (∀ r ∈ rows, r.proxy ≠ p) → J p = I p

/-! ## Order independence -/

/-- **A PERMUTATION OF A SUCCESSFUL RUN IS A SUCCESSFUL RUN TO THE SAME STATE.** For rows naming
distinct proxies: if `applyRows` succeeds in one order, it succeeds in every order, and reaches
the same state. So under `validateRows`, with reinitializers inert, as the `612a71ccc` model
assumes (`Specs/Rows.lean`), neither the post-state nor whether the call reverts depends on the
enum order the rows arrive in. The Solidity does call `upgradeAndCall` with
`initializeUpgrade` (`ProxyUpgradeRowLib.sol:137-139`); a reinitializer that moves another
row's proxy can make the order decide a mismatch revert (`ReinitReadBreaksOrder` in
`Properties/RowsOrder.lean`, at `e561b9cc2`). `RowsCurrentStrong` treats reinitializers. This
implies `OrderIndependent`, whose premise that both orders succeed it discharges. -/
def Properties.OrderIndependentExecutability : Prop :=
  ∀ (C : Config) (I J : Impl) (rows rows' : List Row), rows.Perm rows' →
    rows.Pairwise (fun a b => a.proxy ≠ b.proxy) →
    ApplyRows C I rows J → ApplyRows C I rows' J

/-! ## Witness -/

/-- **THE PREMISES ARE MET BY A REAL UPGRADE.** Rows `5: 10 → 11` and `6: 10 → 12` are valid.
The applier owns their admin, neither is left to a foreign administrator, and both proxies
start at their source and not at their target. So the premises of `ApplyRowsPostcondition`,
`AppliedGatePasses` (with nothing moved in between), `OrderIndependent`,
`ApplyRowsPassesGateWhenEnabled` and `OrderIndependentExecutability` hold with a nonempty run.
`applyRows` succeeds in both orders and reaches one state, which differs from the start and
passes the gate. A row left to a foreign administrator is enabled. The stale row
`5: 11 → 12` is not enabled in the start state, and with `rowP6` on a distinct proxy the call
reverts. -/
def Properties.RowsStrongWitness : Prop :=
  ValidRows [rowAB, rowP6] ∧
    (∀ r ∈ [rowAB, rowP6], ¬ LeftToAdministrator cmConfig r ∧
      cmConfig.adminOwner (adminOf cmConfig r) = cmConfig.self ∧
      cmImpl r.proxy = r.expectedOldImpl ∧ cmImpl r.proxy ≠ r.implNew) ∧
    ApplyRows cmConfig cmImpl [rowAB, rowP6] pairFinal ∧
    ApplyRows cmConfig cmImpl [rowP6, rowAB] pairFinal ∧
    pairFinal ≠ cmImpl ∧ RowsApplied pairFinal [rowAB, rowP6] ∧
    RowEnabled fgnConfig cmImpl fgnRow ∧
    ¬ RowEnabled cmConfig cmImpl rowBC ∧
    [rowP6, rowBC].Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    ¬ ∃ J, ApplyRows cmConfig cmImpl [rowP6, rowBC] J

end Contracts.ProxyUpgrade
