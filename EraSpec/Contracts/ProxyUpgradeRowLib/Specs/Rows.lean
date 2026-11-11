import Mathlib.Tactic
import EraSpec.Core.Word

/-!
# Model: `ProxyUpgradeRowLib` — the registry-driven upgrade's proxy rows

The registry-driven upgrade system carries implementation swaps as *rows*, and
`ProxyUpgradeRowLib` is the one place their semantics live — shared by the core
registry, the CTM transition and the bootstrap migration, and by everything that
applies them.  The library's own summary:

    /// @notice THE `ProxyUpgradeRow` semantics, shared by everything that carries rows […]:
    ///         rows are SOURCE-CHECKED edges — a proxy already at `implNew` is skipped
    ///         (idempotence); a proxy at `expectedOldImpl` is upgraded; a proxy at anything else
    ///         reverts, so replaying a stale object can never downgrade a proxy that a later
    ///         upgrade has already moved on.

**This file is definitions only.**  The results are in
`EraSpec.Contracts.ProxyUpgradeRowLib.Properties.Rows` and proved in
`EraSpec.Contracts.ProxyUpgradeRowLib.Proofs.Rows`.

## Why this is worth modelling

Three claims are made for these rows and none of them is obvious from the loop:
idempotence, replay safety, and that a post-state check (`requireRowsApplied`)
follows from having applied them.  The third turns out to depend on the duplicate
check in `validateRows`, which is the kind of dependency that is easy to lose in a
refactor — see `Contracts.ProxyUpgrade.Properties.DuplicateRowsBreakPostcondition`.

## The four cases of one row

`applyRows` is a loop whose body has four outcomes, and the model has a constructor
for the three that succeed:

    if (address(_rows[i].admin) != address(0) && admin.owner() != address(this)) {
        emit ProxyRowLeftToAdministrator(...); continue;                    // foreign admin
    }
    address liveImpl = admin.getProxyImplementation(proxy);
    if (liveImpl == newImpl) { continue; }                                  // already there
    if (liveImpl != _rows[i].expectedOldImpl) { revert ProxyUpgradeRowMismatch(...); }
    …upgrade…                                                              // the edge

The fourth outcome is the revert, and it is modelled by the *absence* of a step: a
mismatch means no `ApplyRow` relates the states at all, so a run that reverts is a
run that does not exist.  One further revert is inherited rather than written — a
row under the applier's own bound admin that the applier does not own reverts
inside `ProxyAdmin.upgrade`, which is why `upgrade` below requires ownership while
the skip does not.

## What is not modelled

`callInitializeUpgrade` selects `upgradeAndCall` over `upgrade` with a fixed,
argument-less selector.  Both land the same implementation, and what the
reinitializer *does* is the audited implementation's business, so the flag is
carried on the row and does not affect any transition here.  The events are not
modelled; `LOG` cannot change state.

Both the loop and `requireRowsApplied` read the live implementation as
`adminOf(row).getProxyImplementation(proxy)`, which a transparent proxy answers only
to its actual admin.  The model reads one mapping instead, which builds in the
configuration assumption that a row names the admin that really administers its
proxy.  A row that gets this wrong reverts on the read, so the assumption costs no
safety here — it means these results say nothing about *that* misconfiguration.
-/

namespace Contracts.ProxyUpgrade

open Clear

/-- Addresses as 256-bit words; `0` is the zero address, as in Solidity. -/
abbrev Address := UInt256

/-- Point update of a proxy-keyed mapping. -/
def upd (f : Address → Address) (p : Address) (v : Address) : Address → Address :=
  fun x => if x = p then v else f x

/-- `ProxyUpgradeRow`: a source-checked edge, not just a target. -/
structure Row where
  /-- The proxy this row upgrades. -/
  proxy : Address
  /-- The implementation the proxy must currently point at for the row to apply — the
  replay guard. -/
  expectedOldImpl : Address
  /-- The implementation it points at afterwards.  Zero marks an inventory slot as
  explicitly not upgraded; such a slot never becomes a row. -/
  implNew : Address
  /-- Whether the swap reinitializes.  Carried, and deliberately inert here. -/
  callInitializeUpgrade : Bool
  /-- The `ProxyAdmin` administering `proxy`; zero means the applier's own bound admin. -/
  admin : Address
deriving DecidableEq

/-- The applying contract, its bound `ProxyAdmin`, and who owns each admin.

Ownership is configuration rather than state: `applyRows` never changes an admin's
owner, so hoisting it here is faithful and keeps the step relation about one
mapping. -/
structure Config where
  /-- `address(this)` of the applying contract. -/
  self : Address
  /-- The applier's bound `ProxyAdmin`. -/
  defaultAdmin : Address
  /-- `admin.owner()`. -/
  adminOwner : Address → Address

/-- The live implementation behind each proxy — the state rows act on. -/
abbrev Impl := Address → Address

/-- The admin a row is read and applied through. -/
def adminOf (C : Config) (r : Row) : Address :=
  if r.admin = 0 then C.defaultAdmin else r.admin

/-- The row names a *foreign* `ProxyAdmin` the applier does not own.  `applyRows`
logs such a row and moves on, leaving it to that administrator — while
`requireRowsApplied` still demands it. -/
def LeftToAdministrator (C : Config) (r : Row) : Prop :=
  r.admin ≠ 0 ∧ C.adminOwner (adminOf C r) ≠ C.self

/-- One row's three succeeding outcomes.  A mismatch has no constructor: the call
reverts, and a reverting run is one this relation does not contain. -/
inductive ApplyRow (C : Config) : Impl → Row → Impl → Prop
  /-- Foreign admin: logged and skipped, state unchanged. -/
  | leftToAdmin {I r} : LeftToAdministrator C r → ApplyRow C I r I
  /-- Already at the target: skipped.  This is the idempotence case. -/
  | alreadyAtTarget {I r} : ¬ LeftToAdministrator C r → I r.proxy = r.implNew →
      ApplyRow C I r I
  /-- The edge: the proxy is at `expectedOldImpl`, so it moves to `implNew`.  Ownership
  is required because `ProxyAdmin.upgrade` is `onlyOwner`. -/
  | upgrade {I r} : ¬ LeftToAdministrator C r → C.adminOwner (adminOf C r) = C.self →
      I r.proxy ≠ r.implNew → I r.proxy = r.expectedOldImpl →
      ApplyRow C I r (upd I r.proxy r.implNew)

/-- `applyRows`: the loop, in order. -/
inductive ApplyRows (C : Config) : Impl → List Row → Impl → Prop
  | nil {I} : ApplyRows C I [] I
  | cons {I J K r rs} : ApplyRow C I r J → ApplyRows C J rs K → ApplyRows C I (r :: rs) K

/-- `requireRowsApplied`: every row's proxy is at its `implNew`. -/
def RowsApplied (I : Impl) (rows : List Row) : Prop :=
  ∀ r ∈ rows, I r.proxy = r.implNew

/-- `validateRows`: every row is a real, unique edge.  The pairwise condition is the
nested loop that refuses a second row on the same proxy. -/
structure ValidRows (rows : List Row) : Prop where
  /-- No placeholder rows. -/
  fieldsNonzero : ∀ r ∈ rows, r.proxy ≠ 0 ∧ r.expectedOldImpl ≠ 0 ∧ r.implNew ≠ 0
  /-- One row per proxy. -/
  distinctProxies : rows.Pairwise (fun a b => a.proxy ≠ b.proxy)

/-- `_dropInertSlots`: an inventory slot participates exactly when `implNew` is set. -/
def dropInertSlots (slots : List Row) : List Row :=
  slots.filter (fun r => decide (r.implNew ≠ 0))

/-- `toRows`: the length check, then the drop.  Modelled as the drop plus the length
side condition the caller must supply, since the check only rejects. -/
def toRows (slots : List Row) : List Row := dropInertSlots slots

/-! ## Countermodel witnesses

Concrete data for the three results that say a check is load-bearing.  They live
here, with the model, so that `Properties` stays statements and `Proofs` stays
proofs. -/

/-- The applier owns every admin, so nothing is left to an administrator. -/
def cmConfig : Config where
  self := 1
  defaultAdmin := 7
  adminOwner := fun _ => 1

/-- Every proxy starts at implementation `10`. -/
def cmImpl : Impl := fun _ => 10

/-- Proxy `5`: `10 → 11`. -/
def rowAB : Row := ⟨5, 10, 11, false, 0⟩

/-- Proxy `5` again: `11 → 12`.  Two rows on one proxy — exactly what `validateRows`
refuses. -/
def rowBC : Row := ⟨5, 11, 12, false, 0⟩

/-- The state the pair reaches in the order `[rowAB, rowBC]`. -/
def cmFinal : Impl := upd (upd cmImpl 5 11) 5 12

/-- An applier that owns nothing. -/
def fgnConfig : Config where
  self := 1
  defaultAdmin := 7
  adminOwner := fun _ => 2

/-- A row under an explicitly named foreign admin: skipped by `applyRows`, still
demanded by `requireRowsApplied`. -/
def fgnRow : Row := ⟨5, 10, 11, false, 9⟩

end Contracts.ProxyUpgrade
