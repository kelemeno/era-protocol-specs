import EraSpec.Contracts.RegistryBootstrapMigration.Specs.Authority

/-!
# Properties: the bootstrap does not park authority on itself

Statements about `EraSpec.Contracts.RegistryBootstrapMigration.Specs.Authority`. Proofs are
in `EraSpec.Contracts.RegistryBootstrapMigration.Proofs.Authority`.

## What holds

* **`migrate()` with a genuine CTM executor parks nothing.** After it, the CTM and the
  CTM-domain `ProxyAdmin` are the executor's, no CTM nomination is outstanding, and
  `validateApplied()` passes (`MigrateLeavesNothingParked`; `MigrateWitness` fires it from
  the governance hand-over, exercising the claim at :271-273).
* **The bundle parks nothing, whatever the executor's code.** Its last call,
  `validateApplied()`, excludes every parked state (`ValidateAppliedExcludesParking`), so a
  bundle that commits leaves the executor holding both authorities (`BundleNeverParks`;
  `BundleWitness`).
* **The edge is one-shot, and once spent the migration never acts again**
  (`MigrateIsOneShot`). From the state a genuine `migrate` leaves, nothing is parked along
  any run that does not hand authority back to the migration (`NoReparkingAfterMigrate`).

## What needs more than the on-chain checks

* **`migrate()` alone relies on the executor's code.** `validate()` checks the executor's
  getters, not its code. An executor that answers them correctly but whose
  `acceptCTMOwnership()` does nothing makes `migrate()` succeed and leave the CTM owned by
  the spent migration with the executor nominated (`NonGenuineExecutorParksTheCTM`). The
  bundle then reverts at `validateApplied()`. While the spent migration owns the CTM,
  only the nominee's own `acceptOwnership()` changes the owner
  (`ParkedCTMLeavesOnlyByNomineeAccept`).
* **The bundle's atomicity is what keeps a failed edge from parking the `ProxyAdmin`.**
  Sent as separate transactions, the hand-over calls succeed against a CTM whose version
  drifted from the manifest's, after which `migrate()` reverts and the `ProxyAdmin`
  (plain `Ownable`) belongs to the migration (`SplitBundleParksProxyAdmin`). From such a
  state only a successful `migrate()` moves it (`ProxyAdminLeavesMigrationOnlyByMigrate`).
  `ParkedFramesFire` exercises both frames on the countermodels' states.
-/

namespace Contracts.RegistryBootstrapMigration

/-! ## `migrate()` itself -/

/-- **`migrate()` WITH A GENUINE EXECUTOR PARKS NOTHING.** If the CTM executor's
`acceptCTMOwnership()` runs `CTMUpgradeExecutor`'s logic, then after any successful
`migrate()` the CTM's owner and the `ProxyAdmin`'s owner are the CTM executor, no CTM
nomination is outstanding, no authority rests with the migration, and `validateApplied()`
passes. -/
def Properties.MigrateLeavesNothingParked : Prop :=
  ∀ (K : Config) (s s' : AState), (∀ e, K.exec K.m.E = some e → e.genuineAccept = true) →
    MigrateStep K s s' →
    s'.ctmOwner = K.m.E ∧ s'.ctmPending = 0 ∧ s'.paOwner = K.m.E ∧
      ¬ ParkedOnMigration K s' ∧ ValidateAppliedPasses K s'

/-- **THE EDGE IS ONE-SHOT.** After a successful `migrate()`, `executed` is set and no
further `migrate()` succeeds. -/
def Properties.MigrateIsOneShot : Prop :=
  ∀ (K : Config) (s s' : AState), MigrateStep K s s' →
    s'.executed = true ∧ ¬ ∃ s'', MigrateStep K s' s''

/-- **NOTHING RE-PARKS WITHOUT AN EXPLICIT HAND-BACK.** From a state where nothing is
parked on the migration and the edge is spent, along any run in which no transaction
nominates the migration on the CTM or transfers it the `ProxyAdmin`, nothing is parked on
the migration. -/
def Properties.NoReparkingAfterMigrate : Prop :=
  ∀ (K : Config) (s s' : AState) (ls : List Label), s.executed = true →
    ¬ ParkedOnMigration K s → ARun K s ls s' → (∀ l ∈ ls, ¬ l.handsToMigration K) →
    ¬ ParkedOnMigration K s'

/-! ## The bundle -/

/-- **`validateApplied()` EXCLUDES EVERY PARKED STATE.** If it passes, the migration holds
no authority and no CTM nomination is outstanding. -/
def Properties.ValidateAppliedExcludesParking : Prop :=
  ∀ (K : Config) (s : AState), ValidateAppliedPasses K s →
    ¬ ParkedOnMigration K s ∧ s.ctmPending = 0

/-- **A COMMITTED BUNDLE PARKS NOTHING, WHATEVER THE EXECUTOR'S CODE.** After the bundle's
nominate, hand-over, `migrate()` and `validateApplied()` run in one transaction, the CTM
and the `ProxyAdmin` are the CTM executor's, no nomination is outstanding, and no
authority rests with the migration. No premise on the executor. -/
def Properties.BundleNeverParks : Prop :=
  ∀ (K : Config) (s s' : AState), AStep K s .bundle s' →
    s'.ctmOwner = K.m.E ∧ s'.ctmPending = 0 ∧ s'.paOwner = K.m.E ∧ ¬ ParkedOnMigration K s'

/-! ## Countermodels and frames -/

/-- **A NON-GENUINE EXECUTOR LETS `migrate()` PARK THE CTM.** In the witness configuration
with an executor that answers every getter `validate()` reads correctly but whose
`acceptCTMOwnership()` does nothing, `migrate()` succeeds after governance's hand-over and
leaves the CTM owned by the migration with the executor nominated; `validateApplied()`
fails on that state, and the whole bundle has no successful execution. -/
def Properties.NonGenuineExecutorParksTheCTM : Prop :=
  ∃ s', MigrateStep (wConfig false) { wPre with ctmPending := 50, paOwner := 50 } s' ∧
    s'.ctmOwner = 50 ∧ s'.ctmPending = 3 ∧ s'.paOwner = 3 ∧
    ParkedOnMigration (wConfig false) s' ∧ ¬ ValidateAppliedPasses (wConfig false) s' ∧
    ¬ ∃ s'', AStep (wConfig false) wPre .bundle s''

/-- **WHILE THE SPENT MIGRATION OWNS THE CTM, ONLY THE NOMINEE'S ACCEPT MOVES IT.** From a
state where the migration owns the CTM and the edge is spent, every transaction leaves
the owner and the nominee unchanged, except an `acceptOwnership()` by the nominee, which
makes the nominee the owner. -/
def Properties.ParkedCTMLeavesOnlyByNomineeAccept : Prop :=
  ∀ (K : Config) (s s' : AState) (l : Label), s.ctmOwner = K.M → s.executed = true →
    AStep K s l s' →
    (s'.ctmOwner = K.M ∧ s'.ctmPending = s.ctmPending) ∨
      (l = .accept ∧ s'.ctmOwner = s.ctmPending ∧ s.ctmPending ≠ K.M)

/-- **THE `ProxyAdmin` LEAVES THE MIGRATION ONLY THROUGH `migrate()`.** From a state where
the migration owns the CTM-domain `ProxyAdmin`, every transaction other than a successful
`migrate()` leaves it there. -/
def Properties.ProxyAdminLeavesMigrationOnlyByMigrate : Prop :=
  ∀ (K : Config) (s s' : AState) (l : Label), s.paOwner = K.M → AStep K s l s' →
    s'.paOwner = K.M ∨ l = .migrate

/-- **SENT AS SEPARATE TRANSACTIONS, THE BUNDLE PARKS THE `ProxyAdmin`.** With a genuine
executor, but a CTM whose version drifted from the manifest's departing version, the
bundle's nominate and `ProxyAdmin` hand-over succeed as separate transactions; the
`ProxyAdmin` then belongs to the migration and `migrate()` has no successful execution.
Run atomically, the same bundle has none either, so nothing changes. -/
def Properties.SplitBundleParksProxyAdmin : Prop :=
  ∃ s, ARun (wConfig true) wPreDrift [.nominate 50, .transferPA 50] s ∧
    s.paOwner = 50 ∧ ParkedOnMigration (wConfig true) s ∧
    (¬ ∃ s', MigrateStep (wConfig true) s s') ∧
    ¬ ∃ s', AStep (wConfig true) wPreDrift .bundle s'

/-! ## Witnesses -/

/-- **`MigrateLeavesNothingParked` IS NOT VACUOUS.** In the witness configuration with a
genuine executor, after governance nominates the migration and hands it the
`ProxyAdmin`, `migrate()` succeeds; before it the migration was only the CTM's nominee
(so the claim at :271-273 runs), and after it the executor owns both authorities at the
new version `35` on release `60`. -/
def Properties.MigrateWitness : Prop :=
  ∃ s s', ARun (wConfig true) wPre [.nominate 50, .transferPA 50] s ∧
    s.ctmOwner = 9 ∧ s.ctmPending = 50 ∧ MigrateStep (wConfig true) s s' ∧
    s'.ctmOwner = 3 ∧ s'.ctmPending = 0 ∧ s'.paOwner = 3 ∧ s'.ctmPv = 35 ∧ s'.ctmRel = 60

/-- **`BundleNeverParks` IS NOT VACUOUS.** With a genuine executor the bundle commits from
the pre-bundle state. -/
def Properties.BundleWitness : Prop :=
  ∃ s', AStep (wConfig true) wPre .bundle s' ∧ s'.ctmOwner = 3 ∧ s'.paOwner = 3

/-- **THE TWO FRAMES ARE NOT VACUOUS.** In the state the non-genuine `migrate()` leaves, the
migration owns the CTM and the edge is spent, and the nominee's `acceptOwnership()` succeeds
and makes it the owner. In the state the split bundle leaves, the migration owns the
`ProxyAdmin`, and a transfer of it back to governance has no successful execution. -/
def Properties.ParkedFramesFire : Prop :=
  (∃ s' s'', MigrateStep (wConfig false) { wPre with ctmPending := 50, paOwner := 50 } s' ∧
    s'.ctmOwner = 50 ∧ s'.executed = true ∧ AStep (wConfig false) s' .accept s'' ∧
    s''.ctmOwner = 3) ∧
  ∃ s, ARun (wConfig true) wPreDrift [.nominate 50, .transferPA 50] s ∧ s.paOwner = 50 ∧
    ¬ ∃ s', AStep (wConfig true) s (.transferPA 9) s'

end Contracts.RegistryBootstrapMigration
