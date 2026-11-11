import EraSpec.Contracts.ChainTypeManager.Specs.ChainMigration

/-!
# Properties: a returning chain keeps its diamond, drift included

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ChainMigration`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.ChainMigration`.

* **Migration writes no diamond.** Leaving, returning and a failed-transfer recovery
  change nothing in the routing system (`MigrationLeavesRoutingAlone`); a return requires
  the chain to be registered and at the CTM's version and reuses its diamond. The only
  steps that change a registered chain's version or routing are a transition, the
  bootstrap reset and a break-glass cut of that chain (`OnlyUpgradesAndCutsWriteADiamond`).
* **The headline survives migration.** Without break-glass cuts, every chain at a version
  `v` with a release `R_v` routes exactly `R_v` along runs that migrate chains out and
  back (`ChainsRunTheirVersionsReleaseAcrossMigration`; `MigrationRoundTripWitness`).
* **Drift is kept.** A chain whose routing a break-glass cut changed leaves and returns
  with that routing, while the same chain arriving where it has no diamond would get the
  CTM's release (`DriftSurvivesMigrationRoundTrip`). Once the CTM moves on, the returned
  chain can neither upgrade nor leave again (`DriftedReturnerIsStuck`).
-/

namespace Contracts.ChainTypeManager

/-- **MIGRATION LEAVES THE ROUTING SYSTEM ALONE.** Leaving, returning and a failed-transfer
recovery change neither the CTM nor any chain's version or routing; a return also requires
the chain to be registered here and at the CTM's version. -/
def Properties.MigrationLeavesRoutingAlone : Prop :=
  ∀ (W : World) (s s' : MSys) (l : MLabel), MStep W s l s' → (∀ l', l ≠ .base l') →
    s'.sys = s.sys ∧
      ∀ id, l = .migrateReturn id → ∃ c, s.sys.chains id = some c ∧ c.pv = s.sys.ctm.pv

/-- **ONLY AN UPGRADE OR A CUT WRITES A REGISTERED DIAMOND.** If a step changes the version
or the routing of a chain that was registered before it, the step is a transition, the
bootstrap reset, or a break-glass cut of that chain. -/
def Properties.OnlyUpgradesAndCutsWriteADiamond : Prop :=
  ∀ (W : World) (s s' : MSys) (l : MLabel) (id : ChainId) (c c' : Chain),
    MStep W s l s' → s.sys.chains id = some c → s'.sys.chains id = some c' → c' ≠ c →
    l.writesDiamond id

/-- **THE HEADLINE ACROSS MIGRATION.** Along any run from an invariant routing system that
uses no break-glass cut, with chains leaving and returning, every chain at a version `v`
for which the CTM has a release `R_v` routes exactly `R_v`, and `R_v` is a release of
version `v`. -/
def Properties.ChainsRunTheirVersionsReleaseAcrossMigration : Prop :=
  ∀ (W : World) (s s' : MSys) (ls : List MLabel), SysInv W s.sys → MRun W s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (W.relRows (s'.sys.ctm.relAt c.pv))

/-- **DRIFT SURVIVES A ROUND TRIP.** On the witness world: chain `0` is created at version 1
on release `100`, a break-glass cut adds selector `9` (`bgExtra`), and the chain leaves and
returns. It is back, not away, at version 1 — whose release is `100` — still routing
`bgExtra`, which is not release `100`'s routing. The same chain arriving on the fresh
system, where it has no diamond, gets exactly release `100`'s routing. -/
def Properties.DriftSurvivesMigrationRoundTrip : Prop :=
  (∃ s, MRun wWorld wMSys0
      [.base (.genesis 0), .base (.arbitraryCut 0 1 bgExtra), .migrateOut 0, .migrateReturn 0] s ∧
    s.away 0 = false ∧ s.sys.ctm.relAt 1 = 100 ∧
    ∃ c, s.sys.chains 0 = some c ∧ c.pv = 1 ∧ c.routing = bgExtra ∧
      c.routing ≠ rowsRouting (wRows 100)) ∧
  ∃ s, MRun wWorld wMSys0 [.base (.migrateIn 0)] s ∧
    ∃ c, s.sys.chains 0 = some c ∧ c.pv = 1 ∧ c.routing = rowsRouting (wRows 100)

/-- **A DRIFTED RETURNER IS STUCK ONCE THE CTM MOVES ON.** After the round trip above, the
CTM commits `300` (1→2). Chain `0`, still at version 1 with the drifted routing, has no
transition (the guard refuses its routing) and cannot leave again (it is not at the CTM's
version). -/
def Properties.DriftedReturnerIsStuck : Prop :=
  ∃ s, MRun wWorld wMSys0
      [.base (.genesis 0), .base (.arbitraryCut 0 1 bgExtra), .migrateOut 0, .migrateReturn 0,
        .base (.ctm (.commit 300))] s ∧
    s.sys.ctm.pv = 2 ∧ (∃ c, s.sys.chains 0 = some c ∧ c.pv = 1) ∧
    (¬ ∃ s', MStep wWorld s (.base (.transition 0)) s') ∧
    ¬ ∃ s', MStep wWorld s (.migrateOut 0) s'

/-- **THE HEADLINE ACROSS MIGRATION IS NOT VACUOUS.** From the fresh witness system: create
chain `0`, let it leave and return, commit `300`, and upgrade it. The run has no
break-glass cut and starts from an invariant state; chain `0` ends at version 2 routing
release `200`. -/
def Properties.MigrationRoundTripWitness : Prop :=
  ∃ s, MRun wWorld wMSys0
      [.base (.genesis 0), .migrateOut 0, .migrateReturn 0, .base (.ctm (.commit 300)),
        .base (.transition 0)] s ∧
    SysInv wWorld wMSys0.sys ∧
    ∃ c, s.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)

end Contracts.ChainTypeManager
