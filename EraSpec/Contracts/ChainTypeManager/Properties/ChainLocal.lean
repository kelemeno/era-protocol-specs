import EraSpec.Contracts.ChainTypeManager.Specs.ChainLocal

/-!
# Properties: one chain at a time, and the break-glass repair

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ChainLocal`, over the systems of
`ChainRouting` and `ChainMigration`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocal`.

## The per-chain headline

`ChainsRunTheirVersionsRelease` forbids every break-glass cut in the run, on any chain. Two
facts make the headline local to a chain:

* A step that does not write chain `id` keeps it consistent with its CTM: CTM writers never
  lower the version or rewrite the release of a version already reached, and a step of
  another chain, a break-glass cut included, leaves `id`'s diamond alone
  (`StepsElsewhereKeepChainOk`).
* A write of `id` that is not a break-glass cut lands it at a version with a release, routing
  exactly that release, **whatever it routed before**, drift included
  (`NonCutWriteLandsOnRelease`).

Hence, if the last step writing chain `id` is not a break-glass cut, chain `id` runs its
version's release (`ChainRunsItsVersionsRelease`), also along runs in which chains leave and
return (`ChainRunsItsVersionsReleaseAcrossMigration`, through `MigrationRunIsARoutingRun`). A
chain created during such a run is moreover at a version that has a release
(`NewChainRunsItsVersionsRelease`).

The global premise implies the per-chain one for every chain (`GlobalPremiseImpliesChainLocal`),
so the per-chain headline contains the global one. It is strictly more general, and its own
premise is load-bearing (`ChainLocalWitness`): in a run with break-glass cuts of two chains,
the chain whose last write is a transition runs its release, and the chain whose last write is
a cut does not. The same holds across executor runs, where break-glass cuts are forwarded
calls (`ChainLocalExecutor`).

## The repair

* The repair cut (break-glass to version `v` with exactly `R_v`'s routing, `repairCut`) exists
  for every registered chain and every version with a release, and leaves the chain consistent
  at `v` on `R_v`, whatever it routed before (`RepairCutRestoresChainOk`). It is the only
  break-glass cut right after which a chain is on its version's release
  (`OnlyRepairCutsLandOnARelease`).
* Along a run, if the last write of chain `id` is not a break-glass cut, or is a repair cut,
  chain `id` ends on its version's release (`LastWriteDecidesTheRouting`).
* After a repair at a version with a committed transition, the chain can cross it, provided
  the edge's two releases each list every selector once (`RepairEnablesTransition`). This is
  enabledness in the model: timestamps, executed batches, the settlement-layer order and the
  other reject-only checks are not modelled, so only a revert caused by the routing is ruled
  out.
  `CTMRelease.validate()` checks that (`upgrades/registry/objects/CTMRelease.sol:128`,
  `:190-213`) when a release is installed (`state-transition/ChainTypeManager.sol:310`); the
  model omits `validate()`, so it is a stated premise. It cannot be dropped: a release that
  lists a selector twice blocks every changing edge at it, repaired chains included
  (`RepeatedSelectorBlocksTheEdge`, `RepairNeedsUniqueSelectors`).
* The chain of `DriftedReturnerIsStuck` is un-stuck by the repair: it then upgrades to
  version 2 on release `200` and can leave again (`RepairUnsticksDriftedReturner`).

## What this does not say

The per-chain premise is sufficient, not necessary. A break-glass cut may put a chain ahead of
its CTM (it can set any version). Once the CTM reaches that version, the chain is consistent
if its routing is the release installed there, although its last write was a cut
(`ChainLocalPremiseNotNecessary`). The results above are about the two last-write forms only.
-/

namespace Contracts.ChainTypeManager

/-! ## One step -/

/-- **A STEP THAT DOES NOT WRITE A CHAIN KEEPS IT CONSISTENT.** If chain `id` is consistent with
its CTM (not ahead of it, and on `R_v` if its version `v` has a release), then after any step
that does not write `id`'s diamond — a CTM writer, or a step of another chain, including a
break-glass cut of another chain — chain `id` is still consistent. No invariant is needed: CTM
writers never lower the version and never rewrite the release of a version already reached
(`cstep_pv`, `cstep_relAt_low`). -/
def Properties.StepsElsewhereKeepChainOk : Prop :=
  ∀ (W : World) (s s' : Sys) (l : Label) (id : ChainId),
    (∀ c, s.chains id = some c → ChainOk W s c) → Step W s l s' → ¬ l.writesChain id →
    ∀ c, s'.chains id = some c → ChainOk W s' c

/-- **A WRITE THAT IS NOT A BREAK-GLASS CUT LANDS THE CHAIN ON A RELEASE.** On a CTM satisfying
its invariant, after any step that writes chain `id`'s diamond and is not a break-glass cut
(creation, deployment on arrival, a transition, the bootstrap reset), chain `id` is registered
at a version `v ≤ pv` for which the CTM has a release `R_v`, and routes exactly `R_v`, whatever
it routed before, drift included. -/
def Properties.NonCutWriteLandsOnRelease : Prop :=
  ∀ (W : World) (s s' : Sys) (l : Label) (id : ChainId), CtmInv W s.ctm → Step W s l s' →
    l.writesChain id → ¬ l.isArbitrary →
    ∃ c, s'.chains id = some c ∧ c.pv ≤ s'.ctm.pv ∧ s'.ctm.relAt c.pv ≠ 0 ∧
      c.routing = rowsRouting (W.relRows (s'.ctm.relAt c.pv))

/-! ## The per-chain headline -/

/-- **PER-CHAIN HEADLINE: A CHAIN WHOSE LAST WRITE WAS NOT A BREAK-GLASS CUT RUNS ITS VERSION'S
RELEASE.** Take any run from a state where the CTM invariant holds and chain `id` is consistent
with its CTM (`SysInv` gives both). Suppose the last step of the run that writes `id`'s diamond
is not a break-glass cut (`LastWriteNotBreakGlass`; it holds if no step writes it). Then at the
end chain `id`, if registered, is not ahead of its CTM. If the CTM has a release `R_v` for the
chain's version `v`, the chain routes exactly `R_v`'s selectors, each to `R_v`'s facet with
`R_v`'s freezability, and nothing else, and `R_v` is a release of version `v`.

Break-glass cuts of other chains may occur anywhere in the run. Break-glass cuts of `id`
itself may occur before its last write. -/
def Properties.ChainRunsItsVersionsRelease : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label) (id : ChainId), CtmInv W s.ctm →
    (∀ c, s.chains id = some c → ChainOk W s c) → Run W s ls s' → LastWriteNotBreakGlass id ls →
    ∀ c, s'.chains id = some c → c.pv ≤ s'.ctm.pv ∧
      (s'.ctm.relAt c.pv ≠ 0 → W.relVersion (s'.ctm.relAt c.pv) = c.pv ∧
        c.routing = rowsRouting (W.relRows (s'.ctm.relAt c.pv)))

/-- **THE GLOBAL PREMISE IMPLIES THE PER-CHAIN ONE.** A run with no break-glass cut at all (the
premise of `ChainsRunTheirVersionsRelease`) satisfies `LastWriteNotBreakGlass id` for every
chain `id`. So the per-chain headline contains the global one. -/
def Properties.GlobalPremiseImpliesChainLocal : Prop :=
  ∀ (ls : List Label), (∀ l ∈ ls, ¬ l.isArbitrary) → ∀ id, LastWriteNotBreakGlass id ls

/-- **A CHAIN CREATED DURING THE RUN IS ON A RELEASE.** The per-chain form of
`FreshChainsRunTheirVersionsRelease`. Take any run from a state where the CTM invariant holds and
chain `id` is not registered (on a freshly initialized CTM no chain is). If the last write of
`id` is not a break-glass cut, then chain `id`, if registered at the end, is at a version
`v ≤ pv` for which the CTM **has** a release `R_v`, routes exactly `R_v`, and `R_v` is a release
of version `v`. -/
def Properties.NewChainRunsItsVersionsRelease : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label) (id : ChainId), CtmInv W s.ctm →
    s.chains id = none → Run W s ls s' → LastWriteNotBreakGlass id ls →
    ∀ c, s'.chains id = some c → c.pv ≤ s'.ctm.pv ∧ s'.ctm.relAt c.pv ≠ 0 ∧
      W.relVersion (s'.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (W.relRows (s'.ctm.relAt c.pv))

/-! ## Across migration -/

/-- **A MIGRATION-MODEL RUN IS A ROUTING RUN OF ITS ROUTING STEPS.** Dropping leaving, returning
and failed-transfer recoveries from a run of the migration model leaves a `ChainRouting` run
between the same routing systems. So every routing-run result applies across migration. -/
def Properties.MigrationRunIsARoutingRun : Prop :=
  ∀ (W : World) (s s' : MSys) (ls : List MLabel), MRun W s ls s' →
    Run W s.sys (ls.filterMap MLabel.base?) s'.sys

/-- **THE PER-CHAIN HEADLINE ACROSS MIGRATION.** As `ChainRunsItsVersionsRelease`, along runs in
which chains also leave and return. The premise concerns the run's routing steps. -/
def Properties.ChainRunsItsVersionsReleaseAcrossMigration : Prop :=
  ∀ (W : World) (s s' : MSys) (ls : List MLabel) (id : ChainId), CtmInv W s.sys.ctm →
    (∀ c, s.sys.chains id = some c → ChainOk W s.sys c) → MRun W s ls s' →
    LastWriteNotBreakGlass id (ls.filterMap MLabel.base?) →
    ∀ c, s'.sys.chains id = some c → c.pv ≤ s'.sys.ctm.pv ∧
      (s'.sys.ctm.relAt c.pv ≠ 0 → W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
        c.routing = rowsRouting (W.relRows (s'.sys.ctm.relAt c.pv)))

/-! ## The repair -/

/-- **THE REPAIR CUT RESTORES A CHAIN.** Take a CTM satisfying its invariant, a registered chain
`id` (whatever it routes, at whatever version), and a version `v` at which the CTM installed a
release `R_v`. The repair cut of `id` to `v` has a step. Every such step leaves the CTM and all
other chains as they were, and leaves chain `id` at version `v`, consistent with its CTM
(`v ≤ pv` follows from the invariant), routing exactly `R_v`. -/
def Properties.RepairCutRestoresChainOk : Prop :=
  ∀ (W : World) (s : Sys) (id : ChainId) (v : ℕ), CtmInv W s.ctm → (∃ c, s.chains id = some c) →
    s.ctm.relAt v ≠ 0 →
    (∃ s', Step W s (repairCut W s id v) s') ∧
    ∀ s', Step W s (repairCut W s id v) s' →
      s'.ctm = s.ctm ∧ (∀ id', id' ≠ id → s'.chains id' = s.chains id') ∧
      ∃ c, s'.chains id = some c ∧ c.pv = v ∧ ChainOk W s' c ∧
        c.routing = rowsRouting (W.relRows (s'.ctm.relAt v))

/-- **ONLY THE REPAIR CUT LANDS A CHAIN ON A RELEASE.** If, right after a break-glass cut of
chain `id` to version `v`, the chain is at a version with a release and routes exactly that
release, then the CTM had a release at `v`, and the cut is the repair cut to `v` in the state
it was applied in. -/
def Properties.OnlyRepairCutsLandOnARelease : Prop :=
  ∀ (W : World) (s s' : Sys) (id : ChainId) (v : ℕ) (ρ : Routing),
    Step W s (.arbitraryCut id v ρ) s' →
    (∃ c, s'.chains id = some c ∧ s'.ctm.relAt c.pv ≠ 0 ∧
      c.routing = rowsRouting (W.relRows (s'.ctm.relAt c.pv))) →
    s.ctm.relAt v ≠ 0 ∧ Label.arbitraryCut id v ρ = repairCut W s id v

/-- **THE LAST WRITE DECIDES.** Take any run from a state satisfying the CTM invariant (chain
`id` may route anything at the start), split at a step `l` that writes chain `id`'s diamond
and after which no step does. Suppose `l` is not a break-glass cut, or is the repair cut to a
version with a release in the state `s₁` it is applied in. Then chain `id` ends at a version
`v ≤ pv` for which the CTM has a release `R_v`, routing exactly `R_v`, and `R_v` is a release
of version `v`. -/
def Properties.LastWriteDecidesTheRouting : Prop :=
  ∀ (W : World) (s s₁ s₂ s' : Sys) (pre post : List Label) (l : Label) (id : ChainId),
    CtmInv W s.ctm → Run W s pre s₁ → Step W s₁ l s₂ → Run W s₂ post s' →
    l.writesChain id → (∀ l' ∈ post, ¬ l'.writesChain id) →
    (¬ l.isArbitrary ∨ ∃ v, s₁.ctm.relAt v ≠ 0 ∧ l = repairCut W s₁ id v) →
    ∃ c, s'.chains id = some c ∧ c.pv ≤ s'.ctm.pv ∧ s'.ctm.relAt c.pv ≠ 0 ∧
      W.relVersion (s'.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (W.relRows (s'.ctm.relAt c.pv))

/-- **A REPAIRED CHAIN CAN CROSS THE COMMITTED EDGE.** On a CTM satisfying its invariant, after
the repair cut of chain `id` to a version `v` with a release `R_v` and a committed transition
`upgradeTransition[v]`, a transition step exists for chain `id`. This needs the edge's two
releases (`R_v` and the transition's `newRelease()`) each to list every selector once, which
is what `CTMRelease.validate()` checks and the model omits. The transition takes the chain to
the edge's target version `w > v`, routing exactly `R_w`.

This is enabledness **in the model**, which omits the checks that only reject. In the source
the crossing also needs, among others, the manifest's `upgradeTimestamp` to have passed
(`upgrades/BaseZkSyncUpgrade.sol:76-78`), every committed batch executed
(`upgrades/DefaultUpgrade.sol:31`, `BaseZkSyncUpgrade.sol:109-113`), the settlement layer to be
at the new version already (`BaseZkSyncUpgrade.sol:83-88`), and, on a minor bump, the previous
L2 upgrade transaction finalized (`BaseZkSyncUpgrade.sol:245-254`). What the result rules out
is a revert caused by the routing. -/
def Properties.RepairEnablesTransition : Prop :=
  ∀ (W : World) (s s' : Sys) (id : ChainId) (v : ℕ), CtmInv W s.ctm → s.ctm.relAt v ≠ 0 →
    Step W s (repairCut W s id v) s' → s.ctm.ut v ≠ 0 →
    ((W.relRows (s.ctm.relAt v)).map Prod.fst).Nodup →
    ((W.relRows (s.edge W v).newRel).map Prod.fst).Nodup →
    ∃ s'', Step W s' (.transition id) s'' ∧ ∃ c, s''.chains id = some c ∧ v < c.pv ∧
      c.pv = (s.edge W v).new ∧ s''.ctm.relAt c.pv ≠ 0 ∧
      c.routing = rowsRouting (W.relRows (s''.ctm.relAt c.pv))

/-- **A RELEASE THAT LISTS A SELECTOR TWICE BLOCKS EVERY CHANGING EDGE AT IT.** Suppose the edge
committed at a chain's version changes the routing (its two releases' rows differ) and one of
its two releases lists some selector twice. Then no transition exists for the chain, whatever
it routes, repaired or not. The derived cuts would remove (departing release) or add (arriving
release) that selector twice, and the second `Remove` (`Diamond.sol:209-211`) or `Add`
(`:158-160`) reverts. So neither unique-selector premise of `RepairEnablesTransition` can be
dropped for an edge that changes the routing. -/
def Properties.RepeatedSelectorBlocksTheEdge : Prop :=
  ∀ (W : World) (s : Sys) (id : ChainId) (c : Chain), s.chains id = some c →
    W.relRows (s.edge W c.pv).fromRel ≠ W.relRows (s.edge W c.pv).newRel →
    (¬ ((W.relRows (s.edge W c.pv).fromRel).map Prod.fst).Nodup ∨
      ¬ ((W.relRows (s.edge W c.pv).newRel).map Prod.fst).Nodup) →
    ¬ ∃ s', Step W s (.transition id) s'

/-! ## Witnesses -/

/-- **THE PER-CHAIN HEADLINE IS NOT VACUOUS, ITS PREMISE IS STRICTLY WEAKER THAN THE GLOBAL ONE,
AND IT IS LOAD-BEARING.** From the fresh witness system, which satisfies `SysInv` and has no
chains, the run `wLocalRun`: chains `0` and `1` are created at version 1, both are drifted by
break-glass cuts, chain `0` is repaired, the CTM commits `300` (1→2), and chain `0` crosses it.

* The run contains break-glass cuts, so the global headline does not apply to it.
* The last write of chain `0` is its transition, so the per-chain premise holds for `0`. Chain
  `0` ends at version 2, whose release is `200`, routing release `200`.
* The last write of chain `1` is a break-glass cut, so the premise fails for `1`, and so does
  the conclusion: chain `1` is at version 1, whose release is `100`, and does not route it. -/
def Properties.ChainLocalWitness : Prop :=
  ∃ s, Run wWorld wSys0 wLocalRun s ∧ SysInv wWorld wSys0 ∧ wSys0.chains 0 = none ∧
    (∃ l ∈ wLocalRun, l.isArbitrary) ∧
    LastWriteNotBreakGlass 0 wLocalRun ∧ ¬ LastWriteNotBreakGlass 1 wLocalRun ∧
    (∃ c, s.chains 0 = some c ∧ c.pv = 2 ∧ s.ctm.relAt 2 = 200 ∧
      c.routing = rowsRouting (wRows 200)) ∧
    (∃ c, s.chains 1 = some c ∧ c.pv = 1 ∧ s.ctm.relAt 1 = 100 ∧
      c.routing ≠ rowsRouting (wRows 100))

/-- **THE PER-CHAIN PREMISE IS SUFFICIENT, NOT NECESSARY.** From the fresh witness system: create
chain `0` at version 1, then cut it by break-glass to version 2 with release `200`'s routing.
The CTM is still at version 1, so the chain is ahead of it and not consistent. Then the CTM
commits `300` (1→2), which installs release `200` at version 2. The last write of chain `0` is
the cut, so the per-chain premise fails. Still, chain `0` ends consistent, at version 2 on
release `200`. Consistency is not an invariant of chain `0` along this run: it fails after the
cut and holds at the end. -/
def Properties.ChainLocalPremiseNotNecessary : Prop :=
  ∃ s₁ s, Run wWorld wSys0 [.genesis 0, .arbitraryCut 0 2 (rowsRouting (wRows 200))] s₁ ∧
    Step wWorld s₁ (.ctm (.commit 300)) s ∧
    ¬ LastWriteNotBreakGlass 0
      [.genesis 0, .arbitraryCut 0 2 (rowsRouting (wRows 200)), .ctm (.commit 300)] ∧
    (∃ c, s₁.chains 0 = some c ∧ ¬ ChainOk wWorld s₁ c) ∧
    ∃ c, s.chains 0 = some c ∧ c.pv = 2 ∧ s.ctm.relAt 2 = 200 ∧ ChainOk wWorld s c ∧
      c.routing = rowsRouting (wRows 200)

/-- **THE REPAIR UN-STICKS THE DRIFTED RETURNER.** Start from the fresh witness system, which
satisfies `SysInv`. After the run of `DriftedReturnerIsStuck`, chain `0` is at version 1 with a
drifted routing and has no transition. In that state the CTM invariant holds, version 1 has
release `100`, slot 1 holds a committed transition, and both of its releases list each selector
once. The repair cut there is the break-glass cut to version 1 with release `100`'s routing.
The repair, the transition and leaving again then all succeed in the model (which omits
timestamps and the other reject-only checks): chain `0` ends at version 2 routing release
`200`, away on another settlement layer. The last routing step that writes chain `0` in the
whole run is its transition, so the per-chain premise holds for chain `0` although its routing
was cut twice. -/
def Properties.RepairUnsticksDriftedReturner : Prop :=
  ∃ s s', MRun wWorld wMSys0 wStuckRun s ∧ SysInv wWorld wMSys0.sys ∧
    (¬ ∃ s'', MStep wWorld s (.base (.transition 0)) s'') ∧
    CtmInv wWorld s.sys.ctm ∧ s.sys.ctm.relAt 1 = 100 ∧ s.sys.ctm.ut 1 ≠ 0 ∧
    ((wWorld.relRows (s.sys.ctm.relAt 1)).map Prod.fst).Nodup ∧
    ((wWorld.relRows (s.sys.edge wWorld 1).newRel).map Prod.fst).Nodup ∧
    repairCut wWorld s.sys 0 1 = .arbitraryCut 0 1 (rowsRouting (wRows 100)) ∧
    MRun wWorld s wUnstickRun s' ∧
    LastWriteNotBreakGlass 0 ((wStuckRun ++ wUnstickRun).filterMap MLabel.base?) ∧
    s'.away 0 = true ∧
    ∃ c, s'.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)

/-- **WITHOUT UNIQUE SELECTORS THE REPAIR DOES NOT UN-STICK.** On the repeated-selector world
`wDupWorld`, whose release `700` (version 2) lists selector `1` twice, start from a fresh CTM
on release `100`, which satisfies `SysInv`. Create chain `0` at version 1, then commit `800`
(1→2, onto `700`) and `900` (2→3, leaving `700`). Chain `0` cannot cross `800`: the derived `Add`
of `700`'s rows adds selector `1` twice. Repair it to version 2 with `700`'s routing. Every
premise of `RepairEnablesTransition` then holds except that `700` lists each selector once, and
chain `0` cannot cross `900` either: the derived `Remove` of `700`'s rows removes selector `1`
twice. -/
def Properties.RepairNeedsUniqueSelectors : Prop :=
  ∃ s s', Run wDupWorld wDupSys0 [.genesis 0, .ctm (.commit 800), .ctm (.commit 900)] s ∧
    SysInv wDupWorld wDupSys0 ∧ (¬ ∃ s'', Step wDupWorld s (.transition 0) s'') ∧
    CtmInv wDupWorld s.ctm ∧ s.ctm.relAt 2 = 700 ∧ s.ctm.ut 2 ≠ 0 ∧
    Step wDupWorld s (repairCut wDupWorld s 0 2) s' ∧
    ¬ ((wDupWorld.relRows (s.ctm.relAt 2)).map Prod.fst).Nodup ∧
    ((wDupWorld.relRows (s.edge wDupWorld 2).newRel).map Prod.fst).Nodup ∧
    ¬ ∃ s'', Step wDupWorld s' (.transition 0) s''

end Contracts.ChainTypeManager
