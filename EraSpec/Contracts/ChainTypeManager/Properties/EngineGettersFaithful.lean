import EraSpec.Contracts.ChainTypeManager.Specs.EngineGettersFaithful

/-!
# Properties: what the routing headline assumes about the engine's getters

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.EngineGettersFaithful`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.EngineGettersFaithful`. Namespace
`Contracts.ChainTypeManager.EngineGetters`.

## The premise, made explicit

* **The original transition is the derived-getter case.** Applying the derived cut list is
  `ChainRouting`'s `applyDerived` (`DerivedCutsAreApplyDerived`). When every committed slot holds
  an object whose `facetCuts()` and `upgradeTarget()` are the derived ones (`SlotsDerived`), a
  refined routing step is exactly a `ChainRouting` step (`DerivedEngineStepIsAStep`).
* **Under that premise the refined model is the original one.** Suppose the CTM's code stays in
  place, the start's slots are derived, and every object the run commits or installs as a
  replacement is derived. Then every refined run is an `ExecutorUpgradeChain` run between the same
  states, and the slots stay derived (`DerivedEngineRunIsAUpgradeChainRun`).
* **The re-proved headline** (`DerivedEngineTameRunKeepsChainsOnTheirRelease`) is
  `RefinedTameRunKeepsChainsOnTheirRelease` with that premise as a hypothesis. Every genuine
  `CTMTransition` meets it, and so does the witness (`EngineGettersWitness`).

## Without it

`RefinedTameRunKeepsChainsOnTheirRelease` is documented as needing "nothing ... about the
transitions a `forward` installs as replacements", and the README says the headline holds
"whatever replacements report". Both hold of `oldProtocolVersion()`, not of the getters only the
engine reads.

* **Foreign cuts.** `400` reports the same four CTM-read getters as a genuine replacement of
  `300`, so it is `World.Genuine` and passes every CTM check. Its `facetCuts()` also add selector
  `9`. After the tame run "create, commit `300`, forward the replacement by `400`,
  `upgradeChain(400, 0)`", chain `0` is at version 2 and routes selector `9` besides release `200`.
  `SysInv` fails. The original model runs the same transactions to exactly release `200`
  (`ForeignCutsBreakTheHeadline`).
* **A foreign target.** `400`'s `upgradeTarget()` lands on version 3, not 2. After the same run,
  chain `0` is ahead of its CTM. After a further tame `applyCTMUpgrade(600)` (2→3), it sits at
  version 3 without routing release `250` (`ForeignTargetBreaksTheHeadline`).
-/

namespace Contracts.ChainTypeManager.EngineGetters

/-! ## The premise, made explicit -/

/-- **THE DERIVED CUT LIST IS `ChainRouting`'S DERIVED CUTS.** Applying
`TransitionDerivationLib.deriveFacetCuts`'s list action by action is `applyDerived`. -/
def Properties.DerivedCutsAreApplyDerived : Prop :=
  ∀ (ρ : Routing) (A B : ReleaseRows), applyCuts ρ (derivedCuts A B) = applyDerived ρ A B

/-- **WITH DERIVED SLOTS, A REFINED ROUTING STEP IS A `ChainRouting` STEP.** In a state whose
committed slots all hold objects whose `facetCuts()` and `upgradeTarget()` are what a
`CTMTransition` returns, the refined step and `ChainRouting`'s step relate exactly the same
states. -/
def Properties.DerivedEngineStepIsAStep : Prop :=
  ∀ (W : World) (G : Engine) (s s' : Sys) (l : Label), SlotsDerived W G s.ctm →
    (EStep W G s l s' ↔ Step W s l s')

/-- **WITH DERIVED OBJECTS, A REFINED RUN IS AN `ExecutorUpgradeChain` RUN.** Suppose each
reinitializer moves at most its own proxy and no transaction moves the CTM proxy. The start's
committed slots hold derived objects, and so does every object the run writes into a slot. Then
the refined run is an `ExecutorUpgradeChain` run with the same transactions between the same
states, and at the end every committed slot still holds a derived object. -/
def Properties.DerivedEngineRunIsAUpgradeChainRun : Prop :=
  ∀ (X : XConfig) (G : Engine) (s s' : XState) (us : List ULabel),
    ProxyUpgradeCurrent.ReinitFrames X.rc → SlotsDerived X.W G s.sys.ctm → EURun X G s us s' →
    (∀ u ∈ us, u.toX.KeepsCtmCode X) → (∀ t, (∃ u ∈ us, Installs t u) → EngineDerived X.W G t) →
    URun X s us s' ∧ SlotsDerived X.W G s'.sys.ctm

/-- **THE ROUTING HEADLINE ALONG REFINED RUNS, WITH THE ENGINE PREMISE EXPLICIT.** Take any refined
run of tame transactions from a state satisfying `SysInv`, with reinitializers that move at most
their own proxy. The start's committed slots hold objects returning what a `CTMTransition`
returns, and so does every object the run commits or installs as a replacement. Nothing is
assumed about what replacements report as `oldProtocolVersion()`. Then every chain at a version
`v` with a release `R_v` routes exactly `R_v`, and `R_v` is a release of version `v`. -/
def Properties.DerivedEngineTameRunKeepsChainsOnTheirRelease : Prop :=
  ∀ (X : XConfig) (G : Engine) (s s' : XState) (us : List ULabel),
    ProxyUpgradeCurrent.ReinitFrames X.rc → SysInv X.W s.sys → SlotsDerived X.W G s.sys.ctm →
    EURun X G s us s' → (∀ u ∈ us, u.Tame X) →
    (∀ t, (∃ u ∈ us, Installs t u) → EngineDerived X.W G t) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      X.W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (X.W.relRows (s'.sys.ctm.relAt c.pv))

/-! ## Without it: the countermodels -/

/-- **A REPLACEMENT WITH FOREIGN CUTS BREAKS THE HEADLINE AFTER A TAME `upgradeChain`.** In
`wForeignCuts`, transition `400` reports the four CTM-read getters of a genuine replacement of
`300` (`World.Genuine`). Its `facetCuts()` are the derived cuts plus an `Add` of selector `9`.
Every other object, `300` included, is derived. Start from the fresh witness system, which
satisfies `SysInv`, has no committed slot, and whose reinitializers satisfy `ReinitFrames`. Run
`wReplaceRun`: every transaction is tame, and the only objects it writes into slots are `300` and
`400`. At the end chain `0` is at version 2, whose release is `200`. It routes selector `9` to
facet `99`, so it does not route release `200`, and `SysInv` fails. `ExecutorUpgradeChain` runs
the same transactions from the same start, and there chain `0` routes exactly release `200`. -/
def Properties.ForeignCutsBreakTheHeadline : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧ SysInv wX.W wX0.sys ∧
    SlotsDerived wX.W wForeignCuts wX0.sys.ctm ∧ (∀ u ∈ wReplaceRun, u.Tame wX) ∧
    (∀ t, (∃ u ∈ wReplaceRun, Installs t u) → t = 300 ∨ t = 400) ∧
    EngineDerived wWorld wForeignCuts 300 ∧ wWorld.Genuine 400 ∧
    ¬ EngineDerived wWorld wForeignCuts 400 ∧
    (∃ s, EURun wX wForeignCuts wX0 wReplaceRun s ∧
      (∃ c, s.sys.chains 0 = some c ∧ c.pv = 2 ∧ s.sys.ctm.relAt 2 = 200 ∧
        c.routing 9 = some (99, false) ∧ c.routing ≠ rowsRouting (wWorld.relRows 200)) ∧
      ¬ SysInv wX.W s.sys) ∧
    ∃ s', URun wX wX0 wReplaceRun s' ∧
      ∃ c, s'.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wWorld.relRows 200)

/-- **A REPLACEMENT WITH A FOREIGN TARGET BREAKS THE HEADLINE AFTER A TAME COMMIT.** In
`wForeignTarget`, transition `400` reports the four CTM-read getters of a genuine replacement of
`300`, and its `facetCuts()` are the derived ones. Its `upgradeTarget()` lands on version 3, not
on its `newProtocolVersion()`, 2. Every other object is derived. From the fresh witness system, run
`wReplaceRun`, then `applyCTMUpgrade(600)` (2→3); every transaction is tame. After `wReplaceRun`
chain `0` routes release `200` at version 3, while the CTM is at version 2, so `SysInv` fails.
After the commit the CTM is at version 3, whose release is `250`, and chain `0` does not route it. -/
def Properties.ForeignTargetBreaksTheHeadline : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧ SysInv wX.W wX0.sys ∧
    SlotsDerived wX.W wForeignTarget wX0.sys.ctm ∧
    (∀ u ∈ wReplaceRun ++ [.x (.commit 600)], u.Tame wX) ∧
    wWorld.Genuine 400 ∧ ¬ EngineDerived wWorld wForeignTarget 400 ∧
    wForeignTarget.cuts 400 = derivedCuts (wWorld.relRows 100) (wWorld.relRows 200) ∧
    ∃ s s', EURun wX wForeignTarget wX0 wReplaceRun s ∧
      (∃ c, s.sys.chains 0 = some c ∧ c.pv = 3 ∧ s.sys.ctm.pv = 2 ∧
        c.routing = rowsRouting (wWorld.relRows 200)) ∧
      ¬ SysInv wX.W s.sys ∧
      EUStep wX wForeignTarget s (.x (.commit 600)) s' ∧
      ∃ c, s'.sys.chains 0 = some c ∧ c.pv = 3 ∧ s'.sys.ctm.relAt 3 = 250 ∧
        c.routing ≠ rowsRouting (wWorld.relRows 250)

/-! ## Witness -/

/-- **THE ENGINE PREMISE IS MET BY A REAL RUN.** In `wGenuineEngine` every object returns what a
`CTMTransition` returns. The fresh witness system satisfies `SysInv` and has no committed slot, and
its reinitializers satisfy `ReinitFrames`. Every transaction of `wReplaceRun` is tame. The refined
run exists, and chain `0` ends at version 2 routing exactly release `200`. -/
def Properties.EngineGettersWitness : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧ SysInv wX.W wX0.sys ∧
    (∀ t, EngineDerived wWorld wGenuineEngine t) ∧ SlotsDerived wX.W wGenuineEngine wX0.sys.ctm ∧
    (∀ u ∈ wReplaceRun, u.Tame wX) ∧
    ∃ s, EURun wX wGenuineEngine wX0 wReplaceRun s ∧
      ∃ c, s.sys.chains 0 = some c ∧ c.pv = 2 ∧ s.sys.ctm.relAt 2 = 200 ∧
        c.routing = rowsRouting (wWorld.relRows 200)

end Contracts.ChainTypeManager.EngineGetters
