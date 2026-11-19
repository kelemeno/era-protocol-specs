import EraSpec.Contracts.ChainTypeManager.Specs.ProofGateAtV35

/-!
# Properties: the routing system at `draft/v0.35.0`, with the second-proof-system gate

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ProofGateAtV35` (commit
`b17415d20`). Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.ProofGateAtV35`. The
statements live in `Contracts.ChainTypeManager.ProofGateAtV35.Properties`; a statement named
like one of `ChainRouting`, `ChainLocal` or `Enabledness` (`ChainsRunTheirVersionsRelease`,
`TransitionEnabledIff`, ...) is that statement re-proved over the gated system.

## The v35 step is the gate-free `ChainRouting` step plus one condition

`StepIsTheUngatedStepPlusTheGate`: for every `ChainRouting` label, a v35 step to a routing state
exists iff `ChainRouting`'s step to it exists and `GateHolds` does. `GateHolds` is `True` for
every step except a transition and the bootstrap crossing of a chain that requires its second
proof system. For those it asks the arriving release's verifier to report multi-proof mode.

* **Safety carries over.** The routing image of a v35 run is a `ChainRouting` run
  (`RunIsARun`), so the routing headline holds at v35, globally
  (`ChainsRunTheirVersionsRelease`, `FreshChainsRunTheirVersionsRelease`) and per chain
  (`ChainRunsItsVersionsRelease`).
* **Where no chain requires the second proof system, the routing runs are `ChainRouting`'s.**
  From proof-system fields with the requirement off everywhere, every `ChainRouting` run is the
  routing image of a v35 run in which no chain ever requires it
  (`UngatedRunsAreRunsWithoutTheRequirement`). With `RunIsARun`, the routing states reachable at
  v35 from such a state are exactly those `ChainRouting` reaches. And every step other than the
  transition or the bootstrap crossing of a chain that requires it exists at v35 iff it exists
  in `ChainRouting` (`StepIsTheUngatedStepPlusTheGate`).
* **Liveness gets one premise.** A transition exists iff `Enabledness`'s conditions hold and, if
  the chain requires its second proof system, the arriving release's verifier reports
  multi-proof mode (`TransitionEnabledIff`). Along runs without a break-glass cut, upgrades
  stay enabled under that premise (`UpgradesStayEnabled`), and with validated installs no
  other check the model keeps blocks an upgrade or a deployment
  (`ValidatedRunsKeepEverythingEnabled`). The premise cannot be dropped. In
  `GateStrandsRequiringChain` the CTM commits an edge to a release whose verifier is
  PLONK-only; a chain that requires its second proof system then has no transition, while a
  chain that does not crosses. So `Enabledness`'s `TransitionEnabledIff` and
  `UpgradesStayEnabled`, which are about the gate-free step, do not describe a chain that
  requires its second proof system.
  `protocol-docs/interop-gating.md:43-48` (at `b17415d20`) describes such an edge and leaves its
  prevention to off-chain package verification.

## The guarantee #2628 adds

* From a state where it holds (`ProofInv`), along every v35 run, break-glass cuts included, a
  registered chain that requires its second proof system has a verifier that reports
  multi-proof mode for the empty mask (`RequiringChainsKeepAMultiProofVerifier`). This needs
  `DisablingNeverEnablesMultiProof`, which `MultiProofVerifier` and `ZKsyncOSVerifier` meet.
  `permanentlyRequireSecondProofSystem` checks the mode under the chain's current mask, while
  every cut checks it under mask `0`, and a verifier could treat the two differently
  (`MaskPremiseNeeded`). The model gives every break-glass cut the final check of the v35
  `Admin` facet; the Specs say when a cut in the source makes none.
* That is a statement about the verifier, not about the mode the chain is in. The mode is
  `getProofMode(s.disabledProofSystems)`, and with ZiSK switched off a chain that requires its
  second proof system is not in multi-proof mode
  (`RequirementDoesNotPinTheCurrentProofMode`). The source reserves that switch for the
  Bridgehub owner (`Admin.sol:417-420`; `protocol-docs/interop-gating.md:37-38`); this model
  lets anyone write the mask.
* "Once activated, there is no way back!" (`IAdmin.sol:137-140`), in the model: a registered
  chain's requirement is changed only by the chain's `permanentlyRequireSecondProofSystem`,
  which sets it, and by a break-glass cut of the chain, which may set or clear it
  (`RequirementWriters`). Without such a cut it stays set
  (`RequirementIsPermanentWithoutBreakGlass`). Transitions are those of the in-tree engines; a
  transition whose manifest names another engine is outside the model, as in `ChainRouting`.
  A break-glass cut can clear the requirement, and that is also a way out for a chain stranded
  as in `GateStrandsRequiringChain` (`BreakGlassClearsTheRequirement`).

## Scope

The proof-system fields are a diamond's, and the model has the diamonds of one CTM. A diamond
that migration in deploys starts with fresh fields (`ProofEffect.migrateIn`). Chain migration is
disabled at `b17415d20` (`CHAIN_MIGRATIONS_ENABLED = false`, `common/Config.sol:320`), so the
migration-in steps only add runs; this boundary only matters if a later commit enables
migration. Every result here is about the diamonds registered on the modelled CTM. Callers are not modelled here;
`UpgradeTimingAtV35` has them for `permanentlyRequireSecondProofSystem`.

## Witnesses

`ProofGateWitness` meets the premises of the run-level results in one run in which a chain that
requires its second proof system crosses an edge. `RequiringChainCanCrossWitness` meets those of
the enabledness results with the gate premise in force, `RequirementLifecycleWitness` those of
`RequirementWriters` and `RequirementIsPermanentWithoutBreakGlass`,
`PerChainHeadlineAtV35Witness` those of `ChainRunsItsVersionsRelease` in a run with break-glass
cuts, and `UngatedRunLiftWitness` those of `UngatedRunsAreRunsWithoutTheRequirement`.
`GateStrandsRequiringChain`, `BreakGlassClearsTheRequirement`, `MaskPremiseNeeded` and
`RequirementDoesNotPinTheCurrentProofMode` are the countermodels.
-/

namespace Contracts.ChainTypeManager.ProofGateAtV35

open Contracts.ChainTypeManager

/-! ## The v35 step and run -/

/-- **EVERY v35 STEP IS THE GATE-FREE `ChainRouting` STEP PLUS THE PROOF GATE.** For every `ChainRouting`
label `l` and routing state `sys'`, a v35 step labelled `l` that leaves `sys'` exists, with some
proof-system fields, iff `ChainRouting`'s step `l` to `sys'` exists and `GateHolds` holds before
it. -/
def Properties.StepIsTheUngatedStepPlusTheGate : Prop :=
  ∀ (W : World) (P : ProofWorld) (s : Sys35) (l : Label) (sys' : Sys),
    (∃ pr', Step35 W P s (.routing l) ⟨sys', pr'⟩) ↔ (Step W s.sys l sys' ∧ GateHolds W P s l)

/-- **A v35 RUN IS A `ChainRouting` RUN.** Forgetting the proof-system fields, every v35 run is a
run of `ChainRouting` whose labels are the v35 run's routing steps, in order. The two new writers
are stutters. -/
def Properties.RunIsARun : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (ls : List Label35), Run35 W P s ls s' →
    Run W s.sys (ls.flatMap Label35.routingSteps) s'.sys

/-- **EVERY `ChainRouting` RUN IS A v35 RUN IN WHICH NO CHAIN REQUIRES ITS SECOND PROOF SYSTEM.**
Starting from any proof-system fields with the requirement off everywhere, the same labels run
at v35 to the same routing state, and the requirement is still off everywhere. -/
def Properties.UngatedRunsAreRunsWithoutTheRequirement : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys) (ls : List Label) (pr : ChainId → ProofState),
    Run W s ls s' → (∀ id, (pr id).required = false) →
    ∃ pr', Run35 W P ⟨s, pr⟩ (ls.map Label35.routing) ⟨s', pr'⟩ ∧ ∀ id, (pr' id).required = false

/-! ## The routing headline at v35 -/

/-- **HEADLINE AT v35: EVERY CHAIN AT VERSION `v` HAS EXACTLY `R_v`'S ROUTING.** As
`Contracts.ChainTypeManager.Properties.ChainsRunTheirVersionsRelease`, over v35 runs: along any
v35 run from a state whose routing system satisfies `SysInv`, with no break-glass cut, every
chain at a version `v` with a release `R_v` routes exactly `R_v`, and `R_v` is a release of
version `v`. The proof-system fields are arbitrary. -/
def Properties.ChainsRunTheirVersionsRelease : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (ls : List Label35), SysInv W s.sys →
    Run35 W P s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (W.relRows (s'.sys.ctm.relAt c.pv))

/-- **ON A FRESHLY INITIALIZED CTM AT v35, EVERY CHAIN HAS ITS VERSION'S RELEASE.** Along any v35
run with no break-glass cut from a CTM just initialized with a nonzero release `R` and no chains,
whatever the proof-system fields, every chain is at a version with a release, which is a release
of that version, and routes exactly it. -/
def Properties.FreshChainsRunTheirVersionsRelease : Prop :=
  ∀ (W : World) (P : ProofWorld) (R : Address) (pr : ChainId → ProofState) (s' : Sys35)
    (ls : List Label35), R ≠ 0 →
    Run35 W P ⟨⟨initState W R, fun _ => none⟩, pr⟩ ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.sys.chains id = some c →
      s'.sys.ctm.relAt c.pv ≠ 0 ∧ W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (W.relRows (s'.sys.ctm.relAt c.pv))

/-- **PER-CHAIN HEADLINE AT v35.** As `Contracts.ChainTypeManager.Properties.ChainRunsItsVersionsRelease`:
if the last routing step of the run that writes chain `id` is not a break-glass cut, chain `id`
is not ahead of its CTM and routes its version's release, if the CTM has one. The two
proof-system writers are not routing steps. -/
def Properties.ChainRunsItsVersionsRelease : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (ls : List Label35) (id : ChainId),
    CtmInv W s.sys.ctm → (∀ c, s.sys.chains id = some c → ChainOk W s.sys c) →
    Run35 W P s ls s' → LastWriteNotBreakGlass id (ls.flatMap Label35.routingSteps) →
    ∀ c, s'.sys.chains id = some c → c.pv ≤ s'.sys.ctm.pv ∧
      (s'.sys.ctm.relAt c.pv ≠ 0 → W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
        c.routing = rowsRouting (W.relRows (s'.sys.ctm.relAt c.pv)))

/-! ## Enabledness at v35 -/

/-- **EXACTLY WHEN A TRANSITION EXISTS AT v35.** Under the CTM's invariant, a registered chain
has a v35 transition iff the three conditions of
`Contracts.ChainTypeManager.Properties.TransitionEnabledIff` hold and, if the chain requires its
second proof system, the verifier of the release its edge arrives at reports multi-proof mode
with nothing disabled. As in `Enabledness`, this is about the checks the model keeps. -/
def Properties.TransitionEnabledIff : Prop :=
  ∀ (W : World) (P : ProofWorld) (s : Sys35) (id : ChainId) (c : Chain),
    CtmInv W s.sys.ctm → s.sys.chains id = some c →
    ((∃ s', Step35 W P s (.routing (.transition id)) s') ↔
      (s.sys.ctm.ut c.pv ≠ 0 ∧ c.routing = rowsRouting (W.relRows (s.sys.ctm.relAt c.pv)) ∧
        (W.relRows (s.sys.edge W c.pv).fromRel = W.relRows (s.sys.edge W c.pv).newRel ∨
          (ReleaseWf W (s.sys.edge W c.pv).fromRel ∧ ReleaseWf W (s.sys.edge W c.pv).newRel))) ∧
      ((s.proof id).required = true → P.multi (arrivingVerifier W P s.sys c) 0 = true))

/-- **UPGRADES STAY ENABLED AT v35, GIVEN A MULTI-PROOF ARRIVING VERIFIER WHERE THE CHAIN NEEDS
ONE.** As `Contracts.ChainTypeManager.Properties.UpgradesStayEnabled`, over v35 runs, with one
more premise on the chain: if it requires its second proof system, the arriving release's
verifier reports multi-proof mode. The step lands on the arriving release, at the edge's new
version, with that verifier installed. -/
def Properties.UpgradesStayEnabled : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (ls : List Label35), SysInv W s.sys →
    ChainsOnWfReleases W s.sys → Run35 W P s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.ut c.pv ≠ 0 →
      ReleaseWf W (s'.sys.edge W c.pv).newRel →
      ((s'.proof id).required = true → P.multi (arrivingVerifier W P s'.sys c) 0 = true) →
      Step35 W P s' (.routing (.transition id))
        ⟨s'.sys.crossEdge W id c,
          upd s'.proof id ((s'.proof id).install (arrivingVerifier W P s'.sys c))⟩

/-- **WITH VALIDATED INSTALLS, ONLY THE PROOF GATE CAN BLOCK AN UPGRADE AT v35.** As
`Contracts.ChainTypeManager.Properties.ValidatedRunsKeepEverythingEnabled`, over v35 runs: at
the end of a run with no break-glass cut, from an invariant state whose installed releases are
well-formed, with every install validated,
* every chain whose version has a committed edge can cross it, if it does not require its
  second proof system or the arriving release's verifier reports multi-proof mode;
* every free id can be deployed by genesis or by migration in, with no further condition.
"Can" is relative to the checks the model keeps; migration in is disabled at `b17415d20`
(*Scope*), so its conjunct describes a step the production source does not take. -/
def Properties.ValidatedRunsKeepEverythingEnabled : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (ls : List Label35), SysInv W s.sys →
    RecordedReleasesWf W s.sys.ctm → Run35 W P s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) →
    (∀ l ∈ ls.flatMap Label35.routingSteps, l.InstallsWf W) →
    (∀ id c, s'.sys.chains id = some c → s'.sys.ctm.ut c.pv ≠ 0 →
      ((s'.proof id).required = true → P.multi (arrivingVerifier W P s'.sys c) 0 = true) →
      ∃ pr', Step35 W P s' (.routing (.transition id)) ⟨s'.sys.crossEdge W id c, pr'⟩) ∧
    (∀ id, s'.sys.chains id = none →
      (∃ pr', Step35 W P s' (.routing (.genesis id)) ⟨s'.sys.deployNew W id, pr'⟩) ∧
      ∃ pr', Step35 W P s' (.routing (.migrateIn id)) ⟨s'.sys.deployNew W id, pr'⟩)

/-! ## What #2628 guarantees -/

/-- **A CHAIN THAT REQUIRES ITS SECOND PROOF SYSTEM KEEPS A MULTI-PROOF VERIFIER.** Along every
v35 run, break-glass cuts included, from a state where `ProofInv` holds (every state where no
chain requires the second proof system is one), every registered chain that requires it has a
verifier that reports multi-proof mode for the empty mask, `getProofMode(0)`. The verifiers
must satisfy `DisablingNeverEnablesMultiProof`. Every break-glass cut of the model makes the
v35 `Admin` facet's final check (Specs, *Break-glass*). This says nothing about the chain's own
mask; see `RequirementDoesNotPinTheCurrentProofMode`. -/
def Properties.RequiringChainsKeepAMultiProofVerifier : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (ls : List Label35),
    DisablingNeverEnablesMultiProof P → ProofInv P s → Run35 W P s ls s' → ProofInv P s'

/-- **ONLY ITS WRITER SETS THE REQUIREMENT; ONLY A BREAK-GLASS CUT OF THE CHAIN CHANGES IT
OTHERWISE.** If a step changes a registered chain's `secondProofSystemRequired`, the step is that
chain's `permanentlyRequireSecondProofSystem` and sets it, or a break-glass cut of that chain
(which may set or clear it). Transitions, the bootstrap crossing, genesis and migration of other
chains, CTM writers and `setProofSystemStatus` leave it alone. -/
def Properties.RequirementWriters : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (l : Label35) (id : ChainId) (c : Chain),
    Step35 W P s l s' → s.sys.chains id = some c →
    (s'.proof id).required ≠ (s.proof id).required →
    (l = .requireSecondProofSystem id ∧ (s'.proof id).required = true) ∨
      ∃ v ρ, l = .routing (.arbitraryCut id v ρ)

/-- **"NO WAY BACK", EXCEPT BY BREAK-GLASS** (`IAdmin.sol:137-140`). Along any v35 run with no
break-glass cut of chain `id`, a registered chain that requires its second proof system still
requires it at the end. This is about the chain's diamond on the modelled CTM, upgraded by the
in-tree engines. -/
def Properties.RequirementIsPermanentWithoutBreakGlass : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (ls : List Label35) (id : ChainId) (c : Chain),
    Run35 W P s ls s' → s.sys.chains id = some c → (s.proof id).required = true →
    (∀ v ρ, Label35.routing (.arbitraryCut id v ρ) ∉ ls) → (s'.proof id).required = true

/-! ## Countermodels -/

/-- **A PLONK-ONLY ARRIVING VERIFIER STRANDS THE CHAIN THAT REQUIRES ITS SECOND PROOF SYSTEM.** On
`wWorld` with `wProofPlonk`, run `wGateSetup` from `wSys35`: chains `0` and `1` are created at
version 1 on release `100`, chain `0` requires its second proof system, and the CTM commits `300`
(1→2) to release `200`, whose verifier `52` is PLONK-only.
* Every premise of `Contracts.ChainTypeManager.Properties.UpgradesStayEnabled` holds for the
  run's `ChainRouting` image: the start satisfies `SysInv` and `ChainsOnWfReleases`, there is no
  break-glass cut, an edge is committed at chain `0`'s version and release `200` is well-formed.
* Chain `0`'s verifier `51` is in multi-proof mode, so `ProofInv` holds.
* `ChainRouting` lets chain `0` cross the edge, but in this state chain `0` has no v35
  transition.
* Chain `1`, which does not require the second proof system, has one.
`protocol-docs/interop-gating.md:43-48` (at `b17415d20`) describes such an edge and leaves its
prevention to off-chain package verification. -/
def Properties.GateStrandsRequiringChain : Prop :=
  ∃ s, Run35 wWorld wProofPlonk wSys35 wGateSetup s ∧
    SysInv wWorld wSys35.sys ∧ ChainsOnWfReleases wWorld wSys35.sys ∧
    (∀ l ∈ wGateSetup, ¬ l.isArbitrary) ∧ ProofInv wProofPlonk s ∧
    (∃ c, s.sys.chains 0 = some c ∧ c.pv = 1 ∧ s.sys.ctm.ut 1 = 300 ∧
      (s.proof 0).required = true ∧ ReleaseWf wWorld (s.sys.edge wWorld 1).newRel ∧
      wProofPlonk.multi (arrivingVerifier wWorld wProofPlonk s.sys c) 0 = false ∧
      Step wWorld s.sys (.transition 0) (s.sys.crossEdge wWorld 0 c)) ∧
    (¬ ∃ s', Step35 wWorld wProofPlonk s (.routing (.transition 0)) s') ∧
    ∃ s', Step35 wWorld wProofPlonk s (.routing (.transition 1)) s'

/-- **A BREAK-GLASS CUT CAN CLEAR THE REQUIREMENT, AND THE STRANDED CHAIN THEN CROSSES.** From the
state of `GateStrandsRequiringChain`, a break-glass cut of chain `0` (in the source, the CTM
owner's `executeUpgrade`) that keeps its version and its routing, with an init that turns the
requirement off, succeeds. After it chain `0` crosses to version 2 on release `200`, with the
PLONK-only verifier `52` installed. -/
def Properties.BreakGlassClearsTheRequirement : Prop :=
  ∃ s s', Run35 wWorld wProofPlonk wSys35 wGateSetup s ∧ (s.proof 0).required = true ∧
    Step35 wWorld wProofPlonk s (.routing (.arbitraryCut 0 1 (rowsRouting (wRows 100)))) s' ∧
    (s'.proof 0).required = false ∧
    ∃ s'', Step35 wWorld wProofPlonk s' (.routing (.transition 0)) s'' ∧
      (∃ c, s''.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)) ∧
      (s''.proof 0).verifier = 52

/-- **`DisablingNeverEnablesMultiProof` IS NEEDED.** With `wProofOdd`, whose verifier `54` is in
multi-proof mode exactly with ZiSK disabled (mask `ziskBit`), run `wZiskOffFirstRun` from
`wSys35`: chain `0` is created, ZiSK is switched off, and the chain requires its second proof
system. `ProofInv` held at the start and fails at the end. The verifier is hypothetical; the
masks are ones `setProofSystemStatus` can write. -/
def Properties.MaskPremiseNeeded : Prop :=
  ¬ DisablingNeverEnablesMultiProof wProofOdd ∧ ProofInv wProofOdd wSys35 ∧
    ∃ s, Run35 wWorld wProofOdd wSys35 wZiskOffFirstRun s ∧
      (s.proof 0).required = true ∧ ¬ ProofInv wProofOdd s

/-- **THE REQUIREMENT DOES NOT PIN THE CHAIN'S CURRENT PROOF MODE.** On `wWorld` with
`wProofMulti`, run `wZiskOffRun` from `wSys35`: chain `0` is created with verifier `51`, requires
its second proof system, and ZiSK is switched off (mask `ziskBit`; in the source only the
Bridgehub owner can do this once the requirement is set). At the end the chain still requires
its second proof system and `ProofInv` holds: verifier `51` reports multi-proof mode for the
empty mask. But for the chain's own mask it does not, so `getProofMode(s.disabledProofSystems)`
is not multi-proof. -/
def Properties.RequirementDoesNotPinTheCurrentProofMode : Prop :=
  ∃ s, Run35 wWorld wProofMulti wSys35 wZiskOffRun s ∧
    (s.proof 0).required = true ∧ ProofInv wProofMulti s ∧
    wProofMulti.multi (s.proof 0).verifier 0 = true ∧
    wProofMulti.multi (s.proof 0).verifier (s.proof 0).disabled = false

/-! ## Witnesses -/

/-- **THE v35 PREMISES ARE MET, AND A CHAIN THAT REQUIRES ITS SECOND PROOF SYSTEM UPGRADES.** On
`wWorld` with `wProofMulti` (every release ships a multi-proof verifier), the start `wSys35`
satisfies `SysInv`, `ChainsOnWfReleases`, `RecordedReleasesWf`, `ProofInv` and `NoChainRequires`,
and the verifiers satisfy `DisablingNeverEnablesMultiProof`. Run `wGateRun` (`wGateSetup`, then
transitions of chains `0` and `1`), with no break-glass cut and validated installs. At the end
both chains are at version 2 on release `200`; chain `0` still requires its second proof system,
with release `200`'s verifier `53` installed, which is in multi-proof mode; and `ProofInv`
holds. `wSys35`'s routing system is a freshly initialized CTM on release `100` with no chains, so
this meets the premises of `RunIsARun`, `ChainsRunTheirVersionsRelease`,
`FreshChainsRunTheirVersionsRelease`, `ValidatedRunsKeepEverythingEnabled` and
`RequiringChainsKeepAMultiProofVerifier`. -/
def Properties.ProofGateWitness : Prop :=
  SysInv wWorld wSys35.sys ∧ ChainsOnWfReleases wWorld wSys35.sys ∧
    RecordedReleasesWf wWorld wSys35.sys.ctm ∧ ProofInv wProofMulti wSys35 ∧ NoChainRequires wSys35 ∧
    DisablingNeverEnablesMultiProof wProofMulti ∧
    ∃ s', Run35 wWorld wProofMulti wSys35 wGateRun s' ∧
      (∀ l ∈ wGateRun, ¬ l.isArbitrary) ∧
      (∀ l ∈ wGateRun.flatMap Label35.routingSteps, l.InstallsWf wWorld) ∧
      (∀ id, id ≤ 1 → ∃ c, s'.sys.chains id = some c ∧ c.pv = 2 ∧
        c.routing = rowsRouting (wRows 200)) ∧
      (s'.proof 0).required = true ∧ (s'.proof 0).verifier = 53 ∧
      wProofMulti.multi 53 0 = true ∧ ProofInv wProofMulti s'

/-- **THE ENABLEDNESS PREMISES HOLD WITH THE GATE IN FORCE.** On `wWorld` with `wProofMulti`, run
`wGateSetup` from `wSys35`, which satisfies `SysInv`, `ChainsOnWfReleases` and
`RecordedReleasesWf`; the run has no break-glass cut and its one install is validated. At its
end the CTM satisfies `CtmInv`, and chain `0` is registered at version 1, routes the release the
CTM recorded for that version, has an edge committed there whose departing and arriving releases
are well-formed, requires its second proof system, and the arriving release's verifier reports
multi-proof mode. So every premise of `UpgradesStayEnabled`, of the first conclusion of
`ValidatedRunsKeepEverythingEnabled` and of `TransitionEnabledIff`, and the right side of the
latter, hold for a chain whose gate premise is not vacuous. Chain `0`'s transition exists, to
`crossEdge` with verifier `53` installed. -/
def Properties.RequiringChainCanCrossWitness : Prop :=
  SysInv wWorld wSys35.sys ∧ ChainsOnWfReleases wWorld wSys35.sys ∧
    RecordedReleasesWf wWorld wSys35.sys.ctm ∧ (∀ l ∈ wGateSetup, ¬ l.isArbitrary) ∧
    (∀ l ∈ wGateSetup.flatMap Label35.routingSteps, l.InstallsWf wWorld) ∧
    ∃ s c, Run35 wWorld wProofMulti wSys35 wGateSetup s ∧ CtmInv wWorld s.sys.ctm ∧
      s.sys.chains 0 = some c ∧ c.pv = 1 ∧ s.sys.ctm.ut c.pv ≠ 0 ∧
      c.routing = rowsRouting (wWorld.relRows (s.sys.ctm.relAt c.pv)) ∧
      ReleaseWf wWorld (s.sys.edge wWorld c.pv).fromRel ∧
      ReleaseWf wWorld (s.sys.edge wWorld c.pv).newRel ∧
      (s.proof 0).required = true ∧
      wProofMulti.multi (arrivingVerifier wWorld wProofMulti s.sys c) 0 = true ∧
      Step35 wWorld wProofMulti s (.routing (.transition 0))
        ⟨s.sys.crossEdge wWorld 0 c, upd s.proof 0 ((s.proof 0).install 53)⟩

/-- **THE REQUIREMENT'S WRITERS AND ITS PERMANENCE, ON CONCRETE STEPS.** On `wWorld` with
`wProofMulti`:
* after the geneses of chains `0` and `1` from `wSys35`, chain `0`'s
  `permanentlyRequireSecondProofSystem` changes a registered chain's requirement from off to on
  (the premises of `RequirementWriters`, in its first case; `BreakGlassClearsTheRequirement` is
  a step in its second);
* from the end of `wGateSetup`, where chain `0` is registered and requires its second proof
  system, the two transitions of `wGateRun` are a run with no break-glass cut of chain `0`, and
  chain `0` still requires it at the end (the premises and conclusion of
  `RequirementIsPermanentWithoutBreakGlass`). -/
def Properties.RequirementLifecycleWitness : Prop :=
  (∃ s s' c, Run35 wWorld wProofMulti wSys35 [.routing (.genesis 0), .routing (.genesis 1)] s ∧
    Step35 wWorld wProofMulti s (.requireSecondProofSystem 0) s' ∧ s.sys.chains 0 = some c ∧
    (s.proof 0).required = false ∧ (s'.proof 0).required = true) ∧
  ∃ s s' c, Run35 wWorld wProofMulti wSys35 wGateSetup s ∧
    Run35 wWorld wProofMulti s [.routing (.transition 0), .routing (.transition 1)] s' ∧
    s.sys.chains 0 = some c ∧ (s.proof 0).required = true ∧
    (∀ v ρ, Label35.routing (.arbitraryCut 0 v ρ) ∉
      [Label35.routing (.transition 0), Label35.routing (.transition 1)]) ∧
    (s'.proof 0).required = true

/-- **THE PER-CHAIN PREMISE HOLDS WHERE THE GLOBAL ONE FAILS, AT v35.** On `wWorld` with
`wProofMulti`, run `wGateLocalRun` from `wSys35`, which satisfies `SysInv` and has no chain `0`:
chains `0` and `1` are created, chain `0` requires its second proof system, break-glass cuts drift
both chains, a third cut restores chain `0`, the CTM commits `300` and chain `0` crosses it. The
run has break-glass cuts, so `ChainsRunTheirVersionsRelease` does not apply to it. The last
routing step writing chain `0` is its transition, so `ChainRunsItsVersionsRelease` applies to
chain `0`: it ends at version 2 on release `200`, still requiring its second proof system with
release `200`'s verifier `53` installed, and `ProofInv` holds. The last write of chain `1` is a
cut, and chain `1` ends at version 1 on a routing other than release `100`'s. -/
def Properties.PerChainHeadlineAtV35Witness : Prop :=
  ∃ s, Run35 wWorld wProofMulti wSys35 wGateLocalRun s ∧ SysInv wWorld wSys35.sys ∧
    wSys35.sys.chains 0 = none ∧ (∃ l ∈ wGateLocalRun, l.isArbitrary) ∧
    LastWriteNotBreakGlass 0 (wGateLocalRun.flatMap Label35.routingSteps) ∧
    ¬ LastWriteNotBreakGlass 1 (wGateLocalRun.flatMap Label35.routingSteps) ∧
    (∃ c, s.sys.chains 0 = some c ∧ c.pv = 2 ∧ s.sys.ctm.relAt 2 = 200 ∧
      c.routing = rowsRouting (wRows 200)) ∧
    (s.proof 0).required = true ∧ (s.proof 0).verifier = 53 ∧ ProofInv wProofMulti s ∧
    (∃ c, s.sys.chains 1 = some c ∧ c.pv = 1 ∧ s.sys.ctm.relAt 1 = 100 ∧
      c.routing ≠ rowsRouting (wRows 100))

/-- **A `ChainRouting` RUN THAT LIFTS TO v35.** The routing image of `wGateRun`, namely the
geneses of chains `0` and `1`, the commit of `300` and both transitions, is a `ChainRouting` run
from `wSys0` that ends with both chains at version 2, and the fields of `wSys35` have the
requirement off everywhere: the premises of `UngatedRunsAreRunsWithoutTheRequirement`. -/
def Properties.UngatedRunLiftWitness : Prop :=
  wGateRun.flatMap Label35.routingSteps =
      [.genesis 0, .genesis 1, .ctm (.commit 300), .transition 0, .transition 1] ∧
    (∀ id : ChainId, (wSys35.proof id).required = false) ∧
    ∃ s', Run wWorld wSys0 (wGateRun.flatMap Label35.routingSteps) s' ∧
      ∀ id, id ≤ 1 → ∃ c, s'.chains id = some c ∧ c.pv = 2

end Contracts.ChainTypeManager.ProofGateAtV35
