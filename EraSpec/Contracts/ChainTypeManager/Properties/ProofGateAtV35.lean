import EraSpec.Contracts.ChainTypeManager.Specs.ProofGateAtV35

/-!
# Properties: the routing system at `draft/v0.35.0`, with the second-proof-system gate

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ProofGateAtV35` (commit
`d9f6789`). Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.ProofGateAtV35`. The
statements live in `Contracts.ChainTypeManager.ProofGateAtV35.Properties`; a statement named
like an `e561b9cc2` one (`ChainsRunTheirVersionsRelease`, `TransitionEnabledIff`, ...) is that
statement re-proved over the v35 system.

## The v35 step is the `e561b9cc2` step plus one condition

`StepIsTheE561StepPlusTheGate`: for every `ChainRouting` label, a v35 step to a routing state
exists iff `ChainRouting`'s step to it exists and `GateHolds` does. `GateHolds` is `True` for
every step except a transition and the bootstrap crossing of a chain that requires its second
proof system. For those it asks the arriving release's verifier to report multi-proof mode.

* **Safety carries over.** A v35 run is a `ChainRouting` run (`RunIsARun`), so the routing
  headline holds at v35, globally (`ChainsRunTheirVersionsRelease`,
  `FreshChainsRunTheirVersionsRelease`) and per chain (`ChainRunsItsVersionsRelease`).
* **Everything carries over where no chain requires the second proof system.** Every
  `ChainRouting` run is a v35 run in which no chain ever requires it
  (`E561RunsAreRunsWithoutTheRequirement`). So for such chains every `e561b9cc2` result,
  enabledness included, describes v35 verbatim.
* **Liveness gets one premise.** A transition exists iff `e561b9cc2`'s conditions hold and, if
  the chain requires its second proof system, the arriving release's verifier reports
  multi-proof mode (`TransitionEnabledIff`). Along runs without a break-glass cut, upgrades
  stay enabled under that premise (`UpgradesStayEnabled`), and with validated installs
  nothing else blocks progress (`ValidatedRunsKeepEverythingEnabled`). The premise cannot be
  dropped. When the CTM commits an edge to a release whose verifier is PLONK-only, a chain
  that requires its second proof system is stranded while every other chain crosses
  (`GateStrandsRequiringChain`). So `e561b9cc2`'s `TransitionEnabledIff` and
  `UpgradesStayEnabled` are false of v35 as stated.

## The guarantee #2628 adds

* Along every v35 run, break-glass cuts included, a chain that requires its second proof
  system has a verifier in multi-proof mode with nothing disabled
  (`RequiringChainsKeepAMultiProofVerifier`). This needs `DisablingNeverEnablesMultiProof`,
  which every in-tree verifier meets. `permanentlyRequireSecondProofSystem` checks the mode
  under the chain's current mask, while every cut checks it under mask `0`, and a verifier
  could treat the two differently (`MaskPremiseNeeded`).
* "Once activated, there is no way back!" (`IAdmin.sol:137-140`) holds against everyone but
  the CTM owner. Only `permanentlyRequireSecondProofSystem` sets the requirement, and only a
  break-glass cut of the chain clears it (`RequirementWriters`,
  `RequirementIsPermanentWithoutBreakGlass`). The CTM owner's cut can clear it, and that cut is
  also the way out for a stranded chain (`BreakGlassClearsTheRequirement`).

## Witnesses

`ProofGateWitness` meets every premise above in one run where a chain that requires its
second proof system crosses an edge. `GateStrandsRequiringChain`, `BreakGlassClearsTheRequirement`
and `MaskPremiseNeeded` are the countermodels.
-/

namespace Contracts.ChainTypeManager.ProofGateAtV35

open Contracts.ChainTypeManager

/-! ## The v35 step and run -/

/-- **EVERY v35 STEP IS THE `e561b9cc2` STEP PLUS THE PROOF GATE.** For every `ChainRouting`
label `l` and routing state `sys'`, a v35 step labelled `l` that leaves `sys'` exists, with some
proof-system fields, iff `ChainRouting`'s step `l` to `sys'` exists and `GateHolds` holds before
it. -/
def Properties.StepIsTheE561StepPlusTheGate : Prop :=
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
def Properties.E561RunsAreRunsWithoutTheRequirement : Prop :=
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

/-- **ON A FRESHLY INITIALIZED CTM AT v35, EVERY CHAIN HAS ITS VERSION'S RELEASE.** -/
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
with nothing disabled. -/
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
* every free id can be deployed by genesis or by migration in, with no further condition. -/
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
verifier in multi-proof mode with nothing disabled. The verifiers must satisfy
`DisablingNeverEnablesMultiProof`. -/
def Properties.RequiringChainsKeepAMultiProofVerifier : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (ls : List Label35),
    DisablingNeverEnablesMultiProof P → ProofInv P s → Run35 W P s ls s' → ProofInv P s'

/-- **ONLY ITS WRITER SETS THE REQUIREMENT; ONLY A BREAK-GLASS CUT OF THE CHAIN CHANGES IT
OTHERWISE.** If a step changes a registered chain's `secondProofSystemRequired`, the step is that
chain's `permanentlyRequireSecondProofSystem` and sets it, or a break-glass cut of that chain.
Transitions, the bootstrap crossing, genesis and migration of other chains, CTM writers and
`setProofSystemStatus` leave it alone. -/
def Properties.RequirementWriters : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (l : Label35) (id : ChainId) (c : Chain),
    Step35 W P s l s' → s.sys.chains id = some c →
    (s'.proof id).required ≠ (s.proof id).required →
    (l = .requireSecondProofSystem id ∧ (s'.proof id).required = true) ∨
      ∃ v ρ, l = .routing (.arbitraryCut id v ρ)

/-- **"NO WAY BACK", EXCEPT BY BREAK-GLASS** (`IAdmin.sol:137-140`). Along any v35 run with no
break-glass cut of chain `id`, a registered chain that requires its second proof system still
requires it at the end. -/
def Properties.RequirementIsPermanentWithoutBreakGlass : Prop :=
  ∀ (W : World) (P : ProofWorld) (s s' : Sys35) (ls : List Label35) (id : ChainId) (c : Chain),
    Run35 W P s ls s' → s.sys.chains id = some c → (s.proof id).required = true →
    (∀ v ρ, Label35.routing (.arbitraryCut id v ρ) ∉ ls) → (s'.proof id).required = true

/-! ## Countermodels and witnesses -/

/-- **A PLONK-ONLY ARRIVING VERIFIER STRANDS THE CHAIN THAT REQUIRES ITS SECOND PROOF SYSTEM.** On
`wWorld` with `wProofPlonk`, run `wGateSetup` from `wSys35`: chains `0` and `1` are created at
version 1 on release `100`, chain `0` requires its second proof system, and the CTM commits `300`
(1→2) to release `200`, whose verifier `52` is PLONK-only.
* Every premise of `Contracts.ChainTypeManager.Properties.UpgradesStayEnabled` holds for the
  run's `ChainRouting` image: the start satisfies `SysInv` and `ChainsOnWfReleases`, there is no
  break-glass cut, an edge is committed at chain `0`'s version and release `200` is well-formed.
* Chain `0`'s verifier `51` is in multi-proof mode, so `ProofInv` holds.
* `ChainRouting` lets chain `0` cross the edge, but at v35 it has no transition at all.
* Chain `1`, which does not require the second proof system, crosses. -/
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

/-- **THE CTM OWNER CAN CLEAR THE REQUIREMENT, AND THE STRANDED CHAIN THEN CROSSES.** From the
state of `GateStrandsRequiringChain`, a break-glass cut of chain `0` that keeps its version and
its routing, with an init that turns the requirement off, succeeds. After it chain `0` crosses to
version 2 on release `200`, with the PLONK-only verifier `52` installed. -/
def Properties.BreakGlassClearsTheRequirement : Prop :=
  ∃ s s', Run35 wWorld wProofPlonk wSys35 wGateSetup s ∧ (s.proof 0).required = true ∧
    Step35 wWorld wProofPlonk s (.routing (.arbitraryCut 0 1 (rowsRouting (wRows 100)))) s' ∧
    (s'.proof 0).required = false ∧
    ∃ s'', Step35 wWorld wProofPlonk s' (.routing (.transition 0)) s'' ∧
      (∃ c, s''.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)) ∧
      (s''.proof 0).verifier = 52

/-- **`DisablingNeverEnablesMultiProof` IS NEEDED.** With `wProofOdd`, whose verifier `54` is in
multi-proof mode only with mask `1` disabled: chain `0` is created, its mask is set to `1`, and it
requires its second proof system. `ProofInv` held at the start and fails at the end. -/
def Properties.MaskPremiseNeeded : Prop :=
  ¬ DisablingNeverEnablesMultiProof wProofOdd ∧ ProofInv wProofOdd wSys35 ∧
    ∃ s, Run35 wWorld wProofOdd wSys35
        [.routing (.genesis 0), .setProofSystems 0 1, .requireSecondProofSystem 0] s ∧
      (s.proof 0).required = true ∧ ¬ ProofInv wProofOdd s

/-- **THE v35 PREMISES ARE MET, AND A CHAIN THAT REQUIRES ITS SECOND PROOF SYSTEM UPGRADES.** On
`wWorld` with `wProofMulti` (every release ships a multi-proof verifier), the start `wSys35`
satisfies `SysInv`, `ChainsOnWfReleases`, `RecordedReleasesWf`, `ProofInv` and `NoChainRequires`,
and the verifiers satisfy `DisablingNeverEnablesMultiProof`. Run `wGateRun` (`wGateSetup`, then
transitions of chains `0` and `1`), with no break-glass cut and validated installs. At the end
both chains are at version 2 on release `200`; chain `0` still requires its second proof system,
with release `200`'s verifier `53` installed, which is in multi-proof mode; and `ProofInv`
holds. -/
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

end Contracts.ChainTypeManager.ProofGateAtV35
