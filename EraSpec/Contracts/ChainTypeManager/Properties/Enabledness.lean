import EraSpec.Contracts.ChainTypeManager.Specs.Enabledness

/-!
# Properties: when a chain can upgrade, be deployed, or cross the bootstrap edge

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.Enabledness`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.Enabledness`.

These are liveness results **relative to the model**. Each positive result says no check the
model keeps blocks the step. The checks the model omits (timestamps, batches executed, callers,
facet code, and the rest listed in the spec file) are further premises of any source-level
claim. The negative results need no such premise.

## One step

* **A chain on its release can cross the edge committed at its version** when both releases
  list each selector once (`TransitionEnabled`). The step lands exactly on the arriving
  release's routing at the edge's new version. The premises are about that one chain and the
  CTM: break-glass cuts on other chains are irrelevant.
* **Exactly when** (`TransitionEnabledIff`): a transition exists iff an edge is committed at the
  chain's version, the chain routes its version's release, and the two releases route
  identically (the empty-cut shortcut) or both list each selector once. Once an edge is
  committed, drift (`DriftBlocksTransition`) and a repeated selector are the only obstacles.
* **A free id can be deployed**, by genesis or by migration in, iff the current release lists
  each selector once (`NewChainEnabled`, `NewChainEnabledIff`).
* **A chain at the bootstrap version can cross the bootstrap edge** iff the bootstrap's genesis
  release lists each selector once, whatever the chain routes (`BootstrapResetEnabledIff`).

## What `validate()`'s duplicate check buys

* **A release that lists a selector twice bricks its edge and the CTM's new chains.** If the
  CTM commits a transition to such a release, every chain at the departing version is stuck
  and no chain can be created or migrate in (`DuplicateSelectorBricksEdge`). This is reachable
  from a fresh CTM without a break-glass cut, because the model omits `validate()`. At the
  source, `_setCurrentRelease` and `CTMTransition`'s constructor refuse such a release, which is
  the reason `CTMRelease.sol:125-127` gives.
* **`SysInv` alone does not make the departing release well-formed**
  (`DepartingDuplicateBlocksTransition`): a chain could route an ill-formed release only if it
  started there. No run from a starting state puts it there.

## Along runs

* **Every chain stays on a well-formed release** along runs without a break-glass cut, even if
  the CTM installs an ill-formed release: every way a chain's routing is installed adds a
  release's rows, and an `Add` that repeats a selector reverts (`ChainsStayOnWfReleases`). Every
  starting state meets this premise (`StartingStatesMeetLivenessPremises`).
* **Headline: upgrades stay enabled** (`UpgradesStayEnabled`). Along any run without a
  break-glass cut, every chain whose version has a committed edge can cross it as soon as the
  arriving release lists each selector once. The departing release needs no premise.
* **With validated installs nothing in the model blocks progress**
  (`ValidatedRunsKeepEverythingEnabled`). If additionally every release the CTM installs passes
  the duplicate check, as `_setCurrentRelease` requires, then every committed edge can be crossed
  and every free id deployed. That check is `_requireNoDuplicateSelectors`, proved exact in
  `DuplicateSelectorCheck` (`ReleaseWfIsTheDuplicateCheck`).
* **No chain is left behind, except across an opaque legacy edge** (`BehindChainsCanCatchUp`).
  Under the same premises, every chain behind its CTM can take its transition, or can take the
  bootstrap reset, or sits at a version whose recorded way out is an opaque legacy cut and has
  neither. Crossing an opaque cut is a break-glass step.

Witnesses: `EnablednessWitness` (fresh start: every positive premise met, every step fires)
and `CatchUpWitness` (bootstrap start: all three cases of `BehindChainsCanCatchUp` occur).
-/

namespace Contracts.ChainTypeManager

/-! ## One step -/

/-- **A CHAIN ON ITS RELEASE CAN CROSS THE EDGE COMMITTED AT ITS VERSION.** Suppose the CTM
satisfies its invariant and chain `id` is consistent with it (`ChainOk`: not ahead of the CTM,
routing its version's release). Suppose an edge is committed at the chain's version and both of
its releases list each selector once. Then the transition step exists, and it lands the chain at
the edge's new version routing exactly the arriving release. Nothing is assumed about other
chains. -/
def Properties.TransitionEnabled : Prop :=
  ∀ (W : World) (s : Sys) (id : ChainId) (c : Chain), CtmInv W s.ctm →
    s.chains id = some c → ChainOk W s c → s.ctm.ut c.pv ≠ 0 →
    ReleaseWf W (s.edge W c.pv).fromRel → ReleaseWf W (s.edge W c.pv).newRel →
    Step W s (.transition id) (s.crossEdge W id c)

/-- **EXACTLY WHEN A TRANSITION EXISTS.** Under the CTM's invariant, a registered chain has a
transition step iff all three of these hold:

* an edge is committed at its version;
* it routes exactly its version's release;
* the edge's two releases route identically (the empty-cut shortcut,
  `TransitionDerivationLib.sol:56-58`), or both list each selector once.

So once an edge is committed, drift and a repeated selector are the only things in the model
that block an upgrade. -/
def Properties.TransitionEnabledIff : Prop :=
  ∀ (W : World) (s : Sys) (id : ChainId) (c : Chain), CtmInv W s.ctm → s.chains id = some c →
    ((∃ s', Step W s (.transition id) s') ↔
      s.ctm.ut c.pv ≠ 0 ∧ c.routing = rowsRouting (W.relRows (s.ctm.relAt c.pv)) ∧
      (W.relRows (s.edge W c.pv).fromRel = W.relRows (s.edge W c.pv).newRel ∨
        (ReleaseWf W (s.edge W c.pv).fromRel ∧ ReleaseWf W (s.edge W c.pv).newRel)))

/-- **A FREE ID CAN BE DEPLOYED.** If no diamond is registered for `id` and the CTM's current
release lists each selector once, both `createNewChain` and `forwardedBridgeMint` succeed in
the model. Each deploys a diamond at the CTM's version that routes exactly the current release.
No invariant is needed. -/
def Properties.NewChainEnabled : Prop :=
  ∀ (W : World) (s : Sys) (id : ChainId), s.chains id = none → ReleaseWf W s.ctm.cur →
    Step W s (.genesis id) (s.deployNew W id) ∧ Step W s (.migrateIn id) (s.deployNew W id)

/-- **EXACTLY WHEN A CHAIN CAN BE DEPLOYED.** Genesis, and likewise migration in, exists iff the
id is free and the current release lists each selector once. -/
def Properties.NewChainEnabledIff : Prop :=
  ∀ (W : World) (s : Sys) (id : ChainId),
    ((∃ s', Step W s (.genesis id) s') ↔ s.chains id = none ∧ ReleaseWf W s.ctm.cur) ∧
    ((∃ s', Step W s (.migrateIn id) s') ↔ s.chains id = none ∧ ReleaseWf W s.ctm.cur)

/-- **EXACTLY WHEN A CHAIN CAN CROSS THE BOOTSTRAP EDGE.** Under the CTM's invariant, a
registered chain has a bootstrap-reset step iff the bootstrap cut is recorded at its version for
a genesis release `R` that lists each selector once. What the chain routes does not matter: the
reset removes the whole live routing first (`BootstrapUpgrade.sol:40`). -/
def Properties.BootstrapResetEnabledIff : Prop :=
  ∀ (W : World) (s : Sys) (id : ChainId) (c : Chain), CtmInv W s.ctm → s.chains id = some c →
    ((∃ s', Step W s (.bootstrapReset id) s') ↔
      ∃ R, s.ctm.legacy c.pv = LegacyCut.bootstrap R ∧ ReleaseWf W R)

/-! ## What `validate()`'s duplicate check buys -/

/-- **A DUPLICATE SELECTOR IN THE ARRIVING RELEASE BRICKS THE EDGE AND THE CTM'S NEW CHAINS.**
On `wEnDupWorld`, from the fresh system on the well-formed release `100`, a run with no break-glass
cut creates chain `0` and commits `700` (1→2). Release `260`, where `700` arrives, lists selector
`1` twice. `700` is a genuine transition.

Every premise of `TransitionEnabled`, `UpgradesStayEnabled` and
`ValidatedRunsKeepEverythingEnabled` holds except the arriving release's well-formedness, and
except `InstallsWf` for the commit:

* the start satisfies `SysInv`, `RecordedReleasesWf` and `ChainsOnWfReleases`;
* the end satisfies `SysInv`;
* chain `0` is at version 1 with `700` committed there;
* release `100` lists each selector once.

Yet:

* chain `0` has no transition: the derived `Add` of selector `1` reverts the second time;
* no chain can be created or migrate in: `DiamondInit`'s `Add` of `260`'s rows reverts in the
  same way.

At the source, `_setCurrentRelease` refuses `260` (`ChainTypeManager.sol:310`), and so does the
constructor of any `CTMTransition` arriving there (`CTMTransition.sol:74`). -/
def Properties.DuplicateSelectorBricksEdge : Prop :=
  wEnDupWorld.Genuine 700 ∧ SysInv wEnDupWorld wEnDupSys0 ∧ RecordedReleasesWf wEnDupWorld wEnDupSys0.ctm ∧
    ChainsOnWfReleases wEnDupWorld wEnDupSys0 ∧
    ∃ s, Run wEnDupWorld wEnDupSys0 [.genesis 0, .ctm (.commit 700)] s ∧
      (∀ l ∈ [Label.genesis 0, .ctm (.commit 700)], ¬ l.isArbitrary) ∧ SysInv wEnDupWorld s ∧
      ¬ (Label.ctm (.commit 700)).InstallsWf wEnDupWorld ∧
      (∃ c, s.chains 0 = some c ∧ c.pv = 1 ∧ s.ctm.ut 1 = 700 ∧ ChainOk wEnDupWorld s c ∧
        ReleaseWf wEnDupWorld (s.edge wEnDupWorld 1).fromRel ∧
        ¬ ReleaseWf wEnDupWorld (s.edge wEnDupWorld 1).newRel) ∧
      (¬ ∃ s', Step wEnDupWorld s (.transition 0) s') ∧
      s.chains 1 = none ∧ (¬ ∃ s', Step wEnDupWorld s (.genesis 1) s') ∧
      ¬ ∃ s', Step wEnDupWorld s (.migrateIn 1) s'

/-- **`SysInv` ALONE DOES NOT MAKE THE DEPARTING RELEASE WELL-FORMED.** Take `wDupDepSys`: a CTM
on release `150`, which lists selector `1` twice, with chain `0` routing exactly `150`. It
satisfies `SysInv`. The CTM then commits the genuine transition `800` (1→2) to the well-formed
release `200`, and `SysInv` still holds. Chain `0` is ChainOk with an edge committed at its
version, and the arriving release is well-formed, yet it has no transition: the derived
`Remove` of selector `1` reverts the second time.

So `TransitionEnabled` needs its departing-release premise. `UpgradesStayEnabled` needs
`ChainsOnWfReleases` at its start, and `wDupDepSys` fails it. No run from a starting state gets
here: not even the first chain can be deployed on `150`. -/
def Properties.DepartingDuplicateBlocksTransition : Prop :=
  wEnDupWorld.Genuine 800 ∧ SysInv wEnDupWorld wDupDepSys ∧ ¬ ChainsOnWfReleases wEnDupWorld wDupDepSys ∧
    (∃ s, Run wEnDupWorld wDupDepSys [.ctm (.commit 800)] s ∧ SysInv wEnDupWorld s ∧
      (∃ c, s.chains 0 = some c ∧ c.pv = 1 ∧ s.ctm.ut 1 = 800 ∧ ChainOk wEnDupWorld s c ∧
        ¬ ReleaseWf wEnDupWorld (s.edge wEnDupWorld 1).fromRel ∧
        ReleaseWf wEnDupWorld (s.edge wEnDupWorld 1).newRel) ∧
      ¬ ∃ s', Step wEnDupWorld s (.transition 0) s') ∧
    ¬ ∃ s', Step wEnDupWorld ⟨initState wEnDupWorld 150, fun _ => none⟩ (.genesis 0) s'

/-! ## Along runs -/

/-- **EVERY STARTING STATE MEETS THE LIVENESS PREMISES.** Both starting states satisfy
`DepartedBelow`, `ChainsOnWfReleases` and `ChainsAtDepartedVersions`, and they satisfy
`RecordedReleasesWf` when their release passes the duplicate check:

* a freshly initialized CTM has no chains, and has reached only its own version;
* a just-bootstrapped CTM's pre-registry chains, all at or below the departing version `old`,
  sit at versions with no release, each with a recorded legacy cut: the bootstrap's at `old`,
  opaque ones below it.

The release check is the one `initialize` and the bootstrap's legacy commit run through
`_setCurrentRelease`. -/
def Properties.StartingStatesMeetLivenessPremises : Prop :=
  ∀ (W : World) (R : Address),
    (ReleaseWf W R → RecordedReleasesWf W (initState W R)) ∧
    DepartedBelow (initState W R) ∧ ChainsOnWfReleases W ⟨initState W R, fun _ => none⟩ ∧
    ChainsAtDepartedVersions ⟨initState W R, fun _ => none⟩ ∧
    ∀ (old : ℕ) (chains : ChainId → Option Chain), old < W.relVersion R →
      (∀ id c, chains id = some c → c.pv ≤ old) →
      (ReleaseWf W R → RecordedReleasesWf W (bootstrapState W old R)) ∧
      DepartedBelow (bootstrapState W old R) ∧
      ChainsOnWfReleases W ⟨bootstrapState W old R, chains⟩ ∧
      ChainsAtDepartedVersions ⟨bootstrapState W old R, chains⟩

/-- **EVERY CHAIN STAYS ON A WELL-FORMED RELEASE.** Along any run from an invariant state whose
chains are on well-formed releases, with no break-glass cut, every chain at a version with a
release is still on a well-formed one, even if the CTM installs an ill-formed release on the way.
Each way a chain's routing is installed (genesis, migration in, the bootstrap reset, a
transition that changes the routing) adds a release's rows, and an `Add` that lists a selector
twice reverts. -/
def Properties.ChainsStayOnWfReleases : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label), SysInv W s → ChainsOnWfReleases W s →
    Run W s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) → ChainsOnWfReleases W s'

/-- **HEADLINE (LIVENESS): UPGRADES STAY ENABLED.** Along any run from an invariant state whose
chains are on well-formed releases, with no break-glass cut, the following holds at the end.
Every chain whose version has a committed edge can cross it, landing on the arriving release at
the edge's new version, provided that arriving release lists each selector once. Nothing is
assumed about the departing release: on such runs it is well-formed already
(`ChainsStayOnWfReleases`). -/
def Properties.UpgradesStayEnabled : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label), SysInv W s → ChainsOnWfReleases W s →
    Run W s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.chains id = some c → s'.ctm.ut c.pv ≠ 0 → ReleaseWf W (s'.edge W c.pv).newRel →
      Step W s' (.transition id) (s'.crossEdge W id c)

/-- **WITH VALIDATED INSTALLS, NOTHING IN THE MODEL BLOCKS AN UPGRADE OR A NEW CHAIN.** Take a run
with no break-glass cut, from an invariant state whose installed releases list each selector
once, in which every release the CTM installs passes the same check (as `_setCurrentRelease`
requires at the source). At the end of it:

* every chain whose version has a committed edge can cross it;
* every free id can be deployed, by genesis or by migration in. -/
def Properties.ValidatedRunsKeepEverythingEnabled : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label), SysInv W s → RecordedReleasesWf W s.ctm →
    Run W s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) → (∀ l ∈ ls, l.InstallsWf W) →
    (∀ id c, s'.chains id = some c → s'.ctm.ut c.pv ≠ 0 →
      Step W s' (.transition id) (s'.crossEdge W id c)) ∧
    (∀ id, s'.chains id = none →
      Step W s' (.genesis id) (s'.deployNew W id) ∧ Step W s' (.migrateIn id) (s'.deployNew W id))

/-- **NO CHAIN IS LEFT BEHIND, EXCEPT ACROSS AN OPAQUE LEGACY EDGE.** Under the premises of
`ValidatedRunsKeepEverythingEnabled`, plus `DepartedBelow` and `ChainsAtDepartedVersions` at the
start (which every starting state meets), every chain behind its CTM at the end is in one of
three cases:

* it can take the transition committed at its version, landing on the arriving release;
* the bootstrap cut is recorded at its version and the bootstrap reset is enabled;
* the cut recorded at its version is an opaque legacy cut, and the chain has neither a
  transition nor a bootstrap reset.

In the third case the only step that moves the chain is a break-glass cut
(`Label.arbitraryCut`, which is how the model crosses an opaque legacy edge): genesis and
migration in need a free id, and `OnlyUpgradesAndCutsWriteADiamond` lists the rest. -/
def Properties.BehindChainsCanCatchUp : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label), SysInv W s → RecordedReleasesWf W s.ctm →
    DepartedBelow s.ctm → ChainsAtDepartedVersions s →
    Run W s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) → (∀ l ∈ ls, l.InstallsWf W) →
    ∀ id c, s'.chains id = some c → c.pv < s'.ctm.pv →
      Step W s' (.transition id) (s'.crossEdge W id c) ∨
      (∃ R, s'.ctm.legacy c.pv = LegacyCut.bootstrap R ∧
        ∃ s'', Step W s' (.bootstrapReset id) s'') ∨
      (s'.ctm.legacy c.pv = LegacyCut.opaque ∧ (¬ ∃ s'', Step W s' (.transition id) s'') ∧
        ¬ ∃ s'', Step W s' (.bootstrapReset id) s'')

/-! ## Witnesses -/

/-- **THE ONE-STEP AND RUN PREMISES ARE MET, AND EVERY STEP FIRES.** From the fresh witness
system on release `100`, a validated run with no break-glass cut creates chain `0` and commits
`300` (1→2). The start satisfies `SysInv`, `RecordedReleasesWf` and `ChainsOnWfReleases`. At the
end:

* chain `0` is ChainOk at version 1 with `300` committed there, both releases are well-formed and
  route differently, and the transition fires, so it is a real reinstall;
* chain `1` is free, the current release `200` is well-formed, and both genesis and migration in
  fire. -/
def Properties.EnablednessWitness : Prop :=
  SysInv wWorld wSys0 ∧ RecordedReleasesWf wWorld wSys0.ctm ∧ ChainsOnWfReleases wWorld wSys0 ∧
    ∃ s, Run wWorld wSys0 [.genesis 0, .ctm (.commit 300)] s ∧
      (∀ l ∈ [Label.genesis 0, .ctm (.commit 300)], ¬ l.isArbitrary ∧ l.InstallsWf wWorld) ∧
      SysInv wWorld s ∧
      (∃ c, s.chains 0 = some c ∧ c.pv = 1 ∧ ChainOk wWorld s c ∧ s.ctm.ut c.pv ≠ 0 ∧
        ReleaseWf wWorld (s.edge wWorld c.pv).fromRel ∧
        ReleaseWf wWorld (s.edge wWorld c.pv).newRel ∧
        wWorld.relRows (s.edge wWorld c.pv).fromRel ≠ wWorld.relRows (s.edge wWorld c.pv).newRel ∧
        Step wWorld s (.transition 0) (s.crossEdge wWorld 0 c)) ∧
      s.chains 1 = none ∧ ReleaseWf wWorld s.ctm.cur ∧
      Step wWorld s (.genesis 1) (s.deployNew wWorld 1) ∧
      Step wWorld s (.migrateIn 1) (s.deployNew wWorld 1)

/-- **ALL THREE CASES OF `BehindChainsCanCatchUp` OCCUR.** The start is `wLagSys`, the
just-bootstrapped system at version 2 on release `200`, with pre-registry chains `5` (version 0)
and `6` (version 1). It meets the premises of `StartingStatesMeetLivenessPremises` (release `200`
is well-formed, `1 < 2`, both chains at or below version 1), and hence those of
`BehindChainsCanCatchUp`. A validated run with no break-glass cut creates chain `0` and commits
`600` (2→3). At the end the CTM is at version 3, and:

* chain `0`, at version 2, can take transition `600`;
* chain `6`, at version 1, can take the bootstrap reset onto release `200`;
* chain `5`, at version 0, is behind an opaque legacy cut, with neither a transition nor a
  bootstrap reset. -/
def Properties.CatchUpWitness : Prop :=
  ReleaseWf wWorld 200 ∧ 1 < wWorld.relVersion 200 ∧
    (∀ id c, wLagSys.chains id = some c → c.pv ≤ 1) ∧ wLagSys.ctm = bootstrapState wWorld 1 200 ∧
    SysInv wWorld wLagSys ∧ RecordedReleasesWf wWorld wLagSys.ctm ∧ DepartedBelow wLagSys.ctm ∧
    ChainsAtDepartedVersions wLagSys ∧
    ∃ s, Run wWorld wLagSys [.genesis 0, .ctm (.commit 600)] s ∧
      (∀ l ∈ [Label.genesis 0, .ctm (.commit 600)], ¬ l.isArbitrary ∧ l.InstallsWf wWorld) ∧
      s.ctm.pv = 3 ∧
      (∃ c, s.chains 0 = some c ∧ c.pv = 2 ∧
        Step wWorld s (.transition 0) (s.crossEdge wWorld 0 c)) ∧
      (∃ c, s.chains 6 = some c ∧ c.pv = 1 ∧ s.ctm.legacy 1 = LegacyCut.bootstrap 200 ∧
        ∃ s', Step wWorld s (.bootstrapReset 6) s') ∧
      (∃ c, s.chains 5 = some c ∧ c.pv = 0 ∧ s.ctm.legacy 0 = LegacyCut.opaque ∧
        (¬ ∃ s', Step wWorld s (.transition 5) s') ∧
        ¬ ∃ s', Step wWorld s (.bootstrapReset 5) s')

end Contracts.ChainTypeManager
