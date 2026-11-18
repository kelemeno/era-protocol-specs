import EraSpec.Contracts.ChainTypeManager.Specs.MutableSelectors

/-!
# Properties: the routing headline needs stable `selectors()` answers

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.MutableSelectors`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.MutableSelectors`. Namespace
`Contracts.ChainTypeManager.MutableSelectors`.

## With stable answers

* **The model refines `LiveRouting`** (`StableRunIsACountedRun`). Under `StableSelectors M σ` a
  run is a `LiveRouting` run of the world whose facets answer `σ`, and the answers are still `σ`
  at the end. No invariant is needed: the guards are the same, and the stored cuts are the
  derived ones. Conversely, every `LiveRouting` run is such a run (`CountedRunIsAStableRun`).
* **Headline** (`ChainsRunTheirVersionsReleaseStable`). Take a run from an invariant state, with no
  break-glass cut, under `StableSelectors`. Every chain at a version `v` with a release `R_v`
  routes exactly `R_v`'s rows with the selectors `σ` gives them, and passes the count check
  against `R_v` as the facets answer at the end. On a fresh CTM every chain has such a release
  (`FreshChainsRunTheirVersionsReleaseStable`).
* **The base headline's world** (`StableRunIsARoutingRun`). The routing view of such a run is a
  `ChainRouting` run of `(M.at σ).toWorld`, whose `relRows R` is `flattenRows σ (genesisFacets R)`,
  so `ChainsRunTheirVersionsRelease` applies with that world.
* **Only the transitions a run can cross matter** (`StableSelectorsOn`). `StableSelectors` asks
  every address for cuts derived under `σ`. The refinement and the headline need that only of the
  transitions in a slot at the start and of those the run commits or installs as a replacement
  (`StableOnRunIsACountedRun`, `ChainsRunTheirVersionsReleaseStableOn`); the first premise implies
  the second (`StableSelectorsIsStableOn`).
* Witnesses: `StableSelectorsWitness` (`LiveRouting`'s witness run: it creates chains and crosses
  an edge) and `StableSelectorsOnWitness` (a run that meets the weaker premise in a world where the
  stronger one fails for every `σ`).

## How the two installing paths read the answers

* **A crossing installs the answers from when the transition was built**
  (`CrossingInstallsTheBuildAnswers`): from a diamond routing the departing release with the
  answers `σ` the transition was built under, the stored cuts land on the arriving release with
  the same `σ`, whatever the facets answer when the chain crosses.
* **What the guard does establish** (`UnchangedDepartingAnswersLandOnRelease`): on consistent
  diamond storage, with the departing release's rows well-formed under the answers now, and the
  departing release's facets answering as they did when the transition was built, a crossing
  lands on the arriving release with the build answers. Nothing is asked of the arriving release's
  facets. `MutableSelectorsLeaveDepartingFacetRouted` shows the last premise is needed.
* **A new chain gets the answers now** (`CreationInstallsTheAnswersNow`): genesis and migration in
  install the current release with the answers when they run.
* `InstallsReadDifferentAnswersWitness` meets the premises of all three at two consecutive
  states, while the facets answer the arriving release's facet differently from when the
  transition was built.

## Without them

All on `LiveRouting`'s witness world with genuine objects: every transition stored the cuts its
constructor derives, and every release passes `validate()`'s facet checks both before and after
the change.

* **One change splits a release's routing** (`MutableSelectorsSplitRouting`). Chain `0` is created
  on release `100`, and the CTM commits `300` (1→2), while facet `21` answers `[1, 2]`. Facet `21`
  then answers `[1, 3]`. Chain `0` crosses with `300`'s stored cuts and routes `[1, 2]`. Chain `1`,
  created afterwards, routes `[1, 3]`. Both are at version 2, whose release is `200`. No
  `ChainRouting` world reaches that state along a run without break-glass cut from an invariant
  state, and no `LiveRouting` world does either. Of `StableSelectors`, only the `constant` field
  fails (`MutableSelectorsSplitRoutingOnlyConstantFails`, in the Proofs file).
* **The guard reads the answers now** (`CrossingNeedsTheAnswersNow`). A chain whose diamond fails
  the count check against its version's release, as the facets answer now, cannot cross. That
  holds whatever transition is committed at its version, whenever it was built.
* **So the next edge refuses the chain that crossed with the old answers**
  (`MutableSelectorsBlockNextEdge`). After the split, the CTM commits `600` (2→3), built after the
  change. Chain `1` can cross. Chain `0` fails the count check and cannot.
* **Stable during the run is not enough** (`StaleCutsSplitRouting`). Let facet `21` answer `[1, 3]`
  from the start, with no change during the run. The same split happens, because `300` was built
  while facet `21` answered `[1, 2]`. `StableSelectors` fails for every `σ`: the answers must also
  be the ones every transition was built under.
* **A change of the departing release's facet leaves that facet routed**
  (`MutableSelectorsLeaveDepartingFacetRouted`). Facet `11`, release `100`'s, starts answering
  `[1, 2, 5]`; a chain created on release `100` afterwards routes all three. Before it crosses,
  every premise of `UnchangedDepartingAnswersLandOnRelease` but the last holds. It passes the
  guard and crosses `300`, whose stored `Remove` names only `[1, 2]`. At version 2 it still routes
  selector `5` to facet `11`, which release `200` does not list: its routing is release `200`'s
  under no answers, no `LiveRouting` run of these objects reaches it from an invariant state
  without break-glass cut, and it fails the count check against release `200` under every answer
  set.
-/

namespace Contracts.ChainTypeManager.MutableSelectors

/-! ## With stable answers -/

/-- **UNDER STABLE ANSWERS, A RUN IS A `LiveRouting` RUN.** Under `StableSelectors M σ`, a run of
this model is a run of `LiveRouting`'s system in the world whose facets answer `σ`, with the
run's labels unwrapped (`MutLabel.toDLabels`; under the premise no label is an answer change), and
the answers are still `σ` at the end. -/
def Properties.StableRunIsACountedRun : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s s' : MutSys) (ls : List MutLabel),
    StableSelectors M σ s ls → MutRun M s ls s' →
    DRun (M.at σ) s.sys (MutLabel.toDLabels ls) s'.sys ∧ s'.sel = σ

/-- **EVERY `LiveRouting` RUN IS A STABLE RUN.** With each transition's cuts stored as derived under
the world's answers (`MutWorld.ofDWorld`), a `LiveRouting` run is a run of this model, with the
same labels and no answer change, and it meets `StableSelectors`. Read with the world's answers,
the lifted objects are the world itself. `LiveRouting`'s `CountedRoutingWitness` supplies a run
that creates chains and crosses an edge. -/
def Properties.CountedRunIsAStableRun : Prop :=
  ∀ (D : DWorld) (s s' : DSys) (ls : List DLabel), DRun D s ls s' →
    MutRun (MutWorld.ofDWorld D) ⟨s, D.selectors⟩ (ls.map MutLabel.sys) ⟨s', D.selectors⟩ ∧
    StableSelectors (MutWorld.ofDWorld D) D.selectors ⟨s, D.selectors⟩ (ls.map MutLabel.sys) ∧
    (MutWorld.ofDWorld D).at D.selectors = D

/-- **HEADLINE: UNDER STABLE ANSWERS, EVERY CHAIN AT VERSION `v` HAS EXACTLY `R_v`'S ROUTING.**
Along any run from an invariant state (`DSysInv` in the world whose facets answer `σ`) that uses no
break-glass cut, if every facet answers `σ` throughout and every transition was built under `σ`
(`StableSelectors`), then every chain at a version `v` for which the CTM has a release `R_v`:
* `R_v` is a release of version `v`;
* the chain's proxy routes exactly `R_v`'s rows with the selectors `σ` gives them;
* the chain passes the count check of `requireReleaseRouting(R_v)` as the facets answer at the
  end;
* its diamond storage is consistent (`DiamondOk`).

`StableSelectorsWitness` meets every premise. -/
def Properties.ChainsRunTheirVersionsReleaseStable : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s s' : MutSys) (ls : List MutLabel),
    StableSelectors M σ s ls → DSysInv (M.at σ) s.sys → MutRun M s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      M.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.ds.routing = rowsRouting (flattenRows σ (M.genesisFacets (s'.sys.ctm.relAt c.pv))) ∧
      CountCheck s'.sel c.ds (M.genesisFacets (s'.sys.ctm.relAt c.pv)) ∧ DiamondOk c.ds

/-- **ON A FRESHLY INITIALIZED CTM, UNDER STABLE ANSWERS, EVERY CHAIN HAS ITS VERSION'S RELEASE.**
The CTM starts as `initialize(R)` leaves it, with no chains, and `R` passes `validate()`'s facet
checks under `σ`. Along a run with no break-glass cut under `StableSelectors`, every chain's
version has a nonzero release `R_v`, which is a release of that version; the chain routes `R_v`'s
rows with the selectors `σ` gives them and passes the count check against `R_v` as the facets
answer at the end. `StableSelectorsWitness` meets every premise. -/
def Properties.FreshChainsRunTheirVersionsReleaseStable : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (R : Address) (s' : MutSys) (ls : List MutLabel),
    R ≠ 0 → ReleaseValid (M.at σ) R →
    StableSelectors M σ ⟨⟨initState (M.at σ).toWorld R, fun _ => none⟩, σ⟩ ls →
    MutRun M ⟨⟨initState (M.at σ).toWorld R, fun _ => none⟩, σ⟩ ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.sys.chains id = some c →
      s'.sys.ctm.relAt c.pv ≠ 0 ∧ M.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.ds.routing = rowsRouting (flattenRows σ (M.genesisFacets (s'.sys.ctm.relAt c.pv))) ∧
      CountCheck s'.sel c.ds (M.genesisFacets (s'.sys.ctm.relAt c.pv))

/-- **UNDER STABLE ANSWERS, THE BASE HEADLINE APPLIES WITH ONE FIXED WORLD.** For a run as in the
headline, the start's routing view satisfies `ChainRouting`'s invariant, and the run's routing
view is a `ChainRouting` run with no break-glass cut of the world `(M.at σ).toWorld`, whose
`relRows R` is `R`'s rows flattened with the selectors `σ` gives them. So
`ChainsRunTheirVersionsRelease` holds of it with that `World`. -/
def Properties.StableRunIsARoutingRun : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s s' : MutSys) (ls : List MutLabel),
    StableSelectors M σ s ls → DSysInv (M.at σ) s.sys → MutRun M s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) →
    SysInv (M.at σ).toWorld s.sys.view ∧
      Run (M.at σ).toWorld s.sys.view ((MutLabel.toDLabels ls).map DLabel.view) s'.sys.view ∧
      (∀ l ∈ (MutLabel.toDLabels ls).map DLabel.view, ¬ l.isArbitrary) ∧
      ∀ R, (M.at σ).toWorld.relRows R = flattenRows σ (M.genesisFacets R)

/-- **`StableSelectors` IS THE SPECIAL CASE OF `StableSelectorsOn` THAT CONSTRAINS EVERY ADDRESS.**
`StableSelectorsWitness` meets the premise; `StableSelectorsOnWitness` shows the converse fails. -/
def Properties.StableSelectorsIsStableOn : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s : MutSys) (ls : List MutLabel),
    StableSelectors M σ s ls → StableSelectorsOn M σ s ls

/-- **THE REFINEMENT NEEDS STABLE CUTS ONLY FOR THE TRANSITIONS THE RUN CAN CROSS.**
`StableRunIsACountedRun` under `StableSelectorsOn`: no step changes an answer, and the transitions
in a slot at the start, committed by the run, or installed by it as a replacement stored the cuts
derived under `σ`. Nothing is asked of any other transition object. `StableSelectorsOnWitness`
meets every premise. -/
def Properties.StableOnRunIsACountedRun : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s s' : MutSys) (ls : List MutLabel),
    StableSelectorsOn M σ s ls → MutRun M s ls s' →
    DRun (M.at σ) s.sys (MutLabel.toDLabels ls) s'.sys ∧ s'.sel = σ

/-- **HEADLINE, WITH THE PREMISE ONLY ON THE TRANSITIONS THE RUN CAN CROSS.**
`ChainsRunTheirVersionsReleaseStable` with `StableSelectorsOn` in place of `StableSelectors`; the
conclusion is the same. `StableSelectorsOnWitness` meets every premise. -/
def Properties.ChainsRunTheirVersionsReleaseStableOn : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s s' : MutSys) (ls : List MutLabel),
    StableSelectorsOn M σ s ls → DSysInv (M.at σ) s.sys → MutRun M s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      M.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.ds.routing = rowsRouting (flattenRows σ (M.genesisFacets (s'.sys.ctm.relAt c.pv))) ∧
      CountCheck s'.sel c.ds (M.genesisFacets (s'.sys.ctm.relAt c.pv)) ∧ DiamondOk c.ds

/-- **THE STABLE HEADLINE IS NOT VACUOUS.** `LiveRouting`'s witness run (`CountedRoutingWitness`) in
this model: on `wDWorld` with every transition built under its answers, the CTM starts as
`initialize(100)` leaves it, and release `100` passes `validate()`'s facet checks. The run creates
chain `0` at version 1, commits `300` (1→2), upgrades chain `0` and creates chain `1`; no answer
changes and there is no break-glass cut. The run meets `StableSelectors` and starts from an
invariant state. Both chains end at version 2, whose release is `200`, routing release `200`,
which differs from release `100`. -/
def Properties.StableSelectorsWitness : Prop :=
  mutSys0 = ⟨⟨initState (mutWorld.at mutSelA).toWorld 100, fun _ => none⟩, mutSelA⟩ ∧
    (100 : Address) ≠ 0 ∧ ReleaseValid (mutWorld.at mutSelA) 100 ∧
    StableSelectors mutWorld mutSelA mutSys0
      [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)] ∧
    DSysInv (mutWorld.at mutSelA) mutSys0.sys ∧
    (∀ l ∈ ([.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0),
      .sys (.genesis 1)] : List MutLabel), ¬ l.isArbitrary) ∧
    ∃ s, MutRun mutWorld mutSys0
        [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)] s ∧
      s.sys.ctm.relAt 2 = 200 ∧
      ∃ c₀ c₁, s.sys.chains 0 = some c₀ ∧ s.sys.chains 1 = some c₁ ∧ c₀.pv = 2 ∧ c₁.pv = 2 ∧
        c₀.ds.routing = rowsRouting (wRows 200) ∧ c₁.ds.routing = rowsRouting (wRows 200) ∧
        rowsRouting (wRows 200) ≠ rowsRouting (wRows 100)

/-- **THE WEAKER PREMISE IS MET WHERE THE STRONGER ONE CANNOT BE.** In `mutLateWorld`, transition
`300` stored the cuts derived while facet `21` answered `[1, 2]`, and `600` those derived while it
answered `[1, 3]`. The run starts from an invariant state with the facets answering `mutSelA`:
create chain `0`, commit `300` (1→2), upgrade chain `0`, create chain `1`. No answer changes,
there is no break-glass cut, and `600` is never committed. The run meets `StableSelectorsOn` with
`mutSelA`; it meets `StableSelectors` with no `σ`, because `600` was not built under `mutSelA`.
Both chains end at version 2, whose release is `200`, routing release `200`, which differs from
release `100`. -/
def Properties.StableSelectorsOnWitness : Prop :=
  StableSelectorsOn mutLateWorld mutSelA mutSys0
      [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)] ∧
    ¬ mutLateWorld.FrozenUnder mutSelA 600 ∧
    (∀ σ, ¬ StableSelectors mutLateWorld σ mutSys0
      [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)]) ∧
    DSysInv (mutLateWorld.at mutSelA) mutSys0.sys ∧
    (∀ l ∈ ([.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0),
      .sys (.genesis 1)] : List MutLabel), ¬ l.isArbitrary) ∧
    ∃ s, MutRun mutLateWorld mutSys0
        [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)] s ∧
      s.sys.ctm.relAt 2 = 200 ∧
      ∃ c₀ c₁, s.sys.chains 0 = some c₀ ∧ s.sys.chains 1 = some c₁ ∧ c₀.pv = 2 ∧ c₁.pv = 2 ∧
        c₀.ds.routing = rowsRouting (wRows 200) ∧ c₁.ds.routing = rowsRouting (wRows 200) ∧
        rowsRouting (wRows 200) ≠ rowsRouting (wRows 100)

/-! ## How the two installing paths read the answers -/

/-- **A CROSSING INSTALLS THE ARRIVING RELEASE AS ITS FACETS ANSWERED WHEN THE TRANSITION WAS
BUILT.** Suppose the transition committed at a chain's version stored the cuts derived under the
answers `σ`, and the chain routes the departing release's rows with the selectors `σ` gives them.
If the chain crosses, it lands at the transition's new version, routing the arriving release's rows
with the selectors `σ` gives them. The answers when it crosses (`s.sel`) are not constrained,
beyond what the crossing's own guard requires. `InstallsReadDifferentAnswersWitness` meets every
premise with `s.sel` differing from `σ` on the arriving release's facet. -/
def Properties.CrossingInstallsTheBuildAnswers : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s s' : MutSys) (id : ChainId) (c : DChain),
    s.sys.chains id = some c → M.FrozenUnder σ (s.sys.ctm.ut c.pv) →
    c.ds.routing =
      rowsRouting (flattenRows σ (M.genesisFacets (M.tr (s.sys.ctm.ut c.pv)).fromRel)) →
    MutStep M s (.sys (.transition id)) s' →
    ∃ c', s'.sys.chains id = some c' ∧ c'.pv = (M.tr (s.sys.ctm.ut c.pv)).new ∧
      c'.ds.routing =
        rowsRouting (flattenRows σ (M.genesisFacets (M.tr (s.sys.ctm.ut c.pv)).newRel))

/-- **A CROSSING LANDS ON THE ARRIVING RELEASE AS BUILT, IF THE DEPARTING RELEASE'S FACETS STILL
ANSWER AS THEY DID.** Suppose the transition committed at a chain's version stored the cuts derived
under the answers `σ`; the chain's diamond storage is consistent (`DiamondOk`); the departing
release's rows pass `validate()`'s selector checks under the answers now (`RowsWf`); and the
departing release's rows flatten the same under the answers now as under `σ`. If the chain
crosses, it lands at the transition's new version, routing the arriving release's rows with the
selectors `σ` gives them. Nothing is asked of the arriving release's facets.
`InstallsReadDifferentAnswersWitness` meets every premise with the arriving release's facet
answering differently; `MutableSelectorsLeaveDepartingFacetRouted` meets every premise but the
last, and its chain lands on the arriving release under no answers. -/
def Properties.UnchangedDepartingAnswersLandOnRelease : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s s' : MutSys) (id : ChainId) (c : DChain),
    s.sys.chains id = some c → M.FrozenUnder σ (s.sys.ctm.ut c.pv) → DiamondOk c.ds →
    RowsWf s.sel (M.genesisFacets (M.tr (s.sys.ctm.ut c.pv)).fromRel) →
    flattenRows s.sel (M.genesisFacets (M.tr (s.sys.ctm.ut c.pv)).fromRel) =
      flattenRows σ (M.genesisFacets (M.tr (s.sys.ctm.ut c.pv)).fromRel) →
    MutStep M s (.sys (.transition id)) s' →
    ∃ c', s'.sys.chains id = some c' ∧ c'.pv = (M.tr (s.sys.ctm.ut c.pv)).new ∧
      c'.ds.routing =
        rowsRouting (flattenRows σ (M.genesisFacets (M.tr (s.sys.ctm.ut c.pv)).newRel))

/-- **A NEW CHAIN GETS THE CURRENT RELEASE AS ITS FACETS ANSWER NOW.** After a genesis or a
migration in, the chain is at the CTM's version and routes the current release's rows with the
selectors the facets give when the step runs. `InstallsReadDifferentAnswersWitness` meets the
premise. -/
def Properties.CreationInstallsTheAnswersNow : Prop :=
  ∀ (M : MutWorld) (s s' : MutSys) (id : ChainId),
    (MutStep M s (.sys (.genesis id)) s' ∨ MutStep M s (.sys (.migrateIn id)) s') →
    ∃ c', s'.sys.chains id = some c' ∧ c'.pv = s.sys.ctm.pv ∧
      c'.ds.routing = rowsRouting (flattenRows s.sel (M.genesisFacets s.sys.ctm.cur))

/-- **BOTH INSTALLING PATHS RUN WHILE THE ANSWERS DIFFER FROM THE BUILD ANSWERS.** In `mutWorld`,
from the invariant state `mutSys0`, the run "create chain `0`, commit `300`, facet `21` starts
answering `[1, 3]`" reaches a state where:
* chain `0` is at version 1, on consistent diamond storage;
* the transition committed at version 1 stored the cuts derived under `mutSelA`, and lands on
  release `200`;
* chain `0` routes that transition's departing release's rows with the selectors `mutSelA` gives
  them; those rows are well-formed under the answers now and flatten the same as under `mutSelA`;
* the facets answer `mutSelB`, and chain `0` crosses.

In the next state the facets still answer `mutSelB`, the current release is `200`, and chain `1`
is created. The two answer sets flatten release `200`'s rows differently. -/
def Properties.InstallsReadDifferentAnswersWitness : Prop :=
  DSysInv (mutWorld.at mutSelA) mutSys0.sys ∧
    ∃ s₃ s₄ s₅ : MutSys,
      MutRun mutWorld mutSys0
        [.sys (.genesis 0), .sys (.ctm (.commit 300)), .setSelectors 21 [1, 3]] s₃ ∧
      (∃ c, s₃.sys.chains 0 = some c ∧ c.pv = 1 ∧
        mutWorld.FrozenUnder mutSelA (s₃.sys.ctm.ut c.pv) ∧
        c.ds.routing = rowsRouting
          (flattenRows mutSelA (mutWorld.genesisFacets (mutWorld.tr (s₃.sys.ctm.ut c.pv)).fromRel)) ∧
        DiamondOk c.ds ∧
        RowsWf s₃.sel (mutWorld.genesisFacets (mutWorld.tr (s₃.sys.ctm.ut c.pv)).fromRel) ∧
        flattenRows s₃.sel (mutWorld.genesisFacets (mutWorld.tr (s₃.sys.ctm.ut c.pv)).fromRel) =
          flattenRows mutSelA (mutWorld.genesisFacets (mutWorld.tr (s₃.sys.ctm.ut c.pv)).fromRel) ∧
        (mutWorld.tr (s₃.sys.ctm.ut c.pv)).newRel = 200) ∧
      s₃.sel = mutSelB ∧ MutStep mutWorld s₃ (.sys (.transition 0)) s₄ ∧
      s₄.sel = mutSelB ∧ MutStep mutWorld s₄ (.sys (.genesis 1)) s₅ ∧ s₄.sys.ctm.cur = 200 ∧
      flattenRows mutSelA (mutWorld.genesisFacets 200) ≠
        flattenRows mutSelB (mutWorld.genesisFacets 200)

/-! ## Without stable answers -/

/-- **COUNTERMODEL: ONE CHANGED ANSWER SPLITS A RELEASE'S ROUTING, WITH GENUINE OBJECTS.**

The objects:
* every transition stored the cuts its constructor derives under the starting answers `mutSelA`;
* `300` meets everything `CTMTransition`'s constructor establishes under them
  (`GenuineUnder`), with stored cuts `Remove [1, 2]` then `Add 21 [1, 2]`;
* every address passes `validate()`'s facet checks under both answer sets (releases `100`, `200`,
  `250` list one facet each; every other address lists none);
* the two answer sets differ only in facet `21`'s list.

The run starts from an invariant state with the facets answering `mutSelA`. It creates chain `0`
on release `100` and commits `300` (1→2). Facet `21` then starts answering `[1, 3]`. Chain `0`
crosses, and chain `1` is created. There is no break-glass cut.

At the end both chains are at version 2, whose release is `200`. Chain `0` routes release `200`'s
rows with the old answers; chain `1` routes them with the new ones. So no `ChainRouting` world
reaches the final state's routing view along a run without break-glass cut from an invariant
state, and no `LiveRouting` world reaches the final state that way. -/
def Properties.MutableSelectorsSplitRouting : Prop :=
  (∀ t, mutWorld.FrozenUnder mutSelA t) ∧ mutWorld.GenuineUnder mutSelA 300 ∧
    mutWorld.cuts 300 = [⟨0, .remove, false, [1, 2]⟩, ⟨21, .add, false, [1, 2]⟩] ∧
    (∀ R, ReleaseValid (mutWorld.at mutSelA) R ∧ ReleaseValid (mutWorld.at mutSelB) R) ∧
    (∀ f, f ≠ 21 → mutSelB f = mutSelA f) ∧ mutSelA 21 = [1, 2] ∧ mutSelB 21 = [1, 3] ∧
    DSysInv (mutWorld.at mutSelA) mutSys0.sys ∧ mutSys0.sel = mutSelA ∧
    ∃ s, MutRun mutWorld mutSys0
        [.sys (.genesis 0), .sys (.ctm (.commit 300)), .setSelectors 21 [1, 3],
          .sys (.transition 0), .sys (.genesis 1)] s ∧
      s.sel = mutSelB ∧ s.sys.ctm.relAt 2 = 200 ∧
      (∃ c₀ c₁, s.sys.chains 0 = some c₀ ∧ s.sys.chains 1 = some c₁ ∧ c₀.pv = 2 ∧ c₁.pv = 2 ∧
        c₀.ds.routing = rowsRouting (flattenRows mutSelA (mutWorld.genesisFacets 200)) ∧
        c₁.ds.routing = rowsRouting (flattenRows mutSelB (mutWorld.genesisFacets 200)) ∧
        c₀.ds.routing ≠ c₁.ds.routing) ∧
      (¬ ∃ (W : World) (s₀ : Sys) (ls : List Label), SysInv W s₀ ∧ Run W s₀ ls s.sys.view ∧
        ∀ l ∈ ls, ¬ l.isArbitrary) ∧
      ¬ ∃ (D : DWorld) (s₀ : DSys) (ls : List DLabel), DSysInv D s₀ ∧ DRun D s₀ ls s.sys ∧
        ∀ l ∈ ls, ¬ l.isArbitrary

/-- **A CROSSING NEEDS THE ROUTING THE FACETS DESCRIBE NOW.** Suppose the CTM satisfies `CtmInv`
and a chain's diamond fails the count check against its version's release, as the facets answer
now. Then the chain has no crossing, whatever transition is committed at its version and whatever
cuts that transition stored: the guard re-reads `selectors()`. `MutableSelectorsBlockNextEdge`
meets every premise (chain `0` there). -/
def Properties.CrossingNeedsTheAnswersNow : Prop :=
  ∀ (M : MutWorld) (s : MutSys) (id : ChainId) (c : DChain),
    CtmInv (M.at s.sel).toWorld s.sys.ctm → s.sys.chains id = some c →
    ¬ CountCheck s.sel c.ds (M.genesisFacets (s.sys.ctm.relAt c.pv)) →
    ¬ ∃ s', MutStep M s (.sys (.transition id)) s'

/-- **COUNTERMODEL: THE NEXT EDGE REFUSES THE CHAIN THAT CROSSED WITH THE OLD ANSWERS.** In
`mutLateWorld`, transition `600` (2→3, release `200` to `250`) meets everything `CTMTransition`'s
constructor establishes while facet `21` answers `[1, 3]`, and `300` everything it establishes
while facet `21` answers `[1, 2]`. From `mutSys0`, run the labels of
`MutableSelectorsSplitRouting`'s run (`mutLateWorld` differs from `mutWorld` only in `600`'s
cuts), then commit `600`. The CTM then satisfies `CtmInv`, slot 2 holds `600`, and version 2's
release is `200`. Chain `0`, at version 2, fails the count check against release `200` as the
facets answer now, and has no crossing. Chain `1`, at version 2, passes it, crosses, and lands at
version 3. -/
def Properties.MutableSelectorsBlockNextEdge : Prop :=
  mutLateWorld.GenuineUnder mutSelB 600 ∧ mutLateWorld.GenuineUnder mutSelA 300 ∧
    ∃ s, MutRun mutLateWorld mutSys0
        [.sys (.genesis 0), .sys (.ctm (.commit 300)), .setSelectors 21 [1, 3],
          .sys (.transition 0), .sys (.genesis 1), .sys (.ctm (.commit 600))] s ∧
      CtmInv (mutLateWorld.at s.sel).toWorld s.sys.ctm ∧
      s.sys.ctm.ut 2 = 600 ∧ s.sys.ctm.relAt 2 = 200 ∧
      (∃ c₀, s.sys.chains 0 = some c₀ ∧ c₀.pv = 2 ∧
        ¬ CountCheck s.sel c₀.ds (mutLateWorld.genesisFacets 200) ∧
        ¬ ∃ s', MutStep mutLateWorld s (.sys (.transition 0)) s') ∧
      ∃ c₁, s.sys.chains 1 = some c₁ ∧ c₁.pv = 2 ∧
        CountCheck s.sel c₁.ds (mutLateWorld.genesisFacets 200) ∧
        ∃ s', MutStep mutLateWorld s (.sys (.transition 1)) s' ∧
          ∃ c, s'.sys.chains 1 = some c ∧ c.pv = 3

/-- **COUNTERMODEL: STABLE DURING THE RUN IS NOT ENOUGH.** Facet `21` answers `[1, 3]` from the
start and no step changes an answer. Every transition was built under `mutSelA`, so `300` was not
built under the answers the run sees, and the run meets `StableSelectors` for no `σ`. The run
starts from an invariant state under the answers it sees: it creates chain `0`, commits `300`,
upgrades chain `0` and creates chain `1`. Both chains end at version 2, whose release is `200`,
and route differently, so no `ChainRouting` world reaches the final state's routing view along a
run without break-glass cut from an invariant state. -/
def Properties.StaleCutsSplitRouting : Prop :=
  (∀ t, mutWorld.FrozenUnder mutSelA t) ∧ ¬ mutWorld.FrozenUnder mutSelB 300 ∧
    (∀ σ, ¬ StableSelectors mutWorld σ mutStaleSys0
      [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)]) ∧
    DSysInv (mutWorld.at mutSelB) mutStaleSys0.sys ∧ mutStaleSys0.sel = mutSelB ∧
    ∃ s, MutRun mutWorld mutStaleSys0
        [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)] s ∧
      s.sel = mutSelB ∧ s.sys.ctm.relAt 2 = 200 ∧
      (∃ c₀ c₁, s.sys.chains 0 = some c₀ ∧ s.sys.chains 1 = some c₁ ∧ c₀.pv = 2 ∧ c₁.pv = 2 ∧
        c₀.ds.routing ≠ c₁.ds.routing) ∧
      ¬ ∃ (W : World) (s₀ : Sys) (ls : List Label), SysInv W s₀ ∧ Run W s₀ ls s.sys.view ∧
        ∀ l ∈ ls, ¬ l.isArbitrary

/-- **COUNTERMODEL: A CHANGED ANSWER OF THE DEPARTING RELEASE'S FACET LEAVES THAT FACET ROUTED.**
In `mutWorld` (every transition built under `mutSelA`; `300`, with stored cuts `Remove [1, 2]` then
`Add 21 [1, 2]`, meets everything `CTMTransition`'s constructor establishes under them), every
address passes `validate()`'s facet checks under `mutSelC`, which differs from `mutSelA` only in
facet `11`'s list, `[1, 2, 5]`.

The run starts from an invariant state with the facets answering `mutSelA`. Facet `11`, release
`100`'s only facet, starts answering `[1, 2, 5]`. Chain `0` is created on release `100` and the
CTM commits `300` (1→2). In that state chain `0` is on consistent diamond storage, `300` is
committed at its version, and the departing release's rows are well-formed under the answers now
but flatten differently from under `mutSelA`: every premise of
`UnchangedDepartingAnswersLandOnRelease` but the last holds. Chain `0` crosses: the guard passes,
because the chain routes the three selectors facet `11` names now. There is no break-glass cut.

At the end chain `0` is at version 2, whose release is `200`, and routes selector `5` to facet
`11`. For no answer set is its routing release `200`'s, so no `LiveRouting` run of these objects,
whatever fixed answers the facets give, reaches the final state from an invariant state without
break-glass cut. It fails the count check against release `200` under every answer set. -/
def Properties.MutableSelectorsLeaveDepartingFacetRouted : Prop :=
  (∀ t, mutWorld.FrozenUnder mutSelA t) ∧ mutWorld.GenuineUnder mutSelA 300 ∧
    mutWorld.cuts 300 = [⟨0, .remove, false, [1, 2]⟩, ⟨21, .add, false, [1, 2]⟩] ∧
    (∀ R, ReleaseValid (mutWorld.at mutSelC) R) ∧
    (∀ f, f ≠ 11 → mutSelC f = mutSelA f) ∧ mutSelA 11 = [1, 2] ∧ mutSelC 11 = [1, 2, 5] ∧
    DSysInv (mutWorld.at mutSelA) mutSys0.sys ∧ mutSys0.sel = mutSelA ∧
    ∃ s₃ s, MutRun mutWorld mutSys0
        [.setSelectors 11 [1, 2, 5], .sys (.genesis 0), .sys (.ctm (.commit 300))] s₃ ∧
      (∃ c, s₃.sys.chains 0 = some c ∧ mutWorld.FrozenUnder mutSelA (s₃.sys.ctm.ut c.pv) ∧
        DiamondOk c.ds ∧
        RowsWf s₃.sel (mutWorld.genesisFacets (mutWorld.tr (s₃.sys.ctm.ut c.pv)).fromRel) ∧
        flattenRows s₃.sel (mutWorld.genesisFacets (mutWorld.tr (s₃.sys.ctm.ut c.pv)).fromRel) ≠
          flattenRows mutSelA (mutWorld.genesisFacets (mutWorld.tr (s₃.sys.ctm.ut c.pv)).fromRel) ∧
        (mutWorld.tr (s₃.sys.ctm.ut c.pv)).newRel = 200) ∧
      MutStep mutWorld s₃ (.sys (.transition 0)) s ∧
      MutRun mutWorld mutSys0
        [.setSelectors 11 [1, 2, 5], .sys (.genesis 0), .sys (.ctm (.commit 300)),
          .sys (.transition 0)] s ∧
      s.sel = mutSelC ∧ s.sys.ctm.relAt 2 = 200 ∧
      ∃ c, s.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.ds.routing 5 = some (11, false) ∧
        (∀ σ, c.ds.routing ≠ rowsRouting (flattenRows σ (mutWorld.genesisFacets 200))) ∧
        (∀ σ, ¬ CountCheck σ c.ds (mutWorld.genesisFacets 200)) ∧
        ¬ ∃ (σ : Address → List Selector) (s₀ : DSys) (ls : List DLabel),
          DSysInv (mutWorld.at σ) s₀ ∧ DRun (mutWorld.at σ) s₀ ls s.sys ∧
            ∀ l ∈ ls, ¬ l.isArbitrary

end Contracts.ChainTypeManager.MutableSelectors
