import EraSpec.Contracts.ChainTypeManager.Specs.MutableSelectors

/-!
# Properties: the routing headline needs stable `selectors()` answers

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.MutableSelectors`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.MutableSelectors`.

## With stable answers

* **The model refines `LiveRouting`** (`StableRunIsACountedRun`). Under `StableSelectors` a run is
  a `LiveRouting` run of the world whose facets answer `σ`, and the answers stay `σ`. No invariant
  is needed: the guards are the same, and the stored cuts are the derived ones. Conversely, every
  `LiveRouting` run is such a run (`CountedRunIsAStableRun`).
* **Headline** (`ChainsRunTheirVersionsReleaseStable`). Take a run from an invariant state, with no
  break-glass cut, under `StableSelectors`. Every chain at a version `v` with a release `R_v`
  routes exactly `R_v`'s rows with the selectors `σ` gives them, and passes the guard against
  `R_v` as the facets answer at the end. On a fresh CTM every chain has such a release
  (`FreshChainsRunTheirVersionsReleaseStable`).
* **The base headline's world** (`StableRunIsARoutingRun`). The routing view of such a run is a
  `ChainRouting` run of `(M.at σ).toWorld`, whose `relRows R` is `flattenRows σ (genesisFacets R)`,
  so `ChainsRunTheirVersionsRelease` applies with that world. This is the sense in which
  `World.relRows` is fixed: the rows are write-once, and the answers are stable.
* `StableSelectorsWitness`: the premise holds on `LiveRouting`'s witness run, which crosses an edge
  and creates chains.

## Without them

All on `LiveRouting`'s witness world with genuine objects. Every transition stored the cuts its
constructor derives, and every release passes `validate()` both before and after the change.

* **One change splits a release's routing** (`MutableSelectorsSplitRouting`). Chain `0` is created
  on release `100`, and the CTM commits `300` (1→2), while facet `21` answers `[1, 2]`. Facet `21`
  then answers `[1, 3]`. Chain `0` crosses with `300`'s stored cuts and routes `[1, 2]`. Chain `1`,
  created afterwards, routes `[1, 3]`. Both are at version 2, whose release is `200`. No
  `ChainRouting` world reaches that state along a run without break-glass cut from an invariant
  state, and no `LiveRouting` world does either. Of `StableSelectors`, only the change fails.
* **The guard reads the answers now** (`CrossingNeedsTheAnswersNow`). A chain whose diamond fails
  the count check against its version's release, as the facets answer now, cannot cross. That
  holds whatever transition is committed at its version, whenever it was built.
* **So the next edge rejects the stale chain** (`MutableSelectorsBlockNextEdge`). After the split,
  the CTM commits `600` (2→3), built after the change. Chain `1` crosses. Chain `0` fails the count
  check and has no crossing.
* **Stable during the run is not enough** (`StaleCutsSplitRouting`). Let facet `21` answer `[1, 3]`
  from the start, with no change during the run. The same split happens, because `300` was built
  while facet `21` answered `[1, 2]`. The answers must also be the ones every transition was built
  under.
-/

namespace Contracts.ChainTypeManager

/-! ## With stable answers -/

/-- **UNDER STABLE ANSWERS, A RUN IS A `LiveRouting` RUN.** Under `StableSelectors M σ`, a run of
this model is a run of `LiveRouting`'s system in the world whose facets answer `σ`, with the same
labels, and the answers are still `σ` at the end. -/
def Properties.StableRunIsACountedRun : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s s' : MutSys) (ls : List MutLabel),
    StableSelectors M σ s ls → MutRun M s ls s' →
    DRun (M.at σ) s.sys (MutLabel.toDLabels ls) s'.sys ∧ s'.sel = σ

/-- **EVERY `LiveRouting` RUN IS A STABLE RUN.** With each transition's cuts stored as derived under
the world's answers (`MutWorld.ofDWorld`), a `LiveRouting` run is a run of this model in which no
answer changes, and it meets `StableSelectors`. Read with the world's answers, the lifted objects
are the world itself. -/
def Properties.CountedRunIsAStableRun : Prop :=
  ∀ (D : DWorld) (s s' : DSys) (ls : List DLabel), DRun D s ls s' →
    MutRun (MutWorld.ofDWorld D) ⟨s, D.selectors⟩ (ls.map MutLabel.sys) ⟨s', D.selectors⟩ ∧
    StableSelectors (MutWorld.ofDWorld D) D.selectors ⟨s, D.selectors⟩ (ls.map MutLabel.sys) ∧
    (MutWorld.ofDWorld D).at D.selectors = D

/-- **HEADLINE: UNDER STABLE ANSWERS, EVERY CHAIN AT VERSION `v` HAS EXACTLY `R_v`'S ROUTING.**
Along any run from an invariant state that uses no break-glass cut, if every facet answers `σ`
throughout and every transition was built under `σ` (`StableSelectors`), then every chain at a
version `v` for which the CTM has a release `R_v`:
* `R_v` is a release of version `v`;
* the chain's proxy routes exactly `R_v`'s rows with the selectors `σ` gives them;
* the chain passes `requireReleaseRouting(R_v)` as the facets answer at the end;
* its diamond storage is consistent. -/
def Properties.ChainsRunTheirVersionsReleaseStable : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s s' : MutSys) (ls : List MutLabel),
    StableSelectors M σ s ls → DSysInv (M.at σ) s.sys → MutRun M s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      M.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.ds.routing = rowsRouting (flattenRows σ (M.genesisFacets (s'.sys.ctm.relAt c.pv))) ∧
      CountCheck s'.sel c.ds (M.genesisFacets (s'.sys.ctm.relAt c.pv)) ∧ DiamondOk c.ds

/-- **ON A FRESHLY INITIALIZED CTM, UNDER STABLE ANSWERS, EVERY CHAIN HAS ITS VERSION'S RELEASE.**
The release `initialize` installs passed `validate()` under the answers `σ`; no chain is ever at a
version without a release. -/
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

/-- **UNDER STABLE ANSWERS, THE BASE HEADLINE APPLIES WITH ONE FIXED WORLD.** The routing view of a
run as in the headline is a `ChainRouting` run from an invariant state, with no break-glass cut, of
the world `(M.at σ).toWorld`, whose `relRows R` is `R`'s rows flattened with the selectors `σ`
gives them. So `ChainsRunTheirVersionsRelease` holds with that `World`. -/
def Properties.StableRunIsARoutingRun : Prop :=
  ∀ (M : MutWorld) (σ : Address → List Selector) (s s' : MutSys) (ls : List MutLabel),
    StableSelectors M σ s ls → DSysInv (M.at σ) s.sys → MutRun M s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) →
    SysInv (M.at σ).toWorld s.sys.view ∧
      Run (M.at σ).toWorld s.sys.view ((MutLabel.toDLabels ls).map DLabel.view) s'.sys.view ∧
      (∀ l ∈ (MutLabel.toDLabels ls).map DLabel.view, ¬ l.isArbitrary) ∧
      ∀ R, (M.at σ).toWorld.relRows R = flattenRows σ (M.genesisFacets R)

/-- **THE STABLE HEADLINE IS NOT VACUOUS.** `LiveRouting`'s witness run (`CountedRoutingWitness`) in
this model: on `wDWorld` with every transition built under its answers, create chain `0` at version
1, commit `300` (1→2), upgrade chain `0` and create chain `1`, with no answer changing. The run
meets `StableSelectors` and starts from an invariant state. Both chains end at version 2 routing
release `200`, which differs from release `100`. -/
def Properties.StableSelectorsWitness : Prop :=
  StableSelectors mutWorld mutSelA mutSys0
      [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)] ∧
    DSysInv (mutWorld.at mutSelA) mutSys0.sys ∧
    ∃ s, MutRun mutWorld mutSys0
        [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)] s ∧
      ∃ c₀ c₁, s.sys.chains 0 = some c₀ ∧ s.sys.chains 1 = some c₁ ∧ c₀.pv = 2 ∧ c₁.pv = 2 ∧
        c₀.ds.routing = rowsRouting (wRows 200) ∧ c₁.ds.routing = rowsRouting (wRows 200) ∧
        rowsRouting (wRows 200) ≠ rowsRouting (wRows 100)

/-! ## Without stable answers -/

/-- **COUNTERMODEL: ONE CHANGED ANSWER SPLITS A RELEASE'S ROUTING, WITH GENUINE OBJECTS.**

The objects:
* every transition stored the cuts its constructor derives under the starting answers `mutSelA`;
* `300` is a genuine `CTMTransition` built under them, with stored cuts `Remove [1, 2]` then
  `Add 21 [1, 2]`;
* every release passes `validate()` under both answer sets;
* the two answer sets differ only in facet `21`'s list.

The run starts from an invariant state with the facets answering `mutSelA`. It creates chain `0`
on release `100` and commits `300` (1→2). Facet `21` then starts answering `[1, 3]`. Chain `0`
crosses, and chain `1` is created. There is no break-glass cut.

At the end both chains are at version 2, whose release is `200`. Chain `0` routes release `200`'s
rows with the old answers; chain `1` routes them with the new ones. So no `ChainRouting` world
reaches the final state along a run without break-glass cut from an invariant state. The routing
view of that state is outside every model in which `ChainsRunTheirVersionsRelease` holds, and the
same goes for `LiveRouting`'s `ChainsRunTheirVersionsReleaseCounted`. -/
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
now. Then the chain has no crossing, whatever transition is committed at its version and whenever
that transition was built: the guard re-reads `selectors()`. -/
def Properties.CrossingNeedsTheAnswersNow : Prop :=
  ∀ (M : MutWorld) (s : MutSys) (id : ChainId) (c : DChain),
    CtmInv (M.at s.sel).toWorld s.sys.ctm → s.sys.chains id = some c →
    ¬ CountCheck s.sel c.ds (M.genesisFacets (s.sys.ctm.relAt c.pv)) →
    ¬ ∃ s', MutStep M s (.sys (.transition id)) s'

/-- **COUNTERMODEL: THE NEXT EDGE REJECTS THE CHAIN THAT CROSSED WITH THE OLD ANSWERS.** In
`mutLateWorld`, transition `600` (2→3, release `200` to `250`) is genuine and was built after facet
`21` started answering `[1, 3]`; `300` is genuine and was built before. After the run of
`MutableSelectorsSplitRouting`, the CTM commits `600`. Chain `0` fails the count check against
release `200` and has no crossing. Chain `1` passes it, crosses, and lands at version 3. -/
def Properties.MutableSelectorsBlockNextEdge : Prop :=
  mutLateWorld.GenuineUnder mutSelB 600 ∧ mutLateWorld.GenuineUnder mutSelA 300 ∧
    ∃ s, MutRun mutLateWorld mutSys0
        [.sys (.genesis 0), .sys (.ctm (.commit 300)), .setSelectors 21 [1, 3],
          .sys (.transition 0), .sys (.genesis 1), .sys (.ctm (.commit 600))] s ∧
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
built under the answers the run sees. The run starts from an invariant state: it creates chain
`0`, commits `300`, upgrades chain `0` and creates chain `1`. Both chains end at version 2 on
release `200` and route differently, so no `ChainRouting` world reaches that state.
`StableSelectors` needs one `σ` for the run and for every transition's construction. -/
def Properties.StaleCutsSplitRouting : Prop :=
  (∀ t, mutWorld.FrozenUnder mutSelA t) ∧ ¬ mutWorld.FrozenUnder mutSelB 300 ∧
    DSysInv (mutWorld.at mutSelB) mutStaleSys0.sys ∧ mutStaleSys0.sel = mutSelB ∧
    ∃ s, MutRun mutWorld mutStaleSys0
        [.sys (.genesis 0), .sys (.ctm (.commit 300)), .sys (.transition 0), .sys (.genesis 1)] s ∧
      s.sel = mutSelB ∧ s.sys.ctm.relAt 2 = 200 ∧
      (∃ c₀ c₁, s.sys.chains 0 = some c₀ ∧ s.sys.chains 1 = some c₁ ∧ c₀.pv = 2 ∧ c₁.pv = 2 ∧
        c₀.ds.routing ≠ c₁.ds.routing) ∧
      ¬ ∃ (W : World) (s₀ : Sys) (ls : List Label), SysInv W s₀ ∧ Run W s₀ ls s.sys.view ∧
        ∀ l ∈ ls, ¬ l.isArbitrary

end Contracts.ChainTypeManager
