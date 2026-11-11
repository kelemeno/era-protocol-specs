import EraSpec.Contracts.ChainTypeManager.Specs.LiveRouting

/-!
# Properties: the counting check is exact, and the headline holds with it

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.LiveRouting`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.LiveRouting`.

## The check

* **Counting is exact routing** (`CountCheckIffExactRouting`): on diamond storage satisfying
  `DiamondOk`, for a release whose rows each self-describe a selector and list no selector
  twice (`RowsWf`), `requireReleaseRouting` passes exactly when the proxy routes exactly the
  release's flattened rows. This is the source's argument at `LiveRoutingReader.sol:34-37`,
  checked. `CountCheckWitness` shows both outcomes.
* **The premises are what `validate()` checks, and each is needed.** `validate()` checks
  `RowsWf` (and nonzero facets); distinct facet rows follow from it
  (`ValidRowsHaveDistinctFacets`), which is what `CTMRelease.sol:167-170` says. Without
  nonempty selector lists, a release `{11: [1], 12: []}` passes the check against a diamond
  `{11: [1], 13: [2]}` that also routes selector `2` (`EmptySelectorRowFoolsCountCheck`).
  Without distinct selectors, a release listing facet `11` twice passes against the same
  diamond (`RepeatedRowFoolsCountCheck`). Without consistent storage — which a `delegatecall`ed
  init can break — a store that routes an extra selector to an unlisted facet passes against a
  valid release (`CorruptStorageFoolsCountCheck`).
* **The empty-row gap has teeth.** With such a release on both sides of an edge (so the
  derived cuts are empty), a chain whose diamond routes a foreign selector crosses the edge
  with it under the counting check, while `ChainRouting`'s semantic guard refuses the same
  crossing (`EmptySelectorRowCarriesDriftAcrossEdge`).

## The system with the check

`DStep` is `ChainRouting.Step` with the routing written by `Diamond.sol`'s own code and the
semantic guard replaced by `CountCheck`.

* **It refines `ChainRouting`** (`CountedStepRefinesStep`): from a state whose CTM satisfies
  `CtmInv` and whose releases and storages are well formed (`StoreInv`), every step is a
  `ChainRouting` step of what the system routes. The non-break-glass steps keep the invariant
  (`CountedStepPreservesInvariant`), so whole runs refine (`CountedRunRefinesRun`).
* **Headline, re-derived** (`ChainsRunTheirVersionsReleaseCounted`): along any run from an
  invariant state without a break-glass cut, every chain at a version `v` with a release
  `R_v` routes exactly `R_v`, passes the on-chain check against `R_v`, and has consistent
  storage. On a fresh CTM every chain has such a release
  (`FreshChainsRunTheirVersionsReleaseCounted`). The starting states are those of
  `ChainRouting` plus `validate()` of the starting release and consistent storage of
  pre-registry chains (`FreshCountedSystemSatisfiesInvariant`,
  `BootstrapCountedSystemSatisfiesInvariant`).
* **Drift still cannot cross an edge** (`CountedDriftBlocksTransition`), now as a consequence
  of the counting check, for a chain whose storage is consistent (a break-glass cut made of
  facet cuts keeps it; `CountedDriftWitness`).

`CountedRoutingWitness` is `ChainRoutingWitness` run through the diamond's code, and
`CountedBootstrapResetWitness` is `BootstrapResetWitness` (including `removeAllCuts`).
-/

namespace Contracts.ChainTypeManager

/-! ## Releases -/

/-- **`validate()`'s CHECKS FORCE DISTINCT FACET ROWS.** A repeated facet repeats its
self-described selectors, which are nonempty; so rows with nonempty and duplicate-free
selector lists name each facet once (`CTMRelease.sol:167-170`: "`validate()` refuses the same
repetition through the selectors it repeats"). -/
def Properties.ValidRowsHaveDistinctFacets : Prop :=
  ∀ (sel : Address → List Selector) (rows : List FacetRow), RowsWf sel rows →
    (rows.map Prod.fst).Nodup

/-! ## The check -/

/-- **HEADLINE: THE COUNTING CHECK IS EXACT ROUTING.** On diamond storage satisfying
`DiamondOk`, for rows with nonempty, duplicate-free selector lists, `requireReleaseRouting`
passes if and only if the proxy routes exactly the rows' selectors, each to its row's facet
with its row's freezability, and nothing else. -/
def Properties.CountCheckIffExactRouting : Prop :=
  ∀ (sel : Address → List Selector) (ds : DiamondStorage) (rows : List FacetRow),
    DiamondOk ds → RowsWf sel rows →
    (CountCheck sel ds rows ↔ ds.routing = rowsRouting (flattenRows sel rows))

/-- **THE EQUIVALENCE IS NOT VACUOUS.** The diamond a chain created on release `100` gets
satisfies `DiamondOk`; releases `100` and `200` pass `validate()`; and the diamond passes the
check against `100` and fails it against `200`. -/
def Properties.CountCheckWitness : Prop :=
  ∃ ds, diamondCut DiamondStorage.fresh (newChainInstallations wDWorld 100) = some ds ∧
    DiamondOk ds ∧ ReleaseValid wDWorld 100 ∧ ReleaseValid wDWorld 200 ∧
    CountCheck wDWorld.selectors ds (wDWorld.genesisFacets 100) ∧
    ¬ CountCheck wDWorld.selectors ds (wDWorld.genesisFacets 200)

/-- **COUNTERMODEL: A SELECTOR-LESS ROW FOOLS THE COUNT.** Release rows `[11, 12]` where
facet `11` self-describes `[1]` and facet `12` nothing; no selector is listed twice. The
diamond built by adding `11: [1]` and `13: [2]` satisfies `DiamondOk` and passes the check
(two facets, two rows; `11` routes its one selector; `12` has nothing to compare), yet routes
selector `2`, which the release does not. So the check's exactness rests on `validate()`
refusing empty selector lists (`CTMRelease.sol:121-123`). -/
def Properties.EmptySelectorRowFoolsCountCheck : Prop :=
  ∃ ds, diamondCut DiamondStorage.fresh cmCuts = some ds ∧ DiamondOk ds ∧
    CountCheck cmSelectors ds cmRows ∧
    ds.routing 2 = some (13, false) ∧ rowsRouting (flattenRows cmSelectors cmRows) 2 = none ∧
    (cmRows.flatMap fun fb => cmSelectors fb.1).Nodup ∧ (12, false) ∈ cmRows ∧
    cmSelectors 12 = []

/-- **COUNTERMODEL: A REPEATED ROW FOOLS THE COUNT.** Release rows `[11, 11]`, facet `11`
self-describing `[1]`: every row has a selector, but selector `1` is listed twice. The same
diamond passes the check (two facets, two rows) and routes selector `2`. So the check also
rests on `validate()` refusing a repeated selector (`CTMRelease.sol:128`). -/
def Properties.RepeatedRowFoolsCountCheck : Prop :=
  ∃ ds, diamondCut DiamondStorage.fresh cmCuts = some ds ∧ DiamondOk ds ∧
    CountCheck cmSelectors ds cmRepeatedRows ∧
    ds.routing 2 = some (13, false) ∧
    rowsRouting (flattenRows cmSelectors cmRepeatedRows) 2 = none ∧
    (∀ fb ∈ cmRepeatedRows, cmSelectors fb.1 ≠ []) ∧
    ¬ (cmRepeatedRows.flatMap fun fb => cmSelectors fb.1).Nodup

/-- **COUNTERMODEL: INCONSISTENT STORAGE FOOLS THE COUNT.** `corruptStore` is release `100`'s
diamond plus a `selectorToFacet` entry routing selector `3` to facet `99`, which no list
records — what an init that writes diamond storage directly can leave. Release `100` passes
`validate()`, the store passes the check against it, and the store routes selector `3`, which
release `100` does not; the store fails `DiamondOk`. -/
def Properties.CorruptStorageFoolsCountCheck : Prop :=
  ReleaseValid wDWorld 100 ∧
    CountCheck wDWorld.selectors corruptStore (wDWorld.genesisFacets 100) ∧
    corruptStore.routing 3 = some (99, false) ∧ rowsRouting (wDWorld.rows 100) 3 = none ∧
    ¬ DiamondOk corruptStore

/-- **COUNTERMODEL: THE EMPTY-ROW GAP CARRIES DRIFT ACROSS AN EDGE.** In `cmWorld`, releases
`700` (version 1) and `710` (version 2) both have rows `[11, 12]`, and transition `720` goes
from one to the other, so its derived cuts are empty. `cmSys` has a CTM satisfying `CtmInv`
with `720` committed, and chain `0` at version 1 on the diamond above, which satisfies
`DiamondOk` and does not route release `700`. The counting check passes, the chain crosses,
and lands at version 2 still routing selector `2`, which release `710` does not. The
`ChainRouting` step with the semantic guard has no such crossing. Release `700` fails
`validate()`. -/
def Properties.EmptySelectorRowCarriesDriftAcrossEdge : Prop :=
  CtmInv cmWorld.toWorld cmSys.ctm ∧ DiamondOk cmStore ∧
    cmSys.ctm.relAt 1 = 700 ∧ cmStore.routing ≠ rowsRouting (cmWorld.rows 700) ∧
    (∃ s', DStep cmWorld cmSys (.transition 0) s' ∧
      ∃ c, s'.chains 0 = some c ∧ c.pv = 2 ∧ c.ds.routing 2 = some (13, false) ∧
        rowsRouting (cmWorld.rows 710) 2 = none) ∧
    (¬ ∃ s', Step cmWorld.toWorld cmSys.view (.transition 0) s') ∧
    ¬ ReleaseValid cmWorld 700

/-! ## The system with the check -/

/-- **EVERY COUNT-CHECKED STEP IS A `ChainRouting` STEP.** From a state whose CTM satisfies
`CtmInv` and whose installed releases and chain storages are well formed, every step —
break-glass included — is a step of `ChainRouting.Step` between the routings the two states
implement, with the corresponding label. -/
def Properties.CountedStepRefinesStep : Prop :=
  ∀ (D : DWorld) (s s' : DSys) (l : DLabel), CtmInv D.toWorld s.ctm → StoreInv D s →
    DStep D s l s' → Step D.toWorld s.view l.view s'.view

/-- **EVERY STEP BUT A BREAK-GLASS CUT PRESERVES THE INVARIANT.** -/
def Properties.CountedStepPreservesInvariant : Prop :=
  ∀ (D : DWorld) (s s' : DSys) (l : DLabel), DSysInv D s → DStep D s l s' →
    ¬ l.isArbitrary → DSysInv D s'

/-- **RUNS REFINE RUNS.** Along any run from an invariant state without a break-glass cut,
the routings form a `ChainRouting` run, and the invariant holds at the end. -/
def Properties.CountedRunRefinesRun : Prop :=
  ∀ (D : DWorld) (s s' : DSys) (ls : List DLabel), DSysInv D s → DRun D s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) →
    Run D.toWorld s.view (ls.map DLabel.view) s'.view ∧ DSysInv D s'

/-- **HEADLINE: EVERY CHAIN AT VERSION `v` HAS EXACTLY `R_v`'S ROUTING, WITH THE COUNTING
CHECK.** Along any run from an invariant state that uses no break-glass cut, every chain at a
version `v` for which the CTM has a release `R_v`: `R_v` is a release of version `v`; the
chain's proxy routes exactly `R_v`'s selectors, each to `R_v`'s facet with `R_v`'s
freezability, and nothing else; the chain passes `requireReleaseRouting(R_v)`; and its
diamond storage is consistent. -/
def Properties.ChainsRunTheirVersionsReleaseCounted : Prop :=
  ∀ (D : DWorld) (s s' : DSys) (ls : List DLabel), DSysInv D s → DRun D s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.chains id = some c → s'.ctm.relAt c.pv ≠ 0 →
      D.relVersion (s'.ctm.relAt c.pv) = c.pv ∧
      c.ds.routing = rowsRouting (D.rows (s'.ctm.relAt c.pv)) ∧
      CountCheck D.selectors c.ds (D.genesisFacets (s'.ctm.relAt c.pv)) ∧ DiamondOk c.ds

/-- **ON A FRESHLY INITIALIZED CTM, EVERY CHAIN HAS ITS VERSION'S RELEASE**, with the counting
check: no chain is ever at a version without a release. -/
def Properties.FreshChainsRunTheirVersionsReleaseCounted : Prop :=
  ∀ (D : DWorld) (R : Address) (s' : DSys) (ls : List DLabel), R ≠ 0 → ReleaseValid D R →
    DRun D ⟨initState D.toWorld R, fun _ => none⟩ ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.chains id = some c →
      s'.ctm.relAt c.pv ≠ 0 ∧ D.relVersion (s'.ctm.relAt c.pv) = c.pv ∧
      c.ds.routing = rowsRouting (D.rows (s'.ctm.relAt c.pv)) ∧
      CountCheck D.selectors c.ds (D.genesisFacets (s'.ctm.relAt c.pv))

/-! ## Starting states -/

/-- **A FRESHLY INITIALIZED CTM WITH NO CHAINS SATISFIES THE INVARIANT**, its release having
passed `validate()` in `initialize` (`ChainTypeManager.sol:297` → :310). -/
def Properties.FreshCountedSystemSatisfiesInvariant : Prop :=
  ∀ (D : DWorld) (R : Address), R ≠ 0 → ReleaseValid D R →
    DSysInv D ⟨initState D.toWorld R, fun _ => none⟩

/-- **A JUST-BOOTSTRAPPED CTM SATISFIES THE INVARIANT**, its release having passed `validate()`
in `setNewVersionUpgrade` (:817 → :310), provided every pre-registry chain is not ahead of the
departing version and has consistent diamond storage. -/
def Properties.BootstrapCountedSystemSatisfiesInvariant : Prop :=
  ∀ (D : DWorld) (old : ℕ) (R : Address) (chains : ChainId → Option DChain),
    R ≠ 0 → old < D.relVersion R → ReleaseValid D R →
    (∀ id c, chains id = some c → c.pv ≤ old ∧ DiamondOk c.ds) →
    DSysInv D ⟨bootstrapState D.toWorld old R, chains⟩

/-! ## Drift -/

/-- **A CHAIN THAT DRIFTED FROM `R_v` CANNOT UPGRADE, UNDER THE COUNTING CHECK.** If the CTM
satisfies `CtmInv`, its releases passed `validate()`, and a chain's storage is consistent but
does not route its version's release, no transition step exists for it. -/
def Properties.CountedDriftBlocksTransition : Prop :=
  ∀ (D : DWorld) (s : DSys) (id : ChainId) (c : DChain), CtmInv D.toWorld s.ctm →
    (∀ v, s.ctm.relAt v ≠ 0 → ReleaseValid D (s.ctm.relAt v)) →
    s.chains id = some c → DiamondOk c.ds →
    c.ds.routing ≠ rowsRouting (D.rows (s.ctm.relAt c.pv)) →
    ¬ ∃ s', DStep D s (.transition id) s'

/-! ## Witnesses -/

/-- **THE COUNTED HEADLINE IS NOT VACUOUS.** `wDWorld` is `ChainRouting`'s witness world with
releases as facet rows. From the fresh witness system: create chain `0` at version 1, commit
`300` (1→2), upgrade chain `0`, and create chain `1`, all through the diamond's code and the
counting check. The run starts from an invariant state; both chains end at version 2 routing
release `200`, which differs from release `100`, and chain `0` passes the check against
`200`. -/
def Properties.CountedRoutingWitness : Prop :=
  wDWorld.toWorld = wWorld ∧ DSysInv wDWorld wDSys0 ∧
    ∃ s, DRun wDWorld wDSys0 [.genesis 0, .ctm (.commit 300), .transition 0, .genesis 1] s ∧
      (∃ c, s.chains 0 = some c ∧ c.pv = 2 ∧ c.ds.routing = rowsRouting (wRows 200) ∧
        CountCheck wDWorld.selectors c.ds (wDWorld.genesisFacets 200)) ∧
      (∃ c, s.chains 1 = some c ∧ c.pv = 2 ∧ c.ds.routing = rowsRouting (wRows 200)) ∧
      rowsRouting (wRows 200) ≠ rowsRouting (wRows 100)

/-- **THE BOOTSTRAP RESET, THROUGH THE DIAMOND'S CODE.** A pre-registry chain at version 0
whose diamond routes only selector `7` (to facet `77`) crosses the bootstrap edge onto
release `100`: `removeAllCuts` removes its routing, the release is installed, and the chain
ends at version 1 routing exactly release `100`, without selector `7`, and passing the check
against it. The starting system satisfies the invariant. -/
def Properties.CountedBootstrapResetWitness : Prop :=
  ∃ s, DRun wDWorld wBootDSys [.bootstrapReset 5] s ∧ DSysInv wDWorld wBootDSys ∧
    wPreStore.routing 7 = some (77, true) ∧
    ∃ c, s.chains 5 = some c ∧ c.pv = 1 ∧ c.ds.routing = rowsRouting (wRows 100) ∧
      c.ds.routing 7 = none ∧ CountCheck wDWorld.selectors c.ds (wDWorld.genesisFacets 100)

/-- **THE DRIFT RESULT IS NOT VACUOUS.** Create chain `0` on release `100`, commit `300`, and
cut it by break-glass to `wBgStore`, release `100`'s diamond plus facet `99` routing selector
`9` (one facet cut). The CTM satisfies `CtmInv`, its releases passed `validate()`, the chain's
storage is consistent and does not route release `100`, and no transition step exists. -/
def Properties.CountedDriftWitness : Prop :=
  ∃ s, DRun wDWorld wDSys0 [.genesis 0, .ctm (.commit 300), .arbitraryCut 0 1 wBgStore] s ∧
    CtmInv wDWorld.toWorld s.ctm ∧
    (∀ v, s.ctm.relAt v ≠ 0 → ReleaseValid wDWorld (s.ctm.relAt v)) ∧
    (∃ c, s.chains 0 = some c ∧ DiamondOk c.ds ∧
      c.ds.routing ≠ rowsRouting (wDWorld.rows (s.ctm.relAt c.pv))) ∧
    ¬ ∃ s', DStep wDWorld s (.transition 0) s'

end Contracts.ChainTypeManager
