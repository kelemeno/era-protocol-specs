import EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting

/-!
# Properties: every chain on a CTM runs its version's release

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.ChainRouting`.

## The headline

`ChainsRunTheirVersionsRelease`: along any run without a break-glass cut, every chain
at a version `v` for which the CTM has a release `R_v` routes exactly `R_v`'s
selectors to `R_v`'s facets. From a freshly initialized CTM every chain is at such a
version (`FreshChainsRunTheirVersionsRelease`). The proof is an induction over the four
ways a chain's routing changes: genesis, migration in, the bootstrap reset and a
transition (`StepPreservesSysInvariant`).

## What a break-glass cut does

A break-glass cut can leave a chain at `v` routing something other than `R_v`; the
headline does not survive it, so it carries the premise. What the system then does:

* **The drift never crosses a registry transition edge** (arbitrary and bootstrap
  crossings remain). A transition requires the live routing to
  be exactly `R_v`'s (`DriftBlocksTransition`), so a drifted chain cannot upgrade until
  its routing is restored. Every transition that does run starts from `R_v` and lands
  on `R_w` (`TransitionStartsAndLandsOnRelease`), whatever happened before.
* **The guard is what stops it.** Without `DefaultUpgrade.sol:37`, the derived cuts only
  touch the two releases' selectors, so any other selector is carried across the edge
  (`UnguardedCutKeepsForeignSelectors`). A concrete break-glass selector survives an
  unguarded transition (`BreakGlassSelectorSurvivesWithoutGuard`). With the guard, the
  same chain has no transition at all.
* **A missing selector bricks transitions.** A chain whose break-glass cut removed one
  of `R_v`'s selectors cannot cross the next edge, and would revert even without the
  guard, at the derived `Remove` of that selector (`MissingSelectorBricksTransition`).
-/

namespace Contracts.ChainTypeManager

/-! ## Starting states -/

/-- **A FRESHLY INITIALIZED CTM WITH NO CHAINS SATISFIES THE INVARIANT.** -/
def Properties.FreshSystemSatisfiesInvariant : Prop :=
  ∀ (W : World) (R : Address), R ≠ 0 → SysInv W ⟨initState W R, fun _ => none⟩

/-- **A JUST-BOOTSTRAPPED CTM SATISFIES THE INVARIANT**, whatever its pre-registry chains
route, provided none is ahead of the departing version (no chain can be ahead of its
CTM). -/
def Properties.BootstrapSystemSatisfiesInvariant : Prop :=
  ∀ (W : World) (old : ℕ) (R : Address) (chains : ChainId → Option Chain),
    R ≠ 0 → old < W.relVersion R → (∀ id c, chains id = some c → c.pv ≤ old) →
    SysInv W ⟨bootstrapState W old R, chains⟩

/-! ## The induction -/

/-- **EVERY STEP BUT A BREAK-GLASS CUT PRESERVES THE INVARIANT.** -/
def Properties.StepPreservesSysInvariant : Prop :=
  ∀ (W : World) (s s' : Sys) (l : Label), SysInv W s → Step W s l s' → ¬ l.isArbitrary →
    SysInv W s'

/-- **HEADLINE: EVERY CHAIN AT VERSION `v` HAS EXACTLY `R_v`'S ROUTING.** Along any run from
an invariant state that uses no break-glass cut, every chain at a version `v` for which
the CTM has a release `R_v` routes exactly `R_v`'s selectors, each to `R_v`'s facet with
`R_v`'s freezability, and nothing else; and `R_v` is a release of version `v`. -/
def Properties.ChainsRunTheirVersionsRelease : Prop :=
  ∀ (W : World) (s s' : Sys) (ls : List Label), SysInv W s → Run W s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.chains id = some c → s'.ctm.relAt c.pv ≠ 0 →
      W.relVersion (s'.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (W.relRows (s'.ctm.relAt c.pv))

/-- **ON A FRESHLY INITIALIZED CTM, EVERY CHAIN HAS ITS VERSION'S RELEASE.** No chain is
ever at a version without a release, so the headline applies to all of them. -/
def Properties.FreshChainsRunTheirVersionsRelease : Prop :=
  ∀ (W : World) (R : Address) (s' : Sys) (ls : List Label), R ≠ 0 →
    Run W ⟨initState W R, fun _ => none⟩ ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.chains id = some c →
      s'.ctm.relAt c.pv ≠ 0 ∧ W.relVersion (s'.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (W.relRows (s'.ctm.relAt c.pv))

/-! ## One transition, whatever came before -/

/-- **A TRANSITION STARTS FROM `R_v` AND LANDS ON `R_w`.** No assumption about the chain's
history — break-glass cuts included: a chain that crosses `upgradeTransition[v]` was
routing exactly `R_v`, and afterwards is at a reached version `w > v` routing exactly
`R_w`. -/
def Properties.TransitionStartsAndLandsOnRelease : Prop :=
  ∀ (W : World) (s s' : Sys) (id : ChainId) (c : Chain), CtmInv W s.ctm →
    s.chains id = some c → Step W s (.transition id) s' →
    s.ctm.relAt c.pv ≠ 0 ∧ c.routing = rowsRouting (W.relRows (s.ctm.relAt c.pv)) ∧
    ∃ c', s'.chains id = some c' ∧ c.pv < c'.pv ∧ c'.pv ≤ s'.ctm.pv ∧
      s'.ctm.relAt c'.pv ≠ 0 ∧ W.relVersion (s'.ctm.relAt c'.pv) = c'.pv ∧
      c'.routing = rowsRouting (W.relRows (s'.ctm.relAt c'.pv))

/-- **A CHAIN THAT DRIFTED FROM `R_v` CANNOT UPGRADE.** If a chain's routing is not its
version's release's, no transition step exists for it: the guard
`LiveRoutingReader.requireReleaseRouting(fromRelease)` reverts. -/
def Properties.DriftBlocksTransition : Prop :=
  ∀ (W : World) (s : Sys) (id : ChainId) (c : Chain), CtmInv W s.ctm →
    s.chains id = some c → c.routing ≠ rowsRouting (W.relRows (s.ctm.relAt c.pv)) →
    ¬ ∃ s', Step W s (.transition id) s'

/-! ## Without the guard -/

/-- **THE DERIVED CUTS ALONE KEEP EVERY SELECTOR NEITHER RELEASE NAMES.** Whatever the
live routing, if the derived cuts of an edge from rows `A` to rows `B` apply, every
selector named by neither release routes afterwards exactly as before; when the edge
changes the routing, every selector of `B` routes as `B` says. -/
def Properties.UnguardedCutKeepsForeignSelectors : Prop :=
  ∀ (ρ σ : Routing) (A B : ReleaseRows), applyDerived ρ A B = some σ →
    (∀ y, y ∉ A.map Prod.fst → y ∉ B.map Prod.fst → σ y = ρ y) ∧
    (A ≠ B → ∀ y ∈ B.map Prod.fst, σ y = rowsRouting B y)

/-- **A BREAK-GLASS SELECTOR WOULD SURVIVE AN UNGUARDED TRANSITION.** On the witness world:
chain `0` is created at version 1 on release `100`, the CTM commits `300` (1→2), and a
break-glass cut adds selector `9`, which neither release `100` nor release `200` routes.
The chain is now at version 1 routing something other than `R_1`, so the headline's
no-break-glass premise is needed. The unguarded engine would cross the edge and keep
selector `9`; the guarded system has no transition for this chain. -/
def Properties.BreakGlassSelectorSurvivesWithoutGuard : Prop :=
  ∃ s, Run wWorld wSys0 [.genesis 0, .ctm (.commit 300), .arbitraryCut 0 1 bgExtra] s ∧
    (∃ c, s.chains 0 = some c ∧ c.pv = 1 ∧ s.ctm.relAt 1 = 100 ∧
      c.routing ≠ rowsRouting (wRows 100) ∧ c.routing 9 = some (99, false) ∧
      rowsRouting (wRows 100) 9 = none ∧ rowsRouting (wRows 200) 9 = none) ∧
    (∃ ρ, UnguardedCrossing wWorld s 0 ρ ∧ ρ 9 = some (99, false)) ∧
    ¬ ∃ s', Step wWorld s (.transition 0) s'

/-- **A MISSING SELECTOR BRICKS THE NEXT TRANSITION.** As above, but the break-glass cut
removes selector `2`, which release `100` routes. The chain cannot cross the committed
edge: not with the guard, and not without it either, since the derived `Remove` of
selector `2` reverts on an unrouted selector. -/
def Properties.MissingSelectorBricksTransition : Prop :=
  ∃ s, Run wWorld wSys0 [.genesis 0, .ctm (.commit 300), .arbitraryCut 0 1 bgMissing] s ∧
    (∃ c, s.chains 0 = some c ∧ c.pv = 1 ∧ c.routing 2 = none ∧
      rowsRouting (wRows 100) 2 ≠ none) ∧
    (¬ ∃ ρ, UnguardedCrossing wWorld s 0 ρ) ∧
    ¬ ∃ s', Step wWorld s (.transition 0) s'

/-! ## Witnesses -/

/-- **THE HEADLINE IS NOT VACUOUS.** From the fresh witness system: create chain `0` at
version 1, commit `300` (1→2), upgrade chain `0`, and create chain `1`. The run uses no
break-glass cut and starts from an invariant state. Both chains end at version 2 routing
release `200`, which differs from release `100` — so the transition really reinstalled
the routing. -/
def Properties.ChainRoutingWitness : Prop :=
  ∃ s, Run wWorld wSys0 [.genesis 0, .ctm (.commit 300), .transition 0, .genesis 1] s ∧
    SysInv wWorld wSys0 ∧
    (∃ c, s.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)) ∧
    (∃ c, s.chains 1 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)) ∧
    s.ctm.relAt 2 = 200 ∧ rowsRouting (wRows 200) ≠ rowsRouting (wRows 100)

/-- **THE BOOTSTRAP RESET WIPES PRE-REGISTRY ROUTING.** A pre-registry chain at version 0
that routes only selector `7` crosses the bootstrap edge onto release `100` at version 1:
selector `7` is gone and the chain routes exactly release `100`. -/
def Properties.BootstrapResetWitness : Prop :=
  ∃ s, Run wWorld wBootSys [.bootstrapReset 5] s ∧ SysInv wWorld wBootSys ∧
    (∃ c, wBootSys.chains 5 = some c ∧ c.routing 7 ≠ none ∧ c.routing ≠ rowsRouting (wRows 100)) ∧
    (∃ c, s.chains 5 = some c ∧ c.pv = 1 ∧ c.routing = rowsRouting (wRows 100) ∧ c.routing 7 = none)

end Contracts.ChainTypeManager
