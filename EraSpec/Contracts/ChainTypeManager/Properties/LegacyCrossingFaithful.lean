import EraSpec.Contracts.ChainTypeManager.Specs.LegacyCrossingFaithful

/-!
# Properties: the executor headlines once pre-v35 chains cross opaque legacy edges themselves

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.LegacyCrossingFaithful`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.LegacyCrossingFaithful`. Namespace
`Contracts.ChainTypeManager.LegacyCrossing`.

## The gap

`ExecutorForward` reaches a chain-side crossing of an opaque legacy edge only as a forwarded
`arbitraryCut`, which `Tame` excludes. The source has a second route: a pre-v35 chain's admin or
validator calls the cut-taking `Admin.upgradeChainFromVersion` on the chain's own diamond, with
no owner involved. The refined model adds that route (`LLabel.cross`).

## What it costs

* **The tame headlines' source reading is false** (`ChainSideCrossingBreaksTameHeadline`). Start
  from the just-bootstrapped witness system, which satisfies `SysInv`. One tame `forward` of the
  legacy fix-up `setUpgradeDiamondCut(cut, 0)` is followed by pre-registry chain `5`'s own
  crossing of that edge. Chain `5` then sits at version 1 without routing release `100`, and
  `SysInv` fails. Every executor transaction of the run is `Tame`. No tame `ExecutorForward` run
  and no tame `ExecutorUpgradeChain` run from the same start reaches that state, so those runs
  miss a real behaviour. The run also fails the per-chain premise for chain `5`. So the source
  reading of `TameRunPreservesSysInv`, `TameRunKeepsChainsOnTheirRelease`,
  `RefinedTameRunKeepsChainsOnTheirRelease` and `TamePremiseImpliesChainLocal` ("every run whose
  executor transactions are tame") is false.
* **What a crossing is.** It writes like a break-glass cut (`CrossIsABreakGlassStep`), and its
  landing decides `SysInv` exactly (`CrossKeepsSysInvIff`).

## What survives

* **Counting crossings as break-glass** (the proposed fix `LLabel.Tame`): a tame refined run has
  no crossing, so it is an `ExecutorUpgradeChain` run (`CrossFreeRunsAreUpgradeChainRuns`). All of
  `TameRunPreservesSysInv` and the headline then hold (`TameRefinedRunKeepsChainsOnTheirRelease`).
* **Crossings that land consistently**: the global replacement. Along runs whose executor
  transactions are tame and each of whose crossings lands its chain consistent with the CTM,
  `SysInv`, the version bound, the CTM proxy and the headline all hold
  (`LandingRunPreservesSysInv`). `LegacyCatchUpWitness` meets the premise with a realistic
  catch-up of a pre-registry chain, with no owner action at all.
* **With no premise on crossings, chain by chain.** A refined run that keeps the CTM's code is a
  routing run (`CrossRunIsARoutingRun`). Along it, every chain whose last write is neither a
  forwarded break-glass cut nor a crossing runs its version's release
  (`ChainRunsItsVersionsReleaseAcrossCrossings`). Executor-tame runs meet that premise for every
  chain that no crossing of the run names (`ExecTamePremiseImpliesChainLocal`).
* **The slot results are unaffected.** A crossing never touches the CTM, so
  `MisreportingSlotStaysFrozen` and `GenuineReplacementsKeepUpgradeChainLive` hold along refined
  runs with any crossings (`MisreportingSlotStaysFrozenAcrossCrossings`,
  `GenuineReplacementsKeepUpgradeChainLiveAcrossCrossings`).
-/

namespace Contracts.ChainTypeManager.LegacyCrossing

/-! ## What a chain-side crossing is -/

/-- **A CHAIN-SIDE CROSSING WRITES LIKE A BREAK-GLASS CUT.** Every chain-side crossing of an
opaque legacy edge relates the same systems as `ChainRouting`'s `Step.arbitraryCut` with the same
chain, version and routing. So `Label.arbitraryCut` covers it at the routing level. At the
executor level, `ExecutorForward` reaches that label only through the owner's `forward`. -/
def Properties.CrossIsABreakGlassStep : Prop :=
  ∀ (W : World) (s s' : Sys) (id : ChainId) (v : ℕ) (ρ : Routing),
    CrossStep s id v ρ s' → Step W s (.arbitraryCut id v ρ) s'

/-- **ONE CROSSING KEEPS `SysInv` EXACTLY WHEN IT LANDS CONSISTENTLY.** From a state satisfying
`SysInv`, a chain-side crossing to version `v` with routing `ρ` leaves `SysInv` true if and only if
`v` is not above the CTM's version and, if the CTM has a release `R_v`, `ρ` is exactly `R_v`'s
routing (`CrossLandsOk`). Nothing about the crossing's opaque cut is assumed. -/
def Properties.CrossKeepsSysInvIff : Prop :=
  ∀ (W : World) (s s' : Sys) (id : ChainId) (v : ℕ) (ρ : Routing), SysInv W s →
    CrossStep s id v ρ s' → (SysInv W s' ↔ CrossLandsOk W s v ρ)

/-! ## The countermodel -/

/-- **THE TAME HEADLINES DO NOT HOLD ONCE PRE-V35 CHAINS CROSS THEIR OWN LEGACY EDGES.** The start
is `wLX0`: the CTM is `bootstrapState wWorld 0 100`, and pre-registry chain `5` is at version 0. It
satisfies `SysInv`, and its reinitializers satisfy `ReinitFrames`. Run `wRecutRun`:

1. One `forward` of `setUpgradeDiamondCut(cut, 0)` (`Op.legacyRecut 0`) re-commits the bootstrap
   edge with a cut the model cannot see. This is the legacy fix-up of
   `ChainTypeManager.sol:835-855`. The forward is `Tame`, and `SysInv` still holds after it.
2. Chain `5`'s admin crosses that edge on its own diamond, landing at version 1 with routing
   `bgExtra`.

Every executor transaction of the run is `Tame` and keeps the CTM's code. The crossing is no
executor transaction. At the end:

* chain `5` is at version 1, whose release is `100`, and does not route it;
* `SysInv` fails, and so does the per-chain premise `LastWriteNotBreakGlass 5`;
* no tame `ExecutorForward` run from `wLX0` reaches this state, and no tame `ExecutorUpgradeChain`
  run does either (by `TameRunKeepsChainsOnTheirRelease` and
  `RefinedTameRunKeepsChainsOnTheirRelease`).

So those models leave out a real behaviour, and their tame headlines, read as statements about
every run in which the owner does no break-glass cut, are false. -/
def Properties.ChainSideCrossingBreaksTameHeadline : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧ SysInv wX.W wLX0.sys ∧
    (∀ l ∈ wRecutRun, l.ExecTame wX) ∧ (∀ l ∈ wRecutRun, l.KeepsCtmCode wX) ∧
    ∃ s1 s, LStep wX wLX0 (.u (.x (.forward [.sys (.ctm (.legacyRecut 0))]))) s1 ∧
      SysInv wX.W s1.sys ∧ LStep wX s1 (.cross 5 1 bgExtra) s ∧ LRun wX wLX0 wRecutRun s ∧
      (∃ c, s.sys.chains 5 = some c ∧ c.pv = 1 ∧ s.sys.ctm.relAt 1 = 100 ∧
        c.routing ≠ rowsRouting (wWorld.relRows 100)) ∧
      ¬ SysInv wX.W s.sys ∧
      ¬ LastWriteNotBreakGlass 5 (wRecutRun.flatMap LLabel.sysLabels) ∧
      (¬ ∃ xs, XRun wX wLX0 xs s ∧ ∀ x ∈ xs, x.Tame wX) ∧
      (¬ ∃ us, URun wX wLX0 us s ∧ ∀ u ∈ us, u.Tame wX)

/-! ## What survives: counting crossings as break-glass -/

/-- **A REFINED RUN WITHOUT CROSSINGS IS AN `ExecutorUpgradeChain` RUN, AND CONVERSELY.** -/
def Properties.CrossFreeRunsAreUpgradeChainRuns : Prop :=
  ∀ (X : XConfig) (s s' : XState) (us : List ULabel),
    LRun X s (us.map LLabel.u) s' ↔ URun X s us s'

/-- **WITH CROSSINGS COUNTED AS BREAK-GLASS, THE OLD CONCLUSIONS STAND.** Take a refined run from a
state satisfying `SysInv`, with reinitializers that move at most their own proxy, in which every
transaction is `LLabel.Tame`, so it contains no chain-side crossing. It is an
`ExecutorUpgradeChain` run of tame transactions. At the end `SysInv` holds, the CTM's version has
not decreased, and the CTM proxy has not moved. Every chain at a version `v` with a release `R_v`
routes exactly `R_v`, and `R_v` is a release of version `v`. -/
def Properties.TameRefinedRunKeepsChainsOnTheirRelease : Prop :=
  ∀ (X : XConfig) (s s' : XState) (ls : List LLabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    SysInv X.W s.sys → LRun X s ls s' → (∀ l ∈ ls, l.Tame X) →
    (∃ us, ls = us.map LLabel.u ∧ URun X s us s' ∧ ∀ u ∈ us, u.Tame X) ∧
    SysInv X.W s'.sys ∧ s.sys.ctm.pv ≤ s'.sys.ctm.pv ∧ s'.impl X.ctmProxy = s.impl X.ctmProxy ∧
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      X.W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (X.W.relRows (s'.sys.ctm.relAt c.pv))

/-! ## What survives: crossings that land consistently -/

/-- **THE GLOBAL HEADLINE, WITH ITS PREMISE ON CROSSINGS EXPLICIT.** Take a refined run from a
state satisfying `SysInv`, with reinitializers that move at most their own proxy. Its executor
transactions are `Tame`, and each chain-side crossing, in the state where it is taken, lands its
chain consistent with the CTM (`LRunOk`). This is a property of the opaque cuts the CTM owner
committed. At the end `SysInv` holds, the CTM's version has not decreased, and the CTM proxy has not
moved. Every chain at a version `v` with a release `R_v` routes exactly `R_v`, and `R_v` is a release
of version `v`. -/
def Properties.LandingRunPreservesSysInv : Prop :=
  ∀ (X : XConfig) (s s' : XState) (ls : List LLabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    SysInv X.W s.sys → LRunOk X s ls s' → (∀ l ∈ ls, l.ExecTame X) →
    SysInv X.W s'.sys ∧ s.sys.ctm.pv ≤ s'.sys.ctm.pv ∧ s'.impl X.ctmProxy = s.impl X.ctmProxy ∧
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      X.W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (X.W.relRows (s'.sys.ctm.relAt c.pv))

/-! ## What survives: chain by chain, with no premise on crossings -/

/-- **A REFINED RUN THAT KEEPS THE CTM'S CODE IS A ROUTING RUN.** Suppose each reinitializer moves
at most its own proxy, and no executor transaction of a refined run moves the CTM proxy. Then the
run's routing steps, in order, form a `ChainRouting` run between the same routing systems. A
chain-side crossing contributes its `Label.arbitraryCut`. -/
def Properties.CrossRunIsARoutingRun : Prop :=
  ∀ (X : XConfig) (s s' : XState) (ls : List LLabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    LRun X s ls s' → (∀ l ∈ ls, l.KeepsCtmCode X) →
    Run X.W s.sys (ls.flatMap LLabel.sysLabels) s'.sys

/-- **THE PER-CHAIN HEADLINE ACROSS CHAIN-SIDE CROSSINGS.** Suppose each reinitializer moves at most
its own proxy. Take a refined run from a state where the CTM invariant holds and chain `id` is
consistent with its CTM. No executor transaction of the run moves the CTM proxy, and the last
routing step writing `id` is neither a break-glass cut nor a chain-side crossing. At the end chain
`id`, if registered, is not ahead of its CTM. If the CTM has a release `R_v` for the chain's version
`v`, the chain routes exactly `R_v`, and `R_v` is a release of version `v`. Crossings and forwarded
cuts of other chains are allowed anywhere, and so are those of `id` before its last write. -/
def Properties.ChainRunsItsVersionsReleaseAcrossCrossings : Prop :=
  ∀ (X : XConfig) (s s' : XState) (ls : List LLabel) (id : ChainId),
    ProxyUpgradeCurrent.ReinitFrames X.rc → CtmInv X.W s.sys.ctm →
    (∀ c, s.sys.chains id = some c → ChainOk X.W s.sys c) → LRun X s ls s' →
    (∀ l ∈ ls, l.KeepsCtmCode X) → LastWriteNotBreakGlass id (ls.flatMap LLabel.sysLabels) →
    ∀ c, s'.sys.chains id = some c → c.pv ≤ s'.sys.ctm.pv ∧
      (s'.sys.ctm.relAt c.pv ≠ 0 → X.W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
        c.routing = rowsRouting (X.W.relRows (s'.sys.ctm.relAt c.pv)))

/-- **EXECUTOR-TAME RUNS MEET THE PER-CHAIN PREMISES FOR EVERY CHAIN NO CROSSING NAMES.** A
refined run whose executor transactions are `Tame` keeps the CTM's code, and it satisfies
`LastWriteNotBreakGlass id` for every chain `id` that no chain-side crossing of the run names. This
replaces `TamePremiseImpliesChainLocal`, whose "for every chain" fails for the crossing chain of
`ChainSideCrossingBreaksTameHeadline`. -/
def Properties.ExecTamePremiseImpliesChainLocal : Prop :=
  ∀ (X : XConfig) (s s' : XState) (ls : List LLabel), LRun X s ls s' →
    (∀ l ∈ ls, l.ExecTame X) →
    (∀ l ∈ ls, l.KeepsCtmCode X) ∧
      ∀ id, (∀ v ρ, LLabel.cross id v ρ ∉ ls) → LastWriteNotBreakGlass id (ls.flatMap LLabel.sysLabels)

/-! ## The slot results are unaffected -/

/-- **A MISREPORTING SLOT STAYS FROZEN, CROSSINGS INCLUDED.** `MisreportingSlotStaysFrozen` along
refined runs: no premise on chain-side crossings is needed, because they never touch the CTM. Along
any refined run whose executor transactions are `Tame`, with reinitializers that move at most their
own proxy, from a state satisfying `CtmInv` in which slot `v` holds a transition whose
`oldProtocolVersion()` is not `v`: slot `v` is unchanged at the end, and no chain at version `v` has
an `upgradeChain` step, for any argument. -/
def Properties.MisreportingSlotStaysFrozenAcrossCrossings : Prop :=
  ∀ (X : XConfig) (s s' : XState) (ls : List LLabel) (v : ℕ),
    ProxyUpgradeCurrent.ReinitFrames X.rc → CtmInv X.W s.sys.ctm → s.sys.ctm.ut v ≠ 0 →
    (X.W.tr (s.sys.ctm.ut v)).old ≠ v → LRun X s ls s' → (∀ l ∈ ls, l.ExecTame X) →
    s'.sys.ctm.ut v = s.sys.ctm.ut v ∧
      ∀ id c, s'.sys.chains id = some c → c.pv = v →
        ¬ ∃ t s'', UStep X s' (.upgradeChain t id) s''

/-- **GENUINE REPLACEMENTS KEEP `upgradeChain` LIVE, CROSSINGS INCLUDED.**
`GenuineReplacementsKeepUpgradeChainLive` along refined runs. Take a refined run whose executor
transactions are `Tame`, with reinitializers that move at most their own proxy, from a state
satisfying `CtmInv` whose committed slots report their version. Suppose every replacement it
forwards reports its departing release's version. Then at the end every committed slot still
reports its version. For every chain, `upgradeChain(t, id)` reaches a state for some `t` exactly
when the chain admin's direct call does. -/
def Properties.GenuineReplacementsKeepUpgradeChainLiveAcrossCrossings : Prop :=
  ∀ (X : XConfig) (s s' : XState) (ls : List LLabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    CtmInv X.W s.sys.ctm → SlotsReport X.W s.sys.ctm → LRun X s ls s' →
    (∀ l ∈ ls, l.ExecTame X) →
    (∀ e r, (∃ l ∈ ls, l.ForwardsReplace e r) →
      (X.W.tr r).old = X.W.relVersion (X.W.tr r).fromRel) →
    SlotsReport X.W s'.sys.ctm ∧
      ∀ id s'', (∃ t, UStep X s' (.upgradeChain t id) s'') ↔
        ∃ old, UStep X s' (.adminUpgrade id old) s''

/-! ## Witness -/

/-- **THE LANDING PREMISE IS MET BY A PRE-REGISTRY CHAIN CATCHING UP ON ITS OWN.** The start is
`wLagX0`: the CTM is `bootstrapState wWorld 1 200`, at version 2 on release `200`. It records an
opaque pre-registry cut at version 0 and the bootstrap cut at version 1, and it satisfies `SysInv`.
Pre-registry chain `5` is at version 0. In the routing model it has neither a transition nor a
bootstrap reset there, so `ExecutorForward` can move it only by a forwarded break-glass cut (the
third case of `BehindChainsCanCatchUp`). In the refined model, run `wCatchUpRun`, which contains no
executor transaction:

1. Chain `5`'s admin crosses the opaque edge at version 0 to version 1. Version 1 has no registry
   release and is not above the CTM, so the crossing lands consistently.
2. The chain crosses the bootstrap edge onto release `200`.

At the end `SysInv` holds, and chain `5` is at version 2 routing exactly release `200`. -/
def Properties.LegacyCatchUpWitness : Prop :=
  SysInv wX.W wLagX0.sys ∧ wLagSys.ctm.legacy 0 = LegacyCut.opaque ∧
    (¬ ∃ s', Step wWorld wLagSys (.transition 5) s') ∧
    (¬ ∃ s', Step wWorld wLagSys (.bootstrapReset 5) s') ∧
    (∀ l ∈ wCatchUpRun, l.ExecTame wX) ∧
    ∃ s, LRunOk wX wLagX0 wCatchUpRun s ∧ SysInv wX.W s.sys ∧
      ∃ c, s.sys.chains 5 = some c ∧ c.pv = 2 ∧ s.sys.ctm.relAt 2 = 200 ∧
        c.routing = rowsRouting (wWorld.relRows 200)

end Contracts.ChainTypeManager.LegacyCrossing
