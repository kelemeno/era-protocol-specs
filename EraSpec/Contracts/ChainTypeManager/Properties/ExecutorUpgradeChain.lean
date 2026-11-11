import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorUpgradeChain

/-!
# Properties: the executor's `upgradeChain`, and what a replacement must report

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ExecutorUpgradeChain`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorUpgradeChain`.

## Safety is not affected

* **`upgradeChain` runs the edge its argument names.** A successful `upgradeChain(t, id)` is an
  `ExecutorForward` `upgradeChain` step, `t` is the transition the CTM commits at the chain's
  version, and the chain lands on `t.newProtocolVersion()`, the version the `ChainUpgradeApplied`
  event reports (`UpgradeChainRunsTheCommittedEdge`).
* **Refined runs are executor runs** (`RefinedRunIsAnExecutorRun`), so every result of
  `ExecutorForward` carries over. In particular the routing headline holds along tame refined
  runs with no premise on what replacements report
  (`RefinedTameRunKeepsChainsOnTheirRelease`).
* **And executor runs are refined runs.** Every `ExecutorForward` run is a refined run that never
  uses `upgradeChain`, each crossing being the owner's `forward` of the CTM call
  (`ExecutorRunsNeedNoUpgradeChain`). So both models reach exactly the same states.

## Liveness depends on what the committed transition reports

* **When `upgradeChain` is enabled.** For some argument, exactly when the chain can cross its
  edge at all and the transition committed at the chain's version reports that version
  (`UpgradeChainEnabledIff`).
* **Part (a).** When every committed slot reports its version, `upgradeChain` relates exactly
  what `ExecutorForward`'s step relates (`ReportingSlotsMakeUpgradeChainTheTransition`). This
  stays so along tame runs whose forwarded replacements report their departing release's
  version, as every `CTMTransition` does; then `upgradeChain` is enabled exactly when the chain
  admin's direct call is (`GenuineReplacementsKeepUpgradeChainLive`).
* **A misreporting slot is frozen.** If slot `v` holds a transition reporting another version,
  no commit and no replacement ever rewrites slot `v` (`MisreportingSlotIsFrozen`), so along
  every tame run no chain at `v` has an `upgradeChain` step (`MisreportingSlotStaysFrozen`).
  The replacement mechanism cannot repair the slot.
* **Part (b), the countermodel.** A tame `forward` replacing `300` by `500`, which reports
  version `7`, kills `upgradeChain` for chain `0` at version 1 for good, while the chain admin's
  direct call and a forwarded CTM call still take chain `0` to release `200`
  (`NonGenuineReplacementBricksUpgradeChain`).

The CTM's missing departure check on `replaceUpgradeTransition` therefore costs the liveness of
the executor's fixed entry point, and of further replacement of that slot. It does not cost
safety, and it does not stop the chain from upgrading.
-/

namespace Contracts.ChainTypeManager

/-! ## Safety -/

/-- **`upgradeChain` RUNS THE EDGE ITS ARGUMENT NAMES.** A successful `upgradeChain(t, id)` is
the `ExecutorForward` step `XStep.upgradeChain` between the same states. Its argument `t` is the
transition the CTM commits at the chain's version (`upgradeTransition[c.pv]`), and the chain
lands on `t.newProtocolVersion()`, which is what `ChainUpgradeApplied` reports
(`CTMUpgradeExecutor.sol:101`). -/
def Properties.UpgradeChainRunsTheCommittedEdge : Prop :=
  ∀ (X : XConfig) (s s' : XState) (t : Address) (id : ChainId),
    UStep X s (.upgradeChain t id) s' →
    XStep X s (.upgradeChain id) s' ∧
      ∃ c c', s.sys.chains id = some c ∧ s.sys.ctm.ut c.pv = t ∧
        s'.sys.chains id = some c' ∧ c'.pv = (X.W.tr t).new

/-- **EVERY REFINED RUN IS AN EXECUTOR RUN.** Mapping each transaction to its `ExecutorForward`
label (`ULabel.toX`) turns a refined run into an `ExecutorForward` run between the same states.
So every result `ExecutorForward` proves for executor runs (`TameRunPreservesSysInv`,
`TameRunKeepsChainsOnTheirRelease`) holds for refined runs. -/
def Properties.RefinedRunIsAnExecutorRun : Prop :=
  ∀ (X : XConfig) (s s' : XState) (us : List ULabel),
    URun X s us s' → XRun X s (us.map ULabel.toX) s'

/-- **EXECUTOR RUNS NEED NO `upgradeChain`.** Every `ExecutorForward` run is a refined run between
the same states in which no transaction is the executor's `upgradeChain`: each crossing is the
owner's `forward` of `CTM.upgradeChainFromVersion` (`ULabel.ofX`). The translation keeps every
transaction's tameness. With `RefinedRunIsAnExecutorRun`, the refined model and `ExecutorForward`
reach exactly the same states from any start: the getter lookup removes an entry point, never a
state. -/
def Properties.ExecutorRunsNeedNoUpgradeChain : Prop :=
  ∀ (X : XConfig) (s s' : XState) (xs : List XLabel), XRun X s xs s' →
    URun X s (xs.map ULabel.ofX) s' ∧ (∀ x, (ULabel.ofX x).Tame X ↔ x.Tame X) ∧
      ∀ u ∈ xs.map ULabel.ofX, ∀ t id, u ≠ .upgradeChain t id

/-- **THE ROUTING HEADLINE HOLDS ALONG REFINED RUNS, WHATEVER THE REPLACEMENTS REPORT.** Along
any refined run of tame transactions from a state satisfying `SysInv`, with reinitializers that
move at most their own proxy: every chain at a version `v` with a release `R_v` routes exactly
`R_v`, and `R_v` is a release of version `v`. Nothing is assumed about the transitions a
`forward` installs as replacements. -/
def Properties.RefinedTameRunKeepsChainsOnTheirRelease : Prop :=
  ∀ (X : XConfig) (s s' : XState) (us : List ULabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    SysInv X.W s.sys → URun X s us s' → (∀ u ∈ us, u.Tame X) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      X.W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (X.W.relRows (s'.sys.ctm.relAt c.pv))

/-! ## When `upgradeChain` is enabled -/

/-- **`upgradeChain` IS ENABLED EXACTLY WHEN THE CHAIN CAN CROSS AND ITS SLOT REPORTS ITS
VERSION.** In every state: some `upgradeChain(t, id)` succeeds if and only if chain `id` is
registered, the transition the CTM commits at the chain's version `v` reports
`oldProtocolVersion() = v`, and the chain can cross its edge (`Step.transition`). No premise. -/
def Properties.UpgradeChainEnabledIff : Prop :=
  ∀ (X : XConfig) (s : XState) (id : ChainId),
    (∃ t s', UStep X s (.upgradeChain t id) s') ↔
      ∃ c, s.sys.chains id = some c ∧ (X.W.tr (s.sys.ctm.ut c.pv)).old = c.pv ∧
        ∃ sys', Step X.W s.sys (.transition id) sys'

/-- **PART (a): WITH REPORTING SLOTS, `upgradeChain` IS EXACTLY THE TRANSITION STEP.** In a state
where every committed slot holds a transition reporting that slot as its `oldProtocolVersion()`,
`upgradeChain(t, id)` succeeds for some `t` and reaches `s'` exactly when `ExecutorForward`'s
`XStep.upgradeChain` reaches `s'`. -/
def Properties.ReportingSlotsMakeUpgradeChainTheTransition : Prop :=
  ∀ (X : XConfig) (s s' : XState) (id : ChainId), SlotsReport X.W s.sys.ctm →
    ((∃ t, UStep X s (.upgradeChain t id) s') ↔ XStep X s (.upgradeChain id) s')

/-- **GENUINE REPLACEMENTS KEEP `upgradeChain` LIVE.** Take a refined run of tame transactions,
with reinitializers that move at most their own proxy. It starts from a state satisfying
`CtmInv` whose committed slots report their version; a fresh CTM qualifies, since it has no
committed slot. Every replacement the run forwards reports its departing release's version
(`(W.tr r).old = W.relVersion (W.tr r).fromRel`), as every `CTMTransition` does
(`CTMTransition.sol:61-64`). Then at the end every committed slot still reports its version, and
for every chain `upgradeChain(t, id)` reaches a state for some `t` exactly when the chain admin's
direct `Admin.upgradeChainFromVersion` does. -/
def Properties.GenuineReplacementsKeepUpgradeChainLive : Prop :=
  ∀ (X : XConfig) (s s' : XState) (us : List ULabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    CtmInv X.W s.sys.ctm → SlotsReport X.W s.sys.ctm → URun X s us s' →
    (∀ u ∈ us, u.Tame X) →
    (∀ e r, (∃ u ∈ us, u.ForwardsReplace e r) →
      (X.W.tr r).old = X.W.relVersion (X.W.tr r).fromRel) →
    SlotsReport X.W s'.sys.ctm ∧
      ∀ id s'', (∃ t, UStep X s' (.upgradeChain t id) s'') ↔
        ∃ old, UStep X s' (.adminUpgrade id old) s''

/-! ## A misreporting slot -/

/-- **A SLOT HOLDING A MISREPORTING TRANSITION IS FROZEN.** In a state satisfying `CtmInv`, if
slot `v` holds a transition whose `oldProtocolVersion()` is not `v`, no run of CTM writers
changes slot `v`. A commit writes the slot of the current version, which lies above every
committed slot. `replaceUpgradeTransition(e, r)` finds its slot through `e.oldProtocolVersion()`
and requires `e` to be committed there (`ChainTypeManager.sol:433-437`). To rewrite slot `v` it
would need an `e` that reports `v` and is committed at `v`, and the only transition committed at
`v` reports another version. So replacement cannot repair the slot. -/
def Properties.MisreportingSlotIsFrozen : Prop :=
  ∀ (W : World) (s s' : CTM) (ops : List Op) (v : ℕ), CtmInv W s → s.ut v ≠ 0 →
    (W.tr (s.ut v)).old ≠ v → CRun W s ops s' → s'.ut v = s.ut v

/-- **AND THEN `upgradeChain` IS DEAD AT THAT VERSION FOR GOOD.** Along any refined run of tame
transactions, with reinitializers that move at most their own proxy, from a state satisfying
`CtmInv` in which slot `v` holds a transition whose `oldProtocolVersion()` is not `v`: slot `v`
is unchanged at the end, and no chain at version `v` has an `upgradeChain` step, for any
argument. -/
def Properties.MisreportingSlotStaysFrozen : Prop :=
  ∀ (X : XConfig) (s s' : XState) (us : List ULabel) (v : ℕ),
    ProxyUpgradeCurrent.ReinitFrames X.rc → CtmInv X.W s.sys.ctm → s.sys.ctm.ut v ≠ 0 →
    (X.W.tr (s.sys.ctm.ut v)).old ≠ v → URun X s us s' → (∀ u ∈ us, u.Tame X) →
    s'.sys.ctm.ut v = s.sys.ctm.ut v ∧
      ∀ id c, s'.sys.chains id = some c → c.pv = v →
        ¬ ∃ t s'', UStep X s' (.upgradeChain t id) s''

/-! ## Part (b): the countermodel -/

/-- **A NON-GENUINE REPLACEMENT BRICKS THE EXECUTOR'S `upgradeChain`, NOT THE CHAIN.** Start
from the fresh witness system, which satisfies `SysInv`; its reinitializers satisfy
`ReinitFrames`. Chain `0` is created at version 1 on
release `100`, and `300` (1→2) is committed through `applyCTMUpgrade`. At that point
`upgradeChain(300, 0)` succeeds. Instead, a tame `forward` replaces `300` by `500`. `500` departs
from the same release `100` and lands on the same release `200`, but reports
`oldProtocolVersion() = 7`, so it is not genuine. Afterwards `SysInv` holds, chain `0` is still
at version 1, slot 1 holds `500`, and:

* no `upgradeChain(t, 0)` succeeds, for any `t`. That includes `500`, the argument the NatSpec
  prescribes after a replacement (`ICTMUpgradeExecutor.sol:55-56`), and the replaced `300`;
* this lasts: along every tame continuation, slot 1 still holds `500`, and no chain at version 1
  has an `upgradeChain` step;
* the chain admin's direct `Admin.upgradeChainFromVersion(_, 1)` succeeds, and so does the
  owner's `forward` of `CTM.upgradeChainFromVersion(0, 1)`. Each takes chain `0` to version 2,
  routing exactly release `200`, and `SysInv` still holds.

So `GenuineReplacementsKeepUpgradeChainLive` needs its premise on replacements. -/
def Properties.NonGenuineReplacementBricksUpgradeChain : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧ SysInv wX.W wX0.sys ∧
    ∃ s1 s, URun wX wX0 [.x (.env (.genesis 0)), .x (.commit 300)] s1 ∧
      (∃ s', UStep wX s1 (.upgradeChain 300 0) s') ∧
      UStep wX s1 (.x (.forward [.sys (.ctm (.replace 300 500))])) s ∧
      ULabel.Tame wX (.x (.forward [.sys (.ctm (.replace 300 500))])) ∧
      SysInv wX.W s.sys ∧
      (∃ c, s.sys.chains 0 = some c ∧ c.pv = 1) ∧ s.sys.ctm.ut 1 = 500 ∧
      (wWorld.tr 500).old = 7 ∧ ¬ wWorld.Genuine 500 ∧
      (¬ ∃ t s', UStep wX s (.upgradeChain t 0) s') ∧
      (∀ us s'', URun wX s us s'' → (∀ u ∈ us, u.Tame wX) →
        s''.sys.ctm.ut 1 = 500 ∧
          ∀ id c, s''.sys.chains id = some c → c.pv = 1 →
            ¬ ∃ t s''', UStep wX s'' (.upgradeChain t id) s''') ∧
      (∃ s', UStep wX s (.adminUpgrade 0 1) s' ∧ SysInv wX.W s'.sys ∧
        ∃ c, s'.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)) ∧
      (∃ s', UStep wX s (.x (.forward [.sys (.transition 0)])) s' ∧ SysInv wX.W s'.sys ∧
        ∃ c, s'.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200))

/-! ## Witnesses -/

/-- **THE PREMISES ARE MET BY A REAL RUN WITH A GENUINE REPLACEMENT.** Start from the fresh
witness system. It satisfies `SysInv` and has no committed slot, so every slot reports its
version; the reinitializers satisfy `ReinitFrames`. Create chain `0`, commit `300` (1→2) through
`applyCTMUpgrade`, and `forward` its replacement by the genuine `400`. Every transaction is
tame, and the one replacement forwarded reports its departing release's version. Afterwards:

* slot 1 holds `400`, and every slot reports its version;
* the replaced `300` no longer works as the argument of `upgradeChain`: the replaced object
  "stops working at once" (`protocol-docs/ecosystem-upgrade-coordination.md:192-193`);
* `upgradeChain(400, 0)` takes chain `0` to version 2, whose release `200` it then routes
  exactly. -/
def Properties.ExecutorUpgradeChainWitness : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧ SysInv wX.W wX0.sys ∧
    SlotsReport wX.W wX0.sys.ctm ∧
    (∀ u ∈ [ULabel.x (.env (.genesis 0)), .x (.commit 300),
      .x (.forward [.sys (.ctm (.replace 300 400))]), .upgradeChain 400 0], u.Tame wX) ∧
    (∀ e r, (∃ u ∈ [ULabel.x (.env (.genesis 0)), .x (.commit 300),
        .x (.forward [.sys (.ctm (.replace 300 400))])], u.ForwardsReplace e r) →
      (wWorld.tr r).old = wWorld.relVersion (wWorld.tr r).fromRel) ∧
    ULabel.ForwardsReplace 300 400 (.x (.forward [.sys (.ctm (.replace 300 400))])) ∧
    ∃ s s', URun wX wX0 [.x (.env (.genesis 0)), .x (.commit 300),
        .x (.forward [.sys (.ctm (.replace 300 400))])] s ∧
      s.sys.ctm.ut 1 = 400 ∧ SlotsReport wX.W s.sys.ctm ∧
      (¬ ∃ s'', UStep wX s (.upgradeChain 300 0) s'') ∧
      UStep wX s (.upgradeChain 400 0) s' ∧
      ∃ c, s'.sys.chains 0 = some c ∧ c.pv = 2 ∧ s'.sys.ctm.relAt 2 = 200 ∧
        c.routing = rowsRouting (wRows 200)

/-- **A MISREPORTING SLOT EXISTS, CANNOT BE REPLACED, AND OUTLASTS LATER COMMITS.** From
`initialize(100)`, commit `300` and replace it by `500`, as in
`NonGenuineReplacementBreaksSlotVersion`. The state satisfies `CtmInv`, and slot 1 holds `500`,
which reports `7`. Replacing `500` by anything reverts, because `replaceUpgradeTransition` looks
`500` up at slot 7, where nothing is committed (`ChainTypeManager.sol:433-437`). The CTM still
moves on: committing `600` (2→3) succeeds and leaves slot 1 at `500`. -/
def Properties.MisreportingSlotWitness : Prop :=
  ∃ c c', CRun wWorld (initState wWorld 100) [.commit 300, .replace 300 500] c ∧
    CtmInv wWorld c ∧ c.ut 1 = 500 ∧ (wWorld.tr (c.ut 1)).old ≠ 1 ∧
    (∀ r, ¬ ∃ c'', CStep wWorld c (.replace 500 r) c'') ∧
    CRun wWorld c [.commit 600] c' ∧ c'.ut 1 = 500 ∧ c'.pv = 3

end Contracts.ChainTypeManager
