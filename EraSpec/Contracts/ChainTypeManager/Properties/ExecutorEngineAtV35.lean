import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorEngineAtV35

/-!
# Properties: `applyInfrastructureUpgrade` at `draft/v0.35.0`, with an arbitrary engine

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ExecutorEngineAtV35` (commit
`b17415d20`). Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorEngineAtV35`.

## What the executor checks, and what it does not

Whatever engine the transition pins, a successful leg establishes only this
(`ExecutorChecksAfterAnyEngine`): the object and the engine have code, the object is of the CTM
domain with an inventory of the domain's length, the CTM's `admin()` was not the `ProxyAdmin`
before the leg, every row's proxy is at its `implNew`, the executor's `owner`/`pendingOwner` are
unchanged, and the domain holders are unchanged up to a collision of the hash it compares on the
logged pair (before, after). The pre-check and each of the three post-checks reject some witness
leg whose engine code succeeds (`CtmAdminPrecheckRefusesTheLeg`,
`OwnershipCheckRefusesAnEngineNomination`, `HoldersCheckRefusesAnEngineNomination`,
`RowsCheckRefusesAHookThatMovesARowProxy`), and the collision case is reachable when the hash
does not separate the pair (`HoldersCollisionCaseIsReachable`). An engine can make every call a
`forward` can, inside the fixed entry point (`EveryForwardIsAnEngineLeg`). So `ExecutorForward`'s
run invariants, whose premise for an infrastructure step was only "no row names the CTM proxy",
fail at `b17415d20`, even for genuine transition objects (`TameRunsNoLongerPreserveSysInv`,
`TameRunsNoLongerKeepChainsOnTheirRelease`, `FixedEntrypointsNoLongerMoveOnlyAlongRows`).

## With the genuine row engine nothing changes

If the transition pins `DefaultProxyUpgradeEngine`, the leg is `ExecutorForward`'s
infrastructure step, and conversely, given the checks the executor and engine now make
(`DefaultEngineLegIsAnInfraStep`, `InfraStepIsADefaultEngineLeg`). The default engine meets the
review condition `EngineReviewed` (`DefaultEngineIsReviewed`), and the routing headline holds
across `b17415d20` runs whose transitions pin it (`DefaultEngineRunKeepsChainsOnTheirRelease`).

## What governance must check

Two conditions on the engine, both defined in the Specs file; the executor checks neither.

* **`EngineIsTame`** (the engine makes no break-glass cut and does not move the CTM proxy: every
  leg is a run of tame `e561b9cc2` transactions) is what the CTM's invariants need. With
  `ReinitFrames` and tame transactions as at `e561b9cc2`, a run whose engines are tame is a tame
  `ExecutorForward` run (`TameEngineRunIsATameExecutorRun`), so `SysInv` holds, the CTM's version
  never decreases, the CTM proxy does not move (`TameEngineRunPreservesSysInv`), and every chain
  at `v` routes `R_v` (`TameEngineRunKeepsChainsOnTheirRelease`).
* **`EngineReviewed`** (the engine runs `DefaultProxyUpgradeEngine`'s core on the manifest's rows,
  and its hooks make only CTM calls that are not break-glass cuts) is what the row library's
  source check needs. A reviewed leg is a `forward`, the `e561b9cc2` infrastructure step and a
  `forward` (`ReviewedLegIsAnExecutorRun`), so for rows not naming the CTM proxy a reviewed
  engine is tame (`ReviewedEngineIsTame`, `ReviewedRunKeepsChainsOnTheirRelease`). Beyond that,
  the fixed entry points move proxies only along rows' edges, for any rows
  (`ReviewedLegsMoveProxiesOnlyAlongRows`), and a stale object reverts
  (`ReviewedEngineRefusesStaleRows`).

Each part is load-bearing. Each countermodel below uses a genuine transition object whose rows do
not name the CTM proxy, passes every executor check, and violates one part:

| Engine | Tame | Reviewed | Countermodel |
|---|---|---|---|
| `_afterSwaps` makes a break-glass cut | no | no | `CuttingEngineBreaksTheHeadline` |
| `_afterSwaps` upgrades the CTM proxy | no | no | `CtmSwappingEngineBreaksSysInv` |
| `_afterSwaps` upgrades a proxy no row names | yes | no | `ProxyMovingEngineMovesAnUnnamedProxy` |
| `_beforeSwaps` moves a row's proxy | yes | no | `BeforeHookDefeatsTheSourceCheck` |
| swaps without `applyRows` | yes | no | `DirectEngineSkipsTheSourceCheck` |

## Witnesses

| Witness | Meets every premise of |
|---|---|
| `ReviewedRunWitness` | `ExecutorChecksAfterAnyEngine`, `DefaultEngineLegIsAnInfraStep`, `InfraStepIsADefaultEngineLeg`, `DefaultEngineIsReviewed`, `ReviewedLegIsAnExecutorRun`, `ReviewedEngineIsTame`, `TameEngineRunIsATameExecutorRun`, `TameEngineRunPreservesSysInv`, `TameEngineRunKeepsChainsOnTheirRelease`, `ReviewedRunKeepsChainsOnTheirRelease`, `ReviewedLegsMoveProxiesOnlyAlongRows` |
| `DefaultEngineRunWitness` | `DefaultEngineRunKeepsChainsOnTheirRelease` |
| `EveryForwardIsAnEngineLegWitness` | `EveryForwardIsAnEngineLeg` (both sides of the equivalence hold) |
| `DirectEngineSkipsTheSourceCheck` (its first half) | `ReviewedEngineRefusesStaleRows` |

The negative statements, the refusals and the countermodels are concrete: they are their own
witnesses.
-/

namespace Contracts.ChainTypeManager.ExecutorEngineAtV35

/-! ## What the executor checks, whatever the engine -/

/-- **WHAT THE EXECUTOR ESTABLISHES, WHATEVER THE ENGINE.** After a successful
`applyInfrastructureUpgrade(T)`: the object and its engine have code, the object is of the CTM
domain and its inventory has the CTM domain's length, the CTM's `admin()` was not the
`ProxyAdmin` in the start state, every row's proxy is at its `implNew`, the executor's `owner`
and `pendingOwner` are unchanged, and the domain holders are unchanged unless the pair (before,
after) is a collision of `holdersHash`. -/
def Properties.ExecutorChecksAfterAnyEngine : Prop :=
  ∀ (X : V35Config) (T : V35Transition) (s s' : V35State), V35Step X s (.infra T) s' →
    X.base.rc.hasCode T.addr ∧ T.domain = .ctm ∧ X.base.rc.hasCode T.engine ∧
    T.inventory.length = X.inventoryLength .ctm ∧ s.holders.ctmAdmin ≠ X.proxyAdmin ∧
    ProxyUpgradeCurrent.RowsApplied s'.x.impl T.rows ∧
    s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner ∧
    (s'.holders = s.holders ∨
      (s'.holders ≠ s.holders ∧ X.holdersHash s'.holders = X.holdersHash s.holders))

/-- **AN ENGINE CAN DO WHAT A `forward` CAN.** Take a CTM-domain object with code whose inventory
has the CTM domain's length and whose engine has code and only makes the calls `calls`, and a
start state in which the CTM's `admin()` is not the `ProxyAdmin`. Then `applyInfrastructureUpgrade`
succeeds from `s` and ends in `x'` with the executor's ownership and the holders as they were,
exactly when `forward(calls)` (as `ExecutorForward` models it) succeeds from `s` and ends in `x'`
and every row's proxy is at its `implNew` in `x'`. The modelled calls go to the CTM and its
`ProxyAdmin`, so the code check `forward` makes at `b17415d20` does not separate the two. The
forwards of `ExecutorForward`'s countermodels (`ForwardDowngradesAProxy`,
`ForwardCtmSwapBreaksInvariants`) therefore run inside the fixed entry point once its rows are
applied. Unlike a `forward`, the leg emits no `CallForwarded`. The equivalence is in the model:
the one omitted reject-only check that separates the two sides is `_domainHolders` reverting for a
ServerNotifier the `ProxyAdmin` no longer administers (`ProxyUpgradeExecutorBase.sol:112-114`;
`MODEL-CTM-ENGINE-V35`), which can make the real leg revert where the modelled `forward` succeeds.
(`onlyOwner` guards `forward` too, and `_checkPostconditions` belongs to the default engine, not
the `callingEngine` quantified here.) -/
def Properties.EveryForwardIsAnEngineLeg : Prop :=
  ∀ (X : V35Config) (T : V35Transition) (s : V35State) (calls : List FCall) (x' : XState),
    X.code T.engine = callingEngine X.base calls → X.base.rc.hasCode T.addr → T.domain = .ctm →
    X.base.rc.hasCode T.engine → s.holders.ctmAdmin ≠ X.proxyAdmin →
    T.inventory.length = X.inventoryLength .ctm →
    (V35Step X s (.infra T) { s with x := x' } ↔
      XStep X.base s.x (.forward calls) x' ∧ ProxyUpgradeCurrent.RowsApplied x'.impl T.rows)

/-- **AT `b17415d20` TAME RUNS NO LONGER PRESERVE THE INVARIANT.** `ExecutorForward`'s
`TameRunPreservesSysInv` without a premise on the engines is false at `b17415d20`, even when every
applied object is a genuine `ProxyUpgradeTransition`: some configuration with `ReinitFrames` has
a run of tame transactions from a `SysInv` state that ends outside `SysInv`. -/
def Properties.TameRunsNoLongerPreserveSysInv : Prop :=
  ¬ ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → SysInv X.base.W s.x.sys → V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → T.Genuine (X.inventoryLength T.domain)) →
    SysInv X.base.W s'.x.sys

/-- **AND NO LONGER KEEP EVERY CHAIN ON ITS RELEASE.** `ExecutorForward`'s
`TameRunKeepsChainsOnTheirRelease` without a premise on the engines is false at `b17415d20`, even
for genuine objects. -/
def Properties.TameRunsNoLongerKeepChainsOnTheirRelease : Prop :=
  ¬ ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → SysInv X.base.W s.x.sys → V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → T.Genuine (X.inventoryLength T.domain)) →
    ∀ id c, s'.x.sys.chains id = some c → s'.x.sys.ctm.relAt c.pv ≠ 0 →
      c.routing = rowsRouting (X.base.W.relRows (s'.x.sys.ctm.relAt c.pv))

/-- **AND THE FIXED ENTRY POINTS NO LONGER MOVE PROXIES ONLY ALONG ROWS.**
`ExecutorForward`'s `FixedEntrypointsMoveProxiesOnlyAlongRows` (and its `AnyRows` form) without
a premise on the engine is false at `b17415d20`, even for a genuine object, whose rows name
distinct proxies. -/
def Properties.FixedEntrypointsNoLongerMoveOnlyAlongRows : Prop :=
  ¬ ∀ (X : V35Config) (s s' : V35State) (l : V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → V35Step X s l s' → (∀ calls, l ≠ .forward calls) →
    (∀ T, l = .infra T → T.Genuine (X.inventoryLength T.domain)) → V35MovesOnlyAlongRows s s' l

/-! ## The pre-check and each post-check reject some leg -/

/-- **THE PRE-CHECK ON THE CTM'S ADMIN REJECTS.** From the fresh witness state the
default-engine leg of `wTAB 70` succeeds; from the same state with the CTM's `admin()` set to the
`ProxyAdmin`, it reverts, although the engine's code still runs (the pre-check reads only the
start state). -/
def Properties.CtmAdminPrecheckRefusesTheLeg : Prop :=
  wV0.holders.ctmAdmin ≠ wV35.proxyAdmin ∧ (∃ s', V35Step wV35 wV0 (.infra (wTAB 70)) s') ∧
    (∃ s', wV35.code (wTAB 70).engine (wTAB 70)
      { wV0 with holders := { wHolders with ctmAdmin := wV35.proxyAdmin } } s') ∧
    ¬ ∃ s', V35Step wV35 { wV0 with holders := { wHolders with ctmAdmin := wV35.proxyAdmin } }
      (.infra (wTAB 70)) s'

/-- **THE OWNERSHIP POST-CHECK REJECTS AN ENGINE THAT NOMINATES A NEW OWNER OF THE EXECUTOR.**
Engine `77` runs `DefaultProxyUpgradeEngine`'s core on the genuine object `wTAB 77` (rows applied,
holders unchanged) and writes `66` into the executor's `pendingOwner`. The engine's code succeeds
from the fresh witness state; the leg reverts. -/
def Properties.OwnershipCheckRefusesAnEngineNomination : Prop :=
  (wTAB 77).Genuine (wV35.inventoryLength .ctm) ∧ V35Label.Tame wV35 (.infra (wTAB 77)) ∧
    (∃ s', wV35.code (wTAB 77).engine (wTAB 77) wV0 s' ∧
      ProxyUpgradeCurrent.RowsApplied s'.x.impl (wTAB 77).rows ∧ s'.holders = wV0.holders ∧
      s'.pendingOwner ≠ wV0.pendingOwner) ∧
    ¬ ∃ s', V35Step wV35 wV0 (.infra (wTAB 77)) s'

/-- **THE HOLDERS POST-CHECK REJECTS AN ENGINE THAT NOMINATES A NEW OWNER OF THE CTM.** Engine
`78` runs `DefaultProxyUpgradeEngine`'s core on the genuine object `wTAB 78` (rows applied, the
executor's ownership unchanged) and calls the CTM's `transferOwnership(66)`. With the witness
hash, which separates the two holder values, the engine's code succeeds from the fresh witness
state and the leg reverts. -/
def Properties.HoldersCheckRefusesAnEngineNomination : Prop :=
  (wTAB 78).Genuine (wV35.inventoryLength .ctm) ∧ V35Label.Tame wV35 (.infra (wTAB 78)) ∧
    (∃ s', wV35.code (wTAB 78).engine (wTAB 78) wV0 s' ∧
      ProxyUpgradeCurrent.RowsApplied s'.x.impl (wTAB 78).rows ∧ s'.owner = wV0.owner ∧
      s'.pendingOwner = wV0.pendingOwner ∧ s'.holders.ctmPendingOwner = 66 ∧
      wV35.holdersHash s'.holders ≠ wV35.holdersHash wV0.holders) ∧
    ¬ ∃ s', V35Step wV35 wV0 (.infra (wTAB 78)) s'

/-- **THE ROWS POST-CHECK REJECTS A HOOK THAT MOVES A ROW'S PROXY AFTER THE SWAPS.** Engine `79` is
a `DefaultProxyUpgradeEngine` subclass whose `_afterSwaps` upgrades proxy `5`, which a row of the
genuine object `wTAB 79` names, to `42`. The engine's code succeeds from the fresh witness state,
with the executor's ownership and the holders unchanged and proxy `5` off its row's `implNew`;
the leg reverts at the executor's second `requireRowsApplied`
(`ProxyUpgradeExecutorBase.sol:99-103`). -/
def Properties.RowsCheckRefusesAHookThatMovesARowProxy : Prop :=
  (wTAB 79).Genuine (wV35.inventoryLength .ctm) ∧ V35Label.Tame wV35 (.infra (wTAB 79)) ∧
    (∃ s', wV35.code (wTAB 79).engine (wTAB 79) wV0 s' ∧ s'.owner = wV0.owner ∧
      s'.pendingOwner = wV0.pendingOwner ∧ s'.holders = wV0.holders ∧ s'.x.impl 5 = 42 ∧
      ¬ ProxyUpgradeCurrent.RowsApplied s'.x.impl (wTAB 79).rows) ∧
    ¬ ∃ s', V35Step wV35 wV0 (.infra (wTAB 79)) s'

/-- **THE COLLISION CASE OF `ExecutorChecksAfterAnyEngine` IS REACHABLE.** With a holders hash
that does not separate the pair (here a constant), the leg of engine `78` succeeds and moves the
CTM's `pendingOwner` to `66`: the holders changed and the hash collides on the leg's own logged
pair (before, after). So the holders guarantee is exactly as strong as the hash on that pair. -/
def Properties.HoldersCollisionCaseIsReachable : Prop :=
  ∃ s', V35Step wV35Blind wV0 (.infra (wTAB 78)) s' ∧ s'.holders.ctmPendingOwner = 66 ∧
    s'.holders ≠ wV0.holders ∧ wV35Blind.holdersHash s'.holders = wV35Blind.holdersHash wV0.holders

/-! ## The genuine row engine -/

/-- **WITH `DefaultProxyUpgradeEngine` THE LEG IS THE `e561b9cc2` INFRASTRUCTURE STEP.** If the
transition pins the genuine row engine, a successful `applyInfrastructureUpgrade(T)` at
`b17415d20` relates the CTM, its chains and the implementations as `ExecutorForward`'s
`applyInfrastructureUpgrade` of the same object does, the executor owns its `ProxyAdmin`, and
the executor's `owner` and `pendingOwner` are unchanged. -/
def Properties.DefaultEngineLegIsAnInfraStep : Prop :=
  ∀ (X : V35Config) (T : V35Transition) (s s' : V35State), EngineIsDefault X T →
    V35Step X s (.infra T) s' →
    XStep X.base s.x (.infra T.toCurrent) s'.x ∧ X.base.rc.adminOwner = X.base.rc.self ∧
      s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner

/-- **AND EVERY `e561b9cc2` INFRASTRUCTURE STEP IS SUCH A LEG**, given the checks the `b17415d20`
leg makes that `ExecutorForward`'s infrastructure step does not include: the executor owns its
`ProxyAdmin` (`DefaultProxyUpgradeEngine.sol:33-37`), the engine has code
(`ProxyUpgradeExecutorBase.sol:63`), the CTM's `admin()` is not the `ProxyAdmin` (`:72-77`), and
the inventory has the CTM domain's length (`:99-102`). The leg can leave the executor's ownership
and the domain holders as they were. With `DefaultEngineLegIsAnInfraStep`: on the executor-model
state, a leg pinning the genuine row engine is the `e561b9cc2` infrastructure step restricted by
these checks, so `ExecutorForward`'s results about that step describe it. This holds in the
model: the reject-only checks it omits (`onlyOwner`, `_checkPostconditions`, and
`_domainHolders` reverting for a ServerNotifier the `ProxyAdmin` no longer administers,
`ProxyUpgradeExecutorBase.sol:112-114`; `MODEL-CTM-ENGINE-V35`) can make the real leg revert. -/
def Properties.InfraStepIsADefaultEngineLeg : Prop :=
  ∀ (X : V35Config) (T : V35Transition) (s : V35State) (x' : XState), EngineIsDefault X T →
    XStep X.base s.x (.infra T.toCurrent) x' → X.base.rc.adminOwner = X.base.rc.self →
    X.base.rc.hasCode T.engine → s.holders.ctmAdmin ≠ X.proxyAdmin →
    T.inventory.length = X.inventoryLength .ctm →
    V35Step X s (.infra T) { s with x := x' }

/-- **THE GENUINE ROW ENGINE MEETS THE REVIEW CONDITION**, with empty hooks. -/
def Properties.DefaultEngineIsReviewed : Prop :=
  ∀ (X : V35Config) (T : V35Transition), EngineIsDefault X T → EngineReviewed X T

/-- **THE HEADLINE AT `b17415d20` WITH THE GENUINE ROW ENGINE.** `ChainsRunTheirVersionsRelease`
across `b17415d20` executor runs: under `ReinitFrames`, from a `SysInv` state, along a run of
tame transactions (as at `e561b9cc2`) whose infrastructure transitions all pin
`DefaultProxyUpgradeEngine`, every chain at a version `v` with a release `R_v` routes exactly
`R_v`, and `R_v` is a release of version `v`. -/
def Properties.DefaultEngineRunKeepsChainsOnTheirRelease : Prop :=
  ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → SysInv X.base.W s.x.sys → V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → EngineIsDefault X T) →
    ∀ id c, s'.x.sys.chains id = some c → s'.x.sys.ctm.relAt c.pv ≠ 0 →
      X.base.W.relVersion (s'.x.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (X.base.W.relRows (s'.x.sys.ctm.relAt c.pv))

/-! ## Tame and reviewed engines -/

/-- **A REVIEWED LEG IS AN `e561b9cc2` EXECUTOR RUN.** If the engine meets `EngineReviewed`, a
successful `applyInfrastructureUpgrade(T)` relates the executor model's states as three
`ExecutorForward` transactions do: a `forward` of the `_beforeSwaps` calls, the infrastructure
step of the same object, and a `forward` of the `_afterSwaps` calls, each forwarded call a CTM
call that is not a break-glass cut. -/
def Properties.ReviewedLegIsAnExecutorRun : Prop :=
  ∀ (X : V35Config) (T : V35Transition) (s s' : V35State), EngineReviewed X T →
    V35Step X s (.infra T) s' →
    ∃ pre post : List FCall, (∀ c ∈ pre ++ post, ReviewedHookCall c) ∧
      XRun X.base s.x [.forward pre, .infra T.toCurrent, .forward post] s'.x

/-- **A REVIEWED ENGINE IS TAME** for a transition whose rows do not name the CTM proxy: its
legs are runs of tame `ExecutorForward` transactions. -/
def Properties.ReviewedEngineIsTame : Prop :=
  ∀ (X : V35Config) (T : V35Transition), EngineReviewed X T → V35Label.Tame X (.infra T) →
    EngineIsTame X T

/-- **A RUN WITH TAME ENGINES IS A TAME `e561b9cc2` EXECUTOR RUN.** If every transaction of a
`b17415d20` run is `Tame` and every infrastructure transition pins a tame engine, some run of
tame `ExecutorForward` transactions relates the same executor-model states. -/
def Properties.TameEngineRunIsATameExecutorRun : Prop :=
  ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label), V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → EngineIsTame X T) →
    ∃ xs : List XLabel, XRun X.base s.x xs s'.x ∧ ∀ x ∈ xs, x.Tame X.base

/-- **RUNS WITH TAME ENGINES PRESERVE THE INVARIANT** (`TameRunPreservesSysInv` at `b17415d20`).
Under `ReinitFrames`, from a `SysInv` state, along a run of tame transactions whose infrastructure
transitions pin tame engines: `SysInv` holds at the end, the CTM's version has not decreased, and
the CTM proxy has not moved. -/
def Properties.TameEngineRunPreservesSysInv : Prop :=
  ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → SysInv X.base.W s.x.sys → V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → EngineIsTame X T) →
    SysInv X.base.W s'.x.sys ∧ s.x.sys.ctm.pv ≤ s'.x.sys.ctm.pv ∧
      s'.x.impl X.base.ctmProxy = s.x.impl X.base.ctmProxy

/-- **HEADLINE AT `b17415d20`: EVERY CHAIN AT VERSION `v` RUNS `R_v`, IF THE ENGINES ARE TAME.**
(`TameRunKeepsChainsOnTheirRelease` at `b17415d20`.) Under the premises of
`TameEngineRunPreservesSysInv`, every chain at a version `v` with a release `R_v` routes exactly
`R_v`, and `R_v` is a release of version `v`. -/
def Properties.TameEngineRunKeepsChainsOnTheirRelease : Prop :=
  ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → SysInv X.base.W s.x.sys → V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → EngineIsTame X T) →
    ∀ id c, s'.x.sys.chains id = some c → s'.x.sys.ctm.relAt c.pv ≠ 0 →
      X.base.W.relVersion (s'.x.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (X.base.W.relRows (s'.x.sys.ctm.relAt c.pv))

/-- **THE HEADLINE FOR REVIEWED ENGINES.** As `TameEngineRunKeepsChainsOnTheirRelease`, with every
infrastructure transition pinning a reviewed engine. -/
def Properties.ReviewedRunKeepsChainsOnTheirRelease : Prop :=
  ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → SysInv X.base.W s.x.sys → V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → EngineReviewed X T) →
    ∀ id c, s'.x.sys.chains id = some c → s'.x.sys.ctm.relAt c.pv ≠ 0 →
      X.base.W.relVersion (s'.x.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (X.base.W.relRows (s'.x.sys.ctm.relAt c.pv))

/-- **THE FIXED ENTRY POINTS MOVE A PROXY ONLY ALONG A ROW'S EDGE, IF THE ENGINE IS REVIEWED.**
(`FixedEntrypointsMoveProxiesOnlyAlongRowsAnyRows` at `b17415d20`.) Any transaction other than
`forward` whose infrastructure transition, if any, pins a reviewed engine, with reinitializers that
move at most their own proxy, leaves every proxy where it was or moves it from a row's
`expectedOldImpl` to that row's `implNew`. No premise on the rows: the object may be
non-genuine. -/
def Properties.ReviewedLegsMoveProxiesOnlyAlongRows : Prop :=
  ∀ (X : V35Config) (s s' : V35State) (l : V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → V35Step X s l s' →
    (∀ calls, l ≠ .forward calls) → (∀ T, l = .infra T → EngineReviewed X T) →
    V35MovesOnlyAlongRows s s' l

/-- **A REVIEWED ENGINE REFUSES A STALE OBJECT** (the row library's source check). Under
`ReinitFrames`, for a transition whose rows name distinct proxies (a genuine object's do) and
which pins a reviewed engine: if some row's proxy is at neither its `expectedOldImpl` nor its
`implNew`, `applyInfrastructureUpgrade` reverts. A replayed stale object cannot downgrade a proxy
that a later upgrade moved on. -/
def Properties.ReviewedEngineRefusesStaleRows : Prop :=
  ∀ (X : V35Config) (T : V35Transition) (s : V35State) (r : ProxyUpgradeCurrent.Row),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → EngineReviewed X T →
    T.rows.Pairwise (fun a b => a.proxy ≠ b.proxy) → r ∈ T.rows →
    s.x.impl r.proxy ≠ r.expectedOldImpl → s.x.impl r.proxy ≠ r.implNew →
    ¬ ∃ s', V35Step X s (.infra T) s'

/-! ## Countermodels: each part of `EngineIsTame` and `EngineReviewed` is load-bearing -/

/-- **A HOOK THAT CUTS A CHAIN BREAKS THE HEADLINE.** In the witness executor, from the fresh state
(which satisfies `SysInv`; reinitializers inert): chain `0` is created at version 1 on release
`100`, then `applyInfrastructureUpgrade` applies a genuine object with rows `5: 10 → 11` and
`6: 10 → 12`, which do not name the CTM proxy `8`, pinning a `DefaultProxyUpgradeEngine` subclass
whose `_afterSwaps` makes the break-glass cut `executeUpgrade(0, ·)`. Both transactions are `Tame`
and every executor check passes: the rows are applied, and the executor's ownership and the
holders are unchanged. Chain `0` ends at version 1, whose release is `100`, routing something
else. So the engine is neither tame nor reviewed. -/
def Properties.CuttingEngineBreaksTheHeadline : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wV35.base.rc ∧ SysInv wV35.base.W wV0.x.sys ∧
    (wTAB 72).Genuine (wV35.inventoryLength .ctm) ∧
    (∀ l ∈ [V35Label.env (.genesis 0), .infra (wTAB 72)], l.Tame wV35) ∧
    ¬ EngineIsTame wV35 (wTAB 72) ∧ ¬ EngineReviewed wV35 (wTAB 72) ∧
    ∃ s', V35Run wV35 wV0 [.env (.genesis 0), .infra (wTAB 72)] s' ∧
      s'.owner = wV0.owner ∧ s'.pendingOwner = wV0.pendingOwner ∧ s'.holders = wV0.holders ∧
      ∃ c, s'.x.sys.chains 0 = some c ∧ c.pv = 1 ∧ s'.x.sys.ctm.relAt 1 = 100 ∧
        c.routing ≠ rowsRouting (wRows 100)

/-- **A HOOK THAT SWAPS THE CTM'S CODE VOIDS THE CTM'S INVARIANTS, THROUGH THE FIXED ENTRY POINT.**
`ExecutorForward`'s `ForwardCtmSwapBreaksInvariants` at `b17415d20`. After the same tame run
(chain `0` created, `300` committed, chain `0` upgraded to version 2; `SysInv` holds), a genuine
object whose rows do not name the CTM proxy, so `Tame` as at `e561b9cc2`, pins a subclass whose
`_afterSwaps` is that countermodel's `upgradeAndCall` on the CTM proxy. Every executor check
passes. The CTM proxy moved, the CTM's version decreased, and `SysInv` fails. So the engine is
neither tame nor reviewed. -/
def Properties.CtmSwappingEngineBreaksSysInv : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wV35.base.rc ∧ (wTAB 73).Genuine (wV35.inventoryLength .ctm) ∧
    V35Label.Tame wV35 (.infra (wTAB 73)) ∧ XLabel.Tame wX (.infra (wTAB 73).toCurrent) ∧
    ¬ EngineIsTame wV35 (wTAB 73) ∧ ¬ EngineReviewed wV35 (wTAB 73) ∧
    ∃ s s', V35Run wV35 wV0 [.env (.genesis 0), .commit 300, .upgradeChain 0] s ∧
      SysInv wV35.base.W s.x.sys ∧ V35Step wV35 s (.infra (wTAB 73)) s' ∧
      s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner ∧ s'.holders = s.holders ∧
      s'.x.impl wX.ctmProxy ≠ s.x.impl wX.ctmProxy ∧
      s'.x.sys.ctm.pv < s.x.sys.ctm.pv ∧ ¬ SysInv wV35.base.W s'.x.sys

/-- **A HOOK THAT UPGRADES ANOTHER PROXY IS NOT CAUGHT.** From the fresh state, a genuine object
with rows `5: 10 → 11` and `6: 10 → 12` pins a subclass whose `_afterSwaps` upgrades proxy `7`,
which no row names, from `10` to `42`. Every executor check passes, and proxy `7` moved along no
row's edge. At `e561b9cc2` only a `forward` could do this (`ForwardDowngradesAProxy`); here it is
the fixed entry point. The engine is tame (the CTM's invariants are safe) but not reviewed. -/
def Properties.ProxyMovingEngineMovesAnUnnamedProxy : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wV35.base.rc ∧ (wTAB 75).Genuine (wV35.inventoryLength .ctm) ∧
    (wTAB 75).rows.Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    (∀ r ∈ (wTAB 75).rows, r.proxy ≠ 7) ∧ EngineIsTame wV35 (wTAB 75) ∧
    ¬ EngineReviewed wV35 (wTAB 75) ∧
    ∃ s', V35Step wV35 wV0 (.infra (wTAB 75)) s' ∧ wV0.x.impl 7 = 10 ∧ s'.x.impl 7 = 42 ∧
      s'.owner = wV0.owner ∧ s'.pendingOwner = wV0.pendingOwner ∧ s'.holders = wV0.holders ∧
      ¬ V35MovesOnlyAlongRows wV0 s' (.infra (wTAB 75))

/-- **AN ENGINE NOT BUILT ON `applyRows` SKIPS THE SOURCE CHECK.** Two default-engine legs
(`wStaleRun`) move proxy `5` from `10` to `11` (row `5: 10 → 11`) and on to `12` (row
`5: 11 → 12`). The stale first object `wTA 30 70` then names a row whose proxy is at neither end,
and the default engine, which is reviewed, refuses it. A genuine object with the same rows whose
engine only calls `ProxyAdmin.upgrade(5, 11)` (code with no `applyRows`) succeeds, every executor
check passes, and proxy `5` goes `12 → 11`, along no row's edge. That engine is tame but not
reviewed. -/
def Properties.DirectEngineSkipsTheSourceCheck : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wV35.base.rc ∧ EngineReviewed wV35 (wTA 30 70) ∧
    (wTA 30 70).Genuine (wV35.inventoryLength .ctm) ∧ (wTA 34 74).Genuine (wV35.inventoryLength .ctm) ∧
    (wTA 34 74).rows = (wTA 30 70).rows ∧
    (wTA 30 70).rows.Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    wV35.code (wTA 34 74).engine = callingEngine wV35.base [.upgradeProxy 5 11] ∧
    EngineIsTame wV35 (wTA 34 74) ∧ ¬ EngineReviewed wV35 (wTA 34 74) ∧
    ∃ s, V35Run wV35 wV0 wStaleRun s ∧ s.x.impl 5 = 12 ∧
      s.x.impl ProxyUpgradeCurrent.rowA.proxy ≠ ProxyUpgradeCurrent.rowA.expectedOldImpl ∧
      s.x.impl ProxyUpgradeCurrent.rowA.proxy ≠ ProxyUpgradeCurrent.rowA.implNew ∧
      (¬ ∃ s', V35Step wV35 s (.infra (wTA 30 70)) s') ∧
      ∃ s', V35Step wV35 s (.infra (wTA 34 74)) s' ∧ s'.x.impl 5 = 11 ∧
        s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner ∧ s'.holders = s.holders ∧
        ¬ V35MovesOnlyAlongRows s s' (.infra (wTA 34 74))

/-- **A `_beforeSwaps` HOOK THAT MOVES A ROW'S PROXY DEFEATS THE SOURCE CHECK.** After `wStaleRun`
(proxy `5` at `12`), a genuine object with the stale row `5: 10 → 11` pins a
`DefaultProxyUpgradeEngine` subclass whose `_beforeSwaps` moves proxy `5` to `10`, the row's
`expectedOldImpl`. `applyRows` then upgrades it to `11` and every executor check passes: proxy `5`
goes `12 → 11`. The executor's second `requireRowsApplied` (`ProxyUpgradeExecutorBase.sol:99-103`)
reads only the end state, where proxy `5` is at the row's `implNew`. The engine is tame but not
reviewed. -/
def Properties.BeforeHookDefeatsTheSourceCheck : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wV35.base.rc ∧ (wTA 36 76).Genuine (wV35.inventoryLength .ctm) ∧
    EngineIsTame wV35 (wTA 36 76) ∧ ¬ EngineReviewed wV35 (wTA 36 76) ∧
    ∃ s, V35Run wV35 wV0 wStaleRun s ∧ s.x.impl 5 = 12 ∧
      ∃ s', V35Step wV35 s (.infra (wTA 36 76)) s' ∧ s'.x.impl 5 = 11 ∧
        s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner ∧ s'.holders = s.holders ∧
        ¬ V35MovesOnlyAlongRows s s' (.infra (wTA 36 76))

/-! ## Witnesses -/

/-- **THE PREMISES ARE MET BY A REAL RUN, WITH A HOOK.** From the fresh witness state, which
satisfies `SysInv` (reinitializers inert, so `ReinitFrames` holds; the executor owns its
`ProxyAdmin`; the CTM's admin `50` is not the `ProxyAdmin` `60`), run `wReviewedRun`: apply
`wTAB 70` (the default engine: proxies `5` and `6` upgraded; this leg is also an `ExecutorForward`
infrastructure step), create chain `0`, commit `300`, upgrade chain `0`, then apply `wTAB 71`,
which has the same rows and pins a reviewed subclass whose `_afterSwaps` replaces the committed
transition `300` by `400` (the rows are already applied and skip themselves). Every transaction
is tame, both engines are reviewed and tame, the first is the default engine and the second is
not, both objects are genuine and they and their engines have code. At the end chain `0` is at
version 2 on release `200`, slot 1 holds `400`, proxies `5` and `6` moved, and the executor's
ownership and the holders are unchanged. -/
def Properties.ReviewedRunWitness : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wV35.base.rc ∧ SysInv wV35.base.W wV0.x.sys ∧
    wV35.base.rc.adminOwner = wV35.base.rc.self ∧ wV0.holders.ctmAdmin ≠ wV35.proxyAdmin ∧
    EngineIsDefault wV35 (wTAB 70) ∧ EngineReviewed wV35 (wTAB 70) ∧
    EngineReviewed wV35 (wTAB 71) ∧ ¬ EngineIsDefault wV35 (wTAB 71) ∧
    EngineIsTame wV35 (wTAB 70) ∧ EngineIsTame wV35 (wTAB 71) ∧
    (wTAB 70).Genuine (wV35.inventoryLength .ctm) ∧ (wTAB 71).Genuine (wV35.inventoryLength .ctm) ∧
    wV35.base.rc.hasCode (wTAB 70).addr ∧ wV35.base.rc.hasCode (wTAB 71).addr ∧
    wV35.base.rc.hasCode (wTAB 70).engine ∧ wV35.base.rc.hasCode (wTAB 71).engine ∧
    (∃ x', XStep wV35.base wV0.x (.infra (wTAB 70).toCurrent) x') ∧
    (∀ l ∈ wReviewedRun, l.Tame wV35) ∧
    ∃ s', V35Run wV35 wV0 wReviewedRun s' ∧
      s'.x.impl 5 = 11 ∧ s'.x.impl 6 = 12 ∧ s'.x.sys.ctm.ut 1 = 400 ∧ s'.x.sys.ctm.pv = 2 ∧
      s'.x.sys.ctm.relAt 2 = 200 ∧
      (∃ c, s'.x.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)) ∧
      s'.owner = wV0.owner ∧ s'.pendingOwner = wV0.pendingOwner ∧ s'.holders = wV0.holders

/-- **A DEFAULT-ENGINE RUN MEETS THE PREMISES OF `DefaultEngineRunKeepsChainsOnTheirRelease`.**
From the fresh witness state (`SysInv`, `ReinitFrames`), `wDefaultRun` applies `wTAB 70` (the
default engine), creates chain `0`, commits `300` and upgrades chain `0`. Every transaction is
tame and its one infrastructure transition pins the default engine. At the end chain `0` is at
version 2, whose release is `200`, and routes it: the conclusion is about a real chain. -/
def Properties.DefaultEngineRunWitness : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wV35.base.rc ∧ SysInv wV35.base.W wV0.x.sys ∧
    (∀ l ∈ wDefaultRun, l.Tame wV35) ∧
    (∀ T, V35Label.infra T ∈ wDefaultRun → EngineIsDefault wV35 T) ∧
    ∃ s', V35Run wV35 wV0 wDefaultRun s' ∧ s'.x.impl 5 = 11 ∧ s'.x.impl 6 = 12 ∧
      s'.x.sys.ctm.relAt 2 = 200 ∧
      ∃ c, s'.x.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)

/-- **BOTH SIDES OF `EveryForwardIsAnEngineLeg` HOLD FOR A NONEMPTY CALL LIST.** The genuine object
`wTA 34 74` (row `5: 10 → 11`) pins engine `74`, which only calls `ProxyAdmin.upgrade(5, 11)`. From
the fresh witness state every premise holds, `forward([upgrade(5, 11)])` succeeds and leaves the
row applied, and so does the leg, ending in the same executor-model state. -/
def Properties.EveryForwardIsAnEngineLegWitness : Prop :=
  wV35.code (wTA 34 74).engine = callingEngine wV35.base [.upgradeProxy 5 11] ∧
    wV35.base.rc.hasCode (wTA 34 74).addr ∧ (wTA 34 74).domain = .ctm ∧
    wV35.base.rc.hasCode (wTA 34 74).engine ∧ wV0.holders.ctmAdmin ≠ wV35.proxyAdmin ∧
    (wTA 34 74).inventory.length = wV35.inventoryLength .ctm ∧
    ∃ x', XStep wV35.base wV0.x (.forward [.upgradeProxy 5 11]) x' ∧ x'.impl 5 = 11 ∧
      ProxyUpgradeCurrent.RowsApplied x'.impl (wTA 34 74).rows ∧
      V35Step wV35 wV0 (.infra (wTA 34 74)) { wV0 with x := x' }

end Contracts.ChainTypeManager.ExecutorEngineAtV35
