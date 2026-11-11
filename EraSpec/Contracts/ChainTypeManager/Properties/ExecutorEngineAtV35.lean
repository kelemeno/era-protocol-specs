import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorEngineAtV35

/-!
# Properties: `applyInfrastructureUpgrade` at `draft/v0.35.0`, with an arbitrary engine

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ExecutorEngineAtV35` (commit
`d9f6789`). Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorEngineAtV35`.

## What the executor checks, and what it does not

Whatever engine the transition pins, the executor establishes only three things after it
returns: every row's proxy at its `implNew`, its own `owner`/`pendingOwner` unchanged, and the
domain holders unchanged up to a collision of the hash it compares
(`ExecutorChecksAfterAnyEngine`). An engine can make every call a `forward` can, inside the
fixed entry point (`EveryForwardIsAnEngineLeg`). So `ExecutorForward`'s run invariants, whose
premise for an infrastructure step was only "no row names the CTM proxy", fail at `d9f6789`,
even for genuine transition objects (`TameRunsNoLongerPreserveSysInv`,
`TameRunsNoLongerKeepChainsOnTheirRelease`, `FixedEntrypointsNoLongerMoveOnlyAlongRows`).

## With the genuine row engine nothing changes

If the transition pins `DefaultProxyUpgradeEngine`, the leg is `ExecutorForward`'s
infrastructure step, and conversely, given the checks `d9f6789` added
(`DefaultEngineLegIsAnInfraStep`, `InfraStepIsADefaultEngineLeg`). The default engine meets the
review condition `EngineReviewed` (`DefaultEngineIsReviewed`), and the headline holds across
`d9f6789` runs whose transitions pin it (`DefaultEngineRunKeepsChainsOnTheirRelease`).

## What governance must check

Two conditions on the engine, both defined in the Specs file; the executor checks neither.

* **`EngineIsTame`** (the engine makes no break-glass cut and does not move the CTM proxy: every
  leg is a run of tame `e561b9cc2` transactions) is what the CTM's invariants need. With
  `ReinitFrames` and tame transactions as at `e561b9cc2`, a run whose engines are tame is a tame
  `ExecutorForward` run (`TameEngineRunIsATameExecutorRun`), so `SysInv` holds, the CTM's version
  never decreases, the CTM proxy does not move (`TameEngineRunPreservesSysInv`), and every chain
  at `v` routes `R_v` (`TameEngineRunKeepsChainsOnTheirRelease`).
* **`EngineReviewed`** (the engine runs `DefaultProxyUpgradeEngine`'s core on the manifest's rows,
  and its hooks make only CTM calls that are not break-glass cuts) is what source-checked swaps
  need. A reviewed leg is a `forward`, the `e561b9cc2` infrastructure step and a `forward`
  (`ReviewedLegIsAnExecutorRun`), so for rows not naming the CTM proxy a reviewed engine is tame
  (`ReviewedEngineIsTame`, `ReviewedRunKeepsChainsOnTheirRelease`). Beyond that, the fixed entry
  points move proxies only along rows' edges, for any rows
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

## The NatSpec

`ICTMUpgradeExecutor.sol:33-34`: "Applies a CTM-domain transition's source-checked implementation
swaps through the bound CTM `ProxyAdmin`, and verifies every row at its `implNew` before
returning."

* "verifies every row at its `implNew`" holds for every engine (`ExecutorChecksAfterAnyEngine`).
* "source-checked implementation swaps" holds for a reviewed engine
  (`ReviewedEngineRefusesStaleRows`, `ReviewedLegsMoveProxiesOnlyAlongRows`) and fails otherwise:
  an engine not built on `applyRows` replays a stale object (`DirectEngineSkipsTheSourceCheck`),
  and so does a `DefaultProxyUpgradeEngine` subclass whose `_beforeSwaps` moves a row's proxy
  onto its `expectedOldImpl` (`BeforeHookDefeatsTheSourceCheck`).
* "through the bound CTM `ProxyAdmin`" understates the leg: the engine also acts as the CTM's
  owner (`CuttingEngineBreaksTheHeadline`).
-/

namespace Contracts.ChainTypeManager.ExecutorEngineAtV35

/-! ## What the executor checks, whatever the engine -/

/-- **WHAT THE EXECUTOR ESTABLISHES, WHATEVER THE ENGINE.** After a successful
`applyInfrastructureUpgrade(T)`: the object and its engine have code, the object is of the CTM
domain, every row's proxy is at its `implNew`, the executor's `owner` and `pendingOwner` are
unchanged, and the domain holders are unchanged unless the pair (before, after) is a collision
of `holdersHash`. -/
def Properties.ExecutorChecksAfterAnyEngine : Prop :=
  ∀ (X : V35Config) (T : V35Transition) (s s' : V35State), V35Step X s (.infra T) s' →
    X.base.rc.hasCode T.addr ∧ T.domain = .ctm ∧ X.base.rc.hasCode T.engine ∧
    ProxyUpgradeCurrent.RowsApplied s'.x.impl T.rows ∧
    s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner ∧
    (s'.holders = s.holders ∨
      (s'.holders ≠ s.holders ∧ X.holdersHash s'.holders = X.holdersHash s.holders))

/-- **AN ENGINE CAN DO WHAT A `forward` CAN.** Take a CTM-domain object with code whose inventory
has the CTM domain's length and whose engine has code and only makes the calls `calls`. Then
`applyInfrastructureUpgrade` succeeds from `s` and ends in `x'` with the executor's storage and
the holders as they were, exactly when `forward(calls)` succeeds from `s` and ends in `x'` and
every row's proxy is at its `implNew` in `x'`. So the forwards of `ExecutorForward`'s
countermodels (`ForwardDowngradesAProxy`, `ForwardCtmSwapBreaksInvariants`) run inside the fixed
entry point once its rows are applied. Unlike a `forward`, the leg emits no `CallForwarded`. -/
def Properties.EveryForwardIsAnEngineLeg : Prop :=
  ∀ (X : V35Config) (T : V35Transition) (s : V35State) (calls : List FCall) (x' : XState),
    X.code T.engine = callingEngine X.base calls → X.base.rc.hasCode T.addr → T.domain = .ctm →
    X.base.rc.hasCode T.engine → T.inventory.length = X.inventoryLength .ctm →
    (V35Step X s (.infra T) { s with x := x' } ↔
      XStep X.base s.x (.forward calls) x' ∧ ProxyUpgradeCurrent.RowsApplied x'.impl T.rows)

/-- **AT `d9f6789` TAME RUNS NO LONGER PRESERVE THE INVARIANT.** `ExecutorForward`'s
`TameRunPreservesSysInv` without a premise on the engines is false at `d9f6789`, even when every
applied object is a genuine `ProxyUpgradeTransition`: some configuration with `ReinitFrames` has
a run of tame transactions from a `SysInv` state that ends outside `SysInv`. -/
def Properties.TameRunsNoLongerPreserveSysInv : Prop :=
  ¬ ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → SysInv X.base.W s.x.sys → V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → T.Genuine (X.inventoryLength T.domain)) →
    SysInv X.base.W s'.x.sys

/-- **AND NO LONGER KEEP EVERY CHAIN ON ITS RELEASE.** `ExecutorForward`'s
`TameRunKeepsChainsOnTheirRelease` without a premise on the engines is false at `d9f6789`, even
for genuine objects. -/
def Properties.TameRunsNoLongerKeepChainsOnTheirRelease : Prop :=
  ¬ ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → SysInv X.base.W s.x.sys → V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → T.Genuine (X.inventoryLength T.domain)) →
    ∀ id c, s'.x.sys.chains id = some c → s'.x.sys.ctm.relAt c.pv ≠ 0 →
      c.routing = rowsRouting (X.base.W.relRows (s'.x.sys.ctm.relAt c.pv))

/-- **AND THE FIXED ENTRY POINTS NO LONGER MOVE PROXIES ONLY ALONG ROWS.**
`ExecutorForward`'s `FixedEntrypointsMoveProxiesOnlyAlongRows` (and its `AnyRows` form) without
a premise on the engine is false at `d9f6789`, even for a genuine object whose rows name distinct
proxies. -/
def Properties.FixedEntrypointsNoLongerMoveOnlyAlongRows : Prop :=
  ¬ ∀ (X : V35Config) (s s' : V35State) (l : V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → V35Step X s l s' → (∀ calls, l ≠ .forward calls) →
    (∀ T, l = .infra T → T.Genuine (X.inventoryLength T.domain)) → V35MovesOnlyAlongRows s s' l

/-! ## The genuine row engine -/

/-- **WITH `DefaultProxyUpgradeEngine` THE LEG IS THE `e561b9cc2` INFRASTRUCTURE STEP.** If the
transition pins the genuine row engine, a successful `applyInfrastructureUpgrade(T)` at
`d9f6789` relates the CTM, its chains and the implementations as `ExecutorForward`'s
`applyInfrastructureUpgrade` of the same object does, the executor owns its `ProxyAdmin`, and
the executor's storage is unchanged. -/
def Properties.DefaultEngineLegIsAnInfraStep : Prop :=
  ∀ (X : V35Config) (T : V35Transition) (s s' : V35State), EngineIsDefault X T →
    V35Step X s (.infra T) s' →
    XStep X.base s.x (.infra T.toCurrent) s'.x ∧ X.base.rc.adminOwner = X.base.rc.self ∧
      s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner

/-- **AND EVERY `e561b9cc2` INFRASTRUCTURE STEP IS SUCH A LEG**, given the checks `d9f6789`
added: the executor owns its `ProxyAdmin` (`DefaultProxyUpgradeEngine.sol:33-37`), the engine has
code (`ProxyUpgradeExecutorBase.sol:60`), and the inventory has the CTM domain's length
(`:93-96`). The leg leaves the executor's storage and the domain holders as they were. So with the
genuine row engine #2654 only removes runs, and `ExecutorForward`'s results about the
infrastructure step describe `d9f6789`. -/
def Properties.InfraStepIsADefaultEngineLeg : Prop :=
  ∀ (X : V35Config) (T : V35Transition) (s : V35State) (x' : XState), EngineIsDefault X T →
    XStep X.base s.x (.infra T.toCurrent) x' → X.base.rc.adminOwner = X.base.rc.self →
    X.base.rc.hasCode T.engine → T.inventory.length = X.inventoryLength .ctm →
    V35Step X s (.infra T) { s with x := x' }

/-- **THE GENUINE ROW ENGINE MEETS THE REVIEW CONDITION**, with empty hooks. -/
def Properties.DefaultEngineIsReviewed : Prop :=
  ∀ (X : V35Config) (T : V35Transition), EngineIsDefault X T → EngineReviewed X T

/-- **THE HEADLINE AT `d9f6789` WITH THE GENUINE ROW ENGINE.** `ChainsRunTheirVersionsRelease`
across `d9f6789` executor runs: under `ReinitFrames`, from a `SysInv` state, along a run of tame
transactions (as at `e561b9cc2`) whose infrastructure transitions all pin
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
`d9f6789` run is `Tame` and every infrastructure transition pins a tame engine, some run of tame
`ExecutorForward` transactions relates the same executor-model states. -/
def Properties.TameEngineRunIsATameExecutorRun : Prop :=
  ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label), V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → EngineIsTame X T) →
    ∃ xs : List XLabel, XRun X.base s.x xs s'.x ∧ ∀ x ∈ xs, x.Tame X.base

/-- **RUNS WITH TAME ENGINES PRESERVE THE INVARIANT** (`TameRunPreservesSysInv` at `d9f6789`).
Under `ReinitFrames`, from a `SysInv` state, along a run of tame transactions whose infrastructure
transitions pin tame engines: `SysInv` holds at the end, the CTM's version has not decreased, and
the CTM proxy has not moved. -/
def Properties.TameEngineRunPreservesSysInv : Prop :=
  ∀ (X : V35Config) (s s' : V35State) (ls : List V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → SysInv X.base.W s.x.sys → V35Run X s ls s' →
    (∀ l ∈ ls, l.Tame X) → (∀ T, V35Label.infra T ∈ ls → EngineIsTame X T) →
    SysInv X.base.W s'.x.sys ∧ s.x.sys.ctm.pv ≤ s'.x.sys.ctm.pv ∧
      s'.x.impl X.base.ctmProxy = s.x.impl X.base.ctmProxy

/-- **HEADLINE AT `d9f6789`: EVERY CHAIN AT VERSION `v` RUNS `R_v`, IF THE ENGINES ARE TAME.**
(`TameRunKeepsChainsOnTheirRelease` at `d9f6789`.) Under the premises of
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
(`FixedEntrypointsMoveProxiesOnlyAlongRowsAnyRows` at `d9f6789`.) Any transaction other than
`forward` whose infrastructure transition, if any, pins a reviewed engine, with reinitializers that
move at most their own proxy, leaves every proxy where it was or moves it from a row's
`expectedOldImpl` to that row's `implNew`. No premise on the rows: the object may be
non-genuine. -/
def Properties.ReviewedLegsMoveProxiesOnlyAlongRows : Prop :=
  ∀ (X : V35Config) (s s' : V35State) (l : V35Label),
    ProxyUpgradeCurrent.ReinitFrames X.base.rc → V35Step X s l s' →
    (∀ calls, l ≠ .forward calls) → (∀ T, l = .infra T → EngineReviewed X T) →
    V35MovesOnlyAlongRows s s' l

/-- **A REVIEWED ENGINE REFUSES A STALE OBJECT** (the NatSpec's source check). Under
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
and every executor check passes: the rows are applied, and the executor's storage and the holders
are unchanged. Chain `0` ends at version 1, whose release is `100`, routing something else. So the
engine is neither tame nor reviewed. -/
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
`ExecutorForward`'s `ForwardCtmSwapBreaksInvariants` at `d9f6789`. After the same tame run (chain
`0` created, `300` committed, chain `0` upgraded to version 2; `SysInv` holds), a genuine object
whose rows do not name the CTM proxy, so `Tame` as at `e561b9cc2`, pins a subclass whose
`_afterSwaps` is that countermodel's `upgradeAndCall` on the CTM proxy. Every executor check passes.
The CTM proxy moved, the CTM's version decreased, and `SysInv` fails. So the engine is neither
tame nor reviewed. -/
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

/-- **AN ENGINE NOT BUILT ON `applyRows` SKIPS THE SOURCE CHECK**, so the NatSpec's
"source-checked implementation swaps" fails. Two default-engine legs (`wStaleRun`) move proxy `5`
from `10` to `11` (row `5: 10 → 11`) and on to `12` (row `5: 11 → 12`). The stale first object
`wTA 30 70` then names a row whose proxy is at neither end, and the default engine, which is
reviewed, refuses it. A genuine object with the same rows whose engine only calls
`ProxyAdmin.upgrade(5, 11)` (code with no `applyRows`) succeeds, every executor check passes, and
proxy `5` goes `12 → 11`, along no row's edge. That engine is tame but not reviewed. -/
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
goes `12 → 11`. The executor's second `requireRowsApplied`, documented as catching "a follow-up hook
that moves a proxy of the row set" (`ProxyUpgradeRowLib.sol:126-127`), reads only the end state.
The engine is tame but not reviewed. -/
def Properties.BeforeHookDefeatsTheSourceCheck : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wV35.base.rc ∧ (wTA 36 76).Genuine (wV35.inventoryLength .ctm) ∧
    EngineIsTame wV35 (wTA 36 76) ∧ ¬ EngineReviewed wV35 (wTA 36 76) ∧
    ∃ s, V35Run wV35 wV0 wStaleRun s ∧ s.x.impl 5 = 12 ∧
      ∃ s', V35Step wV35 s (.infra (wTA 36 76)) s' ∧ s'.x.impl 5 = 11 ∧
        s'.owner = s.owner ∧ s'.pendingOwner = s.pendingOwner ∧ s'.holders = s.holders ∧
        ¬ V35MovesOnlyAlongRows s s' (.infra (wTA 36 76))

/-! ## Witness -/

/-- **THE PREMISES ARE MET BY A REAL RUN, WITH A HOOK.** From the fresh witness state, which
satisfies `SysInv` (reinitializers inert, so `ReinitFrames` holds; the executor owns its
`ProxyAdmin`), run `wReviewedRun`: apply `wTAB 70` (the default engine: proxies `5` and `6`
upgraded; this leg is also an `ExecutorForward` infrastructure step), create chain `0`, commit
`300`, upgrade chain `0`, then apply `wTAB 71`, which has the same rows and pins a reviewed
subclass whose `_afterSwaps` replaces the committed transition `300` by `400` (the rows are
already applied and skip themselves). Every transaction is tame, both engines are reviewed and
tame, the first is the default engine and the second is not, both objects are genuine and have
code. At the end chain `0` is at
version 2 on release `200`, slot 1 holds `400`, proxies `5` and `6` moved, and the executor's
storage and the holders are unchanged. -/
def Properties.ReviewedRunWitness : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wV35.base.rc ∧ SysInv wV35.base.W wV0.x.sys ∧
    wV35.base.rc.adminOwner = wV35.base.rc.self ∧
    EngineIsDefault wV35 (wTAB 70) ∧ EngineReviewed wV35 (wTAB 70) ∧
    EngineReviewed wV35 (wTAB 71) ∧ ¬ EngineIsDefault wV35 (wTAB 71) ∧
    EngineIsTame wV35 (wTAB 70) ∧ EngineIsTame wV35 (wTAB 71) ∧
    (wTAB 70).Genuine (wV35.inventoryLength .ctm) ∧ (wTAB 71).Genuine (wV35.inventoryLength .ctm) ∧
    wV35.base.rc.hasCode (wTAB 70).engine ∧ wV35.base.rc.hasCode (wTAB 71).engine ∧
    (∃ x', XStep wV35.base wV0.x (.infra (wTAB 70).toCurrent) x') ∧
    (∀ l ∈ wReviewedRun, l.Tame wV35) ∧
    ∃ s', V35Run wV35 wV0 wReviewedRun s' ∧
      s'.x.impl 5 = 11 ∧ s'.x.impl 6 = 12 ∧ s'.x.sys.ctm.ut 1 = 400 ∧ s'.x.sys.ctm.pv = 2 ∧
      (∃ c, s'.x.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)) ∧
      s'.owner = wV0.owner ∧ s'.pendingOwner = wV0.pendingOwner ∧ s'.holders = wV0.holders

end Contracts.ChainTypeManager.ExecutorEngineAtV35
