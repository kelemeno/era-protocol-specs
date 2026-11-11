import EraSpec.Contracts.ChainTypeManager.Specs.ChainLocal
import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorForward

/-!
# Model: the per-chain headline across the CTM executor's transactions

Source: branch `feat/upgrade-simplification` at `e561b9cc2`, as for
`EraSpec.Contracts.ChainTypeManager.Specs.ExecutorForward`, whose executor model this file
reuses unchanged. It adds no step and no state: it names the routing steps each executor
transaction takes and the transactions that leave the CTM's own code in place. Paths are
relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.ChainLocalExecutor` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocalExecutor`.

## Why

The CTM owner is the `CTMUpgradeExecutor`. Its fixed entry points are
`applyInfrastructureUpgrade`, `applyCTMUpgrade` and `upgradeChain`
(`upgrades/registry/executors/CTMUpgradeExecutor.sol:64-102`); the break-glass
`ChainTypeManager.executeUpgrade` (`state-transition/ChainTypeManager.sol:631-633`, `onlyOwner`)
is reachable only through the owner-gated `forward` (`governance/UpgradeExecutorBase.sol:32-46`;
"Every other owner operation of the CTM ... goes through the owner-gated, event-logged
`forward`", `CTMUpgradeExecutor.sol:25-29`; the authority matrix lists `executeUpgrade` as
"`forward` only", `docs/registry-driven-upgrades.md:412` at the repository root). So every
break-glass cut, and every repair, is a forwarded call.

`XLabel.Tame` excludes every forwarded break-glass cut, so
`Properties.TameRunKeepsChainsOnTheirRelease` says nothing about a run in which the owner
cuts or repairs any chain. The per-chain headline needs only that the CTM's own code stays in
place (`XLabel.KeepsCtmCode`: a CTM code swap leaves the CTM's version state arbitrary,
`Properties.ForwardCtmSwapBreaksInvariants`), and a premise about the chain's own last write
among the run's routing steps (`XLabel.sysLabels`).

## The routing steps of a transaction (`XLabel.sysLabels`)

* `applyInfrastructureUpgrade`: none. It moves CTM-domain proxies. If its rows do not name the
  CTM proxy, and reinitializers move at most their own proxy, it leaves the CTM untouched.
* `applyCTMUpgrade(t)`: the registry commit of `t`.
* `upgradeChain(_, id)`: the transition of chain `id`.
* `forward(calls)`: the forwarded calls to the CTM, in order (`FCall.sys?`). A `ProxyAdmin`
  call is no routing step.
* another actor's step: that step.
-/

namespace Contracts.ChainTypeManager

/-- The routing step a forwarded call is, if any: `none` for a `ProxyAdmin` call. -/
def FCall.sys? : FCall → Option Label
  | .sys l => some l
  | _ => none

/-- A forwarded call that does not swap the CTM's code. Forwarded break-glass cuts are allowed,
unlike in `FCall.Tame`. -/
def FCall.KeepsCtmCode : FCall → Prop
  | .swapCtm _ _ => False
  | _ => True

/-- A transaction that leaves the CTM proxy's implementation in place: an infrastructure
transition whose rows do not name the CTM proxy, or a forward with no CTM code swap. Unlike
`XLabel.Tame`, forwarded break-glass cuts are allowed. -/
def XLabel.KeepsCtmCode (X : XConfig) : XLabel → Prop
  | .infra T => ∀ r ∈ T.rows, r.proxy ≠ X.ctmProxy
  | .forward calls => ∀ c ∈ calls, c.KeepsCtmCode
  | _ => True

/-- The routing steps a transaction takes, in order. -/
def XLabel.sysLabels : XLabel → List Label
  | .infra _ => []
  | .commit t => [.ctm (.commit t)]
  | .upgradeChain id => [.transition id]
  | .forward calls => calls.filterMap FCall.sys?
  | .env l => [l]

/-! ## Witness data

On the witness executor `wX` of `ExecutorForward` (the `ChainRouting` witness world, the CTM
proxy `8`), from `wX0` (a fresh CTM on release `100`, no chains). -/

/-- Chains `0` and `1` are created at version 1. One `forward` drifts both to `bgExtra` by
break-glass cuts. The executor commits `300` (1→2). -/
def wExecStuckRun : List XLabel :=
  [.env (.genesis 0), .env (.genesis 1),
    .forward [.sys (.arbitraryCut 0 1 bgExtra), .sys (.arbitraryCut 1 1 bgExtra)],
    .commit 300]

/-- A `forward` of the repair cut of chain `0` (version 1, release `100`'s routing), then the
executor's `upgradeChain` for chain `0`. -/
def wExecRepairRun : List XLabel :=
  [.forward [.sys (.arbitraryCut 0 1 (rowsRouting (wRows 100)))], .upgradeChain 0]

end Contracts.ChainTypeManager
