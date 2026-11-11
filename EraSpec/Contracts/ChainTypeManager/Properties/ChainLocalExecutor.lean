import EraSpec.Contracts.ChainTypeManager.Specs.ChainLocalExecutor

/-!
# Properties: the per-chain headline across the CTM executor's transactions

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ChainLocalExecutor`, over the
executor model of `ExecutorForward`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.ChainLocalExecutor`.

* **An executor run that keeps the CTM's code is a routing run** of its routing steps
  (`ExecutorRunIsARoutingRun`), provided reinitializers move at most their own proxy.
  Forwarded break-glass cuts included, every `ChainRouting` run result then applies, under
  its own premises.
* **Per-chain headline across executor runs.** Along such a run, a chain whose last write among
  the run's routing steps is not a break-glass cut runs its version's release
  (`ChainRunsItsVersionsReleaseAcrossExecutorRuns`). Besides the reinitializer frame, this
  needs only that no transaction moves the CTM proxy. `TameRunKeepsChainsOnTheirRelease` needed
  every transaction `Tame`, which also forbids forwarded cuts of every chain. Tame runs meet the
  new premises for every chain (`TamePremiseImpliesChainLocal`).
* **The executor's own repair path** (`ExecutorChainLocalWitness`): the owner drifts two chains
  by one forward, and chain `0` then has no `upgradeChain`. After a forwarded repair cut of
  chain `0`, the fixed entry point `upgradeChain` succeeds for it in the model (which omits
  timestamps and the other reject-only checks). Chain `0` ends on release `200`, and chain
  `1`, whose last write is a cut, is still drifted.
* **The CTM's code must stay in place** (`CtmSwapBreaksChainLocal`): a forwarded CTM code swap
  is no routing step, so it leaves the last-write premise intact, yet it can leave a chain
  ahead of its CTM. The reinitializer premise is load-bearing for the same reason in the row
  library (`ProxyUpgradeCurrent.ReinitLeakIsNotCaught`).
-/

namespace Contracts.ChainTypeManager

/-- **AN EXECUTOR RUN THAT KEEPS THE CTM'S CODE IS A ROUTING RUN.** Suppose each reinitializer
moves at most its own proxy, and no transaction of an executor run moves the CTM proxy (no
infrastructure row names it, no forwarded CTM code swap). Then the run's routing steps, in
order, form a `ChainRouting` run between the same routing systems. Forwarded break-glass cuts
are allowed. -/
def Properties.ExecutorRunIsARoutingRun : Prop :=
  ∀ (X : XConfig) (s s' : XState) (xs : List XLabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    XRun X s xs s' → (∀ x ∈ xs, x.KeepsCtmCode X) →
    Run X.W s.sys (xs.flatMap XLabel.sysLabels) s'.sys

/-- **THE PER-CHAIN HEADLINE ACROSS EXECUTOR RUNS.** Suppose each reinitializer moves at most its
own proxy. Take an executor run from a state where the CTM invariant holds and chain `id` is
consistent with its CTM, in which no transaction moves the CTM proxy, and in which the last
routing step writing `id` is not a break-glass cut. At the end chain `id`, if registered, is
not ahead of its CTM. If the CTM has a release `R_v` for the chain's version `v`, the chain
routes exactly `R_v`, and `R_v` is a release of version `v`. Forwarded break-glass cuts of
other chains, and of `id` before its last write, are allowed. -/
def Properties.ChainRunsItsVersionsReleaseAcrossExecutorRuns : Prop :=
  ∀ (X : XConfig) (s s' : XState) (xs : List XLabel) (id : ChainId),
    ProxyUpgradeCurrent.ReinitFrames X.rc → CtmInv X.W s.sys.ctm →
    (∀ c, s.sys.chains id = some c → ChainOk X.W s.sys c) → XRun X s xs s' →
    (∀ x ∈ xs, x.KeepsCtmCode X) → LastWriteNotBreakGlass id (xs.flatMap XLabel.sysLabels) →
    ∀ c, s'.sys.chains id = some c → c.pv ≤ s'.sys.ctm.pv ∧
      (s'.sys.ctm.relAt c.pv ≠ 0 → X.W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
        c.routing = rowsRouting (X.W.relRows (s'.sys.ctm.relAt c.pv)))

/-- **TAME RUNS MEET THE PER-CHAIN PREMISES FOR EVERY CHAIN.** An executor run of `Tame`
transactions, the premise of `TameRunKeepsChainsOnTheirRelease`, keeps the CTM's code and
satisfies `LastWriteNotBreakGlass id` for every chain `id`. -/
def Properties.TamePremiseImpliesChainLocal : Prop :=
  ∀ (X : XConfig) (s s' : XState) (xs : List XLabel), XRun X s xs s' → (∀ x ∈ xs, x.Tame X) →
    (∀ x ∈ xs, x.KeepsCtmCode X) ∧ ∀ id, LastWriteNotBreakGlass id (xs.flatMap XLabel.sysLabels)

/-- **THE EXECUTOR'S REPAIR PATH, AND THE PER-CHAIN HEADLINE ACROSS EXECUTOR RUNS IS NOT
VACUOUS.** In the witness executor, whose reinitializers move at most their own proxy, from the
fresh state, which satisfies `SysInv`, run `wExecStuckRun`: chains `0` and `1` are created, one
`forward` drifts both by break-glass cuts, and `applyCTMUpgrade(300)` commits 1→2. Chain `0`
then has no `upgradeChain`. Then run `wExecRepairRun`: a `forward` of the repair cut of chain
`0`, then `upgradeChain` for chain `0`.

* No transaction moves the CTM proxy, but the forwards are not `Tame`, so
  `TameRunKeepsChainsOnTheirRelease` does not apply.
* The last routing step writing chain `0` is its transition: chain `0` ends at version 2
  routing release `200`.
* The last routing step writing chain `1` is a break-glass cut: the premise fails for `1`, and
  chain `1` is still at version 1, whose release is `100`, without routing it. -/
def Properties.ExecutorChainLocalWitness : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧ SysInv wX.W wX0.sys ∧
    (∀ x ∈ wExecStuckRun ++ wExecRepairRun, x.KeepsCtmCode wX) ∧
    (∃ x ∈ wExecStuckRun ++ wExecRepairRun, ¬ x.Tame wX) ∧
    LastWriteNotBreakGlass 0 ((wExecStuckRun ++ wExecRepairRun).flatMap XLabel.sysLabels) ∧
    ¬ LastWriteNotBreakGlass 1 ((wExecStuckRun ++ wExecRepairRun).flatMap XLabel.sysLabels) ∧
    ∃ s s', XRun wX wX0 wExecStuckRun s ∧ (¬ ∃ s'', XStep wX s (.upgradeChain 0) s'') ∧
      XRun wX s wExecRepairRun s' ∧
      (∃ c, s'.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)) ∧
      (∃ c, s'.sys.chains 1 = some c ∧ c.pv = 1 ∧ s'.sys.ctm.relAt 1 = 100 ∧
        c.routing ≠ rowsRouting (wRows 100))

/-- **THE CTM-CODE PREMISE IS LOAD-BEARING.** The run of `ForwardCtmSwapBreaksInvariants`: from
the fresh state, chain `0` is created, `applyCTMUpgrade(300)` commits 1→2 and `upgradeChain`
upgrades chain `0`, and then one `forward` swaps the CTM's code for code that leaves the CTM as
`initialize(100)` would. The last routing step writing chain `0` is its transition (the swap is
no routing step), and every other premise of `ChainRunsItsVersionsReleaseAcrossExecutorRuns`
holds, except that the swap does not keep the CTM's code. Chain `0` ends ahead of its CTM. -/
def Properties.CtmSwapBreaksChainLocal : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧ SysInv wX.W wX0.sys ∧
    (∀ x ∈ [XLabel.env (.genesis 0), .commit 300, .upgradeChain 0], x.KeepsCtmCode wX) ∧
    ¬ XLabel.KeepsCtmCode wX (.forward [.swapCtm 42 (initState wWorld 100)]) ∧
    LastWriteNotBreakGlass 0 (([XLabel.env (.genesis 0), .commit 300, .upgradeChain 0,
      .forward [.swapCtm 42 (initState wWorld 100)]]).flatMap XLabel.sysLabels) ∧
    ∃ s s', XRun wX wX0 [.env (.genesis 0), .commit 300, .upgradeChain 0] s ∧
      XStep wX s (.forward [.swapCtm 42 (initState wWorld 100)]) s' ∧
      ∃ c, s'.sys.chains 0 = some c ∧ s'.sys.ctm.pv < c.pv

end Contracts.ChainTypeManager
