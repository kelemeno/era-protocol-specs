import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeWedgeV35

/-!
# Properties: a pending L2 upgrade transaction at an expired version wedges the chain

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.UpgradeWedgeV35` (at `d9f6789`).
Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeWedgeV35`.

## What this file says

* **The refinement is conservative** (`PendingRunIsATimedRun`). Every run of this model is a run
  of `UpgradeTiming`'s timed model, with the same routing, CTM and notifier, and `DiamondAux`
  writes in place of the batch and role steps. No break-glass cut appears that was not in the
  run.
* **`b ≠ 0 → h ≠ 0` is invariant** (`PendingInvAlongRuns`): an upgrade batch number is only set
  while a transaction is pending, and execution clears both together.
* **No upgrade while blocked** (`PendingTxBlocksEveryUpgrade`). A chain on its settlement layer
  with a pending transaction, whose next edge is minor, cannot be upgraded, by any path, caller
  or time.
* **Headline, negative: the wedge persists** (`PendingTxAtExpiredVersionWedges`). Suppose such a
  chain also has its transaction in no batch yet, the CTM has moved past its version, the
  version has no legacy cut, and the version's deadline `x` is before `τ`. Then along every run
  whose block times are `τ` or later, with no break-glass cut and no
  `setProtocolVersionDeadline` at the chain's version, the chain stays in that state and is in
  dead time at every time from `τ` on.
* **(a) `WedgeCountermodel`.** Edges `0.1.0 → 0.2.0` and `0.2.0 → 0.3.0` are minor and
  L2-carrying and pass `requireValidEdge`'s checks; `0.2.0`'s deadline `20` is before `25`. A
  clean chain at `0.1.0` (nothing pending, every batch executed) upgrades at `25` and lands on
  `0.2.0` with a pending transaction, `0.2.0` inactive. From there, along every run as above,
  it is in dead time forever. This refutes `VersionEdgeLib.sol:28-29` ("one every chain can
  execute") for a lagging chain.
* **(b) `NoDeadTimeWithoutPendingTx`.** `ValidatedTimedRunsHaveNoDeadTime` holds in this model
  under the extra premise "no transaction pending, or the next edge is patch-only", together
  with what `requireValidEdge` says of a patch (no L2 side). `NoDeadTimeWithoutPendingTxWitness`
  meets every premise. `PendingPremiseIsLoadBearing` shows that dropping the extra premise alone
  makes the conclusion false: the end state of the `WedgeCountermodel` run meets every other
  premise and is in dead time.
* **(c) `OnlyOverrideUnwedges`.** For a chain blocked as above with nothing in a batch, no step
  turns dead time at `τ` from true to false except `setProtocolVersionDeadline` at the chain's
  version and a break-glass cut. `OverrideRecoversWedgedChain` shows the override does recover
  it: after it, the chain commits, proves and executes the transaction's batch and is upgraded
  across the next edge. `BreakGlassUnwedges` shows a break-glass cut does too. So both
  exceptions in (c) are needed.
-/

namespace Contracts.ChainTypeManager

/-! ## The refinement -/

/-- **EVERY RUN OF THIS MODEL IS A TIMED RUN.** For every run of this model there is a run of
`UpgradeTiming`'s `TimedStep` between the same timed states. Each of its labels is not a base
step (an upgrade, a notifier write, or a `DiamondAux` write), or is a base step `base l` whose
label `PLabel.base l` occurs in the run. -/
def Properties.PendingRunIsATimedRun : Prop :=
  ∀ (C : PendingConfig) (s s' : PendingSys) (ls : List PLabel), PRun C s ls s' →
    ∃ ls' : List TimedLabel, TimedRun C.T s.ts ls' s'.ts ∧
      ∀ l' ∈ ls', (∀ l, l' ≠ .base l) ∨ ∃ l, l' = .base l ∧ PLabel.base l ∈ ls

/-- **NO UPGRADE BATCH NUMBER WITHOUT A PENDING TRANSACTION.** `PendingInv` holds at the end of
every run that starts in a state satisfying it. -/
def Properties.PendingInvAlongRuns : Prop :=
  ∀ (C : PendingConfig) (s s' : PendingSys) (ls : List PLabel),
    PendingInv s → PRun C s ls s' → PendingInv s'

/-! ## The wedge -/

/-- **A PENDING TRANSACTION BLOCKS EVERY UPGRADE ACROSS A MINOR EDGE.** If chain `id` is
`PendingBlock`ed (on its settlement layer, a transaction pending, the edge at its version
minor), then no upgrade of it succeeds, through any entry point, by any caller, at any block
time. -/
def Properties.PendingTxBlocksEveryUpgrade : Prop :=
  ∀ (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain),
    PendingBlock C s id c →
    ∀ path caller τ, ¬ ∃ s', PStep C s (.upgrade id path caller τ) s'

/-- **HEADLINE (NEGATIVE): A PENDING TRANSACTION AT AN EXPIRED VERSION WEDGES THE CHAIN.**
Suppose chain `id`, at chain state `c`, is `PendingWedge`d: on its settlement layer, a
transaction pending and in no batch, the edge at its version minor, the CTM past its version,
no legacy cut there. Suppose the version's deadline is `x < τ`. Take any run with:
* no break-glass cut;
* no `setProtocolVersionDeadline` at `c.pv`;
* every block time (of an upgrade or a commit) `τ` or later.

At its end the chain is still `PendingWedge`d at `c`, its version's deadline is still `x`, and
the chain is in dead time at every block time `τ'` from `τ` on. -/
def Properties.PendingTxAtExpiredVersionWedges : Prop :=
  ∀ (C : PendingConfig) (s s' : PendingSys) (ls : List PLabel) (id : ChainId) (c : Chain)
    (x τ : ℕ),
    PendingWedge C s id c → versionDeadline C.T s.dl s.ts.sys.ctm c.pv = some x → x < τ →
    PRun C s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary ∧ (∀ t, l ≠ .setDeadline c.pv t) ∧ l.NotBefore τ) →
    PendingWedge C s' id c ∧ versionDeadline C.T s'.dl s'.ts.sys.ctm c.pv = some x ∧
      ∀ τ', τ ≤ τ' → PChainDeadTime C s' id τ'

/-- **(a) THE WEDGE COUNTERMODEL.** In the witness world:
* transitions `300` (`0.1.0 → 0.2.0`) and `600` (`0.2.0 → 0.3.0`) pass every check
  `ValidEdgeV35` lists, change the minor component and carry an L2 side, and `600`'s deadline
  for `0.2.0`, `20`, is before `25`;
* the run `wvSetup` from a fresh CTM leaves chain `0` at `0.1.0` with `300` and `600`
  committed, every batch executed, on L1, nothing pending, and no override;
* at time `25` the CTM's owner upgrades it through the CTM, and it lands on `0.2.0` with an
  upgrade transaction pending; `0.2.0` is not active at `25`;
* along every run from there with no break-glass cut, no `setProtocolVersionDeadline` at
  `0.2.0`, and every block time `25` or later, chain `0` is in dead time at every time from
  `25` on. -/
def Properties.WedgeCountermodel : Prop :=
  ValidEdgeV35 wvConfig 300 ∧ ValidEdgeV35 wvConfig 600 ∧
    minorOf (wvWorld.tr 300).old < minorOf (wvWorld.tr 300).new ∧
    minorOf (wvWorld.tr 600).old < minorOf (wvWorld.tr 600).new ∧
    wvConfig.hasL2 300 = true ∧ wvConfig.hasL2 600 = true ∧
    (wvWorld.tr 300).new = (wvWorld.tr 600).old ∧ (wvSched 600).deadline < 25 ∧
    ∃ s0 s1, PRun wvConfig wvSys0 wvSetup s0 ∧
      s0.ts.sys.chains 0 = some ⟨wv1, rowsRouting (wRows 100)⟩ ∧
      s0.ts.sys.ctm.ut wv1 = 300 ∧ s0.ts.sys.ctm.ut wv2 = 600 ∧
      (s0.ts.aux 0).committed = (s0.ts.aux 0).executed ∧ (s0.ts.aux 0).slVersion = none ∧
      (s0.bx 0).txHash = 0 ∧ (s0.bx 0).batch = 0 ∧ s0.dl = (fun _ => 0) ∧
      PStep wvConfig s0 wvLateUpgrade s1 ∧
      s1.ts.sys.chains 0 = some ⟨wv2, rowsRouting (wRows 200)⟩ ∧ (s1.bx 0).txHash ≠ 0 ∧
      ¬ ProtocolVersionActive wvTimed s1.dl s1.ts.sys.ctm wv2 25 ∧
      ∀ ls s', PRun wvConfig s1 ls s' →
        (∀ l ∈ ls, ¬ l.isArbitrary ∧ (∀ t, l ≠ .setDeadline wv2 t) ∧ l.NotBefore 25) →
        ∀ τ', 25 ≤ τ' → PChainDeadTime wvConfig s' 0 τ'

/-! ## (b) No dead time without a pending transaction -/

/-- **(b) HEADLINE (POSITIVE): NO DEAD TIME WITHOUT A PENDING TRANSACTION.** The premises of
`ValidatedTimedRunsHaveNoDeadTime`, for a run of this model:
* the run starts from a state satisfying `SysInv`, whose installed releases list each selector
  once, whose committed slots have valid schedules, and which satisfies `PendingInv`;
* it has no break-glass cut, every release it installs passes the duplicate check, and every
  transition it commits or installs as a replacement has a valid schedule;
* at its end chain `id` is at a version `c.pv` with a committed edge and no stored override,
  has executed every committed batch, and its settlement layer, if any, is at the edge's target.

Two more premises, about the L2 upgrade transaction:
* **the extra premise**: no transaction is pending, or the edge is patch-only;
* if the edge is patch-only it carries no L2 side (`VersionEdgeLib.sol:88-90`).

Then the chain is in dead time at no block time; at every block time its version is active or
both the admin's direct upgrade and the CTM owner's upgrade through the CTM succeed, landing on
`PendingSys.crossed`; and at the edge's upgrade timestamp the version is active and both
upgrades succeed. -/
def Properties.NoDeadTimeWithoutPendingTx : Prop :=
  ∀ (C : PendingConfig) (s s' : PendingSys) (ls : List PLabel),
    SysInv C.T.X.W s.ts.sys → RecordedReleasesWf C.T.X.W s.ts.sys.ctm →
    SlotSchedulesValid C.T s.ts.sys.ctm → PendingInv s →
    PRun C s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) → (∀ l ∈ ls, l.InstallsWf C.T.X.W) →
    (∀ l ∈ ls, l.CommitsValidSchedule C.T) →
    ∀ id c, s'.ts.sys.chains id = some c → s'.ts.sys.ctm.ut c.pv ≠ 0 → s'.dl c.pv = 0 →
      (s'.ts.aux id).committed = (s'.ts.aux id).executed →
      (∀ w, (s'.ts.aux id).slVersion = some w → (s'.ts.sys.edge C.T.X.W c.pv).new ≤ w) →
      ((s'.bx id).txHash = 0 ∨ PatchOnly c.pv (s'.ts.sys.edge C.T.X.W c.pv).new) →
      (PatchOnly c.pv (s'.ts.sys.edge C.T.X.W c.pv).new → C.hasL2 (s'.ts.sys.ctm.ut c.pv) = false) →
      (∀ τ, ¬ PChainDeadTime C s' id τ) ∧
      (∀ τ, ProtocolVersionActive C.T s'.dl s'.ts.sys.ctm c.pv τ ∨
        (PStep C s' (.upgrade id (.direct c.pv) (s'.ts.aux id).admin τ) (s'.crossed C id c) ∧
          PStep C s' (.upgrade id (.ctm c.pv) C.T.ctmOwner τ) (s'.crossed C id c))) ∧
      ProtocolVersionActive C.T s'.dl s'.ts.sys.ctm c.pv
        (C.T.sched (s'.ts.sys.ctm.ut c.pv)).upgradeTimestamp ∧
      PStep C s' (.upgrade id (.direct c.pv) (s'.ts.aux id).admin
          (C.T.sched (s'.ts.sys.ctm.ut c.pv)).upgradeTimestamp) (s'.crossed C id c) ∧
      PStep C s' (.upgrade id (.ctm c.pv) C.T.ctmOwner
          (C.T.sched (s'.ts.sys.ctm.ut c.pv)).upgradeTimestamp) (s'.crossed C id c)

/-- **THE PREMISES OF (b) ARE MET.** The fresh witness system satisfies the start premises, the
labels of `wvSetup` the run premises, and at its end chain `0` (at `0.1.0`, `300` committed, no
override, every batch executed, on L1) has nothing pending. The edge `300` is minor, so the L2
premise on patches holds vacuously. The chain is in dead time at no block time. -/
def Properties.NoDeadTimeWithoutPendingTxWitness : Prop :=
  SysInv wvTimed.X.W wvSys0.ts.sys ∧ RecordedReleasesWf wvTimed.X.W wvSys0.ts.sys.ctm ∧
    SlotSchedulesValid wvTimed wvSys0.ts.sys.ctm ∧ PendingInv wvSys0 ∧
    (∀ l ∈ wvSetup, ¬ l.isArbitrary ∧ l.InstallsWf wvTimed.X.W ∧ l.CommitsValidSchedule wvTimed) ∧
    ∃ s, PRun wvConfig wvSys0 wvSetup s ∧
      s.ts.sys.chains 0 = some ⟨wv1, rowsRouting (wRows 100)⟩ ∧ s.ts.sys.ctm.ut wv1 ≠ 0 ∧
      s.dl wv1 = 0 ∧ (s.ts.aux 0).committed = (s.ts.aux 0).executed ∧
      (s.ts.aux 0).slVersion = none ∧ (s.bx 0).txHash = 0 ∧
      ¬ PatchOnly wv1 (s.ts.sys.edge wvTimed.X.W wv1).new ∧
      ∀ τ, ¬ PChainDeadTime wvConfig s 0 τ

/-- **THE EXTRA PREMISE OF (b) IS LOAD-BEARING.** The run `wvSetup` followed by the late upgrade
`wvLateUpgrade` starts from the witness system (which meets the start premises of (b),
`NoDeadTimeWithoutPendingTxWitness`) and meets the run premises. At its end chain `0` is at
`0.2.0` with `600` committed, no override, every batch executed, on L1, and the patch premise
holds vacuously. Only the extra premise fails: a transaction is pending and `600` is not
patch-only. And the conclusion fails: the chain is in dead time at `25`. -/
def Properties.PendingPremiseIsLoadBearing : Prop :=
  (∀ l ∈ wvSetup ++ [wvLateUpgrade],
      ¬ l.isArbitrary ∧ l.InstallsWf wvTimed.X.W ∧ l.CommitsValidSchedule wvTimed) ∧
    ∃ s, PRun wvConfig wvSys0 (wvSetup ++ [wvLateUpgrade]) s ∧
      s.ts.sys.chains 0 = some ⟨wv2, rowsRouting (wRows 200)⟩ ∧ s.ts.sys.ctm.ut wv2 ≠ 0 ∧
      s.dl wv2 = 0 ∧ (s.ts.aux 0).committed = (s.ts.aux 0).executed ∧
      (s.ts.aux 0).slVersion = none ∧
      (PatchOnly wv2 (s.ts.sys.edge wvTimed.X.W wv2).new →
        wvConfig.hasL2 (s.ts.sys.ctm.ut wv2) = false) ∧
      (s.bx 0).txHash ≠ 0 ∧ ¬ PatchOnly wv2 (s.ts.sys.edge wvTimed.X.W wv2).new ∧
      PChainDeadTime wvConfig s 0 25

/-! ## (c) Only an override or break-glass unwedges -/

/-- **(c) ONLY AN OVERRIDE OR A BREAK-GLASS CUT UNWEDGES.** Suppose chain `id`, at chain state
`c`, is `PendingWedge`d and in dead time at `τ`. If one step leaves it not in dead time at `τ`,
that step is `setProtocolVersionDeadline(c.pv, t)` for some `t`, or a break-glass cut. Every
other label (any upgrade, CTM writer, commit at any block time, prove, execute, revert,
notifier, role or migration write, and an override at another version) keeps it in dead time at
`τ`. -/
def Properties.OnlyOverrideUnwedges : Prop :=
  ∀ (C : PendingConfig) (s s' : PendingSys) (l : PLabel) (id : ChainId) (c : Chain) (τ : ℕ),
    PendingWedge C s id c → PStep C s l s' →
    PChainDeadTime C s id τ → ¬ PChainDeadTime C s' id τ →
    (∃ t, l = .setDeadline c.pv t) ∨ l.isArbitrary

/-- **THE OVERRIDE RECOVERS THE WEDGED CHAIN.** From the end state of the `WedgeCountermodel`
run, the run `wvRecovery` succeeds: the CTM's owner sets `0.2.0`'s deadline to `100`; the chain
commits the batch that carries the pending transaction at `30`, proves and executes it, which
clears the transaction; then the owner upgrades it through the CTM at `30`. The chain ends at
`0.3.0` with nothing pending. Right after the override the chain is not in dead time at `25`. -/
def Properties.OverrideRecoversWedgedChain : Prop :=
  ∃ s1 s2 s3, PRun wvConfig wvSys0 (wvSetup ++ [wvLateUpgrade]) s1 ∧
    PChainDeadTime wvConfig s1 0 25 ∧
    PStep wvConfig s1 (.setDeadline wv2 100) s2 ∧ ¬ PChainDeadTime wvConfig s2 0 25 ∧
    PRun wvConfig s1 wvRecovery s3 ∧
    (∃ ρ, s3.ts.sys.chains 0 = some ⟨wv3, ρ⟩) ∧ (s3.bx 0).txHash = 0 ∧ (s3.bx 0).batch = 0

/-- **A BREAK-GLASS CUT UNWEDGES TOO.** From the end state of the `WedgeCountermodel` run, a
break-glass cut moving chain `0` to `0.3.0` with release `250`'s routing leaves it not in dead
time at `25`: `0.3.0` is the CTM's current version and has no deadline. -/
def Properties.BreakGlassUnwedges : Prop :=
  ∃ s1 s2, PRun wvConfig wvSys0 (wvSetup ++ [wvLateUpgrade]) s1 ∧
    PChainDeadTime wvConfig s1 0 25 ∧
    PStep wvConfig s1 (.base (.arbitraryCut 0 wv3 (rowsRouting (wRows 250)))) s2 ∧
    ¬ PChainDeadTime wvConfig s2 0 25

end Contracts.ChainTypeManager
