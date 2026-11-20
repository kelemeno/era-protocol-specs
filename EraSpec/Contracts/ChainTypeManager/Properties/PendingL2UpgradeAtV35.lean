import EraSpec.Contracts.ChainTypeManager.Specs.PendingL2UpgradeAtV35
import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTimingAtV35
import EraSpec.Core.Headline

/-!
# Properties: the pending L2 upgrade transaction, at `draft/v0.35.0`

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.PendingL2UpgradeAtV35` (`b17415d`).
Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.PendingL2UpgradeAtV35`.

## What this file says

* **The model refines `UpgradeTiming`** (`PendingRunIsATimedRun`). Every run of this model is a
  run of `UpgradeTiming`'s timed steps between the same timed states, with `setAux` in place of
  each step that writes a chain's `DiamondAux` (role, settlement-layer, migration and batch
  steps). Every routing step of that timed run is a routing step of the run, so no break-glass
  cut is added.
* **`batch ≠ 0 → txHash ≠ 0` is invariant** (`PendingInvAlongRuns`).
* **A pending transaction blocks every upgrade across a minor edge**
  (`PendingTxBlocksEveryUpgrade`): a chain on its settlement layer with a pending transaction or
  an upgrade batch, whose next edge changes the minor component, has no upgrade step, by any
  path, caller or block time.
* **A pending transaction in no batch, at an expired version, stays**
  (`ExpiredPendingChainStaysInDeadTime`). Take a chain on its settlement layer with a pending
  transaction in no batch, a minor edge committed at its version, the CTM past its version, no
  legacy cut there, and that version's deadline `x` before `τ`. Along every run with no
  break-glass cut, no `setProtocolVersionDeadline` at the chain's version, and every block time
  `τ` or later, the chain keeps all of this and is in dead time at every block time from `τ` on.
  `ExpiredPendingChainWitness` meets every premise with a run that touches other chains.
* **A concrete instance** (`LateUpgradeLandsInDeadTime`). Transitions `0.1.0 → 0.2.0` and
  `0.2.0 → 0.3.0` pass the checks `ValidEdge` states, change the minor component and carry an L2
  side. A chain at `0.1.0` with nothing pending and every batch executed (no batch committed
  yet) is not in dead time at
  `25`, though `0.1.0`'s deadline `20` has passed: the CTM's owner can upgrade it. After that
  upgrade it is at `0.2.0` with a transaction pending and `0.2.0`'s deadline `20` passed, and the
  previous result applies from `25` on.
* **No dead time without a pending transaction** (`NoDeadTimeWithoutPendingTx`).
  `ValidatedTimedRunsHaveNoDeadTime` holds in this model with two more premises: no transaction
  is pending or the next edge is a patch, and a patch carries no L2 side (what `requireValidEdge`
  checks). Two witnesses meet every premise, one through each side of the first
  (`NoDeadTimeWithoutPendingTxWitness`, `NoDeadTimeAcrossPatchWithPendingTx`). Without the first
  premise the conclusion is false (`NoDeadTimeNeedsItsPendingTxPremise`).
* **Only an override or a break-glass cut ends that dead time**
  (`OnlyOverrideOrBreakGlassEndsDeadTime`). From a state as in the negative result, in dead time
  at `τ`, a step of this model that ends dead time at `τ` is `setProtocolVersionDeadline` at the
  chain's version or a break-glass cut. Both happen (`OverrideRecoversExpiredPendingChain`,
  `BreakGlassEndsDeadTime`). An override to a nonzero time `t ≥ τ` lets the pending
  transaction's batch be committed at `τ`, proved and executed, which clears the transaction,
  when every committed batch is verified and executed (`OverrideClearsPendingTx`).

Every statement is about this model. A swap of the CTM's implementation is not a step of it.
-/

namespace Contracts.ChainTypeManager.PendingL2UpgradeAtV35

/-! ## The refinement -/

/-- **EVERY RUN OF THIS MODEL IS A TIMED RUN.** For every run of this model there is a run of
`UpgradeTiming`'s `TimedStep` between the same timed states. Each label of that timed run is not
a routing step (it is an upgrade, a notifier write or a `DiamondAux` write), or is a routing step
`base l` such that `PLabel.base l` is a label of the run. Witness: the runs in
`OverrideRecoversExpiredPendingChain` and `ExpiredPendingChainWitness`. -/
def Properties.PendingRunIsATimedRun : Prop :=
  ∀ (C : PendingConfig) (s s' : PendingSys) (ls : List PLabel), PRun C s ls s' →
    ∃ ls' : List TimedLabel, TimedRun C.T s.ts ls' s'.ts ∧
      ∀ l' ∈ ls', (∀ l, l' ≠ .base l) ∨ ∃ l, l' = .base l ∧ PLabel.base l ∈ ls

/-- **WITHOUT THE SECOND-PROOF-SYSTEM REQUIREMENT, EVERY RUN OF THIS MODEL IS A GATED v35 RUN.**
This model omits the second-proof-system checks (Specs). Composing `PendingRunIsATimedRun` with
`UpgradeTimingAtV35.Properties.UngatedTimedRunsAreRunsWithoutTheRequirement`: for every proof
world and proof-system fields with the requirement off everywhere, every run of this model is the
timed image of a run of `UpgradeTimingAtV35`'s gated system (`TimedRun35`) between the same timed
states, in which no chain ever requires its second proof system, and whose timed labels relate to
the run's labels as in `PendingRunIsATimedRun`. So the results here describe `b17415d20` runs
of chains that do not require their second proof system; for a chain that does, an upgrade has
the extra gate of `UpgradeTimingAtV35`, which only rejects. -/
def Properties.PendingRunIsAGatedRunWithoutTheRequirement : Prop :=
  ∀ (C : PendingConfig) (P : ProofGateAtV35.ProofWorld) (s s' : PendingSys) (ls : List PLabel)
    (pr : ChainId → ProofGateAtV35.ProofState), PRun C s ls s' → (∀ id, (pr id).required = false) →
    ∃ (ls' : List TimedLabel) (pr' : ChainId → ProofGateAtV35.ProofState),
      UpgradeTimingAtV35.TimedRun35 C.T P ⟨s.ts, pr⟩ (ls'.map UpgradeTimingAtV35.TimedLabel35.timed)
        ⟨s'.ts, pr'⟩ ∧ (∀ id, (pr' id).required = false) ∧
      ∀ l' ∈ ls', (∀ l, l' ≠ .base l) ∨ ∃ l, l' = .base l ∧ PLabel.base l ∈ ls

/-- **NO UPGRADE BATCH NUMBER WITHOUT A PENDING TRANSACTION.** `PendingInv` holds at the end of
every run that starts in a state satisfying it. Witness: the fresh witness system satisfies it
(`NoDeadTimeWithoutPendingTxWitness`), and `OverrideRecoversExpiredPendingChain` runs from it
through a state with an upgrade batch recorded. -/
def Properties.PendingInvAlongRuns : Prop :=
  ∀ (C : PendingConfig) (s s' : PendingSys) (ls : List PLabel),
    PendingInv s → PRun C s ls s' → PendingInv s'

/-! ## The block -/

/-- **A PENDING TRANSACTION BLOCKS EVERY UPGRADE ACROSS A MINOR EDGE**
(`BaseZkSyncUpgrade.sol:259-268`). Take chain `id`, registered at chain state `c` and on its
settlement layer, where the edge committed at its version changes the minor component, and a
transaction is pending or an upgrade batch is recorded. Then no upgrade of the chain succeeds,
through any entry point, by any caller, at any block time. Witness: `PendingUnbatched`, which
`ExpiredPendingChainWitness` meets, contains every premise. -/
@[headline] def Properties.PendingTxBlocksEveryUpgrade : Prop :=
  ∀ (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain),
    s.ts.sys.chains id = some c → (s.ts.aux id).slVersion = none →
    minorOf c.pv < minorOf (s.ts.sys.edge C.T.X.W c.pv).new →
    ((s.bx id).txHash ≠ 0 ∨ (s.bx id).batch ≠ 0) →
    ∀ path caller τ, ¬ ∃ s', PStep C s (.upgrade id path caller τ) s'

/-- **A PENDING TRANSACTION IN NO BATCH, AT AN EXPIRED VERSION, STAYS.** Suppose chain `id`, at
chain state `c`, is `PendingUnbatched`: registered, on its settlement layer, a transaction
pending and in no batch, the edge committed at its version changing the minor component, the CTM
past its version, and no legacy cut there. Suppose that version's deadline is `x < τ`. Take any
run with:
* no break-glass cut;
* no `setProtocolVersionDeadline` at `c.pv`;
* every block time (of an upgrade or a commit) `τ` or later.

At its end the chain is still `PendingUnbatched` at `c`, its version's deadline is still `x`, and
the chain is in dead time at every block time `τ'` from `τ` on. -/
def Properties.ExpiredPendingChainStaysInDeadTime : Prop :=
  ∀ (C : PendingConfig) (s s' : PendingSys) (ls : List PLabel) (id : ChainId) (c : Chain)
    (x τ : ℕ),
    PendingUnbatched C s id c → versionDeadline C.T s.dl s.ts.sys.ctm c.pv = some x → x < τ →
    PRun C s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary ∧ (∀ t, l ≠ .setDeadline c.pv t) ∧ l.NotBefore τ) →
    PendingUnbatched C s' id c ∧ versionDeadline C.T s'.dl s'.ts.sys.ctm c.pv = some x ∧
      ∀ τ', τ ≤ τ' → PChainDeadTime C s' id τ'

/-- **THE PREMISES OF `ExpiredPendingChainStaysInDeadTime` ARE MET.** From the fresh witness
system, the run `pwSetup` followed by the late upgrade `pwLateUpgrade` reaches a state in which
chain `0`, at `0.2.0` routing release `200`, is `PendingUnbatched` and `0.2.0`'s deadline is `20`,
before `25`. From there the run `pwIdle` succeeds and meets the run premises for `0.2.0`
and `25`: it overrides `0.1.0`'s deadline to `30`, sets chain `0`'s own upgrade time, and creates
chain `1`, which commits a batch. At its end chain `0` is still `PendingUnbatched` and in dead
time at `25`. -/
@[witness] def Properties.ExpiredPendingChainWitness : Prop :=
  ∃ s1 s2, PRun pwConfig pwSys0 (pwSetup ++ [pwLateUpgrade]) s1 ∧
    PendingUnbatched pwConfig s1 0 ⟨v020, rowsRouting (pwRows 200)⟩ ∧
    versionDeadline pwTimed s1.dl s1.ts.sys.ctm v020 = some 20 ∧
    PRun pwConfig s1 pwIdle s2 ∧
    (∀ l ∈ pwIdle, ¬ l.isArbitrary ∧ (∀ t, l ≠ .setDeadline v020 t) ∧ l.NotBefore 25) ∧
    s2.dl v010 = 30 ∧ (s2.ts.aux 1).committed = 1 ∧
    PendingUnbatched pwConfig s2 0 ⟨v020, rowsRouting (pwRows 200)⟩ ∧
    PChainDeadTime pwConfig s2 0 25

/-- **A CONCRETE INSTANCE.** In the witness world:
* transitions `300` (`0.1.0 → 0.2.0`) and `600` (`0.2.0 → 0.3.0`) satisfy `ValidEdge`, change
  the minor component, and carry an L2 side;
* the run `pwSetup` from the fresh system leaves chain `0` at `0.1.0` routing release `100`,
  with `300` and `600` committed, the CTM at `0.3.0`, every batch executed (no batch committed
  yet), on L1, nothing pending, and no override;
* at time `25` version `0.1.0` is not active, and chain `0` is not in dead time;
* at `25` the CTM's owner upgrades chain `0` through the CTM. It lands at `0.2.0` routing
  release `200` with transaction `7` pending, and `0.2.0`'s deadline is `20`;
* along every run from there with no break-glass cut, no `setProtocolVersionDeadline` at
  `0.2.0`, and every block time `25` or later, chain `0` is in dead time at every block time
  from `25` on. -/
@[countermodel] def Properties.LateUpgradeLandsInDeadTime : Prop :=
  ValidEdge pwConfig 300 ∧ ValidEdge pwConfig 600 ∧
    minorOf v010 < minorOf v020 ∧ minorOf v020 < minorOf v030 ∧
    pwConfig.hasL2 300 = true ∧ pwConfig.hasL2 600 = true ∧
    ∃ s0 s1, PRun pwConfig pwSys0 pwSetup s0 ∧
      s0.ts.sys.chains 0 = some ⟨v010, rowsRouting (pwRows 100)⟩ ∧
      s0.ts.sys.ctm.ut v010 = 300 ∧ s0.ts.sys.ctm.ut v020 = 600 ∧ s0.ts.sys.ctm.pv = v030 ∧
      (s0.ts.aux 0).committed = (s0.ts.aux 0).executed ∧ (s0.ts.aux 0).slVersion = none ∧
      (s0.bx 0).txHash = 0 ∧ (s0.bx 0).batch = 0 ∧ s0.dl = (fun _ => 0) ∧
      ¬ ProtocolVersionActive pwTimed s0.dl s0.ts.sys.ctm v010 25 ∧
      ¬ PChainDeadTime pwConfig s0 0 25 ∧
      PStep pwConfig s0 pwLateUpgrade s1 ∧
      s1.ts.sys.chains 0 = some ⟨v020, rowsRouting (pwRows 200)⟩ ∧ (s1.bx 0).txHash = 7 ∧
      versionDeadline pwTimed s1.dl s1.ts.sys.ctm v020 = some 20 ∧
      ∀ ls s', PRun pwConfig s1 ls s' →
        (∀ l ∈ ls, ¬ l.isArbitrary ∧ (∀ t, l ≠ .setDeadline v020 t) ∧ l.NotBefore 25) →
        ∀ τ', 25 ≤ τ' → PChainDeadTime pwConfig s' 0 τ'

/-! ## No dead time without a pending transaction -/

/-- **NO DEAD TIME WITHOUT A PENDING TRANSACTION.** The premises of
`ValidatedTimedRunsHaveNoDeadTime`, for a run of this model:
* the run starts from a state satisfying `SysInv`, whose installed releases list each selector
  once, whose committed slots have valid schedules, and which satisfies `PendingInv`;
* it has no break-glass cut, every release it installs passes the duplicate check, and every
  transition it commits or installs as a replacement has a valid schedule;
* at its end chain `id` is at a version `c.pv` with a committed edge and no stored override,
  has executed every committed batch, and its settlement layer, if any, is at the edge's target.

Two more premises, about the L2 upgrade transaction:
* no transaction is pending, or the edge is a patch;
* if the edge is a patch, it carries no L2 side (`VersionEdgeLib.sol:88-90`).

Then the chain is in dead time at no block time. At every block time its version is active, or
both the admin's direct upgrade and the CTM owner's upgrade through the CTM succeed, landing on
`PendingSys.crossed`. At the edge's upgrade timestamp the version is active and both upgrades
succeed.

The model omits further reject-only checks of an upgrade (see the Specs), so at the source these
upgrades also need those checks to pass. -/
@[headline] def Properties.NoDeadTimeWithoutPendingTx : Prop :=
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

/-- **THE PREMISES OF `NoDeadTimeWithoutPendingTx` ARE MET, NOTHING PENDING.** The fresh witness
system satisfies the start premises; every label of `pwSetup` meets the run premises. At the end
of `pwSetup` chain `0` is at `0.1.0` with `300` committed, no override, every batch executed (no
batch committed yet: `committed = executed = 0`), on L1, and nothing pending; the edge `300` is
not a patch. At `25`, `0.1.0` is not active and the chain's admin `3` upgrades it directly,
landing on `PendingSys.crossed`. The chain is in dead time at no block time. -/
@[witness] def Properties.NoDeadTimeWithoutPendingTxWitness : Prop :=
  SysInv pwTimed.X.W pwSys0.ts.sys ∧ RecordedReleasesWf pwTimed.X.W pwSys0.ts.sys.ctm ∧
    SlotSchedulesValid pwTimed pwSys0.ts.sys.ctm ∧ PendingInv pwSys0 ∧
    (∀ l ∈ pwSetup, ¬ l.isArbitrary ∧ l.InstallsWf pwTimed.X.W ∧ l.CommitsValidSchedule pwTimed) ∧
    ∃ s, PRun pwConfig pwSys0 pwSetup s ∧
      s.ts.sys.chains 0 = some ⟨v010, rowsRouting (pwRows 100)⟩ ∧ s.ts.sys.ctm.ut v010 = 300 ∧
      s.dl v010 = 0 ∧ (s.ts.aux 0).committed = (s.ts.aux 0).executed ∧
      (s.ts.aux 0).slVersion = none ∧ (s.bx 0).txHash = 0 ∧
      ¬ PatchOnly v010 (s.ts.sys.edge pwTimed.X.W v010).new ∧
      ¬ ProtocolVersionActive pwTimed s.dl s.ts.sys.ctm v010 25 ∧
      PStep pwConfig s (.upgrade 0 (.direct v010) 3 25)
        (s.crossed pwConfig 0 ⟨v010, rowsRouting (pwRows 100)⟩) ∧
      ∀ τ, ¬ PChainDeadTime pwConfig s 0 τ

/-- **THE PREMISES OF `NoDeadTimeWithoutPendingTx` ARE MET THROUGH A PATCH, A TRANSACTION
PENDING.** From the fresh witness system (start premises: `NoDeadTimeWithoutPendingTxWitness`),
the run `pwPatchSetup` (with the patch `700` committed at `0.2.0`) followed by the late upgrade
`pwLateUpgrade` meets the run premises. At its end chain `0` is at `0.2.0` with `700` committed,
no override, every batch executed (no batch committed yet), on L1, and transaction `7` pending.
The edge `700` is a patch
and carries no L2 side. At `25`, `0.2.0` is not active and the chain's admin `3` upgrades it
directly across the patch; the transaction stays pending. The chain is in dead time at no block
time. -/
@[witness] def Properties.NoDeadTimeAcrossPatchWithPendingTx : Prop :=
  (∀ l ∈ pwPatchSetup ++ [pwLateUpgrade],
      ¬ l.isArbitrary ∧ l.InstallsWf pwTimed.X.W ∧ l.CommitsValidSchedule pwTimed) ∧
    ∃ s, PRun pwConfig pwSys0 (pwPatchSetup ++ [pwLateUpgrade]) s ∧
      s.ts.sys.chains 0 = some ⟨v020, rowsRouting (pwRows 200)⟩ ∧ s.ts.sys.ctm.ut v020 = 700 ∧
      s.dl v020 = 0 ∧ (s.ts.aux 0).committed = (s.ts.aux 0).executed ∧
      (s.ts.aux 0).slVersion = none ∧ (s.bx 0).txHash = 7 ∧
      PatchOnly v020 (s.ts.sys.edge pwTimed.X.W v020).new ∧ pwConfig.hasL2 700 = false ∧
      ¬ ProtocolVersionActive pwTimed s.dl s.ts.sys.ctm v020 25 ∧
      PStep pwConfig s (.upgrade 0 (.direct v020) 3 25)
        (s.crossed pwConfig 0 ⟨v020, rowsRouting (pwRows 200)⟩) ∧
      ((s.crossed pwConfig 0 ⟨v020, rowsRouting (pwRows 200)⟩).bx 0).txHash = 7 ∧
      ∀ τ, ¬ PChainDeadTime pwConfig s 0 τ

/-- **THE PENDING-TRANSACTION PREMISE CANNOT BE DROPPED.** `NoDeadTimeWithoutPendingTx` with the
premise "no transaction is pending, or the edge is a patch" removed, and every other premise
kept, is false. -/
@[countermodel] def Properties.NoDeadTimeNeedsItsPendingTxPremise : Prop :=
  ¬ ∀ (C : PendingConfig) (s s' : PendingSys) (ls : List PLabel),
    SysInv C.T.X.W s.ts.sys → RecordedReleasesWf C.T.X.W s.ts.sys.ctm →
    SlotSchedulesValid C.T s.ts.sys.ctm → PendingInv s →
    PRun C s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) → (∀ l ∈ ls, l.InstallsWf C.T.X.W) →
    (∀ l ∈ ls, l.CommitsValidSchedule C.T) →
    ∀ id c, s'.ts.sys.chains id = some c → s'.ts.sys.ctm.ut c.pv ≠ 0 → s'.dl c.pv = 0 →
      (s'.ts.aux id).committed = (s'.ts.aux id).executed →
      (∀ w, (s'.ts.aux id).slVersion = some w → (s'.ts.sys.edge C.T.X.W c.pv).new ≤ w) →
      (PatchOnly c.pv (s'.ts.sys.edge C.T.X.W c.pv).new → C.hasL2 (s'.ts.sys.ctm.ut c.pv) = false) →
      ∀ τ, ¬ PChainDeadTime C s' id τ

/-! ## Ways out -/

/-- **ONLY AN OVERRIDE OR A BREAK-GLASS CUT ENDS THAT DEAD TIME.** Suppose chain `id`, at chain
state `c`, is `PendingUnbatched` and in dead time at `τ`. If one step of this model leaves it not
in dead time at `τ`, that step is `setProtocolVersionDeadline(c.pv, t)` for some `t`, or a
break-glass cut. Every other label keeps it in dead time at `τ`: any upgrade, any routing step
other than a break-glass cut, a notifier, role or migration write, a commit, prove, execute or
revert at any block time, and an override at another version. -/
def Properties.OnlyOverrideOrBreakGlassEndsDeadTime : Prop :=
  ∀ (C : PendingConfig) (s s' : PendingSys) (l : PLabel) (id : ChainId) (c : Chain) (τ : ℕ),
    PendingUnbatched C s id c → PStep C s l s' →
    PChainDeadTime C s id τ → ¬ PChainDeadTime C s' id τ →
    (∃ t, l = .setDeadline c.pv t) ∨ l.isArbitrary

/-- **AN OVERRIDE LETS THE PENDING BATCH THROUGH.** Take chain `id`, registered at chain state
`c`, on its settlement layer, with no upgrade batch recorded, every committed batch verified and
executed. After `setProtocolVersionDeadline(c.pv, t)` with `t` nonzero and `τ ≤ t`, the run
"commit one batch at `τ`, prove it, execute it" succeeds. It leaves the routing system as it
was, no transaction pending and no upgrade batch, every committed batch executed, and the
chain's version active at `τ`. -/
def Properties.OverrideClearsPendingTx : Prop :=
  ∀ (C : PendingConfig) (s : PendingSys) (id : ChainId) (c : Chain) (t τ : ℕ),
    s.ts.sys.chains id = some c → (s.ts.aux id).slVersion = none → (s.bx id).batch = 0 →
    (s.ts.aux id).committed = (s.ts.aux id).executed →
    (s.bx id).verified = (s.ts.aux id).committed → t ≠ 0 → τ ≤ t →
    ∃ s', PRun C s [.setDeadline c.pv t, .commit id τ, .prove id 1, .execute id 1] s' ∧
      s'.ts.sys = s.ts.sys ∧ (s'.bx id).txHash = 0 ∧ (s'.bx id).batch = 0 ∧
      (s'.ts.aux id).committed = (s'.ts.aux id).executed ∧
      ProtocolVersionActive C.T s'.dl s'.ts.sys.ctm c.pv τ

/-- **THE OVERRIDE ENDS IT IN THE INSTANCE.** From the end state of `LateUpgradeLandsInDeadTime`'s
late upgrade (chain `0` `PendingUnbatched` at `0.2.0` with every committed batch verified and
executed, in dead time at `25`), which with `t = 100` and `τ = 30` meets every premise of
`OverrideClearsPendingTx` and of `OnlyOverrideOrBreakGlassEndsDeadTime`:
* `setProtocolVersionDeadline(0.2.0, 100)` leaves chain `0` not in dead time at `25`;
* chain `0` then commits a batch at `30`, which is recorded as the upgrade batch `1`;
* the run `pwRecovery` succeeds: the override, that commit, proving and executing the batch,
  which clears the transaction, and the owner's upgrade through the CTM at `30`. Chain `0` ends
  at `0.3.0`, the CTM's version, routing release `250`, with `600`'s transaction (hash `7`)
  pending in no batch, and in dead time at no block time. -/
def Properties.OverrideRecoversExpiredPendingChain : Prop :=
  ∃ s1 s2 s3 s4, PRun pwConfig pwSys0 (pwSetup ++ [pwLateUpgrade]) s1 ∧
    PendingUnbatched pwConfig s1 0 ⟨v020, rowsRouting (pwRows 200)⟩ ∧
    (s1.ts.aux 0).committed = (s1.ts.aux 0).executed ∧
    (s1.bx 0).verified = (s1.ts.aux 0).committed ∧
    PChainDeadTime pwConfig s1 0 25 ∧
    PStep pwConfig s1 (.setDeadline v020 100) s2 ∧ ¬ PChainDeadTime pwConfig s2 0 25 ∧
    PStep pwConfig s2 (.commit 0 30) s3 ∧ (s3.bx 0).txHash = 7 ∧ (s3.bx 0).batch = 1 ∧
    PRun pwConfig s1 pwRecovery s4 ∧
    s4.ts.sys.chains 0 = some ⟨v030, rowsRouting (pwRows 250)⟩ ∧ s4.ts.sys.ctm.pv = v030 ∧
    (s4.bx 0).txHash = 7 ∧ (s4.bx 0).batch = 0 ∧
    ∀ τ, ¬ PChainDeadTime pwConfig s4 0 τ

/-- **A BREAK-GLASS CUT ENDS IT TOO.** From the same state, a break-glass cut moving chain `0` to
`0.3.0` with release `250`'s routing leaves it not in dead time at `25`: `0.3.0` is the CTM's
version and has no deadline. -/
def Properties.BreakGlassEndsDeadTime : Prop :=
  ∃ s1 s2, PRun pwConfig pwSys0 (pwSetup ++ [pwLateUpgrade]) s1 ∧
    PendingUnbatched pwConfig s1 0 ⟨v020, rowsRouting (pwRows 200)⟩ ∧
    PChainDeadTime pwConfig s1 0 25 ∧
    PStep pwConfig s1 (.base (.arbitraryCut 0 v030 (rowsRouting (pwRows 250)))) s2 ∧
    ¬ PChainDeadTime pwConfig s2 0 25

end Contracts.ChainTypeManager.PendingL2UpgradeAtV35
