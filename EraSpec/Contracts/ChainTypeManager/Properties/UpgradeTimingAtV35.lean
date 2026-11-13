import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTimingAtV35

/-!
# Properties: who may upgrade a chain, and when, at `draft/v0.35.0`

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTimingAtV35` (commit
`d9f6789`). Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTimingAtV35`. The
statements live in `Contracts.ChainTypeManager.UpgradeTimingAtV35.Properties`; a statement named
like one of `UpgradeTiming` is that statement over the v35 system.

## Do the `UpgradeTiming` theorems describe v35?

Yes, verbatim for every chain that does not require its second proof system. For a chain that
does, an upgrade has one more condition.

* A v35 timed step is the `e561b9cc2` timed step plus `TimedGateHolds`
  (`TimedStepIsTheE561StepPlusTheGate`). For a chain that does not require its second proof
  system, the gate is vacuous and an upgrade succeeds at v35 exactly when it does in
  `UpgradeTiming` (`UnflaggedChainsUpgradeAsAtE561`). Every `UpgradeTiming` run is a v35 run in
  which no chain requires it (`E561TimedRunsAreRunsWithoutTheRequirement`).
* Every necessary condition `UpgradeTiming` proves still binds, because every v35 timed run is
  an `UpgradeTiming` run (`TimedRunIsATimedRun`). That covers `ManifestTimestampGates`,
  `EveryPathNeedsExecutedBatches`, `EveryPathNeedsTheSettlementLayerAhead`,
  `OtherCallersNeedTheNotifier` and the routing headline (`TimedRunKeepsChainsOnTheirRelease`).
* `ICTMUpgradeExecutor.sol:53-54` still holds: the executor's call does not depend on the
  notifier (`ExecutorPathIgnoresNotifier`).
* `ICTMUpgradeExecutor.sol:48-49` ("at any time") is still false, through the same instance
  (`NotAtAnyTime`, for every proof world). At v35 it fails in a second way: an upgrade of a
  chain that requires its second proof system needs the arriving release's verifier in
  multi-proof mode, whatever the path, the caller and the time (`ProofGateBindsEveryPath`). In
  `OwnerCannotUpgradeARequiringChainToAPlonkRelease`, every condition of `UpgradeTiming`'s
  repaired statement holds for the owner from time 10 on, yet nobody can ever upgrade the chain.
* **The repaired statement at v35** is `UpgradeChainEnabledIffTimed`: `e561b9cc2`'s eight
  conditions plus "if the chain requires its second proof system, the verifier of the
  transition's new release reports multi-proof mode with nothing disabled".

## The proof-system guarantees along timed runs

A v35 timed run is a `ProofGateAtV35` run of its routing steps and its proof-system writes
(`TimedRunIsAProofGateRun`), so that file's results hold along timed runs:

* a chain that requires its second proof system keeps a verifier that reports multi-proof mode
  for the empty mask (`TimedRunsKeepAMultiProofVerifier`);
* the requirement is set only by `permanentlyRequireSecondProofSystem`, called by the chain's
  admin while the diamond is on its settlement layer, and otherwise changed only by a
  break-glass cut of the chain (`TimedRequirementWriters`);
* without such a cut it stays set (`TimedRequirementIsPermanentWithoutBreakGlass`).

`UpgradeTimingAtV35Witness` is a v35 run in which a chain that requires its second proof system
is upgraded through `upgradeChain` by its admin. Its setup contains a successful
`permanentlyRequireSecondProofSystem` by the admin.
-/

namespace Contracts.ChainTypeManager.UpgradeTimingAtV35

open Contracts.ChainTypeManager
open Contracts.ChainTypeManager.ProofGateAtV35

/-! ## The v35 timed step and run -/

/-- **EVERY v35 TIMED STEP IS THE `e561b9cc2` TIMED STEP PLUS THE PROOF GATE.** For every
`UpgradeTiming` label `l` and timed state `t'`, a v35 step labelled `l` that leaves `t'` exists,
with some proof-system fields, iff `UpgradeTiming`'s step `l` to `t'` exists and `TimedGateHolds`
holds before it. -/
def Properties.TimedStepIsTheE561StepPlusTheGate : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s : TimedSys35) (l : TimedLabel) (t' : TimedSys),
    (∃ pr', TimedStep35 T P s (.timed l) ⟨t', pr'⟩) ↔
      (TimedStep T s.timed l t' ∧ TimedGateHolds T P s l)

/-- **A v35 TIMED RUN IS AN `UpgradeTiming` RUN.** Forgetting the proof-system fields, every v35
timed run is a run of `UpgradeTiming` of its timed labels, in order. -/
def Properties.TimedRunIsATimedRun : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (ls : List TimedLabel35),
    TimedRun35 T P s ls s' → TimedRun T s.timed (ls.flatMap TimedLabel35.timedSteps) s'.timed

/-- **EVERY `UpgradeTiming` RUN IS A v35 RUN IN WHICH NO CHAIN REQUIRES ITS SECOND PROOF
SYSTEM.** -/
def Properties.E561TimedRunsAreRunsWithoutTheRequirement : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys) (ls : List TimedLabel)
    (pr : ChainId → ProofState), TimedRun T s ls s' → (∀ id, (pr id).required = false) →
    ∃ pr', TimedRun35 T P ⟨s, pr⟩ (ls.map TimedLabel35.timed) ⟨s', pr'⟩ ∧
      ∀ id, (pr' id).required = false

/-- **FOR A CHAIN THAT DOES NOT REQUIRE ITS SECOND PROOF SYSTEM, AN UPGRADE SUCCEEDS AT v35 EXACTLY
WHEN IT DOES IN `UpgradeTiming`**, by every path, for every caller and at every time, with the
same effect on the timed state. -/
def Properties.UnflaggedChainsUpgradeAsAtE561 : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s : TimedSys35) (id : ChainId) (path : UpgradePath)
    (caller : Address) (τ : ℕ) (t' : TimedSys), (s.proof id).required = false →
    ((∃ pr', TimedStep35 T P s (.timed (.upgrade id path caller τ)) ⟨t', pr'⟩) ↔
      TimedStep T s.timed (.upgrade id path caller τ) t')

/-- **THE ROUTING HEADLINE ALONG v35 TIMED RUNS.** As
`Contracts.ChainTypeManager.Properties.TimedRunKeepsChainsOnTheirRelease`, over v35 timed runs. -/
def Properties.TimedRunKeepsChainsOnTheirRelease : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (ls : List TimedLabel35),
    SysInv T.X.W s.timed.sys → TimedRun35 T P s ls s' → (∀ l ∈ ls, ¬ l.isArbitrary) →
    ∀ id c, s'.timed.sys.chains id = some c → s'.timed.sys.ctm.relAt c.pv ≠ 0 →
      T.X.W.relVersion (s'.timed.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (T.X.W.relRows (s'.timed.sys.ctm.relAt c.pv))

/-! ## The proof-system guarantees along timed runs -/

/-- **A v35 TIMED RUN IS A `ProofGateAtV35` RUN.** Forgetting callers, block times, the notifier
and each chain's `DiamondAux`, every v35 timed run is a `ProofGateAtV35` run of its
`gateSteps`, in order: an upgrade by any path is a transition, a base step is itself, the two
proof-system writers are themselves, and the notifier and `DiamondAux` writes are stutters. -/
def Properties.TimedRunIsAProofGateRun : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (ls : List TimedLabel35),
    TimedRun35 T P s ls s' →
    Run35 T.X.W P s.routing (ls.flatMap TimedLabel35.gateSteps) s'.routing

/-- **ALONG v35 TIMED RUNS, A CHAIN THAT REQUIRES ITS SECOND PROOF SYSTEM KEEPS A MULTI-PROOF
VERIFIER.** As `ProofGateAtV35.Properties.RequiringChainsKeepAMultiProofVerifier`, over timed
runs, break-glass cuts included: from a state where `ProofInv` holds, every registered chain
that requires its second proof system has a verifier that reports multi-proof mode for the
empty mask. The verifiers must satisfy `DisablingNeverEnablesMultiProof`. -/
def Properties.TimedRunsKeepAMultiProofVerifier : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (ls : List TimedLabel35),
    DisablingNeverEnablesMultiProof P → ProofInv P s.routing → TimedRun35 T P s ls s' →
    ProofInv P s'.routing

/-- **ONLY THE CHAIN'S ADMIN, ON ITS SETTLEMENT LAYER, SETS THE REQUIREMENT; ONLY A BREAK-GLASS
CUT OF THE CHAIN CHANGES IT OTHERWISE.** If a v35 timed step changes a registered chain's
`secondProofSystemRequired`, then either the step is that chain's
`permanentlyRequireSecondProofSystem`, its caller is the chain's admin, the diamond is on its
settlement layer and the step sets the requirement, or the step is a break-glass cut of that
chain. An upgrade by any path, by any caller and at any time leaves it alone. -/
def Properties.TimedRequirementWriters : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (l : TimedLabel35) (id : ChainId)
    (c : Chain), TimedStep35 T P s l s' → s.timed.sys.chains id = some c →
    (s'.proof id).required ≠ (s.proof id).required →
    (∃ caller, l = .requireSecondProofSystem id caller ∧ caller = (s.timed.aux id).admin ∧
        (s.timed.aux id).slVersion = none ∧ (s'.proof id).required = true) ∨
      ∃ v ρ, l = .timed (.base (.arbitraryCut id v ρ))

/-- **"NO WAY BACK", EXCEPT BY BREAK-GLASS, ALONG v35 TIMED RUNS** (`IAdmin.sol:137-140`). Along
any v35 timed run with no break-glass cut of chain `id`, a registered chain that requires its
second proof system still requires it at the end. As in `ProofGateAtV35`, this is about the
chain's diamond on the modelled CTM, upgraded by the in-tree engines. -/
def Properties.TimedRequirementIsPermanentWithoutBreakGlass : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (ls : List TimedLabel35)
    (id : ChainId) (c : Chain), TimedRun35 T P s ls s' → s.timed.sys.chains id = some c →
    (s.proof id).required = true →
    (∀ v ρ, TimedLabel35.timed (.base (.arbitraryCut id v ρ)) ∉ ls) →
    (s'.proof id).required = true

/-! ## The NatSpec of `upgradeChain`, at v35 -/

/-- **THE EXECUTOR PATH IGNORES THE NOTIFIER AT v35** (`ICTMUpgradeExecutor.sol:53-54`). As
`Contracts.ChainTypeManager.Properties.ExecutorPathIgnoresNotifier`: replacing the notifier's
whole schedule changes neither which `upgradeChain` calls succeed nor what they do, to the timed
state and to the proof-system fields. -/
def Properties.ExecutorPathIgnoresNotifier : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s : TimedSys35) (id : ChainId) (t caller : Address)
    (τ : ℕ) (n : ChainId → ℕ → ℕ),
    (∀ (sys' : Sys) (pr' : ChainId → ProofState),
      TimedStep35 T P s (.timed (.upgrade id (.executor t) caller τ))
          ⟨{ s.timed with sys := sys' }, pr'⟩ ↔
        TimedStep35 T P ⟨{ s.timed with notifier := n }, s.proof⟩
          (.timed (.upgrade id (.executor t) caller τ))
          ⟨{ s.timed with notifier := n, sys := sys' }, pr'⟩) ∧
    ((∃ s', TimedStep35 T P s (.timed (.upgrade id (.executor t) caller τ)) s') ↔
      ∃ s', TimedStep35 T P ⟨{ s.timed with notifier := n }, s.proof⟩
        (.timed (.upgrade id (.executor t) caller τ)) s')

/-- **THE PROOF GATE BINDS EVERY PATH.** Whatever the path, the caller and the time, a v35
upgrade of a chain that requires its second proof system installs the verifier of the release
its edge arrives at, and that verifier reports multi-proof mode with nothing disabled. -/
def Properties.ProofGateBindsEveryPath : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (id : ChainId) (path : UpgradePath)
    (caller : Address) (τ : ℕ) (c : Chain),
    TimedStep35 T P s (.timed (.upgrade id path caller τ)) s' → s.timed.sys.chains id = some c →
    (s.proof id).required = true →
    P.multi (arrivingVerifier T.X.W P s.timed.sys c) 0 = true ∧
      (s'.proof id).verifier = arrivingVerifier T.X.W P s.timed.sys c

/-- **EXACTLY WHEN `upgradeChain` SUCCEEDS AT v35.** `upgradeChain(t, id)` by `caller` at time `τ`
succeeds iff the eight conditions of
`Contracts.ChainTypeManager.Properties.UpgradeChainEnabledIffTimed` hold and, if chain `id`
requires its second proof system, the verifier of `t`'s new release reports multi-proof mode with
nothing disabled. The notifier still does not appear. -/
def Properties.UpgradeChainEnabledIffTimed : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s : TimedSys35) (id : ChainId) (t caller : Address)
    (τ : ℕ),
    (∃ s', TimedStep35 T P s (.timed (.upgrade id (.executor t) caller τ)) s') ↔
      (((caller = T.execOwner ∨ caller = (s.timed.aux id).admin) ∧
        s.timed.sys.ctm.ut (T.X.W.tr t).old = t ∧ T.X.rc.self = T.ctmOwner ∧
        (∃ c, s.timed.sys.chains id = some c ∧ c.pv = (T.X.W.tr t).old) ∧
        (T.sched t).upgradeTimestamp ≤ τ ∧
        (s.timed.aux id).committed = (s.timed.aux id).executed ∧
        (∀ w, (s.timed.aux id).slVersion = some w → (T.X.W.tr t).new ≤ w) ∧
        ∃ sys', Step T.X.W s.timed.sys (.transition id) sys') ∧
      ((s.proof id).required = true → P.multi (P.relVerifier (T.X.W.tr t).newRel) 0 = true))

/-! ## Not at any time, at v35 -/

/-- **NOBODY CAN UPGRADE BEFORE THE MANIFEST'S TIME, AT v35** (refutes `ICTMUpgradeExecutor.sol:48-49`
at `d9f6789`). For every proof world: the instance of
`Contracts.ChainTypeManager.Properties.NotAtAnyTime`, run at v35 from `wTimingSys35`. At time `9`
neither the executor's owner `2` nor the chain's admin `3` can upgrade chain `0` through
`upgradeChain`, and nobody can by any path; at time `10` both can, through `upgradeChain(300, 0)`. -/
def Properties.NotAtAnyTime : Prop :=
  ∀ P : ProofWorld, ∃ s, TimedRun35 wTiming P wTimingSys35 (wTimingSetup.map TimedLabel35.timed) s ∧
    s.timed.sys.ctm.ut 1 = 300 ∧ (wTiming.sched 300).upgradeTimestamp = 10 ∧
    (∃ c, s.timed.sys.chains 0 = some c ∧ c.pv = 1) ∧ wTiming.execOwner = 2 ∧
    (s.timed.aux 0).admin = 3 ∧
    (∀ t, ¬ ∃ s', TimedStep35 wTiming P s (.timed (.upgrade 0 (.executor t) 2 9)) s') ∧
    (∀ t, ¬ ∃ s', TimedStep35 wTiming P s (.timed (.upgrade 0 (.executor t) 3 9)) s') ∧
    (∀ path caller, ¬ ∃ s', TimedStep35 wTiming P s (.timed (.upgrade 0 path caller 9)) s') ∧
    (∃ s', TimedStep35 wTiming P s (.timed (.upgrade 0 (.executor 300) 2 10)) s') ∧
    (∃ s', TimedStep35 wTiming P s (.timed (.upgrade 0 (.executor 300) 3 10)) s')

/-- **AT v35 THE OWNER CANNOT UPGRADE A CHAIN THAT REQUIRES ITS SECOND PROOF SYSTEM ACROSS AN EDGE
TO A RELEASE WITH A PLONK-ONLY VERIFIER, AT ANY TIME.** With `wProofPlonk` (release `200`'s
verifier `52` is PLONK-only), run `wTimingGateSetup` from `wTimingSys35`: chain `0` is created
and configured with admin `3`, the admin requires its second proof system (verifier `51`, in
multi-proof mode), the CTM commits `300` (1→2, onto release `200`), and the admin schedules
version 1 for time `12`.
* At every time from `10` on, every condition of
  `Contracts.ChainTypeManager.Properties.UpgradeChainEnabledIffTimed` holds for
  `upgradeChain(300, 0)` by the executor's owner `2`, and `UpgradeTiming` lets it upgrade.
* At v35 nobody can upgrade chain `0`, by any path, at any time. -/
def Properties.OwnerCannotUpgradeARequiringChainToAPlonkRelease : Prop :=
  ∃ s, TimedRun35 wTiming wProofPlonk wTimingSys35 wTimingGateSetup s ∧
    (s.proof 0).required = true ∧ wProofPlonk.multi (s.proof 0).verifier 0 = true ∧
    (∀ τ, 10 ≤ τ →
      ((2 = wTiming.execOwner ∨ 2 = (s.timed.aux 0).admin) ∧
        s.timed.sys.ctm.ut (wTiming.X.W.tr 300).old = 300 ∧ wTiming.X.rc.self = wTiming.ctmOwner ∧
        (∃ c, s.timed.sys.chains 0 = some c ∧ c.pv = (wTiming.X.W.tr 300).old) ∧
        (wTiming.sched 300).upgradeTimestamp ≤ τ ∧
        (s.timed.aux 0).committed = (s.timed.aux 0).executed ∧
        (∀ w, (s.timed.aux 0).slVersion = some w → (wTiming.X.W.tr 300).new ≤ w) ∧
        ∃ sys', Step wTiming.X.W s.timed.sys (.transition 0) sys') ∧
      ∃ t', TimedStep wTiming s.timed (.upgrade 0 (.executor 300) 2 τ) t') ∧
    ∀ path caller τ, ¬ ∃ s', TimedStep35 wTiming wProofPlonk s (.timed (.upgrade 0 path caller τ)) s'

/-- **THE v35 PREMISES ARE MET, AND A CHAIN THAT REQUIRES ITS SECOND PROOF SYSTEM IS UPGRADED
THROUGH `upgradeChain`.** With `wProofMulti` (release `200` ships the multi-proof verifier `53`),
run `wTimingGateSetup` from `wTimingSys35`, whose routing system satisfies `SysInv`, then
`upgradeChain(300, 0)` by the chain's admin `3` at time `10`. The run has no break-glass cut. At
the end chain `0` is at version 2 on release `200`, still requires its second proof system, and
has verifier `53` installed, which is in multi-proof mode. -/
def Properties.UpgradeTimingAtV35Witness : Prop :=
  SysInv wTiming.X.W wTimingSys35.timed.sys ∧
    ∃ s, TimedRun35 wTiming wProofMulti wTimingSys35
        (wTimingGateSetup ++ [.timed (.upgrade 0 (.executor 300) 3 10)]) s ∧
      (∀ l ∈ wTimingGateSetup ++ [.timed (.upgrade 0 (.executor 300) 3 10)], ¬ l.isArbitrary) ∧
      (∃ c, s.timed.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)) ∧
      (s.proof 0).required = true ∧ (s.proof 0).verifier = 53 ∧ wProofMulti.multi 53 0 = true

end Contracts.ChainTypeManager.UpgradeTimingAtV35
