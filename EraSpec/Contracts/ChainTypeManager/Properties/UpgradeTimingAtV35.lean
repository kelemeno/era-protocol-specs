import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTimingAtV35
import EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTimingStrong
import EraSpec.Core.Headline

/-!
# Properties: who may upgrade a chain, and when, at `draft/v0.35.0`

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.UpgradeTimingAtV35` (commit
`b17415d20`). Proofs are in `EraSpec.Contracts.ChainTypeManager.Proofs.UpgradeTimingAtV35`. The
statements live in `Contracts.ChainTypeManager.UpgradeTimingAtV35.Properties`; a statement named
like one of `UpgradeTiming` is that statement over the v35 system.

## Do the `UpgradeTiming` theorems describe v35?

For a chain that does not require its second proof system, yes. For a chain that does, an
upgrade has one more condition.

* A v35 timed step is the `UpgradeTiming` timed step (first written at `e561b9cc2`; it
  omits the proof-system checks) plus `TimedGateHolds`
  (`TimedStepIsTheUngatedStepPlusTheGate`). For a chain that does not require its second proof
  system, the gate is vacuous and an upgrade succeeds at v35 exactly when it does in
  `UpgradeTiming`, with the same effect on the timed state (`UnflaggedChainsUpgradeAsUngated`).
  Every `UpgradeTiming` run is the timed image of a v35 run in which no chain requires it
  (`UngatedTimedRunsAreRunsWithoutTheRequirement`).
* Every necessary condition `UpgradeTiming` proves for a timed run still binds, because the
  timed image of every v35 timed run is an `UpgradeTiming` run (`TimedRunIsATimedRun`). That
  covers `ManifestTimestampGates`, `EveryPathNeedsExecutedBatches`,
  `EveryPathNeedsTheSettlementLayerAhead`, `OtherCallersNeedTheNotifier` and the routing headline
  (`TimedRunKeepsChainsOnTheirRelease`, restated here).
* `ICTMUpgradeExecutor.sol:53-54` still holds: whether the executor's call succeeds, and what it
  does, does not depend on the notifier (`ExecutorPathIgnoresNotifier`).
* `ICTMUpgradeExecutor.sol:48-49` ("at any time") is still false, through the same instance
  (`NotAtAnyTime`, for every proof world). At v35 it fails in a second way: an upgrade of a
  chain that requires its second proof system needs the arriving release's verifier in
  multi-proof mode, whatever the path, the caller and the time (`ProofGateBindsEveryPath`). In
  the state of `OwnerCannotUpgradeARequiringChainToAPlonkRelease`, every condition of
  `UpgradeTiming`'s repaired statement holds for the owner from time 10 on, yet no upgrade of
  the chain exists, by any path, for any caller, at any block time.
* **The repaired statement at v35** is `UpgradeChainEnabledIffTimed`: `UpgradeTiming`'s eight
  conditions plus "if the chain requires its second proof system, the verifier of the
  transition's new release reports multi-proof mode with nothing disabled". As in
  `UpgradeTiming`, it is exact for the model; in the source these conditions are necessary, not
  sufficient, since further reject-only checks are omitted.

## `UpgradeTiming`'s other step results at v35

Restated over v35 timed steps, under the same names: `UpgradeIsATransition` (a
`ProofGateAtV35` transition), `ManifestTimestampGates`, `EveryPathNeedsExecutedBatches`,
`EveryPathNeedsTheSettlementLayerAhead`, `OtherCallersNeedTheNotifier`,
`NotifierWrittenOnlyByItsChainAdmin`, `CtmPathIsADiamondCallByTheCtm`,
`ExecutorPathIsACtmCallByTheExecutor`, `AdminAndCtmSkipTheNotifier` and
`UpgradeStaysEnabledLater`. `UpgradeTimingStrong`'s headline is restated as
`ValidatedTimedRunsHaveNoDeadTime`, with the gate on the arriving release's verifier as one more
premise, which `OwnerCannotUpgradeARequiringChainToAPlonkRelease` shows cannot be dropped.

## The proof-system guarantees along timed runs

The routing image of a v35 timed run is a `ProofGateAtV35` run of its routing steps and its
proof-system writes (`TimedRunIsAProofGateRun`), so that file's results hold along timed runs:

* from a state where `ProofInv` holds, a chain that requires its second proof system keeps a
  verifier that reports multi-proof mode for the empty mask
  (`TimedRunsKeepAMultiProofVerifier`);
* a registered chain's requirement is set by `permanentlyRequireSecondProofSystem`, called by
  the chain's admin while the diamond is on its settlement layer, and otherwise changed only by
  a break-glass cut of the chain (`TimedRequirementWriters`);
* without such a cut it stays set (`TimedRequirementIsPermanentWithoutBreakGlass`).

The caller of `setProofSystemStatus` is not modelled; its mask write is arbitrary, as in
`ProofGateAtV35`.

## Witnesses

`UpgradeTimingAtV35Witness` is a v35 run in which a chain that requires its second proof system
is upgraded through `upgradeChain` by its admin; it meets the premises of the run-level results
and of `ProofGateBindsEveryPath`. `TimedRequirementWritersWitness` is the setup's successful
`permanentlyRequireSecondProofSystem` by the admin, which a validator's call cannot replace.
`UnflaggedUpgradeWitness` meets the premises of `UngatedTimedRunsAreRunsWithoutTheRequirement` and
`UnflaggedChainsUpgradeAsUngated` with an upgrade that exists on both sides.
`NotAtAnyTime` and `OwnerCannotUpgradeARequiringChainToAPlonkRelease` are the countermodels.
-/

namespace Contracts.ChainTypeManager.UpgradeTimingAtV35

open Contracts.ChainTypeManager
open Contracts.ChainTypeManager.ProofGateAtV35

/-! ## The v35 timed step and run -/

/-- **EVERY v35 TIMED STEP IS THE `UpgradeTiming` TIMED STEP PLUS THE PROOF GATE.** For every
`UpgradeTiming` label `l` and timed state `t'`, a v35 step labelled `l` that leaves `t'` exists,
with some proof-system fields, iff `UpgradeTiming`'s step `l` to `t'` exists and `TimedGateHolds`
holds before it. -/
def Properties.TimedStepIsTheUngatedStepPlusTheGate : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s : TimedSys35) (l : TimedLabel) (t' : TimedSys),
    (∃ pr', TimedStep35 T P s (.timed l) ⟨t', pr'⟩) ↔
      (TimedStep T s.timed l t' ∧ TimedGateHolds T P s l)

/-- **A v35 TIMED RUN IS AN `UpgradeTiming` RUN.** Forgetting the proof-system fields, every v35
timed run is a run of `UpgradeTiming` of its timed labels, in order. -/
def Properties.TimedRunIsATimedRun : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (ls : List TimedLabel35),
    TimedRun35 T P s ls s' → TimedRun T s.timed (ls.flatMap TimedLabel35.timedSteps) s'.timed

/-- **EVERY `UpgradeTiming` RUN IS A v35 RUN IN WHICH NO CHAIN REQUIRES ITS SECOND PROOF
SYSTEM.** Starting from any proof-system fields with the requirement off everywhere, the same
labels run at v35 to the same timed state, and the requirement is still off everywhere. -/
def Properties.UngatedTimedRunsAreRunsWithoutTheRequirement : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys) (ls : List TimedLabel)
    (pr : ChainId → ProofState), TimedRun T s ls s' → (∀ id, (pr id).required = false) →
    ∃ pr', TimedRun35 T P ⟨s, pr⟩ (ls.map TimedLabel35.timed) ⟨s', pr'⟩ ∧
      ∀ id, (pr' id).required = false

/-- **FOR A CHAIN THAT DOES NOT REQUIRE ITS SECOND PROOF SYSTEM, AN UPGRADE SUCCEEDS AT v35 EXACTLY
WHEN IT DOES IN `UpgradeTiming`**, by every path, for every caller and at every time, with the
same effect on the timed state. -/
def Properties.UnflaggedChainsUpgradeAsUngated : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s : TimedSys35) (id : ChainId) (path : UpgradePath)
    (caller : Address) (τ : ℕ) (t' : TimedSys), (s.proof id).required = false →
    ((∃ pr', TimedStep35 T P s (.timed (.upgrade id path caller τ)) ⟨t', pr'⟩) ↔
      TimedStep T s.timed (.upgrade id path caller τ) t')

/-- **THE ROUTING HEADLINE ALONG v35 TIMED RUNS.** As
`Contracts.ChainTypeManager.Properties.TimedRunKeepsChainsOnTheirRelease`, over v35 timed runs:
from a state whose routing system satisfies `SysInv`, with no break-glass cut, every chain at a
version `v` with a release `R_v` routes exactly `R_v`, which is a release of version `v`. -/
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
runs, break-glass cuts included (each making the v35 `Admin` facet's final check, as there): from
a state where `ProofInv` holds, every registered chain that requires its second proof system has
a verifier that reports multi-proof mode for the empty mask. The verifiers must satisfy
`DisablingNeverEnablesMultiProof`. -/
def Properties.TimedRunsKeepAMultiProofVerifier : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (ls : List TimedLabel35),
    DisablingNeverEnablesMultiProof P → ProofInv P s.routing → TimedRun35 T P s ls s' →
    ProofInv P s'.routing

/-- **THE REQUIREMENT'S WRITER SUCCEEDS ONLY FOR THE CHAIN'S ADMIN, ON ITS SETTLEMENT LAYER; ONLY A
BREAK-GLASS CUT OF THE CHAIN CHANGES IT OTHERWISE.** If a v35 timed step changes a registered
chain's `secondProofSystemRequired`, then either the step is that chain's
`permanentlyRequireSecondProofSystem`, its caller is the chain's admin, the diamond is on its
settlement layer and the step sets the requirement, or the step is a break-glass cut of that
chain (which may set or clear it). An upgrade by any path, by any caller and at any time leaves
it alone. The caller and settlement-layer conjuncts restate the modelled `onlyAdmin` and
`onlySettlementLayer` modifiers (`facets/ZKChainBase.sol:46-51`, `:141-146`), which are premises of
`TimedStep35.requireSecondProofSystem`; the result checks that transcription and that no other
step writes the field. -/
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
@[headline] def Properties.ExecutorPathIgnoresNotifier : Prop :=
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
@[headline] def Properties.ProofGateBindsEveryPath : Prop :=
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
nothing disabled. The notifier still does not appear. As there, "succeeds" is relative to the
checks the model keeps. -/
@[headline] def Properties.UpgradeChainEnabledIffTimed : Prop :=
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

/-! ## `UpgradeTiming`'s step results over v35 timed steps

Each statement below is the `UpgradeTiming` statement of the same name, over `TimedStep35`. The
necessary conditions transfer through the projection of a v35 timed step to its `UpgradeTiming`
step; the equivalences transfer because the gate an upgrade adds (`TimedGateHolds`) reads only the
chain, its proof-system fields and the routing state, never the path, the caller, the block time
or the notifier. -/

/-- **AN UPGRADE BY ANY PATH IS A v35 TRANSITION.** A v35 upgrade of chain `id`, by any path,
caller and time, is a `ProofGateAtV35` transition of `id` on the routing view, and writes neither
`DiamondAux` nor the notifier. -/
def Properties.UpgradeIsATransition : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (id : ChainId) (path : UpgradePath)
    (caller : Address) (τ : ℕ), TimedStep35 T P s (.timed (.upgrade id path caller τ)) s' →
    Step35 T.X.W P s.routing (.routing (.transition id)) s'.routing ∧
      s'.timed.aux = s.timed.aux ∧ s'.timed.notifier = s.timed.notifier

/-- **NO v35 UPGRADE BEFORE THE MANIFEST'S TIME.** As
`Contracts.ChainTypeManager.Properties.ManifestTimestampGates`, over v35 timed steps: every
upgrade, by any path, happens at or after the `upgradeTimestamp` of the transition committed at
the chain's version. -/
@[headline] def Properties.ManifestTimestampGates : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (id : ChainId) (path : UpgradePath)
    (caller : Address) (τ : ℕ), TimedStep35 T P s (.timed (.upgrade id path caller τ)) s' →
    ∃ c, s.timed.sys.chains id = some c ∧
      (T.sched (s.timed.sys.ctm.ut c.pv)).upgradeTimestamp ≤ τ

/-- **EVERY v35 UPGRADE NEEDS ALL COMMITTED BATCHES EXECUTED.** As
`Contracts.ChainTypeManager.Properties.EveryPathNeedsExecutedBatches`, over v35 timed steps. -/
@[headline] def Properties.EveryPathNeedsExecutedBatches : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (id : ChainId) (path : UpgradePath)
    (caller : Address) (τ : ℕ), TimedStep35 T P s (.timed (.upgrade id path caller τ)) s' →
    (s.timed.aux id).committed = (s.timed.aux id).executed

/-- **EVERY v35 UPGRADE NEEDS THE SETTLEMENT LAYER AHEAD.** As
`Contracts.ChainTypeManager.Properties.EveryPathNeedsTheSettlementLayerAhead`, over v35 timed
steps: if the chain records a settlement-layer version `w`, the edge's new version is at most
`w`. -/
@[headline] def Properties.EveryPathNeedsTheSettlementLayerAhead : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (id : ChainId) (path : UpgradePath)
    (caller : Address) (τ w : ℕ), TimedStep35 T P s (.timed (.upgrade id path caller τ)) s' →
    (s.timed.aux id).slVersion = some w →
    ∃ c, s.timed.sys.chains id = some c ∧ (s.timed.sys.edge T.X.W c.pv).new ≤ w

/-- **AT v35 A VALIDATOR'S DIRECT UPGRADE NEEDS THE NOTIFIER.** As
`Contracts.ChainTypeManager.Properties.OtherCallersNeedTheNotifier`, over v35 timed steps: a
direct `upgradeChainFromVersion` by a caller that is neither the chain's admin nor the CTM is by
one of the chain's validators, at or after a nonzero time the notifier holds for the version. -/
@[headline] def Properties.OtherCallersNeedTheNotifier : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (id : ChainId) (v : ℕ)
    (caller : Address) (τ : ℕ), TimedStep35 T P s (.timed (.upgrade id (.direct v) caller τ)) s' →
    caller ≠ (s.timed.aux id).admin → caller ≠ T.X.ctmProxy →
    (s.timed.aux id).validators caller = true ∧ s.timed.notifier id v ≠ 0 ∧
      s.timed.notifier id v ≤ τ

/-- **AT v35 ONLY THE CHAIN'S ADMIN WRITES ITS NOTIFIER ENTRY.** As
`Contracts.ChainTypeManager.Properties.NotifierWrittenOnlyByItsChainAdmin`, over v35 timed steps
of every label, the two proof-system writers included: a step that changes the notifier's entry
for chain `id` and version `v` is the chain admin's `setUpgradeTimestamp` for the chain's current
version with a nonzero time, which it writes, or a swap of the notifier. -/
def Properties.NotifierWrittenOnlyByItsChainAdmin : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (l : TimedLabel35) (id : ChainId)
    (v : ℕ), TimedStep35 T P s l s' → s'.timed.notifier id v ≠ s.timed.notifier id v →
    (∃ caller ts c, l = .timed (.setUpgradeTimestamp id caller ts) ∧
      caller = (s.timed.aux id).admin ∧ s.timed.sys.chains id = some c ∧ c.pv = v ∧ ts ≠ 0 ∧
      s'.timed.notifier id v = ts) ∨
    ∃ n, l = .timed (.swapNotifier n)

/-- **AT v35 THE CTM PATH IS A DIAMOND CALL BY THE CTM.** As
`Contracts.ChainTypeManager.Properties.CtmPathIsADiamondCallByTheCtm`, over v35 timed steps: the
CTM owner's `upgradeChainFromVersion` on the CTM succeeds, with a given effect on the timed state
and on the proof-system fields, iff the caller is the CTM owner and the CTM's direct call on the
diamond does. -/
def Properties.CtmPathIsADiamondCallByTheCtm : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (id : ChainId) (v : ℕ)
    (caller : Address) (τ : ℕ),
    TimedStep35 T P s (.timed (.upgrade id (.ctm v) caller τ)) s' ↔
      caller = T.ctmOwner ∧ TimedStep35 T P s (.timed (.upgrade id (.direct v) T.X.ctmProxy τ)) s'

/-- **AT v35 THE EXECUTOR PATH IS A CTM CALL BY THE EXECUTOR.** As
`Contracts.ChainTypeManager.Properties.ExecutorPathIsACtmCallByTheExecutor`, over v35 timed
steps: `upgradeChain(t, id)` succeeds, with a given effect, iff the caller is the executor's owner
or the chain's admin, `t` is committed at its old version, and the executor's call of the CTM
path with that version does. -/
def Properties.ExecutorPathIsACtmCallByTheExecutor : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (id : ChainId) (t caller : Address)
    (τ : ℕ),
    TimedStep35 T P s (.timed (.upgrade id (.executor t) caller τ)) s' ↔
      (caller = T.execOwner ∨ caller = (s.timed.aux id).admin) ∧
      s.timed.sys.ctm.ut (T.X.W.tr t).old = t ∧
      TimedStep35 T P s (.timed (.upgrade id (.ctm (T.X.W.tr t).old) T.X.rc.self τ)) s'

/-- **AT v35 THE CHAIN'S ADMIN AND THE CTM SKIP THE NOTIFIER.** As
`Contracts.ChainTypeManager.Properties.AdminAndCtmSkipTheNotifier`, over v35 timed steps: for a
direct upgrade by the chain's admin or by the CTM, replacing the whole notifier changes neither
whether the call succeeds nor its effect on the routing state and the proof-system fields. -/
def Properties.AdminAndCtmSkipTheNotifier : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s : TimedSys35) (id : ChainId) (v : ℕ)
    (caller : Address) (τ : ℕ) (n : ChainId → ℕ → ℕ) (sys' : Sys) (pr' : ChainId → ProofState),
    (caller = (s.timed.aux id).admin ∨ caller = T.X.ctmProxy) →
    (TimedStep35 T P s (.timed (.upgrade id (.direct v) caller τ))
        ⟨{ s.timed with sys := sys' }, pr'⟩ ↔
      TimedStep35 T P ⟨{ s.timed with notifier := n }, s.proof⟩
        (.timed (.upgrade id (.direct v) caller τ))
        ⟨{ s.timed with notifier := n, sys := sys' }, pr'⟩)

/-- **A v35 UPGRADE STAYS ENABLED LATER.** As
`Contracts.ChainTypeManager.Properties.UpgradeStaysEnabledLater`, over v35 timed steps: an
upgrade that succeeds at time `τ` succeeds, with the same effect, at every later time. -/
def Properties.UpgradeStaysEnabledLater : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (s s' : TimedSys35) (id : ChainId) (path : UpgradePath)
    (caller : Address) (τ τ' : ℕ), TimedStep35 T P s (.timed (.upgrade id path caller τ)) s' →
    τ ≤ τ' → TimedStep35 T P s (.timed (.upgrade id path caller τ')) s'

/-- **NO DEAD TIME AT v35, GIVEN THE GATE** (`UpgradeTimingStrong`'s
`ValidatedTimedRunsHaveNoDeadTime`, over v35 timed runs). Along a v35 timed run with no
break-glass cut, from an invariant state whose recorded releases are well-formed and whose
committed slots have valid schedules, in which every timed transaction installs only well-formed
releases and commits only valid schedules: take a registered chain whose version has a committed
edge and no deadline override, with every committed batch executed and, if it records a
settlement-layer version, the edge's new version at most that. If the chain requires its second
proof system, assume the arriving release's verifier reports multi-proof mode with nothing
disabled. Then at every block time the chain's version is active or both its admin's direct call
and the CTM owner's call upgrade it across the edge; at the edge's upgrade time the version is
still active and both calls succeed. The successful upgrade crosses the edge and installs the
arriving release's verifier. Without the gate premise the conclusion fails
(`OwnerCannotUpgradeARequiringChainToAPlonkRelease`). -/
@[headline] def Properties.ValidatedTimedRunsHaveNoDeadTime : Prop :=
  ∀ (T : TimedConfig) (P : ProofWorld) (d : ℕ → ℕ) (s s' : TimedSys35)
    (ls : List TimedLabel35),
    SysInv T.X.W s.timed.sys → RecordedReleasesWf T.X.W s.timed.sys.ctm →
    SlotSchedulesValid T s.timed.sys.ctm → TimedRun35 T P s ls s' →
    (∀ l ∈ ls, ¬ l.isArbitrary) → (∀ l ∈ ls.flatMap TimedLabel35.timedSteps, l.InstallsWf T.X.W) →
    (∀ l ∈ ls.flatMap TimedLabel35.timedSteps, l.CommitsValidSchedule T) →
    ∀ id c, s'.timed.sys.chains id = some c → s'.timed.sys.ctm.ut c.pv ≠ 0 → d c.pv = 0 →
      (s'.timed.aux id).committed = (s'.timed.aux id).executed →
      (∀ w, (s'.timed.aux id).slVersion = some w → (s'.timed.sys.edge T.X.W c.pv).new ≤ w) →
      ((s'.proof id).required = true → P.multi (arrivingVerifier T.X.W P s'.timed.sys c) 0 = true) →
      (∀ τ, ProtocolVersionActive T d s'.timed.sys.ctm c.pv τ ∨
        (TimedStep35 T P s' (.timed (.upgrade id (.direct c.pv) (s'.timed.aux id).admin τ))
          ⟨{ s'.timed with sys := s'.timed.sys.crossEdge T.X.W id c },
          upd s'.proof id ((s'.proof id).install (arrivingVerifier T.X.W P s'.timed.sys c))⟩ ∧
         TimedStep35 T P s' (.timed (.upgrade id (.ctm c.pv) T.ctmOwner τ))
          ⟨{ s'.timed with sys := s'.timed.sys.crossEdge T.X.W id c },
          upd s'.proof id ((s'.proof id).install (arrivingVerifier T.X.W P s'.timed.sys c))⟩)) ∧
      ProtocolVersionActive T d s'.timed.sys.ctm c.pv
        (T.sched (s'.timed.sys.ctm.ut c.pv)).upgradeTimestamp ∧
      TimedStep35 T P s' (.timed (.upgrade id (.direct c.pv) (s'.timed.aux id).admin
          (T.sched (s'.timed.sys.ctm.ut c.pv)).upgradeTimestamp))
        ⟨{ s'.timed with sys := s'.timed.sys.crossEdge T.X.W id c },
          upd s'.proof id ((s'.proof id).install (arrivingVerifier T.X.W P s'.timed.sys c))⟩ ∧
      TimedStep35 T P s' (.timed (.upgrade id (.ctm c.pv) T.ctmOwner
          (T.sched (s'.timed.sys.ctm.ut c.pv)).upgradeTimestamp))
        ⟨{ s'.timed with sys := s'.timed.sys.crossEdge T.X.W id c },
          upd s'.proof id ((s'.proof id).install (arrivingVerifier T.X.W P s'.timed.sys c))⟩

/-! ## Not at any time, at v35 -/

/-- **NOBODY CAN UPGRADE BEFORE THE MANIFEST'S TIME, AT v35** (refutes `ICTMUpgradeExecutor.sol:48-49`
at `b17415d20`). For every proof world: the instance of
`Contracts.ChainTypeManager.Properties.NotAtAnyTime`, run at v35 from `wTimingSys35`. At time `9`
neither the executor's owner `2` nor the chain's admin `3` can upgrade chain `0` through
`upgradeChain`, and nobody can by any path; at time `10` both can, through `upgradeChain(300, 0)`. -/
@[countermodel] def Properties.NotAtAnyTime : Prop :=
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
TO A RELEASE WITH A PLONK-ONLY VERIFIER, AT ANY BLOCK TIME.** With `wProofPlonk` (release `200`'s
verifier `52` is PLONK-only), run `wTimingGateSetup` from `wTimingSys35`: chain `0` is created
and configured with admin `3`, the admin requires its second proof system (verifier `51`, in
multi-proof mode), the CTM commits `300` (1→2, onto release `200`), and the admin schedules
version 1 for time `12`. In the state this reaches:
* at every time from `10` on, every condition of
  `Contracts.ChainTypeManager.Properties.UpgradeChainEnabledIffTimed` holds for
  `upgradeChain(300, 0)` by the executor's owner `2`, and `UpgradeTiming` lets it upgrade;
* no v35 upgrade of chain `0` exists, by any path, for any caller, at any block time.
`protocol-docs/interop-gating.md:43-48` (at `b17415d20`) describes such an edge and leaves its
prevention to off-chain package verification. -/
@[countermodel] def Properties.OwnerCannotUpgradeARequiringChainToAPlonkRelease : Prop :=
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

/-! ## Witnesses -/

/-- **THE v35 PREMISES ARE MET, AND A CHAIN THAT REQUIRES ITS SECOND PROOF SYSTEM IS UPGRADED
THROUGH `upgradeChain`.** With `wProofMulti` (release `200` ships the multi-proof verifier `53`;
the verifiers satisfy `DisablingNeverEnablesMultiProof`), start from `wTimingSys35`, whose
routing system satisfies `SysInv` and whose fields satisfy `ProofInv`. Run `wTimingGateSetup` to
a state `s` in which chain `0` is registered and requires its second proof system, then take
`upgradeChain(300, 0)` by the chain's admin `3` at time `10`, to `s'`. The whole run has no
break-glass cut. At the end chain `0` is at version 2 on release `200`, still requires its second
proof system, and has verifier `53` installed, which is in multi-proof mode; `ProofInv` holds.
This meets the premises of `TimedRunIsATimedRun`, `TimedRunKeepsChainsOnTheirRelease`,
`TimedRunIsAProofGateRun`, `TimedRunsKeepAMultiProofVerifier`, `ProofGateBindsEveryPath` (the
last step, from `s`) and, through that step, `TimedRequirementIsPermanentWithoutBreakGlass`:
the statement gives the step from `s`, and the one-step run from `s` is that step followed by the
empty run. -/
@[witness] def Properties.UpgradeTimingAtV35Witness : Prop :=
  SysInv wTiming.X.W wTimingSys35.timed.sys ∧ ProofInv wProofMulti wTimingSys35.routing ∧
    DisablingNeverEnablesMultiProof wProofMulti ∧
    ∃ s s', TimedRun35 wTiming wProofMulti wTimingSys35 wTimingGateSetup s ∧
      TimedStep35 wTiming wProofMulti s (.timed (.upgrade 0 (.executor 300) 3 10)) s' ∧
      TimedRun35 wTiming wProofMulti wTimingSys35
        (wTimingGateSetup ++ [.timed (.upgrade 0 (.executor 300) 3 10)]) s' ∧
      (∀ l ∈ wTimingGateSetup ++ [.timed (.upgrade 0 (.executor 300) 3 10)], ¬ l.isArbitrary) ∧
      (∃ c, s.timed.sys.chains 0 = some c ∧ c.pv = 1) ∧ (s.proof 0).required = true ∧
      (∃ c, s'.timed.sys.chains 0 = some c ∧ c.pv = 2 ∧ c.routing = rowsRouting (wRows 200)) ∧
      (s'.proof 0).required = true ∧ (s'.proof 0).verifier = 53 ∧ wProofMulti.multi 53 0 = true ∧
      ProofInv wProofMulti s'.routing

/-- **THE REQUIREMENT IS SET BY THE CHAIN'S ADMIN, NOT BY ITS VALIDATOR.** With `wProofMulti`,
from `wTimingSys35`, chain `0` is created and configured (admin `3`, validator `4`, on its
settlement layer). Then `permanentlyRequireSecondProofSystem` on chain `0` by `3` is a step that
changes the registered chain's requirement from off to on: the premises of
`TimedRequirementWriters`, in its first case. The same call by `4` has no step. -/
@[witness] def Properties.TimedRequirementWritersWitness : Prop :=
  ∃ s s' c, TimedRun35 wTiming wProofMulti wTimingSys35
      [.timed (.base (.genesis 0)), .timed (.setAux 0 wTimingAux)] s ∧
    TimedStep35 wTiming wProofMulti s (.requireSecondProofSystem 0 3) s' ∧
    s.timed.sys.chains 0 = some c ∧ (s.timed.aux 0).admin = 3 ∧
    (s.timed.aux 0).validators 4 = true ∧ (s.timed.aux 0).slVersion = none ∧
    (s.proof 0).required = false ∧ (s'.proof 0).required = true ∧
    ¬ ∃ s'', TimedStep35 wTiming wProofMulti s (.requireSecondProofSystem 0 4) s''

/-- **AN UPGRADE OF A CHAIN THAT DOES NOT REQUIRE ITS SECOND PROOF SYSTEM, ON BOTH SIDES.** For
every proof world: the `UpgradeTiming` run `wTimingSetup` from `wTimingSys0`, with the all-off
fields of `wTimingSys35`, meets the premises of `UngatedTimedRunsAreRunsWithoutTheRequirement`, and
its v35 counterpart reaches a state whose timed part is the `UpgradeTiming` one and in which no
chain requires its second proof system (the premise of `UnflaggedChainsUpgradeAsUngated`). There
`upgradeChain(300, 0)` by the executor's owner `2` at time `10` is both an `UpgradeTiming` step and
a v35 step. -/
@[witness] def Properties.UnflaggedUpgradeWitness : Prop :=
  ∀ P : ProofWorld, ∃ s0 s, TimedRun wTiming wTimingSys0 wTimingSetup s0 ∧
    (∀ id, (wTimingSys35.proof id).required = false) ∧
    TimedRun35 wTiming P wTimingSys35 (wTimingSetup.map TimedLabel35.timed) s ∧ s.timed = s0 ∧
    (∀ id, (s.proof id).required = false) ∧
    (∃ t', TimedStep wTiming s.timed (.upgrade 0 (.executor 300) 2 10) t') ∧
    ∃ s', TimedStep35 wTiming P s (.timed (.upgrade 0 (.executor 300) 2 10)) s'

end Contracts.ChainTypeManager.UpgradeTimingAtV35
