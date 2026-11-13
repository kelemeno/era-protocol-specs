import EraSpec.Contracts.SecondProofSystem.Specs.UpgradeGateV35

/-!
# Properties: the second-proof gate on every chain upgrade (draft/v0.35.0)

Statements about `EraSpec.Contracts.SecondProofSystem.Specs.UpgradeGateV35`, at era-contracts
`d9f678900e1bc8286412b78f56d4a9f443983c29`. Proofs are in
`EraSpec.Contracts.SecondProofSystem.Proofs.UpgradeGateV35`.

## The source comments, checked

* **"A chain that requires its second proof system must keep a verifier that supports it"**
  (`BaseZkSyncUpgrade.sol:141`). True for every cut: after any successful cut of a chain whose
  flag is set at the end of the cut, its verifier answers MULTI under mask `0`
  (`FlaggedCutsKeepMultiProof`). Only a break-glass cut can clear the flag
  (`FlagSurvivesAllButBreakGlass`). Along every run, every flagged chain's verifier passes the
  gate, provided the verifiers answer MULTI under mask `0` whenever they do under some mask
  (`FlaggedChainsStayMultiProof`), which both deployed verifiers do
  (`MaskMonotoneHoldsForDeployedVerifiers`). Without that proviso a chain can be flagged on a
  verifier that fails the gate (`MaskMonotoneIsLoadBearing`).
* **The gate uses mask `0`** (`Admin.sol:122`, `BaseZkSyncUpgrade.sol:144`). So the emergency
  switch, which sets the Zisk bit of the chain's mask, never blocks an upgrade: whether an upgrade
  step exists does not depend on the chain's mask at all (`EmergencyOffDoesNotBlockUpgrades`). On
  the deployed multi-proof verifier, a flagged chain whose Zisk is switched off answers PLONK
  under its own mask, and still upgrades (`EmergencyOffFlaggedChainStillUpgrades`).
* **Commits do not look at the target's proof mode** (`ChainTypeManager.sol:403-418, 449-452`).
  Whether a CTM writer succeeds, and what it does, does not depend on any verifier
  (`CommitIgnoresProofMode`).

## The repaired characterisation

`UpgradeChainEnabledIffTimedV35` is `UpgradeTiming.UpgradeChainEnabledIffTimed` with two new
conjuncts: the target release's verifier is nonzero, and if the chain is flagged it answers
MULTI under mask `0`. Without them the statement is false at this commit
(`UpgradeChainEnabledIffTimedFailsV35`), and so is the analogue of
`Enabledness.UpgradesStayEnabled` (`UpgradesStayEnabledFailsV35`).

## A flagged chain can be locked out of a committed edge

A chain is `Locked` when it is flagged at `v`, the edge committed at `v` lands at the CTM's
version on its current release, and that release's verifier fails the gate. A locked chain cannot
upgrade by any path, caller or time (`LockedChainCannotUpgrade`). A replacement that lands at the
CTM's version is pinned to the current release (`ReplacementAtCurrentVersionIsPinned`), so no
replacement can fix it: along every run whose labels neither cut the chain by break-glass nor
move the CTM's version, the chain stays locked (`SameTargetReplacementCannotFix`). The escapes
are a CTM commit followed by a skip-replacement onto a later release, or a break-glass cut that
installs a MULTI verifier or clears the flag (`EscapesUnlockTheLockedChain`). Meanwhile the chain
can keep committing batches at `v` only until the edge's deadline, unless the CTM's owner
overrides it (`LockedChainNeedsDeadlineOverride`).

`FlaggedChainCannotCrossNonMultiProofEdge` is the countermodel: two chains at version 1 with
the same routing and `DiamondAux`, one flagged; the committed edge installs a single-proof
verifier. The unflagged chain crosses; the flagged one cannot, by any path, at any time, along
any run without an escape. A multi-proof target lets it cross, and dropping the
`currentRelease` pin admits a same-target replacement that lets it cross.

`UpgradeGateV35Witness` shows the premise bundles satisfiable on reachable states.
-/

namespace Contracts.SecondProofSystem

open Contracts.ChainTypeManager

/-! ## The gate holds -/

/-- **(a) FLAGGED CUTS KEEP A MULTI-PROOF VERIFIER.** After any successful step that cuts chain
`id`'s diamond (an upgrade by any path, genesis, migration in, the bootstrap reset, a break-glass
cut), if the chain's flag is set its verifier answers MULTI to `getProofMode(0)`. -/
def Properties.FlaggedCutsKeepMultiProof : Prop :=
  ∀ (G : GateConfig) (s s' : GSys) (l : GLabel) (id : ChainId), GStep G s l s' →
    l.CutsChain id → (s'.gate id).flag = true → IsMulti G (s'.gate id).verifier

/-- **THE FLAG IS ONE-WAY EXCEPT UNDER BREAK-GLASS.** For a registered chain, every successful
step other than a break-glass cut of that chain keeps its flag set. -/
def Properties.FlagSurvivesAllButBreakGlass : Prop :=
  ∀ (G : GateConfig) (s s' : GSys) (l : GLabel) (id : ChainId), GStep G s l s' →
    s.ts.sys.chains id ≠ none → (∀ v ρ g, l ≠ .breakGlass id v ρ g) →
    (s.gate id).flag = true → (s'.gate id).flag = true

/-- **EVERY FLAGGED CHAIN STAYS ON A MULTI-PROOF VERIFIER.** If every verifier that answers MULTI
under some mask answers MULTI under mask `0` (`MaskMonotone`), then along any run from a state
where every flagged chain's verifier passes the gate, every flagged chain's verifier passes it
at the end. -/
def Properties.FlaggedChainsStayMultiProof : Prop :=
  ∀ (G : GateConfig) (s s' : GSys) (ls : List GLabel), MaskMonotone G → GateInv G s →
    GRun G s ls s' → GateInv G s'

/-- **BOTH DEPLOYED VERIFIERS ARE MASK-MONOTONE**: among `uint8` masks,
`MultiProofVerifier.getProofMode` answers MULTI only under mask `0`, and it does answer MULTI
there; `ZKsyncOSVerifier.getProofMode` never answers MULTI. So the two witness configurations,
whose verifiers are these two, are `MaskMonotone`. -/
def Properties.MaskMonotoneHoldsForDeployedVerifiers : Prop :=
  (∀ d, d < 256 → multiProofMode d = some MULTI → d = 0) ∧ (∀ d, singleProofMode d ≠ some MULTI) ∧
    multiProofMode 0 = some MULTI ∧ MaskMonotone gCfg ∧ MaskMonotone gCfgMulti

/-- **WITHOUT MASK-MONOTONICITY A CHAIN CAN BE FLAGGED ON A VERIFIER THAT FAILS THE GATE.**
`permanentlyRequireSecondProofSystem` checks the chain's own mask (`Admin.sol:458`,
`ZKChainBase.sol:188-190`), the gate checks mask `0`. A verifier answering MULTI under mask
`ziskBit` and PLONK under `0` breaks `GateInv` in one step. -/
def Properties.MaskMonotoneIsLoadBearing : Prop :=
  ∃ (G : GateConfig) (s s' : GSys) (id : ChainId) (caller : Address),
    GateInv G s ∧ GStep G s (.requireSecondProof id caller) s' ∧ ¬ GateInv G s'

/-! ## The emergency switch and the CTM -/

/-- **(b) THE EMERGENCY SWITCH DOES NOT BLOCK UPGRADES.** The gate reads `getProofMode(0)`, not
`getProofMode(s.disabledProofSystems)`: an upgrade step of chain `id` exists exactly when it
exists with chain `id`'s mask replaced by any `d`. -/
def Properties.EmergencyOffDoesNotBlockUpgrades : Prop :=
  ∀ (G : GateConfig) (s : GSys) (id : ChainId) (path : UpgradePath) (caller : Address) (τ d : ℕ),
    (∃ s', GStep G s (.upgrade id path caller τ) s') ↔
      (∃ s', GStep G (s.withMask id d) (.upgrade id path caller τ) s')

/-- **A FLAGGED CHAIN WITH ZISK SWITCHED OFF STILL UPGRADES.** From `gLock` with every release
shipping the multi-proof verifier, the bridgehub owner `9` switches chain `0`'s Zisk off. The
chain is flagged, its mask is `ziskBit`, and its verifier answers PLONK under that mask, so a
gate that read the chain's own mask would reject. Yet `upgradeChain(300, 0)` succeeds. -/
def Properties.EmergencyOffFlaggedChainStillUpgrades : Prop :=
  ∃ s1 : GSys, GStep gCfgMulti gLock (.setProofSystemStatus 0 9 false) s1 ∧
    (s1.gate 0).flag = true ∧ (s1.gate 0).disabled = ziskBit ∧
    gCfgMulti.proofMode (s1.gate 0).verifier (s1.gate 0).disabled = some PLONK ∧
    gCfgMulti.proofMode (edgeVerifier gCfgMulti s1 1) (s1.gate 0).disabled ≠ some MULTI ∧
    ∃ s2, GStep gCfgMulti s1 (.upgrade 0 (.executor 300) 3 10) s2

/-- **(c) THE CTM'S WRITERS NEVER READ A VERIFIER.** A commit, replacement, legacy commit or
legacy recut on the gated system is exactly `VersionRegistry`'s `CStep` on the CTM's version
state, leaving every chain and every gate field as it was. So whether it succeeds, and the state
it leaves, do not depend on the verifiers' `getProofMode`, on which verifier each release ships,
or on any chain's flag.

This holds by construction of the model: the source's commit path
(`ChainTypeManager.sol:403-418, 449-452, 300-318`) contains no call of `getProofMode`, and the
model adds none. `FlaggedChainCannotCrossNonMultiProofEdge` shows such a commit succeeding with
a flagged chain at its departing version and a single-proof target. -/
def Properties.CommitIgnoresProofMode : Prop :=
  ∀ (G : GateConfig) (s s' : GSys) (op : Op),
    (GStep G s (.other (.base (.ctm op))) s' ↔
      ∃ c', CStep G.T.X.W s.ts.sys.ctm op c' ∧
        s' = ⟨{ s.ts with sys := { s.ts.sys with ctm := c' } }, s.gate⟩) ∧
    ∀ (pm : Address → ℕ → Option ℕ) (rv : Address → Address),
      (GStep G s (.other (.base (.ctm op))) s' ↔
        GStep { G with proofMode := pm, relVerifier := rv } s (.other (.base (.ctm op))) s')

/-! ## The repaired characterisation -/

/-- **(d) WHEN `upgradeChain(t, id)` SUCCEEDS, AT d9f67890.** Exactly when the conditions of
`UpgradeTiming.UpgradeChainEnabledIffTimed` hold and, in addition:
* the verifier of `t`'s `newRelease()` is nonzero (`DefaultUpgrade.sol:69-71`);
* if chain `id` is flagged, that verifier answers MULTI to `getProofMode(0)`
  (`BaseZkSyncUpgrade.sol:143-148`, `Admin.sol:121-126`). -/
def Properties.UpgradeChainEnabledIffTimedV35 : Prop :=
  ∀ (G : GateConfig) (s : GSys) (id : ChainId) (t caller : Address) (τ : ℕ),
    (∃ s', GStep G s (.upgrade id (.executor t) caller τ) s') ↔
      ((caller = G.T.execOwner ∨ caller = (s.ts.aux id).admin) ∧
        s.ts.sys.ctm.ut (G.T.X.W.tr t).old = t ∧ G.T.X.rc.self = G.T.ctmOwner ∧
        (∃ c, s.ts.sys.chains id = some c ∧ c.pv = (G.T.X.W.tr t).old) ∧
        (G.T.sched t).upgradeTimestamp ≤ τ ∧
        (s.ts.aux id).committed = (s.ts.aux id).executed ∧
        (∀ w, (s.ts.aux id).slVersion = some w → (G.T.X.W.tr t).new ≤ w) ∧
        (∃ sys', Step G.T.X.W s.ts.sys (.transition id) sys') ∧
        G.relVerifier (G.T.X.W.tr t).newRel ≠ 0 ∧
        ((s.gate id).flag = true → IsMulti G (G.relVerifier (G.T.X.W.tr t).newRel)))

/-- **THE e561 CHARACTERISATION IS FALSE AT d9f67890.** `UpgradeChainEnabledIffTimed`'s
right-hand side, read on the gated system, does not imply that `upgradeChain` succeeds. -/
def Properties.UpgradeChainEnabledIffTimedFailsV35 : Prop :=
  ¬ ∀ (G : GateConfig) (s : GSys) (id : ChainId) (t caller : Address) (τ : ℕ),
    (∃ s', GStep G s (.upgrade id (.executor t) caller τ) s') ↔
      ((caller = G.T.execOwner ∨ caller = (s.ts.aux id).admin) ∧
        s.ts.sys.ctm.ut (G.T.X.W.tr t).old = t ∧ G.T.X.rc.self = G.T.ctmOwner ∧
        (∃ c, s.ts.sys.chains id = some c ∧ c.pv = (G.T.X.W.tr t).old) ∧
        (G.T.sched t).upgradeTimestamp ≤ τ ∧
        (s.ts.aux id).committed = (s.ts.aux id).executed ∧
        (∀ w, (s.ts.aux id).slVersion = some w → (G.T.X.W.tr t).new ≤ w) ∧
        ∃ sys', Step G.T.X.W s.ts.sys (.transition id) sys')

/-- **UPGRADES DO NOT STAY ENABLED AT d9f67890.** The analogue of `Enabledness.UpgradesStayEnabled`
on the gated system is false, even when the chain's batches are all executed and it is on its
settlement layer, and even allowing any path, caller and block time: along a run from an
invariant state with no break-glass cut, a chain at a version with a committed edge onto a
well-formed release can have no upgrade step. -/
def Properties.UpgradesStayEnabledFailsV35 : Prop :=
  ¬ ∀ (G : GateConfig) (s s' : GSys) (ls : List GLabel), SysInv G.T.X.W s.ts.sys →
    ChainsOnWfReleases G.T.X.W s.ts.sys → GRun G s ls s' → (∀ l ∈ ls, ¬ l.IsBreakGlass) →
    ∀ id c, s'.ts.sys.chains id = some c → s'.ts.sys.ctm.ut c.pv ≠ 0 →
      ReleaseWf G.T.X.W (s'.ts.sys.edge G.T.X.W c.pv).newRel →
      (s'.ts.aux id).committed = (s'.ts.aux id).executed → (s'.ts.aux id).slVersion = none →
      ∃ path caller τ s'', GStep G s' (.upgrade id path caller τ) s''

/-! ## Locked chains -/

/-- **A LOCKED CHAIN CANNOT UPGRADE**, by any path, caller or block time. -/
def Properties.LockedChainCannotUpgrade : Prop :=
  ∀ (G : GateConfig) (s : GSys) (id : ChainId) (v : ℕ), Locked G s id v →
    ∀ path caller τ s', ¬ GStep G s (.upgrade id path caller τ) s'

/-- **A REPLACEMENT LANDING AT THE CTM'S VERSION IS PINNED TO THE CURRENT RELEASE**
(`_requireOnwardDestination`, `ChainTypeManager.sol:506-507, 515-517`). -/
def Properties.ReplacementAtCurrentVersionIsPinned : Prop :=
  ∀ (W : World) (c c' : CTM) (e r : Address), CStep W c (.replace e r) c' →
    (W.tr r).new = c.pv → (W.tr r).newRel = c.cur

/-- **(e) NO SAME-TARGET REPLACEMENT CAN FIX A LOCKED CHAIN.** Along any run whose labels are
neither a break-glass cut of chain `id` nor a CTM writer that moves the CTM's version, a locked
chain stays locked: replacements, other chains' steps, notifier, `DiamondAux` and gate-field
writes, all at any time, leave it unable to upgrade (`LockedChainCannotUpgrade`). -/
def Properties.SameTargetReplacementCannotFix : Prop :=
  ∀ (G : GateConfig) (s s' : GSys) (ls : List GLabel) (id : ChainId) (v : ℕ), Locked G s id v →
    GRun G s ls s' → (∀ l ∈ ls, ¬ l.Escapes id) → Locked G s' id v

/-- **`Locked`'S `noSlotsAhead` IS AN INVARIANT, AND A LOCKED CHAIN IS STUCK.** In a state whose
CTM satisfies `CtmInv`, nothing is committed at or above the CTM's version. And a locked chain
in such a state is `Stuck`: the only release recorded at or above the edge's target is the
current one. -/
def Properties.LockedIsStuck : Prop :=
  ∀ (G : GateConfig) (s : GSys), CtmInv G.T.X.W s.ts.sys.ctm →
    (∀ w, s.ts.sys.ctm.pv ≤ w → s.ts.sys.ctm.ut w = 0) ∧
    ∀ id v, Locked G s id v → Stuck G s id v

/-- **A STUCK CHAIN CANNOT UPGRADE**, by any path, caller or block time: the edge committed at
its version lands on the release recorded at the edge's target, whose verifier fails the
gate. -/
def Properties.StuckChainCannotUpgrade : Prop :=
  ∀ (G : GateConfig) (s : GSys) (id : ChainId) (v : ℕ), Stuck G s id v →
    ∀ path caller τ s', ¬ GStep G s (.upgrade id path caller τ) s'

/-- **A REPLACEMENT LANDS ON AN INSTALLED RELEASE, NO EARLIER THAN THE REPLACED EDGE**
(`_requireOnwardDestination`, `ChainTypeManager.sol:498-518`). From a CTM satisfying `CtmInv`,
after `replaceUpgradeTransition(e, r)` the replacement's `newRelease()` is the release the CTM
installed when it reached the replacement's target version, and that target is at or above the
replaced edge's. So a replacement cannot bring in a release the CTM has not installed. -/
def Properties.ReplacementLandsOnAnInstalledRelease : Prop :=
  ∀ (W : World) (c c' : CTM) (e r : Address), CtmInv W c → CStep W c (.replace e r) c' →
    (W.tr e).new ≤ (W.tr r).new ∧ c.relAt (W.tr r).new ≠ 0 ∧
      (W.tr r).newRel = c.relAt (W.tr r).new ∧ c'.relAt = c.relAt

/-- **(e, general form) A STUCK CHAIN STAYS STUCK UNTIL A MULTI-PROOF RELEASE IS INSTALLED OR ITS
DIAMOND IS CUT BY BREAK-GLASS.** Along any run in which no label is a break-glass cut of chain
`id` and no CTM writer installs a release whose verifier passes the gate, a stuck chain stays
stuck, hence cannot upgrade (`StuckChainCannotUpgrade`). The run may contain replacements of any
slot, commits and legacy commits of releases whose verifier fails the gate, other chains' steps
of every kind, and any notifier, `DiamondAux` and gate-field write. -/
def Properties.StuckUntilMultiReleaseOrBreakGlass : Prop :=
  ∀ (G : GateConfig) (s s' : GSys) (ls : List GLabel) (id : ChainId) (v : ℕ), Stuck G s id v →
    GRun G s ls s' → (∀ l ∈ ls, ¬ l.BreakGlassOf id ∧ ¬ l.InstallsMulti G) → Stuck G s' id v

/-- **A LOCKED CHAIN NEEDS A DEADLINE OVERRIDE TO KEEP COMMITTING.** With no stored override for
`v`, once the block time passes the deadline of the edge committed at `v` the version is no longer
active, so the chain can commit no batch (`Committer.sol`'s `protocolVersionIsActive` check).
With an override `x ≠ 0` written by `setProtocolVersionDeadline` (`ChainTypeManager.sol:563-566`),
the version is active exactly until `x`. Of `Locked` this uses only that an edge is committed at
`v`. The override keeps the chain operating at `v`; it does not let it cross the edge
(`LockedChainCannotUpgrade` has no time premise). -/
def Properties.LockedChainNeedsDeadlineOverride : Prop :=
  ∀ (G : GateConfig) (d : ℕ → ℕ) (s : GSys) (id : ChainId) (v τ : ℕ), Locked G s id v →
    (d v = 0 → (G.T.sched (s.ts.sys.ctm.ut v)).deadline < τ →
      ¬ ProtocolVersionActive G.T d s.ts.sys.ctm v τ) ∧
    ∀ x, x ≠ 0 → (ProtocolVersionActive G.T (upd d v x) s.ts.sys.ctm v τ ↔ τ ≤ x)

/-- **THE ESCAPES WORK.** From the locked state `gLock` (chain `0` flagged at version 1):
* the CTM commits `600` (2→3, onto release `250`, which ships the multi-proof verifier) and then
  replaces `300` by the skip transition `420` (1→3 onto `250`); chain `0` then upgrades through
  the executor and lands at version 3, still flagged;
* a break-glass cut installing the multi-proof verifier `700` succeeds;
* a break-glass cut clearing the flag and installing the single-proof verifier `701` succeeds;
* no break-glass cut leaves the flag set with verifier `701`. -/
def Properties.EscapesUnlockTheLockedChain : Prop :=
  (∃ s1 s2 s3 : GSys, GStep gCfg gLock (.other (.base (.ctm (.commit 600)))) s1 ∧
      GStep gCfg s1 (.other (.base (.ctm (.replace 300 420)))) s2 ∧
      GStep gCfg s2 (.upgrade 0 (.executor 420) 3 10) s3 ∧
      (s3.gate 0).flag = true ∧ ∃ c, s3.ts.sys.chains 0 = some c ∧ c.pv = 3) ∧
    (∃ s', GStep gCfg gLock (.breakGlass 0 2 (rowsRouting (wRows 200)) ⟨true, 700, 0⟩) s') ∧
    (∃ s', GStep gCfg gLock (.breakGlass 0 2 (rowsRouting (wRows 200)) ⟨false, 701, 0⟩) s') ∧
    ∀ v ρ s', ¬ GStep gCfg gLock (.breakGlass 0 v ρ ⟨true, 701, 0⟩) s'

/-- **A SKIP-REPLACEMENT ONTO ANOTHER SINGLE-PROOF RELEASE DOES NOT HELP.** In `gCfgSingle`
releases `200` and `250` both ship the single-proof verifier `701`. From `gLock` the CTM commits
`600` (2→3 onto `250`) and replaces `300` by the skip transition `420` (1→3 onto `250`), the two
steps that free chain `0` in `EscapesUnlockTheLockedChain`. Here neither installs a multi-proof
release. After the commit chain `0` is no longer `Locked` (the CTM has left the edge's target
version), but it is `Stuck` throughout, and after the replacement it still cannot upgrade by any
path, caller or time. -/
def Properties.SkipOntoSingleProofReleaseDoesNotHelp : Prop :=
  Stuck gCfgSingle gLock 0 1 ∧
    ∃ s1 s2 : GSys, GStep gCfgSingle gLock (.other (.base (.ctm (.commit 600)))) s1 ∧
      GStep gCfgSingle s1 (.other (.base (.ctm (.replace 300 420)))) s2 ∧
      ¬ (GLabel.other (.base (.ctm (.commit 600)))).InstallsMulti gCfgSingle ∧
      ¬ Locked gCfgSingle s1 0 1 ∧ s2.ts.sys.ctm.ut 1 = 420 ∧ Stuck gCfgSingle s2 0 1 ∧
      ∀ path caller τ s', ¬ GStep gCfgSingle s2 (.upgrade 0 path caller τ) s'

/-! ## The countermodel and the witness -/

/-- **COUNTERMODEL: A FLAGGED CHAIN CANNOT CROSS A NON-MULTI-PROOF EDGE.** From a fresh CTM,
`gLockRun` creates chains `0` and `1` with the same `DiamondAux`, chain `0`'s admin flags chain
`0`, and the CTM commits `300` (1→2) onto release `200`, which ships the single-proof verifier
`701`: the commit is admitted with a flagged chain at its departing version. In the state
`gLock` it reaches:
* both chains are at version 1 with the same routing and `DiamondAux`; `0` is flagged, `1` not;
* chain `1` crosses (`upgradeChain(300, 1)` by its admin at time `10`): the flag is
  load-bearing;
* chain `0` cannot, by any path, caller or time, along any run from `gLock` without an escape;
* with release `200` shipping the multi-proof verifier, chain `0` crosses;
* `replaceUpgradeTransition(300, 410)`, onto release `210` (version 2, multi-proof verifier) is
  refused, but its checks without the `currentRelease` pin pass, and after that replacement
  chain `0` crosses. -/
def Properties.FlaggedChainCannotCrossNonMultiProofEdge : Prop :=
  GRun gCfg gSys0 gLockRun gLock ∧
    gLock.ts.sys.chains 0 = gLock.ts.sys.chains 1 ∧ gLock.ts.aux 0 = gLock.ts.aux 1 ∧
    (gLock.gate 0).flag = true ∧ (gLock.gate 1).flag = false ∧
    ¬ IsMulti gCfg (gCfg.relVerifier (gWorld.tr 300).newRel) ∧
    (∃ s', GStep gCfg gLock (.upgrade 1 (.executor 300) 3 10) s') ∧
    (∀ ls s', GRun gCfg gLock ls s' → (∀ l ∈ ls, ¬ l.Escapes 0) →
      ∀ path caller τ s'', ¬ GStep gCfg s' (.upgrade 0 path caller τ) s'') ∧
    (∃ s', GStep gCfgMulti gLock (.upgrade 0 (.executor 300) 3 10) s') ∧
    (∀ c', ¬ CStep gWorld gLock.ts.sys.ctm (.replace 300 410) c') ∧
    ReplaceUnpinned gWorld gLock.ts.sys.ctm 300 410 ∧
    ∃ s', GStep gCfg
      ⟨{ gLock.ts with sys := { gLockSys with
          ctm := { gLockSys.ctm with ut := upd gLockSys.ctm.ut 1 410 } } }, gLock.gate⟩
      (.upgrade 0 (.executor 410) 3 10) s'

/-- **(f) SATISFIABILITY WITNESS.** The premise bundles are met on reachable states:
* `Locked gCfg gLock 0 1`, reached from a fresh CTM by `gLockRun` (the premise of
  `LockedChainCannotUpgrade`, `SameTargetReplacementCannotFix` and
  `LockedChainNeedsDeadlineOverride`);
* the fresh state satisfies `GateInv` and both configurations are `MaskMonotone` (the premises
  of `FlaggedChainsStayMultiProof`), and `gLock` satisfies `GateInv`;
* `gLock`'s CTM satisfies `CtmInv` and chain `0` is `Stuck` there (the premises of `LockedIsStuck`,
  `StuckChainCannotUpgrade` and `StuckUntilMultiReleaseOrBreakGlass`), and no label of `gLockRun`
  is a break-glass cut;
* `gLock` is reached in `gCfgMulti` too, and there the flagged chain `0` upgrades and stays
  flagged, so `FlaggedCutsKeepMultiProof`'s hypotheses are met by a flagged chain. -/
def Properties.UpgradeGateV35Witness : Prop :=
  GRun gCfg gSys0 gLockRun gLock ∧ Locked gCfg gLock 0 1 ∧
    GateInv gCfg gSys0 ∧ MaskMonotone gCfg ∧ GateInv gCfg gLock ∧
    CtmInv gWorld gLock.ts.sys.ctm ∧ Stuck gCfg gLock 0 1 ∧
    (∀ l ∈ gLockRun, ¬ l.IsBreakGlass) ∧
    GRun gCfgMulti gSys0 gLockRun gLock ∧ MaskMonotone gCfgMulti ∧
    ∃ s', GStep gCfgMulti gLock (.upgrade 0 (.executor 300) 3 10) s' ∧ (s'.gate 0).flag = true

end Contracts.SecondProofSystem
