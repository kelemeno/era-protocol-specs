import EraSpec.Contracts.ChainTypeManager.Specs.ExecutorForward

/-!
# Properties: which invariants survive the CTM executor's `forward`

Statements about `EraSpec.Contracts.ChainTypeManager.Specs.ExecutorForward`. Proofs are in
`EraSpec.Contracts.ChainTypeManager.Proofs.ExecutorForward`.

## What survives

* **Forwarded calls to the CTM are ordinary runs.** A `forward` whose calls all target the
  CTM relates exactly the states a `ChainRouting` run relates, and leaves every proxy
  alone (`ForwardOfCtmCallsIsARun`). The CTM's checks live in the CTM, so going through
  `forward` bypasses none of them. Every run result of `VersionRegistry` and `ChainRouting`
  therefore applies to such forwards, under that result's own premises (the routing
  headline still needs "no break-glass cut", and `executeUpgrade` is reachable only
  through `forward`).
* **Along any executor run of tame transactions the invariants hold.** If no
  infrastructure row names the CTM proxy, no forwarded call swaps the CTM's code or makes
  a break-glass cut, and each reinitializer moves at most its own proxy, then `SysInv` is
  preserved, the version never decreases and the CTM proxy is not moved
  (`TameRunPreservesSysInv`), so every chain at `v` routes `R_v`
  (`TameRunKeepsChainsOnTheirRelease`).
* **The fixed entry points move a proxy only along a row's edge**
  (`FixedEntrypointsMoveProxiesOnlyAlongRows`), the executor-level form of the row
  library's replay safety.

## What does not

* **A forward can move a proxy with no source check** (`ForwardDowngradesAProxy`): a
  tame forward of `CTM_PROXY_ADMIN.upgrade` takes a proxy that a transition moved
  `10 → 11` back to `10`. The row library's replay safety is a property of `applyRows`,
  not of the executor.
* **A forward that swaps the CTM's code voids the CTM's invariants**
  (`ForwardCtmSwapBreaksInvariants`): from an invariant state with a chain at version 2,
  one forwarded `upgradeAndCall` on the CTM proxy leaves the CTM at version 1, so the
  version decreased and the chain is ahead of its CTM. `VersionsIncreaseAlongRuns` and
  `ChainsRunTheirVersionsRelease` do not extend to executor runs that contain such a call.
  Within the model the same holds for an infrastructure transition whose rows move the CTM
  proxy; the `Tame` premise excludes both.
-/

namespace Contracts.ChainTypeManager

/-! ## What survives -/

/-- **A FORWARD OF CTM CALLS IS EXACTLY A RUN.** A successful `forward` whose calls all
target the CTM relates the system as the corresponding `ChainRouting` run does, and moves no
proxy; conversely, every such run is a successful `forward` of those calls. -/
def Properties.ForwardOfCtmCallsIsARun : Prop :=
  ∀ (X : XConfig) (s : XState) (ls : List Label),
    (∀ s', FRun X s (ls.map FCall.sys) s' → Run X.W s.sys ls s'.sys ∧ s'.impl = s.impl) ∧
    (∀ sys', Run X.W s.sys ls sys' → FRun X s (ls.map FCall.sys) { s with sys := sys' })

/-- **TAME EXECUTOR RUNS PRESERVE THE INVARIANT.** Along any run of executor transactions
and other actors' steps from a state satisfying `SysInv`, if every transaction is `Tame`
(no infrastructure row names the CTM proxy; no forwarded break-glass cut or CTM code swap)
and each reinitializer moves at most its own proxy: `SysInv` holds at the end, the CTM's
version has not decreased, and the CTM proxy's implementation has not changed. -/
def Properties.TameRunPreservesSysInv : Prop :=
  ∀ (X : XConfig) (s s' : XState) (xs : List XLabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    SysInv X.W s.sys → XRun X s xs s' → (∀ x ∈ xs, x.Tame X) →
    SysInv X.W s'.sys ∧ s.sys.ctm.pv ≤ s'.sys.ctm.pv ∧ s'.impl X.ctmProxy = s.impl X.ctmProxy

/-- **THE ROUTING HEADLINE ACROSS TAME EXECUTOR RUNS.** Under the premises of
`TameRunPreservesSysInv`, every chain at a version `v` with a release `R_v` routes exactly
`R_v`, and `R_v` is a release of version `v`. -/
def Properties.TameRunKeepsChainsOnTheirRelease : Prop :=
  ∀ (X : XConfig) (s s' : XState) (xs : List XLabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    SysInv X.W s.sys → XRun X s xs s' → (∀ x ∈ xs, x.Tame X) →
    ∀ id c, s'.sys.chains id = some c → s'.sys.ctm.relAt c.pv ≠ 0 →
      X.W.relVersion (s'.sys.ctm.relAt c.pv) = c.pv ∧
      c.routing = rowsRouting (X.W.relRows (s'.sys.ctm.relAt c.pv))

/-- **THE FIXED ENTRY POINTS MOVE A PROXY ONLY ALONG A ROW'S EDGE.** Any executor step other
than `forward`, applying only transitions whose rows name distinct proxies, with
reinitializers that move at most their own proxy, leaves every proxy where it was or moves
it from some row's `expectedOldImpl` to that row's `implNew`. -/
def Properties.FixedEntrypointsMoveProxiesOnlyAlongRows : Prop :=
  ∀ (X : XConfig) (s s' : XState) (x : XLabel), ProxyUpgradeCurrent.ReinitFrames X.rc →
    XStep X s x s' → (∀ calls, x ≠ .forward calls) →
    (∀ T, x = .infra T → T.rows.Pairwise (fun a b => a.proxy ≠ b.proxy)) →
    MovesOnlyAlongRows s s' x

/-! ## What does not -/

/-- **A FORWARD CAN MOVE A PROXY WITH NO SOURCE CHECK.** In the witness configuration (whose
reinitializers satisfy `ReinitFrames` and whose transition's rows name distinct proxies),
`applyInfrastructureUpgrade` moves proxy `5` from `10` to `11`. A tame `forward` of
`CTM_PROXY_ADMIN.upgrade(5, 10)` then succeeds and moves it back to `10`, which no row of
any transition did: the conclusion of `FixedEntrypointsMoveProxiesOnlyAlongRows` fails for
that step. -/
def Properties.ForwardDowngradesAProxy : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧
    wInfra.rows.Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    ∃ s s', XRun wX wX0 [.infra wInfra] s ∧
      XStep wX s (.forward [.upgradeProxy 5 10]) s' ∧
      XLabel.Tame wX (.forward [.upgradeProxy 5 10]) ∧
      s.impl 5 = 11 ∧ s'.impl 5 = 10 ∧
      ¬ MovesOnlyAlongRows s s' (.forward [.upgradeProxy 5 10])

/-- **A FORWARDED CTM CODE SWAP VOIDS THE CTM'S INVARIANTS.** From the fresh witness system,
which satisfies `SysInv`: a tame run creates chain `0`, commits `300` (1→2) through
`applyCTMUpgrade` and upgrades chain `0` to version 2, after which `SysInv` still holds.
Then one `forward` of `upgradeAndCall` on the CTM proxy, whose new code leaves the CTM in
the state `initialize(100)` would (version 1), succeeds. The CTM's version decreased, and
`SysInv` fails: chain `0` is ahead of its CTM. -/
def Properties.ForwardCtmSwapBreaksInvariants : Prop :=
  SysInv wX.W wX0.sys ∧
    ∃ s s', XRun wX wX0 [.env (.genesis 0), .commit 300, .upgradeChain 0] s ∧
      (∀ x ∈ [XLabel.env (.genesis 0), .commit 300, .upgradeChain 0], x.Tame wX) ∧
      SysInv wX.W s.sys ∧
      XStep wX s (.forward [.swapCtm 42 (initState wWorld 100)]) s' ∧
      ¬ XLabel.Tame wX (.forward [.swapCtm 42 (initState wWorld 100)]) ∧
      s'.sys.ctm.pv < s.sys.ctm.pv ∧ ¬ SysInv wX.W s'.sys

/-! ## Witness -/

/-- **THE PREMISES ARE MET BY A REAL RUN.** From the fresh witness system: apply the
CTM-domain transition (proxies `5` and `6` upgraded), create chain `0`, commit `300`,
upgrade chain `0`, then one `forward` that replaces the committed transition `300` by `400`
on the CTM and upgrades proxy `7` to `42` through the `ProxyAdmin`. Every transaction is
tame, the reinitializers satisfy `ReinitFrames`, the transition's rows name distinct
proxies, and the start satisfies `SysInv`. At the end chain `0` is at version 2, which has a
release, slot 1 holds `400`, and the three proxies have moved. -/
def Properties.ExecutorWitness : Prop :=
  ProxyUpgradeCurrent.ReinitFrames wX.rc ∧ SysInv wX.W wX0.sys ∧
    wInfra.rows.Pairwise (fun a b => a.proxy ≠ b.proxy) ∧
    (∀ x ∈ [XLabel.infra wInfra, .env (.genesis 0), .commit 300, .upgradeChain 0,
      .forward [.sys (.ctm (.replace 300 400)), .upgradeProxy 7 42]], x.Tame wX) ∧
    ∃ s', XRun wX wX0 [.infra wInfra, .env (.genesis 0), .commit 300, .upgradeChain 0,
        .forward [.sys (.ctm (.replace 300 400)), .upgradeProxy 7 42]] s' ∧
      s'.impl 5 = 11 ∧ s'.impl 6 = 12 ∧ s'.impl 7 = 42 ∧ s'.sys.ctm.ut 1 = 400 ∧
      s'.sys.ctm.pv = 2 ∧ s'.sys.ctm.relAt 2 ≠ 0 ∧ ∃ c, s'.sys.chains 0 = some c ∧ c.pv = 2

end Contracts.ChainTypeManager
