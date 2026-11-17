import EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.ExecutorOwnerCallsV35

/-!
# Properties: which CTM executor frames make the CTM's owner calls, and what they log (v0.35)

Statements about `EraSpec.Contracts.ProxyUpgradeExecutorBase.Specs.ExecutorOwnerCallsV35`
(`draft/v0.35.0` at `b17415d20`). Proofs are in
`EraSpec.Contracts.ProxyUpgradeExecutorBase.Proofs.ExecutorOwnerCallsV35`.

A frame is one successful invocation of an executor entry point; its trace is what that
invocation's own code did, the engine it delegatecalls included (see the Specs header). A
"CTM owner call" is a call of a CTM function that passes the owner gate because the executor
owns the CTM.

## For every frame

* **Each entry fixes its owner calls and its log** (`EntryFixesOwnerCallsAndLog`): the owner
  calls of the trace and the executor's log are read off the entry. A `forward` logs one
  `CallForwarded` per listed call, in order, and makes exactly its listed CTM calls; an
  infrastructure leg makes exactly the CTM calls its engine made, and its log is the engine's
  own logs followed by `CTMInfrastructureUpgradeApplied`.
* **Four origins** (`OwnerCallOrigins`): every owner call is `applyCTMUpgrade`'s commit, the
  call of an `upgradeChain` (caller: the executor's owner or that chain's admin), a call a
  `forward` lists, or a call the pinned engine of an `applyInfrastructureUpgrade` made. Apart
  from `upgradeChain`, the caller owns the executor.
* **Outside engine legs the executor's log names every owner call**
  (`OwnerCallsOutsideEngineLegsAreLogged`), by its `CallForwarded`, `CTMUpgradeApplied` or
  `ChainUpgradeApplied`. With engine legs included this fails
  (`EngineOwnerCallsNotLoggedByExecutor`).
* **An engine leg keeps the executor's ownership and its rows, and the holders the
  post-check reads unless the holders hash collides on the leg's own two lists**
  (`EngineLegKeepsHoldersOrCollides`, with `HoldersViewUnchangedIff` saying which holders
  those are).
* **Every route goes through the CTM's own checks** (`TameFramesKeepTheVersionInvariant`): a
  frame with no call or act the model leaves arbitrary keeps the `VersionRegistry` invariant
  `CtmInv` and never lowers `protocolVersion`, whether its commits and replacements come from
  `applyCTMUpgrade`, a `forward` or an engine leg.

## Witnesses and countermodels

* `OwnerCallOriginsEachOccur`: each of the four origins occurs, from a CTM initialized on a
  witness release; the `upgradeChain` one is called by a chain admin that does not own the
  executor.
* `EngineLegReplacesAndMovesDeadlineWithoutForward`: an infrastructure leg whose engine calls
  `replaceUpgradeTransition` and `setProtocolVersionDeadline` on the CTM succeeds, for every
  holders hash; the executor's log of that leg names neither call. This is the route
  `docs/registry-driven-upgrades.md:473-478` describes.
* `EngineNominationRefusedOnlyByHoldersHash`: an engine that nominates a CTM owner is refused
  by a holders hash that reads the pending owner, and passes one that reads nothing, where the
  collision disjunct of `EngineLegKeepsHoldersOrCollides` is the one that holds.
  `ForwardNominatesCtmOwner`: the same nomination through `forward` passes for every holders
  hash, logged as `CallForwarded`.
* `VersionInvariantPremisesMetAndNeeded`: the witness leg meets the premises of
  `TameFramesKeepTheVersionInvariant`, and a leg with one act the model leaves arbitrary can
  break `CtmInv` while keeping every holder.
* `EngineLegNominatesCtmAdmin`: an engine that nominates a CTM admin passes for every holders
  hash, as `ProxyUpgradeExecutorBase.sol:114-116` states (`pendingAdmin` is private and not
  compared).

No statement assumes anything about the holders hash `H`.
-/

namespace Contracts.ExecutorOwnerCallsV35

open Contracts.ChainTypeManager (Address World CtmInv wWorld)

/-! ## For every frame -/

/-- **EACH ENTRY POINT FIXES ITS CTM OWNER CALLS AND ITS LOG.** In every successful frame, the
CTM owner calls the trace records, in order, are `Entry.ownerCalls` of the entry, and the
executor's log, in order, is `Entry.exLog` of the entry. So a `forward` makes exactly the CTM
calls it lists and logs one `CallForwarded` per listed call, in the listed order;
`applyCTMUpgrade(t)` makes the commit of `t` and logs `CTMUpgradeApplied(t, old, new)`;
`upgradeChain(t, id)` makes `upgradeChainFromVersion(id, old)` and logs
`ChainUpgradeApplied(id, new)` (`old`, `new`: `t`'s getters); an infrastructure leg makes
exactly the CTM owner calls of its engine's acts, and its log is the logs the engine emitted,
in order, followed by `CTMInfrastructureUpgradeApplied(T)`; `acceptCTMOwnership` and the
executor's own `transferOwnership` and `acceptOwnership` make no owner call and log nothing
modelled. -/
def Properties.EntryFixesOwnerCallsAndLog : Prop :=
  ∀ (cfg : Config) (s s' : State) (caller : Address) (e : Entry) (tr : List Obs),
    Frame cfg s caller e s' tr → ownerCalls tr = e.ownerCalls cfg.W ∧ exLog tr = e.exLog cfg.W

/-- **WHERE THE CTM'S OWNER CALLS COME FROM.** Every CTM owner call of every successful frame
is one of four: the commit of `t` by `applyCTMUpgrade(t)`, with `t` code; the call
`upgradeChainFromVersion(id, old)` of `upgradeChain(t, id)`, with `t` the transition the CTM
has committed for `old` when the frame starts; a call a `forward` lists; or a call the engine
of an `applyInfrastructureUpgrade(T)` made, with `T` a CTM-domain transition with code that
pins an engine with code. In the first, third and fourth case the frame's caller owns the
executor; in the second it owns the executor or is chain `id`'s admin. -/
def Properties.OwnerCallOrigins : Prop :=
  OriginsCover fun cfg s caller e op =>
    FromApplyCTMUpgrade cfg s caller e op ∨ FromUpgradeChain cfg s caller e op ∨
      FromForward cfg s caller e op ∨ FromEngineLeg cfg s caller e op

/-- **OUTSIDE ENGINE LEGS THE EXECUTOR'S LOG NAMES EVERY OWNER CALL.** In every successful
frame that is not an infrastructure leg whose engine makes a CTM owner call
(`Entry.EngineQuiet`), every CTM owner call of the trace is named in the same trace's
executor log: by its own `CallForwarded`; or, for the commit of `t`, by
`CTMUpgradeApplied(t, old, new)`; or, for `upgradeChainFromVersion(id, old)`, by
`ChainUpgradeApplied(id, new)` (`LoggedByExecutor`). -/
def Properties.OwnerCallsOutsideEngineLegsAreLogged : Prop :=
  ∀ (cfg : Config) (s s' : State) (caller : Address) (e : Entry) (tr : List Obs),
    Frame cfg s caller e s' tr → e.EngineQuiet →
    ∀ op, Obs.ctmCall op ∈ tr → LoggedByExecutor cfg.W tr op

/-- **WITH ENGINE LEGS INCLUDED, THE LOGGING STATEMENT FAILS.** It is false that every CTM
owner call of every successful frame is named in that frame's executor log
(`LoggedByExecutor`). The frame of `EngineLegReplacesAndMovesDeadlineWithoutForward` is a
counterexample. -/
def Properties.EngineOwnerCallsNotLoggedByExecutor : Prop :=
  ¬ ∀ (cfg : Config) (s s' : State) (caller : Address) (e : Entry) (tr : List Obs),
      Frame cfg s caller e s' tr → ∀ op, Obs.ctmCall op ∈ tr → LoggedByExecutor cfg.W tr op

/-- **THE LIST THE POST-CHECK HASHES IS UNCHANGED EXACTLY WHEN THE HOLDERS IT READS ARE.** For
any two states, `holdersView` (what `_domainHolders` hashes) is the same in both iff
`HoldersKept`: the `ProxyAdmin`'s owner, the CTM's owner, pending owner, admin and
ServerNotifier, what `getProxyAdmin(CTM)` returns, and, when the ServerNotifier is nonzero,
its owner, pending owner, what `getProxyAdmin` returns for it, and its CTM, are all unchanged.
`HoldersKept` does not read the CTM's `pendingAdmin`. -/
def Properties.HoldersViewUnchangedIff : Prop :=
  ∀ (cfg : Config) (s s' : State), holdersView cfg s' = holdersView cfg s ↔ HoldersKept cfg s s'

/-- **AN ENGINE LEG KEEPS THE EXECUTOR'S OWNERSHIP, ITS ROWS, AND THE HOLDERS UP TO A COLLISION
ON ITS OWN TWO LISTS.** After every successful `applyInfrastructureUpgrade(T)`, whatever its
engine did: the executor's owner and pending owner are those before; every row of `T` has its
proxy at its `implNew`; and either every holder the post-check reads is unchanged
(`HoldersKept`), or the two lists `_domainHolders` read before and after the engine differ and
hash the same (`HoldersCollide`). Only the state after the engine is compared with the state
before it: what happened in between is not constrained.

The three parts restate the leg's post-checks. The last is that check split on whether the two
lists are equal; what it adds is which holders the list covers (`HoldersViewUnchangedIff`).
`EngineNominationRefusedOnlyByHoldersHash` shows both disjuncts occur. -/
def Properties.EngineLegKeepsHoldersOrCollides : Prop :=
  ∀ (cfg : Config) (s s' : State) (caller : Address) (T : Transition) (acts : List EngAct)
    (tr : List Obs),
    Frame cfg s caller (.applyInfrastructureUpgrade T acts) s' tr →
      s'.exOwner = s.exOwner ∧ s'.exPending = s.exPending ∧
      (∀ r ∈ T.rows, s'.impl r.proxy = r.implNew) ∧
      (HoldersKept cfg s s' ∨ HoldersCollide cfg s s')

/-- **EVERY ROUTE TO THE CTM'S VERSION STATE GOES THROUGH THE CTM'S OWN CHECKS.** In every
successful frame that makes no call or act whose effect the model leaves arbitrary
(`Entry.Tame`: no `CtmOp.other` owner call, no `FwdCall.other` call, no `EngAct.other` act):
if the CTM's version state satisfies the `VersionRegistry` invariant `CtmInv` before the frame,
it does after, and `protocolVersion` has not decreased. The commits and replacements may come
from `applyCTMUpgrade`, from a `forward` or from an engine leg: each is a `CStep`, and every
`CStep` preserves `CtmInv` (`Contracts.ChainTypeManager.Properties.StepPreservesInvariant`). -/
def Properties.TameFramesKeepTheVersionInvariant : Prop :=
  ∀ (cfg : Config) (s s' : State) (caller : Address) (e : Entry) (tr : List Obs),
    Frame cfg s caller e s' tr → e.Tame → CtmInv cfg.W s.ctm.reg →
      CtmInv cfg.W s'.ctm.reg ∧ s.ctm.reg.pv ≤ s'.ctm.reg.pv

/-! ## Witnesses and countermodels -/

/-- **EACH OF THE FOUR ORIGINS OCCURS.** For every holders hash `H`, in the witness
configuration `ocCfg H`:
* from `ocS0`, the executor's owner `2` runs `applyCTMUpgrade(300)`, reaching `ocS1` with trace
  `ocCommitTrace`; the commit is an owner call of the trace from that origin, and the trace's
  executor log names it;
* from `ocS1`, chain `0`'s admin `50`, which is not the executor's owner, runs
  `upgradeChain(300, 0)`; its owner call `upgradeChainFromVersion(0, 1)` is from that origin
  and named in the log;
* from `ocS1`, `2` runs `forward(ocFwdCalls)` (the deadline call `setProtocolVersionDeadline(1, 77)`
  to the CTM, then a call with calldata to `33`); the deadline call is from that origin, the
  log is one `CallForwarded` per call and names it, and the stored deadline of version 1 is
  then `77`;
* from `ocS1`, `2` runs `applyInfrastructureUpgrade` of `ocT` with engine acts `ocActs`; its
  owner call `replaceUpgradeTransition(300, 400)` is from the engine-leg origin. -/
def Properties.OwnerCallOriginsEachOccur : Prop :=
  ∀ H : List Address → UInt256,
    (Frame (ocCfg H) ocS0 2 (.applyCTMUpgrade 300) ocS1 ocCommitTrace ∧
      Obs.ctmCall (.commit 300) ∈ ocCommitTrace ∧
      FromApplyCTMUpgrade (ocCfg H) ocS0 2 (.applyCTMUpgrade 300) (.commit 300) ∧
      LoggedByExecutor wWorld ocCommitTrace (.commit 300)) ∧
    (∃ s' tr, Frame (ocCfg H) ocS1 50 (.upgradeChain 300 0) s' tr ∧ (50 : Address) ≠ ocS1.exOwner ∧
      Obs.ctmCall (.upgradeChain 0 1) ∈ tr ∧
      FromUpgradeChain (ocCfg H) ocS1 50 (.upgradeChain 300 0) (.upgradeChain 0 1) ∧
      LoggedByExecutor wWorld tr (.upgradeChain 0 1)) ∧
    (∃ s' tr, Frame (ocCfg H) ocS1 2 (.forward ocFwdCalls) s' tr ∧
      Obs.ctmCall (.setDeadline 1 77) ∈ tr ∧
      FromForward (ocCfg H) ocS1 2 (.forward ocFwdCalls) (.setDeadline 1 77) ∧
      exLog tr = ocFwdCalls.map ExEvent.callForwarded ∧
      LoggedByExecutor wWorld tr (.setDeadline 1 77) ∧ s'.ctm.dl 1 = 77) ∧
    (∃ s' tr, Frame (ocCfg H) ocS1 2 (.applyInfrastructureUpgrade ocT ocActs) s' tr ∧
      Obs.ctmCall (.replace 300 400) ∈ tr ∧
      FromEngineLeg (ocCfg H) ocS1 2 (.applyInfrastructureUpgrade ocT ocActs) (.replace 300 400))

/-- **AN ENGINE LEG REPLACES A COMMITTED TRANSITION AND MOVES A DEADLINE, AND THE EXECUTOR'S LOG
NAMES NEITHER CALL.** For every holders hash `H`: from `ocS0`, the executor's owner's
`applyCTMUpgrade(300)` reaches `ocS1`; from `ocS1`, the owner's `applyInfrastructureUpgrade`
of the one-row transition `ocT`, whose engine applies the row, logs it, and calls
`replaceUpgradeTransition(300, 400)` and `setProtocolVersionDeadline(1, 77)` on the CTM
(`ocActs`), succeeds with trace `ocLegTrace`. Afterwards slot 1 holds `400`, the stored
deadline of version 1 is `77`, and proxy `5` runs `11`. The trace's owner calls are exactly
those two calls; the executor's log is exactly `ProxyImplementationUpgraded(5, 11)` then
`CTMInfrastructureUpgradeApplied(3)`, and it names neither owner call; the CTM's log is
`UpgradeTransitionReplaced(1, 300, 400)`, `NewUpgradeTransition(1, 400)`,
`UpdateProtocolVersionDeadline(1, 77)`. The leg keeps every holder, and the holders hash does
not collide on the leg's two lists. -/
def Properties.EngineLegReplacesAndMovesDeadlineWithoutForward : Prop :=
  ∀ H : List Address → UInt256,
    Frame (ocCfg H) ocS0 2 (.applyCTMUpgrade 300) ocS1 ocCommitTrace ∧
    ∃ s', Frame (ocCfg H) ocS1 2 (.applyInfrastructureUpgrade ocT ocActs) s' ocLegTrace ∧
      s'.ctm.reg.ut 1 = 400 ∧ s'.ctm.dl 1 = 77 ∧ s'.impl 5 = 11 ∧
      ownerCalls ocLegTrace = [.replace 300 400, .setDeadline 1 77] ∧
      exLog ocLegTrace = [.proxyImplementationUpgraded 5 11, .infraApplied 3] ∧
      ctmLog ocLegTrace = [.upgradeTransitionReplaced 1 300 400, .newUpgradeTransition 1 400,
        .updateProtocolVersionDeadline 1 77] ∧
      (∀ op ∈ ownerCalls ocLegTrace, ¬ LoggedByExecutor wWorld ocLegTrace op) ∧
      HoldersKept (ocCfg H) ocS1 s' ∧ ¬ HoldersCollide (ocCfg H) ocS1 s'

/-- **THE HOLDERS HASH IS WHAT REFUSES AN ENGINE'S NOMINATION OF A CTM OWNER.** From `ocS1`,
take the owner's `applyInfrastructureUpgrade` of `ocT` whose engine applies the row and then
calls `transferOwnership(42)` on the CTM (`ocNominateOwner`). With the holders hash
`ocHPending`, which reads the CTM's pending owner, no such frame exists. With `ocHConst`, which
reads nothing, one exists: the CTM's pending owner goes from `0` to `42`, `HoldersKept` fails
and `HoldersCollide` holds, so in that frame the collision disjunct of
`EngineLegKeepsHoldersOrCollides` is the one that holds. -/
def Properties.EngineNominationRefusedOnlyByHoldersHash : Prop :=
  (∀ s' tr, ¬ Frame (ocCfg ocHPending) ocS1 2 (.applyInfrastructureUpgrade ocT ocNominateOwner)
    s' tr) ∧
  ∃ s' tr, Frame (ocCfg ocHConst) ocS1 2 (.applyInfrastructureUpgrade ocT ocNominateOwner) s' tr ∧
    ocS1.ctm.pending = 0 ∧ s'.ctm.pending = 42 ∧
    ¬ HoldersKept (ocCfg ocHConst) ocS1 s' ∧ HoldersCollide (ocCfg ocHConst) ocS1 s'

/-- **THE SAME NOMINATION THROUGH `forward` PASSES FOR EVERY HOLDERS HASH, AND IS LOGGED.** For
every holders hash: from `ocS1`, the owner's `forward` of the one call `transferOwnership(42)`
to the CTM succeeds; the CTM's pending owner goes from `0` to `42`, and the executor's log is
exactly that call's `CallForwarded`. `forward` has no holders check; "a succession ... is a
`forward`, not a leg" (`ProxyUpgradeExecutorBase.sol:38-39`). -/
def Properties.ForwardNominatesCtmOwner : Prop :=
  ∀ H : List Address → UInt256,
    ∃ s' tr, Frame (ocCfg H) ocS1 2 (.forward [.ctm (.transferOwnership 42)]) s' tr ∧
      ocS1.ctm.pending = 0 ∧ s'.ctm.pending = 42 ∧
      exLog tr = [.callForwarded (.ctm (.transferOwnership 42))]

/-- **THE PREMISES OF `TameFramesKeepTheVersionInvariant` ARE MET BY THE WITNESS LEG, AND THE
TAMENESS PREMISE IS NEEDED.** `ocS0` and `ocS1` satisfy `CtmInv`, and the witness leg (`ocT`
with `ocActs`) is tame. For every holders hash that leg succeeds from `ocS1` with trace
`ocLegTrace`, replacing the committed transition of slot 1 by `400`, and its end state satisfies
`CtmInv`. For every holders hash, the leg of `ocT` whose engine applies the row and then does
one act the model leaves arbitrary (`ocOpaqueActs`) also succeeds from `ocS1`, and ends in
`ocOpaqueAfter`, whose `currentRelease` is zero, so `CtmInv` fails there; every holder is
kept. The documents name one real act of that kind: an engine "can still rewrite the storage
of any proxy under its `ProxyAdmin` (rows, the CTM and the ServerNotifier included) through
`upgradeAndCall`" (`docs/registry-driven-upgrades.md:262-264`). -/
def Properties.VersionInvariantPremisesMetAndNeeded : Prop :=
  CtmInv wWorld ocS0.ctm.reg ∧ CtmInv wWorld ocS1.ctm.reg ∧
    (Entry.applyInfrastructureUpgrade ocT ocActs).Tame ∧
    (∀ H : List Address → UInt256, ∃ s',
      Frame (ocCfg H) ocS1 2 (.applyInfrastructureUpgrade ocT ocActs) s' ocLegTrace ∧
      s'.ctm.reg.ut 1 = 400 ∧ CtmInv wWorld s'.ctm.reg) ∧
    ∀ H : List Address → UInt256, ∃ tr,
      Frame (ocCfg H) ocS1 2 (.applyInfrastructureUpgrade ocT ocOpaqueActs) ocOpaqueAfter tr ∧
      ¬ CtmInv wWorld ocOpaqueAfter.ctm.reg ∧ HoldersKept (ocCfg H) ocS1 ocOpaqueAfter

/-- **AN ENGINE'S NOMINATION OF A CTM ADMIN IS NOT AMONG THE HOLDERS.** For every holders hash
`H`: from `ocS1`, the owner's `applyInfrastructureUpgrade` of `ocT` whose engine applies the
row and then calls `setPendingAdmin(42)` on the CTM (`ocNominateAdmin`) succeeds; the CTM's
`pendingAdmin` goes from `0` to `42`, and every holder the post-check reads is kept. This is the
case `ProxyUpgradeExecutorBase.sol:114-116` and `docs/registry-driven-upgrades.md:285-286`
describe: `pendingAdmin` is private and the post-check does not compare it. -/
def Properties.EngineLegNominatesCtmAdmin : Prop :=
  ∀ H : List Address → UInt256,
    ∃ s' tr, Frame (ocCfg H) ocS1 2 (.applyInfrastructureUpgrade ocT ocNominateAdmin) s' tr ∧
      ocS1.ctm.pendingAdmin = 0 ∧ s'.ctm.pendingAdmin = 42 ∧ HoldersKept (ocCfg H) ocS1 s'

end Contracts.ExecutorOwnerCallsV35
