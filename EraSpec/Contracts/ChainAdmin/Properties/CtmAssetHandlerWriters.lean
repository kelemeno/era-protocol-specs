import EraSpec.Contracts.ChainAdmin.Specs.CtmAssetHandlerWriters

/-!
# Properties: the CTM asset's handler is the chain asset handler, so P's check is off

Statements about `EraSpec.Contracts.ChainAdmin.Specs.CtmAssetHandlerWriters`.  Proofs are in
`EraSpec.Contracts.ChainAdmin.Proofs.CtmAssetHandlerWriters`.

## (d) The writers

* Both `CTMDeploymentTracker` writers set the CTM's handler to the Bridgehub's current
  `chainAssetHandler`, record the CTMDT as its tracker, and move no other handler;
  `registerCTMAssetOnL1` also records the CTM in `ctmAssetIdToAddress`
  (`CtmTrackerWritesChainAssetHandler`).
* They are the only writers of a CTM's handler: every call that changes it is one of
  them, or the vault fallback on an unset handler, or a logged call whose own triple
  collides with the CTM's (`OnlyCtmTrackerRewritesCtmHandler`).  The Bridgehub's
  `chainAssetHandler` moves only by `setAddresses` (`OnlySetAddressesMovesChainAssetHandler`).

## Runs

* Once the CTMDT has registered the CTM, the handler is never zero or the Bridgehub, as
  long as `setAddresses` never names the Bridgehub (or zero) as chain asset handler, unless
  the run logs a collision with the CTM's triple (`CtmHandlerStaysOffBridgehub`,
  `CtmHandlerOffBridgehubAfterRegistration`).
* Without `setAddresses` it is exactly the Bridgehub's `chainAssetHandler`
  (`CtmHandlerIsChainAssetHandler`, `CtmHandlerIsChainAssetHandlerAfterRegistration`):
  the premise of `PermanentRestrictionMigration.DeployedConfigDisablesMigrationCheck`.
* **Headline.**  After such a run, `PermanentRestriction` accepts every migration request
  for the CTM, whatever its L2 admin and whatever the whitelist
  (`DeployedRunsDisableMigrationCheck`).

## Witnesses and load-bearing premises

* `CtmWritersDeploymentWitness`: the deployment sequence (tracker write, then
  `registerCTMAssetOnL1`) meets every premise of the run results, and afterwards P accepts
  a migration to an admin no whitelist names.
* `BridgehubAsChainAssetHandlerWitness`: if governance makes the Bridgehub its own chain
  asset handler and re-points the CTM, the handler is the Bridgehub and P's check fires.
  So the `setAddresses` premise is needed.  (In that configuration the migration itself
  cannot succeed: the Bridgehub has no `bridgeBurn`;
  `PermanentRestrictionMigration.CheckedRequestsBurnAtBridgehub`.)
* `RepointingToChainAssetHandlerDisablesCheck`: the mechanism in one run.  From that
  Bridgehub-as-handler state, an upgrade installs a chain asset handler and the CTMDT
  re-points the CTM to it, as `setCtmAssetHandlerAddressOnL1` is meant to be used
  (`CTMDT:82-85`); a migration call P rejected before is accepted after.
* `CtmHandlerCollisionWitness`: with an encoding that collides on the vault's triple, a
  vault registration re-points the CTM to the Bridgehub; the collision disjunct names it.
-/

namespace Contracts.ChainAdmin.CtmAssetHandlerWriters

open PermanentRestrictionMigration (Abi Env Call Bytes MigrationRequest
  BridgehubAnswersNoChainId validateCall newAdminFromMigration burnAdmin prmCall prmEnv)

/-! ## (d) The writers -/

/-- **(d) THE CTMDT WRITERS SET THE CTM'S HANDLER TO THE CHAIN ASSET HANDLER.**  After
`registerCTMAssetOnL1(ctm)` or `setCtmAssetHandlerAddressOnL1(ctm)`, the CTM's handler is
the Bridgehub's `chainAssetHandler` as it was when called, its tracker is the CTMDT, no
other handler moved, and the Bridgehub's `chainAssetHandler` is unchanged;
`registerCTMAssetOnL1` also maps the CTM's id to the CTM. -/
def Properties.CtmTrackerWritesChainAssetHandler : Prop :=
  ∀ (K : Cfg) (s s' : St) (op : Op) (ctm : Address), op.WritesCtmHandler ctm →
    Step K s op s' →
      s'.router.handler (ctmAssetId K ctm) = s.chainAssetHandler ∧
      s'.router.tracker (ctmAssetId K ctm) = K.ctmdt ∧
      (∀ a, a ≠ ctmAssetId K ctm → s'.router.handler a = s.router.handler a) ∧
      s'.chainAssetHandler = s.chainAssetHandler ∧
      (op = .registerCTMAssetOnL1 ctm → s'.ctmAssetIdToAddress (ctmAssetId K ctm) = ctm)

/-- **(d) THE CTMDT WRITERS ARE THE ONLY WRITERS OF A CTM'S HANDLER.**  Every call that
changes the handler at a CTM's id is one of the two CTMDT writers for that CTM, or the
vault fallback on an unset handler, or writes at the hash of a triple other than the
CTM's own `(L1, CTMDT, ctm)` that hashes to the CTM's id.  No hash premise. -/
def Properties.OnlyCtmTrackerRewritesCtmHandler : Prop :=
  ∀ (K : Cfg) (s s' : St) (op : Op) (ctm : Address), Step K s op s' →
    s'.router.handler (ctmAssetId K ctm) ≠ s.router.handler (ctmAssetId K ctm) →
      op.WritesCtmHandler ctm ∨
      (op = .finalize (ctmAssetId K ctm) ∧ s.router.handler (ctmAssetId K ctm) = 0) ∨
      ∃ t : Chain × Address × AssetData, op.handlerTriple K = some t ∧
        t ≠ (K.l1, K.ctmdt, ctm) ∧ K.enc t.1 t.2.1 t.2.2 = ctmAssetId K ctm

/-- **ONLY `setAddresses` MOVES THE BRIDGEHUB'S CHAIN ASSET HANDLER.** -/
def Properties.OnlySetAddressesMovesChainAssetHandler : Prop :=
  ∀ (K : Cfg) (s s' : St) (op : Op), Step K s op s' →
    s'.chainAssetHandler ≠ s.chainAssetHandler → op.IsSetAddresses

/-! ## Runs -/

/-- **A SET HANDLER OFF THE BRIDGEHUB STAYS OFF IT.**  From a state where the CTM's handler
is set and is not the Bridgehub, and the Bridgehub's `chainAssetHandler` is neither zero
nor the Bridgehub, along any run whose `setAddresses` calls never name zero or the
Bridgehub as chain asset handler, both stay so, unless the run logs a collision with the
CTM's triple. -/
def Properties.CtmHandlerStaysOffBridgehub : Prop :=
  ∀ (K : Cfg) (s s' : St) (ops : List Op) (ctm : Address), Run K s ops s' →
    HandlerOffBridgehub K ctm s → ChainAssetHandlerOk K s →
    (∀ op ∈ ops, op.KeepsChainAssetHandlerOk K) →
      (HandlerOffBridgehub K ctm s' ∧ ChainAssetHandlerOk K s') ∨ CollidesWithCtm K ctm ops

/-- **AFTER THE CTMDT REGISTERS A CTM, ITS HANDLER IS NEVER THE BRIDGEHUB.**  Along any run
that starts with a chain asset handler other than zero and the Bridgehub, whose
`setAddresses` calls keep it so, and that contains a CTMDT write for `ctm`, the CTM's
handler ends set and not the Bridgehub, unless the run logs a collision with the CTM's
triple.  The run may start anywhere, the Bridgehub as handler included. -/
def Properties.CtmHandlerOffBridgehubAfterRegistration : Prop :=
  ∀ (K : Cfg) (s s' : St) (ops : List Op) (ctm : Address), Run K s ops s' →
    ChainAssetHandlerOk K s → (∀ op ∈ ops, op.KeepsChainAssetHandlerOk K) →
    (∃ op ∈ ops, op.WritesCtmHandler ctm) →
      HandlerOffBridgehub K ctm s' ∨ CollidesWithCtm K ctm ops

/-- **WITHOUT `setAddresses`, THE CTM'S HANDLER STAYS THE CHAIN ASSET HANDLER.**  From a
state where the CTM's handler is the Bridgehub's nonzero `chainAssetHandler`, along any
run with no `setAddresses`, it stays so, unless the run logs a collision with the CTM's
triple. -/
def Properties.CtmHandlerIsChainAssetHandler : Prop :=
  ∀ (K : Cfg) (s s' : St) (ops : List Op) (ctm : Address), Run K s ops s' →
    s.router.handler (ctmAssetId K ctm) = s.chainAssetHandler → s.chainAssetHandler ≠ 0 →
    (∀ op ∈ ops, ¬ op.IsSetAddresses) →
      s'.router.handler (ctmAssetId K ctm) = s'.chainAssetHandler ∨ CollidesWithCtm K ctm ops

/-- **AFTER REGISTRATION, WITHOUT `setAddresses`, THE HANDLER IS THE CHAIN ASSET HANDLER.**
Along any run with no `setAddresses`, a nonzero chain asset handler, and a CTMDT write for
`ctm`, the CTM's handler ends as the Bridgehub's `chainAssetHandler`, unless the run logs
a collision with the CTM's triple. -/
def Properties.CtmHandlerIsChainAssetHandlerAfterRegistration : Prop :=
  ∀ (K : Cfg) (s s' : St) (ops : List Op) (ctm : Address), Run K s ops s' →
    s.chainAssetHandler ≠ 0 → (∀ op ∈ ops, ¬ op.IsSetAddresses) →
    (∃ op ∈ ops, op.WritesCtmHandler ctm) →
      s'.router.handler (ctmAssetId K ctm) = s'.chainAssetHandler ∨ CollidesWithCtm K ctm ops

/-- **HEADLINE: AFTER THE DEPLOYED REGISTRATION, P ACCEPTS EVERY MIGRATION OF THE CTM'S
CHAINS.**  After a run as in `CtmHandlerOffBridgehubAfterRegistration` that logs no
collision with the CTM's triple, for any `PermanentRestriction` reading the resulting
state, every migration request naming the CTM's asset id passes P whatever the
whitelist, hence whatever L2 admin it names; given that the Bridgehub answers no
`getChainId()` and is not the consulting `ChainAdmin`. -/
def Properties.DeployedRunsDisableMigrationCheck : Prop :=
  ∀ (K : Cfg) (s s' : St) (ops : List Op) (ctm : Address) (A : Abi) (E : Env)
    (chainAdmin : Address) (c : Call) (bridgehubData : Bytes),
    Run K s ops s' → ChainAssetHandlerOk K s → (∀ op ∈ ops, op.KeepsChainAssetHandlerOk K) →
    (∃ op ∈ ops, op.WritesCtmHandler ctm) → ¬ CollidesWithCtm K ctm ops →
    EnvReads K s' E → MigrationRequest A E c (ctmAssetId K ctm) bridgehubData →
    BridgehubAnswersNoChainId E → E.bridgehub ≠ chainAdmin →
      newAdminFromMigration A E c = .notMigration ∧
      ∀ allowed : Address → Bool,
        validateCall A { E with allowedL2Admins := allowed } chainAdmin c = true

/-! ## Witnesses and load-bearing premises -/

/-- **WITNESS: THE DEPLOYMENT SEQUENCE, AND P ACCEPTING AN UNLISTED ADMIN AFTER IT.**  From
`cawS0`, the router owner's tracker write and `registerCTMAssetOnL1(30)` succeed; the
premises of `CtmHandlerOffBridgehubAfterRegistration`,
`CtmHandlerIsChainAssetHandlerAfterRegistration` and `DeployedRunsDisableMigrationCheck`
hold, with no collision logged; the CTM's handler is the chain asset handler `13` and its
id maps to the CTM, so `cawS1` meets the start premises of `CtmHandlerStaysOffBridgehub`
and `CtmHandlerIsChainAssetHandler`.  A `PermanentRestriction` reading that state accepts
the migration request `prmCall`, whose L2 admin `66` is not whitelisted. -/
def Properties.CtmWritersDeploymentWitness : Prop :=
  Run cawCfg cawS0 cawOps cawS1 ∧ ChainAssetHandlerOk cawCfg cawS0 ∧
  HandlerOffBridgehub cawCfg 30 cawS1 ∧ ChainAssetHandlerOk cawCfg cawS1 ∧
  (∀ op ∈ cawOps, op.KeepsChainAssetHandlerOk cawCfg) ∧
  (∀ op ∈ cawOps, ¬ op.IsSetAddresses) ∧
  (∃ op ∈ cawOps, op.WritesCtmHandler 30) ∧ ¬ CollidesWithCtm cawCfg 30 cawOps ∧
  cawS1.router.handler (ctmAssetId cawCfg 30) = cawS1.chainAssetHandler ∧
  cawS1.chainAssetHandler = 13 ∧
  cawS1.ctmAssetIdToAddress (ctmAssetId cawCfg 30) = 30 ∧
  EnvReads cawCfg cawS1 cawEnv ∧
  MigrationRequest cawAbi cawEnv prmCall (ctmAssetId cawCfg 30) [3] ∧
  BridgehubAnswersNoChainId cawEnv ∧ cawEnv.bridgehub ≠ 20 ∧
  burnAdmin cawAbi [3] = some 66 ∧ cawEnv.allowedL2Admins 66 = false ∧
  validateCall cawAbi cawEnv 20 prmCall = true

/-- **THE `setAddresses` PREMISE IS LOAD-BEARING.**  If, after the deployment sequence,
`setAddresses` makes the Bridgehub its own chain asset handler and the CTMDT re-points the
CTM, the run logs no collision, the CTM's handler is the Bridgehub, and a
`PermanentRestriction` reading that state checks `prmCall`: it decodes the admin `66` and
rejects the call. -/
def Properties.BridgehubAsChainAssetHandlerWitness : Prop :=
  ∃ (s : St) (E : Env), Run cawCfg cawS0 cawOpsBridgehubAsHandler s ∧
    ¬ CollidesWithCtm cawCfg 30 cawOpsBridgehubAsHandler ∧
    s.router.handler (ctmAssetId cawCfg 30) = cawCfg.bridgehub ∧
    EnvReads cawCfg s E ∧ MigrationRequest cawAbi E prmCall (ctmAssetId cawCfg 30) [3] ∧
    newAdminFromMigration cawAbi E prmCall = .migration 66 ∧
    validateCall cawAbi E 20 prmCall = false

/-- **RE-POINTING THE CTM TO A CHAIN ASSET HANDLER SWITCHES P'S CHECK OFF.**  In `cawS3` the
CTM's handler is the Bridgehub and P rejects `prmCall` (its admin `66` is not
whitelisted).  An upgrade then installs the chain asset handler `13` and the CTMDT
re-points the CTM to it, with no collision logged.  From the state after `setAddresses`
the premises of `CtmHandlerOffBridgehubAfterRegistration` hold although the handler is
still the Bridgehub; at the end the handler is `13`, and P accepts the same call. -/
def Properties.RepointingToChainAssetHandlerDisablesCheck : Prop :=
  Run cawCfg cawS3 cawOpsRepoint cawS5 ∧
  cawS3.router.handler (ctmAssetId cawCfg 30) = cawCfg.bridgehub ∧
  EnvReads cawCfg cawS3 cawEnvBridgehubAsHandler ∧
  validateCall cawAbi cawEnvBridgehubAsHandler 20 prmCall = false ∧
  ChainAssetHandlerOk cawCfg cawS4 ∧
  cawS4.router.handler (ctmAssetId cawCfg 30) = cawCfg.bridgehub ∧
  Run cawCfg cawS4 [.setCtmAssetHandlerAddressOnL1 30] cawS5 ∧
  ¬ CollidesWithCtm cawCfg 30 cawOpsRepoint ∧
  HandlerOffBridgehub cawCfg 30 cawS5 ∧
  EnvReads cawCfg cawS5 cawEnvRepointed ∧
  validateCall cawAbi cawEnvRepointed 20 prmCall = true

/-- **THE COLLISION DISJUNCT FIRES.**  With an encoding that ignores the sender, after the
deployment sequence a vault registration of `bytes32(30)` with the Bridgehub as handler
succeeds and re-points the CTM's id to the Bridgehub, while the chain asset handler stays
good; the run logs exactly that collision. -/
def Properties.CtmHandlerCollisionWitness : Prop :=
  ∃ s : St, Run cawCollidingCfg cawS0 (cawOps ++ [.register 14 30 10]) s ∧
    ChainAssetHandlerOk cawCollidingCfg cawS0 ∧
    (∀ op ∈ cawOps ++ [.register 14 30 10], op.KeepsChainAssetHandlerOk cawCollidingCfg) ∧
    s.router.handler (ctmAssetId cawCollidingCfg 30) = cawCollidingCfg.bridgehub ∧
    CollidesWithCtm cawCollidingCfg 30 (cawOps ++ [.register 14 30 10])

end Contracts.ChainAdmin.CtmAssetHandlerWriters
