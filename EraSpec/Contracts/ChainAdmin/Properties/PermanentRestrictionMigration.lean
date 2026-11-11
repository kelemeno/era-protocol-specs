import EraSpec.Contracts.ChainAdmin.Specs.PermanentRestrictionMigration

/-!
# Properties: when `PermanentRestriction` checks a migration, and why it never does

Statements about `EraSpec.Contracts.ChainAdmin.Specs.PermanentRestrictionMigration`.
Proofs are in `EraSpec.Contracts.ChainAdmin.Proofs.PermanentRestrictionMigration`.

A *migration request* (`MigrationRequest`) is a well-formed
`requestL2TransactionTwoBridges` call to P's Bridgehub, through the Bridgehub's asset
router, with `NEW_ENCODING_VERSION` data naming a chain asset id.  It is the call a
chain's admin makes to migrate the chain: the chain asset handler's `bridgeBurn` is
`onlyAssetRouter` and requires the Bridgehub's caller to be the chain's admin
(`core/chain-asset-handler/ChainAssetHandlerBase.sol:199, 225-227`), so the `ChainAdmin`
must call the Bridgehub itself.

## (a) The check fires exactly when the handler is the Bridgehub

* P decodes and checks an L2 admin `a` iff the call is a migration request whose asset id
  has a CTM (`ctmAssetIdToAddress id ≠ 0`), whose handler in the router is the Bridgehub,
  and whose burn data decodes to `a` (`MigrationCheckFiresIff`).
* On a migration request the migration check passes iff the id has no CTM, or its
  handler is not the Bridgehub, or the decoded admin is whitelisted
  (`MigrationCheckOutcome`).  It reverts only on undecodable data
  (`MigrationReadRevertsOnlyOnUndecodableData`).
* P's other two checks never reject a migration request: the Bridgehub answers no
  `getChainId()`, so it is not a chain the `ChainAdmin` administers, and it is not the
  `ChainAdmin` itself (`MigrationRequestPassesOtherChecks`).

## (b) The deployed configuration switches the check off

The deployment registers `BRIDGE_HUB.chainAssetHandler()` as the CTM asset's handler
(topic `CtmAssetHandlerWriters`).  When that handler is not the Bridgehub, P accepts every
migration request, whatever its L2 admin and whatever P's whitelist
(`DeployedConfigDisablesMigrationCheck`; the general form is
`HandlerOffBridgehubSkipsCheck`).  `PRMigrationDeployedCountermodel` is a concrete
instance: a migration to an admin no whitelist names, accepted.  So the intended guarantee
("a migration passes P only with a whitelisted L2 admin") is false as stated
(`MigrationWhitelistGuaranteeFails`); (c) and the repair below are its true forms.

## (c) With the Bridgehub as handler, the check is the whitelist

If the handler is the Bridgehub (what the comment at :353-354 expects, and what the unit
test mocks), P accepts a migration request only if its L2 admin is whitelisted
(`HandlerIsBridgehubForcesWhitelist`), and then it accepts it
(`HandlerIsBridgehubCheckIsTheWhitelist`).  `PRMigrationHandlerIsBridgehubWitness`.

## (e) The check never guards a migration that could succeed

The router calls `bridgeBurn` on the handler P reads (`burnTarget`).  Whenever P checks a
request, that call goes to the Bridgehub (`CheckedRequestsBurnAtBridgehub`), which
implements no `bridgeBurn`, so the migration reverts anyway.  Conversely, every migration
request whose `bridgeBurn` call can return passes P, whatever its L2 admin and whatever
the whitelist (`DeliverableMigrationsPassUnchecked`).  This needs no premise on the
deployment, only the code fact that the Bridgehub has no `bridgeBurn`.  So at both
snapshots P's `_validateMigrationToL2` rejects only migrations that would revert anyway.

## The repair

Comparing the handler with `BRIDGE_HUB.chainAssetHandler()` instead (not in the source)
makes the whitelist bind every migration request routed to the chain asset handler
(`RepairedCheckForcesWhitelist`, `RepairedCheckGuardsChainAssetHandlerBurns`).  Every
successful migration is routed there: the Bridgehub, the CTM and the chain's diamond
accept the migration's `forwarded…` calls only from `BRIDGE_HUB.chainAssetHandler()`
(`core/bridgehub/BridgehubBase.sol:161-166, 403-406`, `state-transition/ChainTypeManager.sol:221-231`,
`state-transition/chain-deps/facets/ZKChainBase.sol:112-117`).  The repair changes nothing
on other calls (`RepairedAgreesOffMigrationRequests`).  `PRMigrationRepairWitness`.
-/

namespace Contracts.ChainAdmin.PermanentRestrictionMigration

/-! ## (a) When the check fires -/

/-- **(a) P CHECKS AN L2 ADMIN EXACTLY WHEN THE CTM ASSET'S HANDLER IS THE BRIDGEHUB.**
`_getNewAdminFromMigration` returns `(l2Admin, true)` iff the call is a migration request
for some chain asset id, that id has a CTM, the router's handler for it is P's Bridgehub,
and its burn data decodes to `l2Admin`.  No premise. -/
def Properties.MigrationCheckFiresIff : Prop :=
  ∀ (A : Abi) (E : Env) (c : Call) (l2Admin : Address),
    newAdminFromMigration A E c = .migration l2Admin ↔
      ∃ (chainAssetId : AssetId) (bridgehubData : Bytes),
        MigrationRequest A E c chainAssetId bridgehubData ∧
        E.ctmAssetIdToAddress chainAssetId ≠ 0 ∧
        E.assetHandlerAddress chainAssetId = E.bridgehub ∧
        burnAdmin A bridgehubData = some l2Admin

/-- **THE MIGRATION CHECK ON A MIGRATION REQUEST.**  `_validateMigrationToL2` passes on a
migration request iff its asset id has no CTM, or the id's handler is not the Bridgehub,
or the burn data decodes to a whitelisted L2 admin. -/
def Properties.MigrationCheckOutcome : Prop :=
  ∀ (A : Abi) (E : Env) (c : Call) (chainAssetId : AssetId) (bridgehubData : Bytes),
    MigrationRequest A E c chainAssetId bridgehubData →
      (validateMigrationToL2 A E c = true ↔
        E.ctmAssetIdToAddress chainAssetId = 0 ∨
        E.assetHandlerAddress chainAssetId ≠ E.bridgehub ∨
        ∃ l2Admin, burnAdmin A bridgehubData = some l2Admin ∧ E.allowedL2Admins l2Admin = true)

/-- **`_getNewAdminFromMigration` REVERTS ONLY ON UNDECODABLE DATA.**  If it reverts, the
call is a `requestL2TransactionTwoBridges` call to the Bridgehub, and either its request
does not decode, or its second-bridge data (through the router with version `0x01`) does
not decode as `(bytes32, bytes)`, or it is a migration request whose burn data does not
decode to an admin. -/
def Properties.MigrationReadRevertsOnlyOnUndecodableData : Prop :=
  ∀ (A : Abi) (E : Env) (c : Call), newAdminFromMigration A E c = .reverts →
    c.target = E.bridgehub ∧
      ∃ args : Bytes, c.data = requestL2TransactionTwoBridgesSelector ++ args ∧
        (A.decodeTwoBridges args = none ∨
          (∃ (request : TwoBridgesRequest) (encodedData : Bytes),
            A.decodeTwoBridges args = some request ∧
            request.secondBridgeAddress = E.assetRouter ∧
            request.secondBridgeCalldata = NEW_ENCODING_VERSION :: encodedData ∧
            A.decodeAssetData encodedData = none) ∨
          ∃ (chainAssetId : AssetId) (bridgehubData : Bytes),
            MigrationRequest A E c chainAssetId bridgehubData ∧
            burnAdmin A bridgehubData = none)

/-- **THE OTHER TWO CHECKS NEVER REJECT A CALL TO THE BRIDGEHUB.**  If the Bridgehub answers
no `getChainId()` and is not the consulting `ChainAdmin`, then on every call to it
`_validateAsChainAdmin` and `_validateRemoveRestriction` pass, so `validateCall` (with any
expected handler) is the migration check alone. -/
def Properties.MigrationRequestPassesOtherChecks : Prop :=
  ∀ (A : Abi) (E : Env) (chainAdmin expectedHandler : Address) (c : Call),
    c.target = E.bridgehub → BridgehubAnswersNoChainId E → E.bridgehub ≠ chainAdmin →
      validateAsChainAdmin A E chainAdmin c = true ∧
      validateRemoveRestriction A E chainAdmin c = true ∧
      validateCallWith A E expectedHandler chainAdmin c =
        validateMigrationToL2With A E expectedHandler c

/-! ## (b) The deployed configuration -/

/-- **A HANDLER OTHER THAN THE BRIDGEHUB SWITCHES THE CHECK OFF.**  On a migration request
whose asset id's handler is not the Bridgehub, `_getNewAdminFromMigration` reports no
migration and P accepts the call, given that the Bridgehub answers no `getChainId()` and
is not the consulting `ChainAdmin`. -/
def Properties.HandlerOffBridgehubSkipsCheck : Prop :=
  ∀ (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) (chainAssetId : AssetId)
    (bridgehubData : Bytes),
    MigrationRequest A E c chainAssetId bridgehubData →
    E.assetHandlerAddress chainAssetId ≠ E.bridgehub →
    BridgehubAnswersNoChainId E → E.bridgehub ≠ chainAdmin →
      newAdminFromMigration A E c = .notMigration ∧ validateCall A E chainAdmin c = true

/-- **(b) THE DEPLOYED CONFIGURATION DISABLES P'S MIGRATION CHECK.**  If the CTM asset's
handler is `BRIDGE_HUB.chainAssetHandler()` (as `CTMDeploymentTracker` registers it) and
that is not the Bridgehub (`OPS-CONFIG`), then P accepts the migration request for every
whitelist: whatever `allowedL2Admins` holds, and so whatever L2 admin the request names.
Side premises as in `HandlerOffBridgehubSkipsCheck`. -/
def Properties.DeployedConfigDisablesMigrationCheck : Prop :=
  ∀ (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) (chainAssetId : AssetId)
    (bridgehubData : Bytes),
    MigrationRequest A E c chainAssetId bridgehubData →
    E.assetHandlerAddress chainAssetId = E.chainAssetHandler →
    E.chainAssetHandler ≠ E.bridgehub →
    BridgehubAnswersNoChainId E → E.bridgehub ≠ chainAdmin →
      newAdminFromMigration A E c = .notMigration ∧
      ∀ allowed : Address → Bool,
        validateCall A { E with allowedL2Admins := allowed } chainAdmin c = true

/-- **THE INTENDED GUARANTEE IS FALSE.**  "P lets a migration request for a CTM's chain
through only if it names a whitelisted L2 admin" does not hold: the deployed
configuration of `PRMigrationDeployedCountermodel` refutes it.  Its weakest true forms add
the premise that the handler is the Bridgehub (`HandlerIsBridgehubForcesWhitelist`), or
compare the handler with the chain asset handler instead (`RepairedCheckForcesWhitelist`). -/
def Properties.MigrationWhitelistGuaranteeFails : Prop :=
  ¬ ∀ (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) (chainAssetId : AssetId)
      (bridgehubData : Bytes),
      MigrationRequest A E c chainAssetId bridgehubData →
      E.ctmAssetIdToAddress chainAssetId ≠ 0 →
      validateCall A E chainAdmin c = true →
        ∃ l2Admin, burnAdmin A bridgehubData = some l2Admin ∧ E.allowedL2Admins l2Admin = true

/-! ## (c) The Bridgehub as handler -/

/-- **(c) WITH THE BRIDGEHUB AS HANDLER, P FORCES THE WHITELIST.**  If a migration request's
asset id has a CTM and its handler is the Bridgehub, P accepts the call only if the burn
data decodes to a whitelisted L2 admin.  No side premise. -/
def Properties.HandlerIsBridgehubForcesWhitelist : Prop :=
  ∀ (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) (chainAssetId : AssetId)
    (bridgehubData : Bytes),
    MigrationRequest A E c chainAssetId bridgehubData →
    E.ctmAssetIdToAddress chainAssetId ≠ 0 →
    E.assetHandlerAddress chainAssetId = E.bridgehub →
    validateCall A E chainAdmin c = true →
      ∃ l2Admin, burnAdmin A bridgehubData = some l2Admin ∧ E.allowedL2Admins l2Admin = true

/-- **WITH THE BRIDGEHUB AS HANDLER, P'S VERDICT IS THE WHITELIST.**  Under the side
premises of `HandlerOffBridgehubSkipsCheck`, such a request passes P iff its burn data
decodes to a whitelisted L2 admin. -/
def Properties.HandlerIsBridgehubCheckIsTheWhitelist : Prop :=
  ∀ (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) (chainAssetId : AssetId)
    (bridgehubData : Bytes),
    MigrationRequest A E c chainAssetId bridgehubData →
    E.ctmAssetIdToAddress chainAssetId ≠ 0 →
    E.assetHandlerAddress chainAssetId = E.bridgehub →
    BridgehubAnswersNoChainId E → E.bridgehub ≠ chainAdmin →
      (validateCall A E chainAdmin c = true ↔
        ∃ l2Admin, burnAdmin A bridgehubData = some l2Admin ∧ E.allowedL2Admins l2Admin = true)

/-! ## (e) The check never guards a migration that could succeed -/

/-- **P CHECKS ONLY REQUESTS THAT THE ROUTER BURNS AT THE BRIDGEHUB.**  Whenever
`_getNewAdminFromMigration` reports a migration, the call is a migration request whose
`bridgeBurn` the router sends to the Bridgehub itself (for a nonzero Bridgehub). -/
def Properties.CheckedRequestsBurnAtBridgehub : Prop :=
  ∀ (A : Abi) (E : Env) (c : Call) (l2Admin : Address),
    E.bridgehub ≠ 0 → newAdminFromMigration A E c = .migration l2Admin →
      ∃ (chainAssetId : AssetId) (bridgehubData : Bytes),
        MigrationRequest A E c chainAssetId bridgehubData ∧
        burnTarget E chainAssetId = E.bridgehub

/-- **(e) EVERY MIGRATION REQUEST THAT CAN REACH A `bridgeBurn` PASSES P UNCHECKED.**  If the
Bridgehub implements no `bridgeBurn` (true at both snapshots), then on every migration
request whose router `bridgeBurn` call can return, `_getNewAdminFromMigration` reports no
migration, and P accepts the call for every whitelist.  Side premises as in
`HandlerOffBridgehubSkipsCheck`.  No premise on which handler is registered. -/
def Properties.DeliverableMigrationsPassUnchecked : Prop :=
  ∀ (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) (chainAssetId : AssetId)
    (bridgehubData : Bytes),
    E.implementsBridgeBurn E.bridgehub = false → E.bridgehub ≠ 0 →
    MigrationRequest A E c chainAssetId bridgehubData →
    E.implementsBridgeBurn (burnTarget E chainAssetId) = true →
    BridgehubAnswersNoChainId E → E.bridgehub ≠ chainAdmin →
      newAdminFromMigration A E c = .notMigration ∧
      ∀ allowed : Address → Bool,
        validateCall A { E with allowedL2Admins := allowed } chainAdmin c = true

/-! ## The repair -/

/-- **THE REPAIRED CHECK FORCES THE WHITELIST ON CHAIN-ASSET-HANDLER MIGRATIONS.**  With the
handler compared to `BRIDGE_HUB.chainAssetHandler()`, a migration request whose asset id
has a CTM and whose handler is the chain asset handler passes only with a whitelisted L2
admin. -/
def Properties.RepairedCheckForcesWhitelist : Prop :=
  ∀ (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) (chainAssetId : AssetId)
    (bridgehubData : Bytes),
    MigrationRequest A E c chainAssetId bridgehubData →
    E.ctmAssetIdToAddress chainAssetId ≠ 0 →
    E.assetHandlerAddress chainAssetId = E.chainAssetHandler →
    validateCallRepaired A E chainAdmin c = true →
      ∃ l2Admin, burnAdmin A bridgehubData = some l2Admin ∧ E.allowedL2Admins l2Admin = true

/-- **THE REPAIRED CHECK GUARDS EVERY REQUEST THE ROUTER BURNS AT THE CHAIN ASSET HANDLER.**
If the vault is not the chain asset handler, every migration request whose asset id has a
CTM and whose router `bridgeBurn` goes to `BRIDGE_HUB.chainAssetHandler()` (as every
successful migration's does; see the header) passes the repaired P only with a
whitelisted L2 admin. -/
def Properties.RepairedCheckGuardsChainAssetHandlerBurns : Prop :=
  ∀ (A : Abi) (E : Env) (chainAdmin : Address) (c : Call) (chainAssetId : AssetId)
    (bridgehubData : Bytes),
    E.ntv ≠ E.chainAssetHandler →
    MigrationRequest A E c chainAssetId bridgehubData →
    E.ctmAssetIdToAddress chainAssetId ≠ 0 →
    burnTarget E chainAssetId = E.chainAssetHandler →
    validateCallRepaired A E chainAdmin c = true →
      ∃ l2Admin, burnAdmin A bridgehubData = some l2Admin ∧ E.allowedL2Admins l2Admin = true

/-- **THE REPAIR CHANGES NOTHING OFF MIGRATION REQUESTS.**  On a call that is not a
migration request for any asset id, the repaired and the deployed `validateCall` agree. -/
def Properties.RepairedAgreesOffMigrationRequests : Prop :=
  ∀ (A : Abi) (E : Env) (chainAdmin : Address) (c : Call),
    (∀ (chainAssetId : AssetId) (bridgehubData : Bytes),
      ¬ MigrationRequest A E c chainAssetId bridgehubData) →
      validateCallRepaired A E chainAdmin c = validateCall A E chainAdmin c

/-! ## Countermodel and witnesses -/

/-- **COUNTERMODEL: P ACCEPTS A MIGRATION TO AN ADMIN NO WHITELIST NAMES.**  In the deployed
configuration `prmEnv`, the call `prmCall` is a migration request for the CTM asset `100`
whose burn data names the L2 admin `66`; `66` is not whitelisted; the asset's handler is
the chain asset handler, which is not the Bridgehub and implements `bridgeBurn`; the
Bridgehub implements no `bridgeBurn` and answers no `getChainId()`.  P accepts the call.
This meets every premise of `DeployedConfigDisablesMigrationCheck` and
`DeliverableMigrationsPassUnchecked`. -/
def Properties.PRMigrationDeployedCountermodel : Prop :=
  MigrationRequest prmAbi prmEnv prmCall 100 [3] ∧
  burnAdmin prmAbi [3] = some 66 ∧ prmEnv.allowedL2Admins 66 = false ∧
  prmEnv.ctmAssetIdToAddress 100 ≠ 0 ∧
  prmEnv.assetHandlerAddress 100 = prmEnv.chainAssetHandler ∧
  prmEnv.chainAssetHandler ≠ prmEnv.bridgehub ∧
  prmEnv.implementsBridgeBurn (burnTarget prmEnv 100) = true ∧
  prmEnv.implementsBridgeBurn prmEnv.bridgehub = false ∧ prmEnv.bridgehub ≠ 0 ∧
  BridgehubAnswersNoChainId prmEnv ∧ prmEnv.bridgehub ≠ 20 ∧
  newAdminFromMigration prmAbi prmEnv prmCall = .notMigration ∧
  validateCall prmAbi prmEnv 20 prmCall = true

/-- **WITNESS: WITH THE BRIDGEHUB AS HANDLER THE CHECK BITES, AND THE MIGRATION CANNOT
SUCCEED.**  In `prmEnvHandlerIsBridgehub` the same call is checked: P decodes the admin
`66` and rejects the call.  With `66` whitelisted P accepts it.  In both, the router's
`bridgeBurn` would go to the Bridgehub, which implements none.  This meets the premises of
`HandlerIsBridgehubForcesWhitelist`, `HandlerIsBridgehubCheckIsTheWhitelist` and
`CheckedRequestsBurnAtBridgehub`. -/
def Properties.PRMigrationHandlerIsBridgehubWitness : Prop :=
  MigrationRequest prmAbi prmEnvHandlerIsBridgehub prmCall 100 [3] ∧
  prmEnvHandlerIsBridgehub.ctmAssetIdToAddress 100 ≠ 0 ∧
  prmEnvHandlerIsBridgehub.assetHandlerAddress 100 = prmEnvHandlerIsBridgehub.bridgehub ∧
  BridgehubAnswersNoChainId prmEnvHandlerIsBridgehub ∧ prmEnvHandlerIsBridgehub.bridgehub ≠ 0 ∧
  newAdminFromMigration prmAbi prmEnvHandlerIsBridgehub prmCall = .migration 66 ∧
  validateCall prmAbi prmEnvHandlerIsBridgehub 20 prmCall = false ∧
  validateCall prmAbi
    { prmEnvHandlerIsBridgehub with allowedL2Admins := fun a => decide (a = 66) } 20 prmCall =
      true ∧
  burnTarget prmEnvHandlerIsBridgehub 100 = prmEnvHandlerIsBridgehub.bridgehub ∧
  prmEnvHandlerIsBridgehub.implementsBridgeBurn prmEnvHandlerIsBridgehub.bridgehub = false

/-- **WITNESS: THE REPAIR REJECTS THE COUNTERMODEL'S CALL AND ACCEPTS A WHITELISTED ONE.**
In the deployed configuration the repaired P rejects `prmCall` (admin `66` is not
whitelisted) and accepts it once `66` is whitelisted; the router's `bridgeBurn` goes to the
chain asset handler, which is not the vault.  A call to another address is not a
migration request, and there the two versions agree, as on every such call.  This meets
the premises of `RepairedCheckForcesWhitelist`, `RepairedCheckGuardsChainAssetHandlerBurns`
and `RepairedAgreesOffMigrationRequests`. -/
def Properties.PRMigrationRepairWitness : Prop :=
  validateCallRepaired prmAbi prmEnv 20 prmCall = false ∧
  validateCallRepaired prmAbi prmEnvWhitelisted 20 prmCall = true ∧
  burnTarget prmEnv 100 = prmEnv.chainAssetHandler ∧ prmEnv.ntv ≠ prmEnv.chainAssetHandler ∧
  (∀ (chainAssetId : AssetId) (bridgehubData : Bytes),
    ¬ MigrationRequest prmAbi prmEnv { prmCall with target := 99 } chainAssetId bridgehubData)

/-- **WITNESS: AN UNDECODABLE REQUEST MAKES P REVERT.**  The request bytes `[9]` decode to
nothing, so `_getNewAdminFromMigration` reverts and P rejects the call.  This meets the
premise of `MigrationReadRevertsOnlyOnUndecodableData`. -/
def Properties.PRMigrationUndecodableWitness : Prop :=
  newAdminFromMigration prmAbi prmEnv
      ⟨10, 0, requestL2TransactionTwoBridgesSelector ++ [9]⟩ = .reverts ∧
  validateCall prmAbi prmEnv 20 ⟨10, 0, requestL2TransactionTwoBridgesSelector ++ [9]⟩ = false

end Contracts.ChainAdmin.PermanentRestrictionMigration
