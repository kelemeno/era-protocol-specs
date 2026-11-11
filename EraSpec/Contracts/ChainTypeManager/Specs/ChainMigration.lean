import EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting

/-!
# Model: chains leaving and returning — a returning chain keeps its diamond

Source: branch `feat/upgrade-simplification` at `e561b9cc2`, as for
`EraSpec.Contracts.ChainTypeManager.Specs.ChainRouting`, whose system this model extends.
Paths are relative to `l1-contracts/contracts/`.

**This file is definitions only.** The results are in
`EraSpec.Contracts.ChainTypeManager.Properties.ChainMigration` and are proved in
`EraSpec.Contracts.ChainTypeManager.Proofs.ChainMigration`.

`ChainRouting` has one migration step, `migrateIn`: a chain that arrives where it has no
diamond gets a fresh one built from the CTM's current release. This file adds the other
half: the chain's diamond on this settlement layer stays registered while the chain lives
elsewhere, and a chain that comes back reuses it.

## Leaving

`ChainTypeManager.forwardedBridgeBurn` (`state-transition/ChainTypeManager.sol:726-746`)
requires the chain to be at the CTM's version:

    if (chainProtocolVersion != protocolVersion) { revert OutdatedProtocolVersion(...); } // :741-743

and the diamond's `Migrator.forwardedBridgeBurn`
(`state-transition/chain-deps/facets/Migrator.sol:154-209`) refuses a chain already away
and records the new settlement layer, touching neither routing nor version:

    if (s.settlementLayer != address(0)) { revert AlreadyMigrated(); }            // :162-164
    if (currentProtocolVersion != protocolVersion) { revert ProtocolVersionNotUpToDate(...); } // :196-198
    s.settlementLayer = _settlementLayer;                                         // :207

The bridgehub keeps the diamond registered (`BridgehubBase.sol:403-421` changes only the
chain's settlement layer and reads `zkChainMap`).

## Returning

`ChainAssetHandlerBase.bridgeMint` (`core/chain-asset-handler/ChainAssetHandlerBase.sol:361-420`):

    (address zkChain, address ctm) = IBridgehubBase(_getBridgehub()).forwardedBridgeMint(...); // :391-395
    bool contractAlreadyDeployed = zkChain != address(0);                          // :397
    if (!contractAlreadyDeployed) {                                                // :398
        zkChain = IChainTypeManager(ctm).forwardedBridgeMint(...);                 // :399
        ...
    } else { _getMessageRoot().setMigratingChainBatchNumber(...); }                // :410-415
    IZKChain(zkChain).forwardedBridgeMint(bridgehubMintData.chainData, contractAlreadyDeployed); // :417

So a registered chain skips `ChainTypeManager.forwardedBridgeMint` — and with it the CTM's
version check (:759-761) and `_deployNewChain`, which would revert `ChainAlreadyLive`
anyway (:680-683). The diamond's `Migrator.forwardedBridgeMint` (`Migrator.sol:213-305`)
does check the version, and clears the settlement layer:

    if (currentProtocolVersion != protocolVersion) { revert OutdatedProtocolVersion(...); } // :225-229
    if (!_contractAlreadyDeployed) { revert ContractNotDeployed(); }   // on L1, :277-279
    if (s.settlementLayer == address(0)) { revert NotMigrated(); }     // :280-282 (L1), :285-287
    s.settlementLayer = address(0);                                    // :299

Nothing on the return path writes the diamond's facet routing.

## A failed migration

`Migrator.forwardedBridgeConfirmTransferResult` (`Migrator.sol:309-333`), on a failed
transfer, refuses a chain not away (:324-326) and clears the settlement layer (:332),
touching neither routing nor version.

## Modelling choices

* **`away`** is the diamond's `s.settlementLayer != address(0)`.
* **Reject-only checks are omitted**: priority queue, deposit pause, admin, batches,
  settlement-layer CTM, migration numbers, message-root bookkeeping, and the version
  carried by a failed transfer's data (`Migrator.sol:327-330`). Omitting them only adds
  runs.
* **Every `ChainRouting` step is kept as is** and does not read `away`; in particular a
  diamond that is away can still be upgraded or cut, since `upgradeChainFromVersion`
  (`Admin.sol:528-559`) and `executeUpgrade` (:562-564) carry no `onlySettlementLayer`.
  On L1 the fresh `migrateIn` of `ChainRouting` cannot happen (`Migrator.sol:277-279`
  reverts `ContractNotDeployed`); keeping it only adds runs.
-/

namespace Contracts.ChainTypeManager

/-- The CTM, its chains, and which registered diamonds are away. -/
structure MSys where
  /-- The routing system. -/
  sys : Sys
  /-- `s.settlementLayer != address(0)` on each chain's diamond here. -/
  away : ChainId → Bool

/-- What happens. -/
inductive MLabel
  /-- A step of the routing model. -/
  | base (l : Label)
  /-- The chain leaves (`bridgeBurn` → `forwardedBridgeBurn`). -/
  | migrateOut (id : ChainId)
  /-- The chain comes back to its existing diamond (`bridgeMint` with
  `contractAlreadyDeployed`). -/
  | migrateReturn (id : ChainId)
  /-- A failed departure is confirmed (`forwardedBridgeConfirmTransferResult`, failure). -/
  | migrateRecover (id : ChainId)

/-- The break-glass steps. -/
def MLabel.isArbitrary : MLabel → Prop
  | .base l => l.isArbitrary
  | _ => False

/-- One step. -/
inductive MStep (W : World) : MSys → MLabel → MSys → Prop
  /-- A routing step; `away` is unchanged. -/
  | base {s : MSys} {l : Label} {s' : Sys} :
      Step W s.sys l s' → MStep W s (.base l) { s with sys := s' }
  /-- Leaving: the chain is registered, not away (`Migrator.sol:162-164`), and at the
  CTM's version (`ChainTypeManager.sol:741-743`, `Migrator.sol:196-198`). -/
  | migrateOut {s : MSys} {id : ChainId} {c : Chain} :
      s.sys.chains id = some c → s.away id = false → c.pv = s.sys.ctm.pv →
      MStep W s (.migrateOut id) { s with away := upd s.away id true }
  /-- Returning: the chain is registered, so its diamond is reused
  (`ChainAssetHandlerBase.sol:397-417`); it is away (`Migrator.sol:280-282`, :285-287) and
  at the CTM's version (`Migrator.sol:225-229`). -/
  | migrateReturn {s : MSys} {id : ChainId} {c : Chain} :
      s.sys.chains id = some c → s.away id = true → c.pv = s.sys.ctm.pv →
      MStep W s (.migrateReturn id) { s with away := upd s.away id false }
  /-- A failed departure: the chain is registered and away (`Migrator.sol:324-326`). -/
  | migrateRecover {s : MSys} {id : ChainId} {c : Chain} :
      s.sys.chains id = some c → s.away id = true →
      MStep W s (.migrateRecover id) { s with away := upd s.away id false }

/-- A sequence of steps. -/
inductive MRun (W : World) : MSys → List MLabel → MSys → Prop
  | nil {s : MSys} : MRun W s [] s
  | cons {s s' s'' : MSys} {l : MLabel} {ls : List MLabel} :
      MStep W s l s' → MRun W s' ls s'' → MRun W s (l :: ls) s''

/-- The steps that write a registered chain's diamond: a transition, the bootstrap reset,
and a break-glass cut. -/
def MLabel.writesDiamond (id : ChainId) : MLabel → Prop
  | .base (.transition id') => id' = id
  | .base (.bootstrapReset id') => id' = id
  | .base (.arbitraryCut id' _ _) => id' = id
  | _ => False

/-! ## Witness data -/

/-- The fresh witness system with nothing away. -/
def wMSys0 : MSys := ⟨wSys0, fun _ => false⟩

end Contracts.ChainTypeManager
