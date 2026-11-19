import EraSpec.Contracts.L2AssetTracker.Specs.LaterHeads
import EraSpec.Contracts.L2AssetTracker.Specs.RecoveryNeutrality

/-!
# Refinement: the `RecoveryNeutrality` tracker is the canonical tracker model

Source: era-contracts `draft/v0.35.0` head `b17415d20`, `l1-contracts/contracts/bridge/asset-tracker/
L2AssetTracker.sol` (`TRK`) and `bridge/ntv/L2NativeTokenVault.sol` (`L2NTV`).

This folder has two transcriptions of the tracker's code at `b17415d20`:

* the canonical one, namespace `Contracts.L2AssetTracker` (`Specs/Accounting.lean`, with the
  `b17415d20` step `HeadStep` and the recovery guard `RecoveryAccountingNeutral` of
  `Specs/LaterHeads.lean`): storage `Storage`, the vault's maps fixed in `Config`;
* the one inside `Contracts.L2AssetTracker.RecoveryNeutrality` (`Specs/RecoveryNeutrality.lean`),
  which composes the tracker with the vault's registry, the router, the base-token holder and the
  flow manager, and keeps one value for each copy of `L1_CHAIN_ID` and `BASE_TOKEN_ASSET_ID` in its
  `Config`.

This file defines the projection from the second to the first.  `toStorage cfg t` is the tracker
storage `t` with `L1_CHAIN_ID`, `BASE_TOKEN_ASSET_ID` taken from `cfg` and `initL2` done
(`RecoveryNeutrality` runs start after genesis, and the backfill flag's slot is never written at
`b17415d20`, `TRK:65`).  `toConfig cfg sys` is the canonical `Config` whose vault maps are
`sys`'s at the moment of the call.  The results (`Properties/RecoveryNeutralityRefinement.lean`)
show that each tracker function of `RecoveryNeutrality` is the canonical one on the projection,
and that its vault recovery check with every guard on (`Guards.v35`) is `RecoveryAccountingNeutral`.
So `RecoveryNeutrality`'s results are about the same tracker code as the canonical model's.

The canonical `Config` fixes the vault's maps for a run, while `RecoveryNeutrality` lets them
change (`vaultRegister`, `vaultUpdateBase`); the correspondence is therefore per call, with the
maps of that call.  The system addresses other than the vault (`holder`, `upgrader`) are free
parameters: the canonical functions read them only in caller checks, which the projection passes.
-/

namespace Contracts.L2AssetTracker.RecoveryNeutralityRefinement

open Contracts.L2AssetTracker

/-- The canonical `SavedTotalSupply` of a `RecoveryNeutrality` one (the same two fields). -/
def toSaved (x : RecoveryNeutrality.SavedTotalSupply) : SavedTotalSupply := ⟨x.isSaved, x.amount⟩

/-- The canonical `InteropL2Info` of a `RecoveryNeutrality` one (the same two fields). -/
def toInfo (x : RecoveryNeutrality.InteropL2Info) : InteropL2Info :=
  ⟨x.totalWithdrawalsToL1, x.totalSuccessfulDepositsFromL1⟩

/-- The canonical token reads of a `RecoveryNeutrality` one (the same two values). -/
def toReads (r : RecoveryNeutrality.TokenReads) : TokenReads := ⟨r.totalSupply, r.ntvBalance⟩

/-- **The storage projection.**  The tracker's four live maps as they are; `L1_CHAIN_ID` and
`BASE_TOKEN_ASSET_ID` from the configuration; the backfill flag clear; `initL2` done. -/
def toStorage (cfg : RecoveryNeutrality.Config) (t : RecoveryNeutrality.Tracker) : Storage where
  chainBalance := t.chainBalance
  isAssetRegistered := t.isAssetRegistered
  l1ChainId := cfg.l1
  baseTokenAssetId := cfg.base
  interopInfo := toInfo ∘ t.interopInfo
  totalPreV31TotalSupply := toSaved ∘ t.totalPreV31TotalSupply
  needBaseTokenTotalSupplyBackfill := false
  guardInitialized := true

/-- **The configuration projection**, at one call: the vault's maps as `sys` has them, the vault
address `cfg.ntv`, the base token `cfg.baseTokenAddr`, and the given holder and upgrader
addresses. -/
def toConfig (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys)
    (holder upgrader : Address) : Config where
  ntv := cfg.ntv
  baseTokenHolder := holder
  l2BaseToken := cfg.baseTokenAddr
  upgrader := upgrader
  thisChain := cfg.thisChain
  ntvOriginChainId := sys.origin
  ntvTokenAddress := sys.token
  initL1ChainId := cfg.l1
  initBaseAssetId := cfg.base

end Contracts.L2AssetTracker.RecoveryNeutralityRefinement
