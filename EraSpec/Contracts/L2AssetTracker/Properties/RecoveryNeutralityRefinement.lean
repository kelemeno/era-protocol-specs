import EraSpec.Contracts.L2AssetTracker.Specs.RecoveryNeutralityRefinement

/-!
# Properties: `RecoveryNeutrality`'s tracker is the canonical tracker

Statements about `EraSpec.Contracts.L2AssetTracker.Specs.RecoveryNeutralityRefinement`.  Proofs are
in `EraSpec.Contracts.L2AssetTracker.Proofs.RecoveryNeutralityRefinement`.  Each holds for every
configuration, system state, token reads, holder and upgrader address; none takes a premise about
the state.

* Registration: `RegisterNewTokenIsCanonical`, `RegisterLegacyIsCanonical`.
* The four flow hooks: `TrackerInitiateIsCanonical`, `TrackerInitiateBaseIsCanonical`,
  `TrackerFinalizeIsCanonical`, `TrackerFinalizeBaseIsCanonical`.  Each says that the
  `RecoveryNeutrality` function, mapped through `toStorage`, IS the canonical entry point called by
  its permitted caller on the projected storage, reverts included.
* The recovery guard: `VaultRecoverChecksHeadGuard`: with every check on, the vault recovery of
  `RecoveryNeutrality` reverts whenever the canonical guard `RecoveryAccountingNeutral` fails, and
  `VaultRecoverGuardIsHeadGuard`: its two vault checks are exactly that guard.
-/

namespace Contracts.L2AssetTracker.RecoveryNeutralityRefinement

open Contracts.L2AssetTracker

/-- `registerNewTokenIfNeeded(a, o)` called by the vault. -/
def Properties.RegisterNewTokenIsCanonical : Prop :=
  ∀ (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys) (holder upgrader : Address)
    (t : RecoveryNeutrality.Tracker) (a : AssetId) (o : ChainId),
    registerNewTokenIfNeeded (toConfig cfg sys holder upgrader) (toStorage cfg t) cfg.ntv a o =
      some (toStorage cfg (RecoveryNeutrality.registerNewToken cfg t a o))

/-- `_registerLegacyToken(a, tok)`, the first-touch registration's inner function. -/
def Properties.RegisterLegacyIsCanonical : Prop :=
  ∀ (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys) (holder upgrader : Address)
    (reads : RecoveryNeutrality.TokenReads) (t : RecoveryNeutrality.Tracker) (a : AssetId)
    (tok : Address),
    registerLegacyTokenInner (toConfig cfg sys holder upgrader) (toStorage cfg t) (toReads reads)
        a tok =
      (RecoveryNeutrality.registerLegacyInner cfg sys reads t a tok).map (toStorage cfg)

/-- The vault's `handleInitiateBridgingOnL2(d, a, x, originChainId[a])`. -/
def Properties.TrackerInitiateIsCanonical : Prop :=
  ∀ (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys) (holder upgrader : Address)
    (reads : RecoveryNeutrality.TokenReads) (d : ChainId) (a : AssetId) (x : UInt256),
    handleInitiateBridgingOnL2 (toConfig cfg sys holder upgrader) (toStorage cfg sys.trk) sys.sl
        (toReads reads) cfg.ntv d a x (sys.origin a) =
      (RecoveryNeutrality.trackerInitiate cfg sys reads d a x).map (toStorage cfg)

/-- The holder's `handleInitiateBaseTokenBridgingOnL2(d, x)`. -/
def Properties.TrackerInitiateBaseIsCanonical : Prop :=
  ∀ (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys) (holder upgrader : Address)
    (reads : RecoveryNeutrality.TokenReads) (d : ChainId) (x : UInt256),
    handleInitiateBaseTokenBridgingOnL2 (toConfig cfg sys holder upgrader) (toStorage cfg sys.trk)
        sys.sl (toReads reads) holder d x =
      (RecoveryNeutrality.trackerInitiateBase cfg sys reads d x).map (toStorage cfg)

/-- The vault's `handleFinalizeBridgingOnL2(c, a, x, originChainId[a], tokenAddress[a])`. -/
def Properties.TrackerFinalizeIsCanonical : Prop :=
  ∀ (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys) (holder upgrader : Address)
    (reads : RecoveryNeutrality.TokenReads) (c : ChainId) (a : AssetId) (x : UInt256),
    handleFinalizeBridgingOnL2 (toConfig cfg sys holder upgrader) (toStorage cfg sys.trk) sys.sl
        (toReads reads) cfg.ntv c a x (sys.origin a) (sys.token a) =
      (RecoveryNeutrality.trackerFinalize cfg sys reads c a x).map (toStorage cfg)

/-- `handleFinalizeBaseTokenBridgingOnL2(c, x)` called by the holder or by the base token. -/
def Properties.TrackerFinalizeBaseIsCanonical : Prop :=
  ∀ (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys) (holder upgrader : Address)
    (reads : RecoveryNeutrality.TokenReads) (caller : Address) (c : ChainId) (x : UInt256),
    (caller = holder ∨ caller = cfg.baseTokenAddr) →
    handleFinalizeBaseTokenBridgingOnL2 (toConfig cfg sys holder upgrader) (toStorage cfg sys.trk)
        sys.sl (toReads reads) caller c x =
      (RecoveryNeutrality.trackerFinalizeBase cfg sys reads c x).map (toStorage cfg)

/-- **The vault's two recovery checks are the canonical guard.**  With `Guards.v35`, the two checks
`RecoveryNeutrality.vaultRecover` makes before anything else (the tracker's
`assertRecoveryIsAccountingNeutral` as the vault calls it, `L2NTV:213`) pass exactly when
`RecoveryAccountingNeutral` holds on the projection. -/
def Properties.VaultRecoverGuardIsHeadGuard : Prop :=
  ∀ (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys) (holder upgrader : Address)
    (a : AssetId) (d : ChainId),
    RecoveryAccountingNeutral (toConfig cfg sys holder upgrader) (toStorage cfg sys.trk) a d ↔
      (¬ (RecoveryNeutrality.Guards.v35.vaultL1 = true ∧ d = cfg.l1) ∧
        ¬ (RecoveryNeutrality.Guards.v35.vaultBase = true ∧ a = cfg.base ∧
          sys.origin a = cfg.thisChain))

/-- **A recovery the canonical guard rejects reverts.**  With `Guards.v35`, whatever the mint
data, `RecoveryNeutrality.vaultRecover` reverts when `RecoveryAccountingNeutral` fails on the
projection. -/
def Properties.VaultRecoverChecksHeadGuard : Prop :=
  ∀ (cfg : RecoveryNeutrality.Config) (sys : RecoveryNeutrality.Sys) (holder upgrader : Address)
    (reads : AssetId → RecoveryNeutrality.TokenReads) (d : ChainId) (a : AssetId)
    (m : Option RecoveryNeutrality.MintData),
    ¬ RecoveryAccountingNeutral (toConfig cfg sys holder upgrader) (toStorage cfg sys.trk) a d →
      RecoveryNeutrality.vaultRecover cfg RecoveryNeutrality.Guards.v35 sys reads d a m = none

end Contracts.L2AssetTracker.RecoveryNeutralityRefinement
