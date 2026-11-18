import EraSpec.Contracts.DataEncoding.Specs.AssetIdRecovery

/-!
# Properties: atomic recovery of a custom asset, with keccak as the id hash

Statements about `EraSpec.Contracts.DataEncoding.Specs.AssetIdRecovery`. Proofs are in
`EraSpec.Contracts.DataEncoding.Proofs.AssetIdRecovery`.

The model restated here is the router's atomic-recovery model (`AssetRouterBase` `AtomicRecovery`),
which describes `recoverAtomicCall` at `c67894b9`; later trees send the refund to the asset's
registered handler instead (`Specs/AssetIdRecovery.lean`, "Later trees").

First, that model's abstract id guard `FailsAssetIdCheck` is, at byte level and with the vault at
`L2_NATIVE_TOKEN_VAULT_ADDR`, exactly the library's `assetIdCheck` reverting
(`FailsAssetIdCheckIsLibraryRevert`). Then its custom-asset results
(`Contracts.AssetRouter.AtomicRecovery.Properties`) are restated with
`enc := routerEnc keccak` and NO premise on keccak: the refund of a router-routed leg on a custom
asset reverts, or keccak collides on two named 96-byte preimages (`routerPreimage`), namely the
custom triple's and the NTV preimage of an origin pair that the run or the call names. For
senders that are real addresses these are the `abi.encode(chainId, sender, assetData)` bytes
`encodeAssetId` hashes (`RouterModelIsLibrary`). Witnesses show the collision disjuncts false
with every premise met, on the model's witness world with a custom asset registered on that
world's own chain, and a countermodel shows that under the collision the refund of a custom asset
the vault does not know returns `true` instead of reverting.
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (HashCollision)
open AssetRouter.AtomicRecovery (Config Hooks World MintData recoverAtomicCall burnHandler
  outcomeOf VaultUnaware)

/-- **THE RECOVERY MODEL'S ID GUARD IS THE LIBRARY'S `assetIdCheck`.** The atomic-recovery model
states the vault's guard abstractly: `FailsAssetIdCheck enc cfg a m` says that for the decoded
mint data `md` and every origin chain `c` its metadata decodes to, `a` is not
`ntvId enc cfg c (widen md.originToken)`.
With `enc := routerEnc keccak` and the vault configured at the normalised
`L2_NATIVE_TOKEN_VAULT_ADDR`, that is exactly `assetIdCheck(c, a, md.originToken)` reverting
(`DataEncoding.sol:208-214`) for each such `c`. -/
def Properties.FailsAssetIdCheckIsLibraryRevert : Prop :=
  ∀ (keccak : Keccak) (cfg : Config) (a : UInt256) (m : Option MintData),
    cfg.ntv = addrAsBytes32 l2NtvAddr →
      (AssetRouter.AtomicRecovery.FailsAssetIdCheck (routerEnc keccak) cfg a m ↔
        ∀ md, m = some md → ∀ c, cfg.tokenOrigin md.metadata = some c →
          assetIdCheck keccak c a md.originToken = none)

/-- **ITS PREMISE HOLDS, AND THE GUARD BOTH PASSES AND FAILS.** On a configuration with the vault
at the normalised `L2_NATIVE_TOKEN_VAULT_ADDR` on a nonzero chain, and mint data whose metadata
decodes to a nonzero origin chain and whose origin token is nonzero: the guard does not fail
for the (nonzero) NTV id of the decoded origin pair, and fails for a nonzero id that differs
from it. -/
def Properties.FailsAssetIdCheckIsLibraryRevertWitness : Prop :=
  ∃ (keccak : Keccak) (cfg : Config) (md : MintData) (c a : UInt256),
    cfg.ntv = addrAsBytes32 l2NtvAddr ∧ cfg.thisChain ≠ 0
    ∧ cfg.tokenOrigin md.metadata = some c ∧ c ≠ 0 ∧ md.originToken ≠ 0
    ∧ encodeNTVAssetIdOfToken keccak c md.originToken ≠ 0
    ∧ ¬ AssetRouter.AtomicRecovery.FailsAssetIdCheck (routerEnc keccak) cfg
        (encodeNTVAssetIdOfToken keccak c md.originToken) (some md)
    ∧ a ≠ 0 ∧ a ≠ encodeNTVAssetIdOfToken keccak c md.originToken
    ∧ AssetRouter.AtomicRecovery.FailsAssetIdCheck (routerEnc keccak) cfg a (some md)

/-- **A CUSTOM-ASSET REFUND REVERTS, OR KECCAK COLLIDES ON TWO NAMED PREIMAGES.**
`CustomAssetRecoveryRevertsOrCollision` at byte level. Take a custom asset
`a = routerEnc keccak c₀ s d` (for a real address `s`, `encodeAssetId(c₀, d, s)`) with registrant
`s` not the vault, unknown to the vault (`VaultUnaware`: no token recorded for `a`, and not native
here). Then the router's `recoverAtomicCall`, called by the flow manager, of a `finalizeDeposit`
call on `a` reverts, unless the call's mint data decodes to an origin pair `(c, originToken)` and
keccak collides on the two preimages `routerPreimage c₀ s d` and
`routerPreimage c vault originToken`. -/
def Properties.CustomAssetRecoveryRevertsOrKeccakCollision : Prop :=
  ∀ (X : Type) (keccak : Keccak) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src c₀ : AssetRouter.Chain) (s : AssetRouter.Address) (d : AssetRouter.AssetData)
    (m : Option MintData),
    s ≠ cfg.ntv → VaultUnaware cfg w.vault (routerEnc keccak c₀ s d) →
      recoverAtomicCall (routerEnc keccak) cfg hk w cfg.manager dest
          (.finalizeDeposit src (routerEnc keccak c₀ s d) m) = none
      ∨ ∃ md c, m = some md ∧ cfg.tokenOrigin md.metadata = some c
          ∧ HashCollision keccak (routerPreimage c₀ s d)
              (routerPreimage c cfg.ntv (NativeTokenVaultBase.widen md.originToken))

/-- **ITS PREMISES HOLD AND ITS COLLISION DISJUNCT IS FALSE, SO THE REFUND REVERTS.** A custom
triple (`s` not the vault) whose id the vault does not know, decodable mint data whose origin
pair's NTV preimage keccak does not collide with the custom preimage, an unpaused vault and
hooks that all succeed; the refund of the `finalizeDeposit` call on the custom id reverts. (In
the proof the custom asset is registered on the configuration's own chain.) -/
def Properties.CustomAssetRecoveryRevertsOrKeccakCollisionWitness : Prop :=
  ∃ (X : Type) (keccak : Keccak) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src c₀ : AssetRouter.Chain) (s : AssetRouter.Address) (d : AssetRouter.AssetData)
    (md : MintData) (c : AssetRouter.Chain),
    s ≠ cfg.ntv ∧ VaultUnaware cfg w.vault (routerEnc keccak c₀ s d)
    ∧ cfg.tokenOrigin md.metadata = some c
    ∧ ¬ HashCollision keccak (routerPreimage c₀ s d)
        (routerPreimage c cfg.ntv (NativeTokenVaultBase.widen md.originToken))
    ∧ w.paused = false
    ∧ (∀ x ch b amt, hk.fromChain x ch b amt ≠ none)
    ∧ (∀ x b ot ch, hk.deploy x b ot ch ≠ none)
    ∧ (∀ x tok rcv amt, hk.mint x tok rcv amt ≠ none)
    ∧ recoverAtomicCall (routerEnc keccak) cfg hk w cfg.manager dest
        (.finalizeDeposit src (routerEnc keccak c₀ s d) (some md)) = none

/-- **UNDER THE NAMED COLLISION THE VAULT MINTS FOR A CUSTOM ASSET.** A keccak, a custom asset
(`s` not the vault) unknown to the vault, and decodable mint data on which the manager's
`recoverAtomicCall` returns `true` (outcome `recovered`) instead of reverting. Keccak then collides
on the custom preimage and the NTV preimage of the decoded origin pair. So the collision disjunct
cannot be dropped. (For an asset the vault does not know, the model returns `true` only through
the vault's deploy branch, step 6 of `AtomicRecovery.vaultRefund`, which registers a bridged token
for the custom id and mints to the original caller; the statement records the outcome only.) -/
def Properties.KeccakCollisionLetsVaultMintCustomAsset : Prop :=
  ∃ (X : Type) (keccak : Keccak) (cfg : Config) (hk : Hooks X) (w : World X)
    (dest src c₀ : AssetRouter.Chain) (s : AssetRouter.Address) (d : AssetRouter.AssetData)
    (md : MintData),
    s ≠ cfg.ntv ∧ VaultUnaware cfg w.vault (routerEnc keccak c₀ s d)
    ∧ outcomeOf (recoverAtomicCall (routerEnc keccak) cfg hk w cfg.manager dest
        (.finalizeDeposit src (routerEnc keccak c₀ s d) (some md)))
      = AttackVectors.RecoveryLimits.Outcome.recovered
    ∧ ∃ c, cfg.tokenOrigin md.metadata = some c
      ∧ HashCollision keccak (routerPreimage c₀ s d)
          (routerPreimage c cfg.ntv (NativeTokenVaultBase.widen md.originToken))

/-- **HEADLINE (a) OF `AtomicRecovery` AT BYTE LEVEL: A CUSTOM-HANDLER DEPOSIT IS BURNED BY ITS
HANDLER AND ITS REFUND REVERTS, OR KECCAK COLLIDES ON NAMED PREIMAGES.**
`CustomHandlerDepositRefundReverts` with its two `IdInjOn` premises dropped. On a nonzero chain,
take asset `a = routerEnc keccak c₀ s d`, an id hashed from a sender `s` that is not the vault,
whose routing-table handler is neither zero nor the vault, with the vault's registry the end of a
logged registry run from fresh storage. Then the handler `_burn` picks at the source
(`burnHandler`) is not the vault, and the flow manager's `recoverAtomicCall` of a
`finalizeDeposit` call on `a` reverts, unless keccak collides on the custom preimage and one of:

* the NTV preimage `routerPreimage p.1 vault p.2` of a pair `p` the registry run hashed;
* the NTV preimage of the origin pair decoded from the call's mint data.

(The custom preimage is `routerPreimage c₀ s d`; for a real address `s` it is
`abi.encode(c₀, s, d)`.) -/
def Properties.CustomHandlerDepositRefundRevertsOrKeccakCollision : Prop :=
  ∀ (X : Type) (keccak : Keccak) (cfg : Config) (hk : Hooks X) (w : World X)
    (log : List NativeTokenVault.Op) (audit : NativeTokenVault.Audit)
    (dest src c₀ : AssetRouter.Chain) (s : AssetRouter.Address) (d : AssetRouter.AssetData)
    (m : Option MintData),
    cfg.thisChain ≠ 0 → s ≠ cfg.ntv →
    w.router.handler (routerEnc keccak c₀ s d) ≠ 0 →
    w.router.handler (routerEnc keccak c₀ s d) ≠ cfg.ntv →
    NativeTokenVault.ReachLog (AssetRouter.AtomicRecovery.ntvId (routerEnc keccak) cfg)
      cfg.thisChain NativeTokenVault.empty ⟨w.vault, audit⟩ log →
      (burnHandler cfg w.router (routerEnc keccak c₀ s d) ≠ cfg.ntv
        ∧ recoverAtomicCall (routerEnc keccak) cfg hk w cfg.manager dest
            (.finalizeDeposit src (routerEnc keccak c₀ s d) m) = none)
      ∨ (∃ p ∈ NativeTokenVault.registeredPairs cfg.thisChain log,
          HashCollision keccak (routerPreimage c₀ s d) (routerPreimage p.1 cfg.ntv p.2))
      ∨ (∃ md c, m = some md ∧ cfg.tokenOrigin md.metadata = some c
          ∧ HashCollision keccak (routerPreimage c₀ s d)
              (routerPreimage c cfg.ntv (NativeTokenVaultBase.widen md.originToken)))

/-- **ITS PREMISES HOLD AND ITS COLLISION DISJUNCTS ARE FALSE.** A nonzero chain, a logged
registry run with at least one hashed pair, a custom asset routed to a custom handler, decodable
mint data, an unpaused vault, every hook succeeding, and keccak colliding on none of the named
preimage pairs. (In the proof: `AtomicRecovery`'s witness world, with the custom asset registered
on the configuration's own chain.) -/
def Properties.CustomHandlerDepositRefundRevertsOrKeccakCollisionWitness : Prop :=
  ∃ (X : Type) (keccak : Keccak) (cfg : Config) (hk : Hooks X) (w : World X)
    (log : List NativeTokenVault.Op) (audit : NativeTokenVault.Audit)
    (c₀ : AssetRouter.Chain) (s : AssetRouter.Address) (d : AssetRouter.AssetData) (md : MintData),
    cfg.thisChain ≠ 0 ∧ s ≠ cfg.ntv
    ∧ w.router.handler (routerEnc keccak c₀ s d) ≠ 0
    ∧ w.router.handler (routerEnc keccak c₀ s d) ≠ cfg.ntv
    ∧ NativeTokenVault.ReachLog (AssetRouter.AtomicRecovery.ntvId (routerEnc keccak) cfg)
        cfg.thisChain NativeTokenVault.empty ⟨w.vault, audit⟩ log
    ∧ (NativeTokenVault.registeredPairs cfg.thisChain log).Nonempty
    ∧ (∀ p ∈ NativeTokenVault.registeredPairs cfg.thisChain log,
        ¬ HashCollision keccak (routerPreimage c₀ s d) (routerPreimage p.1 cfg.ntv p.2))
    ∧ (∀ c, cfg.tokenOrigin md.metadata = some c →
        ¬ HashCollision keccak (routerPreimage c₀ s d)
            (routerPreimage c cfg.ntv (NativeTokenVaultBase.widen md.originToken)))
    ∧ (∃ c, cfg.tokenOrigin md.metadata = some c) ∧ w.paused = false
    ∧ (∀ x ch b amt, hk.fromChain x ch b amt ≠ none)
    ∧ (∀ x b ot ch, hk.deploy x b ot ch ≠ none)
    ∧ (∀ x tok rcv amt, hk.mint x tok rcv amt ≠ none)

end Contracts.DataEncoding
