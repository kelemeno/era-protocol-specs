import EraSpec.Contracts.DataEncoding.Specs.AssetIdRecovery

/-!
# Properties: atomic recovery of a custom asset, with keccak as the id hash

Statements about `EraSpec.Contracts.DataEncoding.Specs.AssetIdRecovery`. Proofs are in
`EraSpec.Contracts.DataEncoding.Proofs.AssetIdRecovery`.

B1's custom-asset results (`Contracts.AssetRouter.AtomicRecovery.Properties`), restated with
`enc := routerEnc keccak` and NO premise on keccak: the refund of a router-routed leg on a custom
asset reverts, or keccak collides on two named 96-byte preimages, namely the custom triple's and
the NTV preimage of an origin pair that the run or the call names. A witness shows the collision
disjunct is false on B1's own nontrivial instance, and a countermodel shows that under the
collision the vault really mints for the custom asset.
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (HashCollision)
open AssetRouter.AtomicRecovery (Config Hooks World MintData recoverAtomicCall burnHandler
  outcomeOf VaultUnaware)

/-- **A CUSTOM-ASSET REFUND REVERTS, OR KECCAK COLLIDES ON TWO NAMED PREIMAGES.**
`CustomAssetRecoveryRevertsOrCollision` at byte level. Take a custom asset
`a = encodeAssetId(c₀, d, s)` with registrant `s` not the vault, unknown to the vault. Then the
router's `recoverAtomicCall` of a `finalizeDeposit` call on `a` reverts, unless the call's mint
data decodes to an origin pair `(c, originToken)` and keccak collides on
`abi.encode(c₀, s, d)` and `abi.encode(c, vault, originToken)`. -/
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

/-- **ITS COLLISION DISJUNCT IS NOT A TAUTOLOGY.** A custom triple and decodable mint data whose
origin pair's NTV preimage keccak does not collide with the custom preimage. -/
def Properties.CustomAssetRecoveryRevertsOrKeccakCollisionWitness : Prop :=
  ∃ (keccak : Keccak) (cfg : Config) (c₀ : AssetRouter.Chain) (s : AssetRouter.Address)
    (d : AssetRouter.AssetData) (md : MintData) (c : AssetRouter.Chain),
    s ≠ cfg.ntv ∧ cfg.tokenOrigin md.metadata = some c
    ∧ ¬ HashCollision keccak (routerPreimage c₀ s d)
        (routerPreimage c cfg.ntv (NativeTokenVaultBase.widen md.originToken))

/-- **UNDER THE NAMED COLLISION THE VAULT MINTS FOR A CUSTOM ASSET.** A keccak, a custom asset
unknown to the vault, and decodable mint data on which the refund does not revert: the vault
deploys and registers a bridged token for the custom id and mints to the original caller. Keccak
then collides on the custom preimage and the NTV preimage of the decoded origin pair. So the
collision disjunct cannot be dropped. -/
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

/-- **HEADLINE (a) OF B1 AT BYTE LEVEL: A CUSTOM-HANDLER DEPOSIT IS BURNED BY ITS HANDLER AND ITS
REFUND REVERTS, OR KECCAK COLLIDES ON NAMED PREIMAGES.**
`CustomHandlerDepositRefundReverts` with its two `IdInjOn` premises dropped. Take asset
`a = encodeAssetId(c₀, d, s)`, registered by `s` (not the vault) and routed to a handler other
than the vault, with the vault's registry the end of a logged registry run. Then the burn at the
source went to the custom handler and the refund reverts, unless keccak collides on the custom
preimage `abi.encode(c₀, s, d)` and one of:

* the NTV preimage `abi.encode(p.1, vault, p.2)` of a pair `p` the registry run hashed;
* the NTV preimage of the origin pair decoded from the call's mint data. -/
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

/-- **ITS COLLISION DISJUNCTS ARE FALSE ON A NONTRIVIAL INSTANCE.** B1's witness at byte level: a
logged registry run with at least one hashed pair, a custom asset routed to a custom handler,
decodable mint data, every hook succeeding, and keccak colliding on none of the named preimage
pairs. -/
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
