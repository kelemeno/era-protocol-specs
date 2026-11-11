import EraSpec.Contracts.DataEncoding.Properties.AssetIdRecovery
import EraSpec.Contracts.DataEncoding.Proofs.AssetIdRuns
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery

/-!
# Proofs: atomic recovery of a custom asset, with keccak as the id hash

As in `AssetIdRuns`: B1's theorem when its `IdInjOn` premises hold, and otherwise a router break
on a two-element set, which is a keccak collision on exactly those two preimages
(`assetIdRecovery_pair_break`). The witnesses are B1's, carried to byte level by
`RouterEncodingsAreKeccakInstances`.
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (HashCollision)
open AssetRouter.AtomicRecovery (Config Hooks World MintData recoverAtomicCall burnHandler
  outcomeOf VaultUnaware)

/-- A router break on a two-element set is a collision on its two preimages, in this order. -/
theorem assetIdRecovery_pair_break {keccak : Keccak} {c c' : AssetRouter.Chain}
    {s s' : AssetRouter.Address} {d d' : AssetRouter.AssetData}
    (h : RouterIdBreakOn keccak {(c, s, d), (c', s', d')}) :
    HashCollision keccak (routerPreimage c s d) (routerPreimage c' s' d') := by
  obtain ⟨p, hp, q, hq, hne, heq⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨hne, heq⟩
  · exact ⟨fun he => hne he.symm, heq.symm⟩
  · exact absurd rfl hne

/-- A collision on two preimages is a router break on the two-element set. -/
theorem assetIdRecovery_break_of_collision {keccak : Keccak} {c c' : AssetRouter.Chain}
    {s s' : AssetRouter.Address} {d d' : AssetRouter.AssetData}
    (h : HashCollision keccak (routerPreimage c s d) (routerPreimage c' s' d')) :
    RouterIdBreakOn keccak {(c, s, d), (c', s', d')} :=
  ⟨(c, s, d), Set.mem_insert _ _, (c', s', d'), Set.mem_insert_of_mem _ rfl, h⟩

/-- `IdInjOn` on a two-element set excludes the collision on its two preimages. -/
theorem assetIdRecovery_no_collision_of_injOn {keccak : Keccak} {c c' : AssetRouter.Chain}
    {s s' : AssetRouter.Address} {d d' : AssetRouter.AssetData}
    (h : AssetRouter.IdInjOn (routerEnc keccak) {(c, s, d), (c', s', d')}) :
    ¬ HashCollision keccak (routerPreimage c s d) (routerPreimage c' s' d') :=
  fun hc => (routerIdInjOn_iff keccak _).mp h (assetIdRecovery_break_of_collision hc)

theorem CustomAssetRecoveryRevertsOrKeccakCollision :
    Properties.CustomAssetRecoveryRevertsOrKeccakCollision := by
  intro X keccak cfg hk w dest src c₀ s d m hs hun
  rcases AssetRouter.AtomicRecovery.CustomAssetRecoveryRevertsOrCollision X (routerEnc keccak) cfg
    hk w dest src c₀ s d m hun with h | ⟨md, c, hm, hc, heq⟩
  · exact Or.inl h
  · exact Or.inr ⟨md, c, hm, hc, assetIdRuns_router_clash hs heq⟩

theorem CustomAssetRecoveryRevertsOrKeccakCollisionWitness :
    Properties.CustomAssetRecoveryRevertsOrKeccakCollisionWitness := by
  obtain ⟨enc, cfg, c₀, s, d, md, c, hs, hc, hne⟩ :=
    AssetRouter.AtomicRecovery.CustomCollisionNotTautology
  obtain ⟨keccak, rfl⟩ := RouterEncodingsAreKeccakInstances enc
  exact ⟨keccak, cfg, c₀, s, d, md, c, hs, hc, fun hcoll => hne hcoll.2⟩

theorem KeccakCollisionLetsVaultMintCustomAsset :
    Properties.KeccakCollisionLetsVaultMintCustomAsset := by
  obtain ⟨X, enc, cfg, hk, w, dest, src, c₀, s, d, md, hs, hun, hrec⟩ :=
    AssetRouter.AtomicRecovery.CollisionLetsVaultMintCustomAsset
  obtain ⟨keccak, rfl⟩ := RouterEncodingsAreKeccakInstances enc
  refine ⟨X, keccak, cfg, hk, w, dest, src, c₀, s, d, md, hs, hun, hrec, ?_⟩
  rcases CustomAssetRecoveryRevertsOrKeccakCollision X keccak cfg hk w dest src c₀ s d (some md)
    hs hun with hnone | ⟨md', c, hm, hc, hcoll⟩
  · rw [hnone] at hrec
    simp [outcomeOf] at hrec
  · obtain rfl : md' = md := (Option.some.inj hm).symm
    exact ⟨c, hc, hcoll⟩

theorem CustomHandlerDepositRefundRevertsOrKeccakCollision :
    Properties.CustomHandlerDepositRefundRevertsOrKeccakCollision := by
  intro X keccak cfg hk w log audit dest src c₀ s d m h0 hs hh0 hhn hrun
  by_cases h1 : ∀ p ∈ NativeTokenVault.registeredPairs cfg.thisChain log,
      AssetRouter.IdInjOn (routerEnc keccak) {(c₀, s, d), (p.1, cfg.ntv, p.2)}
  · by_cases h2 : ∀ md, m = some md → ∀ c, cfg.tokenOrigin md.metadata = some c →
        AssetRouter.IdInjOn (routerEnc keccak)
          {(c₀, s, d), (c, cfg.ntv, NativeTokenVaultBase.widen md.originToken)}
    · exact Or.inl (AssetRouter.AtomicRecovery.CustomHandlerDepositRefundReverts X
        (routerEnc keccak) cfg hk w log audit dest src c₀ s d m h0 hs hh0 hhn hrun h1 h2)
    · push Not at h2
      obtain ⟨md, hm, c, hc, hni⟩ := h2
      exact Or.inr (Or.inr ⟨md, c, hm, hc,
        assetIdRecovery_pair_break (assetIdRuns_break_of_not_injOn hni)⟩)
  · push Not at h1
    obtain ⟨p, hp, hni⟩ := h1
    exact Or.inr (Or.inl ⟨p, hp, assetIdRecovery_pair_break (assetIdRuns_break_of_not_injOn hni)⟩)

theorem CustomHandlerDepositRefundRevertsOrKeccakCollisionWitness :
    Properties.CustomHandlerDepositRefundRevertsOrKeccakCollisionWitness := by
  obtain ⟨X, enc, cfg, hk, w, log, audit, c₀, s, d, md, h0, hs, hh0, hhn, hrun, hne, h1, h2, hc,
    hp, hfrom, hdep, hmint⟩ := AssetRouter.AtomicRecovery.CustomHandlerDepositRefundRevertsSatisfiable
  obtain ⟨keccak, rfl⟩ := RouterEncodingsAreKeccakInstances enc
  exact ⟨X, keccak, cfg, hk, w, log, audit, c₀, s, d, md, h0, hs, hh0, hhn, hrun, hne,
    fun p hp' => assetIdRecovery_no_collision_of_injOn (h1 p hp'),
    fun c hc' => assetIdRecovery_no_collision_of_injOn (h2 c hc'), hc, hp, hfrom, hdep, hmint⟩

end Contracts.DataEncoding
