import EraSpec.Contracts.DataEncoding.Properties.AssetIdRecovery
import EraSpec.Contracts.DataEncoding.Proofs.AssetIdRuns
import EraSpec.Contracts.AssetRouterBase.Proofs.AtomicRecovery

/-!
# Proofs: atomic recovery of a custom asset, with keccak as the id hash

As in `AssetIdRuns`: the `AtomicRecovery` theorem when its `IdInjOn` premises hold, and
otherwise a router break on a two-element set, which is a keccak collision on exactly those two
preimages (`assetIdRecovery_pair_break`). The countermodel is `AtomicRecovery`'s, carried to byte
level by `RouterEncodingsAreKeccakInstances`. The two witnesses reuse `AtomicRecovery`'s witness
world (`wCfg`, `wWorld`, `okHooks`, `wMd`, the one-step registry run `[wOp]`) with the byte-level
instance of its encoding `wEnc` (`assetIdRecoveryKeccak`), and take the custom asset as
registered on this chain (chain `7`, sender `9`, data `1`) instead of that model's triple on
chain `0`.
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

theorem FailsAssetIdCheckIsLibraryRevert : Properties.FailsAssetIdCheckIsLibraryRevert := by
  intro keccak cfg a m hcfg
  have hid : AssetRouter.AtomicRecovery.ntvId (routerEnc keccak) cfg = vaultEnc keccak :=
    VaultModelIsRouterModelAtNtv keccak cfg hcfg
  unfold AssetRouter.AtomicRecovery.FailsAssetIdCheck
  rw [hid]
  refine forall_congr' fun md => forall_congr' fun _ => forall_congr' fun c =>
    forall_congr' fun _ => ?_
  rw [assetIdCheck_none_iff, VaultModelIsLibrary]

/-- The keccak of `FailsAssetIdCheckIsLibraryRevertWitness`: the NTV preimage of origin chain `1`
and origin token `9` goes to `1`, every other byte string to `2`. It is not a hash. -/
def assetIdRecoveryGuardKeccak : Keccak := fun x =>
  if x = assetIdPreimageOfToken 1 l2NtvAddr 9 then 1 else 2

/-- The mint data of `FailsAssetIdCheckIsLibraryRevertWitness`: original caller `11`, remote
receiver `12`, origin token `9`, amount `1`, empty metadata. -/
def assetIdRecoveryGuardMd : MintData := ⟨11, 12, 9, 1, []⟩

theorem assetIdRecoveryGuard_id :
    encodeNTVAssetIdOfToken assetIdRecoveryGuardKeccak 1 assetIdRecoveryGuardMd.originToken = 1 := by
  have hot : assetIdRecoveryGuardMd.originToken = 9 := rfl
  rw [hot]
  unfold encodeNTVAssetIdOfToken assetIdRecoveryGuardKeccak
  exact ite_eq_left rfl

/-- The witness uses `assetIdL2Config` (chain `324`, the vault at `L2_NATIVE_TOKEN_VAULT_ADDR`,
metadata decoding to origin chain `1`) and `assetIdRecoveryGuardMd`. -/
theorem FailsAssetIdCheckIsLibraryRevertWitness :
    Properties.FailsAssetIdCheckIsLibraryRevertWitness := by
  have hcfg : assetIdL2Config.ntv = addrAsBytes32 l2NtvAddr := rfl
  have hid := assetIdRecoveryGuard_id
  have h21 : (2 : UInt256) ≠ 1 := by decide
  have h10 : (1 : UInt256) ≠ 0 := by decide
  have hot : assetIdRecoveryGuardMd.originToken ≠ 0 := by
    show (9 : Addr) ≠ 0
    decide
  refine ⟨assetIdRecoveryGuardKeccak, assetIdL2Config, assetIdRecoveryGuardMd, 1, 2, hcfg,
    by decide, rfl, h10, hot, by rw [hid]; exact h10, ?_, by decide, by rw [hid]; exact h21, ?_⟩
  · rw [FailsAssetIdCheckIsLibraryRevert _ _ _ _ hcfg]
    intro h
    have := h assetIdRecoveryGuardMd rfl 1 rfl
    rw [assetIdCheck_none_iff] at this
    exact this rfl
  · rw [FailsAssetIdCheckIsLibraryRevert _ _ _ _ hcfg]
    intro md' hm c hc
    obtain rfl : md' = assetIdRecoveryGuardMd := (Option.some.inj hm).symm
    obtain rfl : c = 1 := (Option.some.inj hc).symm
    rw [assetIdCheck_none_iff, hid]
    exact h21

theorem CustomAssetRecoveryRevertsOrKeccakCollision :
    Properties.CustomAssetRecoveryRevertsOrKeccakCollision := by
  intro X keccak cfg hk w dest src c₀ s d m hs hun
  rcases AssetRouter.AtomicRecovery.CustomAssetRecoveryRevertsOrCollision X (routerEnc keccak) cfg
    hk w dest src c₀ s d m hun with h | ⟨md, c, hm, hc, heq⟩
  · exact Or.inl h
  · exact Or.inr ⟨md, c, hm, hc, assetIdRuns_router_clash hs heq⟩

/-- The keccak of the two witnesses: the byte-level instance of `AtomicRecovery`'s witness
encoding `wEnc` (ids hashed from the vault address `4` are `1`, every other id is `2`). -/
def assetIdRecoveryKeccak : Keccak := keccakOfRouterEnc AssetRouter.AtomicRecovery.wEnc

theorem assetIdRecovery_routerEnc :
    routerEnc assetIdRecoveryKeccak = AssetRouter.AtomicRecovery.wEnc :=
  routerEnc_keccakOfRouterEnc _

/-- The custom id of the witnesses, `encodeAssetId(7, 1, 9)` under `assetIdRecoveryKeccak`. -/
theorem assetIdRecovery_custom_id : routerEnc assetIdRecoveryKeccak 7 9 1 = 2 := by
  rw [assetIdRecovery_routerEnc]; unfold AssetRouter.AtomicRecovery.wEnc; decide

/-- Under `assetIdRecoveryKeccak` the custom preimage collides with no NTV preimage. -/
theorem assetIdRecovery_no_ntv_collision (c : AssetRouter.Chain) (t : AssetRouter.AssetData) :
    ¬ HashCollision assetIdRecoveryKeccak (routerPreimage 7 9 1)
      (routerPreimage c AssetRouter.AtomicRecovery.wCfg.ntv t) := by
  apply assetIdRecovery_no_collision_of_injOn
  rw [assetIdRecovery_routerEnc]
  exact AssetRouter.AtomicRecovery.wEnc_injOn _ _ _ _

theorem CustomAssetRecoveryRevertsOrKeccakCollisionWitness :
    Properties.CustomAssetRecoveryRevertsOrKeccakCollisionWitness := by
  open AssetRouter.AtomicRecovery in
  have hun : VaultUnaware wCfg wWorld.vault (routerEnc assetIdRecoveryKeccak 7 9 1) := by
    rw [assetIdRecovery_custom_id]; exact wVault_unaware_two
  have hs : (9 : AssetRouter.Address) ≠ AssetRouter.AtomicRecovery.wCfg.ntv := by decide
  refine ⟨Unit, assetIdRecoveryKeccak, AssetRouter.AtomicRecovery.wCfg,
    AssetRouter.AtomicRecovery.okHooks, AssetRouter.AtomicRecovery.wWorld, 8, 7, 7, 9, 1,
    AssetRouter.AtomicRecovery.wMd, 1, hs, hun, rfl, assetIdRecovery_no_ntv_collision _ _, rfl,
    fun _ _ _ _ => Option.some_ne_none _, fun _ _ _ _ => Option.some_ne_none _,
    fun _ _ _ _ => Option.some_ne_none _, ?_⟩
  rcases CustomAssetRecoveryRevertsOrKeccakCollision Unit assetIdRecoveryKeccak
    AssetRouter.AtomicRecovery.wCfg AssetRouter.AtomicRecovery.okHooks
    AssetRouter.AtomicRecovery.wWorld 8 7 7 9 1 (some AssetRouter.AtomicRecovery.wMd) hs hun with
    hnone | ⟨md', c', -, -, hcoll⟩
  · exact hnone
  · exact absurd hcoll (assetIdRecovery_no_ntv_collision _ _)

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
  refine ⟨Unit, assetIdRecoveryKeccak, AssetRouter.AtomicRecovery.wCfg,
    AssetRouter.AtomicRecovery.okHooks, AssetRouter.AtomicRecovery.wWorld,
    [AssetRouter.AtomicRecovery.wOp], NativeTokenVault.empty.audit, 7, 9, 1,
    AssetRouter.AtomicRecovery.wMd, by decide, by decide, ?_, ?_, ?_, ?_,
    fun _ _ => assetIdRecovery_no_ntv_collision _ _, fun _ _ => assetIdRecovery_no_ntv_collision _ _,
    ⟨1, rfl⟩, rfl, fun _ _ _ _ => Option.some_ne_none _, fun _ _ _ _ => Option.some_ne_none _,
    fun _ _ _ _ => Option.some_ne_none _⟩
  · rw [assetIdRecovery_custom_id]
    show AssetRouter.AtomicRecovery.wRouter.handler 2 ≠ 0
    unfold AssetRouter.AtomicRecovery.wRouter; decide
  · rw [assetIdRecovery_custom_id]
    show AssetRouter.AtomicRecovery.wRouter.handler 2 ≠ 4
    unfold AssetRouter.AtomicRecovery.wRouter; decide
  · rw [assetIdRecovery_routerEnc]; exact AssetRouter.AtomicRecovery.wReach
  · exact ⟨(1, 9), (NativeTokenVault.MemRegisteredPairs _ _ _).mpr
      ⟨AssetRouter.AtomicRecovery.wOp, List.mem_cons_self, rfl⟩⟩

end Contracts.DataEncoding
