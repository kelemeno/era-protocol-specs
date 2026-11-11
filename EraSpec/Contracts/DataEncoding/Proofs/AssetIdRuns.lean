import EraSpec.Contracts.DataEncoding.Properties.AssetIdRuns
import EraSpec.Contracts.DataEncoding.Proofs.AssetId
import EraSpec.Contracts.AssetRouterBase.Proofs.HandlerRegistrationRuns

/-!
# Proofs: the router's and the vault's results with keccak as the id hash

Each reduction-form result is the model's result plus one case split. If the bounded premise
holds, the model's theorem applies. If it fails, `routerIdInjOn_iff` or
`vaultIdAssumptionsOn_iff` (topic `AssetId`) turns the failure into the named keccak event.
The per-call forms instead turn the model's id-equality disjunct into a collision with
`routerId_clash` / `vaultId_clash`, since distinct triples have distinct preimages.

The witnesses and countermodels are the model's own, carried over: every abstract encoding is
`routerEnc keccak` or `vaultEnc keccak` for some keccak (`RouterEncodingsAreKeccakInstances`,
`VaultEncodingsAreKeccakInstances`), so `subst` turns an abstract instance into a byte-level one.
-/

namespace Contracts.DataEncoding

open AttackVectors.BundleHashEncoding (HashCollision)

/-- Two router ids hashed from different senders are equal only through a keccak collision on
their two preimages. (Unbundled form of `routerId_clash`, so that unification stays first
order.) -/
theorem assetIdRuns_router_clash {keccak : Keccak} {c c' : AssetRouter.Chain}
    {s s' : AssetRouter.Address} {d d' : AssetRouter.AssetData} (hs : s ≠ s')
    (h : routerEnc keccak c s d = routerEnc keccak c' s' d') :
    HashCollision keccak (routerPreimage c s d) (routerPreimage c' s' d') :=
  ⟨fun he => hs (routerPreimage_inj he).2.1, h⟩

/-- Two vault ids of different pairs are equal only through a keccak collision on their two
preimages. (Unbundled form of `vaultId_clash`.) -/
theorem assetIdRuns_vault_clash {keccak : Keccak} {c c' : NativeTokenVault.Chain}
    {t t' : NativeTokenVault.Address} (hne : (c, t) ≠ (c', t'))
    (h : vaultEnc keccak c t = vaultEnc keccak c' t') :
    HashCollision keccak (vaultPreimage c t) (vaultPreimage c' t') := by
  refine ⟨fun he => hne ?_, h⟩
  obtain ⟨h1, h2⟩ := vaultPreimage_inj he
  rw [h1, h2]

/-- A failed bounded router premise is a router break. -/
theorem assetIdRuns_break_of_not_injOn {keccak : Keccak}
    {S : Set (AssetRouter.Chain × AssetRouter.Address × AssetRouter.AssetData)}
    (h : ¬ AssetRouter.IdInjOn (routerEnc keccak) S) : RouterIdBreakOn keccak S := by
  by_contra hno
  exact h ((routerIdInjOn_iff keccak S).mpr hno)

/-- A failed bounded vault premise is a vault event. -/
theorem assetIdRuns_break_of_not_idAssumptionsOn {keccak : Keccak}
    {S : Set (NativeTokenVault.Chain × NativeTokenVault.Address)}
    (h : ¬ NativeTokenVault.IdAssumptionsOn (vaultEnc keccak) S) : VaultIdBreakOn keccak S := by
  by_contra hno
  exact h ((vaultIdAssumptionsOn_iff keccak S).mpr hno)

/-! ## One router call -/

theorem NoHijackOrKeccakCollision : Properties.NoHijackOrKeccakCollision := by
  intro keccak thisChain ntv ntvAddr R caller d h hc s d' hs
  rcases AssetRouter.NoHijackOrCollision (routerEnc keccak) thisChain ntv ntvAddr R caller d h hc
    s d' hs with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (assetIdRuns_router_clash hs h2)

theorem NtvTouchesOnlyItsOwnIdsOrKeccakCollision :
    Properties.NtvTouchesOnlyItsOwnIdsOrKeccakCollision := by
  intro keccak thisChain ntv ntvAddr R d h s d' hs
  rcases AssetRouter.NtvTouchesOnlyItsOwnIdsOrCollision (routerEnc keccak) thisChain ntv ntvAddr R
    d h s d' hs with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (assetIdRuns_router_clash hs h2)

theorem NoHijackOrKeccakCollisionWitness : Properties.NoHijackOrKeccakCollisionWitness := by
  obtain ⟨enc, thisChain, ntv, ntvAddr, R, caller, d, s, d', hg, hc, hs, hne⟩ :=
    AssetRouter.NoHijackCollisionNotTautology
  obtain ⟨keccak, rfl⟩ := RouterEncodingsAreKeccakInstances enc
  exact ⟨keccak, thisChain, ntv, ntvAddr, R, caller, d, s, d', hg, hc, hs,
    fun hcoll => hne hcoll.2⟩

theorem NtvTouchesOnlyItsOwnIdsOrKeccakCollisionWitness :
    Properties.NtvTouchesOnlyItsOwnIdsOrKeccakCollisionWitness := by
  obtain ⟨enc, thisChain, ntv, ntvAddr, R, d, s, d', hg, hs, hne⟩ :=
    AssetRouter.NtvCollisionNotTautology
  obtain ⟨keccak, rfl⟩ := RouterEncodingsAreKeccakInstances enc
  exact ⟨keccak, thisChain, ntv, ntvAddr, R, d, s, d', hg, hs, fun hcoll => hne hcoll.2⟩

theorem KeccakCollisionHijacks : Properties.KeccakCollisionHijacks := by
  obtain ⟨enc, thisChain, ntv, ntvAddr, R, caller, d, h, s, d', hg, hc, hs, hch⟩ :=
    AssetRouter.HijackUnderCollision
  obtain ⟨keccak, rfl⟩ := RouterEncodingsAreKeccakInstances enc
  refine ⟨keccak, thisChain, ntv, ntvAddr, R, caller, d, h, s, d', hg, hc, hs, hch, ?_⟩
  rcases NoHijackOrKeccakCollision keccak thisChain ntv ntvAddr R caller d h hc s d' hs with
    h1 | h2
  · exact absurd h1 hch
  · exact h2

/-! ## Logged router runs -/

theorem LoggedRunNoHijackOrKeccakCollision : Properties.LoggedRunNoHijackOrKeccakCollision := by
  intro keccak thisChain ntv ntvAddr R₀ R log hrun pre post c S T hlog hpre hstep hc s d' hs
  by_cases hinj : AssetRouter.IdInjOn (routerEnc keccak)
      ↑(insert (thisChain, s, d') (AssetRouter.loggedTriples thisChain ntv ntvAddr log))
  · exact Or.inl (AssetRouter.LoggedRunNoHijack (routerEnc keccak) thisChain ntv ntvAddr R₀ R log
      hrun pre post c S T hlog hpre hstep hc s d' hs hinj)
  · exact Or.inr (assetIdRuns_break_of_not_injOn hinj)

theorem LoggedRunKeepsVaultRoutesOrKeccakCollision :
    Properties.LoggedRunKeepsVaultRoutesOrKeccakCollision := by
  intro keccak thisChain ntv ntvAddr R₀ R log hrun pre post c hlog hc hpost
  by_cases hinj : AssetRouter.IdInjOn (routerEnc keccak)
      ↑(AssetRouter.loggedTriples thisChain ntv ntvAddr log)
  · exact Or.inl (AssetRouter.LoggedRunKeepsVaultRoutes (routerEnc keccak) thisChain ntv ntvAddr
      R₀ R log hrun hinj pre post c hlog hc hpost)
  · exact Or.inr (assetIdRuns_break_of_not_injOn hinj)

theorem LoggedRunNoHijackOrKeccakCollisionWitness :
    Properties.LoggedRunNoHijackOrKeccakCollisionWitness := by
  obtain ⟨enc, thisChain, ntv, ntvAddr, R₀, R, log, pre, post, c, S, T, s, d', hrun, hlog, hpre,
    hstep, hc, hs, hinj, hR₀, hsn, htr, hha, p, hp, p', hp', hcoll⟩ :=
    AssetRouter.LoggedRunNoHijackSatisfiable
  obtain ⟨keccak, rfl⟩ := RouterEncodingsAreKeccakInstances enc
  have hpp' : p ≠ p' := by
    rintro rfl
    exact hp' (Finset.mem_insert_of_mem hp)
  exact ⟨keccak, thisChain, ntv, ntvAddr, R₀, R, log, pre, post, c, S, T, s, d', hrun, hlog, hpre,
    hstep, hc, hs, (routerIdInjOn_iff keccak _).mp hinj, hR₀, hsn, htr, hha, p, hp, p', hp',
    routerId_clash hpp' hcoll⟩

theorem LoggedRunKeepsVaultRoutesOrKeccakCollisionWitness :
    Properties.LoggedRunKeepsVaultRoutesOrKeccakCollisionWitness := by
  obtain ⟨enc, thisChain, ntv, ntvAddr, R₀, R, log, pre, post, c, hrun, hinj, hlog, hc, hpost,
    hR₀, hv, hnv, p, hp, p', hp', hcoll⟩ := AssetRouter.LoggedRunKeepsVaultRoutesSatisfiable
  obtain ⟨keccak, rfl⟩ := RouterEncodingsAreKeccakInstances enc
  have hpp' : p ≠ p' := by
    rintro rfl
    exact hp' hp
  exact ⟨keccak, thisChain, ntv, ntvAddr, R₀, R, log, pre, post, c, hrun,
    (routerIdInjOn_iff keccak _).mp hinj, hlog, hc, hpost, hR₀, hv, hnv, p, hp, p', hp',
    routerId_clash hpp' hcoll⟩

theorem KeccakCollisionOnLogTakesOverLiveRoute :
    Properties.KeccakCollisionOnLogTakesOverLiveRoute := by
  obtain ⟨enc, thisChain, ntv, ntvAddr, s, d, d', h, R₀, S, R, hsn, hsa, hh0, hhn, hR₀, hrun,
    hS, hstep, hRh, hRt, hguard, heq, hninj⟩ := AssetRouter.LoggedCollisionTakesOverLiveRoute
  obtain ⟨keccak, rfl⟩ := RouterEncodingsAreKeccakInstances enc
  exact ⟨keccak, thisChain, ntv, ntvAddr, s, d, d', h, R₀, S, R, hsn, hsa, hh0, hhn, hR₀, hrun,
    hS, hstep, hRh, hRt, hguard, assetIdRuns_router_clash (Ne.symm hsa) heq,
    assetIdRuns_break_of_not_injOn hninj⟩

/-! ## The vault registry -/

theorem RegisterNativeIdFreshOrKeccakEvent : Properties.RegisterNativeIdFreshOrKeccakEvent := by
  intro keccak thisChain V hV t hg
  rcases NativeTokenVault.RegisterNativeIdFreshOrCollision (vaultEnc keccak) thisChain V hV t hg
    with h1 | h2 | ⟨hreg, hne, heq⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · exact Or.inr (Or.inr ⟨hreg, assetIdRuns_vault_clash hne heq⟩)

theorem RegisterNativeIdFreshOrKeccakEventWitness :
    Properties.RegisterNativeIdFreshOrKeccakEventWitness := by
  obtain ⟨e, thisChain, V, t, hV, ha, hg, hz, hn⟩ := NativeTokenVault.RegisterNativeCollisionNotTautology
  obtain ⟨keccak, rfl⟩ := VaultEncodingsAreKeccakInstances e
  refine ⟨keccak, thisChain, V, t, hV, ha, hg, hz, ?_⟩
  rintro ⟨hreg, hne, heq⟩
  refine hn ⟨hreg, ?_, heq⟩
  intro hp
  apply hne
  rw [Prod.mk.injEq] at hp
  rw [hp.1, hp.2]

theorem RegisterNativeIdTakenByKeccakCollision :
    Properties.RegisterNativeIdTakenByKeccakCollision := by
  obtain ⟨e, thisChain, V, t, hV, hg, hreg, hne, heq⟩ := NativeTokenVault.RegisterNativeCollisionReachable
  obtain ⟨keccak, rfl⟩ := VaultEncodingsAreKeccakInstances e
  exact ⟨keccak, thisChain, V, t, hV, hg, hreg, assetIdRuns_vault_clash hne heq⟩

theorem LoggedRunSoundOrKeccakEvent : Properties.LoggedRunSoundOrKeccakEvent := by
  intro keccak thisChain h0 W log hrun
  by_cases hid : NativeTokenVault.IdAssumptionsOn (vaultEnc keccak)
      ↑(NativeTokenVault.registeredPairs thisChain log)
  · exact Or.inl (NativeTokenVault.LoggedRunSound (vaultEnc keccak) thisChain h0 W log hrun hid)
  · exact Or.inr (assetIdRuns_break_of_not_idAssumptionsOn hid)

theorem LoggedRunSoundOrKeccakEventWitness : Properties.LoggedRunSoundOrKeccakEventWitness := by
  obtain ⟨e, thisChain, W, log, h0, hrun, hid, hcard, ha⟩ := NativeTokenVault.LoggedRunSoundSatisfiable
  obtain ⟨keccak, rfl⟩ := VaultEncodingsAreKeccakInstances e
  exact ⟨keccak, thisChain, W, log, h0, hrun, (vaultIdAssumptionsOn_iff keccak _).mp hid, hcard, ha⟩

/-- With every id equal (`constId`), registering token `2` after token `1` breaks `Valid`: token
`1`'s `assetId` entry survives while the id's `tokenAddress` entry now names token `2`. -/
theorem assetIdRuns_twoReg_not_valid :
    ¬ NativeTokenVault.Valid NativeTokenVault.constId 1
      (NativeTokenVault.twoRegWorld NativeTokenVault.constId).vault := by
  intro hV
  have hvault : (NativeTokenVault.twoRegWorld NativeTokenVault.constId).vault
      = NativeTokenVault.setNewTokenStorage
          (NativeTokenVault.setNewTokenStorage NativeTokenVault.empty.vault 1 1 1 1) 1 2 2 1 := rfl
  rw [hvault] at hV
  have h12 : (1 : NativeTokenVault.Address) ≠ 2 := by decide
  have hof : (NativeTokenVault.setNewTokenStorage
      (NativeTokenVault.setNewTokenStorage NativeTokenVault.empty.vault 1 1 1 1) 1 2 2 1).assetOf 1
      = 1 := by
    rw [NativeTokenVault.sn_assetOf_of_ne _ _ _ _ _ h12, NativeTokenVault.sn_assetOf_self]
  have h := hV.tokenOfAsset 1 (by rw [hof]; decide)
  rw [hof, NativeTokenVault.sn_token_self] at h
  exact h12 h.symm

theorem LoggedRunSoundEventNeeded : Properties.LoggedRunSoundEventNeeded := by
  obtain ⟨keccak, hk⟩ := VaultEncodingsAreKeccakInstances NativeTokenVault.constId
  have hrun : NativeTokenVault.ReachLog (vaultEnc keccak) 1 NativeTokenVault.empty
      (NativeTokenVault.twoRegWorld (vaultEnc keccak)) [.registerNative 1, .registerNative 2] :=
    NativeTokenVault.twoReg_reachLog
  have hnv : ¬ NativeTokenVault.Valid (vaultEnc keccak) 1
      (NativeTokenVault.twoRegWorld (vaultEnc keccak)).vault := by
    rw [hk]
    exact assetIdRuns_twoReg_not_valid
  have hcoll : HashCollision keccak (vaultPreimage 1 1) (vaultPreimage 1 2) := by
    refine ⟨fun he => absurd (vaultPreimage_inj he).2 (by decide), ?_⟩
    have h1 : vaultEnc keccak 1 1 = vaultEnc keccak 1 2 := by rw [hk]; rfl
    exact h1
  refine ⟨keccak, NativeTokenVault.twoRegWorld (vaultEnc keccak), hrun, hnv, hcoll, ?_⟩
  rcases LoggedRunSoundOrKeccakEvent keccak 1 (by decide) _ _ hrun with h | h
  · exact absurd h.1 hnv
  · exact h

end Contracts.DataEncoding
