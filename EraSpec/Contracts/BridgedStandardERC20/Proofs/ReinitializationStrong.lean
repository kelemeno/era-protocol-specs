import EraSpec.Contracts.BridgedStandardERC20.Properties.ReinitializationStrong
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Reinitialization
import EraSpec.Contracts.BridgedStandardERC20.Proofs.LegacyFallback

/-!
# Proofs: the token's identity along runs with both branches of `onlyNTV`

A deployed step is a modelled step except for a ledger call on a zero vault, and the legacy
statements (`legacy_step_config`, `legacyStep_step_of_vault_ne`, `legacy_reachable_ledger`) say
what such a call does. The run statements are inductions carrying "the identity is the starting one,
or the fallback configuration of it" with the version nonzero, which keeps `bridgeInitialize`
closed. The fresh-proxy statements apply them to the storage `bridgeInitialize` leaves.
-/

namespace Contracts.BridgedStandardERC20

/-! ## The calls, unfolded -/

private theorem rs_initializeToken_view {s i : InitState} {caller : Address} {assetId : UInt256}
    {originToken : Address} {decoded : Bool}
    (h : initializeToken s caller assetId originToken decoded = some i) :
    s.version = 0 ∧ i = ⟨{ s.token with config := ⟨caller, originToken, assetId⟩ }, 1⟩ := by
  unfold initializeToken at h
  split at h
  · rename_i hg
    exact ⟨hg.1.1, (Option.some.inj h).symm⟩
  · cases h

private theorem rs_initializeStorage_view {s t : TokenStorage} {caller : Address}
    {assetId : UInt256} {originToken : Address} {decoded : Option Metadata}
    (h : initializeStorage s caller assetId originToken decoded = some t) :
    ∃ m, decoded = some m ∧ s.version = 0 ∧
      t = ⟨{ s.token with config := ⟨caller, originToken, assetId⟩ }, 1, m⟩ := by
  unfold initializeStorage at h
  split at h
  · cases h
  · rename_i m
    split at h
    · cases h
    · rename_i i hi
      obtain ⟨h0, rfl⟩ := rs_initializeToken_view hi
      exact ⟨m, rfl, h0, (Option.some.inj h).symm⟩

private theorem rs_initializeStorage_closed {s : TokenStorage} (hv : s.version ≠ 0)
    (caller : Address) (assetId : UInt256) (originToken : Address) (decoded : Option Metadata) :
    initializeStorage s caller assetId originToken decoded = none := by
  cases h : initializeStorage s caller assetId originToken decoded with
  | none => rfl
  | some t =>
    obtain ⟨_, _, h0, _⟩ := rs_initializeStorage_view h
    exact absurd h0 hv

/-- `bridgeInitialize` on a fresh proxy, computed. -/
private theorem rs_fresh_initializeStorage {caller : Address} {assetId : UInt256}
    {originToken : Address} {metadata : Metadata} (ho : originToken ≠ 0) :
    initializeStorage freshStorage caller assetId originToken (some metadata) =
      some ⟨⟨⟨caller, originToken, assetId⟩, fun _ => 0, 0⟩, 1, metadata⟩ := by
  have hi : initializeToken freshStorage.init caller assetId originToken true =
      some ⟨⟨⟨caller, originToken, assetId⟩, fun _ => 0, 0⟩, 1⟩ := by
    unfold initializeToken
    rw [ite_eq_left ⟨⟨rfl, ho⟩, rfl⟩]
    rfl
  unfold initializeStorage
  rw [hi]

private theorem rs_reinit_view {beaconOwner : Option Address} {s t : TokenStorage}
    {caller : Address} {getters : Getters} {name symbol : Text} {version : UInt8}
    (h : reinitializeToken beaconOwner s caller getters name symbol version = some t) :
    version.toNat = s.version.toNat + 1 ∧
      t = ⟨s.token, version, reinitMetadata s.metadata getters name symbol⟩ :=
  ⟨((ReinitSucceedsIff beaconOwner s caller getters name symbol version).mp ⟨t, h⟩).1,
    ReinitExactEffect beaconOwner s caller getters name symbol version t h⟩

private theorem rs_version_ne_zero_of_next {s : TokenStorage} {version : UInt8}
    (hn : version.toNat = s.version.toNat + 1) : version ≠ 0 := by
  intro h0
  rw [h0] at hn
  have : (0 : UInt8).toNat = 0 := rfl
  omega

/-- The L2 vault's zero-amount burn from a nonzero account, on a zero vault: it succeeds and
changes nothing but the configuration. -/
private theorem rs_zero_burn {env : LegacyEnv} {s : State} {owner : Address}
    (hl : s.config.vault = 0) (ho : owner ≠ 0) :
    bridgeBurn env s l2NativeTokenVaultAddr owner 0 =
      some { s with config := fallbackConfig env s.config } := by
  have h0 : (0 : UInt256).val ≤ s.balances owner := Nat.zero_le _
  rw [legacy_bridge_burn_enabled env hl ho h0]
  congr 1
  have hz : (0 : UInt256).val = 0 := rfl
  simp only [burnEffect, hz, Nat.sub_zero, Function.update_eq_self]

/-! ## The deployed steps and the modelled steps -/

private theorem rs_deployed_of_storageStep (env : LegacyEnv) {s t : TokenStorage}
    (h : StorageStep s t) : DeployedStorageStep env s t := by
  cases h with
  | bridgeInitialize h => exact DeployedStorageStep.bridgeInitialize h
  | reinitialize h => exact DeployedStorageStep.reinitialize h
  | ledger h => exact DeployedStorageStep.ledger (step_legacyStep env h)

private theorem rs_storageStep_of_deployed {env : LegacyEnv} {s t : TokenStorage}
    (hv : s.token.config.vault ≠ 0) (h : DeployedStorageStep env s t) : StorageStep s t := by
  cases h with
  | bridgeInitialize h => exact StorageStep.bridgeInitialize h
  | reinitialize h => exact StorageStep.reinitialize h
  | ledger h => exact StorageStep.ledger (legacyStep_step_of_vault_ne hv h)

theorem DeployedRunsIncludeModelledRuns : Properties.DeployedRunsIncludeModelledRuns := by
  intro env s t h
  induction h with
  | refl => exact DeployedStorageReach.refl
  | tail _ hstep ih => exact DeployedStorageReach.tail ih (rs_deployed_of_storageStep env hstep)

private theorem rs_step_ledger {env : LegacyEnv} {s t : TokenStorage} (hw : WellFormed s.token)
    (h : DeployedStorageStep env s t) :
    WellFormed t.token ∧ s.version.toNat ≤ t.version.toNat := by
  cases h with
  | bridgeInitialize h =>
    obtain ⟨_, _, h0, rfl⟩ := rs_initializeStorage_view h
    refine ⟨hw, ?_⟩
    rw [h0]
    exact Nat.zero_le _
  | reinitialize h =>
    obtain ⟨hn, rfl⟩ := rs_reinit_view h
    exact ⟨hw, by dsimp only; omega⟩
  | ledger h =>
    exact ⟨(legacy_reachable_ledger env hw (LegacyReach.tail LegacyReach.refl h)).1, le_rfl⟩

theorem DeployedRunsPreserveLedger : Properties.DeployedRunsPreserveLedger := by
  intro env s t hw h
  induction h with
  | refl => exact ⟨hw, le_rfl⟩
  | tail _ hstep ih =>
    obtain ⟨hwt, hle⟩ := ih
    obtain ⟨hwu, hle'⟩ := rs_step_ledger hwt hstep
    exact ⟨hwu, hle.trans hle'⟩

/-! ## The identity along deployed runs -/

theorem DeployedInitializedIdentityAtMostFallback :
    Properties.DeployedInitializedIdentityAtMostFallback := by
  intro env s t hv h
  induction h with
  | refl => exact ⟨Or.inl rfl, hv⟩
  | tail _ hstep ih =>
    obtain ⟨hc, hvt⟩ := ih
    cases hstep with
    | bridgeInitialize h' =>
      rw [rs_initializeStorage_closed hvt] at h'
      cases h'
    | reinitialize h' =>
      obtain ⟨hn, rfl⟩ := rs_reinit_view h'
      exact ⟨hc, rs_version_ne_zero_of_next hn⟩
    | ledger h' =>
      refine ⟨?_, hvt⟩
      dsimp only
      rcases legacy_step_config env h' with hc' | ⟨hz, hc'⟩
      · rw [hc']
        exact hc
      · rcases hc with hc | ⟨_, hc⟩
        · rw [hc] at hz hc'
          exact Or.inr ⟨hz, hc'⟩
        · rw [hc] at hz
          exact absurd hz (fallbackConfig_vault_ne env _)

theorem DeployedInitializedIdentityIsFixed : Properties.DeployedInitializedIdentityIsFixed := by
  intro env s t hv hvault h
  obtain ⟨hc, hvt⟩ := DeployedInitializedIdentityAtMostFallback env s t hv h
  rcases hc with hc | ⟨hz, _⟩
  · exact ⟨hc, hvt⟩
  · exact absurd hz hvault

theorem DeployedRunsAreModelledOnceVaultSet : Properties.DeployedRunsAreModelledOnceVaultSet := by
  intro env s t hv hvault
  refine ⟨fun h => ?_, DeployedRunsIncludeModelledRuns env s t⟩
  induction h with
  | refl => exact StorageReach.refl
  | @tail t u hr hstep ih =>
    have hc := (DeployedInitializedIdentityIsFixed env s t hv hvault hr).1
    have hvt : t.token.config.vault ≠ 0 := by
      rw [hc]
      exact hvault
    exact StorageReach.tail ih (rs_storageStep_of_deployed hvt hstep)

/-! ## Countermodels for a zero vault -/

theorem DeployedZeroVaultIdentityRewritten : Properties.DeployedZeroVaultIdentityRewritten := by
  intro env s owner hl ho
  have hb := rs_zero_burn (env := env) hl ho
  refine ⟨hb, DeployedStorageStep.ledger (LegacyStep.bridgeBurn hb), ?_⟩
  intro heq
  have hv := congrArg Config.vault heq
  rw [hl] at hv
  exact fallbackConfig_vault_ne env s.token.config hv

theorem DeployedIdentityNotFixedWithoutVault : Properties.DeployedIdentityNotFixedWithoutVault := by
  intro env hall
  let s : TokenStorage := ⟨⟨⟨0, 9, 5⟩, fun _ => 0, 0⟩, 1, emptyMetadata⟩
  obtain ⟨_, hstep, hne⟩ :=
    DeployedZeroVaultIdentityRewritten env s 1 rfl (by decide)
  exact hne (hall s _ (by decide) (DeployedStorageReach.tail DeployedStorageReach.refl hstep))

theorem DeployedReinitOnFreshProxyIdentity : Properties.DeployedReinitOnFreshProxyIdentity := by
  intro env owner getters name symbol
  obtain ⟨s, hs⟩ := (ReinitSucceedsIff (some owner) freshStorage owner getters name symbol 1).mpr
    ⟨rfl, rfl⟩
  have hform := ReinitExactEffect (some owner) freshStorage owner getters name symbol 1 s hs
  have hv : s.version ≠ 0 := by
    rw [hform]
    show (1 : UInt8) ≠ 0
    decide
  have hcfg : s.token.config = ⟨0, 0, 0⟩ := by
    rw [hform]
    rfl
  refine ⟨s, hs, ?_, ?_⟩
  · intro t ht
    obtain ⟨hc, hvt⟩ := DeployedInitializedIdentityAtMostFallback env s t hv ht
    refine ⟨?_, rs_initializeStorage_closed hvt⟩
    rcases hc with hc | ⟨_, hc⟩
    · exact Or.inl (hc.trans hcfg)
    · rw [hcfg] at hc
      exact Or.inr hc
  · have hl : s.token.config.vault = 0 := by
      rw [hcfg]
    obtain ⟨_, hstep, hne⟩ := DeployedZeroVaultIdentityRewritten env s 1 hl (by decide)
    refine ⟨_, hstep, ?_, hne⟩
    show fallbackConfig env s.token.config = fallbackConfig env ⟨0, 0, 0⟩
    rw [hcfg]

/-! ## The fresh-proxy lifecycle on the deployed token -/

/-- What `bridgeInitialize` on a fresh proxy leaves: version 1, the bound identity, an empty
`WellFormed` ledger. -/
private theorem rs_fresh_init_facts {caller : Address} {assetId : UInt256}
    {originToken : Address} {metadata : Metadata} {s : TokenStorage}
    (h : initializeStorage freshStorage caller assetId originToken (some metadata) = some s) :
    s.version ≠ 0 ∧ s.token.config = ⟨caller, originToken, assetId⟩ ∧ WellFormed s.token := by
  obtain ⟨_, _, _, rfl⟩ := rs_initializeStorage_view h
  refine ⟨show (1 : UInt8) ≠ 0 by decide, rfl, ?_⟩
  refine ⟨Finset.sum_const_zero, ?_, rfl⟩
  norm_num [freshStorage, freshProxy, empty, UInt256.size]

theorem DeployedFreshProxyRunsAreModelled : Properties.DeployedFreshProxyRunsAreModelled := by
  intro env caller assetId originToken metadata s t hcaller hi
  obtain ⟨hv, hc, _⟩ := rs_fresh_init_facts hi
  have hvault : s.token.config.vault ≠ 0 := by
    rw [hc]
    exact hcaller
  exact DeployedRunsAreModelledOnceVaultSet env s t hv hvault

theorem DeployedFreshProxyLifecycle : Properties.DeployedFreshProxyLifecycle := by
  intro env caller assetId originToken metadata s t hcaller hi hr
  have hr' := (DeployedFreshProxyRunsAreModelled env caller assetId originToken metadata s t
    hcaller hi).mp hr
  exact FreshProxyLifecycle caller assetId originToken metadata s t hi hr'

theorem DeployedFreshProxyLifecycleAnyCaller : Properties.DeployedFreshProxyLifecycleAnyCaller := by
  intro env caller assetId originToken metadata s t hi hr
  obtain ⟨hv, hc, hw⟩ := rs_fresh_init_facts hi
  obtain ⟨hct, hvt⟩ := DeployedInitializedIdentityAtMostFallback env s t hv hr
  refine ⟨?_, (DeployedRunsPreserveLedger env s t hw hr).1, rs_initializeStorage_closed hvt⟩
  rcases hct with hct | ⟨hz, hct⟩
  · exact Or.inl (hct.trans hc)
  · rw [hc] at hz hct
    exact Or.inr ⟨hz, hct⟩

theorem DeployedFreshProxyZeroCallerRewritten :
    Properties.DeployedFreshProxyZeroCallerRewritten := by
  intro env assetId originToken metadata ho
  have hi := rs_fresh_initializeStorage (caller := 0) (assetId := assetId) (metadata := metadata) ho
  obtain ⟨_, hstep, hne⟩ := DeployedZeroVaultIdentityRewritten env
    ⟨⟨⟨0, originToken, assetId⟩, fun _ => 0, 0⟩, 1, metadata⟩ 1 rfl (by decide)
  exact ⟨_, _, hi, hstep, rfl, hne⟩

theorem DeployedFreshProxyLifecycleNeedsNonzeroCaller :
    Properties.DeployedFreshProxyLifecycleNeedsNonzeroCaller := by
  intro env hall
  obtain ⟨s, t, hi, hstep, _, hne⟩ :=
    DeployedFreshProxyZeroCallerRewritten env 5 9 emptyMetadata (by decide)
  exact hne (hall 0 5 9 emptyMetadata s t hi
    (DeployedStorageReach.tail DeployedStorageReach.refl hstep))

/-! ## Witness -/

theorem DeployedLifecycleWitness : Properties.DeployedLifecycleWitness := by
  intro env
  have hi := rs_fresh_initializeStorage (caller := 1) (assetId := 5) (metadata := emptyMetadata)
    (originToken := 9) (by decide)
  let c : Config := ⟨1, 9, 5⟩
  obtain ⟨hw0, funded, hmint, _, _⟩ := one_unit_roundtrip c 4 (by decide) (by decide)
  have hsupply : funded.totalSupply = 1 := by
    obtain ⟨_, _, _, hs, _, _⟩ := mint_exact hmint
    rw [hs]
    rfl
  have hcfg : funded.config = c := (mint_exact hmint).2.2.2.2.2
  -- the vault's one-unit mint, through `onlyNTV` on its nonlegacy branch
  have hstep₁ : DeployedStorageStep env ⟨empty c, 1, emptyMetadata⟩
      ⟨funded, 1, emptyMetadata⟩ :=
    DeployedStorageStep.ledger (LegacyStep.bridgeMint (bridgeMint_of_mint env hmint))
  -- the beacon owner's reinitialization to version 2
  obtain ⟨t, ht⟩ := (ReinitSucceedsIff (some 7) ⟨funded, 1, emptyMetadata⟩ 7
    ⟨true, false, false⟩ [0x42] [0x43] 2).mpr ⟨rfl, rfl⟩
  have hform := ReinitExactEffect (some 7) ⟨funded, 1, emptyMetadata⟩ 7
    ⟨true, false, false⟩ [0x42] [0x43] 2 t ht
  have hrun : DeployedStorageReach env ⟨empty c, 1, emptyMetadata⟩ t :=
    DeployedStorageReach.tail (DeployedStorageReach.tail DeployedStorageReach.refl hstep₁)
      (DeployedStorageStep.reinitialize ht)
  refine ⟨⟨empty c, 1, emptyMetadata⟩, t, hi, by decide, by decide, hw0, hrun, ?_, ?_, ?_, ?_⟩
  · rw [hform]
  · rw [hform]
    exact hsupply
  · rw [hform]
    exact hcfg
  · exact ⟨_, rs_fresh_initializeStorage (caller := 0) (by decide), by decide, rfl⟩

end Contracts.BridgedStandardERC20
