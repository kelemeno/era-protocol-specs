import EraSpec.Contracts.BridgedStandardERC20.Properties.ReinitializationFaithful
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Reinitialization
import EraSpec.Contracts.BridgedStandardERC20.Proofs.LegacyFallback

/-!
# Proofs: the token's runs, with both branches of `onlyNTV`

The identity results reduce to one fact about a step from a nonzero version
(`faithful_step_config`). `bridgeInitialize` is closed there. `reinitializeToken` keeps the ledger
and identity and keeps the version nonzero. A ledger step keeps the identity, or takes the
fallback from a zero vault (`legacy_step_config`). The run statements are inductions that carry
"the starting identity, or the fallback's". The ledger and counting results are the
`Reinitialization` proofs again, with `LegacyStep`'s ledger lemma (`legacy_reachable_ledger`) in
place of `Step`'s; the prologue writes neither the ledger nor the version.
-/

namespace Contracts.BridgedStandardERC20

/-! ## The two non-ledger calls, unfolded -/

private theorem faithful_init_view {s t : TokenStorage} {caller : Address}
    {assetId : UInt256} {originToken : Address} {decoded : Option Metadata}
    (h : initializeStorage s caller assetId originToken decoded = some t) :
    ∃ m i, decoded = some m ∧ initializeToken s.init caller assetId originToken true = some i ∧
      t = ⟨i.token, i.version, m⟩ := by
  unfold initializeStorage at h
  split at h
  · cases h
  · rename_i m
    split at h
    · cases h
    · rename_i i hi
      exact ⟨m, i, rfl, hi, (Option.some.inj h).symm⟩

private theorem faithful_initializeToken_version {s t : InitState} {caller : Address}
    {assetId : UInt256} {originToken : Address} {decoded : Bool}
    (h : initializeToken s caller assetId originToken decoded = some t) : s.version = 0 := by
  unfold initializeToken at h
  split at h
  · rename_i hg
    exact hg.1.1
  · cases h

private theorem faithful_init_closed {s : TokenStorage} (hv : s.version ≠ 0)
    (caller : Address) (assetId : UInt256) (originToken : Address) (decoded : Option Metadata) :
    initializeStorage s caller assetId originToken decoded = none := by
  cases h : initializeStorage s caller assetId originToken decoded with
  | none => rfl
  | some t =>
    obtain ⟨_, _, _, hi, _⟩ := faithful_init_view h
    exact absurd (faithful_initializeToken_version hi) hv

/-- A successful `bridgeInitialize` on a fresh proxy, with its result spelled out. -/
private theorem faithful_fresh_init {caller : Address} {assetId : UInt256}
    {originToken : Address} (ho : originToken ≠ 0) (m : Metadata) :
    initializeStorage freshStorage caller assetId originToken (some m) =
      some ⟨empty ⟨caller, originToken, assetId⟩, 1, m⟩ := by
  have hi : initializeToken freshStorage.init caller assetId originToken true =
      some ⟨empty ⟨caller, originToken, assetId⟩, 1⟩ := by
    unfold initializeToken
    rw [ite_eq_left ⟨⟨rfl, ho⟩, rfl⟩]
    rfl
  unfold initializeStorage
  rw [hi]

private theorem faithful_reinit_view {beaconOwner : Option Address} {s t : TokenStorage}
    {caller : Address} {getters : Getters} {name symbol : Text} {version : UInt8}
    (h : reinitializeToken beaconOwner s caller getters name symbol version = some t) :
    t.token = s.token ∧ t.version.toNat = s.version.toNat + 1 := by
  have he := ReinitExactEffect beaconOwner s caller getters name symbol version t h
  refine ⟨by rw [he], ?_⟩
  exact (ReinitVersionIncreasesByOne beaconOwner s caller getters name symbol version t h).2

private theorem faithful_version_ne_zero {a b : UInt8} (hn : b.toNat = a.toNat + 1) :
    b ≠ 0 := by
  intro h0
  rw [h0] at hn
  have : (0 : UInt8).toNat = 0 := rfl
  omega

private theorem faithful_empty_wellFormed (c : Config) : WellFormed (empty c) :=
  ⟨Finset.sum_const_zero, by norm_num [empty, UInt256.size], rfl⟩

/-! ## One step -/

/-- From a nonzero version a step keeps the identity, or takes the fallback from a zero vault,
and keeps the version nonzero. -/
private theorem faithful_step_config {env : LegacyEnv} {u w : TokenStorage}
    (h : LegacyStorageStep env u w) (hv : u.version ≠ 0) :
    (w.token.config = u.token.config ∨
      (u.token.config.vault = 0 ∧ w.token.config = fallbackConfig env u.token.config)) ∧
    w.version ≠ 0 := by
  cases h with
  | bridgeInitialize h' =>
    rw [faithful_init_closed hv] at h'
    cases h'
  | reinitialize h' =>
    obtain ⟨htok, hn⟩ := faithful_reinit_view h'
    exact ⟨Or.inl (by rw [htok]), faithful_version_ne_zero hn⟩
  | ledger h' =>
    exact ⟨legacy_step_config env h', hv⟩

/-- Every step keeps `WellFormed`, and none lowers the version. -/
private theorem faithful_step_ledger {env : LegacyEnv} {u w : TokenStorage}
    (hw : WellFormed u.token) (h : LegacyStorageStep env u w) :
    WellFormed w.token ∧ u.version.toNat ≤ w.version.toNat := by
  cases h with
  | bridgeInitialize h' =>
    obtain ⟨m, i, _, hi, rfl⟩ := faithful_init_view h'
    have h0 : u.version = 0 := faithful_initializeToken_version hi
    have hw' : WellFormed u.init.token := hw
    refine ⟨initialization_preserves_ledger (s := u.init) hw' hi, ?_⟩
    show u.version.toNat ≤ i.version.toNat
    rw [h0]
    exact Nat.zero_le _
  | reinitialize h' =>
    obtain ⟨htok, hn⟩ := faithful_reinit_view h'
    refine ⟨?_, by omega⟩
    rw [htok]
    exact hw
  | ledger h' =>
    exact ⟨(legacy_reachable_ledger env hw (LegacyReach.tail LegacyReach.refl h')).1, le_rfl⟩

/-- A `StorageStep` is a step of the token. -/
private theorem faithful_storageStep {u w : TokenStorage} (env : LegacyEnv)
    (h : StorageStep u w) : LegacyStorageStep env u w := by
  cases h with
  | bridgeInitialize h' => exact LegacyStorageStep.bridgeInitialize h'
  | reinitialize h' => exact LegacyStorageStep.reinitialize h'
  | ledger h' => exact LegacyStorageStep.ledger (step_legacyStep env h')

/-- From a nonzero vault, a step of the token is a `StorageStep`. -/
private theorem faithful_step_of_vault_ne {env : LegacyEnv} {u w : TokenStorage}
    (h : LegacyStorageStep env u w) (hvault : u.token.config.vault ≠ 0) : StorageStep u w := by
  cases h with
  | bridgeInitialize h' => exact StorageStep.bridgeInitialize h'
  | reinitialize h' => exact StorageStep.reinitialize h'
  | ledger h' => exact StorageStep.ledger (legacyStep_step_of_vault_ne hvault h')

private theorem faithful_vault_ne_of_config {a b : TokenStorage}
    (hc : a.token.config = b.token.config) (hb : b.token.config.vault ≠ 0) :
    a.token.config.vault ≠ 0 := by
  rw [hc]
  exact hb

/-! ## The refinement -/

theorem StorageReachIsLegacyStorageReach : Properties.StorageReachIsLegacyStorageReach := by
  intro env s t h
  induction h with
  | refl => exact LegacyStorageReach.refl
  | tail _ hstep ih => exact LegacyStorageReach.tail ih (faithful_storageStep env hstep)

private theorem faithful_callStep (env : LegacyEnv) {s t : TokenStorage} {c : StorageCall}
    (h : StorageCallStep s c t) : LegacyStorageCallStep env s c t := by
  cases h with
  | bridgeInitialize h' => exact LegacyStorageCallStep.bridgeInitialize h'
  | reinitialize h' => exact LegacyStorageCallStep.reinitialize h'
  | ledger h' => exact LegacyStorageCallStep.ledger (step_legacyStep env h')

theorem StorageRunIsLegacyStorageRun : Properties.StorageRunIsLegacyStorageRun := by
  intro env s calls t h
  induction h with
  | nil => exact LegacyStorageRun.nil
  | cons hstep _ ih => exact LegacyStorageRun.cons (faithful_callStep env hstep) ih

theorem InitializedNonlegacyRunsAgree : Properties.InitializedNonlegacyRunsAgree := by
  intro env s t hv hvault
  refine ⟨fun h => ?_, StorageReachIsLegacyStorageReach env s t⟩
  have key : StorageReach s t ∧ t.token.config = s.token.config ∧ t.version ≠ 0 := by
    induction h with
    | refl => exact ⟨StorageReach.refl, rfl, hv⟩
    | tail _ hstep ih =>
      obtain ⟨hr, hc, hvu⟩ := ih
      have hvault' := faithful_vault_ne_of_config hc hvault
      obtain ⟨hcs, hvw⟩ := faithful_step_config hstep hvu
      refine ⟨StorageReach.tail hr (faithful_step_of_vault_ne hstep hvault'), ?_, hvw⟩
      rcases hcs with hcs | ⟨hz, _⟩
      · exact hcs.trans hc
      · exact absurd hz hvault'
  exact key.1

/-! ## `InitializedIdentityIsFixed`, read on the token -/

theorem LegacyBridgeCallRewritesIdentity : Properties.LegacyBridgeCallRewritesIdentity := by
  intro env s recipient amount hl hr hs
  have hmint := legacy_bridge_mint_enabled env (s := s.token) (amount := amount) hl hr hs
  refine ⟨_, LegacyStorageStep.ledger (s := s) (LegacyStep.bridgeMint hmint), rfl, rfl, rfl,
    rfl, ?_⟩
  intro heq
  have hv : (fallbackConfig env s.token.config).vault = s.token.config.vault :=
    congrArg Config.vault heq
  rw [hl] at hv
  exact fallbackConfig_vault_ne env s.token.config hv

theorem InitializedIdentityIsFixedFailsOnLegacyTokens :
    Properties.InitializedIdentityIsFixedFailsOnLegacyTokens := by
  intro env hall
  let s : TokenStorage := { freshStorage with version := 1 }
  obtain ⟨t, hstep, _, _, _, _, hne⟩ :=
    LegacyBridgeCallRewritesIdentity env s 1 0 rfl (by decide) (by decide)
  exact hne (hall s t (by decide) (LegacyStorageReach.tail LegacyStorageReach.refl hstep)).1

/-! ## What holds instead -/

theorem InitializedIdentityFixedOrFallback : Properties.InitializedIdentityFixedOrFallback := by
  intro env s t hv h
  induction h with
  | refl => exact ⟨Or.inl rfl, hv⟩
  | tail _ hstep ih =>
    obtain ⟨hc, hvu⟩ := ih
    obtain ⟨hcs, hvw⟩ := faithful_step_config hstep hvu
    refine ⟨?_, hvw⟩
    rcases hcs with hcs | ⟨hz, hcs⟩
    · rw [hcs]
      exact hc
    · rcases hc with hc | ⟨_, hc⟩
      · rw [hc] at hz hcs
        exact Or.inr ⟨hz, hcs⟩
      · rw [hc] at hz
        exact absurd hz (fallbackConfig_vault_ne env _)

theorem InitializedNonlegacyIdentityIsFixed : Properties.InitializedNonlegacyIdentityIsFixed := by
  intro env s t hv hvault h
  obtain ⟨hc, hvt⟩ := InitializedIdentityFixedOrFallback env s t hv h
  rcases hc with hc | ⟨hz, _⟩
  · exact ⟨hc, hvt⟩
  · exact absurd hz hvault

theorem InitializedOriginTokenIsFixed : Properties.InitializedOriginTokenIsFixed := by
  intro env s t hv h
  rcases (InitializedIdentityFixedOrFallback env s t hv h).1 with hc | ⟨_, hc⟩
  · exact congrArg Config.originToken hc
  · exact (congrArg Config.originToken hc).trans rfl

/-! ## The other results about runs -/

theorem LegacyStorageRunsPreserveLedger : Properties.LegacyStorageRunsPreserveLedger := by
  intro env s t hw h
  induction h with
  | refl => exact ⟨hw, le_rfl⟩
  | tail _ hstep ih =>
    obtain ⟨hwt, hle⟩ := ih
    obtain ⟨hwu, hle'⟩ := faithful_step_ledger hwt hstep
    exact ⟨hwu, hle.trans hle'⟩

theorem FreshProxyLifecycleNonzeroCaller : Properties.FreshProxyLifecycleNonzeroCaller := by
  intro env caller assetId originToken metadata s t hc hi hr
  obtain ⟨m, i, _, hinit, rfl⟩ := faithful_init_view hi
  obtain ⟨hvault, hasset, horigin, _, hversion⟩ := initialization_binds_inputs hinit
  have hw0 : WellFormed freshStorage.init.token := faithful_empty_wellFormed ⟨0, 0, 0⟩
  have hw1 : WellFormed i.token :=
    initialization_preserves_ledger (s := freshStorage.init) hw0 hinit
  have hv1 : (⟨i.token, i.version, m⟩ : TokenStorage).version ≠ 0 := by
    show i.version ≠ 0
    rw [hversion]
    decide
  have hvault1 : (⟨i.token, i.version, m⟩ : TokenStorage).token.config.vault ≠ 0 := by
    show i.token.config.vault ≠ 0
    rw [hvault]
    exact hc
  obtain ⟨hcfg, hv⟩ := InitializedNonlegacyIdentityIsFixed env _ t hv1 hvault1 hr
  refine ⟨?_, (LegacyStorageRunsPreserveLedger env ⟨i.token, i.version, m⟩ t hw1 hr).1,
    faithful_init_closed hv⟩
  rw [hcfg]
  show i.token.config = _
  rw [← hvault, ← hasset, ← horigin]

theorem ZeroCallerInitializationTakesFallback :
    Properties.ZeroCallerInitializationTakesFallback := by
  intro env assetId originToken metadata ho
  have hinit := faithful_fresh_init (caller := 0) (assetId := assetId) ho metadata
  let s : TokenStorage := ⟨empty ⟨0, originToken, assetId⟩, 1, metadata⟩
  have hsup : s.token.totalSupply + (1 : UInt256).val < UInt256.size := by
    show (0 : ℕ) + (1 : UInt256).val < UInt256.size
    decide
  obtain ⟨t, hstep, _, _, htok, hcfg, hne⟩ :=
    LegacyBridgeCallRewritesIdentity env s 4 1 rfl (by decide) hsup
  have hw : WellFormed s.token := faithful_empty_wellFormed _
  refine ⟨s, t, hinit, hstep, hcfg, hne, ?_, (faithful_step_ledger hw hstep).1⟩
  rw [htok]
  rfl

theorem ReinitializedFreshProxyTakesFallback :
    Properties.ReinitializedFreshProxyTakesFallback := by
  intro env owner getters name symbol
  obtain ⟨t, ht⟩ :=
    (ReinitSucceedsIff (some owner) freshStorage owner getters name symbol 1).mpr ⟨rfl, rfl⟩
  have he := ReinitExactEffect _ _ _ _ _ _ _ _ ht
  subst he
  refine ⟨_, ht, ?_, ?_⟩
  · intro u hu
    obtain ⟨hc, hvu⟩ := InitializedIdentityFixedOrFallback env _ u
      (by show (1 : UInt8) ≠ 0; decide) hu
    refine ⟨?_, faithful_init_closed hvu⟩
    rcases hc with hc | ⟨_, hc⟩
    · exact Or.inl hc
    · exact Or.inr hc
  · obtain ⟨u, hstep, _, _, htok, hcfg, _⟩ :=
      LegacyBridgeCallRewritesIdentity env
        ⟨freshStorage.token, 1, reinitMetadata freshStorage.metadata getters name symbol⟩
        4 1 rfl (by decide) (by show (0 : ℕ) + (1 : UInt256).val < UInt256.size; decide)
    refine ⟨u, hstep, hcfg, ?_⟩
    rw [htok]
    rfl

/-! ## Counting calls on the token's runs -/

private theorem faithful_callStep_step {env : LegacyEnv} {s t : TokenStorage} {c : StorageCall}
    (h : LegacyStorageCallStep env s c t) : LegacyStorageStep env s t := by
  cases h with
  | bridgeInitialize h' => exact LegacyStorageStep.bridgeInitialize h'
  | reinitialize h' => exact LegacyStorageStep.reinitialize h'
  | ledger h' => exact LegacyStorageStep.ledger h'

private theorem faithful_step_callStep {env : LegacyEnv} {s t : TokenStorage}
    (h : LegacyStorageStep env s t) : ∃ c, LegacyStorageCallStep env s c t := by
  cases h with
  | bridgeInitialize h' => exact ⟨_, LegacyStorageCallStep.bridgeInitialize h'⟩
  | reinitialize h' => exact ⟨_, LegacyStorageCallStep.reinitialize h'⟩
  | ledger h' => exact ⟨_, LegacyStorageCallStep.ledger h'⟩

private theorem faithful_run_snoc {env : LegacyEnv} {s t u : TokenStorage}
    {calls : List StorageCall} {c : StorageCall} (h : LegacyStorageRun env s calls t)
    (hs : LegacyStorageCallStep env t c u) : LegacyStorageRun env s (calls ++ [c]) u := by
  induction h with
  | nil => exact LegacyStorageRun.cons hs LegacyStorageRun.nil
  | cons hstep _ ih => exact LegacyStorageRun.cons hstep (ih hs)

private theorem faithful_reach_cons {env : LegacyEnv} {s t u : TokenStorage}
    (hs : LegacyStorageStep env s t) (h : LegacyStorageReach env t u) :
    LegacyStorageReach env s u := by
  induction h with
  | refl => exact LegacyStorageReach.tail LegacyStorageReach.refl hs
  | tail _ hstep ih => exact LegacyStorageReach.tail ih hstep

theorem LegacyStorageRunsAreReach : Properties.LegacyStorageRunsAreReach := by
  intro env s t
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], LegacyStorageRun.nil⟩
    | tail _ hstep ih =>
      obtain ⟨calls, hrun⟩ := ih
      obtain ⟨c, hc⟩ := faithful_step_callStep hstep
      exact ⟨calls ++ [c], faithful_run_snoc hrun hc⟩
  · rintro ⟨calls, h⟩
    induction h with
    | nil => exact LegacyStorageReach.refl
    | cons hstep _ ih => exact faithful_reach_cons (faithful_callStep_step hstep) ih

private theorem faithful_versionCalls_cons (c : StorageCall) (calls : List StorageCall) :
    versionCalls (c :: calls) = versionCalls [c] + versionCalls calls := by
  cases c <;> simp only [versionCalls] <;> omega

private theorem faithful_callStep_version {env : LegacyEnv} {s t : TokenStorage}
    {c : StorageCall} (h : LegacyStorageCallStep env s c t) :
    t.version.toNat = s.version.toNat + versionCalls [c] := by
  cases h with
  | bridgeInitialize h' =>
    obtain ⟨m, i, _, hi, rfl⟩ := faithful_init_view h'
    have h0 : s.version = 0 := faithful_initializeToken_version hi
    have h1 : i.version = 1 := (initialization_binds_inputs hi).2.2.2.2
    show i.version.toNat = s.version.toNat + 1
    rw [h0, h1]
    rfl
  | reinitialize h' => exact (faithful_reinit_view h').2
  | ledger h' => rfl

theorem LegacyVersionCountsInitializations : Properties.LegacyVersionCountsInitializations := by
  intro env s calls t h
  induction h with
  | nil => rfl
  | cons hstep _ ih =>
    rename_i call calls _
    rw [ih, faithful_callStep_version hstep, faithful_versionCalls_cons call calls]
    omega

theorem LegacyLifetimeVersionCallBound : Properties.LegacyLifetimeVersionCallBound := by
  intro env calls t h
  have hc := LegacyVersionCountsInitializations env freshStorage calls t h
  have hlt : t.version.toNat < 256 := t.version.toNat_lt_size
  have h0 : freshStorage.version.toNat = 0 := rfl
  omega

theorem LegacyLifetimeBoundIsTight : Properties.LegacyLifetimeBoundIsTight := by
  intro env
  obtain ⟨calls, t, hrun, h1, h2, h3⟩ := LifetimeBoundIsTight
  exact ⟨calls, t, StorageRunIsLegacyStorageRun env _ _ _ hrun, h1, h2, h3⟩

theorem LegacyBridgeInitializeAtMostOnce : Properties.LegacyBridgeInitializeAtMostOnce := by
  intro env s calls t h
  induction h with
  | nil => exact ⟨Nat.zero_le _, fun _ => rfl⟩
  | cons hstep _ ih =>
    obtain ⟨ih1, ih2⟩ := ih
    cases hstep with
    | bridgeInitialize h' =>
      obtain ⟨m, i, _, hi, rfl⟩ := faithful_init_view h'
      have h0 := faithful_initializeToken_version hi
      have h1 : i.version = 1 := (initialization_binds_inputs hi).2.2.2.2
      have hz := ih2 (by show i.version ≠ 0; rw [h1]; decide)
      refine ⟨?_, fun hne => absurd h0 hne⟩
      simp only [initializeCalls]
      omega
    | reinitialize h' =>
      obtain ⟨_, hn⟩ := faithful_reinit_view h'
      have hz := ih2 (faithful_version_ne_zero hn)
      simp only [initializeCalls]
      exact ⟨ih1, fun _ => hz⟩
    | ledger h' =>
      simp only [initializeCalls]
      exact ⟨ih1, ih2⟩

/-! ## Witness -/

theorem LegacyStorageWitness : Properties.LegacyStorageWitness := by
  intro env
  have h1 : (1 : UInt256).val = 1 := rfl
  constructor
  · -- the nonlegacy branch: initialize, mint, reinitialize
    let c : Config := ⟨1, 9, 5⟩
    have hinit := faithful_fresh_init (caller := 1) (assetId := 5) (originToken := 9)
      (by decide) emptyMetadata
    obtain ⟨hw, funded, hmint, _, _⟩ := one_unit_roundtrip c 4 (by decide) (by decide)
    obtain ⟨_, _, _, hsup, _, hcfg⟩ := mint_exact hmint
    have hstep₁ : LegacyStorageStep env ⟨empty c, 1, emptyMetadata⟩ ⟨funded, 1, emptyMetadata⟩ :=
      LegacyStorageStep.ledger (s := ⟨empty c, 1, emptyMetadata⟩)
        (LegacyStep.bridgeMint (bridgeMint_of_mint env hmint))
    obtain ⟨t, ht⟩ := (ReinitSucceedsIff (some 7) ⟨funded, 1, emptyMetadata⟩ 7
      ⟨false, false, false⟩ [0x42] [0x43] 2).mpr ⟨rfl, rfl⟩
    have he := ReinitExactEffect _ _ _ _ _ _ _ _ ht
    subst he
    refine ⟨_, _, hinit, by decide, by decide, hw,
      LegacyStorageReach.tail (LegacyStorageReach.tail LegacyStorageReach.refl hstep₁)
        (LegacyStorageStep.reinitialize ht), rfl, ?_, hcfg⟩
    show funded.totalSupply = 1
    rw [hsup, h1]
    rfl
  · -- the legacy branch: a funded legacy token, the L2 vault's burn, then a reinitialization
    let s : TokenStorage :=
      ⟨⟨⟨0, 9, 0⟩, Function.update (fun _ => 0) 4 1, 1⟩, 1, emptyMetadata⟩
    have hw : WellFormed s.token := by
      refine ⟨?_, ?_, ?_⟩
      · simp [s, Function.update_apply]
      · norm_num [s, UInt256.size]
      · show Function.update (fun _ => 0) (4 : Address) 1 0 = 0
        rw [Function.update_of_ne (by decide)]
    have hl : s.token.config.vault = 0 := rfl
    have hbal : s.token.balances 4 = 1 := by
      show Function.update (fun _ => 0) (4 : Address) 1 4 = 1
      exact Function.update_self _ _ _
    have hburn := legacy_bridge_burn_enabled env (s := s.token) (owner := 4) (amount := 1) hl
      (by decide) (by rw [hbal, h1])
    let u : TokenStorage :=
      { s with token :=
          burnEffect { s.token with config := fallbackConfig env s.token.config } 4 1 }
    have hstep₁ : LegacyStorageStep env s u :=
      LegacyStorageStep.ledger (s := s) (LegacyStep.bridgeBurn hburn)
    obtain ⟨t, ht⟩ := (ReinitSucceedsIff (some 7) u 7 ⟨false, false, false⟩ [] [] 2).mpr
      ⟨rfl, rfl⟩
    have he := ReinitExactEffect _ _ _ _ _ _ _ _ ht
    subst he
    refine ⟨s, u, _, hw, rfl, rfl, hbal, by decide, (original_model_rejects_legacy hl _ _ _).2,
      hstep₁, rfl, ?_, LegacyStorageStep.reinitialize ht,
      LegacyStorageReach.tail (LegacyStorageReach.tail LegacyStorageReach.refl hstep₁)
        (LegacyStorageStep.reinitialize ht), rfl, rfl, ?_⟩
    · show (1 : ℕ) - (1 : UInt256).val = 0
      rw [h1]
    · intro heq
      have hv : (fallbackConfig env s.token.config).vault = s.token.config.vault :=
        congrArg Config.vault heq
      rw [hl] at hv
      exact fallbackConfig_vault_ne env s.token.config hv

end Contracts.BridgedStandardERC20
