import EraSpec.Contracts.BridgedStandardERC20.Properties.Reinitialization
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Model
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Initialization

namespace Contracts.BridgedStandardERC20

/-! ## The call, unfolded -/

private theorem reinit_allowed {beaconOwner : Option Address} {s : TokenStorage}
    {caller : Address} {getters : Getters} {name symbol : Text} {version : UInt8}
    {t : TokenStorage}
    (h : reinitializeToken beaconOwner s caller getters name symbol version = some t) :
    ReinitAllowed beaconOwner s caller version ∧
      t = ⟨s.token, version, reinitMetadata s.metadata getters name symbol⟩ := by
  unfold reinitializeToken at h
  split at h
  · rename_i hg
    exact ⟨hg, (Option.some.inj h).symm⟩
  · cases h

private theorem reinit_of_allowed {beaconOwner : Option Address} {s : TokenStorage}
    {caller : Address} {getters : Getters} {name symbol : Text} {version : UInt8}
    (h : ReinitAllowed beaconOwner s caller version) :
    reinitializeToken beaconOwner s caller getters name symbol version =
      some ⟨s.token, version, reinitMetadata s.metadata getters name symbol⟩ := by
  unfold reinitializeToken
  rw [ite_eq_left h]

private theorem allowed_iff {beaconOwner : Option Address} {s : TokenStorage} {caller : Address}
    {version : UInt8} :
    ReinitAllowed beaconOwner s caller version ↔
      version.toNat = s.version.toNat + 1 ∧ beaconOwner = some caller := by
  unfold ReinitAllowed NextVersion ReinitializerAllowed
  rw [UInt8.lt_iff_toNat_lt]
  constructor
  · rintro ⟨h1, _, h3⟩
    exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    exact ⟨h1, by omega, h3⟩

/-- A successful call, unfolded to its version and owner guards and its effect. -/
private theorem reinit_view {beaconOwner : Option Address} {s : TokenStorage} {caller : Address}
    {getters : Getters} {name symbol : Text} {version : UInt8} {t : TokenStorage}
    (h : reinitializeToken beaconOwner s caller getters name symbol version = some t) :
    version.toNat = s.version.toNat + 1 ∧ beaconOwner = some caller ∧
      t = ⟨s.token, version, reinitMetadata s.metadata getters name symbol⟩ := by
  obtain ⟨hg, ht⟩ := reinit_allowed h
  obtain ⟨hn, ho⟩ := allowed_iff.mp hg
  exact ⟨hn, ho, ht⟩

private theorem reinit_none_of_not_allowed {beaconOwner : Option Address} {s : TokenStorage}
    {caller : Address} {getters : Getters} {name symbol : Text} {version : UInt8}
    (h : ¬ ReinitAllowed beaconOwner s caller version) :
    reinitializeToken beaconOwner s caller getters name symbol version = none := by
  unfold reinitializeToken
  rw [ite_eq_right h]

private theorem version_ne_zero_of_next {s : TokenStorage} {version : UInt8}
    (hn : version.toNat = s.version.toNat + 1) : version ≠ 0 := by
  intro h0
  rw [h0] at hn
  have : (0 : UInt8).toNat = 0 := rfl
  omega

/-! ## `bridgeInitialize` on the full storage, unfolded -/

private theorem initializeStorage_view {s t : TokenStorage} {caller : Address}
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

private theorem initializeToken_version {s t : InitState} {caller : Address} {assetId : UInt256}
    {originToken : Address} {decoded : Bool}
    (h : initializeToken s caller assetId originToken decoded = some t) : s.version = 0 := by
  unfold initializeToken at h
  split at h
  · rename_i hg
    exact hg.1.1
  · cases h

private theorem initializeStorage_closed {s : TokenStorage} (hv : s.version ≠ 0)
    (caller : Address) (assetId : UInt256) (originToken : Address) (decoded : Option Metadata) :
    initializeStorage s caller assetId originToken decoded = none := by
  cases h : initializeStorage s caller assetId originToken decoded with
  | none => rfl
  | some t =>
    obtain ⟨_, _, _, hi, _⟩ := initializeStorage_view h
    exact absurd (initializeToken_version hi) hv

private theorem empty_wellFormed (c : Config) : WellFormed (empty c) :=
  ⟨Finset.sum_const_zero, by norm_num [empty, UInt256.size], rfl⟩

/-- The witnesses' `bridgeInitialize`: vault `1`, asset `5`, origin token `9`. -/
private theorem fresh_init_witness :
    initializeStorage freshStorage 1 5 9 (some emptyMetadata) =
      some ⟨empty ⟨1, 9, 5⟩, 1, emptyMetadata⟩ := by
  have hi : initializeToken freshStorage.init 1 5 9 true = some ⟨empty ⟨1, 9, 5⟩, 1⟩ := by
    unfold initializeToken
    rw [ite_eq_left ⟨⟨rfl, by decide⟩, rfl⟩]
    rfl
  unfold initializeStorage
  rw [hi]

/-- Every ledger step keeps the identity, with no ledger premise. -/
private theorem step_config {a b : State} (h : Step a b) : b.config = a.config := by
  cases h with
  | burn h =>
    unfold burn at h
    split at h
    · cases h
      rfl
    · cases h
  | mint h =>
    unfold mint at h
    split at h
    · cases h
      rfl
    · cases h
  | transfer h =>
    unfold transfer at h
    split at h
    · cases h
      rfl
    · cases h

/-! ## One call -/

theorem ReinitSucceedsIff : Properties.ReinitSucceedsIff := by
  intro beaconOwner s caller getters name symbol version
  constructor
  · rintro ⟨t, h⟩
    exact allowed_iff.mp (reinit_allowed h).1
  · intro h
    exact ⟨_, reinit_of_allowed (allowed_iff.mpr h)⟩

theorem ReinitExactEffect : Properties.ReinitExactEffect := by
  intro beaconOwner s caller getters name symbol version t h
  exact (reinit_view h).2.2

theorem ReinitKeepsLedgerAndIdentity : Properties.ReinitKeepsLedgerAndIdentity := by
  intro beaconOwner s caller getters name symbol version t h
  obtain ⟨_, _, rfl⟩ := reinit_view h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem ReinitPreservesWellFormed : Properties.ReinitPreservesWellFormed := by
  intro beaconOwner s caller getters name symbol version t hw h
  obtain ⟨_, _, rfl⟩ := reinit_view h
  exact hw

theorem ReinitLeavesLedgerCallsUnchanged : Properties.ReinitLeavesLedgerCallsUnchanged := by
  intro beaconOwner s caller getters name symbol version t h who account other amount
  obtain ⟨_, _, rfl⟩ := reinit_view h
  exact ⟨rfl, rfl, rfl⟩

theorem ReinitIndependentOfLedger : Properties.ReinitIndependentOfLedger := by
  intro beaconOwner s caller getters name symbol version token
  by_cases h : ReinitAllowed beaconOwner s caller version
  · have h' : ReinitAllowed beaconOwner { s with token := token } caller version := h
    rw [reinit_of_allowed h', reinit_of_allowed h]
    rfl
  · have h' : ¬ ReinitAllowed beaconOwner { s with token := token } caller version := h
    rw [reinit_none_of_not_allowed h', reinit_none_of_not_allowed h]
    rfl

theorem ReinitVersionIncreasesByOne : Properties.ReinitVersionIncreasesByOne := by
  intro beaconOwner s caller getters name symbol version t h
  obtain ⟨hn, _, rfl⟩ := reinit_view h
  exact ⟨UInt8.lt_iff_toNat_lt.mpr (by dsimp only; omega), hn⟩

theorem VersionJumpHasNoStep : Properties.VersionJumpHasNoStep := by
  intro beaconOwner s caller getters name symbol version hv
  apply reinit_none_of_not_allowed
  intro h
  exact hv (allowed_iff.mp h).1

theorem OnlyTheBeaconOwnerReinitializes : Properties.OnlyTheBeaconOwnerReinitializes := by
  intro beaconOwner s caller getters name symbol version ho
  apply reinit_none_of_not_allowed
  intro h
  exact ho (allowed_iff.mp h).2

theorem ReinitVersionIsSpent : Properties.ReinitVersionIsSpent := by
  intro beaconOwner s caller getters name symbol version t h beaconOwner' caller' getters'
    name' symbol'
  obtain ⟨_, _, rfl⟩ := reinit_view h
  apply VersionJumpHasNoStep
  dsimp only
  omega

theorem ReinitKeepsInitializationClosed : Properties.ReinitKeepsInitializationClosed := by
  intro beaconOwner s caller getters name symbol version t h caller' assetId originToken decoded
  obtain ⟨hn, _, rfl⟩ := reinit_view h
  exact initializeStorage_closed (version_ne_zero_of_next hn) caller' assetId originToken decoded

theorem ImplementationNeverReinitialized : Properties.ImplementationNeverReinitialized := by
  intro beaconOwner caller getters name symbol version
  apply VersionJumpHasNoStep
  have hlt : version.toNat < 256 := version.toNat_lt_size
  have h255 : disabledStorage.version.toNat = 255 := rfl
  omega

theorem OnlyTheStepFrom254DisablesReinitialization :
    Properties.OnlyTheStepFrom254DisablesReinitialization := by
  intro beaconOwner s caller getters name symbol version t h
  obtain ⟨hn, _, rfl⟩ := reinit_view h
  have hlt : version.toNat < 256 := version.toNat_lt_size
  constructor
  · intro hnone
    by_contra h254
    have hs : s.version.toNat ≠ 254 := by
      intro h'
      apply h254
      apply UInt8.toNat_inj.mp
      rw [h']
      rfl
    have hnext : (version + 1).toNat = version.toNat + 1 := by
      rw [UInt8.toNat_add]
      have h1 : (1 : UInt8).toNat = 1 := rfl
      rw [h1]
      exact Nat.mod_eq_of_lt (by omega)
    have hstep := hnone (some 0) 0 getters name symbol (version + 1)
    rw [reinit_of_allowed (allowed_iff.mpr ⟨hnext, rfl⟩)] at hstep
    cases hstep
  · intro h254 beaconOwner' caller' getters' name' symbol' version'
    apply VersionJumpHasNoStep
    have hlt' : version'.toNat < 256 := version'.toNat_lt_size
    have hs : s.version.toNat = 254 := by
      rw [h254]
      rfl
    dsimp only
    omega

theorem WithoutNextVersionAJumpDisablesReinitialization :
    Properties.WithoutNextVersionAJumpDisablesReinitialization := by
  let s : TokenStorage := { freshStorage with version := 1 }
  have hj : reinitializeWithoutNextVersion (some 7) s 7 ⟨false, false, false⟩ [] [] 255 =
      some ⟨s.token, 255, reinitMetadata s.metadata ⟨false, false, false⟩ [] []⟩ := by
    unfold reinitializeWithoutNextVersion
    rw [ite_eq_left ⟨show (1 : UInt8) < 255 by decide, rfl⟩]
  refine ⟨s, _, rfl, hj, ?_, ?_⟩
  · intro beaconOwner caller getters name symbol version
    have hlt : version.toNat < 256 := version.toNat_lt_size
    have h255 : (255 : UInt8).toNat = 255 := rfl
    constructor
    · unfold reinitializeWithoutNextVersion
      rw [ite_eq_right]
      rintro ⟨h, _⟩
      have h' : (255 : UInt8).toNat < version.toNat := UInt8.lt_iff_toNat_lt.mp h
      omega
    · apply VersionJumpHasNoStep
      dsimp only
      omega
  · apply VersionJumpHasNoStep
    show (255 : UInt8).toNat ≠ (1 : UInt8).toNat + 1
    decide

/-! ## Runs -/

private theorem step_ledger {s t : TokenStorage} (hw : WellFormed s.token)
    (h : StorageStep s t) : WellFormed t.token ∧ s.version.toNat ≤ t.version.toNat := by
  cases h with
  | bridgeInitialize h =>
    obtain ⟨m, i, _, hi, rfl⟩ := initializeStorage_view h
    have h0 : s.version = 0 := initializeToken_version hi
    have hw' : WellFormed s.init.token := hw
    refine ⟨initialization_preserves_ledger (s := s.init) hw' hi, ?_⟩
    dsimp only
    rw [h0]
    exact Nat.zero_le _
  | reinitialize h =>
    obtain ⟨hn, _, rfl⟩ := reinit_view h
    exact ⟨hw, by dsimp only; omega⟩
  | ledger h =>
    exact ⟨(reachable_ledger hw (Reach.tail Reach.refl h)).1, le_rfl⟩

theorem RunsPreserveLedger : Properties.RunsPreserveLedger := by
  intro s t hw h
  induction h with
  | refl => exact ⟨hw, le_rfl⟩
  | tail _ hstep ih =>
    obtain ⟨hwt, hle⟩ := ih
    obtain ⟨hwu, hle'⟩ := step_ledger hwt hstep
    exact ⟨hwu, hle.trans hle'⟩

theorem InitializedIdentityIsFixed : Properties.InitializedIdentityIsFixed := by
  intro s t hv h
  induction h with
  | refl => exact ⟨rfl, hv⟩
  | tail _ hstep ih =>
    obtain ⟨hc, hv'⟩ := ih
    cases hstep with
    | bridgeInitialize h' =>
      rw [initializeStorage_closed hv'] at h'
      cases h'
    | reinitialize h' =>
      obtain ⟨hn, _, rfl⟩ := reinit_view h'
      exact ⟨hc, version_ne_zero_of_next hn⟩
    | ledger h' =>
      exact ⟨(step_config h').trans hc, hv'⟩

theorem FreshProxyLifecycle : Properties.FreshProxyLifecycle := by
  intro caller assetId originToken metadata s t hi hr
  obtain ⟨m, i, _, hinit, rfl⟩ := initializeStorage_view hi
  obtain ⟨hvault, hasset, horigin, _, hversion⟩ := initialization_binds_inputs hinit
  have hw0 : WellFormed freshStorage.init.token := empty_wellFormed ⟨0, 0, 0⟩
  have hw1 : WellFormed i.token := initialization_preserves_ledger (s := freshStorage.init) hw0 hinit
  have hv1 : (⟨i.token, i.version, m⟩ : TokenStorage).version ≠ 0 := by
    dsimp only
    rw [hversion]
    decide
  obtain ⟨hc, hv⟩ := InitializedIdentityIsFixed ⟨i.token, i.version, m⟩ t hv1 hr
  refine ⟨?_, (RunsPreserveLedger ⟨i.token, i.version, m⟩ t hw1 hr).1, initializeStorage_closed hv⟩
  rw [hc]
  dsimp only
  rw [← hvault, ← hasset, ← horigin]

/-! ## Counting calls -/

private theorem callStep_step {s t : TokenStorage} {c : StorageCall}
    (h : StorageCallStep s c t) : StorageStep s t := by
  cases h with
  | bridgeInitialize h => exact StorageStep.bridgeInitialize h
  | reinitialize h => exact StorageStep.reinitialize h
  | ledger h => exact StorageStep.ledger h

private theorem step_callStep {s t : TokenStorage} (h : StorageStep s t) :
    ∃ c, StorageCallStep s c t := by
  cases h with
  | bridgeInitialize h => exact ⟨_, StorageCallStep.bridgeInitialize h⟩
  | reinitialize h => exact ⟨_, StorageCallStep.reinitialize h⟩
  | ledger h => exact ⟨_, StorageCallStep.ledger h⟩

private theorem run_snoc {s t u : TokenStorage} {calls : List StorageCall} {c : StorageCall}
    (h : StorageRun s calls t) (hs : StorageCallStep t c u) : StorageRun s (calls ++ [c]) u := by
  induction h with
  | nil => exact StorageRun.cons hs StorageRun.nil
  | cons hstep _ ih => exact StorageRun.cons hstep (ih hs)

private theorem reach_cons {s t u : TokenStorage} (hs : StorageStep s t)
    (h : StorageReach t u) : StorageReach s u := by
  induction h with
  | refl => exact StorageReach.tail StorageReach.refl hs
  | tail _ hstep ih => exact StorageReach.tail ih hstep

theorem StorageRunsAreReach : Properties.StorageRunsAreReach := by
  intro s t
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], StorageRun.nil⟩
    | tail _ hstep ih =>
      obtain ⟨calls, hrun⟩ := ih
      obtain ⟨c, hc⟩ := step_callStep hstep
      exact ⟨calls ++ [c], run_snoc hrun hc⟩
  · rintro ⟨calls, h⟩
    induction h with
    | nil => exact StorageReach.refl
    | cons hstep _ ih => exact reach_cons (callStep_step hstep) ih

private theorem versionCalls_cons (c : StorageCall) (calls : List StorageCall) :
    versionCalls (c :: calls) = versionCalls [c] + versionCalls calls := by
  cases c <;> simp only [versionCalls] <;> omega

private theorem callStep_version {s t : TokenStorage} {c : StorageCall}
    (h : StorageCallStep s c t) : t.version.toNat = s.version.toNat + versionCalls [c] := by
  cases h with
  | bridgeInitialize h =>
    obtain ⟨m, i, _, hi, rfl⟩ := initializeStorage_view h
    have h0 : s.version = 0 := initializeToken_version hi
    have h1 : i.version = 1 := (initialization_binds_inputs hi).2.2.2.2
    show i.version.toNat = s.version.toNat + 1
    rw [h0, h1]
    rfl
  | reinitialize h =>
    obtain ⟨hn, _, rfl⟩ := reinit_view h
    exact hn
  | ledger h => rfl

theorem VersionCountsInitializations : Properties.VersionCountsInitializations := by
  intro s calls t h
  induction h with
  | nil => rfl
  | cons hstep _ ih =>
    rename_i call calls _
    rw [ih, callStep_version hstep, versionCalls_cons call calls]
    omega

theorem LifetimeVersionCallBound : Properties.LifetimeVersionCallBound := by
  intro calls t h
  have hc := VersionCountsInitializations freshStorage calls t h
  have hlt : t.version.toNat < 256 := t.version.toNat_lt_size
  have h0 : freshStorage.version.toNat = 0 := rfl
  omega

private theorem versionCalls_replicate (k : ℕ) :
    versionCalls (List.replicate k .reinitializeToken) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    simp only [versionCalls, ih]

private theorem initializeCalls_replicate (k : ℕ) :
    initializeCalls (List.replicate k .reinitializeToken) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    simp only [initializeCalls, ih]

/-- From any state, the next `k` versions can be reinitialized one after another, as long as they
stay within 255. -/
private theorem reinit_chain :
    ∀ (k : ℕ) (s : TokenStorage), s.version.toNat + k ≤ 255 →
      ∃ t, StorageRun s (List.replicate k .reinitializeToken) t ∧
        t.version.toNat = s.version.toNat + k
  | 0, s, _ => ⟨s, StorageRun.nil, rfl⟩
  | k + 1, s, hk => by
    have hnext : (s.version + 1).toNat = s.version.toNat + 1 := by
      rw [UInt8.toNat_add]
      have h1 : (1 : UInt8).toNat = 1 := rfl
      rw [h1]
      exact Nat.mod_eq_of_lt (by omega)
    have hstep := reinit_of_allowed (getters := ⟨false, false, false⟩) (name := [])
      (symbol := []) ((allowed_iff (s := s) (beaconOwner := some 0) (caller := 0)).mpr
        ⟨hnext, rfl⟩)
    obtain ⟨t, hrun, ht⟩ := reinit_chain k
      ⟨s.token, s.version + 1, reinitMetadata s.metadata ⟨false, false, false⟩ [] []⟩
      (by dsimp only; omega)
    refine ⟨t, StorageRun.cons (StorageCallStep.reinitialize hstep) hrun, ?_⟩
    rw [ht]
    dsimp only
    omega

theorem LifetimeBoundIsTight : Properties.LifetimeBoundIsTight := by
  obtain ⟨t, hrun, ht⟩ := reinit_chain 254 ⟨empty ⟨1, 9, 5⟩, 1, emptyMetadata⟩ (by decide)
  refine ⟨.bridgeInitialize :: List.replicate 254 .reinitializeToken, t,
    StorageRun.cons (StorageCallStep.bridgeInitialize fresh_init_witness) hrun, ?_, ?_, ?_⟩
  · simp only [initializeCalls, initializeCalls_replicate]
  · simp only [versionCalls, versionCalls_replicate]
  · apply UInt8.toNat_inj.mp
    rw [ht]
    rfl

theorem BridgeInitializeAtMostOnce : Properties.BridgeInitializeAtMostOnce := by
  intro s calls t h
  induction h with
  | nil => exact ⟨Nat.zero_le _, fun _ => rfl⟩
  | cons hstep _ ih =>
    obtain ⟨_, ih2⟩ := ih
    cases hstep with
    | bridgeInitialize h' =>
      obtain ⟨m, i, _, hi, rfl⟩ := initializeStorage_view h'
      have h0 := initializeToken_version hi
      have h1 : i.version = 1 := (initialization_binds_inputs hi).2.2.2.2
      have hz := ih2 (by dsimp only; rw [h1]; decide)
      refine ⟨?_, fun hne => absurd h0 hne⟩
      simp only [initializeCalls]
      omega
    | reinitialize h' =>
      obtain ⟨hn, _, rfl⟩ := reinit_view h'
      have hz := ih2 (version_ne_zero_of_next hn)
      simp only [initializeCalls]
      exact ⟨by omega, fun _ => hz⟩
    | ledger h' =>
      simp only [initializeCalls]
      exact ⟨by have := ih2; omega, ih2⟩

/-! ## Countermodel -/

theorem ReinitializeOnFreshProxyBlocksBridgeInitialize :
    Properties.ReinitializeOnFreshProxyBlocksBridgeInitialize := by
  intro owner getters name symbol
  have hallowed : ReinitAllowed (some owner) freshStorage owner 1 := allowed_iff.mpr ⟨rfl, rfl⟩
  refine ⟨_, reinit_of_allowed hallowed, ?_⟩
  intro u hu
  obtain ⟨hc, hv⟩ := InitializedIdentityIsFixed _ _ (show (1 : UInt8) ≠ 0 by decide) hu
  refine ⟨hc, initializeStorage_closed hv, ?_⟩
  intro who account amount
  have hvault : u.token.config.vault = 0 := by
    rw [hc]
    rfl
  constructor
  · unfold burn
    rw [ite_eq_right]
    rintro ⟨h, _⟩
    exact h hvault
  · unfold mint
    rw [ite_eq_right]
    rintro ⟨h, _⟩
    exact h hvault

/-! ## Witnesses -/

theorem ReinitWitness : Properties.ReinitWitness := by
  let c : Config := ⟨1, 9, 5⟩
  have hinit := fresh_init_witness
  obtain ⟨_, funded, hmint, hwf, hburn⟩ := one_unit_roundtrip c 4 (by decide) (by decide)
  have hsupply : funded.totalSupply = 1 := by
    obtain ⟨_, _, _, hs, _, _⟩ := mint_exact hmint
    rw [hs]
    rfl
  have hreach : StorageReach ⟨empty c, 1, emptyMetadata⟩ ⟨funded, 1, emptyMetadata⟩ :=
    StorageReach.tail StorageReach.refl (StorageStep.ledger (Step.mint hmint))
  have hre : ReinitAllowed (some 7) ⟨funded, 1, emptyMetadata⟩ 7 2 := allowed_iff.mpr ⟨rfl, rfl⟩
  refine ⟨_, _, _, hinit, hreach, hwf, hsupply, reinit_of_allowed hre,
    show ([0x42] : Text) ≠ [] from List.cons_ne_nil _ _, rfl, hburn, ?_⟩
  exact ⟨_, reinit_of_allowed (allowed_iff.mpr ⟨rfl, rfl⟩)⟩

theorem LastVersionWitness : Properties.LastVersionWitness := by
  let s : TokenStorage := { freshStorage with version := 254 }
  have hre : ReinitAllowed (some 7) s 7 255 := allowed_iff.mpr ⟨rfl, rfl⟩
  refine ⟨s, _, rfl, reinit_of_allowed hre, ?_⟩
  intro beaconOwner caller getters name symbol version
  apply VersionJumpHasNoStep
  have hlt : version.toNat < 256 := version.toNat_lt_size
  have h255 : (255 : UInt8).toNat = 255 := rfl
  dsimp only
  omega

end Contracts.BridgedStandardERC20
