import EraSpec.Contracts.BridgedStandardERC20.Properties.ReinitializationFaithful
import EraSpec.Contracts.BridgedStandardERC20.Proofs.ReinitializationStrong

/-!
# Proofs: counting the deployed token's calls

A labelled step is a `DeployedStorageStep` with its label, and back. The counting results are the
`Reinitialization` proofs again, one step at a time: a call on either `onlyNTV` branch, like a
transfer, keeps the version. The legacy-branch counts rest on one fact per step: a legacy call
starts on a zero vault slot and leaves a nonzero one, every other call but `bridgeInitialize`
keeps the vault slot, and from a nonzero version `bridgeInitialize` is closed and a nonzero vault
slot stays nonzero (`DeployedInitializedIdentityIsFixed`).
-/

namespace Contracts.BridgedStandardERC20

/-! ## The calls, unfolded -/

private theorem rf_one_ne_zero : (1 : UInt8) ≠ 0 := by decide

private theorem rf_initializeToken_view {s i : InitState} {caller : Address} {assetId : UInt256}
    {originToken : Address} {decoded : Bool}
    (h : initializeToken s caller assetId originToken decoded = some i) :
    s.version = 0 ∧ i = ⟨{ s.token with config := ⟨caller, originToken, assetId⟩ }, 1⟩ := by
  unfold initializeToken at h
  split at h
  · rename_i hg
    exact ⟨hg.1.1, (Option.some.inj h).symm⟩
  · cases h

private theorem rf_initializeStorage_view {s t : TokenStorage} {caller : Address}
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
      obtain ⟨h0, rfl⟩ := rf_initializeToken_view hi
      exact ⟨m, rfl, h0, (Option.some.inj h).symm⟩

/-- `bridgeInitialize` on storage at version 0, computed. -/
private theorem rf_initializeStorage_of_version_zero {s : TokenStorage} (hv : s.version = 0)
    {caller : Address} {assetId : UInt256} {originToken : Address} (ho : originToken ≠ 0)
    (m : Metadata) :
    initializeStorage s caller assetId originToken (some m) =
      some ⟨{ s.token with config := ⟨caller, originToken, assetId⟩ }, 1, m⟩ := by
  have hi : initializeToken s.init caller assetId originToken true =
      some ⟨{ s.token with config := ⟨caller, originToken, assetId⟩ }, 1⟩ := by
    unfold initializeToken
    rw [ite_eq_left ⟨⟨hv, ho⟩, rfl⟩]
    rfl
  unfold initializeStorage
  rw [hi]

private theorem rf_reinit_view {beaconOwner : Option Address} {s t : TokenStorage}
    {caller : Address} {getters : Getters} {name symbol : Text} {version : UInt8}
    (h : reinitializeToken beaconOwner s caller getters name symbol version = some t) :
    version.toNat = s.version.toNat + 1 ∧
      t = ⟨s.token, version, reinitMetadata s.metadata getters name symbol⟩ :=
  ⟨((ReinitSucceedsIff beaconOwner s caller getters name symbol version).mp ⟨t, h⟩).1,
    ReinitExactEffect beaconOwner s caller getters name symbol version t h⟩

private theorem rf_version_ne_zero_of_next {a b : UInt8} (hn : b.toNat = a.toNat + 1) :
    b ≠ 0 := by
  intro h0
  rw [h0] at hn
  have : (0 : UInt8).toNat = 0 := rfl
  omega

/-- A bridge call keeps the configuration from a nonzero vault slot and installs `fallbackConfig`
on a zero one. -/
private theorem rf_bridge_config {env : LegacyEnv} {s : TokenStorage} {token : State}
    (hc : token.config = (legacyFallback env s.token).config) :
    (s.token.config.vault = 0 ∧ token.config = fallbackConfig env s.token.config) ∨
    (s.token.config.vault ≠ 0 ∧ token.config = s.token.config) := by
  by_cases hv : s.token.config.vault = 0
  · rw [legacyFallback_of_vault_eq hv] at hc
    exact Or.inl ⟨hv, hc⟩
  · rw [legacyFallback_of_vault_ne hv] at hc
    exact Or.inr ⟨hv, hc⟩

/-! ## The labels, unfolded -/

private theorem rf_label_entryPoint (s : TokenStorage) :
    (deployedBridgeCallLabel s).entryPoint = .ledger := by
  unfold deployedBridgeCallLabel
  split <;> rfl

private theorem rf_label_of_vault_eq {s : TokenStorage} (h : s.token.config.vault = 0) :
    deployedBridgeCallLabel s = .legacyBridgeCall := by
  unfold deployedBridgeCallLabel
  rw [ite_eq_left h]

private theorem rf_label_of_vault_ne {s : TokenStorage} (h : s.token.config.vault ≠ 0) :
    deployedBridgeCallLabel s = .bridgeCall := by
  unfold deployedBridgeCallLabel
  rw [ite_eq_right h]

private theorem rf_versionCalls_cons (c : StorageCall) (calls : List StorageCall) :
    versionCalls (c :: calls) = versionCalls [c] + versionCalls calls := by
  cases c <;> simp only [versionCalls] <;> omega

private theorem rf_initializeCalls_cons (c : StorageCall) (calls : List StorageCall) :
    initializeCalls (c :: calls) = initializeCalls [c] + initializeCalls calls := by
  cases c <;> simp only [initializeCalls] <;> omega

private theorem rf_legacyBranchCalls_cons (c : DeployedStorageCall)
    (calls : List DeployedStorageCall) :
    legacyBranchCalls (c :: calls) = legacyBranchCalls [c] + legacyBranchCalls calls := by
  cases c <;> simp only [legacyBranchCalls] <;> omega

/-! ## Labelled steps and deployed steps -/

private theorem rf_callStep_step {env : LegacyEnv} {s t : TokenStorage}
    {c : DeployedStorageCall} (h : DeployedStorageCallStep env s c t) :
    DeployedStorageStep env s t := by
  cases h with
  | bridgeInitialize h => exact DeployedStorageStep.bridgeInitialize h
  | reinitialize h => exact DeployedStorageStep.reinitialize h
  | bridgeMint h => exact DeployedStorageStep.ledger (LegacyStep.bridgeMint h)
  | bridgeBurn h => exact DeployedStorageStep.ledger (LegacyStep.bridgeBurn h)
  | transfer h => exact DeployedStorageStep.ledger (LegacyStep.transfer h)

private theorem rf_step_callStep {env : LegacyEnv} {s t : TokenStorage}
    (h : DeployedStorageStep env s t) : ∃ c, DeployedStorageCallStep env s c t := by
  cases h with
  | bridgeInitialize h => exact ⟨_, DeployedStorageCallStep.bridgeInitialize h⟩
  | reinitialize h => exact ⟨_, DeployedStorageCallStep.reinitialize h⟩
  | ledger h =>
    cases h with
    | bridgeMint h => exact ⟨_, DeployedStorageCallStep.bridgeMint h⟩
    | bridgeBurn h => exact ⟨_, DeployedStorageCallStep.bridgeBurn h⟩
    | transfer h => exact ⟨_, DeployedStorageCallStep.transfer h⟩

private theorem rf_run_snoc {env : LegacyEnv} {s t u : TokenStorage}
    {calls : List DeployedStorageCall} {c : DeployedStorageCall}
    (h : DeployedStorageRun env s calls t) (hs : DeployedStorageCallStep env t c u) :
    DeployedStorageRun env s (calls ++ [c]) u := by
  induction h with
  | nil => exact DeployedStorageRun.cons hs DeployedStorageRun.nil
  | cons hstep _ ih => exact DeployedStorageRun.cons hstep (ih hs)

private theorem rf_reach_cons {env : LegacyEnv} {s t u : TokenStorage}
    (hs : DeployedStorageStep env s t) (h : DeployedStorageReach env t u) :
    DeployedStorageReach env s u := by
  induction h with
  | refl => exact DeployedStorageReach.tail DeployedStorageReach.refl hs
  | tail _ hstep ih => exact DeployedStorageReach.tail ih hstep

private theorem rf_run_reach {env : LegacyEnv} {s t : TokenStorage}
    {calls : List DeployedStorageCall} (h : DeployedStorageRun env s calls t) :
    DeployedStorageReach env s t := by
  induction h with
  | nil => exact DeployedStorageReach.refl
  | cons hstep _ ih => exact rf_reach_cons (rf_callStep_step hstep) ih

/-- On a zero vault slot, a successful `bridgeMint` is a `legacyBridgeCall` step. -/
private theorem rf_legacy_mint_step {env : LegacyEnv} {s : TokenStorage} {token : State}
    {caller recipient : Address} {amount : UInt256} (hl : s.token.config.vault = 0)
    (h : bridgeMint env s.token caller recipient amount = some token) :
    DeployedStorageCallStep env s .legacyBridgeCall { s with token := token } := by
  have hs := DeployedStorageCallStep.bridgeMint (env := env) h
  rwa [rf_label_of_vault_eq hl] at hs

/-- On a zero vault slot, a successful `bridgeBurn` is a `legacyBridgeCall` step. -/
private theorem rf_legacy_burn_step {env : LegacyEnv} {s : TokenStorage} {token : State}
    {caller owner : Address} {amount : UInt256} (hl : s.token.config.vault = 0)
    (h : bridgeBurn env s.token caller owner amount = some token) :
    DeployedStorageCallStep env s .legacyBridgeCall { s with token := token } := by
  have hs := DeployedStorageCallStep.bridgeBurn (env := env) h
  rwa [rf_label_of_vault_eq hl] at hs

/-- On a nonzero vault slot, a successful `bridgeMint` is a `bridgeCall` step. -/
private theorem rf_mint_step {env : LegacyEnv} {s : TokenStorage} {token : State}
    {caller recipient : Address} {amount : UInt256} (hv : s.token.config.vault ≠ 0)
    (h : bridgeMint env s.token caller recipient amount = some token) :
    DeployedStorageCallStep env s .bridgeCall { s with token := token } := by
  have hs := DeployedStorageCallStep.bridgeMint (env := env) h
  rwa [rf_label_of_vault_ne hv] at hs

/-- On a nonzero vault slot, a successful `bridgeBurn` is a `bridgeCall` step. -/
private theorem rf_burn_step {env : LegacyEnv} {s : TokenStorage} {token : State}
    {caller owner : Address} {amount : UInt256} (hv : s.token.config.vault ≠ 0)
    (h : bridgeBurn env s.token caller owner amount = some token) :
    DeployedStorageCallStep env s .bridgeCall { s with token := token } := by
  have hs := DeployedStorageCallStep.bridgeBurn (env := env) h
  rwa [rf_label_of_vault_ne hv] at hs

/-- A modelled labelled step is a deployed one, with a label of the same entry point that is not
the legacy branch. -/
private theorem rf_callStep_of_storageCallStep (env : LegacyEnv) {s t : TokenStorage}
    {c : StorageCall} (h : StorageCallStep s c t) :
    ∃ c', DeployedStorageCallStep env s c' t ∧ c'.entryPoint = c ∧
      legacyBranchCalls [c'] = 0 := by
  cases h with
  | bridgeInitialize h => exact ⟨_, DeployedStorageCallStep.bridgeInitialize h, rfl, rfl⟩
  | reinitialize h => exact ⟨_, DeployedStorageCallStep.reinitialize h, rfl, rfl⟩
  | ledger h =>
    cases h with
    | burn hb =>
      exact ⟨_, rf_burn_step (burn_some_iff.mp hb).1.1 (bridgeBurn_of_burn env hb), rfl, rfl⟩
    | mint hm =>
      exact ⟨_, rf_mint_step (mint_some_iff.mp hm).1.1 (bridgeMint_of_mint env hm), rfl, rfl⟩
    | transfer ht => exact ⟨_, DeployedStorageCallStep.transfer ht, rfl, rfl⟩

/-- A labelled step that is not on the legacy branch is a modelled step, at its entry point. -/
private theorem rf_storageCallStep_of_callStep {env : LegacyEnv} {s t : TokenStorage}
    {c : DeployedStorageCall} (h : DeployedStorageCallStep env s c t)
    (hc : legacyBranchCalls [c] = 0) : StorageCallStep s c.entryPoint t := by
  have hnl : ∀ {u : TokenStorage}, legacyBranchCalls [deployedBridgeCallLabel u] = 0 →
      u.token.config.vault ≠ 0 := by
    intro u hu hv
    rw [rf_label_of_vault_eq hv] at hu
    exact absurd hu (by decide)
  cases h with
  | bridgeInitialize h => exact StorageCallStep.bridgeInitialize h
  | reinitialize h => exact StorageCallStep.reinitialize h
  | bridgeMint h =>
    rw [rf_label_entryPoint]
    exact StorageCallStep.ledger (legacyStep_step_of_vault_ne (hnl hc) (LegacyStep.bridgeMint h))
  | bridgeBurn h =>
    rw [rf_label_entryPoint]
    exact StorageCallStep.ledger (legacyStep_step_of_vault_ne (hnl hc) (LegacyStep.bridgeBurn h))
  | transfer h => exact StorageCallStep.ledger (Step.transfer h)

/-! ## The labelled runs -/

theorem DeployedStorageRunsAreReach : Properties.DeployedStorageRunsAreReach := by
  intro env s t
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], DeployedStorageRun.nil⟩
    | tail _ hstep ih =>
      obtain ⟨calls, hrun⟩ := ih
      obtain ⟨c, hc⟩ := rf_step_callStep hstep
      exact ⟨calls ++ [c], rf_run_snoc hrun hc⟩
  · rintro ⟨calls, h⟩
    exact rf_run_reach h

theorem ModelledRunsAreDeployedRunsWithoutLegacyCall :
    Properties.ModelledRunsAreDeployedRunsWithoutLegacyCall := by
  intro env s calls t
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], DeployedStorageRun.nil, rfl, rfl⟩
    | cons hstep _ ih =>
      obtain ⟨calls', hrun, hmap, hlegacy⟩ := ih
      obtain ⟨c', hc', hentry, hne⟩ := rf_callStep_of_storageCallStep env hstep
      refine ⟨c' :: calls', DeployedStorageRun.cons hc' hrun, ?_, ?_⟩
      · rw [List.map_cons, hentry, hmap]
      · rw [rf_legacyBranchCalls_cons, hne, hlegacy]
  · rintro ⟨calls', h, rfl, h0⟩
    induction h with
    | nil => exact StorageRun.nil
    | cons hstep _ ih =>
      rw [rf_legacyBranchCalls_cons] at h0
      exact StorageRun.cons (rf_storageCallStep_of_callStep hstep (by omega)) (ih (by omega))

/-! ## `Reinitialization`'s counting results, on every deployed run -/

private theorem rf_callStep_version {env : LegacyEnv} {s t : TokenStorage}
    {c : DeployedStorageCall} (h : DeployedStorageCallStep env s c t) :
    t.version.toNat = s.version.toNat + versionCalls [c.entryPoint] := by
  cases h with
  | bridgeInitialize h =>
    obtain ⟨_, _, h0, rfl⟩ := rf_initializeStorage_view h
    show (1 : UInt8).toNat = s.version.toNat + 1
    rw [h0]
    rfl
  | reinitialize h =>
    obtain ⟨hn, rfl⟩ := rf_reinit_view h
    exact hn
  | bridgeMint _ =>
    rw [rf_label_entryPoint]
    rfl
  | bridgeBurn _ =>
    rw [rf_label_entryPoint]
    rfl
  | transfer _ => rfl

private theorem rf_callStep_version_ne_zero {env : LegacyEnv} {s t : TokenStorage}
    {c : DeployedStorageCall} (h : DeployedStorageCallStep env s c t) (hv : s.version ≠ 0) :
    t.version ≠ 0 := by
  cases h with
  | bridgeInitialize h =>
    obtain ⟨_, _, _, rfl⟩ := rf_initializeStorage_view h
    exact rf_one_ne_zero
  | reinitialize h =>
    obtain ⟨hn, rfl⟩ := rf_reinit_view h
    exact rf_version_ne_zero_of_next hn
  | bridgeMint _ => exact hv
  | bridgeBurn _ => exact hv
  | transfer _ => exact hv

theorem DeployedVersionCountsInitializations :
    Properties.DeployedVersionCountsInitializations := by
  intro env s calls t h
  induction h with
  | nil => rfl
  | cons hstep _ ih =>
    rw [List.map_cons, rf_versionCalls_cons, ih, rf_callStep_version hstep]
    omega

theorem DeployedLifetimeVersionCallBound : Properties.DeployedLifetimeVersionCallBound := by
  intro env calls t h
  have hc := DeployedVersionCountsInitializations env freshStorage calls t h
  have hlt : t.version.toNat < 256 := t.version.toNat_lt_size
  have h0 : freshStorage.version.toNat = 0 := rfl
  omega

theorem DeployedLifetimeBoundIsTight : Properties.DeployedLifetimeBoundIsTight := by
  intro env
  obtain ⟨calls, t, hrun, h1, h2, h3⟩ := LifetimeBoundIsTight
  obtain ⟨calls', hrun', hmap, _⟩ :=
    (ModelledRunsAreDeployedRunsWithoutLegacyCall env _ _ _).mp hrun
  refine ⟨calls', t, hrun', ?_, ?_, h3⟩
  · rw [hmap]
    exact h1
  · rw [hmap]
    exact h2

theorem DeployedBridgeInitializeAtMostOnce : Properties.DeployedBridgeInitializeAtMostOnce := by
  intro env s calls t h
  induction h with
  | nil => exact ⟨Nat.zero_le _, fun _ => rfl⟩
  | cons hstep hrest ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [List.map_cons, rf_initializeCalls_cons]
    cases hstep with
    | bridgeInitialize h' =>
      obtain ⟨_, _, h0, rfl⟩ := rf_initializeStorage_view h'
      have hz := ih2 rf_one_ne_zero
      refine ⟨?_, fun hne => absurd h0 hne⟩
      simp [DeployedStorageCall.entryPoint, initializeCalls, hz]
    | reinitialize h' =>
      obtain ⟨hn, rfl⟩ := rf_reinit_view h'
      have hz := ih2 (rf_version_ne_zero_of_next hn)
      simp [DeployedStorageCall.entryPoint, initializeCalls, hz]
    | bridgeMint _ =>
      rw [rf_label_entryPoint]
      simp only [initializeCalls, Nat.zero_add]
      exact ⟨ih1, ih2⟩
    | bridgeBurn _ =>
      rw [rf_label_entryPoint]
      simp only [initializeCalls, Nat.zero_add]
      exact ⟨ih1, ih2⟩
    | transfer _ =>
      simp only [DeployedStorageCall.entryPoint, initializeCalls, Nat.zero_add]
      exact ⟨ih1, ih2⟩

/-! ## How many calls take the legacy branch -/

/-- A bridge call adds at most what it costs: a legacy call starts on a zero vault slot and leaves
a nonzero one; a nonlegacy one keeps the vault slot. -/
private theorem rf_bridge_legacy_bound {env : LegacyEnv} {s : TokenStorage} {token : State}
    (hc : token.config = (legacyFallback env s.token).config) :
    legacyBranchCalls [deployedBridgeCallLabel s] +
        (if ({ s with token := token } : TokenStorage).token.config.vault = 0 then 1 else 0) ≤
      (if s.token.config.vault = 0 then 1 else 0) +
        initializeCalls [(deployedBridgeCallLabel s).entryPoint] := by
  rw [rf_label_entryPoint]
  rcases rf_bridge_config hc with ⟨hv, hc'⟩ | ⟨hv, hc'⟩
  · have ht : token.config.vault ≠ 0 := by
      rw [hc']
      exact fallbackConfig_vault_ne env _
    rw [rf_label_of_vault_eq hv]
    simp [legacyBranchCalls, initializeCalls, hv, ht]
  · rw [rf_label_of_vault_ne hv]
    simp [legacyBranchCalls, initializeCalls, hc']

/-- One step's share of `DeployedLegacyBranchBound`. -/
private theorem rf_callStep_legacy_bound {env : LegacyEnv} {s t : TokenStorage}
    {c : DeployedStorageCall} (h : DeployedStorageCallStep env s c t) :
    legacyBranchCalls [c] + (if t.token.config.vault = 0 then 1 else 0) ≤
      (if s.token.config.vault = 0 then 1 else 0) + initializeCalls [c.entryPoint] := by
  cases h with
  | bridgeInitialize _ =>
    have h1 : (if t.token.config.vault = 0 then 1 else 0) ≤ 1 := by split <;> omega
    simp only [legacyBranchCalls, DeployedStorageCall.entryPoint, initializeCalls]
    omega
  | reinitialize h' =>
    obtain ⟨_, rfl⟩ := rf_reinit_view h'
    simp only [legacyBranchCalls, DeployedStorageCall.entryPoint, initializeCalls]
    omega
  | bridgeMint h' => exact rf_bridge_legacy_bound (bridgeMint_config h')
  | bridgeBurn h' => exact rf_bridge_legacy_bound (bridgeBurn_config h')
  | transfer h' =>
    have hc := transfer_config h'
    simp only [legacyBranchCalls, DeployedStorageCall.entryPoint, initializeCalls, hc]
    omega

theorem DeployedLegacyBranchBound : Properties.DeployedLegacyBranchBound := by
  intro env s calls t h
  induction h with
  | nil => exact Nat.zero_le _
  | cons hstep _ ih =>
    have hs := rf_callStep_legacy_bound hstep
    rw [List.map_cons, rf_initializeCalls_cons, rf_legacyBranchCalls_cons]
    omega

/-- One bridge call's share of `DeployedLegacyBranchCountExact`, from a nonzero version. -/
private theorem rf_bridge_count {env : LegacyEnv} {s u : TokenStorage} {token : State}
    {calls : List DeployedStorageCall}
    (hc : token.config = (legacyFallback env s.token).config)
    (hrest : DeployedStorageRun env { s with token := token } calls u)
    (hv : ({ s with token := token } : TokenStorage).version ≠ 0) :
    legacyBranchCalls [deployedBridgeCallLabel s] +
        (if ({ s with token := token } : TokenStorage).token.config.vault = 0 ∧
            u.token.config.vault ≠ 0 then 1 else 0) =
      if s.token.config.vault = 0 ∧ u.token.config.vault ≠ 0 then 1 else 0 := by
  rcases rf_bridge_config hc with ⟨hl, hc'⟩ | ⟨hl, hc'⟩
  · have ht : token.config.vault ≠ 0 := by
      rw [hc']
      exact fallbackConfig_vault_ne env _
    have hend := (DeployedInitializedIdentityIsFixed env _ u hv ht (rf_run_reach hrest)).1
    have hu : u.token.config.vault ≠ 0 := by
      rw [hend]
      exact ht
    rw [rf_label_of_vault_eq hl]
    simp [legacyBranchCalls, hl, ht, hu]
  · rw [rf_label_of_vault_ne hl]
    simp [legacyBranchCalls, hc', hl]

theorem DeployedLegacyBranchCountExact : Properties.DeployedLegacyBranchCountExact := by
  intro env s calls t hv h
  induction h with
  | nil => simp [legacyBranchCalls]
  | cons hstep hrest ih =>
    have hv' := rf_callStep_version_ne_zero hstep hv
    rw [rf_legacyBranchCalls_cons, ih hv']
    cases hstep with
    | bridgeInitialize h' =>
      obtain ⟨_, _, h0, _⟩ := rf_initializeStorage_view h'
      exact absurd h0 hv
    | reinitialize h' =>
      obtain ⟨_, rfl⟩ := rf_reinit_view h'
      simp only [legacyBranchCalls, Nat.zero_add]
    | bridgeMint h' => exact rf_bridge_count (bridgeMint_config h') hrest hv'
    | bridgeBurn h' => exact rf_bridge_count (bridgeBurn_config h') hrest hv'
    | transfer h' =>
      have hc := transfer_config h'
      simp only [legacyBranchCalls, Nat.zero_add, hc]

/-- The fresh-proxy run with two legacy calls: the L2 vault's mint to `4`, `bridgeInitialize` by
caller `0`, the L2 vault's burn from `4`. -/
theorem DeployedLegacyBranchTwiceFromFreshProxy :
    Properties.DeployedLegacyBranchTwiceFromFreshProxy := by
  intro env
  have h1 : (1 : UInt256).val = 1 := rfl
  -- the L2 vault's one-unit mint to `4` on the fresh proxy, through the legacy branch
  let m₁ : State :=
    mintEffect { freshStorage.token with config := fallbackConfig env ⟨0, 0, 0⟩ } 4 1
  have hmint : bridgeMint env freshStorage.token l2NativeTokenVaultAddr 4 1 = some m₁ :=
    legacy_bridge_mint_enabled env (s := freshStorage.token) rfl (by decide)
      (by show (0 : ℕ) + (1 : UInt256).val < UInt256.size; decide)
  let u₁ : TokenStorage := { freshStorage with token := m₁ }
  have hstep₁ : DeployedStorageCallStep env freshStorage .legacyBridgeCall u₁ :=
    rf_legacy_mint_step rfl hmint
  -- `bridgeInitialize` by caller `0`, still at version 0: the vault slot is zero again
  let u₂ : TokenStorage := ⟨{ m₁ with config := ⟨0, 9, 5⟩ }, 1, emptyMetadata⟩
  have hinit : initializeStorage u₁ 0 5 9 (some emptyMetadata) = some u₂ :=
    rf_initializeStorage_of_version_zero rfl (by decide) emptyMetadata
  have hstep₂ : DeployedStorageCallStep env u₁ .bridgeInitialize u₂ :=
    DeployedStorageCallStep.bridgeInitialize hinit
  -- the L2 vault's one-unit burn from `4`, through the legacy branch again
  have hbal : u₂.token.balances 4 = 1 := by
    show Function.update (fun _ => 0) (4 : Address) (0 + (1 : UInt256).val) 4 = 1
    rw [Function.update_self, h1]
  let m₃ : State := burnEffect { m₁ with config := fallbackConfig env ⟨0, 9, 5⟩ } 4 1
  have hburn : bridgeBurn env u₂.token l2NativeTokenVaultAddr 4 1 = some m₃ :=
    legacy_bridge_burn_enabled env (s := u₂.token) rfl (by decide) (by rw [hbal, h1])
  have hstep₃ : DeployedStorageCallStep env u₂ .legacyBridgeCall { u₂ with token := m₃ } :=
    rf_legacy_burn_step rfl hburn
  refine ⟨{ u₂ with token := m₃ }, DeployedStorageRun.cons hstep₁
    (DeployedStorageRun.cons hstep₂ (DeployedStorageRun.cons hstep₃ DeployedStorageRun.nil)),
    rfl, rfl, ?_⟩
  show 0 + (1 : UInt256).val - (1 : UInt256).val = 0
  rw [h1]

/-! ## Witness -/

theorem DeployedCountingWitness : Properties.DeployedCountingWitness := by
  intro env
  have h1 : (1 : UInt256).val = 1 := rfl
  constructor
  · -- the nonlegacy branch: initialize, mint, reinitialize
    let s₁ : TokenStorage := ⟨{ freshStorage.token with config := ⟨1, 9, 5⟩ }, 1, emptyMetadata⟩
    have hinit : initializeStorage freshStorage 1 5 9 (some emptyMetadata) = some s₁ :=
      rf_initializeStorage_of_version_zero rfl (by decide) emptyMetadata
    have hm : MintAllowed s₁.token 1 4 1 := by
      refine ⟨by decide, rfl, by decide, ?_⟩
      show (0 : ℕ) + (1 : UInt256).val < UInt256.size
      decide
    have hmint : mint s₁.token 1 4 1 = some (mintEffect s₁.token 4 1) := ite_eq_left hm
    let s₂ : TokenStorage := { s₁ with token := mintEffect s₁.token 4 1 }
    have hstep₁ : DeployedStorageCallStep env s₁ .bridgeCall s₂ :=
      rf_mint_step (show (1 : Address) ≠ 0 by decide) (bridgeMint_of_mint env hmint)
    obtain ⟨t, ht⟩ := (ReinitSucceedsIff (some 7) s₂ 7 ⟨false, false, false⟩ [0x42] [0x43] 2).mpr
      ⟨rfl, rfl⟩
    have he := ReinitExactEffect _ _ _ _ _ _ _ _ ht
    have hstep₂ : DeployedStorageCallStep env s₂ .reinitializeToken t :=
      DeployedStorageCallStep.reinitialize ht
    have hrun : DeployedStorageRun env s₁ [.bridgeCall, .reinitializeToken] t :=
      DeployedStorageRun.cons hstep₁ (DeployedStorageRun.cons hstep₂ DeployedStorageRun.nil)
    have hmodel : StorageRun freshStorage [.bridgeInitialize, .ledger, .reinitializeToken] t :=
      StorageRun.cons (StorageCallStep.bridgeInitialize hinit)
        (StorageRun.cons (StorageCallStep.ledger (Step.mint hmint))
          (StorageRun.cons (StorageCallStep.reinitialize ht) StorageRun.nil))
    subst he
    refine ⟨s₁, _, hinit, rfl, hrun,
      DeployedStorageRun.cons (DeployedStorageCallStep.bridgeInitialize hinit) hrun, hmodel, rfl,
      ?_, rfl⟩
    show 0 + (1 : UInt256).val = 1
    rw [h1]
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
    have hstep₁ : DeployedStorageCallStep env s .legacyBridgeCall u := rf_legacy_burn_step hl hburn
    obtain ⟨t, ht⟩ := (ReinitSucceedsIff (some 7) u 7 ⟨false, false, false⟩ [] [] 2).mpr
      ⟨rfl, rfl⟩
    have he := ReinitExactEffect _ _ _ _ _ _ _ _ ht
    have hrun : DeployedStorageRun env s [.legacyBridgeCall, .reinitializeToken] t :=
      DeployedStorageRun.cons hstep₁
        (DeployedStorageRun.cons (DeployedStorageCallStep.reinitialize ht) DeployedStorageRun.nil)
    have hcfg : t.token.config = fallbackConfig env ⟨0, 9, 0⟩ := by
      rw [he]
      rfl
    -- the end is not a `StorageReach` end: those runs keep the identity from a nonzero version
    have hnot : ¬ StorageReach s t := by
      intro hr
      have hfix := (InitializedIdentityIsFixed s t (by show (1 : UInt8) ≠ 0; decide) hr).1
      have hv := congrArg Config.vault (hcfg.symm.trans hfix)
      exact fallbackConfig_vault_ne env _ hv
    refine ⟨s, t, hw, rfl, rfl, hbal, rfl, hrun, hnot, by rw [he], hcfg, ?_⟩
    rw [he]
    show (1 : ℕ) - (1 : UInt256).val = 0
    rw [h1]

end Contracts.BridgedStandardERC20
