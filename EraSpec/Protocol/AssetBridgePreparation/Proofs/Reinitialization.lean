import EraSpec.Protocol.AssetBridgePreparation.Properties.Reinitialization
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Model
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Reinitialization
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.Initialization
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Reinitialization

namespace AssetBridgePreparation

open Contracts

variable {Accounting : Type}

/-! ## Steps -/

theorem ReinitStepCases : Properties.ReinitStepCases := by
  intro Accounting hooks s u h
  cases h with
  | trace h => exact Or.inr ⟨rfl, rfl, h⟩
  | reinitialize h =>
    left
    refine ⟨?_, (BridgedStandardERC20.ReinitVersionIncreasesByOne _ _ _ _ _ _ _ _ h).1⟩
    dsimp only
    rw [NativeTokenVaultBase.ReinitLeavesVaultStateUnchanged _ _ _ _ _ _ _ _ _ _ h]

theorem TraceRunsEmbed : Properties.TraceRunsEmbed := by
  intro Accounting hooks version metadata s t h
  induction h with
  | refl => exact ReinitReach.refl
  | tail _ hstep ih => exact ReinitReach.tail ih (ReinitStep.trace hstep)

/-- The token's identity is kept by every trace step from a `WellFormed` vault. -/
private theorem step_token_config {hooks : NativeTokenVaultBase.Hooks Accounting}
    {s t : Ledger Accounting} (hw : NativeTokenVaultBase.WellFormed s.vault)
    (h : Step hooks s t) : t.vault.token.config = s.vault.token.config := by
  cases h with
  | prepare hp =>
    have hb := (NativeTokenVaultBase.preparation_backed hw hp).1
    exact (BridgedStandardERC20.burn_exact hw.1 hb).2.2.2.2.2
  | spend ht =>
    exact (BridgedStandardERC20.transfer_preserves_ledger hw.1 ht).2.2

/-- Every trace step from a `WellFormed` vault keeps `PendingNamesToken`. -/
private theorem step_pending_names {hooks : NativeTokenVaultBase.Hooks Accounting}
    {s t : Ledger Accounting} (hw : NativeTokenVaultBase.WellFormed s.vault)
    (hp : PendingNamesToken s) (h : Step hooks s t) : PendingNamesToken t := by
  have hc := step_token_config hw h
  cases h with
  | prepare hprep =>
    rename_i r out
    intro o ho
    rcases List.mem_append.mp ho with hold | hnew
    · rw [hc]
      exact hp o hold
    · rw [List.mem_singleton] at hnew
      subst hnew
      obtain ⟨_, hasset, _⟩ := NativeTokenVaultBase.preparation_asset_binding hw hprep
      obtain ⟨_, _, horigin, _, _, _⟩ := NativeTokenVaultBase.preparation_payload hw hprep
      refine ⟨hasset.symm, ?_⟩
      change out.data.originToken = out.state.token.config.originToken
      rw [horigin]
      exact (congrArg BridgedStandardERC20.Config.originToken hc).symm
  | spend ht =>
    intro o ho
    rw [hc]
    exact hp o ho

/-- One extended step: conservation, identity, and `PendingNamesToken`, from `WellFormed`. -/
private theorem reinit_step_conservation {hooks : NativeTokenVaultBase.MetaHooks Accounting}
    {s u : TokenTrace Accounting} (hw : NativeTokenVaultBase.WellFormed s.ledger.vault)
    (h : ReinitStep hooks s u) :
    NativeTokenVaultBase.WellFormed u.ledger.vault ∧
    u.ledger.vault.token.totalSupply + pendingAmount u.ledger.pending =
      s.ledger.vault.token.totalSupply + pendingAmount s.ledger.pending ∧
    u.ledger.vault.config = s.ledger.vault.config ∧
    u.ledger.vault.token.config = s.ledger.vault.token.config ∧
    (PendingNamesToken s.ledger → PendingNamesToken u.ledger) ∧
    ∃ later, u.ledger.pending = s.ledger.pending ++ later := by
  rcases ReinitStepCases hooks s u h with ⟨hl, _⟩ | ⟨_, _, hstep⟩
  · rw [hl]
    exact ⟨hw, rfl, rfl, rfl, id, [], (List.append_nil _).symm⟩
  · have hr : Reach (hooks.toHooks s.metadata) s.ledger u.ledger := Reach.tail Reach.refl hstep
    obtain ⟨hwu, hsum, hcfg⟩ := reachable_conservation hw hr
    exact ⟨hwu, hsum, hcfg, step_token_config hw hstep, fun hp => step_pending_names hw hp hstep,
      prepared_data_persists hr⟩

/-! ## Runs -/

private theorem reach_invariants {hooks : NativeTokenVaultBase.MetaHooks Accounting}
    {s t : TokenTrace Accounting} (hw : NativeTokenVaultBase.WellFormed s.ledger.vault)
    (h : ReinitReach hooks s t) :
    NativeTokenVaultBase.WellFormed t.ledger.vault ∧
    t.ledger.vault.token.totalSupply + pendingAmount t.ledger.pending =
      s.ledger.vault.token.totalSupply + pendingAmount s.ledger.pending ∧
    t.ledger.vault.config = s.ledger.vault.config ∧
    t.ledger.vault.token.config = s.ledger.vault.token.config ∧
    (PendingNamesToken s.ledger → PendingNamesToken t.ledger) := by
  induction h with
  | refl => exact ⟨hw, rfl, rfl, rfl, id⟩
  | tail _ hstep ih =>
    obtain ⟨hwt, hsum, hcfg, htok, hpend⟩ := ih
    obtain ⟨hwu, hsum', hcfg', htok', hpend', _⟩ := reinit_step_conservation hwt hstep
    exact ⟨hwu, hsum'.trans hsum, hcfg'.trans hcfg, htok'.trans htok, hpend' ∘ hpend⟩

theorem ReinitTraceConservation : Properties.ReinitTraceConservation := by
  intro Accounting hooks s t hw h
  obtain ⟨hwt, hsum, hcfg, htok, _⟩ := reach_invariants hw h
  exact ⟨hwt, hsum, hcfg, htok⟩

theorem ReinitTracePreparedDataPersists : Properties.ReinitTracePreparedDataPersists := by
  intro Accounting hooks s t h
  induction h with
  | refl => exact ⟨[], (List.append_nil _).symm⟩
  | tail _ hstep ih =>
    obtain ⟨later, hl⟩ := ih
    rcases ReinitStepCases hooks _ _ hstep with ⟨hu, _⟩ | ⟨_, _, hs⟩
    · exact ⟨later, by rw [hu, hl]⟩
    · obtain ⟨more, hm⟩ := prepared_data_persists (Reach.tail Reach.refl hs)
      exact ⟨later ++ more, by rw [hm, hl, List.append_assoc]⟩

theorem PendingObligationsKeepTheirAsset : Properties.PendingObligationsKeepTheirAsset := by
  intro Accounting hooks s t hw hp h
  obtain ⟨_, _, _, htok, hpend⟩ := reach_invariants hw h
  have hpt := hpend hp
  refine ⟨hpt, ?_⟩
  intro o ho
  rw [← htok]
  exact hpt o ho

theorem InitializedTraceWithReinitialization :
    Properties.InitializedTraceWithReinitialization := by
  intro Accounting initHooks start origin registered metadata funded hooks t hi hf hr
  have hinner := (NativeTokenVaultBase.fresh_registration_preconditions hi).2
  have hw := NativeTokenVaultBase.registration_establishes_wellformed hinner
  have hver : registered.tokenVersion = 1 :=
    (NativeTokenVaultBase.registration_initial_fields hinner).2.2.1
  let s₀ : BridgedStandardERC20.TokenStorage :=
    ⟨registered.state.token, registered.tokenVersion, metadata⟩
  have hw₀ : BridgedStandardERC20.WellFormed s₀.token := hw.1
  have hv₀ : s₀.version ≠ 0 := by
    change registered.tokenVersion ≠ 0
    rw [hver]
    decide
  have hwf := (BridgedStandardERC20.RunsPreserveLedger s₀ funded hw₀ hf).1
  have hcfg := (BridgedStandardERC20.InitializedIdentityIsFixed s₀ funded hv₀ hf).1
  have hs : NativeTokenVaultBase.WellFormed
      (NativeTokenVaultBase.withTracked registered.state funded) := by
    refine ⟨hwf, ?_, ?_, hw.2.2.2⟩
    · exact (congrArg BridgedStandardERC20.Config.vault hcfg).trans hw.2.1
    · exact (congrArg BridgedStandardERC20.Config.assetId hcfg).trans hw.2.2.1
  let start' : TokenTrace Accounting :=
    ⟨⟨NativeTokenVaultBase.withTracked registered.state funded, []⟩, funded.version,
      funded.metadata⟩
  have hs' : NativeTokenVaultBase.WellFormed start'.ledger.vault := hs
  obtain ⟨hwt, hsum, _, htok, hpend⟩ := reach_invariants (s := start') hs' hr
  have hp0 : PendingNamesToken start'.ledger := by
    intro o ho
    cases ho
  refine ⟨hwt.1, hwt.2, ?_, hpend hp0, ?_⟩
  · rw [hsum]
    rfl
  · rw [htok]
    exact hcfg

/-! ## Witness -/

/-- What the witness registration installs: the witness configuration, the two registry entries,
and the fresh token initialized by the vault for asset `5` and origin token `9`. -/
private def wRegistered : NativeTokenVaultBase.Registered Unit :=
  ⟨⟨NativeTokenVaultBase.wVault.config,
    NativeTokenVaultBase.installRegistry ⟨fun _ => 0, fun _ => 0⟩ 5 3, false,
    BridgedStandardERC20.empty ⟨1, 9, 5⟩, ()⟩, 1⟩

/-- The funded token storage: ten units at account `4`, version 1, named `[0x41]`. -/
private def wFunded : BridgedStandardERC20.TokenStorage :=
  ⟨NativeTokenVaultBase.wToken, 1, NativeTokenVaultBase.wMetadata⟩

private def wVault₀ : NativeTokenVaultBase.State Unit :=
  NativeTokenVaultBase.withTracked wRegistered.state wFunded

/-- The vault after the first preparation: three units burned from account `4`. -/
private def wVault₁ : NativeTokenVaultBase.State Unit :=
  { wVault₀ with token := BridgedStandardERC20.burnEffect NativeTokenVaultBase.wToken 4 3 }

/-- The vault after the second preparation: three more units burned from account `4`. -/
private def wVault₂ : NativeTokenVaultBase.State Unit :=
  { wVault₀ with token := BridgedStandardERC20.burnEffect wVault₁.token 4 3 }

/-- The token's metadata after the reinitialization. -/
private def wMetadata₂ : BridgedStandardERC20.Metadata :=
  BridgedStandardERC20.reinitMetadata NativeTokenVaultBase.wMetadata ⟨false, false, false⟩
    [0x42] [0x42]

theorem ReinitTraceWitness : Properties.ReinitTraceWitness := by
  have hreg : NativeTokenVaultBase.registerFreshBranch wRegHooks wRegStart 9 =
      some wRegistered := rfl
  have hmint : BridgedStandardERC20.mint wRegistered.state.token 1 4 10 =
      some NativeTokenVaultBase.wToken := rfl
  have hfund : BridgedStandardERC20.StorageReach
      ⟨wRegistered.state.token, wRegistered.tokenVersion, NativeTokenVaultBase.wMetadata⟩
      wFunded :=
    BridgedStandardERC20.StorageReach.tail BridgedStandardERC20.StorageReach.refl
      (BridgedStandardERC20.StorageStep.ledger (BridgedStandardERC20.Step.mint hmint))
  have hprep₁ : NativeTokenVaultBase.prepare
      (NativeTokenVaultBase.wHooks.toHooks NativeTokenVaultBase.wMetadata) wVault₀
      NativeTokenVaultBase.wRequest = some ⟨wVault₁, ⟨4, 12, 9, 3, [0x41]⟩⟩ := rfl
  have hreinit : BridgedStandardERC20.reinitializeToken (some 13)
      (NativeTokenVaultBase.trackedStorage wVault₁ 1 NativeTokenVaultBase.wMetadata) 13
      ⟨false, false, false⟩ [0x42] [0x42] 2 = some ⟨wVault₁.token, 2, wMetadata₂⟩ := rfl
  have hprep₂ : NativeTokenVaultBase.prepare
      (NativeTokenVaultBase.wHooks.toHooks wMetadata₂)
      (NativeTokenVaultBase.withTracked wVault₁ ⟨wVault₁.token, 2, wMetadata₂⟩)
      NativeTokenVaultBase.wRequest = some ⟨wVault₂, ⟨4, 12, 9, 3, [0x42]⟩⟩ := rfl
  let t₀ : TokenTrace Unit := ⟨⟨wVault₀, []⟩, 1, NativeTokenVaultBase.wMetadata⟩
  have h₁ := ReinitStep.trace (hooks := NativeTokenVaultBase.wHooks) (s := t₀)
    (Step.prepare hprep₁)
  have h₂ := ReinitStep.reinitialize (hooks := NativeTokenVaultBase.wHooks)
    (s := ⟨⟨wVault₁, [obligation NativeTokenVaultBase.wRequest ⟨4, 12, 9, 3, [0x41]⟩]⟩, 1,
      NativeTokenVaultBase.wMetadata⟩) hreinit
  have h₃ := ReinitStep.trace (hooks := NativeTokenVaultBase.wHooks)
    (s := ⟨⟨NativeTokenVaultBase.withTracked wVault₁ ⟨wVault₁.token, 2, wMetadata₂⟩,
      [obligation NativeTokenVaultBase.wRequest ⟨4, 12, 9, 3, [0x41]⟩]⟩, 2, wMetadata₂⟩)
    (Step.prepare hprep₂)
  have hrun := ReinitReach.tail (ReinitReach.tail (ReinitReach.tail ReinitReach.refl h₁) h₂) h₃
  have hw₀ : BridgedStandardERC20.WellFormed wRegistered.state.token :=
    (BridgedStandardERC20.one_unit_roundtrip ⟨1, 9, 5⟩ 4 (by decide) (by decide)).1
  have hwf : NativeTokenVaultBase.WellFormed wVault₀ :=
    ⟨BridgedStandardERC20.mint_preserves_ledger hw₀ hmint, rfl, rfl, rfl, rfl⟩
  refine ⟨wRegistered, wFunded, _, hreg, hfund, hwf, hrun, rfl, rfl, ?_, rfl, rfl⟩
  intro o ho
  simp only [List.nil_append, List.cons_append, List.mem_cons,
    List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl <;> exact ⟨rfl, rfl⟩

end AssetBridgePreparation
