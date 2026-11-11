import EraSpec.Protocol.AssetBridgePreparation.Properties.RegistryCorrespondence
import EraSpec.Protocol.AssetBridgePreparation.Proofs.Initialization
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistrationUnified

/-!
# Proofs: the preparation trace is the registry model's recorded outflow

The funding phase is a `RepReach` run of token operations, so
`NativeTokenVaultBase.unifiedLifecycleCorresponds` simulates registration plus
funding.  The trace is then simulated step by step from that registry state: a
preparation by the `bridgeOut` of its own destination chain, asset and amount, a
spend by no step.  The supply identity is `initialized_preparation_trace`.
-/

namespace AssetBridgePreparation

open Contracts

variable {Accounting : Type}

/-! ## The two pending totals -/

theorem pendingAmount_append_one (pending : List Obligation) (o : Obligation) :
    pendingAmount (pending ++ [o]) = pendingAmount pending + o.data.amount.val := by
  simp only [pendingAmount, List.map_append, List.map_cons, List.map_nil, List.sum_append,
    List.sum_cons, List.sum_nil, Nat.add_zero]

theorem pendingAmountTo_append_one (c : UInt256) (pending : List Obligation) (o : Obligation) :
    pendingAmountTo c (pending ++ [o]) =
      pendingAmountTo c pending + if o.destinationChain = c then o.data.amount.val else 0 := by
  unfold pendingAmountTo
  rw [List.filter_append]
  by_cases h : o.destinationChain = c
  · simp [h]
  · simp [h]

/-! ## Token-model runs are representation-model runs -/

theorem token_reach_repReach {hooks : NativeTokenVaultBase.Hooks Accounting}
    {t₀ token : BridgedStandardERC20.State} (h : BridgedStandardERC20.Reach t₀ token)
    (s : NativeTokenVaultBase.State Accounting) (hs : s.token = t₀) :
    NativeTokenVaultBase.RepReach hooks s { s with token := token } := by
  induction h with
  | refl =>
    subst hs
    exact NativeTokenVaultBase.RepReach.refl
  | @tail mid _ _ hstep ih =>
    exact NativeTokenVaultBase.RepReach.tail ih
      (NativeTokenVaultBase.RepStep.tokenOp (s := { s with token := mid }) hstep)

/-! ## The trace, against the registry run -/

/-- From a corresponding, well-formed ledger with nothing pending, on a registry state
where the tracked asset is registered and not native, every trace is simulated by a
registry run that records exactly the trace's preparations as outflow. -/
theorem trace_outflow {hooks : NativeTokenVaultBase.Hooks Accounting}
    {e : NativeTokenVault.NtvAssetId} {S : Set (NativeTokenVault.Chain × NativeTokenVault.Address)}
    {thisChain : NativeTokenVault.Chain} {Wf : NativeTokenVault.World}
    {cfg : NativeTokenVaultBase.Config}
    (hregf : NativeTokenVault.Registered Wf.vault cfg.assetId)
    (hforf : ¬ NativeTokenVault.Native thisChain Wf.vault cfg.assetId)
    {s₀ t : Ledger Accounting} (hr : Reach hooks s₀ t)
    (hcorr₀ : NativeTokenVaultBase.Corr s₀.vault thisChain Wf.vault)
    (hwf₀ : NativeTokenVaultBase.WellFormed s₀.vault) (hcfg₀ : s₀.vault.config = cfg)
    (hpend₀ : s₀.pending = []) :
    ∃ W' : NativeTokenVault.World, NativeTokenVault.ReachIn e thisChain S Wf W'
      ∧ W'.vault = Wf.vault ∧ NativeTokenVaultBase.Corr t.vault thisChain Wf.vault
      ∧ NativeTokenVaultBase.WellFormed t.vault ∧ t.vault.config = cfg
      ∧ W'.audit.totalIn cfg.assetId = Wf.audit.totalIn cfg.assetId
      ∧ W'.audit.totalOut cfg.assetId = Wf.audit.totalOut cfg.assetId + pendingAmount t.pending
      ∧ (∀ c, W'.audit.outTo c cfg.assetId
          = Wf.audit.outTo c cfg.assetId + pendingAmountTo c t.pending)
      ∧ ∀ o ∈ t.pending, o.assetId = cfg.assetId := by
  induction hr with
  | refl =>
    refine ⟨Wf, NativeTokenVault.ReachIn.refl, rfl, hcorr₀, hwf₀, hcfg₀, rfl, ?_, ?_, ?_⟩
    · rw [hpend₀]; rfl
    · intro c; rw [hpend₀]; rfl
    · rw [hpend₀]; simp
  | @tail u₀ u₁ _ hstep ih =>
    obtain ⟨W', hin, hv, hcorr, hwf, hcfg, htin, htout, hto, hassets⟩ := ih
    have hreg : NativeTokenVault.Registered W'.vault cfg.assetId := by rw [hv]; exact hregf
    have hfor : ¬ NativeTokenVault.Native thisChain W'.vault cfg.assetId := by
      rw [hv]; exact hforf
    cases hstep with
    | @prepare r out hp =>
      obtain ⟨hwf', hcfg', _, _, _⟩ := NativeTokenVaultBase.preparation_preserves_ledger hwf hp
      have hra : r.assetId = cfg.assetId :=
        (NativeTokenVaultBase.preparation_asset_binding hwf hp).1.trans (by rw [hcfg])
      have hamt_eq : out.data.amount = r.data.amount :=
        (NativeTokenVaultBase.preparation_payload hwf hp).2.2.2.1
      have hamt : r.data.amount.val ≠ 0 := by
        intro h0
        apply (NativeTokenVaultBase.preparation_backed hwf hp).2.2.2
        rw [hamt_eq]
        exact Fin.ext h0
      obtain ⟨_, _, _, hcorr'⟩ :=
        NativeTokenVaultBase.preparationIsForeignBridgeOut (W := Wf) e hcorr hwf.2 hp
      have hguard : NativeTokenVault.FlowOutGuard W'.vault r.assetId r.data.amount.val :=
        ⟨by rw [hra]; exact hreg, hamt⟩
      refine ⟨NativeTokenVault.bridgeOut thisChain W' r.destinationChain r.assetId
          r.data.amount.val,
        NativeTokenVault.ReachIn.tail hin (NativeTokenVault.StepIn.bridgeOut hguard), ?_,
        hcorr', hwf', hcfg'.trans hcfg, ?_, ?_, ?_, ?_⟩
      · rw [NativeTokenVault.bridgeOut_vault_foreign _ _ _ _ _ (by rw [hra]; exact hfor), hv]
      · rw [NativeTokenVault.bridgeOut_totalIn]
        exact htin
      · change (NativeTokenVault.upd W'.audit.totalOut r.assetId
            (W'.audit.totalOut r.assetId + r.data.amount.val)) cfg.assetId =
          Wf.audit.totalOut cfg.assetId + pendingAmount (u₀.pending ++ [obligation r out.data])
        rw [hra, NativeTokenVault.upd_same, pendingAmount_append_one, htout]
        simp only [obligation, hamt_eq]
        omega
      · intro c
        change (NativeTokenVault.updCA W'.audit.outTo r.destinationChain r.assetId
            (W'.audit.outTo r.destinationChain r.assetId + r.data.amount.val)) c cfg.assetId =
          Wf.audit.outTo c cfg.assetId + pendingAmountTo c (u₀.pending ++ [obligation r out.data])
        rw [hra, pendingAmountTo_append_one]
        simp only [obligation, hamt_eq]
        by_cases hc : r.destinationChain = c
        · subst hc
          rw [NativeTokenVault.updCA_same, hto, ite_eq_left rfl]
          omega
        · rw [NativeTokenVault.updCA_ne _ _ (fun h => hc h.1.symm), hto, ite_eq_right hc]
          omega
      · intro o ho
        rcases List.mem_append.mp ho with ho | ho
        · exact hassets o ho
        · rw [List.mem_singleton] at ho
          rw [ho]
          exact hra
    | @spend owner recipient amount token htr =>
      obtain ⟨hl, _, htcfg⟩ := BridgedStandardERC20.transfer_preserves_ledger hwf.1 htr
      exact ⟨W', hin, hv, NativeTokenVaultBase.corr_with_token hcorr htcfg,
        NativeTokenVaultBase.wellFormed_with_token hwf hl htcfg, hcfg, htin, htout, hto,
        hassets⟩

theorem tightTraceIsRegistryOutflow
    {initHooks : NativeTokenVaultBase.RegistrationHooks Accounting}
    {start : NativeTokenVaultBase.RegistrationState Accounting}
    {origin : NativeTokenVaultBase.Address} {registered : NativeTokenVaultBase.Registered Accounting}
    {fundedToken : BridgedStandardERC20.State} {hooks : NativeTokenVaultBase.Hooks Accounting}
    {t : Ledger Accounting} {e : NativeTokenVault.NtvAssetId}
    {S : Set (NativeTokenVault.Chain × NativeTokenVault.Address)}
    {thisChain : NativeTokenVault.Chain} {W : NativeTokenVault.World}
    (he : NativeTokenVault.IdAssumptionsOn e S) (hc0 : thisChain ≠ 0)
    (hW : NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W)
    (hmem : (start.config.originChainId, NativeTokenVaultBase.widen origin) ∈ S)
    (hc : NativeTokenVaultBase.CorrPre start thisChain W.vault)
    (h : NativeTokenVaultBase.registerFreshBranch' initHooks start origin = some registered)
    (henc : initHooks.assetIdFor start.config.originChainId origin =
      e start.config.originChainId (NativeTokenVaultBase.widen origin))
    (ht : BridgedStandardERC20.Reach registered.state.token fundedToken)
    (hp : Reach hooks ⟨{ registered.state with token := fundedToken }, []⟩ t) :
    ∃ Wf W' : NativeTokenVault.World,
      NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty Wf
      ∧ NativeTokenVault.ReachIn e thisChain S Wf W'
      ∧ Wf.vault = NativeTokenVaultBase.correspondingRegistration start origin W.vault
      ∧ W'.vault = Wf.vault
      ∧ NativeTokenVaultBase.Corr t.vault thisChain W'.vault
      ∧ NativeTokenVault.Valid e thisChain W'.vault
      ∧ NativeTokenVaultBase.WellFormed t.vault
      ∧ fundedToken.totalSupply + Wf.audit.totalOut start.config.assetId
          = Wf.audit.totalIn start.config.assetId
      ∧ W'.audit.totalIn start.config.assetId = Wf.audit.totalIn start.config.assetId
      ∧ W'.audit.totalOut start.config.assetId
          = Wf.audit.totalOut start.config.assetId + pendingAmount t.pending
      ∧ (∀ c, W'.audit.outTo c start.config.assetId
          = Wf.audit.outTo c start.config.assetId + pendingAmountTo c t.pending)
      ∧ (∀ o ∈ t.pending, o.assetId = start.config.assetId)
      ∧ t.vault.token.totalSupply + pendingAmount t.pending = fundedToken.totalSupply := by
  -- registration and funding, by the lifecycle simulation
  have hrun := token_reach_repReach (hooks := hooks) ht registered.state rfl
  obtain ⟨Wf, hinf, _, hvf, hcorrf, hvalf, hwff, hsumf⟩ :=
    NativeTokenVaultBase.unifiedLifecycleCorresponds he hc0 hW hmem hc h henc hrun
  -- the registry write: the tracked asset is registered and not native
  obtain ⟨hg', _, _⟩ := NativeTokenVaultBase.unifiedRegistrationIsRegistryStep (W := W) hc h henc
  have hregf : NativeTokenVault.Registered Wf.vault start.config.assetId := by
    rw [hvf]
    exact (NativeTokenVault.sn_registered_self _ _ _ _ _).mpr hg'.tokenNonzero
  have hforf : ¬ NativeTokenVault.Native thisChain Wf.vault start.config.assetId := by
    rw [hvf]
    exact fun hn => hg'.notNative ((NativeTokenVault.sn_native_self _ _ _ _ _ thisChain).mp hn)
  have hfresh := (NativeTokenVaultBase.registerFreshBranch'_eq_some.mp h).1
  have hcfg₀ : registered.state.config = start.config :=
    (NativeTokenVaultBase.registration_registry_frame
      (NativeTokenVaultBase.fresh_registration_preconditions hfresh).2).1
  -- the trace
  obtain ⟨W', hin', hv', hcorr', hwf', _, htin, htout, hto, hassets⟩ :=
    trace_outflow (e := e) (S := S) (cfg := start.config) hregf hforf hp hcorrf hwff hcfg₀ rfl
  have hsupply := (initialized_preparation_trace hfresh ht hp).2.2
  refine ⟨Wf, W', hinf, hin', hvf, hv', ?_, ?_, hwf', hsumf, htin, htout, hto, hassets, hsupply⟩
  · rw [hv']
    exact hcorr'
  · rw [hv']
    exact hvalf

theorem TightTraceIsRegistryOutflow : Properties.TightTraceIsRegistryOutflow :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ he hc0 hW hmem hc h henc ht hp =>
    tightTraceIsRegistryOutflow he hc0 hW hmem hc h henc ht hp

theorem TightTraceIsRegistryOutflowSatisfiable :
    Properties.TightTraceIsRegistryOutflowSatisfiable := by
  open NativeTokenVaultBase in
  have hg0 : NativeTokenVault.RegisterNativeGuard NativeTokenVault.empty.vault (widen 9) :=
    ⟨fun h0 => absurd (widen_eq_zero.mp h0) (by decide), rfl⟩
  have hW₀ : NativeTokenVault.ReachIn toyId 1 witnessPairs NativeTokenVault.empty
      ⟨nativeVault 9, NativeTokenVault.empty.audit⟩ :=
    NativeTokenVault.ReachIn.tail NativeTokenVault.ReachIn.refl
      (NativeTokenVault.StepIn.registerNative (Or.inl rfl) hg0)
  have hfund : BridgedStandardERC20.Reach witnessRegistered.state.token witnessToken :=
    BridgedStandardERC20.Reach.tail BridgedStandardERC20.Reach.refl
      (BridgedStandardERC20.Step.mint witness_mint)
  obtain ⟨out, hout⟩ := witness_prepare
  have htrace : Reach witnessPrepHooks ⟨{ witnessRegistered.state with token := witnessToken }, []⟩
      ⟨out.state, [] ++ [obligation witnessRequest out.data]⟩ :=
    Reach.tail Reach.refl (Step.prepare (s := ⟨witnessPrepState, []⟩) hout)
  exact ⟨toyHooks 5, witnessState, 7, witnessRegistered, witnessToken, witnessPrepHooks,
    ⟨out.state, [] ++ [obligation witnessRequest out.data]⟩, toyId, witnessPairs, 1,
    ⟨nativeVault 9, NativeTokenVault.empty.audit⟩, witnessPairs_on, by decide, hW₀, Or.inr rfl,
    ⟨rfl, nativeRegistry_corr 9⟩, witness_freshBranch', rfl, hfund, htrace, by simp⟩

end AssetBridgePreparation
