import EraSpec.Contracts.NativeTokenVaultBase.Properties.RegistrationUnifiedStrong
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.RegistrationUnified

/-!
# Proofs: the lifecycle correspondence, tied to the logged run

`lifecycleRel_stepOp` is `lifecycleRel_step` (`Proofs/RegistrationUnified.lean`) with
the matched registry step named: from states related by `LifecycleRel`, a logged
representation step is matched by the logged registry run whose log is its
`registryOp` (empty or one flow), and the flows it records are the step's amounts.
`lifecycleRel_reachLog` iterates it along a `LifecycleReachLog`.  The main theorem
starts that iteration at the registration (`registration_lifecycleRel`), reads the
asset's flows before registration off `Audited.unregisteredQuiet`, and gets
universality from `NativeTokenVault.reachLog_det`.  `unifiedLifecycleCorresponds_of_traced`
rederives `Properties.UnifiedLifecycleCorresponds` from it, so the new form is the
stronger one.  The freeness of the existential form adds one flow step to
`unifiedLifecycleCorresponds`'s world.  The witness reuses the run of
`UnifiedLifecycleSatisfiable`.
-/

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain World NtvAssetId Valid IdAssumptionsOn)

variable {Accounting : Type}

/-! ## Runs of the registry model, composed -/

theorem lifecycle_reachLog_append {e : NtvAssetId} {thisChain : Chain} {W X Y : World}
    {l₁ l₂ : List NativeTokenVault.Op} (h₁ : NativeTokenVault.ReachLog e thisChain W X l₁)
    (h₂ : NativeTokenVault.ReachLog e thisChain X Y l₂) :
    NativeTokenVault.ReachLog e thisChain W Y (l₁ ++ l₂) := by
  induction h₂ with
  | refl => rw [List.append_nil]; exact h₁
  | tail _ hs ih =>
    rw [← List.append_assoc]
    exact NativeTokenVault.ReachLog.tail ih hs

theorem lifecycle_reachIn_trans {e : NtvAssetId} {thisChain : Chain}
    {S : Set (Chain × NativeTokenVault.Address)} {W X Y : World}
    (h₁ : NativeTokenVault.ReachIn e thisChain S W X)
    (h₂ : NativeTokenVault.ReachIn e thisChain S X Y) :
    NativeTokenVault.ReachIn e thisChain S W Y := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact NativeTokenVault.ReachIn.tail ih hs

theorem lifecycle_reach'_trans {e : NtvAssetId} {thisChain : Chain} {W X Y : World}
    (h₁ : NativeTokenVault.Reach' e thisChain W X) (h₂ : NativeTokenVault.Reach' e thisChain X Y) :
    NativeTokenVault.Reach' e thisChain W Y := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hs ih => exact NativeTokenVault.Reach'.tail ih hs

/-! ## The logged run's bookkeeping -/

theorem lifecycleRegistryLog_snoc (a : NativeTokenVault.AssetId) (c : Chain)
    (trace : List LifecycleOp) (o : LifecycleOp) :
    lifecycleRegistryLog a c (trace ++ [o]) =
      lifecycleRegistryLog a c trace ++ (o.registryOp a c).toList := by
  cases h : o.registryOp a c <;> simp [lifecycleRegistryLog, h]

theorem lifecycleOutTotal_snoc (trace : List LifecycleOp) (o : LifecycleOp) :
    lifecycleOutTotal (trace ++ [o]) = lifecycleOutTotal trace + o.outAmount := by
  simp [lifecycleOutTotal]

theorem lifecycleInTotal_snoc (trace : List LifecycleOp) (o : LifecycleOp) :
    lifecycleInTotal (trace ++ [o]) = lifecycleInTotal trace + o.inAmount := by
  simp [lifecycleInTotal]

/-! ## Logging loses no run -/

theorem lifecycleStepOp_repStep {hooks : Hooks Accounting} {o : LifecycleOp}
    {s u : State Accounting} (h : LifecycleStepOp hooks o s u) : RepStep hooks s u := by
  cases h with
  | prepared hp => exact RepStep.prepared hp
  | burn hb => exact RepStep.tokenOp (BridgedStandardERC20.Step.burn hb)
  | mint hm => exact RepStep.tokenOp (BridgedStandardERC20.Step.mint hm)
  | transfer ht => exact RepStep.tokenOp (BridgedStandardERC20.Step.transfer ht)

theorem repStep_lifecycleStepOp {hooks : Hooks Accounting} {s u : State Accounting}
    (h : RepStep hooks s u) : ∃ o, LifecycleStepOp hooks o s u := by
  cases h with
  | prepared hp => exact ⟨_, LifecycleStepOp.prepared hp⟩
  | tokenOp hs =>
    cases hs with
    | burn hb => exact ⟨_, LifecycleStepOp.burn hb⟩
    | mint hm => exact ⟨_, LifecycleStepOp.mint hm⟩
    | transfer ht => exact ⟨_, LifecycleStepOp.transfer ht⟩

theorem lifecycleReachLog_repReach {hooks : Hooks Accounting} {s t : State Accounting}
    {trace : List LifecycleOp} (h : LifecycleReachLog hooks s t trace) : RepReach hooks s t := by
  induction h with
  | refl => exact RepReach.refl
  | tail _ hs ih => exact RepReach.tail ih (lifecycleStepOp_repStep hs)

theorem repReach_lifecycleReachLog {hooks : Hooks Accounting} {s t : State Accounting}
    (h : RepReach hooks s t) : ∃ trace, LifecycleReachLog hooks s t trace := by
  induction h with
  | refl => exact ⟨[], LifecycleReachLog.refl⟩
  | tail _ hs ih =>
    obtain ⟨trace, hl⟩ := ih
    obtain ⟨o, ho⟩ := repStep_lifecycleStepOp hs
    exact ⟨trace ++ [o], LifecycleReachLog.tail hl ho⟩

theorem LifecycleRepReachIffReachLog : Properties.LifecycleRepReachIffReachLog :=
  fun _ _ _ _ => ⟨repReach_lifecycleReachLog, fun ⟨_, h⟩ => lifecycleReachLog_repReach h⟩

/-! ## The supply along a logged run -/

/-- One logged step keeps `WellFormed` and the configuration, and moves the supply by
its amounts. -/
theorem lifecycleStepOp_supply {hooks : Hooks Accounting} {o : LifecycleOp}
    {s u : State Accounting} (hw : WellFormed s) (h : LifecycleStepOp hooks o s u) :
    WellFormed u ∧ u.config = s.config
      ∧ u.token.totalSupply + o.outAmount = s.token.totalSupply + o.inAmount := by
  cases h with
  | @prepared _ r out hp =>
    obtain ⟨hwf', hcfg', _, _, _⟩ := preparation_preserves_ledger hw hp
    obtain ⟨_, _, hsupply, _⟩ := preparation_backed hw hp
    have hamt_eq : out.data.amount = r.data.amount := (preparation_payload hw hp).2.2.2.1
    refine ⟨hwf', hcfg', ?_⟩
    change out.state.token.totalSupply + r.data.amount.val = s.token.totalSupply + 0
    rw [← hamt_eq]
    omega
  | @burn _ token caller owner amount hb =>
    obtain ⟨_, _, _, hsupply, _, htcfg⟩ := BridgedStandardERC20.burn_exact hw.1 hb
    refine ⟨wellFormed_with_token hw (BridgedStandardERC20.burn_preserves_ledger hw.1 hb) htcfg,
      rfl, ?_⟩
    change token.totalSupply + amount.val = s.token.totalSupply + 0
    omega
  | @mint _ token caller recipient amount hm =>
    obtain ⟨_, _, _, hsupply, _, htcfg⟩ := BridgedStandardERC20.mint_exact hm
    refine ⟨wellFormed_with_token hw (BridgedStandardERC20.mint_preserves_ledger hw.1 hm) htcfg,
      rfl, ?_⟩
    change token.totalSupply + 0 = s.token.totalSupply + amount.val
    omega
  | @transfer _ token owner recipient amount ht =>
    obtain ⟨hl, hsupply, htcfg⟩ := BridgedStandardERC20.transfer_preserves_ledger hw.1 ht
    refine ⟨wellFormed_with_token hw hl htcfg, rfl, ?_⟩
    change token.totalSupply + 0 = s.token.totalSupply + 0
    omega

theorem lifecycleLoggedSupply {hooks : Hooks Accounting} {s t : State Accounting}
    {trace : List LifecycleOp} (hw : WellFormed s) (h : LifecycleReachLog hooks s t trace) :
    WellFormed t ∧ t.config = s.config
      ∧ t.token.totalSupply + lifecycleOutTotal trace
          = s.token.totalSupply + lifecycleInTotal trace := by
  induction h with
  | refl => exact ⟨hw, rfl, by simp [lifecycleOutTotal, lifecycleInTotal]⟩
  | @tail t₁ t₂ trace o _ hs ih =>
    obtain ⟨hw₁, hcfg₁, hsum₁⟩ := ih
    obtain ⟨hw₂, hcfg₂, hsum₂⟩ := lifecycleStepOp_supply hw₁ hs
    refine ⟨hw₂, hcfg₂.trans hcfg₁, ?_⟩
    rw [lifecycleOutTotal_snoc, lifecycleInTotal_snoc]
    omega

theorem LifecycleLoggedSupply : Properties.LifecycleLoggedSupply :=
  fun _ _ _ _ _ hw h => lifecycleLoggedSupply hw h

/-! ## One logged step, matched -/

/-- **One logged step of the lifecycle simulation.**  `lifecycleRel_step`, with the
matched registry step named by the logged operation's `registryOp`: the registry run
from `W` with that (empty or one-flow) log ends in a world related to the new state,
with the same vault, and the asset's recorded flows grow by exactly the step's amounts
(other assets' total outflow and inflow unchanged). -/
theorem lifecycleRel_stepOp {hooks : Hooks Accounting} {e : NtvAssetId} {thisChain : Chain}
    (c : Chain) {u u' : State Accounting} {W : World} {o : LifecycleOp}
    (hrel : LifecycleRel thisChain u W) (hstep : LifecycleStepOp hooks o u u') :
    ∃ W' : World,
      NativeTokenVault.ReachLog e thisChain W W' (o.registryOp u.config.assetId c).toList
      ∧ (∀ S, NativeTokenVault.ReachIn e thisChain S W W')
      ∧ NativeTokenVault.Reach' e thisChain W W'
      ∧ W'.vault = W.vault ∧ u'.config = u.config ∧ LifecycleRel thisChain u' W'
      ∧ W'.audit.totalOut u.config.assetId = W.audit.totalOut u.config.assetId + o.outAmount
      ∧ W'.audit.totalIn u.config.assetId = W.audit.totalIn u.config.assetId + o.inAmount
      ∧ ∀ b, b ≠ u.config.assetId →
          W'.audit.totalOut b = W.audit.totalOut b ∧ W'.audit.totalIn b = W.audit.totalIn b := by
  obtain ⟨hcorr, hwf, hreg, hfor, hsum⟩ := hrel
  cases hstep with
  | @prepared _ r out hp =>
    obtain ⟨hwf', hcfg', _, _, _⟩ := preparation_preserves_ledger hwf hp
    obtain ⟨_, _, hsupply, hamt0⟩ := preparation_backed hwf hp
    have hamt_eq : out.data.amount = r.data.amount := (preparation_payload hwf hp).2.2.2.1
    have hamt : r.data.amount.val ≠ 0 := by
      intro h0
      apply hamt0
      rw [hamt_eq]
      exact Fin.ext h0
    obtain ⟨_, _, _, hcorr'⟩ := preparationIsForeignBridgeOut e hcorr hwf.2 hp
    have hguard : NativeTokenVault.FlowOutGuard W.vault u.config.assetId r.data.amount.val :=
      ⟨hreg, hamt⟩
    have hvault := NativeTokenVault.bridgeOut_vault_foreign thisChain W r.destinationChain
      u.config.assetId r.data.amount.val hfor
    refine ⟨NativeTokenVault.bridgeOut thisChain W r.destinationChain u.config.assetId
        r.data.amount.val,
      NativeTokenVault.ReachLog.tail (log := []) NativeTokenVault.ReachLog.refl
        (NativeTokenVault.StepOp.bridgeOut hguard),
      fun _ => NativeTokenVault.ReachIn.tail NativeTokenVault.ReachIn.refl
        (NativeTokenVault.StepIn.bridgeOut hguard),
      NativeTokenVault.Reach'.tail NativeTokenVault.Reach'.refl
        (NativeTokenVault.Step'.bridgeOut hguard),
      hvault, hcfg', ⟨by rw [hvault]; exact hcorr', hwf', ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [hvault, hcfg']
      exact hreg
    · rw [hvault, hcfg']
      exact hfor
    · rw [hcfg', NativeTokenVault.bridgeOut_totalOut, NativeTokenVault.bridgeOut_totalIn,
        NativeTokenVault.upd_same]
      rw [hamt_eq] at hsupply
      omega
    · rw [NativeTokenVault.bridgeOut_totalOut, NativeTokenVault.upd_same]
      rfl
    · rw [NativeTokenVault.bridgeOut_totalIn]
      rfl
    · intro b hb
      rw [NativeTokenVault.bridgeOut_totalOut, NativeTokenVault.bridgeOut_totalIn,
        NativeTokenVault.upd_ne _ _ hb]
      exact ⟨rfl, rfl⟩
  | @burn _ token caller owner amount hb =>
    obtain ⟨_, _, _, hsupply, _, htcfg⟩ := BridgedStandardERC20.burn_exact hwf.1 hb
    have hwf' := wellFormed_with_token hwf
      (BridgedStandardERC20.burn_preserves_ledger hwf.1 hb) htcfg
    have hcorr' := corr_with_token hcorr htcfg
    by_cases hamt : amount.val = 0
    · have hop : (LifecycleOp.burn caller owner amount).registryOp u.config.assetId c = none :=
        ite_eq_left hamt
      refine ⟨W, by rw [hop]; exact NativeTokenVault.ReachLog.refl,
        fun _ => NativeTokenVault.ReachIn.refl, NativeTokenVault.Reach'.refl, rfl, rfl,
        ⟨hcorr', hwf', hreg, hfor, ?_⟩, ?_, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
      · change token.totalSupply + W.audit.totalOut u.config.assetId =
          W.audit.totalIn u.config.assetId
        omega
      · change W.audit.totalOut u.config.assetId = W.audit.totalOut u.config.assetId + amount.val
        omega
      · change W.audit.totalIn u.config.assetId = W.audit.totalIn u.config.assetId + 0
        omega
    · have hop : (LifecycleOp.burn caller owner amount).registryOp u.config.assetId c =
          some (.bridgeOut c u.config.assetId amount.val) := ite_eq_right hamt
      have hguard : NativeTokenVault.FlowOutGuard W.vault u.config.assetId amount.val :=
        ⟨hreg, hamt⟩
      have hvault := NativeTokenVault.bridgeOut_vault_foreign thisChain W c u.config.assetId
        amount.val hfor
      have hlog : NativeTokenVault.ReachLog e thisChain W
          (NativeTokenVault.bridgeOut thisChain W c u.config.assetId amount.val)
          ((LifecycleOp.burn caller owner amount).registryOp u.config.assetId c).toList := by
        rw [hop]
        exact NativeTokenVault.ReachLog.tail (log := []) NativeTokenVault.ReachLog.refl
          (NativeTokenVault.StepOp.bridgeOut hguard)
      refine ⟨NativeTokenVault.bridgeOut thisChain W c u.config.assetId amount.val, hlog,
        fun _ => NativeTokenVault.ReachIn.tail NativeTokenVault.ReachIn.refl
          (NativeTokenVault.StepIn.bridgeOut hguard),
        NativeTokenVault.Reach'.tail NativeTokenVault.Reach'.refl
          (NativeTokenVault.Step'.bridgeOut hguard),
        hvault, rfl, ⟨by rw [hvault]; exact hcorr', hwf', by rw [hvault]; exact hreg,
          by rw [hvault]; exact hfor, ?_⟩, ?_, ?_, ?_⟩
      · change token.totalSupply + (NativeTokenVault.bridgeOut thisChain W c u.config.assetId
            amount.val).audit.totalOut u.config.assetId =
          (NativeTokenVault.bridgeOut thisChain W c u.config.assetId amount.val).audit.totalIn
            u.config.assetId
        rw [NativeTokenVault.bridgeOut_totalOut, NativeTokenVault.bridgeOut_totalIn,
          NativeTokenVault.upd_same]
        omega
      · rw [NativeTokenVault.bridgeOut_totalOut, NativeTokenVault.upd_same]
        rfl
      · rw [NativeTokenVault.bridgeOut_totalIn]
        rfl
      · intro b hb
        rw [NativeTokenVault.bridgeOut_totalOut, NativeTokenVault.bridgeOut_totalIn,
          NativeTokenVault.upd_ne _ _ hb]
        exact ⟨rfl, rfl⟩
  | @mint _ token caller recipient amount hm =>
    obtain ⟨_, _, _, hsupply, _, htcfg⟩ := BridgedStandardERC20.mint_exact hm
    have hwf' := wellFormed_with_token hwf
      (BridgedStandardERC20.mint_preserves_ledger hwf.1 hm) htcfg
    have hcorr' := corr_with_token hcorr htcfg
    have hguard : NativeTokenVault.FlowInGuard thisChain W.vault u.config.assetId amount.val :=
      ⟨hreg, fun hn => absurd hn hfor⟩
    have hvault := NativeTokenVault.bridgeIn_vault_foreign thisChain W c u.config.assetId
      amount.val hfor
    refine ⟨NativeTokenVault.bridgeIn thisChain W c u.config.assetId amount.val,
      NativeTokenVault.ReachLog.tail (log := []) NativeTokenVault.ReachLog.refl
        (NativeTokenVault.StepOp.bridgeIn hguard),
      fun _ => NativeTokenVault.ReachIn.tail NativeTokenVault.ReachIn.refl
        (NativeTokenVault.StepIn.bridgeIn hguard),
      NativeTokenVault.Reach'.tail NativeTokenVault.Reach'.refl
        (NativeTokenVault.Step'.bridgeIn hguard),
      hvault, rfl, ⟨by rw [hvault]; exact hcorr', hwf', by rw [hvault]; exact hreg,
        by rw [hvault]; exact hfor, ?_⟩, ?_, ?_, ?_⟩
    · change token.totalSupply + (NativeTokenVault.bridgeIn thisChain W c u.config.assetId
          amount.val).audit.totalOut u.config.assetId =
        (NativeTokenVault.bridgeIn thisChain W c u.config.assetId amount.val).audit.totalIn
          u.config.assetId
      rw [NativeTokenVault.bridgeIn_totalOut, NativeTokenVault.bridgeIn_totalIn,
        NativeTokenVault.upd_same]
      omega
    · rw [NativeTokenVault.bridgeIn_totalOut]
      rfl
    · rw [NativeTokenVault.bridgeIn_totalIn, NativeTokenVault.upd_same]
      rfl
    · intro b hb
      rw [NativeTokenVault.bridgeIn_totalOut, NativeTokenVault.bridgeIn_totalIn,
        NativeTokenVault.upd_ne _ _ hb]
      exact ⟨rfl, rfl⟩
  | @transfer _ token owner recipient amount ht =>
    obtain ⟨hl, hsupply, htcfg⟩ := BridgedStandardERC20.transfer_preserves_ledger hwf.1 ht
    refine ⟨W, NativeTokenVault.ReachLog.refl, fun _ => NativeTokenVault.ReachIn.refl,
      NativeTokenVault.Reach'.refl, rfl, rfl,
      ⟨corr_with_token hcorr htcfg, wellFormed_with_token hwf hl htcfg, hreg, hfor, ?_⟩,
      ?_, ?_, fun _ _ => ⟨rfl, rfl⟩⟩
    · change token.totalSupply + W.audit.totalOut u.config.assetId =
        W.audit.totalIn u.config.assetId
      omega
    · change W.audit.totalOut u.config.assetId = W.audit.totalOut u.config.assetId + 0
      omega
    · change W.audit.totalIn u.config.assetId = W.audit.totalIn u.config.assetId + 0
      omega

/-- **A logged run, matched.**  `lifecycleRel_stepOp` along a `LifecycleReachLog`: the
registry run from `W` whose log is the run's `lifecycleRegistryLog` ends in a world
related to the run's end, with the same vault, recording the run's totals for the
tracked asset and nothing for any other. -/
theorem lifecycleRel_reachLog {hooks : Hooks Accounting} {e : NtvAssetId} {thisChain : Chain}
    (c : Chain) {u t : State Accounting} {W : World} {trace : List LifecycleOp}
    (hrel : LifecycleRel thisChain u W) (hrun : LifecycleReachLog hooks u t trace) :
    ∃ W' : World,
      NativeTokenVault.ReachLog e thisChain W W' (lifecycleRegistryLog u.config.assetId c trace)
      ∧ (∀ S, NativeTokenVault.ReachIn e thisChain S W W')
      ∧ NativeTokenVault.Reach' e thisChain W W'
      ∧ W'.vault = W.vault ∧ t.config = u.config ∧ LifecycleRel thisChain t W'
      ∧ W'.audit.totalOut u.config.assetId
          = W.audit.totalOut u.config.assetId + lifecycleOutTotal trace
      ∧ W'.audit.totalIn u.config.assetId
          = W.audit.totalIn u.config.assetId + lifecycleInTotal trace
      ∧ ∀ b, b ≠ u.config.assetId →
          W'.audit.totalOut b = W.audit.totalOut b ∧ W'.audit.totalIn b = W.audit.totalIn b := by
  induction hrun with
  | refl =>
    exact ⟨W, NativeTokenVault.ReachLog.refl, fun _ => NativeTokenVault.ReachIn.refl,
      NativeTokenVault.Reach'.refl, rfl, rfl, hrel, by simp [lifecycleOutTotal],
      by simp [lifecycleInTotal], fun _ _ => ⟨rfl, rfl⟩⟩
  | @tail t₁ t₂ trace o _ hs ih =>
    obtain ⟨W₁, hlog₁, hin₁, hti₁, hv₁, hcfg₁, hrel₁, hout₁, hinn₁, hframe₁⟩ := ih
    obtain ⟨W₂, hlog₂, hin₂, hti₂, hv₂, hcfg₂, hrel₂, hout₂, hinn₂, hframe₂⟩ :=
      lifecycleRel_stepOp (e := e) c hrel₁ hs
    rw [hcfg₁] at hlog₂ hout₂ hinn₂ hframe₂
    refine ⟨W₂, ?_, fun S => lifecycle_reachIn_trans (hin₁ S) (hin₂ S),
      lifecycle_reach'_trans hti₁ hti₂, hv₂.trans hv₁, hcfg₂.trans hcfg₁, hrel₂, ?_, ?_, ?_⟩
    · rw [lifecycleRegistryLog_snoc]
      exact lifecycle_reachLog_append hlog₁ hlog₂
    · rw [hout₂, hout₁, lifecycleOutTotal_snoc]
      omega
    · rw [hinn₂, hinn₁, lifecycleInTotal_snoc]
      omega
    · intro b hb
      obtain ⟨h₁, h₂⟩ := hframe₂ b hb
      obtain ⟨h₃, h₄⟩ := hframe₁ b hb
      exact ⟨h₁.trans h₃, h₂.trans h₄⟩

/-! ## The lifecycle correspondence, tied to the trace -/

theorem unifiedLifecycleTraced {rhooks : RegistrationHooks Accounting}
    {hooks : Hooks Accounting} {s : RegistrationState Accounting} {origin : Address}
    {reg : Registered Accounting} {t : State Accounting} {trace : List LifecycleOp}
    {e : NtvAssetId} {S : Set (Chain × NativeTokenVault.Address)} {thisChain : Chain}
    (c : Chain) {W : World}
    (he : IdAssumptionsOn e S) (hc0 : thisChain ≠ 0)
    (hW : NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W)
    (hmem : (s.config.originChainId, widen origin) ∈ S)
    (hc : CorrPre s thisChain W.vault) (h : registerFreshBranch' rhooks s origin = some reg)
    (henc : rhooks.assetIdFor s.config.originChainId origin =
      e s.config.originChainId (widen origin))
    (hrun : LifecycleReachLog hooks reg.state t trace) :
    (∃ W' : World, NativeTokenVault.ReachLog e thisChain
        { W with vault := correspondingRegistration s origin W.vault } W'
        (lifecycleRegistryLog s.config.assetId c trace))
    ∧ ∀ W' : World, NativeTokenVault.ReachLog e thisChain
        { W with vault := correspondingRegistration s origin W.vault } W'
        (lifecycleRegistryLog s.config.assetId c trace) →
      NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W'
      ∧ (NativeTokenVault.Reach' e thisChain NativeTokenVault.empty W →
          NativeTokenVault.Reach' e thisChain NativeTokenVault.empty W')
      ∧ W'.vault = correspondingRegistration s origin W.vault
      ∧ Corr t thisChain W'.vault ∧ Valid e thisChain W'.vault ∧ WellFormed t
      ∧ W'.audit.totalOut s.config.assetId = lifecycleOutTotal trace
      ∧ W'.audit.totalIn s.config.assetId = lifecycleInTotal trace
      ∧ t.token.totalSupply + lifecycleOutTotal trace = lifecycleInTotal trace
      ∧ (∀ n : ℕ, n + W'.audit.totalOut s.config.assetId = W'.audit.totalIn s.config.assetId
          ↔ n = t.token.totalSupply)
      ∧ ∀ b, b ≠ s.config.assetId →
          W'.audit.totalOut b = W.audit.totalOut b ∧ W'.audit.totalIn b = W.audit.totalIn b := by
  -- the registration, as a bounded and tightened registry step
  obtain ⟨hg', hstep', _⟩ := unifiedRegistrationIsRegistryStep (W := W) hc h henc
  have hinner := (fresh_registration_preconditions (registerFreshBranch'_eq_some.mp h).1).2
  have hcfg₀ : reg.state.config = s.config := (registration_registry_frame hinner).1
  have hW₁ : NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty
      { W with vault := correspondingRegistration s origin W.vault } :=
    NativeTokenVault.ReachIn.tail hW
      (NativeTokenVault.StepIn.registerBridged hmem hg'.toRegisterBridgedGuard)
  -- the asset was unregistered before, so the audit had recorded no flow of it
  have hquiet := (NativeTokenVault.run_audited_on he hc0 hW).unregisteredQuiet
    s.config.assetId hg'.freshId
  -- the matched run of the logged trace, from the registration's world
  obtain ⟨W', hlog, hin, hti, hv, hcfg, hrel, hout, hinn, hframe⟩ :=
    lifecycleRel_reachLog (e := e) c (registration_lifecycleRel he hc0 hW hc h henc) hrun
  rw [hcfg₀] at hlog hout hinn hframe hcfg
  have hout' : W'.audit.totalOut s.config.assetId = lifecycleOutTotal trace := by
    have h' : W'.audit.totalOut s.config.assetId =
        W.audit.totalOut s.config.assetId + lifecycleOutTotal trace := hout
    rw [h', hquiet.2, Nat.zero_add]
  have hinn' : W'.audit.totalIn s.config.assetId = lifecycleInTotal trace := by
    have h' : W'.audit.totalIn s.config.assetId =
        W.audit.totalIn s.config.assetId + lifecycleInTotal trace := hinn
    rw [h', hquiet.1, Nat.zero_add]
  have hsum : t.token.totalSupply + W'.audit.totalOut s.config.assetId =
      W'.audit.totalIn s.config.assetId := by
    have h' := hrel.supply
    rw [hcfg] at h'
    exact h'
  have hinW' : NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W' :=
    lifecycle_reachIn_trans hW₁ (hin S)
  refine ⟨⟨W', hlog⟩, fun W'' hlog'' => ?_⟩
  obtain rfl := NativeTokenVault.reachLog_det hlog'' hlog
  refine ⟨hinW', fun h' => lifecycle_reach'_trans (NativeTokenVault.Reach'.tail h' hstep') hti,
    hv, hrel.corr, (NativeTokenVault.run_inv_on he hc0 hinW').1, hrel.wellFormed, hout', hinn',
    by rw [← hout', ← hinn']; exact hsum, fun n => ⟨fun hn => by omega, fun hn => by omega⟩,
    fun b hb => hframe b hb⟩

theorem UnifiedLifecycleTraced : Properties.UnifiedLifecycleTraced :=
  fun _ _ _ _ _ _ _ _ _ _ _ c _ he hc0 hW hmem hc h henc hrun =>
    unifiedLifecycleTraced c he hc0 hW hmem hc h henc hrun

/-- **The trace-tied form subsumes the existential one.**  `UnifiedLifecycleCorresponds`
again, now from `UnifiedLifecycleTraced`: log the run (`repReach_lifecycleReachLog`) and
take the matched registry run, with the token model's mints and burns attributed to the
origin chain. -/
theorem unifiedLifecycleCorresponds_of_traced : Properties.UnifiedLifecycleCorresponds := by
  intro _ _ _ s _ _ _ _ _ _ _ he hc0 hW hmem hc h henc hrun
  obtain ⟨_, hlog⟩ := repReach_lifecycleReachLog hrun
  obtain ⟨⟨W', hW'⟩, hall⟩ :=
    unifiedLifecycleTraced s.config.originChainId he hc0 hW hmem hc h henc hlog
  obtain ⟨hin, hti, hv, hcorr, hvalid, hwf, _, _, _, hiff, _⟩ := hall W' hW'
  exact ⟨W', hin, hti, hv, hcorr, hvalid, hwf, (hiff _).mpr rfl⟩

/-! ## The existential form's identity conjunct is free -/

/-- From any world in which the tracked asset is registered and not native, one bounded
and tightened flow step of it (a `bridgeIn` if the recorded inflow does not exceed `n`
plus the recorded outflow, a nonzero `bridgeOut` otherwise) leaves the vault unchanged
and makes `n` plus the recorded outflow equal the recorded inflow. -/
theorem lifecycle_identity_free_step {e : NtvAssetId} {thisChain : Chain}
    {S : Set (Chain × NativeTokenVault.Address)} (W : World) (a : NativeTokenVault.AssetId)
    (n : ℕ) (hreg : NativeTokenVault.Registered W.vault a)
    (hnn : ¬ NativeTokenVault.Native thisChain W.vault a) :
    ∃ W' : World, NativeTokenVault.StepIn e thisChain S W W'
      ∧ NativeTokenVault.Step' e thisChain W W'
      ∧ W'.vault = W.vault ∧ n + W'.audit.totalOut a = W'.audit.totalIn a := by
  by_cases hle : W.audit.totalIn a ≤ n + W.audit.totalOut a
  · have hg : NativeTokenVault.FlowInGuard thisChain W.vault a
        (n + W.audit.totalOut a - W.audit.totalIn a) := ⟨hreg, fun hn => absurd hn hnn⟩
    refine ⟨NativeTokenVault.bridgeIn thisChain W 0 a (n + W.audit.totalOut a - W.audit.totalIn a),
      NativeTokenVault.StepIn.bridgeIn hg, NativeTokenVault.Step'.bridgeIn hg,
      NativeTokenVault.bridgeIn_vault_foreign _ _ _ _ _ hnn, ?_⟩
    rw [NativeTokenVault.bridgeIn_totalOut, NativeTokenVault.bridgeIn_totalIn,
      NativeTokenVault.upd_same]
    omega
  · have hpos : W.audit.totalIn a - n - W.audit.totalOut a ≠ 0 := by omega
    have hg : NativeTokenVault.FlowOutGuard W.vault a
        (W.audit.totalIn a - n - W.audit.totalOut a) := ⟨hreg, hpos⟩
    refine ⟨NativeTokenVault.bridgeOut thisChain W 0 a (W.audit.totalIn a - n - W.audit.totalOut a),
      NativeTokenVault.StepIn.bridgeOut hg, NativeTokenVault.Step'.bridgeOut hg,
      NativeTokenVault.bridgeOut_vault_foreign _ _ _ _ _ hnn, ?_⟩
    rw [NativeTokenVault.bridgeOut_totalOut, NativeTokenVault.bridgeOut_totalIn,
      NativeTokenVault.upd_same]
    omega

theorem unifiedLifecycleSupplyConjunctFree {rhooks : RegistrationHooks Accounting}
    {hooks : Hooks Accounting} {s : RegistrationState Accounting} {origin : Address}
    {reg : Registered Accounting} {t : State Accounting} {e : NtvAssetId}
    {S : Set (Chain × NativeTokenVault.Address)} {thisChain : Chain} {W : World} (n : ℕ)
    (he : IdAssumptionsOn e S) (hc0 : thisChain ≠ 0)
    (hW : NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W)
    (hmem : (s.config.originChainId, widen origin) ∈ S)
    (hc : CorrPre s thisChain W.vault) (h : registerFreshBranch' rhooks s origin = some reg)
    (henc : rhooks.assetIdFor s.config.originChainId origin =
      e s.config.originChainId (widen origin))
    (hrun : RepReach hooks reg.state t) :
    ∃ W' : World,
      NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W'
      ∧ (NativeTokenVault.Reach' e thisChain NativeTokenVault.empty W →
          NativeTokenVault.Reach' e thisChain NativeTokenVault.empty W')
      ∧ W'.vault = correspondingRegistration s origin W.vault
      ∧ Corr t thisChain W'.vault ∧ Valid e thisChain W'.vault ∧ WellFormed t
      ∧ n + W'.audit.totalOut s.config.assetId = W'.audit.totalIn s.config.assetId := by
  obtain ⟨hg', _, _⟩ := unifiedRegistrationIsRegistryStep (W := W) hc h henc
  obtain ⟨W', hin, hti, hv, hcorr, hvalid, hwf, _⟩ :=
    unifiedLifecycleCorresponds he hc0 hW hmem hc h henc hrun
  have hreg : NativeTokenVault.Registered W'.vault s.config.assetId := by
    rw [hv]
    exact (NativeTokenVault.sn_registered_self _ _ _ _ _).mpr hg'.tokenNonzero
  have hfor : ¬ NativeTokenVault.Native thisChain W'.vault s.config.assetId := by
    rw [hv]
    exact fun hn => hg'.notNative ((NativeTokenVault.sn_native_self _ _ _ _ _ thisChain).mp hn)
  obtain ⟨W'', hs, hs', hv', hid⟩ :=
    lifecycle_identity_free_step (e := e) (S := S) W' s.config.assetId n hreg hfor
  exact ⟨W'', NativeTokenVault.ReachIn.tail hin hs,
    fun h' => NativeTokenVault.Reach'.tail (hti h') hs', hv'.trans hv,
    by rw [hv']; exact hcorr, by rw [hv']; exact hvalid, hwf, hid⟩

theorem UnifiedLifecycleSupplyConjunctFree : Properties.UnifiedLifecycleSupplyConjunctFree :=
  fun _ _ _ _ _ _ _ _ _ _ _ n he hc0 hW hmem hc h henc hrun =>
    unifiedLifecycleSupplyConjunctFree n he hc0 hW hmem hc h henc hrun

/-! ## Anti-vacuity

The registry prefix, registration and run of `UnifiedLifecycleSatisfiable`
(`Proofs/RegistrationUnified.lean`), logged: on chain `1` with the toy encoding, native
token `9` registered; then asset `2 + 1` (origin chain `2`, origin token `7`) registered
at the fresh address `5`; then one unit minted to account `11` and prepared towards
chain `4`. -/

theorem UnifiedLifecycleTracedSatisfiable : Properties.UnifiedLifecycleTracedSatisfiable := by
  have hg0 : NativeTokenVault.RegisterNativeGuard NativeTokenVault.empty.vault (widen 9) :=
    ⟨fun h0 => absurd (widen_eq_zero.mp h0) (by decide), rfl⟩
  have hW₀ : NativeTokenVault.ReachIn toyId 1 witnessPairs NativeTokenVault.empty
      ⟨nativeVault 9, NativeTokenVault.empty.audit⟩ :=
    NativeTokenVault.ReachIn.tail NativeTokenVault.ReachIn.refl
      (NativeTokenVault.StepIn.registerNative (Or.inl rfl) hg0)
  obtain ⟨out, hout⟩ := witness_prepare
  have hlog : LifecycleReachLog witnessPrepHooks witnessRegistered.state out.state
      [.mint 1 11 1, .prepared witnessRequest] :=
    LifecycleReachLog.tail
      (LifecycleReachLog.tail (trace := []) LifecycleReachLog.refl
        (LifecycleStepOp.mint witness_mint))
      (LifecycleStepOp.prepared hout)
  have hinner := (fresh_registration_preconditions
    (registerFreshBranch'_eq_some.mp witness_freshBranch').1).2
  exact ⟨toyHooks 5, witnessPrepHooks, witnessState, 7, witnessRegistered, out.state,
    [.mint 1 11 1, .prepared witnessRequest], toyId, witnessPairs, 1,
    ⟨nativeVault 9, NativeTokenVault.empty.audit⟩, witnessPairs_on, by decide, hW₀, Or.inr rfl,
    ⟨rfl, nativeRegistry_corr 9⟩, witness_freshBranch', rfl, hlog,
    lifecycleReachLog_repReach hlog, registration_establishes_wellformed hinner,
    ⟨1 + 1, nativeVault_registered 9 (by decide)⟩, rfl, rfl, 4, rfl⟩

end Contracts.NativeTokenVaultBase
