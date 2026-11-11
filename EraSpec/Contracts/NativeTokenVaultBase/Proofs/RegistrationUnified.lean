import EraSpec.Contracts.NativeTokenVaultBase.Properties.RegistrationUnified
import EraSpec.Contracts.NativeTokenVaultBase.Proofs.ModelCorrespondence
import EraSpec.Core.Simulation

/-!
# Proofs: the two vault models with the registration guard gap closed

The registration results reduce the tightened definitions to the original ones
(`registerRepresentation'_eq_some`, `registerFreshBranch'_eq_some`) and then reuse the
correspondence proofs of `Proofs/ModelCorrespondence.lean` (`registrationGuardGap`,
`registrationEffectCorresponds`, `registrationPreservesValidOn`) and the
representation model's own public theorems.  The lifecycle simulation is an
induction over `RepReach` carrying the correspondence, both invariants and the
supply/flow identity, with the registry prefix's `Valid` and `Audited` from
`run_inv_on` / `run_audited_on`.  The concrete instances reuse the toy encoding and
states of `Proofs/ModelCorrespondence.lean`.
-/

namespace Contracts.NativeTokenVault

/-! ## The tightened registry model -/

theorem step'_step {e : NtvAssetId} {thisChain : Chain} {W X : World}
    (h : Step' e thisChain W X) : Step e thisChain W X := by
  cases h with
  | registerNative hg => exact Step.registerNative hg
  | registerBridged hg => exact Step.registerBridged hg.toRegisterBridgedGuard
  | bridgeOut hg => exact Step.bridgeOut hg
  | bridgeIn hg => exact Step.bridgeIn hg
  | donate => exact Step.donate

theorem reach'_reach {e : NtvAssetId} {thisChain : Chain} {W X : World}
    (h : Reach' e thisChain W X) : Reach e thisChain W X := by
  induction h with
  | refl => exact Reach.refl
  | tail _ hs ih => exact Reach.tail ih (step'_step hs)

theorem TightStepIsStep : Properties.TightStepIsStep :=
  fun _ _ _ _ => ⟨step'_step, reach'_reach⟩

/-- One tightened step keeps every registered asset's origin token nonzero. -/
theorem step'_originTokens {e : NtvAssetId} {thisChain : Chain} {W X : World}
    (h : Step' e thisChain W X) (hW : ∀ a, Registered W.vault a → W.vault.originToken a ≠ 0) :
    ∀ a, Registered X.vault a → X.vault.originToken a ≠ 0 := by
  cases h with
  | @registerNative t hg =>
    intro a ha
    change Registered (setNewTokenStorage W.vault (e thisChain t) t t thisChain) a at ha
    change (setNewTokenStorage W.vault (e thisChain t) t t thisChain).originToken a ≠ 0
    by_cases hx : a = e thisChain t
    · subst hx
      rw [sn_originToken_self]
      exact hg.nonzero
    · rw [sn_originToken_of_ne _ _ _ _ _ hx]
      exact hW a ((sn_registered_of_ne _ _ _ _ _ hx).mp ha)
  | @registerBridged a' t ot origin hg =>
    intro a ha
    change Registered (setNewTokenStorage W.vault a' t ot origin) a at ha
    change (setNewTokenStorage W.vault a' t ot origin).originToken a ≠ 0
    by_cases hx : a = a'
    · subst hx
      rw [sn_originToken_self]
      exact hg.originTokenNonzero
    · rw [sn_originToken_of_ne _ _ _ _ _ hx]
      exact hW a ((sn_registered_of_ne _ _ _ _ _ hx).mp ha)
  | bridgeOut _ =>
    intro a ha
    rw [bridgeOut_originToken]
    exact hW a ((bridgeOut_registered _ _ _ _ _).mp ha)
  | bridgeIn _ =>
    intro a ha
    rw [bridgeIn_originToken]
    exact hW a ((bridgeIn_registered _ _ _ _ _).mp ha)
  | donate =>
    intro a ha
    rw [donate_originToken]
    exact hW a ((donate_registered _ _ _).mp ha)

theorem tightRunOriginTokensNonzero {e : NtvAssetId} {thisChain : Chain} {W : World}
    (h : Reach' e thisChain empty W) : ∀ a, Registered W.vault a → W.vault.originToken a ≠ 0 := by
  induction h with
  | refl => exact fun _ ha => absurd rfl ha
  | tail _ hs ih => exact step'_originTokens hs ih

theorem TightRunOriginTokensNonzero : Properties.TightRunOriginTokensNonzero :=
  fun _ _ _ h => tightRunOriginTokensNonzero h

end Contracts.NativeTokenVault

namespace Contracts.NativeTokenVaultBase

open NativeTokenVault (Chain Vault World NtvAssetId Valid IdAssumptionsOn PairsIn
  RegisterBridgedGuard RegisterBridgedGuard')

variable {Accounting : Type}

/-! ## Normalisation -/

theorem tokenDataOriginChainId_eq_zero_iff (decoded l1ChainId : UInt256) :
    tokenDataOriginChainId decoded l1ChainId = 0 ↔ decoded = 0 ∧ l1ChainId = 0 := by
  unfold tokenDataOriginChainId
  by_cases h : decoded = 0
  · simp [h]
  · simp [h]

theorem TokenDataOriginChainIdZeroIff : Properties.TokenDataOriginChainIdZeroIff :=
  tokenDataOriginChainId_eq_zero_iff

/-! ## The tightened registration is the original one, guarded -/

theorem registerRepresentation'_eq_some {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting} :
    registerRepresentation' hooks s origin = some out ↔
      registerRepresentation hooks s origin = some out ∧ RegistryOnlyGuards s := by
  unfold registerRepresentation'
  by_cases hg : RegistryOnlyGuards s
  · rw [ite_eq_left hg]
    exact ⟨fun h => ⟨h, hg⟩, fun h => h.1⟩
  · rw [ite_eq_right hg]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.2 hg⟩

theorem registerFreshBranch'_eq_some {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting} :
    registerFreshBranch' hooks s origin = some out ↔
      registerFreshBranch hooks s origin = some out ∧ RegistryOnlyGuards s := by
  unfold registerFreshBranch' registerFreshBranch
  by_cases hf : s.registry.tokenForAsset s.config.assetId = 0
  · rw [ite_eq_left hf, ite_eq_left hf]
    exact registerRepresentation'_eq_some
  · rw [ite_eq_right hf, ite_eq_right hf]
    exact ⟨fun h => absurd h (by simp), fun h => absurd h.1 (by simp)⟩

theorem UnifiedIsGuardedRestriction : Properties.UnifiedIsGuardedRestriction :=
  fun _ _ _ _ _ => ⟨registerRepresentation'_eq_some, registerFreshBranch'_eq_some⟩

/-! ## The source supplies the three conditions -/

/-- A successful registration called the deployer and got the configured token
address (the representation model's own unfolding is private to its proof module). -/
private theorem registration_deployed {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    (h : registerRepresentation hooks s origin = some out) :
    hooks.deploy s.config.originChainId origin = some s.config.tokenAddress := by
  unfold registerRepresentation at h
  split at h
  · cases hd : hooks.deploy s.config.originChainId origin with
    | none => simp only [hd, reduceCtorEq] at h
    | some deployed =>
      simp only [hd] at h
      cases hi : BridgedStandardERC20.initializeToken BridgedStandardERC20.freshProxy
          s.config.vault s.config.assetId origin hooks.metadataDecoded with
      | none => simp only [hi, reduceCtorEq] at h
      | some initialized =>
        simp only [hi] at h
        split at h
        · rename_i he
          rw [he]
        · cases h
  · cases h

theorem sourceInputGivesRegistryOnlyGuards {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    {decoded l1ChainId : UInt256} (hsrc : SourceRegistrationInput hooks s origin decoded l1ChainId)
    (h : registerRepresentation hooks s origin = some out) : RegistryOnlyGuards s := by
  have hd := registration_deployed h
  refine ⟨hsrc.deployFresh.nonzero _ hd, hsrc.deployFresh.unmapped _ hd, ?_⟩
  rw [hsrc.originChain]
  intro h0
  exact hsrc.l1Nonzero ((tokenDataOriginChainId_eq_zero_iff _ _).mp h0).2

theorem SourceInputGivesRegistryOnlyGuards : Properties.SourceInputGivesRegistryOnlyGuards :=
  fun _ _ _ _ _ _ _ hsrc h => sourceInputGivesRegistryOnlyGuards hsrc h

theorem unifiedAgreesOnSourceInputs {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {decoded l1ChainId : UInt256}
    (hsrc : SourceRegistrationInput hooks s origin decoded l1ChainId) :
    registerRepresentation' hooks s origin = registerRepresentation hooks s origin
      ∧ registerFreshBranch' hooks s origin = registerFreshBranch hooks s origin := by
  have hrep : registerRepresentation' hooks s origin = registerRepresentation hooks s origin := by
    cases hr : registerRepresentation hooks s origin with
    | none =>
      cases hr' : registerRepresentation' hooks s origin with
      | none => rfl
      | some out => exact absurd (registerRepresentation'_eq_some.mp hr').1 (by rw [hr]; simp)
    | some out =>
      exact registerRepresentation'_eq_some.mpr ⟨hr, sourceInputGivesRegistryOnlyGuards hsrc hr⟩
  refine ⟨hrep, ?_⟩
  unfold registerFreshBranch' registerFreshBranch
  rw [hrep]

theorem UnifiedAgreesOnSourceInputs : Properties.UnifiedAgreesOnSourceInputs :=
  fun _ _ _ _ _ _ hsrc => unifiedAgreesOnSourceInputs hsrc

/-! ## (a) A tightened registration is a registry step -/

theorem unifiedRegistrationIsRegistryStep {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    {e : NtvAssetId} {thisChain : Chain} {W : World} (hc : CorrPre s thisChain W.vault)
    (h : registerFreshBranch' hooks s origin = some out)
    (henc : hooks.assetIdFor s.config.originChainId origin =
      e s.config.originChainId (widen origin)) :
    RegisterBridgedGuard' e thisChain W.vault s.config.assetId (widen s.config.tokenAddress)
        (widen origin) s.config.originChainId
      ∧ NativeTokenVault.Step' e thisChain W
          { W with vault := correspondingRegistration s origin W.vault }
      ∧ Corr out.state thisChain (correspondingRegistration s origin W.vault) := by
  obtain ⟨hfresh, hg⟩ := registerFreshBranch'_eq_some.mp h
  have hinner := (fresh_registration_preconditions hfresh).2
  have hot : widen origin ≠ 0 :=
    fun h0 => (registration_initial_fields hinner).2.1 (widen_eq_zero.mp h0)
  have hguard : RegisterBridgedGuard' e thisChain W.vault s.config.assetId
      (widen s.config.tokenAddress) (widen origin) s.config.originChainId :=
    ⟨(registrationGuardGap hc hfresh henc).mpr hg, hot⟩
  exact ⟨hguard, NativeTokenVault.Step'.registerBridged hguard,
    registrationEffectCorresponds hc hinner⟩

theorem UnifiedRegistrationIsRegistryStep : Properties.UnifiedRegistrationIsRegistryStep :=
  fun _ _ _ _ _ _ _ _ hc h henc => unifiedRegistrationIsRegistryStep hc h henc

theorem unifiedRegistrationPreservesValidOn {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {out : Registered Accounting}
    {e : NtvAssetId} {S : Set (Chain × NativeTokenVault.Address)} {thisChain : Chain}
    {V : Vault} (he : IdAssumptionsOn e S) (hc0 : thisChain ≠ 0) (hV : Valid e thisChain V)
    (hP : PairsIn S V) (hmem : (s.config.originChainId, widen origin) ∈ S)
    (hc : CorrPre s thisChain V) (h : registerFreshBranch' hooks s origin = some out)
    (henc : hooks.assetIdFor s.config.originChainId origin =
      e s.config.originChainId (widen origin)) :
    Valid e thisChain (correspondingRegistration s origin V)
      ∧ PairsIn S (correspondingRegistration s origin V)
      ∧ Corr out.state thisChain (correspondingRegistration s origin V)
      ∧ WellFormed out.state := by
  obtain ⟨hfresh, hg⟩ := registerFreshBranch'_eq_some.mp h
  obtain ⟨hv, hp, hcorr⟩ := registrationPreservesValidOn he hc0 hV hP hmem hc hfresh henc hg
  exact ⟨hv, hp, hcorr,
    registration_establishes_wellformed (fresh_registration_preconditions hfresh).2⟩

theorem UnifiedRegistrationPreservesValidOn : Properties.UnifiedRegistrationPreservesValidOn :=
  fun _ _ _ _ _ _ _ _ _ he hc0 hV hP hmem hc h henc =>
    unifiedRegistrationPreservesValidOn he hc0 hV hP hmem hc h henc

theorem unifiedRegistrationGuardsAgree {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {accounting : Accounting}
    {e : NtvAssetId} {thisChain : Chain} {V : Vault} (hc : CorrPre s thisChain V)
    (henc : hooks.assetIdFor s.config.originChainId origin =
      e s.config.originChainId (widen origin))
    (hm : hooks.metadataDecoded = true)
    (hd : hooks.deploy s.config.originChainId origin = some s.config.tokenAddress)
    (ht : hooks.registerTracker s.accounting
      (installRegistry s.registry s.config.assetId s.config.tokenAddress)
      (registeredToken s.config origin) s.config.assetId s.config.originChainId =
        some accounting) :
    (∃ out, registerFreshBranch' hooks s origin = some out) ↔
      RegisterBridgedGuard' e thisChain V s.config.assetId (widen s.config.tokenAddress)
        (widen origin) s.config.originChainId := by
  constructor
  · rintro ⟨out, h⟩
    exact (unifiedRegistrationIsRegistryStep (W := ⟨V, NativeTokenVault.empty.audit⟩) hc h
      henc).1
  · intro g
    have htok : s.config.tokenAddress ≠ 0 := fun h0 => g.tokenNonzero (by rw [h0, widen_zero])
    have hfreshTok : s.registry.assetForToken s.config.tokenAddress = 0 := by
      rw [← hc.2.assetOf]
      exact g.freshToken
    have hguards : RegistryOnlyGuards s := ⟨htok, hfreshTok, g.originNonzero⟩
    have hslot : s.registry.tokenForAsset s.config.assetId = 0 := by
      have h0 : V.token s.config.assetId = 0 := not_not.mp g.freshId
      rw [hc.2.token] at h0
      exact widen_eq_zero.mp h0
    have hid : s.config.assetId = hooks.assetIdFor s.config.originChainId origin := by
      rw [henc]
      exact g.idChecked
    have hnn : s.config.originChainId ≠ s.config.chainId := by
      rw [← hc.1]
      exact g.notNative
    have ho : origin ≠ 0 := fun h0 => g.originTokenNonzero (by rw [h0, widen_zero])
    obtain ⟨out, hout⟩ := registration_enabled hid hnn ho hm hd ht
    refine ⟨out, ?_⟩
    unfold registerFreshBranch' registerRepresentation'
    rw [ite_eq_left hslot, ite_eq_left hguards]
    exact hout

theorem UnifiedRegistrationGuardsAgree : Properties.UnifiedRegistrationGuardsAgree :=
  fun _ _ _ _ _ _ _ _ hc henc hm hd ht => unifiedRegistrationGuardsAgree hc henc hm hd ht

/-! ## (b) The four disagreements are gone -/

theorem UnifiedRegistrationCannotRebindLiveToken :
    Properties.UnifiedRegistrationCannotRebindLiveToken := by
  rintro Accounting ⟨e, S, thisChain, V, hooks, s, origin, out, b, _he, _hc0, hV, _hP, _hmem, hc,
    h, _henc, _htok, _hoc, _hb, hreg, htokb⟩
  obtain ⟨_, hg⟩ := registerFreshBranch'_eq_some.mp h
  have hfree : V.assetOf (widen s.config.tokenAddress) = 0 := by
    rw [hc.2.assetOf]
    exact hg.freshToken
  have hinv := hV.inverse b hreg
  rw [htokb, hfree] at hinv
  rw [← hinv] at hreg
  exact hV.zeroUnregistered hreg

theorem UnifiedRegistrationRejectsZeroOriginChain :
    Properties.UnifiedRegistrationRejectsZeroOriginChain := by
  rintro Accounting ⟨e, S, thisChain, V, hooks, s, origin, out, _he, _hc0, _hV, _hP, _hmem, _hc,
    h, _henc, _htok, _hfree, hoc⟩
  exact (registerFreshBranch'_eq_some.mp h).2.originNonzero hoc

theorem UnifiedRegistrationRejectsZeroToken : Properties.UnifiedRegistrationRejectsZeroToken := by
  rintro Accounting ⟨e, S, thisChain, V, hooks, s, origin, out, _he, _hc0, _hV, _hP, _hmem, _hc,
    h, _henc, htok, _hoc⟩
  exact (registerFreshBranch'_eq_some.mp h).2.tokenNonzero htok

theorem TightRegistryRejectsZeroOriginToken : Properties.TightRegistryRejectsZeroOriginToken := by
  refine ⟨?_, ?_⟩
  · rintro ⟨e, S, thisChain, V, a, t, originChain, _he, _hc0, _hV, _hP, _hmem, g⟩
    exact g.originTokenNonzero rfl
  · intro Accounting hooks s origin h0
    cases hr : registerRepresentation' hooks s origin with
    | none => rfl
    | some out =>
      exact absurd (widen_eq_zero.mp h0)
        (registration_initial_fields (registerRepresentation'_eq_some.mp hr).1).2.1

/-! ## (c) The correspondence along the representation model's life -/

/-- A token operation that keeps the token's configuration keeps the correspondence. -/
theorem corr_with_token {s : State Accounting} {thisChain : Chain} {V : Vault}
    {token : BridgedStandardERC20.State} (h : Corr s thisChain V)
    (hcfg : token.config = s.token.config) : Corr { s with token := token } thisChain V := by
  refine ⟨h.chain, h.registry, fun hreg => ?_⟩
  change V.originChain s.config.assetId = s.config.originChainId ∧
    V.originToken s.config.assetId = widen token.config.originToken
  rw [hcfg]
  exact h.tracked hreg

/-- …and the representation invariant, given the new token's ledger. -/
theorem wellFormed_with_token {s : State Accounting} {token : BridgedStandardERC20.State}
    (h : WellFormed s) (hl : BridgedStandardERC20.WellFormed token)
    (hcfg : token.config = s.token.config) : WellFormed { s with token := token } := by
  refine ⟨hl, ?_, ?_, h.2.2.2⟩
  · change token.config.vault = s.config.vault
    rw [hcfg]
    exact h.2.1
  · change token.config.assetId = s.config.assetId
    rw [hcfg]
    exact h.2.2.1

/-- **One step of the lifecycle simulation.**  A preparation is the `bridgeOut` of its
own destination chain, asset and amount; a nonzero token burn a `bridgeOut` and a mint
a `bridgeIn` of the tracked asset (towards / from its origin chain, a choice the token
model does not record); a transfer or a zero burn no step. -/
theorem lifecycleRel_step {hooks : Hooks Accounting} {e : NtvAssetId}
    {S : Set (Chain × NativeTokenVault.Address)} {thisChain : Chain}
    {u u' : State Accounting} {W : World}
    (hrel : LifecycleRel thisChain u W) (hstep : RepStep hooks u u') :
    ∃ W' : World,
      (W' = W ∨ (NativeTokenVault.StepIn e thisChain S W W'
        ∧ NativeTokenVault.Step' e thisChain W W'))
      ∧ W'.vault = W.vault ∧ u'.config = u.config ∧ LifecycleRel thisChain u' W' := by
  obtain ⟨hcorr, hwf, hreg, hfor, hsum⟩ := hrel
  cases hstep with
  | @prepared r out hp =>
    obtain ⟨hwf', hcfg', _, _, _⟩ := preparation_preserves_ledger hwf hp
    have hra : r.assetId = u.config.assetId := (preparation_asset_binding hwf hp).1
    obtain ⟨_, _, hsupply, hamt0⟩ := preparation_backed hwf hp
    have hamt_eq : out.data.amount = r.data.amount := (preparation_payload hwf hp).2.2.2.1
    have hamt : r.data.amount.val ≠ 0 := by
      intro h0
      apply hamt0
      rw [hamt_eq]
      exact Fin.ext h0
    obtain ⟨_, _, hvault, hcorr'⟩ := preparationIsForeignBridgeOut e hcorr hwf.2 hp
    have hguard : NativeTokenVault.FlowOutGuard W.vault r.assetId r.data.amount.val :=
      ⟨by rw [hra]; exact hreg, hamt⟩
    refine ⟨NativeTokenVault.bridgeOut thisChain W r.destinationChain r.assetId
        r.data.amount.val,
      Or.inr ⟨NativeTokenVault.StepIn.bridgeOut hguard, NativeTokenVault.Step'.bridgeOut hguard⟩,
      hvault, hcfg', ⟨by rw [hvault]; exact hcorr', hwf', ?_, ?_, ?_⟩⟩
    · rw [hvault, hcfg']
      exact hreg
    · rw [hvault, hcfg']
      exact hfor
    · rw [hcfg', NativeTokenVault.bridgeOut_totalOut, NativeTokenVault.bridgeOut_totalIn, hra,
        NativeTokenVault.upd_same]
      rw [hamt_eq] at hsupply
      omega
  | @tokenOp token hs =>
    cases hs with
    | @burn caller owner amount hb =>
      obtain ⟨_, _, _, hsupply, _, htcfg⟩ := BridgedStandardERC20.burn_exact hwf.1 hb
      have hwf' := wellFormed_with_token hwf
        (BridgedStandardERC20.burn_preserves_ledger hwf.1 hb) htcfg
      have hcorr' := corr_with_token hcorr htcfg
      by_cases hamt : amount.val = 0
      · refine ⟨W, Or.inl rfl, rfl, rfl, hcorr', hwf', hreg, hfor, ?_⟩
        change token.totalSupply + W.audit.totalOut u.config.assetId =
          W.audit.totalIn u.config.assetId
        omega
      · have hguard : NativeTokenVault.FlowOutGuard W.vault u.config.assetId amount.val :=
          ⟨hreg, hamt⟩
        have hvault := NativeTokenVault.bridgeOut_vault_foreign thisChain W u.config.originChainId
          u.config.assetId amount.val hfor
        refine ⟨NativeTokenVault.bridgeOut thisChain W u.config.originChainId u.config.assetId
            amount.val,
          Or.inr ⟨NativeTokenVault.StepIn.bridgeOut hguard,
            NativeTokenVault.Step'.bridgeOut hguard⟩,
          hvault, rfl, ⟨by rw [hvault]; exact hcorr', hwf', by rw [hvault]; exact hreg,
            by rw [hvault]; exact hfor, ?_⟩⟩
        change token.totalSupply + (NativeTokenVault.bridgeOut thisChain W u.config.originChainId
            u.config.assetId amount.val).audit.totalOut u.config.assetId =
          (NativeTokenVault.bridgeOut thisChain W u.config.originChainId u.config.assetId
            amount.val).audit.totalIn u.config.assetId
        rw [NativeTokenVault.bridgeOut_totalOut, NativeTokenVault.bridgeOut_totalIn,
          NativeTokenVault.upd_same]
        omega
    | @mint caller recipient amount hm =>
      obtain ⟨_, _, _, hsupply, _, htcfg⟩ := BridgedStandardERC20.mint_exact hm
      have hwf' := wellFormed_with_token hwf
        (BridgedStandardERC20.mint_preserves_ledger hwf.1 hm) htcfg
      have hcorr' := corr_with_token hcorr htcfg
      have hguard : NativeTokenVault.FlowInGuard thisChain W.vault u.config.assetId amount.val :=
        ⟨hreg, fun hn => absurd hn hfor⟩
      have hvault := NativeTokenVault.bridgeIn_vault_foreign thisChain W u.config.originChainId
        u.config.assetId amount.val hfor
      refine ⟨NativeTokenVault.bridgeIn thisChain W u.config.originChainId u.config.assetId
          amount.val,
        Or.inr ⟨NativeTokenVault.StepIn.bridgeIn hguard, NativeTokenVault.Step'.bridgeIn hguard⟩,
        hvault, rfl, ⟨by rw [hvault]; exact hcorr', hwf', by rw [hvault]; exact hreg,
          by rw [hvault]; exact hfor, ?_⟩⟩
      change token.totalSupply + (NativeTokenVault.bridgeIn thisChain W u.config.originChainId
          u.config.assetId amount.val).audit.totalOut u.config.assetId =
        (NativeTokenVault.bridgeIn thisChain W u.config.originChainId u.config.assetId
          amount.val).audit.totalIn u.config.assetId
      rw [NativeTokenVault.bridgeIn_totalOut, NativeTokenVault.bridgeIn_totalIn,
        NativeTokenVault.upd_same]
      omega
    | @transfer owner recipient amount htr =>
      obtain ⟨hl, hsupply, htcfg⟩ := BridgedStandardERC20.transfer_preserves_ledger hwf.1 htr
      refine ⟨W, Or.inl rfl, rfl, rfl, corr_with_token hcorr htcfg,
        wellFormed_with_token hwf hl htcfg, hreg, hfor, ?_⟩
      change token.totalSupply + W.audit.totalOut u.config.assetId =
        W.audit.totalIn u.config.assetId
      omega

theorem LifecycleRelIsSimulation : Properties.LifecycleRelIsSimulation :=
  fun _ _ e S _ _ _ _ hrel hstep => lifecycleRel_step (e := e) (S := S) hrel hstep

/-- A tightened registration establishes the lifecycle relation. -/
theorem registration_lifecycleRel {rhooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {reg : Registered Accounting}
    {e : NtvAssetId} {S : Set (Chain × NativeTokenVault.Address)} {thisChain : Chain}
    {W : World} (he : IdAssumptionsOn e S) (hc0 : thisChain ≠ 0)
    (hW : NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W)
    (hc : CorrPre s thisChain W.vault) (h : registerFreshBranch' rhooks s origin = some reg)
    (henc : rhooks.assetIdFor s.config.originChainId origin =
      e s.config.originChainId (widen origin)) :
    LifecycleRel thisChain reg.state
      { W with vault := correspondingRegistration s origin W.vault } := by
  obtain ⟨hg', _, hcorr₁⟩ := unifiedRegistrationIsRegistryStep (W := W) hc h henc
  have hinner := (fresh_registration_preconditions (registerFreshBranch'_eq_some.mp h).1).2
  -- the asset was unregistered before, so the audit has recorded no flow of it
  have hquiet := (NativeTokenVault.run_audited_on he hc0 hW).unregisteredQuiet
    s.config.assetId hg'.freshId
  have hcfg₁ : reg.state.config = s.config := (registration_registry_frame hinner).1
  refine ⟨hcorr₁, registration_establishes_wellformed hinner, ?_, ?_, ?_⟩
  · rw [hcfg₁]
    exact (NativeTokenVault.sn_registered_self _ _ _ _ _).mpr hg'.tokenNonzero
  · rw [hcfg₁]
    exact fun hn => hg'.notNative ((NativeTokenVault.sn_native_self _ _ _ _ _ thisChain).mp hn)
  · rw [hcfg₁]
    change reg.state.token.totalSupply + W.audit.totalOut s.config.assetId =
      W.audit.totalIn s.config.assetId
    rw [(registration_initial_fields hinner).2.2.2.1, hquiet.1, hquiet.2]

theorem RegistrationEstablishesLifecycleRel : Properties.RegistrationEstablishesLifecycleRel :=
  fun _ _ _ _ _ _ _ _ _ he hc0 hW hc h henc => registration_lifecycleRel he hc0 hW hc h henc

/-- **The lifecycle simulation, in the generic framework** (`Core/Simulation.lean`): the
representation model's `RepStep`, simulated under `LifecycleRel` by registry steps that
are both bounded (for any pair set) and tightened. -/
def lifecycleSimulation (hooks : Hooks Accounting) (e : NtvAssetId)
    (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain) :
    LayeredVerification.Simulation (RepStep hooks)
      (fun W W' => NativeTokenVault.StepIn e thisChain S W W' ∧
        NativeTokenVault.Step' e thisChain W W') where
  Rel := LifecycleRel thisChain
  match_step := by
    intro u u' W hrel hstep
    obtain ⟨W', hor, _, _, hrel'⟩ := lifecycleRel_step (e := e) (S := S) hrel hstep
    rcases hor with hW' | hst
    · subst hW'
      exact ⟨_, LayeredVerification.Run.refl _, hrel'⟩
    · exact ⟨W', LayeredVerification.Run.tail (LayeredVerification.Run.refl W) hst, hrel'⟩

theorem lifecycleSimulation_rel (hooks : Hooks Accounting) (e : NtvAssetId)
    (S : Set (Chain × NativeTokenVault.Address)) (thisChain : Chain) :
    (lifecycleSimulation hooks e S thisChain).Rel = LifecycleRel thisChain := rfl

theorem unifiedLifecycleCorresponds {rhooks : RegistrationHooks Accounting}
    {hooks : Hooks Accounting} {s : RegistrationState Accounting} {origin : Address}
    {reg : Registered Accounting} {t : State Accounting} {e : NtvAssetId}
    {S : Set (Chain × NativeTokenVault.Address)} {thisChain : Chain} {W : World}
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
      ∧ t.token.totalSupply + W'.audit.totalOut s.config.assetId
          = W'.audit.totalIn s.config.assetId := by
  -- the registration, as a bounded and tightened registry step
  obtain ⟨hg', hstep', _⟩ := unifiedRegistrationIsRegistryStep (W := W) hc h henc
  have hinner := (fresh_registration_preconditions (registerFreshBranch'_eq_some.mp h).1).2
  have hcfg₁ : reg.state.config = s.config := (registration_registry_frame hinner).1
  -- the relation, carried along the representation model's run
  suffices key : ∀ u, RepReach hooks reg.state u →
      ∃ W' : World, NativeTokenVault.ReachIn e thisChain S NativeTokenVault.empty W'
        ∧ (NativeTokenVault.Reach' e thisChain NativeTokenVault.empty W →
            NativeTokenVault.Reach' e thisChain NativeTokenVault.empty W')
        ∧ W'.vault = correspondingRegistration s origin W.vault
        ∧ u.config = s.config ∧ LifecycleRel thisChain u W' by
    obtain ⟨W', hin, hti, hv, hcfg, hrel⟩ := key t hrun
    have hsum := hrel.supply
    rw [hcfg] at hsum
    exact ⟨W', hin, hti, hv, hrel.corr, (NativeTokenVault.run_inv_on he hc0 hin).1,
      hrel.wellFormed, hsum⟩
  intro u hu
  induction hu with
  | refl =>
    exact ⟨{ W with vault := correspondingRegistration s origin W.vault },
      NativeTokenVault.ReachIn.tail hW
        (NativeTokenVault.StepIn.registerBridged hmem hg'.toRegisterBridgedGuard),
      fun h' => NativeTokenVault.Reach'.tail h' hstep', rfl, hcfg₁,
      registration_lifecycleRel he hc0 hW hc h henc⟩
  | tail _ hstep ih =>
    obtain ⟨W', hin, hti, hv, hcfg, hrel⟩ := ih
    obtain ⟨W'', hor, hv', hcfg', hrel'⟩ := lifecycleRel_step (e := e) (S := S) hrel hstep
    rcases hor with hW'' | ⟨hstIn, hst'⟩
    · subst hW''
      exact ⟨_, hin, hti, hv, hcfg'.trans hcfg, hrel'⟩
    · exact ⟨W'', NativeTokenVault.ReachIn.tail hin hstIn,
        fun h' => NativeTokenVault.Reach'.tail (hti h') hst', hv'.trans hv, hcfg'.trans hcfg,
        hrel'⟩

theorem UnifiedLifecycleCorresponds : Properties.UnifiedLifecycleCorresponds :=
  fun _ _ _ _ _ _ _ _ _ _ _ he hc0 hW hmem hc h henc hrun =>
    unifiedLifecycleCorresponds he hc0 hW hmem hc h henc hrun

/-! ## Concrete instances

The toy encoding `toyId : (c, t) ↦ c + 1` and the states of
`Proofs/ModelCorrespondence.lean`: `witnessState` registers asset `2 + 1` (origin
chain `2`, origin token `7`) at the fresh address `5` next to the native token `9`;
`rebindState` deploys it at `5`, which already holds the native asset `1 + 1`. -/

/-- `registration_enabled`, with the successful result written out. -/
theorem registration_result {hooks : RegistrationHooks Accounting}
    {s : RegistrationState Accounting} {origin : Address} {accounting : Accounting}
    (ha : s.config.assetId = hooks.assetIdFor s.config.originChainId origin)
    (hc : s.config.originChainId ≠ s.config.chainId) (ho : origin ≠ 0)
    (hm : hooks.metadataDecoded = true)
    (hd : hooks.deploy s.config.originChainId origin = some s.config.tokenAddress)
    (ht : hooks.registerTracker s.accounting
      (installRegistry s.registry s.config.assetId s.config.tokenAddress)
      (registeredToken s.config origin) s.config.assetId s.config.originChainId =
        some accounting) :
    registerRepresentation hooks s origin =
      some ⟨⟨s.config, installRegistry s.registry s.config.assetId s.config.tokenAddress,
        s.paused, registeredToken s.config origin, accounting⟩, 1⟩ := by
  have hg : s.config.assetId = hooks.assetIdFor s.config.originChainId origin ∧
      s.config.originChainId ≠ s.config.chainId := ⟨ha, hc⟩
  have hi : BridgedStandardERC20.initializeToken BridgedStandardERC20.freshProxy s.config.vault
      s.config.assetId origin hooks.metadataDecoded =
        some ⟨registeredToken s.config origin, 1⟩ := by
    simp [BridgedStandardERC20.initializeToken, BridgedStandardERC20.InitializeAllowed,
      BridgedStandardERC20.freshProxy, BridgedStandardERC20.empty, registeredToken, ho, hm]
  simp only [registerRepresentation, ite_eq_left hg, hd, hi, ht, ite_true]

/-- The deploy hook of `toyHooks d` is fresh for a state where `d` is nonzero and
unmapped. -/
theorem deployFresh_toy (s : RegistrationState Unit) (origin : Address) {d : Address}
    (hd0 : d ≠ 0) (hfree : s.registry.assetForToken d = 0) :
    DeployFresh (toyHooks d) s origin :=
  ⟨fun _ h => (Option.some.inj h) ▸ hd0, fun _ h => (Option.some.inj h) ▸ hfree⟩

/-- The witness registration, written out. -/
def witnessRegistered : Registered Unit :=
  ⟨⟨witnessState.config, installRegistry witnessState.registry witnessState.config.assetId
    witnessState.config.tokenAddress, witnessState.paused,
    registeredToken witnessState.config 7, ()⟩, 1⟩

theorem witness_registration_result :
    registerRepresentation (toyHooks 5) witnessState 7 = some witnessRegistered :=
  registration_result (accounting := ()) rfl (by decide) (by decide) rfl rfl rfl

theorem witness_freshBranch :
    registerFreshBranch (toyHooks 5) witnessState 7 = some witnessRegistered := by
  have hfree : witnessState.registry.tokenForAsset witnessState.config.assetId = 0 :=
    nativeRegistry_token_ne 9 (by decide)
  unfold registerFreshBranch
  rw [ite_eq_left hfree]
  exact witness_registration_result

theorem witness_freshBranch' :
    registerFreshBranch' (toyHooks 5) witnessState 7 = some witnessRegistered :=
  registerFreshBranch'_eq_some.mpr ⟨witness_freshBranch, witness_guards⟩

theorem SourceRegistrationInputSatisfiable : Properties.SourceRegistrationInputSatisfiable :=
  ⟨toyHooks 5, witnessState, 7, witnessRegistered, 0, 2,
    ⟨by decide, by decide, deployFresh_toy witnessState 7 (by decide)
      (nativeRegistry_asset_ne 9 (by decide))⟩,
    rfl, witness_registration_result, witness_freshBranch, witness_freshBranch'⟩

theorem SourceInputPremisesLoadBearing : Properties.SourceInputPremisesLoadBearing := by
  refine ⟨?_, ?_, ?_⟩
  · -- `_l1ChainId() = 0` with decoded `0`: origin chain `0`, fresh deployment at `5`
    obtain ⟨out, hout⟩ :=
      toy_registration ⟨fun _ => 0, fun _ => 0⟩ 5 7 1 0 rfl (by decide) (by decide)
    exact ⟨toyHooks 5, ⟨toyConfig 5 (0 + 1) 1 0, ⟨fun _ => 0, fun _ => 0⟩, false, ()⟩, 7, out,
      by decide, deployFresh_toy _ 7 (by decide) rfl, hout, fun g => g.originNonzero rfl⟩
  · -- a nonzero `_l1ChainId()`, the deployed address unmapped but `0`
    obtain ⟨out, hout⟩ :=
      toy_registration ⟨fun _ => 0, fun _ => 0⟩ 0 7 1 2 rfl (by decide) (by decide)
    exact ⟨toyHooks 0, ⟨toyConfig 0 (2 + 1) 1 2, ⟨fun _ => 0, fun _ => 0⟩, false, ()⟩, 7, out,
      2, 1, by decide, by decide, fun _ _ => rfl, rfl, hout, fun g => g.tokenNonzero rfl⟩
  · -- a nonzero `_l1ChainId()`, the deployed address nonzero but mapped to `1 + 1`
    obtain ⟨out, hout⟩ := toy_registration (nativeRegistry 5) 5 7 1 2
      (nativeRegistry_token_ne 5 (by decide)) (by decide) (by decide)
    refine ⟨toyHooks 5, rebindState, 7, out, 2, 1, by decide, by decide,
      fun _ h => (Option.some.inj h) ▸ (by decide), hout, fun g => ?_⟩
    have h0 := g.freshToken
    change (nativeRegistry 5).assetForToken 5 = 0 at h0
    rw [nativeRegistry_asset_self] at h0
    exact absurd h0 (by decide)

theorem UnifiedRegistrationSatisfiable : Properties.UnifiedRegistrationSatisfiable := by
  obtain ⟨hv, hp⟩ := nativeVault_valid witnessPairs_on (n := 9) (by decide) (Or.inl rfl)
  exact ⟨toyId, witnessPairs, 1, nativeVault 9, toyHooks 5, witnessState, 7, witnessRegistered,
    witnessPairs_on, by decide, hv, hp, Or.inr rfl, ⟨rfl, nativeRegistry_corr 9⟩,
    witness_freshBranch', rfl, rfl, rfl, rfl, 1 + 1, by decide,
    nativeVault_registered 9 (by decide)⟩

theorem UnifiedGuardsAgreeBothFalse : Properties.UnifiedGuardsAgreeBothFalse := by
  have hc : CorrPre rebindState 1 (nativeVault 5) := ⟨rfl, nativeRegistry_corr 5⟩
  have hbound : rebindState.registry.assetForToken rebindState.config.tokenAddress = 1 + 1 :=
    nativeRegistry_asset_self 5
  have hnot : ¬ RegistryOnlyGuards rebindState := fun g => by
    have h0 := g.freshToken
    rw [hbound] at h0
    exact absurd h0 (by decide)
  obtain ⟨out, hout⟩ := toy_registration (nativeRegistry 5) 5 7 1 2
    (nativeRegistry_token_ne 5 (by decide)) (by decide) (by decide)
  refine ⟨toyId, 1, nativeVault 5, toyHooks 5, rebindState, 7, hc, rfl, rfl, rfl, rfl, ?_, ?_,
    out, hout⟩
  · cases hr : registerFreshBranch' (toyHooks 5) rebindState 7 with
    | none => rfl
    | some o => exact absurd (registerFreshBranch'_eq_some.mp hr).2 hnot
  · intro g
    have h0 := g.freshToken
    rw [hc.2.assetOf, hbound] at h0
    exact absurd h0 (by decide)

/-- Asset `2 + 1` already registered at token `5` (the witness registry), to be deployed
again at the fresh address `6`. -/
def overwriteState : RegistrationState Unit :=
  ⟨toyConfig 6 (2 + 1) 1 2, installRegistry (nativeRegistry 9) (2 + 1) 5, false, ()⟩

theorem InnerRegistrationNeedsFreshSlot : Properties.InnerRegistrationNeedsFreshSlot := by
  obtain ⟨hv, hp, _, _⟩ := unifiedRegistrationPreservesValidOn (s := witnessState) (origin := 7)
    witnessPairs_on (by decide)
    (nativeVault_valid witnessPairs_on (n := 9) (by decide) (Or.inl rfl)).1
    (nativeVault_valid witnessPairs_on (n := 9) (by decide) (Or.inl rfl)).2 (Or.inr rfl)
    ⟨rfl, nativeRegistry_corr 9⟩ witness_freshBranch' rfl
  have hc : CorrPre overwriteState 1 witnessVault :=
    ⟨rfl, registryCorr_install (nativeRegistry_corr 9) _ _ _ _⟩
  have hguards : RegistryOnlyGuards overwriteState := by
    refine ⟨by decide, ?_, by decide⟩
    show Function.update (nativeRegistry 9).assetForToken 5 (2 + 1) 6 = 0
    rw [Function.update_of_ne (by decide)]
    exact nativeRegistry_asset_ne 9 (by decide)
  have hreg : registerRepresentation (toyHooks 6) overwriteState 7 = some
      ⟨⟨overwriteState.config, installRegistry overwriteState.registry
        overwriteState.config.assetId overwriteState.config.tokenAddress, overwriteState.paused,
        registeredToken overwriteState.config 7, ()⟩, 1⟩ :=
    registration_result (accounting := ()) rfl (by decide) (by decide) rfl rfl rfl
  have hslot : overwriteState.registry.tokenForAsset overwriteState.config.assetId = 5 := by
    show Function.update (nativeRegistry 9).tokenForAsset (2 + 1) 5 (2 + 1) = 5
    exact Function.update_self _ _ _
  refine ⟨toyId, witnessPairs, 1, witnessVault, toyHooks 6, overwriteState, 7, _,
    witnessPairs_on, by decide, hv, hp, Or.inr rfl, hc,
    registerRepresentation'_eq_some.mpr ⟨hreg, hguards⟩, rfl, by rw [hslot]; decide, ?_, ?_⟩
  · -- the asset is registered already
    intro g
    apply g.freshId
    show witnessVault.token overwriteState.config.assetId ≠ 0
    rw [hc.2.token, hslot]
    decide
  · -- token `5` still maps to the asset, which now points at `6`
    intro hV'
    have hne : (widen 5 : NativeTokenVault.Address) ≠ widen 6 := by decide
    have hof : (correspondingRegistration overwriteState 7 witnessVault).assetOf (widen 5) =
        2 + 1 := by
      show (NativeTokenVault.setNewTokenStorage witnessVault (2 + 1) (widen 6) (widen 7) 2).assetOf
        (widen 5) = 2 + 1
      rw [NativeTokenVault.sn_assetOf_of_ne _ _ _ _ _ hne, hc.2.assetOf]
      show Function.update (nativeRegistry 9).assetForToken 5 (2 + 1) 5 = 2 + 1
      exact Function.update_self _ _ _
    have htok := hV'.tokenOfAsset (widen 5) (by rw [hof]; decide)
    rw [hof] at htok
    change (NativeTokenVault.setNewTokenStorage witnessVault (2 + 1) (widen 6) (widen 7) 2).token
      (2 + 1) = widen 5 at htok
    rw [NativeTokenVault.sn_token_self] at htok
    exact hne htok.symm

/-- One unit minted to account `11` on the freshly registered token. -/
theorem witness_mint :
    BridgedStandardERC20.mint witnessRegistered.state.token 1 11 1 = some witnessToken := by
  change BridgedStandardERC20.mint (BridgedStandardERC20.empty ⟨1, 7, 2 + 1⟩) 1 11 1 =
    some witnessToken
  unfold BridgedStandardERC20.mint
  rw [ite_eq_left]
  · rfl
  · refine ⟨by decide, rfl, by decide, ?_⟩
    norm_num [BridgedStandardERC20.empty, UInt256.size]

/-- The witness preparation of `Proofs/ModelCorrespondence.lean`: burn that unit
towards chain `4`. -/
theorem witness_prepare :
    ∃ out, prepare witnessPrepHooks witnessPrepState witnessRequest = some out := by
  have hw : WellFormed witnessPrepState := ⟨witnessToken_ledger, witnessPrep_rc⟩
  have htok : witnessPrepState.registry.tokenForAsset (2 + 1) = 5 := witnessPrep_token
  have hs : InScope witnessPrepState witnessRequest := by
    refine ⟨by decide, by decide, by decide, by decide, ?_⟩
    show (if (0 : Address) = 0 then witnessPrepState.registry.tokenForAsset (2 + 1) else 0) = 5
    rw [ite_eq_left rfl, htok]
  have hsel : selectedToken witnessPrepState witnessRequest = 5 := hs.2.2.2.2
  have he : EntryAllowed witnessPrepState witnessRequest := by
    refine ⟨rfl, rfl, rfl, ?_, ?_, by decide⟩
    · rw [hsel]; decide
    · rw [hsel]; exact witnessPrep_asset
  have hb : witnessRequest.data.amount.val ≤ witnessPrepState.token.balances 11 := by
    show (1 : UInt256).val ≤ Function.update (fun _ => 0) (11 : Address) (0 + (1 : UInt256).val) 11
    rw [Function.update_self]
    decide
  exact preparation_enabled (hooks := witnessPrepHooks) (accounted := ())
    (metadata := []) hw hs he rfl (by decide) hb (by decide) (by decide) rfl rfl

theorem UnifiedLifecycleSatisfiable : Properties.UnifiedLifecycleSatisfiable := by
  have hg0 : NativeTokenVault.RegisterNativeGuard NativeTokenVault.empty.vault (widen 9) :=
    ⟨fun h0 => absurd (widen_eq_zero.mp h0) (by decide), rfl⟩
  have hW₀ : NativeTokenVault.ReachIn toyId 1 witnessPairs NativeTokenVault.empty
      ⟨nativeVault 9, NativeTokenVault.empty.audit⟩ :=
    NativeTokenVault.ReachIn.tail NativeTokenVault.ReachIn.refl
      (NativeTokenVault.StepIn.registerNative (Or.inl rfl) hg0)
  have hmid : RepReach witnessPrepHooks witnessRegistered.state witnessPrepState :=
    RepReach.tail RepReach.refl (RepStep.tokenOp (BridgedStandardERC20.Step.mint witness_mint))
  obtain ⟨out, hout⟩ := witness_prepare
  exact ⟨toyHooks 5, witnessPrepHooks, witnessState, 7, witnessRegistered, out.state, toyId,
    witnessPairs, 1, ⟨nativeVault 9, NativeTokenVault.empty.audit⟩, witnessPairs_on, by decide,
    hW₀, Or.inr rfl, ⟨rfl, nativeRegistry_corr 9⟩, witness_freshBranch', rfl,
    RepReach.tail hmid (RepStep.prepared hout), ⟨1 + 1, nativeVault_registered 9 (by decide)⟩,
    witnessPrepState, witnessRequest, out, hmid, by decide, hout, rfl⟩

theorem LifecycleRelSatisfiable : Properties.LifecycleRelSatisfiable := by
  have hg0 : NativeTokenVault.RegisterNativeGuard NativeTokenVault.empty.vault (widen 9) :=
    ⟨fun h0 => absurd (widen_eq_zero.mp h0) (by decide), rfl⟩
  have hW₀ : NativeTokenVault.ReachIn toyId 1 witnessPairs NativeTokenVault.empty
      ⟨nativeVault 9, NativeTokenVault.empty.audit⟩ :=
    NativeTokenVault.ReachIn.tail NativeTokenVault.ReachIn.refl
      (NativeTokenVault.StepIn.registerNative (Or.inl rfl) hg0)
  exact ⟨witnessPrepHooks, 1, witnessRegistered.state, witnessPrepState,
    { (⟨nativeVault 9, NativeTokenVault.empty.audit⟩ : World) with
      vault := correspondingRegistration witnessState 7 (nativeVault 9) },
    registration_lifecycleRel witnessPairs_on (by decide) hW₀ ⟨rfl, nativeRegistry_corr 9⟩
      witness_freshBranch' rfl,
    RepStep.tokenOp (BridgedStandardERC20.Step.mint witness_mint), by decide⟩

end Contracts.NativeTokenVaultBase

namespace Contracts.NativeTokenVault

open NativeTokenVaultBase (toyId toyId_on_single widen widen_eq_zero witnessState witnessPairs
  witnessPairs_on nativeVault nativeRegistry_corr witness_freshBranch'
  unifiedRegistrationIsRegistryStep correspondingRegistration)

theorem RunCanRecordZeroOriginToken : Properties.RunCanRecordZeroOriginToken := by
  have he : IdAssumptionsOn toyId {((2 : Chain), (0 : Address))} := toyId_on_single (by decide)
  have hg : RegisterBridgedGuard toyId 1 empty.vault (2 + 1) (widen 5) 0 2 :=
    ⟨by decide, by decide, rfl, by decide, rfl, fun h => h rfl⟩
  exact ⟨toyId, _, 1, { empty with vault := registerBridged empty.vault (2 + 1) (widen 5) 0 2 },
    he, by decide, ReachIn.tail ReachIn.refl (StepIn.registerBridged rfl hg),
    (registerBridged_preserves_valid_on he (by decide) empty_valid (pairsIn_empty _) rfl hg).1,
    2 + 1, (sn_registered_self empty.vault (2 + 1) (widen 5) 0 2).mpr (by decide),
    sn_originToken_self empty.vault (2 + 1) (widen 5) 0 2⟩

theorem TightRegistrySatisfiable : Properties.TightRegistrySatisfiable := by
  have hg0 : RegisterNativeGuard empty.vault (widen 9) :=
    ⟨fun h0 => absurd (widen_eq_zero.mp h0) (by decide), rfl⟩
  have hc : NativeTokenVaultBase.CorrPre witnessState 1 (nativeVault 9) := ⟨rfl, nativeRegistry_corr 9⟩
  obtain ⟨hg', hstep₁, _⟩ := unifiedRegistrationIsRegistryStep
    (e := toyId) (W := ⟨nativeVault 9, empty.audit⟩) hc witness_freshBranch' rfl
  refine ⟨toyId, witnessPairs, 1,
    ⟨correspondingRegistration witnessState 7 (nativeVault 9), empty.audit⟩, witnessPairs_on,
    by decide, Reach'.tail (Reach'.tail Reach'.refl (Step'.registerNative hg0)) hstep₁,
    ReachIn.tail (ReachIn.tail ReachIn.refl (StepIn.registerNative (Or.inl rfl) hg0))
      (StepIn.registerBridged (Or.inr rfl) hg'.toRegisterBridgedGuard),
    1 + 1, 2 + 1, by decide, by decide, by decide, by decide, by decide⟩

end Contracts.NativeTokenVault
