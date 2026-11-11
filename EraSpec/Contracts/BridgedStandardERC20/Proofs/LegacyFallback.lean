import EraSpec.Contracts.BridgedStandardERC20.Properties.LegacyFallback
import EraSpec.Contracts.BridgedStandardERC20.Proofs.Model

/-!
# Proofs: the legacy zero-vault fallback in `onlyNTV`

Everything reduces to two facts about the prologue `legacyFallback`: it is the identity on a
nonzero vault, and on a zero vault it changes only the configuration, to one whose vault is
nonzero. The call-level statements are then the nonlegacy ones (`mint_exact`, `burn_exact`,
`mint_preserves_ledger`, …) applied to the prologue's result. The run-level statements are
inductions carrying "still legacy, with the starting configuration" or "nonlegacy, with the
fallback configuration".
-/

namespace Contracts.BridgedStandardERC20

/-! ## The nonlegacy operations, read off their definitions -/

theorem mint_some_iff {s t : State} {caller recipient : Address} {amount : UInt256} :
    mint s caller recipient amount = some t ↔
      MintAllowed s caller recipient amount ∧ mintEffect s recipient amount = t := by
  unfold mint
  split <;> simp_all

theorem burn_some_iff {s t : State} {caller owner : Address} {amount : UInt256} :
    burn s caller owner amount = some t ↔
      BurnAllowed s caller owner amount ∧ burnEffect s owner amount = t := by
  unfold burn
  split <;> simp_all

theorem transfer_some_iff {s t : State} {owner recipient : Address} {amount : UInt256} :
    transfer s owner recipient amount = some t ↔
      TransferAllowed s owner recipient amount ∧ transferEffect s owner recipient amount = t := by
  unfold transfer
  split <;> simp_all

theorem mint_config {s t : State} {caller recipient : Address} {amount : UInt256}
    (h : mint s caller recipient amount = some t) : t.config = s.config := by
  obtain ⟨_, rfl⟩ := mint_some_iff.mp h
  rfl

theorem burn_config {s t : State} {caller owner : Address} {amount : UInt256}
    (h : burn s caller owner amount = some t) : t.config = s.config := by
  obtain ⟨_, rfl⟩ := burn_some_iff.mp h
  rfl

theorem transfer_config {s t : State} {owner recipient : Address} {amount : UInt256}
    (h : transfer s owner recipient amount = some t) : t.config = s.config := by
  obtain ⟨_, rfl⟩ := transfer_some_iff.mp h
  rfl

theorem step_config {s t : State} (h : Step s t) : t.config = s.config := by
  cases h with
  | burn hb => exact burn_config hb
  | mint hm => exact mint_config hm
  | transfer ht => exact transfer_config ht

theorem reach_config {s t : State} (h : Reach s t) : t.config = s.config := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact (step_config hs).trans ih

/-! ## The prologue -/

theorem l2_vault_nonzero : Properties.l2_vault_nonzero := by decide

theorem legacyFallback_of_vault_ne {env : LegacyEnv} {s : State} (h : s.config.vault ≠ 0) :
    legacyFallback env s = s :=
  ite_eq_right h

theorem legacyFallback_of_vault_eq {env : LegacyEnv} {s : State} (h : s.config.vault = 0) :
    legacyFallback env s = { s with config := fallbackConfig env s.config } :=
  ite_eq_left h

theorem fallbackConfig_vault_ne (env : LegacyEnv) (c : Config) :
    (fallbackConfig env c).vault ≠ 0 :=
  l2_vault_nonzero

theorem legacyFallback_vault_ne (env : LegacyEnv) (s : State) :
    (legacyFallback env s).config.vault ≠ 0 := by
  by_cases h : s.config.vault = 0
  · rw [legacyFallback_of_vault_eq h]
    exact l2_vault_nonzero
  · rw [legacyFallback_of_vault_ne h]
    exact h

theorem legacyFallback_originToken (env : LegacyEnv) (s : State) :
    (legacyFallback env s).config.originToken = s.config.originToken := by
  by_cases h : s.config.vault = 0
  · rw [legacyFallback_of_vault_eq h]
    rfl
  · rw [legacyFallback_of_vault_ne h]

/-- The prologue does not touch the ledger, so it preserves `WellFormed` both ways. -/
theorem wellFormed_legacyFallback (env : LegacyEnv) (s : State) :
    WellFormed (legacyFallback env s) ↔ WellFormed s := by
  by_cases h : s.config.vault = 0
  · rw [legacyFallback_of_vault_eq h]
    exact Iff.rfl
  · rw [legacyFallback_of_vault_ne h]

theorem bridgeMint_config {env : LegacyEnv} {s t : State} {caller recipient : Address}
    {amount : UInt256} (h : bridgeMint env s caller recipient amount = some t) :
    t.config = (legacyFallback env s).config :=
  mint_config h

theorem bridgeBurn_config {env : LegacyEnv} {s t : State} {caller owner : Address}
    {amount : UInt256} (h : bridgeBurn env s caller owner amount = some t) :
    t.config = (legacyFallback env s).config :=
  burn_config h

/-! ## The extension is conservative -/

theorem nonlegacy_bridge_calls_unchanged (env : LegacyEnv) {s : State}
    (h : s.config.vault ≠ 0) (caller account : Address) (amount : UInt256) :
    Properties.nonlegacy_bridge_calls_unchanged env h caller account amount := by
  unfold Properties.nonlegacy_bridge_calls_unchanged bridgeMint bridgeBurn
  rw [legacyFallback_of_vault_ne h]
  exact ⟨rfl, rfl⟩

theorem original_model_rejects_legacy {s : State} (h : s.config.vault = 0)
    (caller account : Address) (amount : UInt256) :
    Properties.original_model_rejects_legacy h caller account amount := by
  unfold Properties.original_model_rejects_legacy
  constructor
  · cases hm : mint s caller account amount with
    | none => rfl
    | some t => exact absurd h (mint_some_iff.mp hm).1.1
  · cases hb : burn s caller account amount with
    | none => rfl
    | some t => exact absurd h (burn_some_iff.mp hb).1.1

theorem legacy_original_steps_are_transfers {s t : State} (hl : s.config.vault = 0)
    (h : Step s t) : Properties.legacy_original_steps_are_transfers hl h := by
  unfold Properties.legacy_original_steps_are_transfers
  cases h with
  | burn hb => exact absurd hl (burn_some_iff.mp hb).1.1
  | mint hm => exact absurd hl (mint_some_iff.mp hm).1.1
  | transfer ht => exact ⟨_, _, _, ht⟩

theorem bridgeMint_of_mint (env : LegacyEnv) {s t : State} {caller recipient : Address}
    {amount : UInt256} (h : mint s caller recipient amount = some t) :
    bridgeMint env s caller recipient amount = some t := by
  rw [(nonlegacy_bridge_calls_unchanged env (mint_some_iff.mp h).1.1 caller recipient amount).1]
  exact h

theorem bridgeBurn_of_burn (env : LegacyEnv) {s t : State} {caller owner : Address}
    {amount : UInt256} (h : burn s caller owner amount = some t) :
    bridgeBurn env s caller owner amount = some t := by
  rw [(nonlegacy_bridge_calls_unchanged env (burn_some_iff.mp h).1.1 caller owner amount).2]
  exact h

theorem step_legacyStep (env : LegacyEnv) {s t : State} (h : Step s t) :
    LegacyStep env s t := by
  cases h with
  | burn hb => exact LegacyStep.bridgeBurn (bridgeBurn_of_burn env hb)
  | mint hm => exact LegacyStep.bridgeMint (bridgeMint_of_mint env hm)
  | transfer ht => exact LegacyStep.transfer ht

theorem reach_legacyReach (env : LegacyEnv) {s t : State} (h : Reach s t) :
    LegacyReach env s t := by
  induction h with
  | refl => exact LegacyReach.refl
  | tail _ hs ih => exact LegacyReach.tail ih (step_legacyStep env hs)

theorem original_runs_are_legacy_runs (env : LegacyEnv) {s t : State} (h : Reach s t) :
    Properties.original_runs_are_legacy_runs env h :=
  reach_legacyReach env h

/-- From a nonlegacy token, a step of the deployed token is a step of the nonlegacy model. -/
theorem legacyStep_step_of_vault_ne {env : LegacyEnv} {s t : State} (hv : s.config.vault ≠ 0)
    (h : LegacyStep env s t) : Step s t := by
  cases h with
  | @bridgeMint caller recipient amount hm =>
    rw [(nonlegacy_bridge_calls_unchanged env hv caller recipient amount).1] at hm
    exact Step.mint hm
  | @bridgeBurn caller owner amount hb =>
    rw [(nonlegacy_bridge_calls_unchanged env hv caller owner amount).2] at hb
    exact Step.burn hb
  | transfer ht => exact Step.transfer ht

theorem nonlegacy_runs_agree (env : LegacyEnv) {s : State} (h : s.config.vault ≠ 0)
    (t : State) : Properties.nonlegacy_runs_agree env h t := by
  unfold Properties.nonlegacy_runs_agree
  refine ⟨fun hr => ?_, reach_legacyReach env⟩
  have key : Reach s t ∧ t.config = s.config := by
    induction hr with
    | refl => exact ⟨Reach.refl, rfl⟩
    | @tail w x _ hs ih =>
      obtain ⟨hr', hc⟩ := ih
      have hv : w.config.vault ≠ 0 := by rw [hc]; exact h
      have hstep := legacyStep_step_of_vault_ne hv hs
      exact ⟨Reach.tail hr' hstep, (step_config hstep).trans hc⟩
  exact key.1

/-! ## The legacy branch, call by call -/

theorem legacy_bridge_mint_exact (env : LegacyEnv) {s t : State}
    {caller recipient : Address} {amount : UInt256} (hl : s.config.vault = 0)
    (h : bridgeMint env s caller recipient amount = some t) :
    Properties.legacy_bridge_mint_exact env hl h := by
  unfold Properties.legacy_bridge_mint_exact
  have hm : mint (legacyFallback env s) caller recipient amount = some t := h
  rw [legacyFallback_of_vault_eq hl] at hm
  obtain ⟨hc, _, hb, hsup, hother, hcfg⟩ := mint_exact hm
  exact ⟨hc, hcfg, hb, hsup, hother⟩

theorem legacy_bridge_burn_exact (env : LegacyEnv) {s t : State}
    {caller owner : Address} {amount : UInt256} (hw : WellFormed s) (hl : s.config.vault = 0)
    (h : bridgeBurn env s caller owner amount = some t) :
    Properties.legacy_bridge_burn_exact env hw hl h := by
  unfold Properties.legacy_bridge_burn_exact
  have hb : burn (legacyFallback env s) caller owner amount = some t := h
  rw [legacyFallback_of_vault_eq hl] at hb
  have hw' : WellFormed { s with config := fallbackConfig env s.config } := hw
  obtain ⟨hc, _, hbal, hsup, hother, hcfg⟩ := burn_exact hw' hb
  exact ⟨hc, hcfg, hbal, hsup, hother⟩

theorem legacy_unauthorized_bridge_calls (env : LegacyEnv) {s : State}
    {caller : Address} (hl : s.config.vault = 0) (hc : caller ≠ l2NativeTokenVaultAddr)
    (account : Address) (amount : UInt256) :
    Properties.legacy_unauthorized_bridge_calls env hl hc account amount := by
  unfold Properties.legacy_unauthorized_bridge_calls bridgeMint bridgeBurn
  rw [legacyFallback_of_vault_eq hl]
  have hc' : caller ≠ ({ s with config := fallbackConfig env s.config } : State).config.vault :=
    hc
  have h := unauthorized_bridge_calls (account := account) (amount := amount) hc'
  exact ⟨h.2, h.1⟩

theorem legacy_bridge_mint_enabled (env : LegacyEnv) {s : State}
    {recipient : Address} {amount : UInt256} (hl : s.config.vault = 0) (hr : recipient ≠ 0)
    (hs : s.totalSupply + amount.val < UInt256.size) :
    Properties.legacy_bridge_mint_enabled env hl hr hs := by
  unfold Properties.legacy_bridge_mint_enabled bridgeMint
  rw [legacyFallback_of_vault_eq hl]
  have ha : MintAllowed { s with config := fallbackConfig env s.config } l2NativeTokenVaultAddr
      recipient amount := by
    unfold MintAllowed
    exact ⟨l2_vault_nonzero, rfl, hr, hs⟩
  unfold mint
  exact ite_eq_left ha

theorem legacy_bridge_burn_enabled (env : LegacyEnv) {s : State}
    {owner : Address} {amount : UInt256} (hl : s.config.vault = 0) (ho : owner ≠ 0)
    (hb : amount.val ≤ s.balances owner) :
    Properties.legacy_bridge_burn_enabled env hl ho hb := by
  unfold Properties.legacy_bridge_burn_enabled bridgeBurn
  rw [legacyFallback_of_vault_eq hl]
  have ha : BurnAllowed { s with config := fallbackConfig env s.config } l2NativeTokenVaultAddr
      owner amount := by
    unfold BurnAllowed
    exact ⟨l2_vault_nonzero, rfl, ho, hb⟩
  unfold burn
  exact ite_eq_left ha

theorem bridge_call_ends_nonlegacy (env : LegacyEnv) {s t : State}
    {caller account : Address} {amount : UInt256}
    (h : bridgeMint env s caller account amount = some t ∨
      bridgeBurn env s caller account amount = some t) :
    Properties.bridge_call_ends_nonlegacy env h := by
  unfold Properties.bridge_call_ends_nonlegacy
  have hcfg : t.config = (legacyFallback env s).config := by
    rcases h with hm | hb
    · exact bridgeMint_config hm
    · exact bridgeBurn_config hb
  have hcaller : caller = (legacyFallback env s).config.vault := by
    rcases h with hm | hb
    · exact (mint_some_iff.mp hm).1.2.1
    · exact (burn_some_iff.mp hb).1.2.1
  refine ⟨?_, hcfg, ?_⟩
  · rw [hcfg]
    exact hcaller
  · rw [hcfg]
    exact legacyFallback_vault_ne env s

/-! ## Runs -/

theorem legacy_step_config (env : LegacyEnv) {s t : State} (h : LegacyStep env s t) :
    Properties.legacy_step_config env h := by
  unfold Properties.legacy_step_config
  have key : ∀ {u : State}, u.config = (legacyFallback env s).config →
      u.config = s.config ∨ (s.config.vault = 0 ∧ u.config = fallbackConfig env s.config) := by
    intro u hu
    by_cases hv : s.config.vault = 0
    · rw [legacyFallback_of_vault_eq hv] at hu
      exact Or.inr ⟨hv, hu⟩
    · rw [legacyFallback_of_vault_ne hv] at hu
      exact Or.inl hu
  cases h with
  | bridgeMint hm => exact key (bridgeMint_config hm)
  | bridgeBurn hb => exact key (bridgeBurn_config hb)
  | transfer ht => exact Or.inl (transfer_config ht)

theorem legacy_run_config (env : LegacyEnv) {s t : State} (h : LegacyReach env s t) :
    Properties.legacy_run_config env h := by
  unfold Properties.legacy_run_config
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hs ih =>
    rcases legacy_step_config env hs with hc | ⟨hv, hc⟩
    · rw [hc]
      exact ih
    · rcases ih with ih | ⟨_, ih⟩
      · rw [ih] at hv
        refine Or.inr ⟨hv, ?_⟩
        rw [hc, ih]
      · rw [ih] at hv
        exact absurd hv (fallbackConfig_vault_ne env _)

theorem legacy_run_fallback_fired (env : LegacyEnv) {s t : State}
    (hl : s.config.vault = 0) (h : LegacyReach env s t) (hv : t.config.vault ≠ 0) :
    Properties.legacy_run_fallback_fired env hl h hv := by
  unfold Properties.legacy_run_fallback_fired
  rcases legacy_run_config env h with hc | ⟨_, hc⟩
  · rw [hc] at hv
    exact absurd hl hv
  · exact hc

theorem legacyReach_trans {env : LegacyEnv} {s t u : State} (h₂ : LegacyReach env t u) :
    LegacyReach env s t → LegacyReach env s u := by
  induction h₂ with
  | refl => exact id
  | tail _ hs ih => exact fun h₁ => LegacyReach.tail (ih h₁) hs

/-- The forward half of `legacy_runs_characterized`. -/
theorem legacy_runs_forward (env : LegacyEnv) {s t : State} (hl : s.config.vault = 0)
    (h : LegacyReach env s t) :
    (Reach s t ∧ t.config = s.config) ∨
    ∃ u u', Reach s u ∧ u.config = s.config ∧
      ((∃ caller recipient amount,
          mint { u with config := fallbackConfig env s.config } caller recipient amount
            = some u') ∨
        (∃ caller owner amount,
          burn { u with config := fallbackConfig env s.config } caller owner amount
            = some u')) ∧
      Reach u' t := by
  induction h with
  | refl => exact Or.inl ⟨Reach.refl, rfl⟩
  | @tail w x _ hs ih =>
    rcases ih with ⟨hr, hc⟩ | ⟨u, u', hr, hc, hcall, hr'⟩
    · have hwl : w.config.vault = 0 := by rw [hc]; exact hl
      have hfb : legacyFallback env w = { w with config := fallbackConfig env s.config } := by
        rw [legacyFallback_of_vault_eq hwl, hc]
      cases hs with
      | @bridgeMint caller recipient amount hm =>
        have hm' : mint (legacyFallback env w) caller recipient amount = some x := hm
        rw [hfb] at hm'
        exact Or.inr ⟨w, x, hr, hc, Or.inl ⟨caller, recipient, amount, hm'⟩, Reach.refl⟩
      | @bridgeBurn caller owner amount hb =>
        have hb' : burn (legacyFallback env w) caller owner amount = some x := hb
        rw [hfb] at hb'
        exact Or.inr ⟨w, x, hr, hc, Or.inr ⟨caller, owner, amount, hb'⟩, Reach.refl⟩
      | transfer ht =>
        exact Or.inl ⟨Reach.tail hr (Step.transfer ht), (transfer_config ht).trans hc⟩
    · have hu' : u'.config = fallbackConfig env s.config := by
        rcases hcall with ⟨_, _, _, hm⟩ | ⟨_, _, _, hb⟩
        · exact mint_config hm
        · exact burn_config hb
      have hwv : w.config.vault ≠ 0 := by
        rw [reach_config hr', hu']
        exact fallbackConfig_vault_ne env _
      exact Or.inr ⟨u, u', hr, hc, hcall, Reach.tail hr' (legacyStep_step_of_vault_ne hwv hs)⟩

theorem legacy_runs_characterized (env : LegacyEnv) {s : State}
    (hl : s.config.vault = 0) (t : State) :
    Properties.legacy_runs_characterized env hl t := by
  unfold Properties.legacy_runs_characterized
  refine ⟨legacy_runs_forward env hl, ?_⟩
  rintro (⟨hr, _⟩ | ⟨u, u', hr, hc, hcall, hr'⟩)
  · exact reach_legacyReach env hr
  · have hul : u.config.vault = 0 := by rw [hc]; exact hl
    have hfb : legacyFallback env u = { u with config := fallbackConfig env s.config } := by
      rw [legacyFallback_of_vault_eq hul, hc]
    have hstep : LegacyStep env u u' := by
      rcases hcall with ⟨caller, recipient, amount, hm⟩ | ⟨caller, owner, amount, hb⟩
      · refine LegacyStep.bridgeMint (caller := caller) (recipient := recipient)
          (amount := amount) ?_
        show mint (legacyFallback env u) caller recipient amount = some u'
        rw [hfb]
        exact hm
      · refine LegacyStep.bridgeBurn (caller := caller) (owner := owner) (amount := amount) ?_
        show burn (legacyFallback env u) caller owner amount = some u'
        rw [hfb]
        exact hb
    exact legacyReach_trans (reach_legacyReach env hr')
      (LegacyReach.tail (reach_legacyReach env hr) hstep)

theorem legacy_reachable_ledger (env : LegacyEnv) {s t : State} (hw : WellFormed s)
    (h : LegacyReach env s t) : Properties.legacy_reachable_ledger env hw h := by
  unfold Properties.legacy_reachable_ledger
  induction h with
  | refl => exact ⟨hw, rfl⟩
  | @tail w x _ hs ih =>
    obtain ⟨hwf, ho⟩ := ih
    cases hs with
    | bridgeMint hm =>
      have hwf' := (wellFormed_legacyFallback env w).mpr hwf
      refine ⟨mint_preserves_ledger hwf' hm, ?_⟩
      rw [bridgeMint_config hm, legacyFallback_originToken, ho]
    | bridgeBurn hb =>
      have hwf' := (wellFormed_legacyFallback env w).mpr hwf
      refine ⟨burn_preserves_ledger hwf' hb, ?_⟩
      rw [bridgeBurn_config hb, legacyFallback_originToken, ho]
    | transfer ht =>
      refine ⟨(transfer_preserves_ledger hwf ht).1, ?_⟩
      rw [transfer_config ht, ho]

/-! ## Non-vacuity -/

theorem legacy_branch_witness (env : LegacyEnv) (origin account : Address)
    (ha : account ≠ 0) : Properties.legacy_branch_witness env origin account ha := by
  unfold Properties.legacy_branch_witness
  have h1 : (1 : UInt256).val = 1 := rfl
  -- the empty legacy token
  let s₀ : State := empty ⟨0, origin, 0⟩
  have hw₀ : WellFormed s₀ := by
    refine ⟨?_, ?_, rfl⟩
    · exact Finset.sum_const_zero
    · norm_num [s₀, empty, UInt256.size]
  have hl₀ : s₀.config.vault = 0 := rfl
  have hmint := legacy_bridge_mint_enabled env (amount := 1) hl₀ ha
    (by norm_num [s₀, empty, h1, UInt256.size])
  -- the funded legacy token
  let s₁ : State := ⟨⟨0, origin, 0⟩, Function.update (fun _ => 0) account 1, 1⟩
  have hw₁ : WellFormed s₁ := by
    refine ⟨?_, ?_, ?_⟩
    · simp [s₁, Function.update_apply]
    · norm_num [s₁, UInt256.size]
    · show Function.update (fun _ => 0) account 1 0 = 0
      rw [Function.update_of_ne (Ne.symm ha)]
  have hl₁ : s₁.config.vault = 0 := rfl
  have hbal₁ : s₁.balances account = 1 := by
    show Function.update (fun _ => 0) account 1 account = 1
    exact Function.update_self _ _ _
  have hburn := legacy_bridge_burn_enabled env (amount := 1) hl₁ ha (by rw [hbal₁, h1])
  -- a self-transfer of the unit is a nonlegacy-model step of the funded legacy token
  have hself : transfer s₁ account account 1 = some (transferEffect s₁ account account 1) := by
    have hta : TransferAllowed s₁ account account 1 := by
      unfold TransferAllowed
      exact ⟨ha, ha, by rw [hbal₁, h1]⟩
    unfold transfer
    exact ite_eq_left hta
  refine ⟨s₀, _, s₁, _, hw₀, hl₀, rfl, (original_model_rejects_legacy hl₀ _ _ _).1,
    hmint, LegacyReach.tail LegacyReach.refl (LegacyStep.bridgeMint hmint), rfl,
    fallbackConfig_vault_ne env _, ?_, hw₁, hl₁, rfl, hbal₁, ⟨_, Step.transfer hself⟩,
    (original_model_rejects_legacy hl₁ _ _ _).2, hburn, rfl, ?_⟩
  · simp [mintEffect, s₀, empty]
  · show (1 : ℕ) - (1 : UInt256).val = 0
    rw [h1]

end Contracts.BridgedStandardERC20
