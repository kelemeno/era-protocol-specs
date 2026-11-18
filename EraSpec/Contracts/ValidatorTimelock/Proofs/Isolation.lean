import EraSpec.Contracts.ValidatorTimelock.Properties.Isolation
import EraSpec.Contracts.ValidatorTimelock.Proofs.Model

/-!
# Proofs: other chains cannot interfere with a chain

Every check of a call on chain `c` reads the shared fields and `c`'s storage only: the
membership bit, the role admin, the enforced delay and the timestamps of `c`
(`agree_hasRole`, `agree_holdsAdminOf`, `agree_enforced`, `agree_delayPassed`), and every
write to `c`'s storage is the same function of that view. A rotation is an induction over its
grants (`changeMany_congr`). Runs follow by induction, dropping the calls on other chains with
`OtherChainCallsKeepAgreement`.
-/

namespace Contracts.ValidatorTimelock

lemma agreeOn_refl (c : Address) (s : State) : AgreeOn c s s :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

lemma agreeOn_symm {c : Address} {s t : State} (h : AgreeOn c s t) : AgreeOn c t s := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h
  exact ⟨a1.symm, a2.symm, a3.symm, a4.symm, a5.symm, a6.symm, a7.symm, a8.symm⟩

lemma agreeOn_trans {c : Address} {s t u : State} (h1 : AgreeOn c s t) (h2 : AgreeOn c t u) :
    AgreeOn c s u := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := h1
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩ := h2
  exact ⟨a1.trans b1, a2.trans b2, a3.trans b3, a4.trans b4, a5.trans b5, a6.trans b6,
    a7.trans b7, a8.trans b8⟩

lemma agree_hasRole {c : Address} {s t : State} (h : AgreeOn c s t) (e : Env) (r : Role)
    (a : Address) : hasRole e s c r a = hasRole e t c r a := by
  unfold hasRole; rw [h.2.2.2.2.1]

lemma agree_getRoleAdmin {c : Address} {s t : State} (h : AgreeOn c s t) (r : Role) :
    getRoleAdmin s c r = getRoleAdmin t c r := by
  unfold getRoleAdmin; rw [h.2.2.2.2.2.1]

lemma agree_holdsAdminOf {c : Address} {s t : State} (h : AgreeOn c s t) (e : Env) (r : Role)
    (x : Address) : HoldsAdminOf e s c r x ↔ HoldsAdminOf e t c r x := by
  rw [← holdsAdminOf_iff, ← holdsAdminOf_iff, agree_getRoleAdmin h, agree_hasRole h]

lemma agree_enforced {c : Address} {s t : State} (h : AgreeOn c s t) :
    enforcedDelay s c = enforcedDelay t c := by
  rw [enforcedDelay_eq_max, enforcedDelay_eq_max, h.2.2.2.2.2.2.1, h.2.2.2.1]

lemma agree_delayPassed {c : Address} {s t : State} (h : AgreeOn c s t) (lo hi now : ℕ) :
    delayPassed s c lo hi now ↔ delayPassed t c lo hi now := by
  unfold delayPassed; rw [agree_enforced h, h.2.2.2.2.2.2.2]

lemma agree_setMember {c : Address} {s t : State} (h : AgreeOn c s t) (r : Role) (a : Address)
    (b : Bool) : AgreeOn c (setMember s c r a b) (setMember t c r a b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, h6, h7, h8⟩
  funext r' a'
  simp only [setMember]
  rw [h5]

lemma agree_setMembers {c : Address} {s t : State} (h : AgreeOn c s t) (v : Address)
    (rs : List Role) (b : Bool) : AgreeOn c (setMembers s c v rs b) (setMembers t c v rs b) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, h6, h7, h8⟩
  funext r' a'
  simp only [setMembers]
  rw [h5]

lemma changeMany_congr {b : Bool} {e : Env} {x c v : Address} :
    ∀ {rs : List Role} {s t s' : State}, AgreeOn c s t → changeMany b e x c v rs s = some s' →
      ∃ t', changeMany b e x c v rs t = some t' ∧ AgreeOn c s' t'
  | [], s, t, s', hag, h => by
      simp only [changeMany, Option.some.injEq] at h
      subst h
      exact ⟨t, rfl, hag⟩
  | r :: rs, s, t, s', hag, h => by
      simp only [changeMany] at h
      cases h1 : changeRole b e x c r v s with
      | none => rw [h1] at h; simp at h
      | some s₁ =>
        rw [h1, Option.bind_some] at h
        obtain ⟨hr, hadm, rfl⟩ := changeRole_eq_some.mp h1
        have ht₁ : changeRole b e x c r v t = some (setMember t c r v b) :=
          changeRole_eq_some.mpr ⟨hr, (agree_holdsAdminOf hag e r x).mp hadm, rfl⟩
        obtain ⟨t', ht', hag'⟩ := changeMany_congr (agree_setMember hag r v b) h
        refine ⟨t', ?_, hag'⟩
        simp only [changeMany, ht₁, Option.bind_some]
        exact ht'

/-- A call that concerns `c` and addresses some chain addresses `c`. -/
lemma chain_of_concerns {k : Call} {c c' : Address} (hk : k.concerns c)
    (h : k.action.chain k.env = some c') : c' = c := by
  rcases hk with hk | hk
  · rw [h] at hk; exact Option.some.inj hk
  · rw [h] at hk; exact absurd hk (by simp)

theorem StepRespectsAgreement : Properties.StepRespectsAgreement := by
  rintro ⟨e, x, a⟩ c s t s' hk hag h
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ := hag
  have hag : AgreeOn c s t := ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩
  cases a with
  | initializeTimelock o d =>
    obtain ⟨h1, h2, rfl⟩ := initializeTimelock_eq_some.mp h
    exact ⟨_, initializeTimelock_eq_some.mpr ⟨g1 ▸ h1, h2, rfl⟩,
      ⟨rfl, rfl, rfl, rfl, g5, g6, g7, g8⟩⟩
  | transferOwnership n =>
    obtain ⟨h1, rfl⟩ := transferOwnership_eq_some.mp h
    exact ⟨_, transferOwnership_eq_some.mpr ⟨h1.trans g2, rfl⟩,
      ⟨g1, g2, rfl, g4, g5, g6, g7, g8⟩⟩
  | acceptOwnership =>
    obtain ⟨h1, rfl⟩ := acceptOwnership_eq_some.mp h
    exact ⟨_, acceptOwnership_eq_some.mpr ⟨h1.trans g3, rfl⟩,
      ⟨g1, rfl, rfl, g4, g5, g6, g7, g8⟩⟩
  | renounceOwnership =>
    obtain ⟨h1, rfl⟩ := renounceOwnership_eq_some.mp h
    exact ⟨_, renounceOwnership_eq_some.mpr ⟨h1.trans g2, rfl⟩,
      ⟨g1, rfl, rfl, g4, g5, g6, g7, g8⟩⟩
  | setExecutionDelay d =>
    obtain ⟨h1, h2, rfl⟩ := setExecutionDelay_eq_some.mp h
    exact ⟨_, setExecutionDelay_eq_some.mpr ⟨h1.trans g2, h2, rfl⟩,
      ⟨g1, g2, g3, rfl, g5, g6, g7, g8⟩⟩
  | increaseChainExecutionDelay c₀ d =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, h3, rfl⟩ := increaseChainExecutionDelay_eq_some.mp h
    refine ⟨_, increaseChainExecutionDelay_eq_some.mpr ⟨h1, h2, (agree_enforced hag) ▸ h3, rfl⟩,
      ⟨g1, g2, g3, g4, g5, g6, ?_, g8⟩⟩
    simp only [upd_same]
  | setChainExecutionDelay c₀ d =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, rfl⟩ := setChainExecutionDelay_eq_some.mp h
    refine ⟨_, setChainExecutionDelay_eq_some.mpr ⟨h1.trans g2, h2, rfl⟩,
      ⟨g1, g2, g3, g4, g5, g6, ?_, g8⟩⟩
    simp only [upd_same]
  | grantRole c₀ r a =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, rfl⟩ := changeRole_eq_some.mp h
    exact ⟨_, changeRole_eq_some.mpr ⟨h1, (agree_holdsAdminOf hag e r x).mp h2, rfl⟩,
      agree_setMember hag r a true⟩
  | revokeRole c₀ r a =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, rfl⟩ := changeRole_eq_some.mp h
    exact ⟨_, changeRole_eq_some.mpr ⟨h1, (agree_holdsAdminOf hag e r x).mp h2, rfl⟩,
      agree_setMember hag r a false⟩
  | renounceRole c₀ r =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, rfl⟩ := renounceRole_eq_some.mp h
    exact ⟨_, renounceRole_eq_some.mpr ⟨h1, g5 ▸ h2, rfl⟩, agree_setMember hag r x false⟩
  | setRoleAdmin c₀ r ar =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, rfl⟩ := setRoleAdmin_eq_some.mp h
    refine ⟨_, setRoleAdmin_eq_some.mpr ⟨h1, (agree_holdsAdminOf hag e r x).mp h2, rfl⟩,
      ⟨g1, g2, g3, g4, g5, ?_, g7, g8⟩⟩
    funext r'
    simp only [true_and]
    rw [g6]
  | addValidatorRoles c₀ v p =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    exact changeMany_congr hag h
  | removeValidatorRoles c₀ v p =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    exact changeMany_congr hag h
  | addValidator c₀ v =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    exact changeMany_congr hag h
  | removeValidator c₀ v =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    exact changeMany_congr hag h
  | addValidatorForChainId id v =>
    have hc : e.zkChain id = c := chain_of_concerns hk rfl
    have h' : changeMany true e x (e.zkChain id) v addValidatorParams.roles s = some s' := h
    rw [hc] at h'
    obtain ⟨t', ht', hag'⟩ := changeMany_congr hag h'
    refine ⟨t', ?_, hag'⟩
    show changeMany true e x (e.zkChain id) v addValidatorParams.roles t = some t'
    rw [hc]; exact ht'
  | removeValidatorForChainId id v =>
    have hc : e.zkChain id = c := chain_of_concerns hk rfl
    have h' : changeMany false e x (e.zkChain id) v removeValidatorParams.roles s = some s' := h
    rw [hc] at h'
    obtain ⟨t', ht', hag'⟩ := changeMany_congr hag h'
    refine ⟨t', ?_, hag'⟩
    show changeMany false e x (e.zkChain id) v removeValidatorParams.roles t = some t'
    rw [hc]; exact ht'
  | commitBatches c₀ lo hi =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, h3, rfl⟩ := commitBatches_eq_some.mp h
    refine ⟨_, commitBatches_eq_some.mpr ⟨g5 ▸ h1, h2, h3, rfl⟩,
      ⟨g1, g2, g3, g4, g5, g6, g7, ?_⟩⟩
    funext i
    simp only [recordCommit, true_and]
    rw [g8]
  | revertBatches c₀ =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, rfl⟩ := (forwardOnly_eq_some reverter_ne).mp h
    exact ⟨_, (forwardOnly_eq_some reverter_ne).mpr ⟨g5 ▸ h1, h2, rfl⟩, hag⟩
  | proveBatches c₀ =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, rfl⟩ := (forwardOnly_eq_some prover_ne).mp h
    exact ⟨_, (forwardOnly_eq_some prover_ne).mpr ⟨g5 ▸ h1, h2, rfl⟩, hag⟩
  | executeBatches c₀ lo hi =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, h3, h4, rfl⟩ := executeBatches_eq_some.mp h
    exact ⟨_, executeBatches_eq_some.mpr ⟨g5 ▸ h1, h2, (agree_delayPassed hag lo hi e.now).mp h3,
      h4, rfl⟩, hag⟩
  | upgradeChainFromVersion c₀ w =>
    have hc : c₀ = c := chain_of_concerns hk rfl
    subst hc
    obtain ⟨h1, h2, rfl⟩ := (forwardOnly_eq_some upgrader_ne).mp h
    exact ⟨_, (forwardOnly_eq_some upgrader_ne).mpr ⟨g5 ▸ h1, h2, rfl⟩, hag⟩

theorem OtherChainCallsKeepAgreement : Properties.OtherChainCallsKeepAgreement := by
  intro k c s s' h hk
  have hch : ∃ c', k.action.chain k.env = some c' ∧ c' ≠ c := by
    cases hc : k.action.chain k.env with
    | none => exact absurd (Or.inr hc) hk
    | some c' => exact ⟨c', rfl, fun h' => hk (Or.inl (by rw [hc, h']))⟩
  obtain ⟨c', hc', hne⟩ := hch
  obtain ⟨m1, m2, m3, m4⟩ := CallsTouchOnlyTheirChain k s s' c h (by rw [hc']; simpa using hne)
  -- A call that addresses a chain writes none of the shared fields.
  rcases k with ⟨e, x, a⟩
  rw [step_post h]
  rw [step_post h] at m1 m2 m3 m4
  cases a with
  | initializeTimelock o d => simp [Action.chain] at hc'
  | transferOwnership n => simp [Action.chain] at hc'
  | acceptOwnership => simp [Action.chain] at hc'
  | renounceOwnership => simp [Action.chain] at hc'
  | setExecutionDelay d => simp [Action.chain] at hc'
  | _ => exact ⟨rfl, rfl, rfl, rfl, m1.symm, m2.symm, m3.symm, m4.symm⟩

lemma run_congr {c : Address} :
    ∀ {s s' : State} {ks : List Call}, Run s ks s' → ∀ {t : State}, (∀ k ∈ ks, k.concerns c) →
      AgreeOn c s t → ∃ t', Run t ks t' ∧ AgreeOn c s' t'
  | _, _, _, .nil _, t, _, hag => ⟨t, Run.nil t, hag⟩
  | _, _, _, .cons (k := k) h1 h2, t, hall, hag => by
      obtain ⟨t₁, ht₁, hag₁⟩ := StepRespectsAgreement k c _ t _ (hall k List.mem_cons_self) hag h1
      obtain ⟨t', ht', hag'⟩ := run_congr h2 (fun k' hk' => hall k' (List.mem_cons_of_mem _ hk'))
        hag₁
      exact ⟨t', Run.cons ht₁ ht', hag'⟩

lemma run_filter {c : Address} :
    ∀ {s s' : State} {ks : List Call}, Run s ks s' → ∀ {t : State}, AgreeOn c s t →
      ∃ t', Run t (ks.filter (fun k => decide (k.concerns c))) t' ∧ AgreeOn c s' t'
  | _, _, _, .nil _, t, hag => ⟨t, Run.nil t, hag⟩
  | _, _, _, .cons (k := k) h1 h2, t, hag => by
      by_cases hk : k.concerns c
      · obtain ⟨t₁, ht₁, hag₁⟩ := StepRespectsAgreement k c _ t _ hk hag h1
        obtain ⟨t', ht', hag'⟩ := run_filter h2 hag₁
        refine ⟨t', ?_, hag'⟩
        rw [List.filter_cons_of_pos (by simpa using hk)]
        exact Run.cons ht₁ ht'
      · have hkeep := OtherChainCallsKeepAgreement k c _ _ h1 hk
        have hag₁ : AgreeOn c _ t := agreeOn_trans (agreeOn_symm hkeep) hag
        obtain ⟨t', ht', hag'⟩ := run_filter h2 hag₁
        refine ⟨t', ?_, hag'⟩
        rw [List.filter_cons_of_neg (by simpa using hk)]
        exact ht'

theorem OtherChainsCannotInterfere : Properties.OtherChainsCannotInterfere := by
  intro c
  exact ⟨fun s s' ks h => run_filter h (agreeOn_refl c s),
    fun s t s' ks hall hag h => run_congr h hall hag⟩

/-! ## The witness -/

theorem IsolationWitness : Properties.IsolationWitness := by
  obtain ⟨s₀, h0, e0⟩ := exists_run_of_isSome (ks := vtSetupCalls) (s := init) (by decide)
  obtain ⟨s₁, _, e1⟩ := exists_run_of_isSome (s := s₀) (ks := [vtOtherChainCall])
    (by rw [← exec_split e0]; decide)
  have e01 := exec_snoc_of e0 e1
  obtain ⟨s₂, _, e2⟩ := exists_run_of_isSome (s := s₀)
    (ks := [vtCall 1000 vtValidator (.commitBatches vtChain 1 1)])
    (by rw [← exec_split e0]; decide)
  obtain ⟨s₃, _, e3⟩ := exists_run_of_isSome (s := s₁)
    (ks := [vtCall 1000 vtValidator (.commitBatches vtChain 1 1)])
    (by rw [← exec_split e01]; decide)
  have hnc : ¬ vtOtherChainCall.concerns vtChain := by decide
  have hc : (vtCall 1000 vtValidator (.commitBatches vtChain 1 1)).concerns vtChain := by decide
  have hag01 := OtherChainCallsKeepAgreement _ _ _ _ (step_of_exec e1) hnc
  obtain ⟨t, ht, hag23⟩ := StepRespectsAgreement _ _ _ _ _ hc hag01 (step_of_exec e2)
  have ht3 : s₃ = t := Option.some.inj ((step_of_exec e3).symm.trans ht)
  obtain ⟨s₄, h4, _⟩ := exists_run_of_isSome (s := init)
    (ks := vtSetupCalls ++ [vtOtherChainCall,
      vtCall 1000 vtValidator (.commitBatches vtChain 1 1)]) (by decide)
  refine ⟨s₀, s₁, s₂, s₃, h0, step_of_exec e1, ?_, hnc, hag01, hc, step_of_exec e2,
    step_of_exec e3, ht3 ▸ hag23, ⟨s₄, h4⟩, rfl⟩
  rw [map_of_exec e01 (fun s => s.chainDelay vtFake) (b := 50) (by decide),
    map_of_exec e0 (fun s => s.chainDelay vtFake) (b := 0) (by decide)]
  decide

end Contracts.ValidatorTimelock
